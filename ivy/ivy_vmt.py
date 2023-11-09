#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_module as im
from . import ivy_actions as ia
from . import ivy_logic as il
from . import ivy_transrel as tr
from . import ivy_logic_utils as ilu
from . import ivy_utils as iu
from . import ivy_art as art
from . import ivy_interp as itp
from . import ivy_theory as thy
from . import ivy_ast
from . import ivy_proof
from . import ivy_trace
from . import ivy_solver as slvr

from ivy.z3 import simplify
import tempfile
import subprocess
from collections import defaultdict
import itertools
import sys
import os

logfile = None
verbose = False

def checked(thing):
    return ia.checked_assert.value in ["",thing.lineno]

def action_to_tr(mod,action,method):
    bgt = mod.background_theory()
    if method=="fsmc":  # if finite-state, unroll the loops
        with ia.UnrollContext(im.module.sort_card):
            upd = action.update(im.module,None)
    else:
        upd = action.update(im.module,None)
    stvars,trans,error = tr.add_post_axioms(upd,bgt)
    trans = ilu.and_clauses(trans,ilu.Clauses(defs=bgt.defs))
    defsyms = set(x.defines() for x in bgt.defs)
    rn = dict((tr.new(sym),tr.new(sym).prefix('__')) for sym in defsyms)
    trans = ilu.rename_clauses(trans,rn)
    error = ilu.rename_clauses(error,rn)
    stvars = [x for x in stvars if x not in defsyms]  # Remove symbols with state-dependent definitions
    return (stvars,trans,error)

def add_err_flag(action,erf,errconds):
    if isinstance(action,ia.AssertAction):
        if checked(action):
            if verbose:
                print("{}Model checking guarantee".format(action.lineno))
            errcond = ilu.dual_formula(il.drop_universals(action.formula))
            res = ia.AssignAction(erf,il.Or(erf,errcond))
            errconds.append(errcond)
            res.lineno = iu.nowhere()
            return res
        if isinstance(action,ia.SubgoalAction):
#            print "skipping subgoal at line {}".format(action.lineno)
            return ia.Sequence()
    if isinstance(action,ia.AssumeAction) or isinstance(action,ia.AssertAction):
        if isinstance(action,ia.AssertAction):
            if verbose:
                print("assuming assertion at line {}".format(action.lineno))
        res = ia.AssumeAction(il.Or(erf,action.formula))
        res.lineno = iu.nowhere()
        return res
    if isinstance(action,(ia.Sequence,ia.ChoiceAction,ia.EnvAction,ia.BindOldsAction)):
        return action.clone([add_err_flag(a,erf,errconds) for a in action.args])
    if isinstance(action,ia.IfAction):
        return action.clone([action.args[0]] + [add_err_flag(a,erf,errconds) for a in action.args[1:]])
    if isinstance(action,ia.LocalAction):
        return action.clone(action.args[:-1] + [add_err_flag(action.args[-1],erf,errconds)])
    return action

def add_err_flag_mod(mod,erf,errconds):
    for actname in list(mod.actions):
        action = mod.actions[actname]
        new_action = add_err_flag(action,erf,errconds)
        new_action.formal_params = action.formal_params
        new_action.formal_returns = action.formal_returns
        mod.actions[actname] = new_action


# Take a function sort and return a corresponding array sort.
def create_array_sort(sort):
    def aname(i):
        if i == len(sort.dom):
            return (sort.rng.name,[sort.rng])
        sname,ssorts = aname(i+1)
        name = 'arr[' + sort.dom[i].name + '][' + sname + ']'
        if name not in il.sig.sorts:
            asort = il.UninterpretedSort(name)
            il.add_sort(asort)
            il.sig.interp[name] = name
        return (name,[il.sig.sorts[name]]+ssorts)
    return aname(0)

# Should I convert this symbol to an array?

def encode_as_array(sym):
    return not il.is_interpreted_symbol(sym) and sym.name not in im.module.destructor_sorts

# Convert all uninterpreted functions in a formula to
# arrays.

def uf_to_arr_ast(ast):
    args = [uf_to_arr_ast(arg) for arg in ast.args]
    if il.is_app(ast) and not il.is_named_binder(ast) and ast.args:
        sym = ast.rep
        if encode_as_array(sym):
            sname,ssorts = create_array_sort(sym.sort)
            asym = il.Symbol(sym.name,ssorts[0])
            for i,arg in enumerate(args):
                sel = il.Symbol('arrsel',il.FunctionSort(asym.sort,arg.sort,ssorts[i+1]))
                asym = sel(asym,arg)
            return asym
    return ast.clone(args)

def encode_assign(asgn,lhs,rhs):
    sym = lhs.rep
    if sym.name in im.module.destructor_sorts:
        (nlhs,nrhs) = encode_assign(asgn,lhs.args[0],rhs)
        return (lhs.clone([nlhs]+[lhs.args[1:]]),rhs)
    else:
        lvs = set(ilu.variables_ast(lhs));
        rvs = set(ilu.variables_ast(rhs));
        if any(v in rvs for v in lvs):
            raise iu.IvyError(asgn,'cannot convert paramaterized assignment to VMT')
        sym = lhs.rep
        sname, ssorts = create_array_sort(sym.sort)
        asort = ssorts[0]
        asym = il.Symbol(sym.name,asort)
        arhs = uf_to_arr_ast(rhs)
        def recur(i,val):
            if i == len(lhs.args):
                return arhs
            idx = lhs.args[i]
            if il.is_variable(idx):
                sval = recur(i+1,None)
                return il.Symbol('arrcst',il.FunctionSort(ssorts[i+1],ssorts[i]))(sval)
            if val is None:
                raise iu.IvyError(asgn,'cannot convert paramaterized assignment to VMT')
            aidx = uf_to_arr_ast(idx)
            sel = il.Symbol('arrsel',il.FunctionSort(ssorts[i],aidx.sort,ssorts[i+1]))
            sval = recur(i+1,sel(val,aidx))
            upd = il.Symbol('arrupd',il.FunctionSort(ssorts[i],aidx.sort,ssorts[i+1],ssorts[i]))
            return upd(val,aidx,sval)
        return(asym,recur(0,asym))

def uf_to_array_action(action):
    if isinstance(action,ia.Action):
        args = [uf_to_array_action(act) for act in action.args]
        if isinstance(action,ia.AssignAction):
            if action.args[0].args and not il.is_interpreted_symbol(action.args[0].rep):
                args = encode_assign(action,action.args[0],action.args[1])
        return action.clone(args)
    else:
        return uf_to_arr_ast(action)

def has_assert(action):
    for x in action.iter_subactions():
        if isinstance(x,ia.AssertAction):
            return True
    return False

def normalize_prop(prop_z3_fm):
    if prop_z3_fm.is_forall():
        prop_sexpr = prop_z3_fm.body().sexpr()
        for i in range(prop_z3_fm.num_vars()):
            var_name = prop_z3_fm.var_name(i).split(":")[0]
            prop_sexpr = prop_sexpr.replace(f"(:var {i})", var_name)
        return prop_sexpr
    # return prop_z3_fm.sexpr()
    raise Exception("Don't support non-universally quantified properties")


def herbrandize_property_vars(prop_z3_fm):
    if prop_z3_fm.is_forall():
        var_strs = []
        trans = []
        for i in range(prop_z3_fm.num_vars()):
            var_name = prop_z3_fm.var_name(i).split(":")[0]
            var_sort = prop_z3_fm.var_sort(i).name()
            vmt_str = f"(declare-fun {var_name} () {var_sort})"
            vmt_next = f"(declare-fun new_{var_name} () {var_sort})"
            define = f"(define-fun .{var_name} () {var_sort} (! {var_name} :next new_{var_name}))"
            var_strs.append(vmt_str)
            var_strs.append(vmt_next)
            var_strs.append(define)
            trans.append(f"(= {var_name} new_{var_name})")
        return var_strs, trans
    raise Exception("Don't support non-universally quantified properties")

def get_dom_and_rng(sort_name):
    dom, rng = sort_name.split("-")[1:]
    if rng == "bool":
        rng = "Bool"
    return dom, rng

def check_isolate(method="mc"):
    mod = im.module

    # Use the error flag construction to turn assertion checks into
    # an invariant check.

    erf = il.Symbol('err_flag',il.find_sort('bool'))
    errconds = []
    has_erf = any(has_assert(mod.actions[x]) for x in mod.actions)
    if has_erf:
        add_err_flag_mod(mod,erf,errconds)

    # Combine all actions nto a single action

    actions = [(x,mod.actions[x].add_label(x)) for x in sorted(mod.public_actions)]
#    action = ia.EnvAction(*ext_acts)
    if has_erf:
        actions = [(x,ia.Sequence(ia.AssignAction(erf,il.Or()).set_lineno(iu.nowhere()),act))
                   for x,act in actions]

    # We can't currently handle assertions in the initializers

    for (name,init) in mod.initializers:
        if has_assert(init):
            raise iu.IvyError(x,'VMT cannot handle assertions in initializers')

    # Build a single initializer action
    init_action = ia.Sequence(*[act for (nm,act) in mod.initializers])


    # get the invariant to be proved, replacing free variables with
    # skolems. First, we apply any proof tactics.

    pc = ivy_proof.ProofChecker(mod.labeled_axioms,mod.definitions,mod.schemata)
    pmap = dict((lf.id,p) for lf,p in mod.proofs)
    conjs = []
    for lf in mod.labeled_conjs:
        if not checked(lf):
#            print 'skipping {}'.format(lf)
            continue
        if verbose:
            print("{}Model checking invariant".format(lf.lineno))
        if lf.id in pmap:
            proof = pmap[lf.id]
            subgoals = pc.admit_proposition(lf,proof)
            conjs.extend(subgoals)
        else:
            conjs.append(lf)

    # Convert uf's to arrays, if possible

    actions = [(x,uf_to_array_action(action)) for x,action in actions]
    # for x,a in actions:
    #     print (a)

    init_action = uf_to_array_action(init_action)
    # print (init_action)
    conjs = [conj.clone([conj.label,uf_to_arr_ast(conj.formula)]) for conj in conjs]

    # Convert the global action and initializer to logic. Notice we
    # use 'action_to_state' to turn the initializer TR into a state
    # predicate (i.e., it's strongest post).

    actupds = [action_to_tr(mod,action,method) for x,action in actions]
    transs = [ilu.clauses_to_formula(a[1]) for a in actupds]
    trans = il.Or(*[fmla for fmla in transs]) if len(actupds) != 1 else transs[0]
    stvars = list(iu.unique(sym for a in actupds for sym in a[0]))
    istvars,init,ierror = tr.action_to_state(action_to_tr(mod,init_action,method))
    stvars = list(iu.unique(stvars+istvars))

    for action, tran_fm in zip(actions, transs):
        # want to have (=> action trans) but have to declare boolean action vars
        pass


    # trans = ilu.clauses_to_formula(trans)
    init = ilu.clauses_to_formula(init)

    print ('init: {}'.format(init))
    print ('trans: {}'.format(trans))
    for conj in conjs:
        print ('conj: {}'.format(conj))


    sorts = []

    vmt_var_defs = []

    for sym in ilu.used_symbols_asts([init,trans]+[lf.formula for lf in conjs]):
        if slvr.solver_name(sym) is not None:
            decl = slvr.symbol_to_z3(sym)
            if il.is_constant(sym):
                if decl.sort() not in sorts:
                    sorts.append(decl.sort())
                if not il.is_interpreted_symbol(sym):
                    decl_sexpr = decl.sexpr()
                    decl_sort = decl.sort().sexpr()
                    vmt_var_defs.append(f'(declare-fun {decl_sexpr} () {decl_sort})')
            else:
                vmt_var_defs(decl.sexpr())

    vmt_sort_defs = []
    vmt_func_defs = []
    # must declare sorts that are not built-in
    for sort in sorts:
        sort_name = sort.name()
        if "Array" in sort_name:
            continue
        if "Bool" == sort_name:
            continue
        if sort_name.startswith("Arr"):
            dom, rng = get_dom_and_rng(sort_name)
            read = f"(declare-fun Read{sort_name} ({sort_name} {dom}) {rng})"
            write = f"(declare-fun Write{sort_name} ({sort_name} {dom} {rng}) {sort_name})"
            const = f"(declare-fun Const{sort_name} ({rng}) {sort_name})"
            vmt_func_defs.append(read)
            vmt_func_defs.append(write)
            vmt_func_defs.append(const)
        sort_str = f"(declare-sort {sort_name} 0)"
        vmt_sort_defs.append(sort_str)

    for sym in ilu.used_symbols_asts([init,trans]):
        if tr.is_new(sym):
            next_sym = slvr.symbol_to_z3(sym)
            cur_sym = slvr.symbol_to_z3(tr.new_of(sym))
            next_str = next_sym.sexpr()
            cur_str = cur_sym.sexpr()
            sort = cur_sym.sort().sexpr()
            full_str = f"(define-fun .{cur_str} () {sort} (! {cur_str} :next {next_str}))"
            vmt_var_defs.append(full_str)
        elif "fml:" in sym.name:
            next_sym_str = f"|new_{sym.name}|"
            cur_sym_str = f"|{sym.name}|"
            sort = slvr.symbol_to_z3(sym).sort().sexpr()
            next_fml_def = f"(declare-fun {next_sym_str} () {sort})"
            vmt_var_defs.append(next_fml_def)
            define_fun_str = cur_sym_str.replace("|", "").replace(":", "")
            full_str = f"(define-fun .{define_fun_str} () {sort} (! {cur_sym_str} :next {next_sym_str}))"
            vmt_var_defs.append(full_str)

    props = []
    herbrand_trans = [] # List[str]
    for i, lf in enumerate(conjs):
        var_defs, herb_trans = herbrandize_property_vars(slvr.formula_to_z3(lf.formula))
        herbrand_trans.extend(herb_trans)
        vmt_var_defs.extend(var_defs)
        prop_formula = normalize_prop(slvr.formula_to_z3(lf.formula))
        props.append(f'(define-fun property () Bool (! {prop_formula} :invar-property {i}))')

    init_formula_str = simplify(slvr.formula_to_z3(init)).sexpr()
    trans_formula_str = simplify(slvr.formula_to_z3(trans)).sexpr()
    vmt_formula_defs = []
    init_vmt = f"(define-fun init () Bool (! {init_formula_str} :init true))"
    vmt_formula_defs.append(init_vmt)

    vmt_var_defs.extend(get_action_defs(actions))

    trans_vmt = get_trans_str(transs, actions, herbrand_trans) # transs not a typo
    vmt_formula_defs.append(trans_vmt)
    vmt_formula_defs.extend(props)

    with open("ivy.vmt", "w") as f:
        vmt_str = vmt_sort_defs + vmt_func_defs + vmt_var_defs + vmt_formula_defs
        f.write("\n".join(vmt_str))

    print('output written to ivy.vmt')
    exit(0)


def get_trans_str(trans_fm_list, actions, herbrand_trans):
    vmt_list = []
    action_names = []
    for action, trans_fm in zip(actions, trans_fm_list):
        action_name = action[0].split(":")[-1]
        action_names.append(action_name)
        trans_str = simplify(slvr.formula_to_z3(trans_fm)).sexpr()
        full_str = f"(=> {action_name} {trans_str})"
        vmt_list.append(full_str)
    vmt_list.append(f"(or {' '.join(action_names)})")
    for ht in herbrand_trans:
        vmt_list.append(ht)
    vmt_str = '\n'.join(vmt_list)
    return f"(define-fun trans () Bool (! (and {vmt_str}) :trans true))"

def get_action_defs(actions):
    action_defs = []
    for action in actions:
        action_name = action[0].split(":")[-1]
        action_def = f"(declare-fun {action_name} () Bool)"
        define = f"(define-fun .{action_name} () Bool (! {action_name} :action 0))"
        action_defs.append(action_def)
        action_defs.append(define)
    return action_defs

