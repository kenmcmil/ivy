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

from ivy.z3 import simplify, is_func_decl, DatatypeSortRef
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

def action_to_tr(mod,action,method,bgt):
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

mod_set = set()

def add_to_mod_set(action):
    for act in action.iter_subactions():
        mod_set.update(act.modifies())
        if isinstance(act,ia.LocalAction):
            mod_set.update(act.args[:-1])

def encode_as_array(sym):
    return not il.is_interpreted_symbol(sym) and sym.name not in im.module.destructor_sorts and sym in mod_set

# Convert all uninterpreted functions in a formula to
# arrays.

def uf_to_arr_ast(ast):
    args = [uf_to_arr_ast(arg) for arg in ast.args]
    if il.is_app(ast) and not il.is_named_binder(ast) and ast.args:
        sym = ast.rep
        if sym.name == 'sent':
            print ('ast: {}, encode = {}'.format(ast,encode_as_array(sym)))
        if encode_as_array(sym):
            sname,ssorts = create_array_sort(sym.sort)
            asym = il.Symbol(sym.name,ssorts[0])
            for i,arg in enumerate(args):
                sel = il.Symbol('arrsel',il.FunctionSort(asym.sort,arg.sort,ssorts[i+1]))
                asym = sel(asym,arg)
            return asym
    return ast.clone(args)

fresh_skolem_ctr = 0

def fresh_skolem(sort):
    global fresh_skolem_ctr
    res = il.Symbol('__havoc_'+str(fresh_skolem_ctr),sort)
    fresh_skolem_ctr += 1
    return res

def encode_assign(asgn,lhs,rhs):
    sym = lhs.rep
    if sym.name in im.module.destructor_sorts:
        (nlhs,nrhs) = encode_assign(asgn,lhs.args[0],rhs)
        return (lhs.clone([nlhs]+[lhs.args[1:]]),rhs)
    else:
        lvs = set(ilu.variables_ast(lhs));
        rvs = set(ilu.variables_ast(rhs)) if rhs is not None else set();
        rhs_const = not any(v in rvs for v in lvs)
        if any(v in rvs for v in lvs):
            if (il.is_app(rhs) and rhs.args == lhs.args and all(il.is_variable(x) for x in lhs.args)
                and len(set(lhs.args)) == len(lhs.args)):
                sym = lhs.rep
                sname, ssorts = create_array_sort(sym.sort)
                asort = ssorts[0]
                asym = il.Symbol(sym.name,asort)
                rsym = il.Symbol(rhs.rep.name,asort)
                return (asym,rsym)
            # raise iu.IvyError(asgn,'cannot convert paramaterized assignment to VMT')
        sym = lhs.rep
        sname, ssorts = create_array_sort(sym.sort)
        asort = ssorts[0]
        asym = il.Symbol(sym.name,asort)
        arhs = uf_to_arr_ast(rhs) if rhs is not None else fresh_skolem(lhs.sort)
        def recur(i,val):
            if i == len(lhs.args):
                return arhs
            idx = lhs.args[i]
            aidx = uf_to_arr_ast(idx)
            sel = il.Symbol('arrsel',il.FunctionSort(ssorts[i],aidx.sort,ssorts[i+1]))
            sval = recur(i+1,sel(val,aidx))
            if il.is_variable(idx):
                # if il.is_app(sval) and sval.rep.name == 'arrcst' or i == len(lhs.args)-1 and rhs_const:
                #     return il.Symbol('arrcst',il.FunctionSort(ssorts[i+1],ssorts[i]))(sval)
                resval = il.Lambda([aidx],sval)
                return il.Symbol('cast',il.FunctionSort(resval.sort,ssorts[i]))(resval)
            else:
                # work around z3 bug
                if False and is_any_lambda(sval):
                    rn = iu.UniqueRenamer('V',(v.rep for v in ilu.used_variables_ast(sval)))
                    lvar = il.Variable(rn(),idx.sort)
                    sval = ite_into_lambda(sval,il.Equals(lvar,idx),sel(val,lvar))
                    resval = il.Lambda([lvar],sval)
                    return il.Symbol('cast',il.FunctionSort(resval.sort,ssorts[i]))(resval)
                upd = il.Symbol('arrupd',il.FunctionSort(ssorts[i],aidx.sort,ssorts[i+1],ssorts[i]))
                return upd(val,aidx,sval)
        res = (asym,recur(0,asym))
        return res
    
def is_constant_lambda(x):
    if il.is_app(x) and x.rep.name == 'cast' or il.is_lambda(x):
        return is_constant_lambda(x.args[0])
    return il.is_true(x) or il.is_false(x)

def is_any_lambda(x):
    return il.is_app(x) and x.rep.name == 'cast'

def ite_into_lambda(x,cond,elseval):
    if il.is_app(x) and x.rep.name == 'cast':
        arrsort = x.sort
        lx = x.args[0]
        assert il.is_lambda(lx)
        idx = lx.variables[0]
        ressort = lx.args[0].sort
        sel = il.Symbol('arrsel',il.FunctionSort(arrsort,idx.sort,ressort))
        elseval = sel(elseval,idx)
        return x.clone([lx.clone([ite_into_lambda(lx.args[0],cond,elseval)])])
    return il.Ite(cond,x,elseval)


                        
    

def uf_to_array_action(action):
    if isinstance(action,ia.Action):
        args = [uf_to_array_action(act) for act in action.args]
        if isinstance(action,ia.AssignAction):
            if action.args[0].args and not il.is_interpreted_symbol(action.args[0].rep):
                args = encode_assign(action,action.args[0],action.args[1])
        elif isinstance(action,ia.HavocAction):
            if action.args[0].args and not il.is_interpreted_symbol(action.args[0].rep):
                args = encode_assign(action,action.args[0],None)
                return ia.AssignAction(args[0],args[1]).set_lineno(action.lineno)
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

def frame_clauses(all_vars, mod_vars, clauses):
    mod_set = set(mod_vars)
    return ilu.and_clauses(ilu.Clauses([il.Equals(x,tr.new(x)) for x in all_vars if x not in mod_set]), clauses)

def check_isolate(method="mc"):
    mod = im.module

    # Use the error flag construction to turn assertion checks into
    # an invariant check.

    erf = il.Symbol('err_flag',il.find_sort('bool'))
    errconds = []
    has_erf = any(has_assert(mod.actions[x]) for x in mod.actions)
    if has_erf:
        add_err_flag_mod(mod,erf,errconds)


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

    bgt = mod.background_theory()

    # Convert uf's to arrays, if possible

    # Only encode the modified symbols as arrays

    mod_set.clear()
    add_to_mod_set(init_action)
    for x,action in mod.actions.items():
        add_to_mod_set(action)
    # print ('mod_set: {}'.format([str(x) for x in mod_set]))

    for actname in list(mod.actions):
        action = mod.actions[actname]
        new_action = uf_to_array_action(action)
        new_action.formal_params = action.formal_params
        new_action.formal_returns = action.formal_returns
        mod.actions[actname] = new_action

    init_action = uf_to_array_action(init_action)
    # print (init_action)
    conjs = [conj.clone([conj.label,uf_to_arr_ast(conj.formula)]) for conj in conjs]

    # Combine all actions nto a single action

    actions = [(x,mod.actions[x].add_label(x)) for x in sorted(mod.public_actions)]
#    action = ia.EnvAction(*ext_acts)
    if has_erf:
        actions = [(x,ia.Sequence(ia.AssignAction(erf,il.Or()).set_lineno(iu.nowhere()),act))
                   for x,act in actions]

    # Seperate out the axioms that do not have modified symbols

    have_mod = [any(y in mod_set for y in ilu.used_symbols_ast(x)) for x in bgt.fmlas]
    axioms = [x for x,hm in zip(bgt.fmlas,have_mod) if not hm]
    bgt = ilu.Clauses([x for x,hm in zip(bgt.fmlas,have_mod) if hm])
    
    # Convert the global action and initializer to logic. Notice we
    # use 'action_to_state' to turn the initializer TR into a state
    # predicate (i.e., it's strongest post).

    actupds = [action_to_tr(mod,action,method,bgt) for x,action in actions]
    # for a in actupds:
        # print ('a[0]: {}'.format(a[0]))
        # print ('a[1]: {}'.format(a[1]))
    stvars = list(iu.unique(sym for a in actupds for sym in a[0]))
    transs = [ilu.clauses_to_formula(frame_clauses(stvars,a[0],a[1])) for a in actupds]
    trans = il.Or(*[fmla for fmla in transs]) if len(actupds) != 1 else transs[0]
    istvars,init,ierror = tr.action_to_state(action_to_tr(mod,init_action,method,bgt))
    stvars = list(iu.unique(stvars+istvars))

    for action, tran_fm in zip(actions, transs):
        # want to have (=> action trans) but have to declare boolean action vars
        pass


    # trans = ilu.clauses_to_formula(trans)
    init = ilu.clauses_to_formula(init)

    # print ('init: {}'.format(init))
    # print ('trans: {}'.format(trans))
    # for conj in conjs:
    #     print ('conj: {}'.format(conj))


    sorts = []

    vmt_var_defs = []

    def add_sort(sort):
        if sort not in sorts:
            sorts.append(sort)

    declared_symbols = set()
    enum_symbols = set()
    for sym in ilu.used_symbols_asts([init,trans]+[lf.formula for lf in conjs]+axioms):
        sym = il.normalize_symbol(sym)
        if il.is_enumerated_sort(sym.sort):
            if sym in sym.sort.constructors:
                enum_symbols.add(sym)
                continue
        if sym not in declared_symbols and slvr.solver_name(sym) is not None and sym.name != "cast":
            declared_symbols.add(sym)
            decl = slvr.symbol_to_z3_full(sym)
            if il.is_constant(sym):
                if is_func_decl(decl):
                    for i in range(decl.arity()):
                        add_sort(decl.domain(i))
                    add_sort(decl.range())
                    if not il.is_interpreted_symbol(sym):
                        decl_sexpr = decl.sexpr()
                        vmt_var_defs.append(decl_sexpr)
                        # decl_sort = decl.range().sexpr()
                        # decl_dom = ' '.join(decl.domain(i).sexpr() for i in range(decl.arity()))
                        # vmt_var_defs.append(f"(declare-fun {decl_sexpr} ({decl_dom}) {decl_sort})")
                else:
                    add_sort(decl.sort())
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
        if isinstance(sort,DatatypeSortRef):
            sort_str = f"(declare-datatypes () (({sort_name} {' '.join(str(sort.constructor(i)) for i in range(sort.num_constructors()))})))"
        else:
            sort_str = f"(declare-sort {sort_name} 0)"
        vmt_sort_defs.append(sort_str)

    all_used = ilu.used_symbols_asts([init,trans])
    immutable = [sym for sym in all_used if not il.is_function_sort(sym.sort)
                 and not sym.is_skolem() and not tr.is_new(sym)
                 and "fml:" not in sym.name and "loc:" not in sym.name and tr.new(sym) not in all_used
                 and all(sym not in upd[0] for upd in actupds)]
    background_symbols = ilu.used_symbols_asts(axioms)
    background_symbols.update(enum_symbols)
    immutable = [sym for sym in immutable if not sym in background_symbols]
    # print ('immutable: {}'.format(immutable))

    for sym in ilu.used_symbols_asts([init,trans]):
        if tr.is_new(sym):
            next_sym = slvr.symbol_to_z3_full(sym)
            cur_sym = slvr.symbol_to_z3_full(tr.new_of(sym))
            next_str = next_sym.sexpr()
            cur_str = cur_sym.sexpr()
            # print ('foo: {},{}'.format(cur_sym,sym))
            sort = cur_sym.sort().sexpr()
            full_str = f"(define-fun .{cur_str} () {sort} (! {cur_str} :next {next_str}))"
            vmt_var_defs.append(full_str)
        elif "fml:" in sym.name or "loc:" in sym.name or sym.is_skolem() or sym in immutable:
            next_sym_str = f"new_{sym.name.replace(':', '')}"
            cur_sym_str = slvr.symbol_to_z3_full(sym).sexpr()
            # cur_sym_str = f"|{sym.name}|"
            sort = slvr.symbol_to_z3(sym).sort().sexpr()
            next_fml_def = f"(declare-fun {next_sym_str} () {sort})"
            vmt_var_defs.append(next_fml_def)
            define_fun_str = cur_sym_str.replace("|", "").replace(":", "")
            full_str = f"(define-fun .{define_fun_str} () {sort} (! {cur_sym_str} :next {next_sym_str}))"
            vmt_var_defs.append(full_str)

    frame = [il.Equals(x,tr.new(x)) for x in immutable]
    # print ('frame: {}'.format(frame))

    props = []
    herbrand_trans = [simplify(slvr.formula_to_z3(x)).sexpr() for x in frame] # List[str]
    for i, lf in enumerate(conjs):
        # var_defs, herb_trans = herbrandize_property_vars(slvr.formula_to_z3(lf.formula))
        # herbrand_trans.extend(herb_trans)
        # vmt_var_defs.extend(var_defs)
        # prop_formula = normalize_prop(slvr.formula_to_z3(lf.formula))
        prop_formula = slvr.formula_to_z3(lf.formula).sexpr()
        props.append(f'(define-fun property () Bool (! {prop_formula} :invar-property {i}))')

    init_formula_str = simplify(slvr.formula_to_z3(init)).sexpr()
    trans_formula_str = simplify(slvr.formula_to_z3(trans)).sexpr()
    vmt_formula_defs = []
    init_vmt = f"(define-fun init () Bool (! {init_formula_str} :init true))"
    vmt_formula_defs.append(init_vmt)

    vmt_var_defs.extend(get_action_defs(actions))

    # print ('foo : {}'.format(transs[-1]))

    trans_vmt = get_trans_str(transs, actions, herbrand_trans) # transs not a typo
    vmt_formula_defs.append(trans_vmt)
    vmt_formula_defs.extend(props)

    vmt_axiom_defs = []
    for axiom in axioms:
        vmt_axiom_defs.append('(assert {})'.format(simplify(slvr.formula_to_z3(axiom)).sexpr()))

    vmt_file_name = mod.name + '.vmt'
    with open(vmt_file_name, "w") as f:
        vmt_str = vmt_sort_defs + vmt_func_defs + vmt_var_defs + vmt_formula_defs + vmt_axiom_defs
        f.write("\n".join(vmt_str))

    print('output written to '+vmt_file_name)
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
    for i,x in enumerate(action_names):
        for j,y in enumerate(action_names[i+1:]):
            vmt_list.append(f"(or (not {x}) (not {y}))")
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

