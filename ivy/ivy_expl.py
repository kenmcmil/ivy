#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_ast
from . import ivy_proof as pf
from . import ivy_actions as ia
from . import ivy_temporal as tm
from . import ivy_logic as lg
from . import ivy_logic_utils as ilu
from . import ivy_utils as iu
from . import ivy_trace as tr
from . import logic_util as lu
from . import ivy_proof as pr
from . import ivy_auto_inst
from . import ivy_module as im
from . import ivy_solver as slv

from ordered_set import OrderedSet
from collections import OrderedDict

def conjunctive_partition(fm):
    res = []
    def recur(fm):
        if lg.is_and(fm):
            for x in fm.args:
                recur(x)
        else:
            res.append(fm)
    recur(fm)
    return res

def disjunctive_partition(fm):
    res = []
    def recur(fm):
        if lg.is_or(fm):
            for x in fm.args:
                recur(x)
        else:
            res.append(fm)
    recur(fm)
    return res

def remove_symmetric_equalities(fmlas):
    res = []
    seen = set()
    for x in fmlas:
        if lg.is_eq(x):
            if lg.Equals(x.args[1],x.args[0]) in seen:
                continue
        elif lg.is_not(x) and lg.is_eq(x.args[0]):
            if lg.Not(lg.Equals(x.args[0].args[1],x.args[0].args[0])) in seen:
                continue
        seen.add(x)
        res.append(x)
    return res

def simplify(fm):
    if lg.is_and(fm):
        conjs = list(iu.unique(simplify(x) for x in conjunctive_partition(fm)))
        if any(lg.is_false(x) for x in conjs):
            return lg.Or()
        conjs = [x for x in conjs if not lg.is_true(x)]
        if len(conjs) == 1:
            return conjs[0]
        else:
            return lg.And(*remove_symmetric_equalities(conjs))
    if lg.is_or(fm):
        disjs = list(iu.unique(simplify(x) for x in disjunctive_partition(fm)))
        if any(lg.is_true(x) for x in disjs):
            return lg.And()
        disjs = [x for x in disjs if not lg.is_false(x)]
        if len(disjs) == 1:
            return disjs[0]
        else:
            return lg.Or(*remove_symmetric_equalities(disjs))
    if lg.is_eq(fm) and fm.args[0] == fm.args[1]:
        return lg.And()
    return fm.clone([simplify(x) for x in fm.args])

def elim_vars(fm,E):
    fm = simplify(fm)
    fvs = ilu.used_variables_ast(fm)
    lits = conjunctive_partition(fm)
    for lit in lits:
        if lg.is_eq(lit):
            if E(lit.args[0]):
                subs = {lit.args[0]:lit.args[1]}
                lits = [lu.substitute(x,subs) for x in lits if x != lit]
            elif E(lit.args[1]):
                subs = {lit.args[1]:lit.args[0]}
                lits = [lu.substitute(x,subs) for x in lits if x != lit]
        elif lg.is_constant(lit) and E(lit):
            subs = {lit:lg.And()}
            lits = [lu.substitute(x,subs) for x in lits if x != lit]
        elif lg.is_not(lit) and lg.is_constant(lit.args[0]) and E(lit.args[0]):
            subs = {lit.args[0]:lg.Or()}
            lits = [lu.substitute(x,subs) for x in lits if x != lit]
            
            

    normal_lits = [lit for lit in lits if not(lg.is_not(lit) and lg.is_eq(lit.args[0]))]
    negeq_lits = [lit for lit in lits if (lg.is_not(lit) and lg.is_eq(lit.args[0]))]
    # print ('negeq_lits: {}'.format(negeq_lits))
    # print ('normal_lits: {}'.format(normal_lits))
    normal_vocab = ilu.used_symbols_ast(lg.And(*normal_lits))
    def is_eliminable(v):
        return lg.is_constant(v) and E(v) and v not in normal_vocab
    def is_elim_negeq(lit):
        res = is_eliminable(lit.args[0].args[0]) or is_eliminable(lit.args[0].args[1])
        # if res:
        #     print ('eliminating: {}'.format(lit))
        return res
    negeq_lits = [lit for lit in negeq_lits if not is_elim_negeq(lit)]
    # print ('negeq_lits: {}'.format(negeq_lits))
    res = lg.And(*(normal_lits+negeq_lits))
    # print ('before elim: {}'.format(fm))
    # print ('after elim: {}'.format(res))
    return simplify(res)

def easy_qelim(fm):
    if lg.is_forall(fm) or lg.is_exists(fm):
        vs = set(fm.variables)
        def E(x):
            return x in vs
        if lg.is_forall(fm):
            res = Not(elim_vars(Not(fm.args[0]),E))
            if lg.is_and(res.args[0]):
                res = Or(*[Not(x) for x in res.args[0].args])
            return simplify(ForAll(fm.quantifier_vars(),res))
        else:
            res = elim_vars(fm.args[0],fm.quantifier_vars())
            return simplify(Exists(fm.quantifier_vars(),res))
    return fm.clone(tuple(easy_qelim(x) for x in fm.args))

def negate(t):
    return t.args[0] if lg.is_not(t) else lg.Not(t)

def implicant(model,fmla,clauses):

    def my_get_value(model,expr):
        res = model.eval_to_constant(expr)
        return res

    defns = dict()
    for dfn in clauses.defs:
        symbol = dfn.defines()
        defns[symbol] = dfn
    if clauses.fmlas:
        fmla = lg.And(*([fmla] + [lg.close_formula(x) for x in clauses.fmlas]))

    def expand_defn(term):
        if lg.is_app(term):
            sym = term.rep
            if sym in defns:
                dfn = defns[sym]
                vs = dfn.lhs().args
                vals = term.args
                return lu.substitute(dfn.rhs(),zip(vs,vals))
        return None

    def expand_defns(term):
        while True:
            newt = expand_defn(term)
            if newt is None:
                return term
            term = newt

    cnsts_set = set()
    cnsts = []
    def elim_ite(fm,bound):
        fm = expand_defns(fm)
        if lg.is_ite(fm):
            # print ('ite: {}'.format(fm))
            if not any(x in bound for x in ilu.used_variables_ast(fm.args[0])):
                if lg.is_true(my_get_value(model,fm.args[0])):
                    cond = fm.args[0]
                    res = elim_ite(fm.args[1],bound)
                else: 
                    cond = negate(fm.args[0])
                    res = elim_ite(fm.args[2],bound)
                if cond not in cnsts_set:
                    cnsts_set.add(cond)
                    cnsts.append(cond)
                # print ('res: {}'.format(res))
                return res
        elif lg.is_constant(fm) and lg.is_boolean(fm) and fm not in bound:
            if lg.is_true(my_get_value(model,fm)):
                cond = fm
                res = lg.And()
            else:
                cond = negate(fm)
                res = lg.Or()
            if cond not in cnsts_set:
                cnsts_set.add(cond)
                cnsts.append(cond)
            # print ('res: {}'.format(res))
            return res
        elif lg.is_quantifier(fm):
            bound = frozenset(list(bound) + list(fm.variables))
        return fm.clone(tuple(elim_ite(x,bound) for x in fm.args))

    pos_memo = {}
    def recur_pos(model,fm,must=False):
        # if fm in pos_memo:
        #     return pos_memo[fm]
        fm = expand_defns(fm)
        res = _recur_pos(model,fm,must)
        if must and res is None:
            print ('*Z3 got wrong truth value for {}'.format(fm))
            with open("thing.model", "w") as f:
                f.write(str(model))
            print(model)
            exit(1)
        # pos_memo[fm] = res
        # print ('pos arg: {}'.format(fm))
        # print ('pos res: {}'.format(res))
        return res
    def _recur_pos(model,fm,must):
        args = fm.args
        if lg.is_not(fm):
            return recur_neg(model,args[0])
        elif lg.is_and(fm):
            subs = [recur_pos(model,arg,must) for arg in args]
            return lg.And(*subs) if all(x is not None for x in subs) else None
        elif lg.is_or(fm):
            for x in args:
                sub = recur_pos(model,x)
                if sub is not None:
                    return sub
            return None
        elif lg.is_implies(fm):
            lhs = recur_neg(model,args[0])
            if lhs is not None:
                return lhs
            rhs = recur_pos(model,args[1],True)
            if rhs is not None:
                return rhs
            return None
        # elif fm.is_iff():
        #     truths = [model.get_value(arg) for arg in args]
        #     if truths[0].is_true() and truths[1].is_true():
        #         return And(map(recur_pos,args))
        #     if truths[0].is_false() and truths[1].is_false():
        #         return And(map(recur_neg,args))
        #     assert False
        v = model.eval_quant_to_constant(fm)
        if not (lg.is_true(v) or lg.is_false(v)):
            print ('formula: {}, value: {}'.format(fm,v))
            assert False
        b = lg.is_true(v)
        if must and not b:
            print ('Z3 got wrong truth value for {}'.format(fm))
            print ('v: {}'.format(v))
            if lg.is_eq(fm):
                print('left: {}'.format(my_get_value(model,fm.args[0])))
                print('right: {}'.format(my_get_value(model,fm.args[1])))
            assert False
        if b:
            return elim_ite(fm,frozenset([]))
        return None
    neg_memo = {}
    def recur_neg(model,fm,must=False):
        # if fm in neg_memo:
        #     return neg_memo[fm]
        fm = expand_defns(fm)
        res = _recur_neg(model,fm)
        # neg_memo[fm] = res
        return res
    def _recur_neg(model,fm):
        args = fm.args
        if lg.is_not(fm):
            return recur_pos(model,args[0])
        elif lg.is_or(fm):
            subs = [recur_neg(model,arg) for arg in args]
            return lg.And(*subs) if all(x is not None for x in subs) else None
        elif lg.is_and(fm):
            for x in args:
                sub = recur_neg(model,x)
                if sub is not None:
                    return sub
            return None
        elif lg.is_implies(fm):
            lhs = recur_pos(model,args[0])
            rhs = recur_neg(model,args[1])
            return lg.And(lhs,rhs) if lhs is not None and rhs is not None else None
        # elif lg.is_iff(fm):
        #     truths = [model.get_value(arg) for arg in args]
        #     if truths[0].is_true() and truths[1].is_false():
        #         return And(recur_pos(model,args[0]),recur_neg(model,args[1]))
        #     if truths[0].is_false() and truths[1].is_true():
        #         return And(recur_neg(model,args[0]),recur_pos(model,args[1]))
        #     assert False
        elif lg.is_false(model.eval_quant_to_constant(fm)):
            if lg.is_forall(fm):
                return elim_ite(lg.Exists(fm.variables,negate(fm.args[0])),frozenset([]))
            if lg.is_exists(fm):
                return elim_ite(lg.ForAll(fm.variables,negate(fm.args[0])),frozenset([]))
            return negate(elim_ite(fm,frozenset([])))
        return None

    res = recur_pos(model,fmla,True)
    if res is None:
        print (fm)
        if lg.is_or(fm):
            print ([my_get_value(model,x) for x in fm.args()])
        print (my_get_value(model,fm))
        for y in list(reversed(list(conjunctive_partition(fm)))):
            if y.is_implies():
                if y.args[0].is_symbol() and lg.is_true(model.get_value(y.args[0])):
                    print ('action: {}'.format(y.args[0]))
                    for x in list(reversed(list(conjunctive_partition(y.args[1])))):
                        print ('conjunct: {}'.format(x))
                        if x.is_eq():
                            print ('left: {}'.format(model.get_value(x.args[0])))
                            print ('right: {}'.format(model.get_value(x.args[1])))
                        print ('truth: {}'.format(model.get_value(x)))
                        print ('conv: {}'.format(model.converter.convert(x)))
        with open("thing.model", "w") as f:
            f.write(model.z3_model.sexpr())
    assert res is not None
    if cnsts:
        res = lg.And(*(cnsts + [res]))
    return res


def convert_to_prestate(fm,existentials):
    rn = dict()
    for sym in ilu.used_symbols_ast(fm):
        if sym.name.startswith('__') :
            if not sym.name.startswith('__fml:') and not sym.name.startswith('__loc:')  or sym.name.startswith('__prm:'):
                nsym = sym.rename(lambda n: n[2:])
            else:
                nsym = sym.rename(lambda n: n[6:])
                existentials.append(nsym)
            if True or nsym in lg.sig.symbols:
                rn[sym] = nsym
                rn[nsym] = nsym.prefix('new_')
    return ilu.rename_ast(fm,rn)

def witnesses_to_free_variables(fm,existentials):
    rn = dict()
    for sym in ilu.used_symbols_ast(fm):
        if sym.name.startswith('@'):
            nsym = lg.Variable(sym.name[1:],sym.sort)
            existentials.append(nsym)
            rn[sym] = nsym
    return ilu.rename_ast(fm,rn)

# An explanation for a counterexample to induction is a state formula that:
#
# 1) is consistent with the proposed inductive invariant
#
# 2) implies that, for some valuation of the transition variables, the
#    proposed invariant is false after executing an action
#
# This function computes an explanation, given:
#
# 1) A transition relation 'tr'.
# 2) A final condition 'fcc'
# 3) A list of the proposed invariants 'invars'
# 4) A model representing a concrete counterexample to induction
# 5) A list in which to return the existential symbols (variables or constants)
#
# The tr is assumed to be a Clauses structure prepresenting the
# transition relation of some action, and the fcc is a formula
# representing the negation of one of the proposed invariants.  A
# model of 'tr & fcc' is a counterexample to induction for the given
# action and invariant. We require that the invariants are a prefix of
# the formula list in tr and that 'model' is a model of 'tr & fcc'. 
#
# The return value is an explanation. In this formula, the existential
# symbols should be considered existentially quantified. 
#

def show_clauses(cl):
    for x in cl.defs:
        print(f'def: {x}')
    for x in cl.fmlas:
        print(f'fmla: {x}')


def explain(tr,fcc,invars,model,existentials,universals):
    code_fmlas = ilu.Clauses(tr.fmlas[len(invars):],defs=tr.defs)
    imp = implicant(model,ilu.clauses_to_formula(fcc),code_fmlas)
    # print ('imp: {}'.format(imp))
    evars = set(x for x in ilu.used_symbols_in_order_ast(imp) if x.name.startswith('__fml:') or x.name.startswith('__loc:') or x.name.startswith('__ts0') or x.name.startswith('__prm:'))
    def E(sym):
        return sym in evars
    thing = elim_vars(imp,E)
    # print ('thing: {}'.format(thing))
    thing2 = convert_to_prestate(thing,existentials)
    # print ('thing2: {}'.format(thing2))
    thing3 = witnesses_to_free_variables(thing2,existentials)
    # print ('thing3: {}'.format(thing3))

    uvs = ilu.used_variables_ast(lg.And(*(code_fmlas.fmlas)))
    universals.extend(x for x in ilu.used_variables_in_order_ast(thing3) if x in uvs)
    return thing3

# Translate an explanation for a counterexample to induction into human-readable text.
# The parameters are:
#
# 1) The action 'action'
# 2) The violated invariant 'invar'
# 3) The explanation formula
#
# Returns the text.
#

def explanation_to_text(action,invar,expl,existentials,universals):
    res = []
    aname = action.name[4:] if action.name.startswith('ext:') else action.name
    res.append(f'The proposed invariants are not inductive. In particular, the following proposed invariant may not hold after executing the action `{aname}`.\n\n```\ninvariant {invar}\n```\n\n')
    ex = f', for some values of {",".join(x.name for x in existentials)}' if existentials else ''
    un = f', for all values of {",".join(x.name for x in universals)}' if universals else ''
    res.append(f'Suppose that, in the current state, the following conditions hold{ex}{un}:\n\n')
    for cond in conjunctive_partition(expl):
        res.append(f'- `{cond}`\n')
    res.append(f'\nThese conditions are consistent with the proposed invariants. However, if we execute action `{aname}`, the above invariant can become false in the subsequent state. Thus, the invariants are not inductive.\n\n')
    res.append('To correct this problem we need to either weaken the above invariant, strengthen another invariant, or propose an additional invariant.')
    return ''.join(res)
               

def check_vc(axioms,action,vc, postcond,preconds = []):
    fc = ilu.Clauses([postcond.formula ])
    fc.annot = ia.EmptyAnnotation()
    used_names = frozenset(x.name for x in list(lg.sig.symbols.values()))
    def witness(v):
        c = lg.Symbol('@' + v.name, v.sort)
        assert c.name not in used_names
        return c
    fcc = ilu.dual_clauses(fc, witness)
    clauses = ilu.and_clauses(vc,fcc)
    axioms = ilu.Clauses([x.formula for x in axioms])
    clauses = ilu.and_clauses(clauses,axioms)
    model = slv.get_small_model(clauses,lg.uninterpreted_sorts(),[])
    if model is not None:
        existentials = []
        universals = []
        expl = explain(vc,fcc,preconds,model,existentials,universals)
        text = explanation_to_text(action,postcond.formula,expl,existentials,universals)
        print ('=== BEGIN EXPLANATION ===')
        print (text)
        print ('=== END EXPLANATION ===')
        exit(1)
    
def expl(self,decls,proof):
    goal = decls[0]
    conc = pr.goal_conc(goal)
    axioms = pr.goal_prems(goal)
    decls = decls[1:]
    if not isinstance(conc,ivy_ast.TemporalModels) or not lg.is_true(conc.fmla):
        raise iu.IvyError(self,'vcgen tactic applies only to safety properties')
    model = conc.model
    init_vc = tr.make_vc(model.init)
    vcs = []
    for b in model.bindings:
        act = tm.binding_to_action(b)
        vcs.append(tr.make_vc(act,precond=model.invars+model.asms,postcond=None))
    for x in model.invars:
        print ('checking after init: {}'.format(x))
        check_vc(axioms,model.init,init_vc,x)
    for b,vc in zip(model.bindings,vcs):
        print ('checking action: {}'.format(b.name))
        for x in model.invars:
            print ('  checking postcond: {}'.format(x))
            check_vc(axioms,b,vc,x,model.invars+model.asms)
    exit(0)


pf.register_tactic('expl',expl)
