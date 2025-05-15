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

from ordered_set import OrderedSet
from collections import OrderedDict

# This tactic reduces a safety property to initiatation and consecution
# subgoals. TODO: we lose the annotation here, so we can't extract a
# trace. Need to add the annotation to the subgoals.

def vcgen(self,decls,proof):
    goal = decls[0]
    conc = pr.goal_conc(goal)
    decls = decls[1:]
    if not isinstance(conc,ivy_ast.TemporalModels) or not lg.is_true(conc.fmla):
        raise iu.IvyError(self,'vcgen tactic applies only to safety properties')
    model = conc.model
    goal1 = triple_to_goal(proof.lineno,'initiation',model.init,postcond=model.invars)
    goal2 = triple_to_goal(proof.lineno,'consecution',tm.env_action(model.bindings),
                           precond=model.invars+model.asms,postcond=model.invars)
    return [goal1,goal2] + decls[1:]

def vc_to_goal(lineno,name,vc,action):
    return pr.make_goal(lineno,name,[],lg.Not(ilu.clauses_to_formula(vc)),
                        annot=(action,vc.annot))

def triple_to_goal(lineno,name,action,precond=[],postcond=[]):
    vc = tr.make_vc(action,precond,postcond)
    return vc_to_goal(lineno,name,vc,action)

pf.register_tactic('vcgen',vcgen)
    
def skolemize(self,decls,proof):
    goal = decls[0]
    goal = pr.skolemize_goal(goal)
    return [goal] + decls[1:]

pf.register_tactic('skolemize',skolemize)

def skolemizenp(self,decls,proof):
    goal = decls[0]
    goal = pr.skolemize_goal(goal,prenex=False)
    return [goal] + decls[1:]

pf.register_tactic('skolemizenp',skolemizenp)

def tempind_fmla(fmla,cond,params,vs=[]):
    if lg.is_forall(fmla):
        return tempind_fmla(fmla.body,cond,params,vs+list(fmla.variables))
    if isinstance(fmla,lg.Implies):
        prem_vars = set(ilu.variables_ast(fmla.args[0]))
        conc = tempind_fmla(fmla.args[1],cond,params,[v for v in vs if v.name not in prem_vars])
        res = lg.Implies(fmla.args[0],conc)
        uvs = [v for v in vs if v.name in prem_vars]
        return lg.ForAll(uvs,res) if uvs else res
    if vs+params and isinstance(fmla,lg.Globally):
        body = lg.Implies(cond,fmla.body) if params else fmla.body
        gbly = fmla.clone([body])
        whencond = lg.Not(lg.ForAll(vs,fmla.body))
        return lg.ForAll(vs+params,lg.Or(gbly,lg.WhenOperator("next",body,whencond)))
    return lg.ForAll(vs,fmla) if vs else fmla
        
def apply_tempind(goal,proof):
    if proof.tactic_decls:
        raise iu.IvyError(proof,'tactic does not take declarations')
    vocab = pr.goal_vocab(goal,bound=True)
    defs = [pr.compile_expr_vocab(ivy_ast.Atom('=',x.args[0],x.args[1]),vocab) for x in proof.tactic_lets]
    conds = [lg.Equals(a.args[0],a.args[1]) for a in defs]
    cond = conds[0] if len(conds) ==1 else lg.normalized_and(*conds)
    params = list(a.args[0] for a in defs)
    conc = pr.goal_conc(goal)
    if not (goal.temporal or isinstance(conc,ivy_ast.TemporalModels)):
        raise iu.IvyError(proof,'proof goal is not temporal')
    if isinstance(conc,ivy_ast.TemporalModels):
        fmla = tempind_fmla(conc.fmla,cond,params)
        fmla = conc.clone([fmla])
    else:
        fmla = tempind_fmla(conc,cond,params)
    return pr.clone_goal(goal,pr.goal_prems(goal),fmla)
    
def tempind(self,decls,proof):
    goal = decls[0]
    goal = apply_tempind(goal,proof)
    return [goal] + decls[1:]
    
pf.register_tactic('tempind',tempind)

def tempcase_fmla(fmla,cond,vs,proof):
    if lg.is_forall(fmla):
        for v in fmla.variables:
            if v in vs:
                raise IvyError(proof,'variable ' + v + ' would be captured by quantifier')
        return fmla.clone([tempcase_fmla(fmla.body,cond,vs,proof)])
    if isinstance(fmla,lg.Implies):
        return fmla.clone([fmla.args[0],tempcase_fmla(fmla.args[1],cond,vs,proof)])
    if isinstance(fmla,lg.Globally):
        return lg.forall(vs,fmla.clone([lg.Implies(cond,fmla.body)]))
    return fmla

def apply_tempcase(goal,proof):
    if proof.tactic_decls:
        raise iu.IvyError(proof,'tactic does not take declarations')
    vocab = pr.goal_vocab(goal,bound=True)
    defs = [pr.compile_expr_vocab(ivy_ast.Atom('=',x.args[0],x.args[1]),vocab) for x in proof.tactic_lets]
    conds = [lg.Equals(a.args[0],a.args[1]) for a in defs]
    cond = conds[0] if len(conds) ==1 else lg.normalized_and(*conds)
    vs = list(a.args[0] for a in defs)
    conc = pr.goal_conc(goal)
    if isinstance(conc,ivy_ast.TemporalModels):
        fmla = tempcase_fmla(conc.fmla,cond,vs,proof)
        fmla = conc.clone([fmla])
    else:
        fmla = tempcase_fmla(conc,cond,vs,proof)
    subgoal = pr.clone_goal(goal,pr.goal_prems(goal),fmla)
    return subgoal
    
def tempcase(self,decls,proof):
    goal = decls[0]
    goal = apply_tempcase(goal,proof)
    return [goal] + decls[1:]
    
pf.register_tactic('tempcase',tempcase)

used_sorry = False

def sorry(self,decls,proof):
    global used_sorry
    used_sorry = True
    return decls[1:]

pf.register_tactic('sorry',sorry)


def flatten_structs(self,decls,proof):
    goal = decls[0]
    prems = pr.goal_prems(goal)
    conc = pr.goal_conc(goal)
    if not isinstance(conc,ivy_ast.TemporalModels):
        raise iu.IvyError(self,'flatten_structs applies only to invariance or temporal properties')
    model = conc.model
    fmla = conc.fmla
    syms = OrderedSet()
    bindings = [flatten_binding(bnd,syms) for bnd in model.bindings]
    init = flatten_action(model.init,syms)
    invars = [flatten_expr_simp(invar,syms) for invar in model.invars]
    asms = [flatten_expr_simp(asm,syms) for asm in model.asms]
    calls = model.calls
    # TODO: flatten prems
    defns = []
    # for defn in model.macros:
    #     lhs = flatten_expr(defn.formula.args[0],syms)
    #     rhs = flatten_expr(defn.formula.args[1],syms)
    #     for (lhslab,lhsval),(rhslab,rhsval) in zip(lhs.items(),rhs.items()):
    #         fdefn = defn.clone([defn.label.suffix(lhslab),lg.Definition(lhsval,rhsval)])
    #         defns.append(fdefn)
    axioms = [x.clone([x.label,lg.close_formula(flatten_expr_simp(x.formula,syms))]) for x in prems if pr.goal_is_property(x)]
    prems = [ivy_ast.ConstantDecl(sym) for sym in syms] + axioms
    # prems = [ivy_ast.ConstantDecl(sym) for sym in syms]
    model = tm.NormalProgram(bindings,defns,init,invars,asms,calls)
    # TODO: flatten property
    conc = ivy_ast.TemporalModels(model,conc.fmla)
    goal = pr.clone_goal(goal,prems,conc)
    return [goal] + decls[1:]



pf.register_tactic('flatten_structs',flatten_structs)

def field_types(sort):
    res = OrderedDict()
    if im.is_struct_sort(sort):
        for destr in im.sort_destructors(sort):
            fsort = destr.sort.rng
            for field,sort in field_types(fsort).items():
                fname = '.' + destr.name
                res[fname+field] = sort
    else:
        res[''] = sort
    return res

def flatten_expr(expr,syms,pref='',xargs=[]):
    if lg.is_macro(expr):
        return flatten_expr(lg.expand_macro(expr),syms,pref,xargs)
    if lg.is_app(expr):
        if im.is_destructor(expr.rep):
            if len(expr.args) > 1:
                xargs = list(xargs)
                for arg in expr.args[1:]:
                    xargs.append(flatten_expr(arg,syms))
            fname = '.' + expr.rep.name
            fields = flatten_expr(expr.args[0],syms,pref+fname,xargs)
            field = OrderedDict((x[len(fname):],y) for x,y in fields.items() if x.startswith(fname))
            return field
        if im.is_constructor(expr.rep):
            fields = OrderedDict()
            for destr,arg in zip(im.sort_destructors(expr.sort),expr.args):
                for fname,fvalue in flatten_expr(arg,syms).items():
                    fields['.' + destr.name + fname] = fvalue
            return fields
        args = []
        for arg in expr.args:
            args.extend(flatten_expr(arg,syms).values())
        args.extend(xargs)
        # print('args: {}'.format(args))
        dom = [arg.sort for arg in args]
        res = OrderedDict()
        for field,sort in field_types(expr.sort).items():
            if field.startswith(pref):
                fsort = lg.FunctionSort(*(dom + [sort])) if dom else sort
                name = expr.rep.name
                # HACK: can't change arity of polymorphic symbols, so rename them!
                if lg.symbol_is_polymorphic(expr.rep) and len(args) > len(expr.args):
                    name = '$' + name
                sym = lg.Symbol(name + field,fsort)
                if len(args) > len(expr.args) or field:
                    syms.add(sym)
                res[field] = sym(*args)
        return res
    if lg.is_eq(expr) or lg.is_def(expr):
        lhs,rhs = [flatten_expr(arg,syms) for arg in expr.args]
        try:
            return OrderedDict([('',lg.And(*[expr.clone([x,y]) for x,y in zip(lhs.values(),rhs.values())]))])
        except Exception as e:
            print ('expr: {}'.format(expr))
            raise e
    if lg.is_variable(expr):
        fields = OrderedDict()
        for field,sort in field_types(expr.sort).items():
            fields[field] = lg.Variable(expr.name + field, sort)
        return fields
    if lg.is_quantifier(expr):
        vars = list(flatten_expr_list(expr.variables,syms))
        arg = flatten_expr_simp(expr.args[0],syms)
        fields = OrderedDict()
        fields[''] = type(expr)(vars,arg)
        return fields
    args = [flatten_expr(arg,syms) for arg in expr.args]
    # TODO: handle quantifiers, named binders, numerals
    try:
        return OrderedDict([('',expr.clone([arg[''] for arg in args]))])
    except KeyError:
        print ('expr: {}'.format(expr))
        raise KeyError('')
    
def flatten_expr_simp(expr,sysms):
    return flatten_expr(expr,sysms)['']

def flatten_expr_list(exprs,syms):
    res = []
    for expr in exprs:
        res.extend(flatten_expr(expr,syms).values())
    return res
        
class SaveSyms(object):
    def __init__(self,syms,newsyms):
        self.saved = [x for x in newsyms if x in syms]
        self.syms = syms
        self.newsyms = newsyms
        syms.update(newsyms)
    def undo(self):
        for x in self.newsyms:
            self.syms.remove(x)
        self.syms.update(self.saved)
        

def flatten_action(act,syms):
    if isinstance(act,ia.AssignAction):
        lhs = flatten_expr(act.args[0],syms)
        rhs = flatten_expr(act.args[1],syms)
        asgns = [act.clone([x,y]) for x,y in zip(lhs.values(),rhs.values())]
        if len(asgns) == 1:
            return asgns[0]
        return ia.Sequence(*asgns).set_lineno(act.lineno)
    if isinstance(act,ia.LocalAction):
        localsyms = set()
        flatlocs = flatten_expr_list(act.args[:-1],localsyms)
        ss = SaveSyms(syms,flatlocs)
        arg = flatten_action(act.args[-1],syms)
        ss.undo()
        return act.clone(flatlocs + [arg])
    if isinstance(act,ia.CallAction):
        args = flatten_expr_list(act.args[0].args,syms)
        call = act.args[0].clone(args)
        returns = flatten_expr_list(act.args[1:],syms)
        return act.clone([call] + returns)
    args = []
    for arg in act.args:
        if isinstance(arg,ia.Action):
            arg = flatten_action(arg,syms)
        else:
            arg = flatten_expr_simp(arg,syms)
        args.append(arg)
    return act.clone(args)

def flatten_binding(bnd,syms):
    actt = bnd.action
    inputs = flatten_expr_list(actt.inputs,syms)
    outputs = flatten_expr_list(actt.outputs,syms)
    ss = SaveSyms(syms,inputs+outputs)
    stmt = flatten_action(actt.stmt,syms)
    ss.undo()
    actt = tm.ActionTerm(inputs,outputs,actt.labels,stmt)
    bnd = tm.ActionTermBinding(bnd.name,actt)
    return bnd

    
def macro_expand(self,decls,proof):
    goal = decls[0]
    prems = pr.goal_prems(goal)
    conc = pr.goal_conc(goal)
    if not isinstance(conc,ivy_ast.TemporalModels):
        raise iu.IvyError(self,'macro_expand applies only to invariance or temporal properties')
    model = conc.model
    fmla = conc.fmla
    defns = {}
    for x in prems:
        if pr.goal_is_property(x) and x.definition:
            y = lg.drop_universals(x.formula)
            defns[y.args[0].rep] = y
    prems = [x for x in prems if pr.goal_is_property(x) and not x.definition]
    bindings = [macro_expand_binding(bnd,defns) for bnd in model.bindings]
    init = macro_expand_action(model.init,defns)
    invars = [macro_expand_expr(invar,defns) for invar in model.invars]
    asms = [macro_expand_expr(asm,defns) for asm in model.asms]
    calls = model.calls
    prems = [macro_expand_expr(prem,defns) if pr.goal_is_property(prem) else prem for prem in prems]
    # prems = [ivy_ast.ConstantDecl(sym) for sym in defns]
    model = tm.NormalProgram(bindings,[],init,invars,asms,calls)
    conc = ivy_ast.TemporalModels(model,macro_expand_expr(conc.fmla,defns))
    goal = pr.clone_goal(goal,prems,conc)
    return [goal] + decls[1:]

def macro_expand_expr(expr,defns):
    args = [macro_expand_expr(arg,defns) for arg in expr.args]
    if lg.is_app(expr):
        if expr.rep in defns:
            defn = defns[expr.rep]
            rhs = macro_expand_expr(defn.rhs(),defns)
            subst = dict(zip(defn.lhs().args,args))
            return lu.substitute(rhs,subst)
    return expr.clone(args)
            
def macro_expand_action(act,defns):
    args = []
    for arg in act.args:
        if isinstance(arg,ia.Action):
            arg = macro_expand_action(arg,defns)
        else:
            arg = macro_expand_expr(arg,defns)
        args.append(arg)
    return act.clone(args)

def macro_expand_expr_list(exprs):
    return [macro_expand_expr(expr) for expr in exprs]

def macro_expand_binding(bnd,defns):
    actt = bnd.action
    stmt = macro_expand_action(actt.stmt,defns)
    actt = tm.ActionTerm(actt.inputs,actt.outputs,actt.labels,stmt)
    bnd = tm.ActionTermBinding(bnd.name,actt)
    return bnd

pf.register_tactic('macro_expand',macro_expand)
