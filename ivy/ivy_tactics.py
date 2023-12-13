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
from . import ivy_logic_utils as lu
from . import ivy_proof as pr
from . import ivy_auto_inst

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
    return pr.make_goal(lineno,name,[],lg.Not(lu.clauses_to_formula(vc)),
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

