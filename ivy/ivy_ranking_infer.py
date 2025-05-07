#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains a liveness to safety reduction based on
lexicographic relational rankings.

"""

from collections import defaultdict
from itertools import chain

from ivy.ivy_dafny_ast import AssignStmt

from .ivy_printer import print_module
from .ivy_actions import (AssignAction, Sequence, ChoiceAction,
                         AssumeAction, AssertAction, HavocAction,
                          concat_actions, Action, CallAction, IfAction)
from . import ivy_ast
from . import ivy_actions as iact
from . import logic as lg
from . import ivy_logic as ilg
from . import ivy_logic_utils as ilu
from . import logic_util as lu
from . import ivy_utils as iu
from . import ivy_temporal as itm
from . import ivy_proof as ipr
from . import ivy_module as im
from . import ivy_compiler
from . import ivy_theory as thy
from . import ivy_transrel as itr
from . import ivy_temporal
from . import ivy_vmt
from . import ivy_printer
#from .ivy_ranking import auto_hook 
#
# goal: as list of pairs (prog, fmla)
# goal_conc(goal) is conclusion
# goal_prem(goal) are premises of goals
# 
# sorted_tasks, tasks: 
# triggers: 
#   contain auxilliary relations we put into to the ivy ranking tactic
#   work_needed, work_progress, etc.
#


def renaming_hook(subs,tr,fcs):
    return tr.rename(dict((x,y) for (y,x) in subs.items()))



def ls2_g_to_globally(ast):
    def g2g(ast):
        if isinstance(ast,lg.NamedBinder) and ast.name == 'l2s_g':
            return lg.Globally(ast.environ,ast.body)
        return None
    res = ilu.expand_named_binders_ast(ast,g2g)
    return ilu.denormalize_temporal(res)

def auto_hook(tasks,triggers,subs,tr,fcs):
    tr = renaming_hook(subs,tr,fcs)
    tr.pp = ls2_g_to_globally
    # tr.hidden_symbols = temporal_and_l2s
    return tr


def instrument(prover, goal, sorted_tasks, triggers, tasks):
    # we assume one ranking in the proof
    sfx = sorted_tasks[0]

    # fairness conditions
    wp = tasks[sfx]['work_progress']
    rpred = ilg.Symbol('.r',wp.args[0].rep.sort) # symbol
    rdef = wp.args[1] # symbol rhs
    rdefsyms = ilu.symbols_ast(rdef) # free symbols in rdef
    rdefargs = wp.args[0].args # args in lhs

    defn_deps = defaultdict(list)


    conc = ipr.goal_conc(goal)
    model = conc.model.clone([])


    prem_defns = [prem for prem in ipr.goal_prems(goal)
                  if not isinstance(prem,ivy_ast.ConstantDecl)
                  and hasattr(prem,"definition") and prem.definition]

    for defn in list(prover.definitions.values()) + prem_defns:
        fml = ilg.drop_universals(defn.formula)
        for sym in iu.unique(ilu.symbols_ast(fml.args[1])):
            defn_deps[sym].append(fml.args[0].rep)
            

    def dependencies(syms):
        return iu.reachable(syms,lambda x: defn_deps.get(x) or []) 


    def instr_stmt(stmt,labels):

        # A call statement that modifies a monitored symbol as to be split
        # into call followed by assignment.


        #if (isinstance(stmt,CallAction)):
        #    actual_returns = stmt.args[1:]
        #    if any(sym in symprops or sym in symwhens
        #           or sym in symwaits for sym in actual_returns):
        #        return instr_stmt(stmt.split_returns(),labels)


        # first, recur on the sub-statements
        # --- instrument all arguments of each statement if an arg is a statement
        args = [instr_stmt(a,labels) if isinstance(a,Action) else a for a in stmt.args]
        res = stmt.clone(args)

        # now add any needed temporal events after this statement
        mods = set(dependencies(stmt.modifies()))

        # Now, for every property event, we update the property state (none in this case)
        # and also assert the property semantic constraint. 
        # only the event for r needs to be updated
        pre_events = []
        post_events = []
        if len(set(rdefsyms).intersection(mods)) > 0:
            asgn = AssignAction(rpred(*rdefargs), ilg.Or(rpred(*rdefargs), rdef)) # either current or previous value
             
        res =  iact.prefix_action(res,pre_events)
        res =  iact.postfix_action(res,post_events)
        stmt.copy_formals(res) # HACK: This shouldn't be needed
        return res

        # Instrument all the actions

    # add model 
    # need to clone the bindings 
    model.bindings = [b.clone([b.action.clone([instr_stmt(b.action.stmt,b.action.labels)])])
                      for b in model.bindings]
    
#    idle_action = concat_actions(*(
#        assume_g_axioms +  # could be added to model.asms
#        assume_when_axioms +
#        reset_w + 
#        add_consts_to_d
#    )).set_lineno(lineno)
#    idle_action.formal_params = []
#    idle_action.formal_returns = []
#    model.bindings.append(itm.ActionTermBinding('_idle',itm.ActionTerm([],[],[],idle_action)))
#    model.calls.append('_idle')
#    model.postconds['_idle']=postconds

    # create new goal 
    # HACK: reestablish invariant that shouldn't be needed

    for b in model.bindings:
        b.action.stmt.formal_params = b.action.inputs
        b.action.stmt.formal_returns = b.action.outputs

    # Change the conclusion formula to M |= true
    conc = ivy_ast.TemporalModels(model,lg.And())

    # Build the new goal
    prems = list(ipr.goal_prems(goal))
    non_temporal_prems = [x for x in prems if not (hasattr(x,'temporal') and x.temporal)]
    goal = ipr.clone_goal(goal,non_temporal_prems,conc)

    goal = ipr.remove_unused_definitions_goal(goal)

    goal.trace_hook = lambda tr,fcs: auto_hook(tasks,triggers,subs,tr,fcs)
    # goal.trace_hook = lambda tr,fcs: renaming_hook(subs,tr,fcs)

    # Return the new goal stack
    return goal 

    

    # TODO: return a modified goal

def infer(prover, goal, sorted_tasks, triggers, tasks):

    # Filter out the definitional axioms for the work_* predicates

    prems = [x for x in ipr.goal_prems(goal) if
             not(ipr.goal_is_property(x) and
                 any(s.name.startswith('work_')
                     for s in ilu.symbols_ast(x.formula)))]
    # clone existing goal with premises
    goal = ipr.clone_goal(goal,prems,ipr.goal_conc(goal))

    goal = instrument(prover, goal, sorted_tasks, triggers, tasks)

    # get the goal as a module (ignoring the temporal property)
    # the module is expected ivy_vmt
    mod = ivy_temporal.to_module(goal)

    # mod.labeled_axioms = [x for x in mod.labeled_axioms
    #                       if not any(s.name.startswith('work_')
    #                                  for s in ilu.symbols_ast(x.formula))]
    
    ivy_printer.print_module(mod)
    
    # sets mod as current module
    with mod:
        # get sorts and symbols of goal into current signature
#        vocab = ipr.goal_vocab(goal)
#        with ilg.WithSymbols(vocab.symbols):
#            with ilg.WithSorts(vocab.sorts):
                
                # Extract property in the form GF r -> G (p -> F q)

                sfx = sorted_tasks[0]
                work_start = triggers[sfx]['work_start'] 
                rhs = work_start.rhs() 
                assert isinstance(rhs,lg.Not) and isinstance(rhs.args[0],lg.Implies) and isinstance(rhs.args[0].args[1],lg.Eventually)
                p = rhs.args[0].args[0]
                q = rhs.args[0].args[1].args[0]
                ppred = ilg.Symbol('.p',work_start.defines().sort)
                pdef = ilg.Definition(ppred(*work_start.lhs().args),p)
                qpred = ilg.Symbol('.q',work_start.defines().sort)
                qdef = ilg.Definition(qpred(*work_start.lhs().args),q)
                wp = tasks[sfx]['work_progress']
                rpred = ilg.Symbol('.r',wp.args[0].rep.sort)
                rdef = ilg.Definition(rpred(*wp.args[0].args),wp.args[1])
                tds = [
                    ('react_p',pdef),
                    ('react_q',qdef),
                    ('react_r',rdef),
                ]

                # Convert to VMT without Array encoding (does not return)
                ivy_vmt.check_isolate(tagged_dfns = tds, use_array_encoding=False)
