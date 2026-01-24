#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module performs exporting of liveness proof goals to a format called TDL (Transition Description Language)
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
from . import ivy_printer
from . import ivy_tdl
#from .ivy_ranking import auto_hook 



# instrument(...) instruments the transition system with history variables of
# certain transition variables used in the liveness property statement
#   goal: a list of pairs (prog, fmla)
#       goal_conc(goal) is conclusion
#       goal_prem(goal) are premises of goals
# 
#   sorted_tasks:
#   tasks: 
#   triggers: 
#       contain auxilliary relations we put into to the ivy ranking tactic
#       work_needed, work_progress, etc.
#



def instrument(prover, goal, sorted_tasks, triggers, tasks):
    # we assume one ranking in the proof
    sfx = sorted_tasks[0]

    # fairness conditions (work_progress -> .r history variable)
    wp = tasks[sfx]['work_progress']
    rpred = ilg.Symbol('.r',wp.args[0].rep.sort) # symbol
    rdef = wp.args[1] # symbol rhs
    rdefsyms = set(ilu.symbols_ast(rdef)) # free symbols in rdef
    rdefargs = wp.args[0].args # args in lhs

    # conclusion conditions (work_conclude -> .q history variable)
    # work_conclude tracks the predicate in the "eventually q" part of the liveness property
    # that needs to be observed at small-step boundaries
    wc = tasks[sfx].get('work_conclude', None)
    qpred = None
    qdef = None
    qdefsyms = set()
    qdefargs = ()
    if wc is not None:
        qpred = ilg.Symbol('.q', wc.args[0].rep.sort)
        qdef = wc.args[1]
        qdefsyms = set(ilu.symbols_ast(qdef))
        qdefargs = wc.args[0].args

    print("instrument --------------- ")
    print(' definitions')
    print('rdefsyms: ', rdefsyms)
    print('rdefargs: ', rdefargs)
    print('rdef: ', rdef)
    if wc is not None:
        print('qdefsyms: ', qdefsyms)
        print('qdefargs: ', qdefargs)
        print('qdef: ', qdef)
    print('-----')

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
        # Update .r when work_progress symbols are modified
        pre_events = []
        post_events = []
        if len(set(rdefsyms).intersection(mods)) > 0:
            print('updating .r')
            asgn = AssignAction(rpred(*rdefargs), ilg.Or(rpred(*rdefargs), rdef)) # .r := .r | work_progress
            post_events.append(asgn)

        # Update .q when work_conclude symbols are modified
        if qpred is not None and len(set(qdefsyms).intersection(mods)) > 0:
            print('updating .q')
            asgn = AssignAction(qpred(*qdefargs), ilg.Or(qpred(*qdefargs), qdef)) # .q := .q | work_conclude
            post_events.append(asgn)

        res =  iact.prefix_action(res,pre_events)
        res =  iact.postfix_action(res,post_events)
        stmt.copy_formals(res) # HACK: This shouldn't be needed
        return res

        # Instrument all the actions

    def instr_stmt_toplevel(stmt, labels, name):
        stmt = instr_stmt(stmt, labels)
        if name in model.calls:
            # Initialize history variables to false at the start of each exported action
            init_actions = [AssignAction(rpred(*rdefargs), ilg.Or())] # .r := false
            if qpred is not None:
                init_actions.append(AssignAction(qpred(*qdefargs), ilg.Or())) # .q := false
            return iact.prefix_action(stmt, init_actions)
        else:
            return stmt

    idle_action = concat_actions().set_lineno(0)
    idle_action.formal_params = []
    idle_action.formal_returns = []
    model.bindings.append(itm.ActionTermBinding('_idle',itm.ActionTerm([],[],[],idle_action)))
    model.calls.append('_idle')

    # add model
    # need to clone the bindings
    # Initialize history variables to false in the initial state
    init_actions = [AssignAction(rpred(*rdefargs), ilg.Or())] # .r := false
    if qpred is not None:
        init_actions.append(AssignAction(qpred(*qdefargs), ilg.Or())) # .q := false
    model.init = iact.prefix_action(model.init, init_actions)
    model.bindings = [b.clone([b.action.clone([instr_stmt_toplevel(b.action.stmt,b.action.labels, b.name)])])
                      for b in model.bindings]

    # create new goal
    # HACK: reestablish invariant that shouldn't be needed

    for b in model.bindings:
        b.action.stmt.formal_params = b.action.inputs
        b.action.stmt.formal_returns = b.action.outputs

    # Change the conclusion formula to M |= true
    conc = ivy_ast.TemporalModels(model,lg.And())

    # Build the new goal
    # In particular, add history variable symbols to premises
    prems = list(ipr.goal_prems(goal)) + [ivy_ast.ConstantDecl(rpred)]
    if qpred is not None:
        prems.append(ivy_ast.ConstantDecl(qpred))
    non_temporal_prems = [x for x in prems if not (hasattr(x,'temporal') and x.temporal)]
    goal = ipr.clone_goal(goal,non_temporal_prems,conc)

    goal = ipr.remove_unused_definitions_goal(goal)

    # Return the new goal stack
    return goal 

    

    # TODO: return a modified goal

def infer(prover, goal, sorted_tasks, triggers, tasks):

    # Filter out the definitional axioms for the work_* predicates
    print('----------initial goal-----')
    print(goal)
    print('---------------------------')

    prems = [x for x in ipr.goal_prems(goal) if
             not(ipr.goal_is_property(x) and
                 any(s.name.startswith('work_')
                     for s in ilu.symbols_ast(x.formula)))]
    # clone existing goal with premises
    goal = ipr.clone_goal(goal,prems,ipr.goal_conc(goal))

    goal = instrument(prover, goal, sorted_tasks, triggers, tasks)

    print('------------ goal --------')
    print(goal)
    print('---------------------------')
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

                # Handle work_conclude: if present, substitute work_conclude predicate with .q in q formula
                # This is needed because work_conclude (e.g., receiving.now) is only true at small-step
                # boundaries, so we need to use the history variable .q which captures whether
                # work_conclude was true during the action.
                wc = tasks[sfx].get('work_conclude', None)
                if wc is not None:
                    # Get the work_conclude predicate symbol and the .q history variable
                    wc_sym = wc.args[0].rep  # The symbol being defined (e.g., work_conclude)
                    wc_body = wc.args[1]     # The body of the definition (e.g., receiving.now)
                    qpred_hist = ilg.Symbol('.q', wc.args[0].rep.sort)

                    # Find the symbol in q that matches work_conclude's body and substitute with .q
                    # For example, if work_conclude = receiving.now, and q = receiving.now & receiving.value = X
                    # we substitute receiving.now with .q to get: q = .q & receiving.value = X
                    wc_body_syms = list(ilu.symbols_ast(wc_body))
                    if len(wc_body_syms) == 1 and ilg.is_app(wc_body) and len(wc_body.args) == 0:
                        # work_conclude is a simple nullary predicate (e.g., receiving.now)
                        wc_pred_sym = wc_body_syms[0]
                        # Substitute the predicate symbol with .q in q
                        q = lu.substitute(q, {wc_body: qpred_hist(*wc.args[0].args)})
                        print(f'Substituted {wc_body} with .q in q: {q}')

                ppred = ilg.Symbol('.p',work_start.defines().sort)
                pdef = ilg.Definition(ppred(*work_start.lhs().args),p)
                qpred = ilg.Symbol('.q',work_start.defines().sort)
                qdef = ilg.Definition(qpred(*work_start.lhs().args),q)
                wp = tasks[sfx]['work_progress']
                rpred = ilg.Symbol('.r',wp.args[0].rep.sort)
                # The fairness condition in the TDL output should be .r (the history variable),
                # not the original work_progress formula. The history variable .r captures
                # whether work_progress was true at any point during the current action,
                # which is what we need for the liveness-to-safety reduction.
                # We create a definition .r = .r so that rdef.rhs() returns .r itself.
                rdef = ilg.Definition(rpred(*wp.args[0].args), rpred(*wp.args[0].args))
                tds = [
                    ('react_p',pdef),
                    ('react_q',qdef),
                    ('react_r',rdef),
                ]

                # Convert to TDL using Array encoding (does not return)
                ivy_tdl.check_isolate(tagged_dfns = tds, use_array_encoding=True)
