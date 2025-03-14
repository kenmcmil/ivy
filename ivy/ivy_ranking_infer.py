#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains a liveness to safety reduction based on
lexicographic relational rankings.

"""

from collections import defaultdict
from itertools import chain

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

def infer(goal, sorted_tasks, triggers, tasks):

    # Filter out the definitional axioms for the work_* predicates

    prems = [x for x in ipr.goal_prems(goal) if
             not(ipr.goal_is_property(x) and
                 any(s.name.startswith('work_')
                     for s in ilu.symbols_ast(x.formula)))]
    goal = ipr.clone_goal(goal,prems,ipr.goal_conc(goal))

    # get the goal as a module (ignoring the temporal property)
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
