#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
"""
This module contains a liveness to safety reduction that allows
proving temporal properties.


TODO's and open issues:

* automatically add conjectures of original system to the saved state

* automatically add basic conjectures about the monitor (e.g. states
  are mutually exclusive)

* handle multiple temporal properties

* temporal axioms?

* support nesting structure?

* review the correctness

* figure out the public_actions issue

* decide abotu normalizing the Boolean structure of temporal formulas,
  properties, waited formulas, and named binders (e.g. normalize ~~phi
  to phi?)

* a syntax for accessing Skolem constants and functions from the
  negation of temporal properties.


Useful definitions from ivy_module:
self.definitions = []  # TODO: these are actually "derived" relations
self.labeled_axioms = []
self.labeled_props = []
self.labeled_inits = []
self.labeled_conjs = []  # conjectures
self.actions = {}
self.public_actions = set()
self.initializers = [] # list of name,action pairs
self.sig
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

debug = iu.BooleanParameter("l2s_debug",False)

def forall(vs, body):
    return lg.ForAll(vs, body) if len(vs) > 0 else body

def exists(vs, body):
    return lg.Exists(vs, body) if len(vs) > 0 else body

def l2s_tactic(prover,goals,proof,tactic_name="l2s"):
    vocab = ipr.goal_vocab(goals[0])
    with ilg.WithSymbols(vocab.symbols):
        with ilg.WithSorts(vocab.sorts):
            return l2s_tactic_int(prover,goals,proof,tactic_name)

# This version includes all the auxiliary state, not just what is
# referred to in the invariant. It is intended to model checking, where
# the user doesn't give an invariant. Also, for model checking, we hide the
# auxiliary symbols.

def l2s_tactic_full(prover,goals,proof):
    goals = l2s_tactic(prover,goals,proof,"l2s_full")
    goals[0].trace_hook = trace_hook
    return goals

def l2s_tactic_auto(prover,goals,proof):
    goals = l2s_tactic(prover,goals,proof,proof.tactic_name)
    return goals

# This hides the auxiliary variables in an error trace. Also, we
# mark the loop start state.

def trace_hook(tr,fcs):
    # tr.hidden_symbols = lambda sym: sym.name.startswith('l2s_') or sym.name.startswith('_old_l2s_')
    for idx,state in enumerate(tr.states):
        for c in state.clauses.fmlas:
            s1,s2 = list(map(str,c.args))
            if s1 == 'l2s_saved' and s2 == 'true':
                tr.states[0 if idx == 0 else idx-1].loop_start = True
                return tr
    print("failed to find loop start!")
    return tr
    
def l2s_tactic_int(prover,goals,proof,tactic_name):
    full = tactic_name == "l2s_full"
    mod = im.module
    goal = goals[0]                  # pick up the first proof goal
    lineno = iu.Location("nowhere",0)
    conc = ipr.goal_conc(goal)       # get its conclusion
    if not isinstance(conc,ivy_ast.TemporalModels):
        raise iu.IvyError(proof,'proof goal is not temporal')
    model = conc.model.clone([])
    fmla = conc.fmla

    if proof.tactic_lets:
        raise iu.IvyError(proof,'tactic does not take lets')

    # Get all the temporal properties from the prover environment as assumptions
    
    # Add all the assumed invariants to the model

    assumed_gprops = [x for x in prover.axioms if not x.explicit and x.temporal and isinstance(x.formula,lg.Globally)]
    model.asms.extend([p.clone([p.label,p.formula.args[0]]) for p in assumed_gprops])

    temporal_prems = [x for x in ipr.goal_prems(goal) if hasattr(x,'temporal') and x.temporal] + [
        x for x in prover.axioms if not x.explicit and x.temporal]
    if temporal_prems:
        fmla = ilg.Implies(ilg.And(*[x.formula for x in temporal_prems]),fmla)

    # Split the tactic parameters into invariants and definitions

    tactic_invars = [inv for inv in proof.tactic_decls if not isinstance(inv,ivy_ast.DerivedDecl)]
    tactic_defns = [inv for inv in proof.tactic_decls if isinstance(inv,ivy_ast.DerivedDecl)]

    # TRICKY: We postpone compiling formulas in the tactic until now, so
    # that tactics can introduce their own symbols. But, this means that the
    # tactic has to be given an appropriate environment label for any temporal
    # operators. Here, we compile the invariants in the tactic, using the given
    # label.

    # compiled definitions into goal

    for defn in tactic_defns:
        goal = ipr.compile_definition_goal_vocab(defn,goal) 

    # compile definition dependcies

    defn_deps = defaultdict(list)

    prem_defns = [prem for prem in ipr.goal_prems(goal)
                  if not isinstance(prem,ivy_ast.ConstantDecl)
                  and hasattr(prem,"definition") and prem.definition]

    for defn in list(prover.definitions.values()) + prem_defns:
        fml = ilg.drop_universals(defn.formula)
        for sym in iu.unique(ilu.symbols_ast(fml.args[1])):
            defn_deps[sym].append(fml.args[0].rep)
            
    def dependencies(syms):
        return iu.reachable(syms,lambda x: defn_deps.get(x) or [])

#    assert hasattr(proof,'labels') and len(proof.labels) == 1
#    proof_label = proof.labels[0]
    proof_label = ""
#    print 'proof label: {}'.format(proof_label)
    invars = [ilg.label_temporal(ipr.compile_with_goal_vocab(inv,goal),proof_label) for inv in tactic_invars]
#    invars = [ilg.label_temporal(inv.compile(),proof_label) for inv in proof.tactic_decls]


    l2s_waiting = lg.Const('l2s_waiting', lg.Boolean)
    l2s_frozen = lg.Const('l2s_frozen', lg.Boolean)
    l2s_saved = lg.Const('l2s_saved', lg.Boolean)
    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_a = lambda sort: lg.Const('l2s_a',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, proof_label, t)
    l2s_s = lambda vs, t: lg.NamedBinder('l2s_s', vs, proof_label, t)
    l2s_g = lambda vs, t, environ: lg.NamedBinder('l2s_g', vs, environ, t)
    old_l2s_g = lambda vs, t, environ: lg.NamedBinder('_old_l2s_g', vs, environ, t)
    l2s_init = lambda vs, t: lg.NamedBinder('l2s_init', tuple(vs), proof_label, t)
    l2s_when = lambda name, vs, t: lg.NamedBinder('l2s_when'+name, vs, proof_label, t)
    l2s_old = lambda vs, t: lg.NamedBinder('l2s_old', vs, proof_label, t)

    finite_sorts = set()
    for name,sort in ilg.sig.sorts.items():
        if thy.get_sort_theory(sort).is_finite() or name in mod.finite_sorts or full:
            finite_sorts.add(name)
    uninterpreted_sorts = [s for s in list(ilg.sig.sorts.values()) if type(s) is lg.UninterpretedSort and s.name not in finite_sorts]

    # Add invariants for l2s_auto tactic

    if tactic_name.startswith("l2s_auto"):

        def dict_put(dct,sfx,name,dfn):
            if sfx not in dct:
                dct[sfx] = dict()
            dct[sfx][name] = dfn

        def get_aux_defn(name,dct):
            for prem in ipr.goal_prems(goal):
                if not isinstance(prem,ivy_ast.ConstantDecl) and hasattr(prem,"definition") and prem.definition:
                    tmp = prem.formula;
                    if isinstance(tmp,lg.ForAll):
                        tmp = tmp.body
                    dname = tmp.args[0].rep.name
                    if dname.startswith(name):
                        freevs = list(ilu.variables_ast(prem.formula))
                        if freevs:
                            raise iu.IvyError(proof,'free symbol {} not allowed in definition of {}'.format(freevs[0],dname))
                        lhs = (lg.Const(name,tmp.args[0].rep.sort))(*tmp.args[0].args)
                        dfn = tmp.clone([lhs,tmp.args[1]])
                        sfx = dname[len(name):]
                        dict_put(dct,sfx,name,dfn)

        tasks = dict()
        triggers = dict()

        get_aux_defn('work_created',tasks)
        get_aux_defn('work_needed',tasks)
        get_aux_defn('work_done',tasks)
        get_aux_defn('work_progress',tasks)
        get_aux_defn('work_end',tasks)
        get_aux_defn('work_invar',tasks)
        if tactic_name in ["l2s_auto5"]:
            get_aux_defn('work_helpful',tasks)
        get_aux_defn('work_start',triggers)
        
        def get_work_was_done(defn,work_done):
            done_args = work_done.args[0].args
            subs = dict(zip(defn.args[0].args,done_args))
            defnsubs = lu.substitute(defn.args[1],subs)
            if tactic_name not in ["l2s_auto3","l2s_auto4","l2s_auto5"]:
                was_done = l2s_s(done_args,work_done.args[1])(*done_args)
                tmp = lg.Implies(defnsubs,was_done)
            else:
                tmp = l2s_s(done_args,lg.Implies(defnsubs,work_done.args[1]))(*done_args)
            return tmp

        # create a substituion replacing work_done[sfx](X) with
        # $was (work_needed[sfx](X) -> work_done[sfx](X)). This will
        # be used to preprocess "work_helpful".
        
        # depends_subst = dict()
        # for sfx in tasks:
        #     if 'work_needed' in tasks[sfx] and 'work_done' in tasks[sfx]:
        #         work_needed = tasks[sfx]['work_needed']
        #         work_done = tasks[sfx]['work_done']
        #         print ('foo: {}'.format(get_work_was_done(work_needed,work_done)))
        #         rhs = get_work_was_done(work_needed,work_done).rep
        #         lhs = ilg.Symbol('work_done'+sfx,work_done.args[0].rep.sort)
        #         depends_subst[lhs] = rhs
        #         print ('foo: {} = {}'.format(lhs,rhs))
                
        waiting_for_start = lg.Or(*[l2s_w((),triggers[sfx]['work_start'].args[1]) for sfx in triggers])
        not_all_done_preds = []
        not_all_was_done_preds = []
        sched_exists_preds = []

        sorted_tasks = list(sorted(x for x in tasks))

        # infer some predicates

        if sorted_tasks:
            sfx = sorted_tasks[0]
            if not(sfx in triggers and 'work_start' in triggers[sfx]):
                gfmla = fmla
                while isinstance(gfmla,lg.Implies):
                    gfmla = gfmla.args[1]
                if isinstance(gfmla,lg.Globally):
                    work_start = ilg.Definition(ilg.Symbol('work_start'+sfx,lg.Boolean),lg.Not(gfmla.body))
                    dict_put(triggers,sfx,'work_start',work_start)
        
        if tactic_name in ["l2s_auto5"]:
            for idx,sfx in enumerate(sorted_tasks):
                task = tasks[sfx]
                if 'work_needed' in task and 'work_done' not in task:
                    work_needed = task['work_needed']
                    lhs = work_needed.args[0]
                    work_done = ilu.Definition(ilu.Symbol('work_done'+sfx,lhs.rep.sort)(*lhs.args),lg.false)
                    dict_put(tasks,sfx,'work_done',work_done)

        for sfx in tasks:
            for name in ['work_created','work_needed','work_done','work_progress']:
                if name not in tasks[sfx]:
                    raise iu.IvyError(proof,"tactic ls_auto requires a definition of " + name + sfx)

        # generate the l2s invariants

        for idx,sfx in enumerate(sorted_tasks):
            task = tasks[sfx] 
            work_created = task['work_created']
            work_needed = task['work_needed']
            work_done = task['work_done']
            work_progress = task['work_progress']
            work_end = (tasks[sfx]['work_end']
                            if sfx in tasks and 'work_end' in tasks[sfx] else None)
            work_invar = (tasks[sfx]['work_invar']
                            if sfx in tasks and 'work_invar' in tasks[sfx] else None)
            work_helpful = (tasks[sfx]['work_helpful']
                            if sfx in tasks and 'work_helpful' in tasks[sfx] else None)
            work_start = (triggers[sfx]['work_start']
                            if sfx in triggers and 'work_start' in triggers[sfx] else None)

            # work_created, work_needed and work_done must have same sort
           
            if work_created.args[0].rep.sort != work_needed.args[0].rep.sort:
                raise iu.IvyError(proof,"work_created"+sfx+" and work_needed"+sfx+" must have same signature")
            if work_created.args[0].rep.sort != work_done.args[0].rep.sort:
                raise iu.IvyError(proof,"work_created"+sfx+" and work_done"+sfx+" must have same signature")
            if work_helpful is not None and work_helpful.args[0].rep.sort != work_progress.args[0].rep.sort:
                raise iu.IvyError(proof,"work_helpful"+sfx+" and work_progress"+sfx+" must have same signature")
            if work_invar is not None and work_invar.args[0].args:
                raise iu.IvyError(proof,"work_invar"+sfx+" may not have arguments")


           
            # says that all elements used in defn are in l2s_d

            def all_d(defn):
                cons = [l2s_d(var.sort)(var) for var in defn.args[0].args if var.sort.name not in finite_sorts]
                return lg.Implies(defn.args[1],lg.And(*cons))

            # says that all elements used in defn are in l2s_a

            def all_a(defn):
                cons = [l2s_a(var.sort)(var) for var in defn.args[0].args if var.sort.name not in finite_sorts]
                return lg.Implies(defn.args[1],lg.And(*cons))

            def all_created(defn):
                subs = dict(zip(defn.args[0].args,work_created.args[0].args))
                return lg.Implies(lu.substitute(defn.args[1],subs),work_created.args[1])

            def get_is_done(defn):
                subs = dict(zip(defn.args[0].args,work_done.args[0].args))
                return lg.Implies(lu.substitute(defn.args[1],subs),work_done.args[1])

            def not_all_done(defn,skip=0):
                subs = dict(zip(defn.args[0].args,work_done.args[0].args))
                tmp = lg.Implies(lu.substitute(defn.args[1],subs),work_done.args[1])
                if work_end is not None:
                    subs = dict(zip(work_end.args[0].args,work_done.args[0].args))
                    tmp = lg.Implies(lu.substitute(work_end.args[1],subs),tmp)
                if work_invar is not None:
                    tmp = lg.Implies(work_invar.args[1],tmp)
                tmp = lg.Not(forall(work_done.args[0].args[skip:],tmp))
                if tactic_name in ["l2s_auto2","l2s_auto3","l2s_auto4","l2s_auto5"]:
                    tmp = lg.Or(lg.Not(not_waiting_for_start),tmp)
                return tmp

            def get_was_done(defn):
                return get_work_was_done(defn,work_done)

            def not_all_was_done(defn,skip=0):
                tmp = get_was_done(defn)
                return lg.Not(forall(work_done.args[0].args[skip:],tmp))

            def get_depends():
                # prep = ipr.apply_match(depends_subst,work_helpful.args[1])
                # print ('prep: {}'.format(prep))
                subs = dict(zip(work_helpful.args[0].args,work_progress.args[0].args))
                # print ('subs: {}'.format(subs))
                prep = lu.substitute(work_helpful.args[1],subs)
                # print ('prep: {}'.format(prep))
                return prep

            # invariant l2s_needed_when_start
            #
            # This says that if we have seen the start condition
            # then every element in the work_needed set is in work_created. 


            def eventually_start_task(work_start):
                if work_start is None:
                    return lg.And()
                trigf = work_start
                evf = lg.Eventually(proof_label,trigf.args[1])
                vs = trigf.args[0].args
                return forall(vs,l2s_init(vs,evf)(*vs))
                
            def eventually_start():
                return eventually_start_task(work_start)

            not_waiting_for_start = lg.And()
            if work_start is not None:
                not_waiting_for_start = lg.And(eventually_start(),
                                               lg.Or(lg.Not(l2s_waiting),
                                                     lg.Not(l2s_w((),work_start.args[1]))))
            # tmp = lg.Implies(lg.And(l2s_waiting,lg.Not(waiting_for_start)),all_d(work_needed))
            if tactic_name not in ["l2s_auto5"]:
                tmp = lg.Implies(not_waiting_for_start,all_created(work_needed))
            else:
                tmp = lg.Implies(not_waiting_for_start,all_d(work_needed))
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_needed_when_start"+sfx),tmp).sln(proof.lineno))

            # invariant ls2_created
            #
            # This invariant says that every element in the work_created predicate is in l2s_d
            # 

            tmp = all_d(work_created)
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_created"+sfx),tmp).sln(proof.lineno))

            # invariant l2s_needed_are_frozen

            if tactic_name not in ["l2s_auto4","l2s_auto5"]:
                tmp = lg.Implies(lg.And(eventually_start(),lg.Not(l2s_waiting)),all_a(work_needed))
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_needed_are_frozen"+sfx),tmp).sln(proof.lineno))
            else:
                tmp = lg.Not(get_is_done(work_needed))
                cons = [l2s_a(var.sort)(var) for var in work_done.args[0].args if var.sort.name not in finite_sorts]
                tmp = lg.Implies(tmp,lg.And(*cons))
                tmp = lg.Implies(lg.And(eventually_start(),lg.Not(l2s_waiting)),tmp)
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_needed_are_frozen"+sfx),tmp).sln(proof.lineno))
                tmp = lg.Not(get_was_done(work_needed)) 
                tmp = lg.Implies(tmp,lg.And(*cons))
                tmp = lg.Implies(lg.And(eventually_start(),l2s_saved),tmp)
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_needed_were_frozen"+sfx),tmp).sln(proof.lineno))
            
            # invariant done_implies_created

            if tactic_name not in ["l2s_auto3","l2s_auto4","l2s_auto5"]:
                subs = dict(zip(work_done.args[0].args,work_created.args[0].args))
                tmp = lg.Implies(lu.substitute(work_done.args[1],subs),work_created.args[1])
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_done_implies_created"+sfx),tmp).sln(proof.lineno))

            # invariant needed_implies_created

            if tactic_name not in ["l2s_auto5"]:
                subs = dict(zip(work_needed.args[0].args,work_created.args[0].args))
                tmp = lg.Implies(not_waiting_for_start,lg.Implies(lu.substitute(work_needed.args[1],subs),work_created.args[1]))
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_needed_implies_created"+sfx),tmp).sln(proof.lineno))

            # invariant done_implies_needed

            # subs = dict(zip(work_done.args[0].args,work_needed.args[0].args))
            # tmp = lg.Implies(lu.substitute(work_done.args[1],subs),work_needed.args[1])
            # tmp = lg.Implies(not_waiting_for_start,tmp)
            # invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_done_implies_needed"+sfx),tmp).sln(proof.lineno))

            # invariant l2s_work_preserved

            done_args = work_done.args[0].args
            if tactic_name not in ["l2s_auto4","l2s_auto5"]:
                was_done = l2s_s(done_args,work_done.args[1])(*done_args)
                is_done = work_done.args[1]
            else:
                was_done = get_was_done(work_needed)
                is_done = get_is_done(work_needed)
            tmp = lg.Implies(lg.And(l2s_saved,was_done),is_done)
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_work_preserved"+sfx),tmp).sln(proof.lineno))

            def next_task_has_trigger():
                return idx + 1 < len(sorted_tasks) and sorted_tasks[idx+1] in triggers

            def next_task_not_triggered():
                next_sfx = sorted_tasks[idx+1]
                trigf = triggers[next_sfx]['work_start']
                return lg.Not(eventually_start_task(trigf))

            # invariant l2s_progress_made

            if work_start is not None:
                not_all_was_done_preds = []
            progress_args = work_progress.args[0].args
            if tactic_name not in ["l2s_auto5"] and tuple(progress_args) != tuple(done_args[:len(progress_args)]):
                raise iu.IvyError(proof,"work_progess parameters must be a prefix of work_done parameters")
            waiting_for_progress = l2s_w(progress_args,work_progress.args[1])
            if tactic_name != "l2s_auto3":
                if tactic_name in ["l2s_auto5"]:
                    nad = get_depends()
                    nad = l2s_s(progress_args,nad)(*progress_args)
                    if next_task_has_trigger():
                        nad = lg.And(next_task_not_triggered(),nad)
                    tmp = lg.Implies(
                        lg.And(l2s_saved,eventually_start(),
                               exists(progress_args,nad),
                               not_all_was_done(work_needed),
                               forall(progress_args,
                                      lg.Implies(nad,lg.Not(waiting_for_progress(*progress_args))))),
                        exists(done_args,lg.And(lg.Not(was_done),is_done)))
                elif progress_args or len(tasks) > 1:
                    nad = lg.And(not_all_was_done(work_needed,len(progress_args)),lg.Not(lg.Or(*not_all_was_done_preds)))
                    if next_task_has_trigger():
                        nad = lg.And(next_task_not_triggered(),nad)
#                    qt = exists if tactic_name in ["l2s_auto5"] else forall
                    tmp = forall(progress_args,
                                 lg.Implies(lg.And(nad,l2s_saved,eventually_start(),
                                                   lg.Not(waiting_for_progress(*progress_args))),
                                            exists(done_args[len(progress_args):],
                                                   lg.And(lg.Not(was_done),is_done))))
                else:
                    tmp = lg.Implies(lg.And(l2s_saved,
                                            lg.Not(waiting_for_progress)),
                                     exists(done_args,lg.And(lg.Not(was_done),is_done)))
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_progress_made"+sfx),tmp).sln(proof.lineno))
            # invariant l2s_progress_invar

            tmp = lg.Globally(proof_label,lg.Eventually(proof_label,work_progress.args[1]))
            tmp = lg.Implies(l2s_init(progress_args,tmp)(*progress_args),tmp)
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_progress_invar"+sfx),tmp).sln(proof.lineno))
            
            # invariant l2s_not_all_done
            #
            # This says that if we have seen the start condition, there is always some work left to do.
            # This is an *or* over all of the tasks, that is, at all times there must be *some*
            # task that has work left to do.
            
            # tmp = lg.Implies(lg.Or(lg.Not(l2s_waiting),lg.Not(waiting_for_start)),not_all_done(work_needed))
            not_all_done_preds.append(not_all_done(work_needed))
            if idx + 1 < len(sorted_tasks):
                next_sfx = sorted_tasks[idx+1]
                if next_sfx in triggers:
                    trigf = triggers[next_sfx]['work_start']
                    tmp = lg.Implies(lg.Not(eventually_start_task(trigf)),lg.Or(*not_all_done_preds))
                    invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_not_all_done"+sfx),tmp).sln(proof.lineno))
                    not_all_done_preds = []

            not_all_was_done_preds.append(not_all_was_done(work_needed))

            # invariant l2s_sched_stable

            if tactic_name in ["l2s_auto5"]:
                nad = get_depends()
                was_nad = l2s_s(progress_args,nad)(*progress_args)
                tmp = forall(progress_args,
                             lg.Implies(lg.And(was_nad,l2s_saved,eventually_start(),waiting_for_progress(*progress_args)),
                                        nad))
                invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_sched_stable"+sfx),tmp).sln(proof.lineno))
                
                # keep track of schedulers
                
                tmp = exists(progress_args,was_nad)
                sched_exists_preds.append(tmp)

        tmp = lg.Or(*not_all_done_preds)
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_not_all_done"),tmp).sln(proof.lineno))

        if tactic_name in ["l2s_auto5"]:
            tmp = lg.Implies(lg.And(l2s_saved,eventually_start()),lg.Or(*sched_exists_preds))
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_sched_exists"),tmp).sln(proof.lineno))

        def init_globally(prop,res,pos=True):
            if isinstance(prop,(lg.Globally,lg.Eventually)):
                known_inits.add(prop)
            if pos and isinstance(prop,lg.Globally):
                res.append(prop)
                init_globally(prop.args[0],res,pos)
            elif not pos and isinstance(prop,lg.Eventually):
                arg = prop.args[0]
                res.append(lg.Not(prop))
                init_globally(prop.args[0],res,pos)
            elif pos and isinstance(prop,lg.Eventually):
                arg = prop.args[0]
                vs = tuple(ilu.variables_ast(prop.args[0]))
                res.append(lg.Implies(lg.Not(prop),
                                      lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,arg)(*vs)))))
                if isinstance(arg,lg.Globally) or isinstance(arg,lg.Not) and isinstance(arg.args[0],lg.Eventually):
                    res.append(lg.Implies(lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,arg)(*vs))),
                                          arg))
                res.append(l2s_init(vs,prop)(*vs))
            elif not pos and isinstance(prop,lg.Globally):
                arg = prop.args[0]
                vs = tuple(ilu.variables_ast(prop.args[0]))
                res.append(lg.Implies(prop,
                                      lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,lg.Not(arg))(*vs)))))
                if isinstance(arg,lg.Eventually) or isinstance(arg,lg.Not) and isinstance(arg.args[0],lg.Globally):
                    res.append(lg.Implies(lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,lg.Not(arg))(*vs))),
                                          lg.Not(arg)))
                res.append(l2s_init(vs,lg.Not(prop))(*vs))
                    
            elif not pos and isinstance(prop,lg.Implies):
                init_globally(prop.args[0],res,not pos)
                init_globally(prop.args[1],res,pos)
            elif pos and isinstance(prop,lg.And):
                for arg in prop.args:
                    init_globally(arg,res,pos)
            elif not pos and isinstance(prop,lg.Or):
                for arg in prop.args:
                    init_globally(arg,res,pos)
            elif pos and isinstance(prop,lg.ForAll):
                init_globally(prop.args[0],res,pos)
            elif not pos and isinstance(prop,lg.Exists):
                init_globally(prop.args[0],res,pos)
            elif isinstance(prop,lg.Not):
                init_globally(prop.args[0],res,not pos)

        ninvs = []
        known_inits = set()
        init_globally(fmla,ninvs,False)

        for trig in triggers:
            trigf = triggers[trig]['work_start']
            arg = trigf.args[1]
            evf = lg.Eventually(proof_label,arg)
            vs = trigf.args[0].args
            initf = l2s_init(vs,evf)(*vs)
            ninvs.append(lg.Or(initf,lg.Not(evf)))
            ninvs.append(lg.Implies(lg.And(initf,lg.Not(evf)),
                                   lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,arg)(*vs)))))
#            if isinstance(arg,lg.Globally) or isinstance(arg,lg.Not) and isinstance(arg.args[0],lg.Eventually) or isinstance(arg,lg.NamedBinder) and arg.name == 'l2s_g':
#                ninvs.append(lg.Implies(lg.And(initf,lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,arg)(*vs)))),
#                                      arg))
            tinvs = []
            init_globally(arg,tinvs,True)
            for tinv in tinvs:
                ninvs.append(lg.Implies(lg.And(initf,lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w(vs,arg)(*vs)))),
                                        tinv))
                
        for i,ninv in enumerate(ninvs):
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_globally_"+str(i)),ninv).sln(proof.lineno))

        tmp = lg.Or(l2s_waiting,l2s_frozen,l2s_saved)
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_status_0"),tmp).sln(proof.lineno))
            
        tmp = lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_frozen))
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_status_1"),tmp).sln(proof.lineno))

        tmp = lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_saved))
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_status_2"),tmp).sln(proof.lineno))

        tmp = lg.Or(lg.Not(l2s_frozen),lg.Not(l2s_saved))
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_status_3"),tmp).sln(proof.lineno))
        
        tmp = lg.And(*list(l2s_d(s)(c)
                           for s in uninterpreted_sorts
                           if s.name not in finite_sorts
                           for c in list(ilg.sig.symbols.values()) if c.sort == s))
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_consts_d"),tmp).sln(proof.lineno))

        iinvs = []

        def add_ini_invar(cond,fmla):
            if cond not in known_inits:
                iinvs.append(fmla)
                known_inits.add(cond)

        def convert_to_init(fmla):
            if isinstance(fmla,(lg.And,lg.Or,lg.Not,lg.Implies,lg.Iff,lg.ForAll,lg.Exists)):
                return fmla.clone([convert_to_init(arg) for arg in fmla.args])
            vs = tuple(iu.unique(ilu.variables_ast(fmla)))
            ini =  l2s_init(vs,fmla)(*vs)
            if isinstance(fmla,lg.Globally):
                add_ini_invar(fmla,lg.Implies(ini,fmla))
            if isinstance(fmla,lg.Eventually):
                add_ini_invar(fmla,lg.Implies(fmla,ini))
            return ini

        tmp = lg.Not(convert_to_init(fmla))
        for i,ninv in enumerate(iinvs):
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_init_glob_"+str(i)),ninv).sln(proof.lineno))
        
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("neg_prop_init"),tmp).sln(proof.lineno))
                          
        prems = list(x for x in ipr.goal_prems(goal) if ipr.goal_is_property(x))
        
        winvs = []
        for tmprl in list(iu.unique(ilu.temporals_asts(invars+prems))):
            if isinstance(tmprl,lg.WhenOperator):
                if tmprl.name == 'first':
                    nws = lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w((),tmprl.t2)))
                    tmp = lg.Implies(lg.Not(nws),lg.Eq(tmprl,lg.WhenOperator('next',tmprl.t1,tmprl.t2)))
                    tmp = lg.Implies(l2s_init((),lg.Eventually(proof_label,tmprl.t2)),tmp)
                    winvs.append(tmp)

        for i,winv in enumerate(winvs):
            invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_when_"+str(i)),winv).sln(proof.lineno))


        print ('--- l2s_auto invariants ---')
        for inv in invars:
            print('invariant {}'.format(inv))
        print ('---------------------------')


        
    # Desugar the invariants.
    #
    # $was. phi(V)  -->   l2s_saved & ($l2s_s V.phi(V))(V)
    # $happened. phi --> l2s_saved & ~($l2s_w V.phi(V))(V)
    #
    # We push $l2s_s inside propositional connectives, so that the saved
    # values correspond to atoms. Otherwise, we would have redundant
    # saved values, for example p(X) and ~p(X).

    def desugar(expr):
        def apply_was(expr):
            if isinstance(expr,(lg.And,lg.Or,lg.Not,lg.Implies,lg.Iff)):
                return expr.clone([apply_was(a) for a in expr.args])
            vs = list(iu.unique(ilu.variables_ast(expr)))
            return l2s_s(vs,expr)(*vs)
        def apply_happened(expr):
            vs = list(iu.unique(ilu.variables_ast(expr)))
            return lg.Not(l2s_w(vs,expr)(*vs))
        if ilg.is_named_binder(expr):
            if expr.name == 'was':
                if len(expr.variables) > 0:
                    raise iu.IvyError(expr,"operator 'was' does not take parameters")
                return lg.And(l2s_saved,apply_was(expr.body))
            elif expr.name == 'happened':
                if len(expr.variables) > 0:
                    raise iu.IvyError(expr,"operator 'happened' does not take parameters")
                return lg.And(l2s_saved,apply_happened(expr.body))
        return expr.clone([desugar(a) for a in expr.args])

    
    invars = list(map(desugar,invars))
                          
    # Add the invariant phi to the list. TODO: maybe, if it is a G prop
    # invars.append(ipr.clone_goal(goal,[],invar))

    # Add the invariant list to the model
    model.invars = model.invars + invars

    prems = list(ipr.goal_prems(goal))

    def list_transform(lst,trns):
        for i in range(0,len(lst)):
            if ipr.goal_is_property(lst[i]):
                lst[i] = trns(lst[i])
    
    # for inv in invars:
    #     print inv
    #     for b in ilu.named_binders_ast(inv):
    #         print 'orig binder: {} {} {}'.format(b.name,b.environ,b.body)

    # model pass helper funciton
    def mod_pass(transform):
        model.invars = [transform(x) for x in model.invars]
        model.asms = [transform(x) for x in model.asms]
        # TODO: what about axioms and properties?
        newb = []
        model.bindings = [b.clone([transform(b.action)]) for b in model.bindings]
        model.init = transform(model.init)
        list_transform(prems,transform)

    # We first convert all temporal operators to named binders, so
    # it's possible to normalize them. Otherwise we won't have the
    # connection betweel (globally p(X)) and (globally p(Y)). Note
    # that we replace them even inside named binders.
    l2s_gs = set()
    l2s_whens = set()
    l2s_inits = set()
    def _l2s_g(vs, t, env):
        vs = tuple(vs)
        res = l2s_g(vs, t,env)
#        print 'l2s_gs: {} {} {}'.format(vs,t,env)
        l2s_gs.add((vs,t,env))
        return res
    def _l2s_when(name,vs,t):
        if name == 'first':
            res = l2s_when('next',tuple(vs),t)
            l2s_whens.add(res)
            res = l2s_init(tuple(vs),res(*vs))
            return res
        res = l2s_when(name,tuple(vs),t)
        l2s_whens.add(res)
        return res
    replace_temporals_by_l2s_g = lambda ast: ilu.replace_temporals_by_named_binder_g_ast(ast, _l2s_g, _l2s_when)
    mod_pass(replace_temporals_by_l2s_g)

    not_lf = replace_temporals_by_l2s_g(lg.Not(fmla))
    if debug.get():
        print("=" * 80 +"\nafter replace_temporals_by_named_binder_g_ast"+ "\n"*3)
        print("=" * 80 + "\nl2s_gs:")
        for vs, t, env in l2s_gs:
            print(vs, t, env)
        print("=" * 80 + "\n"*3)
        print(model)
        print("=" * 80 + "\n"*3)

    # now we normalize all named binders
    mod_pass(ilu.normalize_named_binders)
    if debug.get():
        print("=" * 80 +"\nafter normalize_named_binders"+ "\n"*3)
        print(model)
        print("=" * 80 + "\n"*3)

    # construct the monitor related building blocks

    reset_a = [
        AssignAction(l2s_a(s)(v), l2s_d(s)(v)).set_lineno(lineno)
        for s in uninterpreted_sorts
        for v in [lg.Var('X',s)]
    ]
    add_consts_to_d = [
        AssignAction(l2s_d(s)(c), lg.true).set_lineno(lineno)
        for s in uninterpreted_sorts
        for c in list(ilg.sig.symbols.values()) if c.sort == s
    ]
    # TODO: maybe add all ground terms, not just consts (if stratified)
    # TODO: add conjectures that constants are in d and a

    # figure out which l2s_w and l2s_s are used in conjectures
    named_binders_conjs = defaultdict(list) # dict mapping names to lists of (vars, body)
    ntprems = [x for x in prems if ipr.goal_is_property(x)
               and not (hasattr(x,'temporal') and x.temporal)]
    for b in ilu.named_binders_asts(model.invars):
#        print 'binder: {} {} {}'.format(b.name,b.environ,b.body)
        named_binders_conjs[b.name].append((b.variables, b.body))
            

    def list_transform(lst,trns):
        for i in range(0,len(lst)):
            if ipr.goal_is_property(lst[i]):
                lst[i] = trns(lst[i])

    named_binders_conjs = defaultdict(list,((k,list(set(v))) for k,v in named_binders_conjs.items()))

    # in full mode, add all the state variables to 'to_save' and all
    # of the temporal operators to 'to_wait'

    if full:
#        for act in mod.actions.values():
        seen = set(t for (vs,t) in named_binders_conjs['l2s_s'])
        for bnd in model.bindings:
            for act in bnd.action.stmt.iter_subactions():
                for sym in act.modifies():
                    vs = ilu.sym_placeholders(sym)
                    expr = sym(*vs) if vs else sym
                    if expr not in seen:
                        named_binders_conjs['l2s_s'].append((vs, expr))
        seen = set(t for (vs,t) in named_binders_conjs['l2s_w'])
        for b in ilu.named_binders_asts([ilu.normalize_named_binders(not_lf)]):
            if b.name == 'l2s_g':
                vs,t = b.variables,ilu.negate(b.body)
                if t not in seen:
                    named_binders_conjs['l2s_w'].append((vs,t))
            if b.name == 'l2s_init':
                named_binders_conjs['l2s_init'].append((b.variables,b.body))
        named_binders_conjs['l2s_init'] = list(set(named_binders_conjs['l2s_init']))
                
                    
    to_wait = [] # list of (variables, term) corresponding to l2s_w in conjectures
    to_wait += named_binders_conjs['l2s_w']
    to_save = [] # list of (variables, term) corresponding to l2s_s in conjectures
    to_save += named_binders_conjs['l2s_s']

    if debug.get():
        print("=" * 40 + "\nto_wait:\n")
        for vs, t in to_wait:
            print(vs, t)
            print(list(ilu.variables_ast(t)) == list(vs))
            print()
        print("=" * 40)

    save_state = [
        AssignAction(l2s_s(vs,t)(*vs), t).set_lineno(lineno)
        for vs, t in to_save
    ]
    done_waiting = [
        forall(vs, lg.Not(l2s_w(vs,t)(*vs)))
        for vs, t in to_wait
    ]
    reset_w = [
        AssignAction(
            l2s_w(vs,t)(*vs),
            lg.And(*([l2s_d(v.sort)(v) for v in vs if v.sort.name not in finite_sorts]
                     + [lg.Not(t),
                        replace_temporals_by_l2s_g(lg.Not(lg.Globally(proof_label,ilu.negate(t))))]))
        ).set_lineno(lineno)
        for vs, t in to_wait
    ]

    print ('reset_w:')
    for x in reset_w:
        print (x)
        
    fair_cycle = [l2s_saved]
    fair_cycle += done_waiting
    # projection of relations
    fair_cycle += [
        forall(vs, lg.Implies(
            lg.And(*(l2s_a(v.sort)(v) for v in vs if v.sort.name not in finite_sorts)),
            lg.Iff(l2s_s(vs, t)(*vs), t)
        ))
        if len(vs) > 0 else
        lg.Iff(l2s_s(vs, t), t)
        for vs, t in to_save
        if (t.sort == lg.Boolean or
            isinstance(t.sort, lg.FunctionSort) and t.sort.range == lg.Boolean
        )
    ]
    # projection of functions and constants
    fair_cycle += [
        forall(vs, lg.Implies(
            lg.And(*(
                [l2s_a(v.sort)(v) for v in vs if v.sort.name not in finite_sorts] +
                ([lg.Or(l2s_a(t.sort)(l2s_s(vs, t)(*vs)),
                       l2s_a(t.sort)(t))] if t.sort.name not in finite_sorts else [])
            )),
            lg.Eq(l2s_s(vs, t)(*vs), t)
        ))
        for vs, t in to_save
        if (isinstance(t.sort, lg.UninterpretedSort) or
            isinstance(t.sort, lg.FunctionSort) and isinstance(t.sort.range, lg.UninterpretedSort)
        )
    ]
    assert_no_fair_cycle = AssertAction(lg.Not(lg.And(*fair_cycle))).set_lineno(lineno)
    assert_no_fair_cycle.lineno = goal.lineno
    if proof.tactic_proof:
        assert_no_fair_cycle = ivy_compiler.apply_assert_proof(prover,assert_no_fair_cycle,proof.tactic_proof)

    monitor_edge = lambda s1, s2: [
        AssumeAction(s1).set_lineno(lineno),
        AssignAction(s1, lg.false).set_lineno(lineno),
        AssignAction(s2, lg.true).set_lineno(lineno),
    ]
    change_monitor_state = [ChoiceAction(
        # waiting -> frozen
        Sequence(*(
            monitor_edge(l2s_waiting, l2s_frozen) +
            [AssumeAction(x).set_lineno(lineno) for x in done_waiting] +
            reset_a
        )).set_lineno(lineno),
        # frozen -> saved
        Sequence(*(
            monitor_edge(l2s_frozen, l2s_saved) +
            save_state +
            reset_w
        )).set_lineno(lineno),
        # stay in same state (self edge)
        Sequence().set_lineno(lineno),
    ).set_lineno(lineno)]

    # tableau construction (sort of)

    # Note that we first transformed globally and eventually to named
    # binders, in order to normalize. Without this, we would get
    # multiple redundant axioms like:
    # forall X. (globally phi(X)) -> phi(X)
    # forall Y. (globally phi(Y)) -> phi(Y)
    # and the same redundancy will happen for transition updates.

    # temporals = []
    # temporals += list(ilu.temporals_asts(
    #     # TODO: these should be handled by mod_pass instead (and come via l2s_gs):
    #     # mod.labeled_axioms +
    #     # mod.labeled_props +
    #     [lf]
    # ))
    # temporals += [lg.Globally(lg.Not(t)) for vs, t in to_wait]
    # temporals += [lg.Globally(t) for vs, t in l2s_gs]
    # # TODO get from temporal axioms and temporal properties as well
    # print '='*40 + "\ntemporals:"
    # for t in temporals:
    #     print t, '\n'
    # print '='*40
    # to_g = [ # list of (variables, formula)
    #     (tuple(sorted(ilu.variables_ast(tt))), tt) # TODO what about variable normalization??
    #     for t in temporals
    #     for tt in [t.body if type(t) is lg.Globally else
    #                lg.Not(t.body) if type(t) is lg.Eventually else 1/0]
    # ]
    # TODO: get rid of the above, after properly combining it
    to_g = [] # list of (variables, formula)
    to_g += list(l2s_gs)
    to_g = list(set(to_g))
    if debug.get():
        print('='*40 + "\nto_g:\n")
        for vs, t, env in to_g:
            print(vs, t, '\n')
        print('='*40)

    assume_g_axioms = [
        AssumeAction(forall(vs, lg.Implies(l2s_g(vs, t, env)(*vs), t))).set_lineno(lineno)
        for vs, t, env in to_g
    ]
    
    assume_when_axioms = [
        AssumeAction(forall(when.variables, lg.Implies(when.body.t1,lg.Eq(when(*when.variables),when.body.t2))))
        for when in l2s_whens
    ]

    def apply_l2s_init(vs,t):
        if type(t) == lg.Not:
            return lg.Not(apply_l2s_init(vs,t.args[0]))
        return l2s_init(vs, t)(*vs)
    
    assume_init_axioms = [
        AssumeAction(forall(vs, lg.Eq(apply_l2s_init(vs,t), t))).set_lineno(lineno)
        for vs, t in named_binders_conjs['l2s_init']
    ]

    assume_w_axioms = [
        AssumeAction(forall(vs, lg.Not(lg.And(t,l2s_w(vs,t)(*vs))))).set_lineno(lineno)
        for vs, t in named_binders_conjs['l2s_w']
    ]

    # now patch the module actions with monitor and tableau


    if debug.get():
        print("public_actions:", model.calls)

    # Tableau construction
    #
    # Each temporal operator has an 'environment'. The operator
    # applies to states *not* in actions labeled with this
    # environment. This has several consequences:
    #
    # 1) The operator's semantic constraint is an assumed invariant (i.e.,
    # it holds outside of any action)
    #
    # 2) An 'event' for the temporal operator occurs when (a) we return
    # from an execution context inside its environment to one outside,
    # or (b) we are outside the environment of the operator and some symbol
    # occurring in it's body is mutated.
    #
    # 3) At any event for the operator, we update its truth value and
    # and re-establish its semantic constraint.
    #

    # This procedure generates code for an event corresponding to a
    # list of operators. The tableau state is updated and the
    # semantics applied.
    
    def prop_events(gprops):
        pre = []
        post = []
        for gprop in gprops:
            vs,t,env = gprop.variables, gprop.body, gprop.environ
            pre.append(AssignAction(old_l2s_g(vs, t, env)(*vs),l2s_g(vs, t, env)(*vs)).set_lineno(lineno))
            pre.append(HavocAction(l2s_g(vs, t, env)(*vs)).set_lineno(lineno))
        for gprop in gprops:
            vs,t,env = gprop.variables, gprop.body, gprop.environ
            pre.append(AssumeAction(forall(vs, lg.Implies(old_l2s_g(vs, t, env)(*vs),
                                                          l2s_g(vs, t, env)(*vs)))).set_lineno(lineno))
            pre.append(AssumeAction(forall(vs, lg.Implies(lg.And(lg.Not(old_l2s_g(vs, t, env)(*vs)), t),
                                                          lg.Not(l2s_g(vs, t, env)(*vs))))).set_lineno(lineno))
            post.append(AssumeAction(forall(vs, lg.Implies(l2s_g(vs, t, env)(*vs), t))).set_lineno(lineno))
            
        return (pre, post)
            
    def when_events(whens):
        pre = []
        post = []
        for when in whens:
            name, vs,t = when.name, when.variables, when.body
            cond,val = t.t1,t.t2
            if name == 'l2s_whennext':
                oldcond = l2s_old(vs, cond)(*vs)
                pre.append(AssignAction(oldcond,cond).set_lineno(lineno))
                # print ('when: {}'.format(when))
                # print ('oldcond :{}'.format(oldcond))
                post.append(IfAction(oldcond,HavocAction(when(*vs)).set_lineno(lineno)).set_lineno(lineno))
            if name == 'l2s_whenprev':
                post.append(IfAction(cond,HavocAction(when(*vs)).set_lineno(lineno)).set_lineno(lineno))
        for when in whens:
            post.append(AssumeAction(forall(when.variables, lg.Implies(when.body.t1,lg.Eq(when(*when.variables),when.body.t2)))))
        # for when in whens:
        #     name, vs,t = when.name, when.variables, when.body
        #     cond,val = t.t1,t.t2
        #     if name == 'next':
        #     pre.append(AssumeAction(forall(vs, lg.Implies(cond,lg.Equals(when(*vs),val)))))
        return (pre, post)
            

    # This procedure generates code for an event corresponding to a
    # list of eventualites to be waited on. The tableau state is updated and the
    # semantics applied.

    def wait_events(waits):
        res = []
        for wait in waits:
            vs = wait.variables
            t = wait.body

        # (l2s_w V. phi)(V) := (l2s_w V. phi)(V) & ~phi & ~(l2s_g V. ~phi)(V)

            res.append(
                AssignAction(
                    wait(*vs),
                    lg.And(wait(*vs),
                           lg.Not(t),
                           replace_temporals_by_l2s_g(lg.Not(lg.Globally(proof_label,ilu.negate(t)))))
                    # TODO check this and make sure its correct
                    # note this adds to l2s_gs
                ).set_lineno(lineno))
        return res

    # The following procedure instruments a statement with operator
    # events for all of the temporal operators.  This depends on the
    # statement's environment, that is, current set of environment
    # labels.
    #
    # Currently, the environment labels of a statement have to be
    # statically determined, but this could change, i.e., the labels
    # could be represented by boolean variables. 
    #
    
    # First, make some memo tables

    envprops = defaultdict(list)
    symprops = defaultdict(list)
    symwaits = defaultdict(list)
    symwhens = defaultdict(list)
    for vs, t, env in l2s_gs:
        prop = l2s_g(vs,t,env)
        envprops[env].append(prop)
        for sym in ilu.symbols_ast(t):
            symprops[sym].append(prop)
    for when in l2s_whens:
        for sym in ilu.symbols_ast(when.body):
            symwhens[sym].append(when)
    for vs, t in to_wait:
        wait = l2s_w(vs,t)
        for sym in ilu.symbols_ast(t):
            symwaits[sym].append(wait)
    actions = dict((b.name,b.action) for b in model.bindings)
    # lines = dict(zip(gprops,gproplines))
            
    def instr_stmt(stmt,labels):

        # A call statement that modifies a monitored symbol as to be split
        # into call followed by assignment.

        if (isinstance(stmt,CallAction)):
            actual_returns = stmt.args[1:]
            if any(sym in symprops or sym in symwhens
                   or sym in symwaits for sym in actual_returns):
                return instr_stmt(stmt.split_returns(),labels)
            
        
        # first, recur on the sub-statements
        args = [instr_stmt(a,labels) if isinstance(a,Action) else a for a in stmt.args]
        res = stmt.clone(args)

        # now add any needed temporal events after this statement
        event_props = set()
        event_whens = set()
        event_waits = set()

        # first, if it is a call, we must consider any events associated with
        # the return
        
        # if isinstance(stmt,CallAction):
        #     callee = actions[stmt.callee()]  # get the called action
        #     exiting = [l for l in callee.labels if l not in labels] # environments we exit on return
        #     for label in exiting:
        #         for prop in envprops[label]:
        #             event_props.add(prop)

        # Second, if a symbol is modified, we must add events for every property that
        # depends on the symbol, but only if we are not in the environment of that property.
        #
        # Notice we have to consider defined functions that depend on the modified symbols
                    
        for sym in dependencies(stmt.modifies()):
            for prop in symprops[sym]:
#                if prop.environ not in labels:
                event_props.add(prop)
            for when in symwhens[sym]:
#                if prop.environ not in labels:
                event_whens.add(when)
            for wait in symwaits[sym]:
                event_waits.add(wait)

                    
        # Now, for every property event, we update the property state (none in this case)
        # and also assert the property semantic constraint. 

        (pre_events, post_events) = prop_events(event_props)
        (when_pre_events, when_post_events) = when_events(event_whens)
        pre_events = when_pre_events + pre_events
        post_events += when_post_events
        post_events += wait_events(event_waits)
        res =  iact.prefix_action(res,pre_events)
        res =  iact.postfix_action(res,post_events)
        stmt.copy_formals(res) # HACK: This shouldn't be needed
        return res

    # Instrument all the actions

    model.bindings = [b.clone([b.action.clone([instr_stmt(b.action.stmt,b.action.labels)])])
                      for b in model.bindings]
    
    # Now, for every exported action, we add the l2s construction. On
    # exit of each external procedure, we add a tableau event for all
    # the operators whose scope is being exited.
    #
    # TODO: This is wrong in the case of an exported procedure that is
    # also internally called.  We do *not* want to update the tableau
    # in the case of an internal call, since the scope of the
    # operators os not exited. One solution to this is to create to
    # duplicate the actions so there is one version for internal
    # callers and one for external callers. It is possible that this
    # is already done by ivy_isolate, but this needs to be verified.
    
    calls = set(model.calls) # the exports
    for b in model.bindings:
        if b.name in calls:
            add_params_to_d = [
                AssignAction(l2s_d(p.sort)(p), lg.true)
                for p in b.action.inputs
                if p.sort.name not in finite_sorts
            ]
            # tableau updates for exit to environment
            # event_props = set()
            # for label in b.action.labels:
            #     for prop in envprops[label]:
            #         event_props.add(prop)
            # events = prop_events(event_props)
            stmt = concat_actions(*(
                add_params_to_d +
                assume_g_axioms +  # could be added to model.asms
                assume_when_axioms +
                assume_w_axioms +
                [b.action.stmt] +
                add_consts_to_d
            )).set_lineno(lineno)
            b.action.stmt.copy_formals(stmt) # HACK: This shouldn't be needed
            b.action = b.action.clone([stmt])

    # The idle action handles automaton state update and cycle checking

    idle_action = concat_actions(*(
        change_monitor_state +
        assume_g_axioms +  # could be added to model.asms
        add_consts_to_d +
        [assert_no_fair_cycle]
    )).set_lineno(lineno)
    idle_action.formal_params = []
    idle_action.formal_returns = []
    model.bindings.append(itm.ActionTermBinding('idle',itm.ActionTerm([],[],[],idle_action)))
    model.calls.append('idle')
    
    l2s_init = [
        AssignAction(l2s_waiting, lg.true).set_lineno(lineno),
        AssignAction(l2s_frozen, lg.false).set_lineno(lineno),
        AssignAction(l2s_saved, lg.false).set_lineno(lineno),
    ]
    l2s_init += add_consts_to_d
    l2s_init += reset_w
    l2s_init += assume_g_axioms
    l2s_init += assume_init_axioms
    l2s_init += [AssumeAction(not_lf).set_lineno(lineno)]
    if not hasattr(model.init,'lineno'):
        model.init.lineno = None  # Hack: fix this
    model.init =  iact.postfix_action(model.init,l2s_init)

    if debug.get():
        print("=" * 80 + "\nafter patching actions" + "\n"*3)
        print(model)
        print("=" * 80 + "\n"*3)

    # now replace all named binders by fresh relations

    named_binders = defaultdict(list) # dict mapping names to lists of (vars, body)
    for b in ilu.named_binders_asts(chain(
            model.invars,
            model.asms,
            [model.init],
            [b.action for b in model.bindings],
    )):
        named_binders[b.name].append(b)
    named_binders = defaultdict(list, ((k,list(sorted(set(v),key=str))) for k,v in named_binders.items()))
    # make sure old_l2s_g is consistent with l2s_g
#    assert len(named_binders['l2s_g']) == len(named_binders['_old_l2s_g'])
    named_binders['_old_l2s_g'] = [
         lg.NamedBinder('_old_l2s_g', b.variables, b.environ, b.body)
         for b in named_binders['l2s_g']
    ]

    subs = dict(
        (b, lg.Const('{}_{}'.format(k, i), b.sort))
        for k, v in named_binders.items()
        for i, b in enumerate(v)
    )
    if debug.get():
        print("=" * 80 + "\nsubs:" + "\n"*3)
        for k, v in list(subs.items()):
            print(k, ' : ', v, '\n')
        print("=" * 80 + "\n"*3)
    mod_pass(lambda ast: ilu.replace_named_binders_ast(ast, subs))

    if debug.get():
        print("=" * 80 + "\nafter replace_named_binders" + "\n"*3)
        print(model)
        print("=" * 80 + "\n"*3)

    # if len(gprops) > 0:
    #     assumes = [gprop_to_assume(x) for x in gprops]
    #     model.bindings = [b.clone([prefix_action(b.action,assumes)]) for b in model.bindings]

    # HACK: reestablish invariant that shouldn't be needed

    for b in model.bindings:
        b.action.stmt.formal_params = b.action.inputs
        b.action.stmt.formal_returns = b.action.outputs

    # Change the conclusion formula to M |= true
    conc = ivy_ast.TemporalModels(model,lg.And())

    # Build the new goal
    non_temporal_prems = [x for x in prems if not (hasattr(x,'temporal') and x.temporal)]
    goal = ipr.clone_goal(goal,non_temporal_prems,conc)

    goal = ipr.remove_unused_definitions_goal(goal)

    if tactic_name.startswith("l2s_auto5"):
        goal.trace_hook = lambda tr,fcs: auto_hook(tasks,triggers,subs,tr,fcs)
    else:
        goal.trace_hook = lambda tr,fcs: renaming_hook(subs,tr,fcs)

    # Return the new goal stack

    goals = [goal] + goals[1:]
    return goals

# Hook to convert temporary symbols back to named binders. Argument
# 'subs' is the map from named binders to temporary symbols.

def renaming_hook(subs,tr,fcs):
    return tr.rename(dict((x,y) for (y,x) in subs.items()))

def temporal_and_l2s(sym):
    return (sym.name.startswith('l2s') and not sym.name.startswith('l2s_g')
            or sym.name.startswith('_old_l2s'))

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
    rsubs = dict((x,y) for (y,x) in subs.items())
    # Figure out which property failed
    failed_fc = None
    for fc in fcs:
        if fc.failed:
            failed_fc = fc
            break
    if failed_fc is None or not hasattr(failed_fc,'lf'):
        return tr # shouldn't happen

    # Find the justice conditions

    justice_pred_map = dict()
    for fc in fcs:
        lf = fc.lf
        if lf.name.startswith('l2s_progress_invar'):
            sfx = lf.name[len('l2s_progress_invar'):]
            gfmla = rsubs[lf.formula.args[1].rep]
            gargs = lf.formula.args[1].args
            jfmla = gfmla.body.args[0]
            jfmla = subs[jfmla.rep]
            justice_pred_map[sfx] = jfmla

    lf = failed_fc.lf
    invar = lf.formula
    name = lf.name
    if name.startswith('l2s_created'):
        sfx = name[len('l2s_created'):]
        print ('\n\nFailed to prove that work_created{} is finite by induction.\n'.format(sfx))
        work_created = tasks[sfx]['work_created']
        vs = work_created.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_created.args[0].rep)(*vals)
            print ('Note: {} is true in the post-state of the action, but not in the pre-state,'.format(pred))
            print ('and its argument(s) are not visited during the action execution.\n')
        tr.hidden_symbols = temporal_and_l2s
            
    elif name.startswith('l2s_needed_when_start'):
        sfx = name[len('l2s_needed_when_start'):]

        # TODO: handle the case where we have already started and needed increases

        print ('\n\nFailed to prove that work_needed{} is a subset of work_created{} when the start condition has occurred.\n'.format(sfx,sfx))
        work_needed = tasks[sfx]['work_needed']
        work_created = tasks[sfx]['work_created']
        vs = work_needed.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred1 = (work_needed.args[0].rep)(*vals)
            pred2 = (work_created.args[0].rep)(*vals)
            print ('Note: the start condition occurs during the action and {} is true in the post-state of the action, but {} is not true.'.format(pred1,pred2))
        tr.hidden_symbols = temporal_and_l2s

    elif name.startswith('l2s_work_preserved'):
        sfx = name[len('l2s_work_preserved'):]

        print ('\n\nFailed to prove that work_needed{} is preserved.\n'.format(sfx,sfx))
        work_needed = tasks[sfx]['work_needed']
        vs = work_needed.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_needed.args[0].rep)(*vals)
            print ('Note: work_invar{} is true and {} changes from false to true.\n'.format(sfx,pred))
        tr.hidden_symbols = temporal_and_l2s

    elif name.startswith('l2s_needed_are_frozen'):
        sfx = name[len('l2s_needed_are_frozen'):]

        print ('\n\nFailed to prove that work_needed{} is preserved.\n'.format(sfx,sfx))
        work_needed = tasks[sfx]['work_needed']
        vs = work_needed.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_needed.args[0].rep)(*vals)
            print ('Note: work_invar{} is true and {} changes from false to true.\n'.format(sfx,pred))
        tr.hidden_symbols = temporal_and_l2s
        
    elif name.startswith('l2s_progress_made'):
        sfx = name[len('l2s_progress_made'):]

        print ('\n\nFailed to prove that work_needed{} decreases when a helpful transition occurs\n'.format(sfx,sfx))
        lhs = invar.args[0]
        all_helpful_happened = lhs.args[4]
        if (ilg.is_forall(all_helpful_happened)):
            was_helpful_pred_nonce = all_helpful_happened.body.args[0].rep
        else:
            was_helpful_pred_nonce = all_helpful_happened.args[0].rep
        work_helpful = tasks[sfx]['work_helpful']
        helpful_map = dict()
        for eqn in tr.states[0].clauses.fmlas:
            if eqn.args[0].rep == was_helpful_pred_nonce:
                helpful_map[tuple(eqn.args[0].args)] = eqn.args[1]
                print ('{} = {}'.format(work_helpful.args[0].rep(*eqn.args[0].args),eqn.args[1]))
        if (ilg.is_forall(all_helpful_happened)):
            trigger_happened_pred_nonce = all_helpful_happened.body.args[1].args[0].rep
        else:
            trigger_happened_pred_nonce = all_helpful_happened.args[1].args[0].rep
        work_progress = tasks[sfx]['work_progress']
        happened_maps = [dict(),dict()]
        for idx in range(2):
            print ('')
            for eqn in tr.states[idx].clauses.fmlas:
                if eqn.args[0].rep == trigger_happened_pred_nonce:
                    happened_maps[idx][tuple(eqn.args[0].args)] = eqn.args[1]
                    print ('~happened {} = {}'.format(work_progress.args[0].rep(*eqn.args[0].args),eqn.args[1]))
        justice_map = dict()
        if sfx in justice_pred_map:
            print ('')
            justice_pred = justice_pred_map[sfx]
            for eqn in tr.states[0].clauses.fmlas:
                if eqn.args[0].rep == justice_pred:
                    justice_map[tuple(eqn.args[0].args)] = eqn.args[1]
                    print ('~eventually {} = {}'.format(work_progress.args[0].rep(*eqn.args[0].args),eqn.args[1]))
        for args in helpful_map:
            if ilg.is_true(helpful_map[args]):
                if all(args in happened_maps[idx] for idx in range(2)):
                    if ilg.is_true(happened_maps[0][args]) and ilg.is_false(happened_maps[1][args]):
                        print ('\nNote: {} is true and {} occurs during the action, but work_needed is not reduced.\n'.format(work_helpful.args[0].rep(*args),work_progress.args[0].rep(*args)))
                        break
        for args in helpful_map:
            if ilg.is_true(helpful_map[args]):
                if args in justice_map:
                    if ilg.is_true(happened_maps[0][args]) and ilg.is_true(justice_map[args]):
                        print ('\nNote: {} is true and eventually {} is false.\n'.format(work_helpful.args[0].rep(*args),work_progress.args[0].rep(*args)))
                        break
        work_needed = tasks[sfx]['work_needed']
        vs = work_needed.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_needed.args[0].rep)(*vals)
            print ('Note: work_invar{} is true and {} changes from false to true.\n'.format(sfx,pred))
        # tr.hidden_symbols = temporal_and_l2s

    elif name.startswith('l2s_sched_stable'):
        sfx = name[len('l2s_sched_stable'):]

        print ('\n\nFailed to prove that work_helpful{} is stable until helpful transition occurs\n'.format(sfx))

        work_progress = tasks[sfx]['work_progress']
        vs = work_progress.args[0].args
        work_helpful = tasks[sfx]['work_helpful']
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_helpful.args[0].rep)(*vals)
            print ('Note: work_invar{} is true and {} changes from true to false, but {} does not occur during the action.\n'.format(sfx,pred,work_progress.args[0].rep(*vals)))
        tr.hidden_symbols = temporal_and_l2s

    elif name.startswith('l2s_not_all_done'):
        rank_names = ' and '.join('work_needed'+sfx for sfx in tasks if 'work_needed' in tasks[sfx])
        print ('The ranking(s) {} have become empty, but termination has not occurred.'.format(rank_names))
        tr.hidden_symbols = temporal_and_l2s
        
    elif name.startswith('l2s_sched_exists'):
        rank_names = ' and '.join('work_helpful'+sfx for sfx in tasks if 'work_helpful' in tasks[sfx])
        print ('The helpful set(s)  {} have become empty, but termination has not occurred'.format(rank_names))
        tr.hidden_symbols = temporal_and_l2s

    return tr
            
        
        
    
            
            

# Register the l2s tactics

ipr.register_tactic('l2s',l2s_tactic)
ipr.register_tactic('l2s_full',l2s_tactic_full)
ipr.register_tactic('l2s_auto',l2s_tactic_auto)
ipr.register_tactic('l2s_auto2',l2s_tactic_auto)
ipr.register_tactic('l2s_auto3',l2s_tactic_auto)
ipr.register_tactic('l2s_auto4',l2s_tactic_auto)
ipr.register_tactic('l2s_auto5',l2s_tactic_auto)
