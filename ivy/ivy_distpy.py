# ivy_distpy.py
# Author: Ruijie Fang
# 
# Description: Use distpy library to enable very-fine grained, highly parallel 
# proof checking in Ivy. The objective is to accelerate Ivy's running time when
# checking very large specifications. 
# 
# The current implementation distributes distpy jobs at the granularity level of
# each properties to check (for non-temporal properties). Each temporal property
# within an isolate is distributed as a single task, while the checking of 
# multiple temporal properties within an isolate is parallelized.
# 
# Checking of assertions is parallelized at the isolate-level. Within each isolate,
# the checking of assertions is not parallelized.

from . import ivy_init
from . import ivy_interp as itp
from . import ivy_actions as act
from . import ivy_utils as utl
from . import ivy_logic_utils as lut
from . import ivy_logic as lg
from . import ivy_utils as iu
from . import ivy_ui
from . import ivy_module as im
from . import ivy_alpha
from . import ivy_art
from . import ivy_interp
from . import ivy_compiler
from . import ivy_isolate
from . import ivy_ast
from . import ivy_theory as ith
from . import ivy_transrel as itr
from . import ivy_solver as islv
from . import ivy_fragment as ifc
from . import ivy_proof
from . import ivy_trace
from . import ivy_temporal as itmp
from . import ivy_printer
from . import ivy_l2s
from . import ivy_mc
from . import ivy_vmt
from . import ivy_bmc
from . import ivy_tactics
from . import ivy_acl
from . import ivy_distpy

from .ivy_check import ConjChecker, ConjAssumer, pretty_lf

import sys
from collections import defaultdict

import pdb, traceback, sys, code
import dispy

checked_action = iu.get_parameter("checked_action")


diagnose = iu.get_parameter("diagnose")
coverage = iu.get_parameter("coverage")
checked_action = iu.get_parameter("action")
opt_trusted = iu.get_parameter("trusted")
opt_mc = iu.get_parameter("mc")
opt_trace = iu.get_parameter("trace")
opt_separate = iu.get_parameter("separate")
opt_unchecked_properties = iu.get_parameter("unchecked_properties")
opt_ivy_stats = iu.get_parameter("ivy_stats")
opt_distributed = iu.get_parameter("distribuedt")


### dispy functionalities

def filter_fcs(fcs):
    global check_lineno
    if check_lineno is None:
        return fcs
    return [fc for fc in fcs if (not isinstance(fc,ConjChecker) or fc.lf.lineno == check_lineno)]


def check_temporals():
    mod = im.module
    props = mod.labeled_props
    pmap = dict((prop.id,p) for prop,p in mod.proofs)
    pc = ivy_proof.ProofChecker(mod.labeled_axioms+mod.assumed_invariants,mod.definitions,mod.schemata)
    for prop in props:
        if prop.temporal:
            if prop.assumed:
                pc.admit_axiom(prop)
            else:
                print('\n    The following temporal property is being proved:\n')
                print(pretty_lf(prop) + ' ...', end=' ')
                sys.stdout.flush()
                if prop.temporal:
                    proof = pmap.get(prop.id,None)
                    propn = ivy_proof.normalize_goal(prop)
                    model = itmp.normal_program_from_module(im.module)
                    subgoal = prop.clone([prop.args[0],ivy_ast.TemporalModels(model,propn.args[1])])
                    subgoals = [subgoal]
                    subgoals = pc.admit_proposition(prop,proof,subgoals)
                    check_subgoals(subgoals)
            
        # else:
        #     # Non-temporal properties have already been proved, so just
        #     # admit them here without proof (in other words, ignore the
        #     # generated subgoals).

        #     pc.admit_proposition(prop,ivy_ast.ComposeTactics())

def get_checked_actions():
    cact = checked_action.get()
    if cact and 'ext:'+cact in im.module.public_actions:
        cact = 'ext:'+cact
    if not(cact and cact not in im.module.public_actions):
        global checked_action_found
        checked_action_found = True
        return [cact] if cact else sorted(im.module.public_actions)
    return []

failures = 0


def print_dots():
    print('...', end=' ')
    sys.stdout.flush()

def is_unprovable_assert(asrt):
    return asrt.args[0].unprovable if isinstance(asrt.args[0],ivy_ast.LabeledFormula) else False

def is_guarantee_mod_unprovable(asrt):
    return is_unprovable_assert(asrt) == act.check_unprovable.get()

def is_check_mod_unprovable(lf):
    return lf.unprovable == act.check_unprovable.get()


def check_fcs_in_state(mod,ag,post,fcs):
#    iu.dbg('"foo"')
    history = ag.get_history(post)
#    iu.dbg('history.actions')
    gmc = lambda cls, final_cond: itr.small_model_clauses(cls,final_cond,shrink=diagnose.get())
    axioms = im.module.background_theory()
    if opt_trace.get() or diagnose.get():
        clauses = history.post
        clauses = lut.and_clauses(clauses,axioms)
        ffcs = filter_fcs(fcs)
        model = itr.small_model_clauses(clauses,ffcs,shrink=True)
        if model is not None:
#            iu.dbg('history.actions')
            failed = [c for c in ffcs if c.failed]
            mclauses = lut.and_clauses(*([clauses] + [c.cond() for c in failed]))
            vocab = lut.used_symbols_clauses(mclauses)
#            handler = MatchHandler(mclauses,model,vocab) if opt_trace.get() else ivy_trace.Trace(mclauses,model,vocab)
            handler = ivy_trace.Trace(mclauses,model,vocab)
            thing = failed[-1].get_annot()
            if thing is None:
                assert all(x is not None for x in history.actions)
                # work around a bug in ivy_interp
                actions = [im.module.actions[a] if isinstance(a,str) else a for a in history.actions]
                action = act.Sequence(*actions)
                annot = clauses.annot
            else:
                action,annot = thing
            act.match_annotation(action,annot,handler)
            handler.end()
            if hasattr(mod,"trace_hook"):
                handler = mod.trace_hook(handler,ffcs)
            ff = failed[0]
            handler.is_cti = (lut.formula_to_clauses(ff.lf.formula) if isinstance(ff,ConjChecker)
                              else None)
            if not opt_trace.get():
                gui_art(handler)
            else:
                print(str(handler))
            exit(0)
    else:
        res = history.satisfy(axioms,gmc,filter_fcs(fcs))
        if res is not None and diagnose.get():
            show_counterexample(ag,post,res)
    return not any(fc.failed for fc in fcs)

def check_conjs_in_state(mod,ag,post,indent=8):
    conjs = mod.conj_subgoals if mod.conj_subgoals is not None else mod.labeled_conjs
    conjs = [x for x in conjs if is_check_mod_unprovable(x)]
    check_lineno = act.checked_assert.get()
    if check_lineno == "":
        check_lineno = None
    if check_lineno is not None:
        lcs = [sub for sub in conjs if sub.lineno == check_lineno]
    else:
        lcs = conjs
    return check_fcs_in_state(mod,ag,post,[ConjChecker(c,indent) for c in lcs])

def check_safety_in_state(mod,ag,post,report_pass=True):
    return check_fcs_in_state(mod,ag,post,[Checker(lg.Or(),report_pass=report_pass)])

opt_summary = iu.get_parameter("summary")

# This gets the pre-state for inductive checks. Only implicit conjectures are used.

def get_conjs(mod):
    fmlas = [lf.formula for lf in mod.labeled_conjs + mod.assumed_invariants if not lf.explicit and not lf.unprovable]
    return lut.Clauses(fmlas,annot=act.EmptyAnnotation())

def apply_conj_proofs(mod):
    # Apply any proof tactics to the conjs to get the conj_subgoals.

    pc = ivy_proof.ProofChecker(mod.labeled_axioms+mod.assumed_invariants,mod.definitions,mod.schemata)
    pmap = dict((lf.id,p) for lf,p in mod.proofs)
    conjs = []
    for lf in mod.labeled_conjs:
        if lf.id in pmap:
            proof = pmap[lf.id]
            subgoals = pc.admit_proposition(lf,proof)
            subgoals = list(map(ivy_compiler.theorem_to_property,subgoals))
            conjs.extend(subgoals)
        else:
            conjs.append(lf)
    mod.conj_subgoals = conjs


### preprocess axioms, properties, conjectures if user supplies an "access control list," 
###  specifying what properties to ignore and what to assume.
def preprocess_assumed_ignored_properties():
    mod = im.module
    axioms = list(map(lambda x: (x, '[axiom]'), mod.labeled_axioms))
    conjs = list(map(lambda x: (x, '[conjecture]'), mod.labeled_conjs))
    props = list(map(lambda x: (x, '[property]'), mod.labeled_props))
    print('\n  Preprocessing list of axioms, properties, conjectures via user-supplied list of unchecked properties.')
    print("\n     The following properties are newly ignored: ")
    for lft in axioms + conjs + props:
        if ivy_acl.is_ignored(lft[0].label):
            print(lft[1] + " " + pretty_lf(lft[0]))
    print('\n     The following properties are newly assumed: ')
    for lft in axioms + conjs + props:
        if ivy_acl.is_assumed(lft[0].label):
            print(lft[1] + " " + pretty_lf(lft[0]))
    mod.labeled_conjs = list(filter(lambda lf: not ivy_acl.is_ignored(lf.label), mod.labeled_conjs))
    # a property is either (1) a user-defined, non-ignored property, or (2) a user-defined, non-ignored conjecture that is assumed.
    mod.labeled_props = [lf for lf in im.module.labeled_props+im.module.labeled_conjs if not (lf.assumed or ivy_acl.is_assumed(lf.label) or ivy_acl.is_ignored(lf.label))]
    # an axiom is a user-defined, non-ignored axiom.
    mod.labeled_axioms = [lf for lf in im.module.labeled_axioms if not(ivy_acl.is_ignored(lf.label))]
    # a conjecture is a user-defined, non-ignored, non-assumed conjecture.
    mod.labeled_conjs = [lf for lf in im.module.labeled_conjs if not(ivy_acl.is_ignored(lf.label)) and not(ivy_acl.is_assumed(lf.label))]



class DistributedCheckingInstance(object):


    def __init__(self, mod)

def check_isolate(trace_hook = None):
    mod = im.module
    cluster = dispy.JobCluster()
    print('\n    The following properties are treated as axioms: ')
    for lf in mod.labeled_axioms:
        print(pretty_lf(lf))
    print('\n    The following properties are treated as properties:')
    for lf in mod.labeled_props:
        print(pretty_lf(lf))
    print('\n    The following properties are treated as conjectures: ')
    for lf in mod.labeled_conjs:
        print(pretty_lf(lf))
    if mod.isolate_proof is not None:
        pc = ivy_proof.ProofChecker(mod.labeled_axioms+mod.assumed_invariants,mod.definitions,mod.schemata)
        model = itmp.normal_program_from_module(im.module)
        prop = ivy_ast.LabeledFormula(ivy_ast.Atom('safety'),lg.And())
        subgoal = ivy_ast.LabeledFormula(ivy_ast.Atom('safety'),ivy_ast.TemporalModels(model,lg.And()))
        subgoal.lineno = mod.isolate_proof.lineno 
        #        print 'subgoal = {}'.format(subgoal)
        subgoals = [subgoal]
        subgoals = pc.admit_proposition(prop,mod.isolate_proof,subgoals)
        check_subgoals(subgoals)
        return
    
    import time
    if opt_ivy_stats.get():
        print('calling fragment checker...')
    fc_start = time.time()
    ifc.check_fragment()
    fc_end = time.time()
    if opt_ivy_stats.get():
        print("\n\t IVY_STATS fragment checker elapsed time (s): ", fc_end - fc_start)
    with im.module.theory_context():
        global check_lineno
        check_lineno = act.checked_assert.get()
        if check_lineno == "":
            check_lineno = None
    #    print 'check_lineno: {}'.format(check_lineno)
        check = not opt_summary.get()
        unprovable = act.check_unprovable.get()
        subgoalmap = dict((x.id,y) for x,y in im.module.subgoals)
        axioms = [m for m in mod.labeled_axioms if m.id not in subgoalmap] 
        schema_instances = [m for m in mod.labeled_axioms if m.id in subgoalmap]
        if axioms:
            print("\n    The following properties are assumed as axioms:")
            for lf in axioms:
                print(pretty_lf(lf))

        if mod.definitions:
            print("\n    The following definitions are used:")
            for lf in mod.definitions:
                print(pretty_lf(lf))

        if (mod.labeled_props or schema_instances) and not checked_action.get() and not unprovable :
            print("\n    The following properties are to be checked:")
            if check:
                for lf in schema_instances:
                    print(pretty_lf(lf) + " [proved by axiom schema]")
                ag = ivy_art.AnalysisGraph()
                clauses1 = lut.true_clauses(annot=act.EmptyAnnotation())
                pre = itp.State(value = clauses1)
                props = [x for x in im.module.labeled_props if not x.temporal]
                props = [p for p in props if not(p.id in subgoalmap and p.explicit)]
                fcs = ([(ConjAssumer if prop.assumed or prop.id in subgoalmap else ConjChecker)(prop) for prop in props])
                check_fcs_in_state(mod,ag,pre,fcs)
            else:
                for lf in schema_instances + mod.labeled_props:
                    print(pretty_lf(lf))

        # after checking properties, make them axioms, except temporals
        im.module.labeled_axioms.extend(p for p in im.module.labeled_props if not p.temporal)
        im.module.update_theory()


        if mod.labeled_inits:
            print("\n    The following properties are assumed initially:")
            for lf in mod.labeled_inits:
                print(pretty_lf(lf))
        checked_invariants = [x for x in mod.labeled_conjs if is_check_mod_unprovable(x)]
        if checked_invariants:
            print("\n    The inductive invariant consists of the following conjectures:")
            for lf in checked_invariants:
                print(pretty_lf(lf))

        apply_conj_proofs(mod)

        if mod.isolate_info is not None and mod.isolate_info.implementations:
            print("\n    The following action implementations are present:")
            for mixer,mixee,action in sorted(mod.isolate_info.implementations,key=lambda x: x[0]):
                print("        {}implementation of {}".format(pretty_lineno(action),mixee))

        if mod.isolate_info is not None and mod.isolate_info.monitors:
            print("\n    The following action monitors are present:")
            for mixer,mixee,action in sorted(mod.isolate_info.monitors,key=lambda x: x[0]):
                print("        {}monitor of {}".format(pretty_lineno(action),mixee))

        # if mod.actions:
        #     print "\n    The following actions are present:"
        #     for actname,action in sorted(mod.actions.iteritems()):
        #         print "        {}{}".format(pretty_lineno(action),actname)

        if mod.initializers:
            print("\n    The following initializers are present:")
            for actname,action in sorted(mod.initializers, key=lambda x: x[0]):
                print("        {}{}".format(pretty_lineno(action),actname))

        if checked_invariants and not checked_action.get() and not unprovable:
            print("\n    Initialization must establish the invariant")
            if check:
                with itp.EvalContext(check=False):
                    ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
                    check_conjs_in_state(mod,ag,ag.states[0])
            else:
                print('')

        if mod.initializers:
            guarantees = [sub for sub in action.iter_subactions()
                          if isinstance(sub,(act.AssertAction,act.Ranking))
                          for action in mod.initializers]
            if check_lineno is not None:
                guarantees = [sub for sub in guarantees if sub.lineno == check_lineno]
            guarantees = [x for x in guarantees if is_guarantee_mod_unprovable(x)]
            if guarantees and not unprovable:
                print("\n    Any assertions in initializers must be checked", end=' ')
                if check:
                    ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
                    fail = itp.State(expr = itp.fail_expr(ag.states[0].expr))
                    check_safety_in_state(mod,ag,fail)


        checked_actions = get_checked_actions()

        if checked_actions and checked_invariants:
            print("\n    The following set of external actions must preserve the invariant:")
            for actname in sorted(checked_actions):
                action = act.env_action(actname)
                print("        {}{}".format(pretty_lineno(action),actname))
                if check:
                    ag = ivy_art.AnalysisGraph()
                    pre = itp.State()
                    pre.clauses = get_conjs(mod)
                    with itp.EvalContext(check=False): # don't check safety
    #                    post = ag.execute(action, pre, None, actname)
                        post = ag.execute(action, pre)
                    check_conjs_in_state(mod,ag,post,indent=12)
                else:
                    print('')



        callgraph = defaultdict(list)
        for actname,action in mod.actions.items():
            for called_name in action.iter_calls():
                callgraph[called_name].append(actname)

        some_assumps = False
        for actname,action in mod.actions.items():
            assumptions = [sub for sub in action.iter_subactions()
                               if isinstance(sub,act.AssumeAction)
                                  and not is_unprovable_assert(sub)]
            if assumptions:
                if not some_assumps:
                    print("\n    The following program assertions are treated as assumptions:")
                    some_assumps = True
                callers = callgraph[actname]
                if actname in mod.public_actions:
                    callers.append("the environment")
                prettyname = actname[4:] if actname.startswith('ext:') else actname
                prettycallers = [c[4:] if c.startswith('ext:') else c for c in callers]
                print("        in action {} when called from {}:".format(prettyname,','.join(prettycallers)))
                for sub in assumptions:
                    print("            {}assumption".format(pretty_lineno(sub)))

        tried = set()
        some_guarants = False
        for actname,action in mod.actions.items():
            guarantees = [sub for sub in action.iter_subactions()
                              if isinstance(sub,(act.AssertAction,act.Ranking))]
            if check_lineno is not None:
                guarantees = [sub for sub in guarantees if sub.lineno == check_lineno]
            guarantees = [x for x in guarantees if is_guarantee_mod_unprovable(x)]
            if guarantees:
                if not some_guarants:
                    print("\n    The following program assertions are treated as guarantees:")
                    some_guarants = True
                callers = callgraph[actname]
                if actname in mod.public_actions:
                    callers.append("the environment")
                prettyname = actname[4:] if actname.startswith('ext:') else actname
                prettycallers = [c[4:] if c.startswith('ext:') else c for c in callers]
                print("        in action {} when called from {}:".format(prettyname,','.join(prettycallers)))
                roots = set(iu.reachable([actname],lambda x: callgraph[x]))
                for sub in guarantees:
                    print("            {}guarantee".format(pretty_lineno(sub)), end=' ')
                    if check and any(r in roots and (r,sub.lineno) not in tried for r in checked_actions):
                        print_dots()
                        old_checked_assert = act.checked_assert.get()
                        act.checked_assert.value = sub.lineno
                        some_failed = False
                        for root in checked_actions:
                            if root in roots:
                               tried.add((root,sub.lineno))
                               action = act.env_action(root)
                               ag = ivy_art.AnalysisGraph()
                               pre = itp.State()
                               pre.clauses = get_conjs(mod)
                               with itp.EvalContext(check=False):
                                   post = ag.execute(action,prestate=pre)
                               fail = itp.State(expr = itp.fail_expr(post.expr))
                               if not check_safety_in_state(mod,ag,fail,report_pass=False):
                                   some_failed = True
                                   break
                        if not some_failed:
                            print('PASS')
                        act.checked_assert.value = old_checked_assert
                    else:
                        print("")

        im.module.assumed_invariants.extend(im.module.labeled_conjs)
        im.module.labeled_conjs = []
        if not unprovable:
            check_temporals()



# This is a little bit backward. When faced with a subgoal from the prover,
# we check it by constructing fake isolate.
                
def check_subgoals(goals,method=None):
    mod = im.module
    for goal in goals:
        # print 'goal: {}'.format(goal)
        conc = ivy_proof.goal_conc(goal)
        if isinstance(conc,ivy_ast.TemporalModels):
            model = conc.model
            fmla = conc.fmla
            if not lg.is_true(fmla):
                raise iu.IvyError(goal,
                  """The temporal subgoal {} has not been reduced to an invariance property. 
                     Try using a tactic such as l2s.""")
            mod = im.module.copy()
            mod.isolate_proof = None
            # mod.labeled_axioms.extend(proved)
            mod.labeled_props = []
            mod.concept_spaces = []
            mod.labeled_conjs = model.invars
            mod.public_actions = set(model.calls)
            mod.actions = model.binding_map
            mod.initializers = [('init',model.init)]
            mod.labeled_axioms = list(mod.labeled_axioms)
            mod.assumed_invariants = model.asms
            mod.params = list(mod.params)
            mod.updates = list(mod.updates)
            for prem in ivy_proof.goal_prems(goal):
                # if hasattr(prem,'temporal') and prem.temporal:
                if ivy_proof.goal_is_property(prem):
                    # print ('using premise: {}'.format(prem))
                    if prem.definition:
                        df = lg.drop_universals(prem.formula)
                        mod.updates.append(act.DerivedUpdate(df))
                    mod.labeled_axioms.append(prem)
                elif ivy_proof.goal_is_defn(prem):
                    dfnd = ivy_proof.goal_defines(prem)
                    if lg.is_constant(dfnd):
                        mod.params.append(dfnd)
            # ivy_printer.print_module(mod)
        else:
            pgoal = ivy_compiler.theorem_to_property(goal)
            mod = im.module.copy()
            # mod.labeled_axioms.extend(proved)
            mod.labeled_props = [pgoal]
            mod.concept_spaces = []
            mod.labeled_conjs = []
            mod.public_actions = set()
            mod.actions = dict()
            mod.initializers = []
            mod.isolate_proof = None
            mod.isolate_info = None
        with mod:
            vocab = ivy_proof.goal_vocab(goal)
            with lg.WithSymbols(vocab.symbols):
                with lg.WithSorts(vocab.sorts):
                    if method is not None:
                        if act.check_unprovable.get():
                            print("SKIPPED\n")
                            return
                        with im.module.theory_context():
                            foo = method()
                            if foo:
                                global failures
                                failures += 1
                                print("FAIL\n")
                                if hasattr(goal,"trace_hook"):
                                    foo = goal.trace_hook(foo)
                                if opt_trace.get():
                                    print(str(foo))
                                    exit(0)
                                if diagnose.get():
                                    gui_art(foo)
                            else:
                                print("PASS\n")
                    else:
                        if hasattr(goal,"trace_hook"):
                            mod.trace_hook = goal.trace_hook
                        check_isolate()
                


