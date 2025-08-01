#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
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
from . import ivy_ranking
from . import ivy_mc
from . import ivy_vmt
from . import ivy_duoai
from . import ivy_bmc
from . import ivy_tactics
from . import ivy_mypyvy

print ('starting ivy_check...')

import sys
from collections import defaultdict

diagnose = iu.BooleanParameter("diagnose",False)
coverage = iu.BooleanParameter("coverage",True)
checked_action = iu.Parameter("action","")
opt_trusted = iu.BooleanParameter("trusted",False)
opt_mc = iu.BooleanParameter("mc",False)
opt_trace = iu.BooleanParameter("trace",False)
opt_separate = iu.BooleanParameter("separate",None)
opt_method = iu.Parameter("method","")

def display_cex(msg,ag):
    if diagnose.get():
        from . import tk_ui as ui
        iu.set_parameters({'mode':'induction'})
        ui.ui_main_loop(ag)
        exit(1)
    raise iu.IvyError(None,msg)
    
def check_properties():
    if itp.false_properties():
        if diagnose.get():
            print("Some properties failed.")
            from . import tk_ui as ui
            iu.set_parameters({'mode':'induction'})
            gui = ui.new_ui()
            gui.tk.update_idletasks() # so that dialog is on top of main window
            gui.try_property()
            gui.mainloop()
            exit(1)
        raise iu.IvyError(None,"Some properties failed.")
    im.module.labeled_axioms.extend(im.module.labeled_props)
    im.module.update_theory()

def show_counterexample(ag,state,bmc_res):
    universe,path = bmc_res
    other_art = ivy_art.AnalysisGraph()
    ag.copy_path(state,other_art,None)
    for state,value in zip(other_art.states[-len(path):],path):
        state.value = value
        state.universe = universe
    gui_art(other_art)

def gui_art(other_art):
    from . import tk_ui as ui
#    iu.set_parameters({'mode':'induction'})
#    iu.set_parameters({'ui':'cti'})
    gui = ui.new_ui()
    if ivy_ui.default_ui.get() == "art":
        print ("initializers: {}".format(im.module.initializers))
        other_art = ivy_art.AnalysisGraph()
        other_art.add_initial_state()
        if 'initialize' in im.module.actions:
            init_action = im.module.actions['initialize']
            print ("initialize: {}".format(init_action))
            ag.execute(init_action, None, None, 'initialize')
    agui = gui.add(other_art)
    gui.tk.update_idletasks() # so that dialog is on top of main window
    gui.tk.mainloop()
    exit(1)

    
def check_conjectures(kind,msg,ag,state):
    failed = itp.undecided_conjectures(state)
    if failed:
        if diagnose.get():
            print("{} failed.".format(kind))
            from . import tk_ui as ui
            iu.set_parameters({'mode':'induction'})
            gui = ui.new_ui()
            agui = gui.add(ag)
            gui.tk.update_idletasks() # so that dialog is on top of main window
            agui.try_conjecture(state,msg="{}\nChoose one to see counterexample.".format(msg),bound=1)
            gui.tk.mainloop()
            exit(1)
        raise iu.IvyError(None,"{} failed.".format(kind))

def has_temporal_stuff(f):
    return any(True for x in lut.temporals_ast(f)) or any(True for x in lut.named_binders_ast(f))

    
# This is a little tricky. We know that the current module is a valid abstraction of the
# program, thus module |= prop implies prop. We tell the prover to trust us and admit
# prop if module |= prop holds.

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


def usage():
    print("usage: \n  {} file.ivy".format(sys.argv[0]))
    sys.exit(1)

def find_assertions(action_name=None):
    res = []
    actions = act.call_set(action_name,im.module.actions) if action_name else list(im.module.actions.keys())
    for actname in actions:
        action = im.module.actions[actname]
        for a in action.iter_subactions():
            if isinstance(a,act.AssertAction) or isinstance(a,act.Ranking):
                res.append(a)
    return res

def show_assertions():
    for a in find_assertions():
        print('{}: {}'.format(a.lineno,a))

checked_action_found = False

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

def is_unprovable(lf):
    return hasattr(lf,'unprovable') and lf.unprovable

def is_check_mod_unprovable(lf):
    return is_unprovable(lf) == act.check_unprovable.get()

class Checker(object):
    def __init__(self,conj,report_pass=True,invert=True):
        self.fc = lut.formula_to_clauses(conj)
        if invert:
            def witness(v):
                return lg.Symbol('@' + v.name, v.sort)
            self.fc = lut.dual_clauses(self.fc,witness)
        self.report_pass = report_pass
        self.failed = False
    def cond(self):
        return self.fc
    def start(self):
        if self.report_pass:
            print_dots()
    def sat(self):
        return self._pass() if act.check_unprovable.get() else self.fail()
        print('FAIL')
        global failures
        failures += 1
        self.failed = True
        return not (diagnose.get() or opt_trace.get()) # ignore failures if not diagnosing
    def unsat(self):
        return self.fail() if act.check_unprovable.get() else self._pass()
    def assume(self):
        return False
    def get_annot(self):
        return None
    def fail(self):
        print('FAIL')
        global failures
        failures += 1
        self.failed = True
        return not (diagnose.get() or opt_trace.get()) or act.check_unprovable.get() # ignore failures if not diagnosing
    def _pass(self):
        if self.report_pass:
            print('PASS')
        return True

def pretty_label(label):
    return "(no name)" if label is None else label

def pretty_lineno(ast):
    return str(ast.lineno) if hasattr(ast,'lineno') else '(internal) '

def pretty_lf(lf,indent=8):
    return indent*' ' + "{}{}".format(pretty_lineno(lf),pretty_label(lf.label))
    
class ConjChecker(Checker):
    def __init__(self,lf,indent=8):
        self.lf = lf
        self.indent = indent
        Checker.__init__(self,lf.formula)
    def start(self):
        print(pretty_lf(self.lf,self.indent), end=' ')
        print_dots()
    def get_annot(self):
        return self.lf.annot if hasattr(self.lf,'annot') else None
    
class ConjAssumer(Checker):
    def __init__(self,lf):
        self.lf = lf
        Checker.__init__(self,lf.formula,invert=False)
    def start(self):
        print(pretty_lf(self.lf) + "  [assumed]")
    def assume(self):
        return True

class MatchHandler(object):
    def __init__(self,clauses,model,vocab):
#        iu.dbg('clauses')
        self.clauses = clauses
        self.model = model
        self.vocab = vocab
        self.current = dict()
        mod_clauses = islv.clauses_model_to_clauses(clauses,model=model,numerals=True)
#        iu.dbg('mod_clauses')
        self.eqs = defaultdict(list)
        for fmla in mod_clauses.fmlas:
            if lg.is_eq(fmla):
                lhs,rhs = fmla.args
                if lg.is_app(lhs):
                    self.eqs[lhs.rep].append(fmla)
            elif isinstance(fmla,lg.Not):
                app = fmla.args[0]
                if lg.is_app(app):
                    self.eqs[app.rep].append(lg.Equals(app,lg.Or()))
            else:
                if lg.is_app(fmla):
                    self.eqs[fmla.rep].append(lg.Equals(fmla,lg.And()))
        # for sym in vocab:
        #     if not itr.is_new(sym) and not itr.is_skolem(sym):
        #         self.show_sym(sym,sym)
        self.started = False
        self.renaming = dict()
        print()
        print('Trace follows...')
        print(80 * '*')

    def show_sym(self,sym,renamed_sym):
        if sym in self.renaming and self.renaming[sym] == renamed_sym:
            return
        self.renaming[sym] = renamed_sym
        rmap = {renamed_sym:sym}
        # TODO: what if the renamed symbol is not in the model?
        for fmla in self.eqs[renamed_sym]:
            rfmla = lut.rename_ast(fmla,rmap)
            lhs,rhs = rfmla.args
            if lhs in self.current and self.current[lhs] == rhs:
                continue
            self.current[lhs] = rhs
            print('    {}'.format(rfmla))
        
    def eval(self,cond):
        truth = self.model.eval_to_constant(cond)
        if lg.is_false(truth):
            return False
        elif lg.is_true(truth):
            return True
        assert False,truth
        
    def is_skolem(self,sym):
        res = itr.is_skolem(sym) and not (sym.name.startswith('__') and sym.name[2:3].isupper())
        return res

    def handle(self,action,env):
        
#        iu.dbg('env')
        if hasattr(action,'lineno'):
#            print '        env: {}'.format('{'+','.join('{}:{}'.format(x,y) for x,y in env.iteritems())+'}')
#            inv_env = dict((y,x) for x,y in env.iteritems())
            if not self.started:
                for sym in self.vocab:
                    if sym not in env and not itr.is_new(sym) and not self.is_skolem(sym):
                        self.show_sym(sym,sym)
                self.started = True
            for sym,renamed_sym in env.items():
                if not itr.is_new(sym) and not self.is_skolem(sym):
                    self.show_sym(sym,renamed_sym)

            print('{}{}'.format(action.lineno,action))

    def do_return(self,action,env):
        pass

    def end(self):
        for sym in self.vocab:
            if not itr.is_new(sym) and not self.is_skolem(sym):
                self.show_sym(sym,sym)
            
    def fail(self):
        pass

                
def filter_fcs(fcs):
    global check_lineno
    if check_lineno is None:
        return fcs
    return [fc for fc in fcs if (not isinstance(fc,ConjChecker) or fc.lf.lineno == check_lineno)]

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

def convert_postconds(state,postconds):
    updated,postcond,pre = state.update if state.update is not None else ([],None,None)
    renaming = dict((s,itr.old_of(s))
                    for s in lut.used_symbols_asts(x.formula for x in postconds)
                    if itr.is_old(s))
    for s in updated:
        renaming[itr.old(s)] = s.prefix('__')
    return [x.clone([x.args[0],lut.rename_ast(x.formula,renaming)])
            for x in postconds]

def check_conjs_in_state(mod,ag,post,indent=8,pcs=[]):
    conjs = mod.conj_subgoals if mod.conj_subgoals is not None else mod.labeled_conjs
    conjs = [x for x in conjs if is_check_mod_unprovable(x)]
    conjs += convert_postconds(post,pcs)
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

opt_summary = iu.BooleanParameter("summary",False)

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




def check_isolate(trace_hook = None):
    mod = im.module
    if mod.isolate_proof is not None:
        axioms = mod.labeled_axioms + mod.assumed_invariants + [x for x in mod.labeled_props if x.assumed]
        defns = [ivy_proof.definition_to_goal(x) for x in mod.definitions]
        pc = ivy_proof.ProofChecker([],[],mod.schemata)
        model = itmp.normal_program_from_module(im.module)
        prop = ivy_proof.make_goal(mod.isolate_proof.lineno, 'safety', [], lg.And())
        subgoal = ivy_proof.make_goal(mod.isolate_proof.lineno,'safety',
                                      defns + axioms, ivy_ast.TemporalModels(model,lg.And()))
        #        print 'subgoal = {}'.format(subgoal)
        subgoals = [subgoal]
        subgoals = pc.admit_proposition(prop,mod.isolate_proof,subgoals)
        # TRICKY: when checking the isolate proof, we don't the axioms
        # and definitions in the module context by default. This allows the
        # tactics to drop axioms and definitions.  For historical
        # reasons, when checking temporal properties we *do* use the
        # context. This should probably be changed, but it requires some
        # substantial chages to the liveness tactics. 
        check_subgoals(subgoals,use_context=False)
        return
 
    ifc.check_fragment()
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

        if (mod.labeled_props or schema_instances) and not checked_action.get():
            print("\n    The following properties are to be checked:")
            if check:
                for lf in schema_instances:
                    print(pretty_lf(lf) + " [proved by axiom schema]")
                ag = ivy_art.AnalysisGraph()
                clauses1 = lut.true_clauses(annot=act.EmptyAnnotation())
                pre = itp.State(value = clauses1)
                props = [x for x in im.module.labeled_props if not x.temporal]
                props = [p for p in props if not(p.id in subgoalmap and p.explicit)]
                props = [p for p in props if is_check_mod_unprovable(p)]
                fcs = ([(ConjAssumer if prop.assumed or prop.id in subgoalmap else ConjChecker)(prop) for prop in props])
                check_fcs_in_state(mod,ag,pre,fcs)
            else:
                for lf in schema_instances + mod.labeled_props:
                    print(pretty_lf(lf))

        # after checking properties, make them axioms, except temporals
        im.module.labeled_axioms.extend(p for p in im.module.labeled_props if not p.temporal and not is_unprovable(p))
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
                    check_conjs_in_state(mod,ag,post,indent=12,pcs=mod.postconds.get(actname,[]))
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
                
def check_subgoals(goals,method=None,use_context=True):
    mod = im.module
    for goal in goals:
        # print 'goal: {}'.format(goal)
        conc = ivy_proof.goal_conc(goal)
        if isinstance(conc,ivy_ast.TemporalModels):
            model = conc.model
            fmla = conc.fmla
            if not lg.is_true(fmla):
                raise IvyError(goal,
                  """The temporal subgoal {} has not been reduced to an invariance property. 
                     Try using a tactic such as l2s.""")
            mod = im.module.copy()
            mod.isolate_proof = None
            # mod.labeled_axioms.extend(proved)
            mod.labeled_props = []
            mod.concept_spaces = []
            mod.labeled_conjs = model.invars
            mod.postconds = model.postconds if hasattr(model,'postconds') else {}
            mod.public_actions = set(model.calls)
            mod.actions = model.binding_map
            mod.initializers = [('init',model.init)]
            mod.labeled_axioms = list(mod.labeled_axioms)
            mod.assumed_invariants = model.asms
            mod.params = list(mod.params)
            mod.updates = list(mod.updates)
            if not use_context: 
                mod.labeled_axioms = []
                mod.definitions = []
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
                
def mc_tactic(prover,goals,proof):
    goal = goals[0]
    conc = ivy_proof.goal_conc(goal)
    if isinstance(conc,ivy_ast.TemporalModels):
        if not lg.is_true(conc.fmla):
            goals = ivy_tactics.tempind(prover,goals,proof)
            goals = ivy_tactics.skolemizenp(prover,goals,proof)
            l2s_pf = proof.clone([proof.args[0],ivy_ast.TacticLets()]+list(proof.args[2:]))
            goals = ivy_l2s.l2s_tactic_full(prover,goals,l2s_pf)
    check_subgoals(goals[0:1],method=ivy_mc.check_isolate)
    return goals[1:]

ivy_proof.register_tactic('mc',mc_tactic)

def vmt_tactic(prover,goals,proof):
    goal = goals[0]
    conc = ivy_proof.goal_conc(goal)
    if isinstance(conc,ivy_ast.TemporalModels):
        if not lg.is_true(conc.fmla):
            goals = ivy_tactics.tempind(prover,goals,proof)
            goals = ivy_tactics.skolemizenp(prover,goals,proof)
            l2s_pf = proof.clone([proof.args[0],ivy_ast.TacticLets()]+list(proof.args[2:]))
            goals = ivy_l2s.l2s_tactic_full(prover,goals,l2s_pf)
    check_subgoals(goals[0:1],method=ivy_vmt.check_isolate)
    return goals[1:]

ivy_proof.register_tactic('vmt',vmt_tactic)
                    
def mypyvy_tactic(prover,goals,proof):
    goal = goals[0]
    conc = ivy_proof.goal_conc(goal)
    if isinstance(conc,ivy_ast.TemporalModels):
        if not lg.is_true(conc.fmla):
            goals = ivy_tactics.tempind(prover,goals,proof)
            goals = ivy_tactics.skolemizenp(prover,goals,proof)
            l2s_pf = proof.clone([proof.args[0],ivy_ast.TacticLets()]+list(proof.args[2:]))
            goals = ivy_l2s.l2s_tactic_full(prover,goals,l2s_pf)
    check_subgoals(goals[0:1],method=ivy_mypyvy.check_isolate)
    return goals[1:]

ivy_proof.register_tactic('mypyvy',mypyvy_tactic)

def duoai_tactic(prover,goals,proof):
    goal = goals[0]
    conc = ivy_proof.goal_conc(goal)
    if isinstance(conc,ivy_ast.TemporalModels):
        if not lg.is_true(conc.fmla):
            goals = ivy_tactics.tempind(prover,goals,proof)
            goals = ivy_tactics.skolemizenp(prover,goals,proof)
            l2s_pf = proof.clone([proof.args[0],ivy_ast.TacticLets()]+list(proof.args[2:]))
            goals = ivy_l2s.l2s_tactic_full(prover,goals,l2s_pf)
    check_subgoals(goals[0:1],method=ivy_duoai.check_isolate)
    return goals[1:]

ivy_proof.register_tactic('duoai',duoai_tactic)
                    
def all_assert_linenos():
    mod = im.module
    all = []
    for actname,action in mod.actions.items():
        guarantees = [sub.lineno for sub in action.iter_subactions()
                      if isinstance(sub,(act.AssertAction,act.Ranking))]
        all.extend(guarantees)
    all.extend(lf.lineno for lf in mod.labeled_conjs)
    seen = set()
    res = []
    for lineno in all:
        if not lineno in seen:
            res.append(lineno)
            seen.add(lineno)
    check_lineno = act.checked_assert.get()
    if check_lineno:
        if check_lineno in seen:
            return [check_lineno]
        raise iu.IvyError(None,'There is no assertion at the specified line')
    return res

def get_isolate_attr(isolate,attr_name,default=None):
    if isolate is None:
        return default
    attr = iu.compose_names(isolate,attr_name)
    if attr not in im.module.attributes:
        parent,child = iu.parent_child_name(isolate)
        if child == 'iso':
            attr = iu.compose_names(parent,attr_name)
        if attr not in im.module.attributes:
            return default
    return im.module.attributes[attr].rep

def check_separately(isolate):
    if opt_separate.get() is not None:
        return opt_separate.get()
    return get_isolate_attr(isolate,'separate','false') == 'true'

def mc_isolate(isolate,meth=ivy_mc.check_isolate):
    im.module.labeled_axioms.extend(lf for lf in im.module.labeled_props if lf.assumed)
    im.module.labeled_props = [lf for lf in im.module.labeled_props if not lf.assumed]
    if any(not x.temporal for x in im.module.labeled_props):
        raise iu.IvyError(im.module.labeled_props[0],'model checking not supported for property yet')
    if not check_separately(isolate):
        with im.module.theory_context():
            res = meth()
            if res is not None:
                print(res)
                print('FAIL')
                exit(1)
        return
    for lineno in all_assert_linenos():
        with im.module.copy():
            old_checked_assert = act.checked_assert.get()
            act.checked_assert.value = lineno
            with im.module.theory_context():
                res = meth()
            if res is not None:
                print(res)
                print('FAIL')
                exit(1)
            act.checked_assert.value = old_checked_assert
    
def get_isolate_method(isolate):
    if opt_mc.get():
        return 'mc'
    if opt_method.get():
        return opt_method.get()
    return get_isolate_attr(isolate,'method','ic')


def check_module():
    # If user specifies an isolate, check it. Else, if any isolates
    # are specificied in the file, check all, else check globally.

    missing = []

    isolate = ivy_compiler.isolate.get()
    if isolate != None:
        isolates = [isolate]
    else:
        isolates = sorted(list(im.module.isolates))
        if len(isolates) == 0:
            isolates = [None]
        else:
            if coverage.get():
                missing = ivy_isolate.check_isolate_completeness()
    if missing:
        raise iu.IvyError(None,"Some assertions are not checked")

    for isolate in isolates:
        if isolate is not None and isolate in im.module.isolates:
            idef = im.module.isolates[isolate]
            if len(idef.verified()) == 0 or isinstance(idef,ivy_ast.TrustedIsolateDef):
                continue # skip if nothing to verify
        if isolate:
            print("\nIsolate {}:".format(isolate))
        if isolate is not None and iu.compose_names(isolate,'macro_finder') in im.module.attributes:
            save_macro_finder = islv.opt_macro_finder.get()
            if save_macro_finder:
                print("Turning off macro_finder")
                islv.set_macro_finder(False)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            if opt_trusted.get():
                continue
            method_name = get_isolate_method(isolate)
            if method_name == 'convert_to_mypyvy':
                ivy_mypyvy.check_isolate()
            elif method_name == 'mc':
                mc_isolate(isolate)
            elif method_name == 'vmt':
                mc_isolate(isolate,meth=ivy_vmt.check_isolate)
            elif method_name.startswith('bmc['):
                global some_bounded
                some_bounded = True
                _,prms = iu.parse_int_subscripts(method_name)
                if len(prms) < 1 or len(prms) > 2:
                    raise IvyError(None,'BMC method specifier should be bmc[<steps>] or bmc[<steps>][<unroll>]. Got "{}".'.format(method_name))
                mc_isolate(isolate,lambda : ivy_bmc.check_isolate(prms[0],n_unroll = prms[1] if len(prms) >= 2 else None))
            else:
                logic = get_isolate_attr(isolate,'complete',None)
                if logic is not None:
                    im.module.logics = [logic]
                check_isolate()
        if isolate is not None and iu.compose_names(isolate,'macro_finder') in im.module.attributes:
            if save_macro_finder:
                print("Turning on macro_finder")
                islv.set_macro_finder(True)
    print('')
    if failures > 0:
        raise iu.IvyError(None,"failed checks: {}".format(failures))
    if checked_action.get() and not checked_action_found:
        raise iu.IvyError(None,"{} is not an exported action of any isolate".format(checked_action.get()))

    cact = checked_action.get()


def main():
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    from . import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    ivy_init.read_params()
    if len(sys.argv) != 2 or not sys.argv[1].endswith('ivy'):
        usage()
    global some_bounded
    some_bounded = False

    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1],ivy_init.open_read(sys.argv[1]),create_isolate=False)
            if isinstance(act.checked_assert.get(),iu.LocationTuple) and act.checked_assert.get().filename == 'none.ivy' and act.checked_assert.get().line == 0:
                print('NOT CHECKED')
                exit(0);
            check_module()
    if some_bounded:
        print("BOUNDED")
    if ivy_tactics.used_sorry:
        print("OK, but used 'sorry'")
    else:
        print("OK")


if __name__ == "__main__":
    main()

