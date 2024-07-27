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

debug = iu.BooleanParameter("ranking_debug",False)

def forall(vs, body):
    return lg.ForAll(vs, body) if len(vs) > 0 else body

def exists(vs, body):
    return lg.Exists(vs, body) if len(vs) > 0 else body

# TODO: This only handles combinations defined symbols
# applied to variables

def old_of(fmla):
    if ilg.is_app(fmla):
        return (itr.old(fmla.rep))(*fmla.args)
    return fmla.clone([old_of(arg) for arg in fmla.args])

def l2s_tactic(prover,goals,proof):
    tactic_name = proof.tactic_name
    vocab = ipr.goal_vocab(goals[0])
    with ilg.WithSymbols(vocab.symbols):
        with ilg.WithSorts(vocab.sorts):
            return l2s_tactic_int(prover,goals,proof,tactic_name)


def l2s_tactic_int(prover,goals,proof,tactic_name):
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

    if debug.get():
        print('ivy_ranking : the following are assumed global properties ........................')
        for gprop in assumed_gprops:
            print('     ASSUMED GPROP : ', str(gprop))
            print(' ------------------------------------------------------------------- ')

    temporal_prems = [x for x in ipr.goal_prems(goal) if hasattr(x,'temporal') and x.temporal] + [
        x for x in prover.axioms if not x.explicit and x.temporal]
    if temporal_prems:
        fmla = ilg.Implies(ilg.And(*[x.formula for x in temporal_prems]),fmla)


    if debug.get():
        print('ivy_ranking : the following are temporal premises ........................')
        for temporal_prem in temporal_prems:
            print('     TEMPORAL PREMISE : ', str(temporal_prem))
            print(' ------------------------------------------------------------------- ')
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


    l2s_d = lambda sort: lg.Const('l2s_d',lg.FunctionSort(sort,lg.Boolean))
    l2s_w = lambda vs, t: lg.NamedBinder('l2s_w', vs, proof_label, t)
    l2s_g = lambda vs, t, environ: lg.NamedBinder('l2s_g', vs, environ, t)
    old_l2s_g = lambda vs, t, environ: lg.NamedBinder('_old_l2s_g', vs, environ, t)
    l2s_init = lambda vs, t: lg.NamedBinder('l2s_init', tuple(vs), proof_label, t)
    l2s_when = lambda name, vs, t: lg.NamedBinder('l2s_when'+name, vs, proof_label, t)
    l2s_old = lambda vs, t: lg.NamedBinder('l2s_old', vs, proof_label, t)

    finite_sorts = set()
    for name,sort in ilg.sig.sorts.items():
        if thy.get_sort_theory(sort).is_finite() or name in mod.finite_sorts:
            finite_sorts.add(name)
    uninterpreted_sorts = [s for s in list(ilg.sig.sorts.values()) if type(s) is lg.UninterpretedSort and s.name not in finite_sorts]

    prems = list(ipr.goal_prems(goal))

    if True:

        def dict_put(dct,sfx,name,dfn):
            if sfx not in dct:
                dct[sfx] = dict()
            dct[sfx][name] = dfn

        def get_aux_defn(name,dct):
            for prem in prems:
                if not isinstance(prem,ivy_ast.ConstantDecl) and hasattr(prem,"definition") and prem.definition:
                    tmp = prem.formula;
                    if isinstance(tmp,lg.ForAll):
                        tmp = tmp.body
                    dname = tmp.args[0].rep.name
                    if dname.startswith(name):
                        freevs = list(ilu.variables_ast(prem.formula))
                        if freevs:
                            raise iu.IvyError(proof,'free symbol {} not allowed in definition of {}'.format(freevs[0],dname))
                        lhs = (lg.Const(dname,tmp.args[0].rep.sort))(*tmp.args[0].args)
                        dfn = tmp.clone([lhs,tmp.args[1]])
                        sfx = dname[len(name):]
                        dict_put(dct,sfx,name,dfn)

        tasks = dict()
        triggers = dict()

        get_aux_defn('work_created',tasks)
        get_aux_defn('work_needed',tasks)
        get_aux_defn('work_progress',tasks)
        get_aux_defn('work_invar',tasks)
        get_aux_defn('work_helpful',tasks)
        get_aux_defn('work_start',triggers)
        get_aux_defn('work_witness',tasks)
        
        not_all_done_preds = []
        not_all_was_done_preds = []
        sched_exists_preds = []

        sorted_tasks = list(sorted(x for x in tasks))

        # infer some predicates

        for sfx in sorted_tasks:
            if not(sfx in triggers and 'work_start' in triggers[sfx]):
                gfmla = fmla
                while isinstance(gfmla,lg.Implies):
                    gfmla = gfmla.args[1]
                if isinstance(gfmla,lg.Globally):
                    work_start = ilg.Definition(ilg.Symbol('work_start'+sfx,lg.Boolean),lg.Not(gfmla.body))
                    dict_put(triggers,sfx,'work_start',work_start)
        
        for sfx in tasks:
            for name in ['work_created','work_needed','work_progress','work_helpful']:
                if name not in tasks[sfx]:
                    raise iu.IvyError(proof,"tactic requires a definition of " + name + sfx)

        # Helpful: if the trigger implies a globally, then that globally must
        # continue hold during work_invar. We establish this by strengthening
        # work_invar.

        D = 0
        E = 1

        def trig_glob(prop,res,pos):
            if pos and isinstance(prop,lg.Globally):
                res.append(prop)
                trig_glob(prop.args[0],res,pos)
            elif not pos and isinstance(prop,lg.Eventually):
                arg = prop.args[0]
                res.append(lg.Not(prop))
                trig_glob(prop.args[0],res,pos)
            elif not pos and isinstance(prop,lg.Implies):
                trig_glob(prop.args[0],res,not pos)
                trig_glob(prop.args[1],res,pos)
            elif pos and isinstance(prop,lg.And):
                for arg in prop.args:
                    trig_glob(arg,res,pos)
            elif not pos and isinstance(prop,lg.Or):
                for arg in prop.args:
                    trig_glob(arg,res,pos)
            elif pos and isinstance(prop,lg.ForAll):
                trig_glob(prop.args[0],res,pos)
            elif not pos and isinstance(prop,lg.Exists):
                trig_glob(prop.args[0],res,pos)
            elif isinstance(prop,lg.Not):
                trig_glob(prop.args[0],res,not pos)

        def str_invar(sfx):
            work_start = triggers[sfx]['work_start']
            work_invar = tasks[sfx]['work_invar']
            globs = []
            trig_glob(work_start.args[1],globs,True)
            rhs = work_invar.args[1]
            if globs:
                rhs = lg.And(*([rhs] + globs))
            return work_invar.clone([work_invar.args[0],rhs])

        str_invar_map = {}
        for idx,sfx in enumerate(sorted_tasks):
            work_invar = str_invar(sfx)
            tasks[sfx]['work_invar'] = work_invar
            str_invar_map[work_invar.args[0].rep] = work_invar.args[1]
            
        for idx in range(len(prems)):
            prem = prems[idx]
            if not isinstance(prem,ivy_ast.ConstantDecl) and hasattr(prem,"definition") and prem.definition:
                tmp = prem.formula;
                if not isinstance(tmp,lg.ForAll):
                    sym = tmp.args[0].rep
                    if sym in str_invar_map:
                        tmp = tmp.clone([tmp.args[0],str_invar_map[sym]])
                        prems[idx] = prem.clone([prem.args[0],tmp])

        # generate the l2s invariants

        postconds = []
        invars
        helps = []
        
        for idx,sfx in enumerate(sorted_tasks):
            task = tasks[sfx] 
            work_created = task['work_created']
            work_needed = task['work_needed']
            work_progress = task['work_progress']
            work_invar = task['work_invar'].args[D]
            work_helpful = tasks[sfx]['work_helpful']
            work_start = triggers[sfx]['work_start']
            progress_args = work_progress.args[0].args
            needed_args = work_needed.args[0].args
            helpful_args = work_helpful.args[0].args
            work_witness = tasks[sfx].get('work_witness',None)

            # work_created, work_needed and work_done must have same sort
           
            if work_created.args[0].rep.sort != work_needed.args[0].rep.sort:
                raise iu.IvyError(proof,"work_created"+sfx+" and work_needed"+sfx+" must have same signature")
            if (len(work_helpful.args[0].args) < len(work_progress.args[0].args)
                or any (x != y for x,y in zip(work_helpful.args[0].args,work_progress.args[0].args))):
                raise iu.IvyError(proof,"work_helpful"+sfx+" parameters must begin with work_progress"+sfx+" parameters")
            if any (x != y for x,y in zip(helpful_args[len(progress_args):],needed_args)):
                raise iu.IvyError(proof,"extra work_helpful"+sfx+" parameters must match work_needed"+sfx+" parameters")
            if work_witness is not None and tuple(x.sort for x in work_witness.args[0].args) != tuple(x.sort for x in work_progress.args[0].args):
                raise iu.IvyError(proof,"work_witness"+sfx+" and work_progress"+sfx+" must have same signature")

            # says that all elements used in defn are in l2s_d

            def all_d(defn):
                cons = [l2s_d(var.sort)(var) for var in defn.args[0].args if var.sort.name not in finite_sorts]
                return lg.Implies(defn.args[D],lg.And(*cons))

            def all_created(defn):
                subs = dict(zip(defn.args[0].args,work_created.args[0].args))
                return lg.Implies(lu.substitute(defn.args[1],subs),work_created.args[1])

            def mklf(name, fmla):
                return ivy_ast.LabeledFormula(ivy_ast.Atom(name),fmla).sln(proof.lineno)

            def mklfs(name, fmla):
                return mklf(name+sfx,fmla)

            # invariant ls2_created
            #
            # This invariant says that every element in the work_created predicate is in l2s_d
            # 

            invars.append(mklfs("l2s_created",all_d(work_created)))

            # invariant needed_implies_created
            
            def eventually_start():
                evf = lg.Eventually(proof_label,work_start.args[1])

            # TODO: add eventually_start here
            postconds.append(mklfs("l2s_needed_implies_created",
                                old_of(lg.Implies(lg.And(work_invar,work_needed.args[D]),work_created.args[D]))))
                          
            # postcond invar_established

            not_waiting_for_trigger = lg.Not(l2s_w([],work_start.args[1])())
            postconds.append(mklfs("l2s_invar",
                                lg.Implies(lg.Or(old_of(work_invar),not_waiting_for_trigger),
                                           work_invar)))

            # postcond l2s_needed_preserved

            no_help = old_of(lg.Not(lg.Or(*helps)))

            tmp = lg.Implies(old_of(lg.And(work_invar,lg.Not(work_needed.args[D]))),lg.Not(work_needed.args[D]))
            # tmp = lg.Implies(eventually_start(),tmp)
            tmp = lg.Implies(no_help,tmp)
            postconds.append(mklfs("l2s_needed_preserved",tmp))

            helps.append(lg.And(work_invar,exists(helpful_args,work_helpful.args[E])))

            # invariant l2s_progress_made

            waiting_for_progress = l2s_w(progress_args,work_progress.args[1])(*progress_args)
            wpargs = needed_args[len(helpful_args)-len(progress_args):]
            if work_witness is None:
                decreased = exists(wpargs,lg.And(old_of(work_needed.args[D]),lg.Not(work_needed.args[D])))
            else:
                subs = {wpargs[0]:work_witness.args[1]}
                decreased = exists(wpargs[1:],lu.substitute(lg.And(old_of(work_needed.args[D]),lg.Not(work_needed.args[D])),subs))
            # tmp = lg.And(
            #     old_of(work_invar),
            #     exists(progress_args,old_of(work_helpful.args[0])),
            #     exists(needed_args,old_of(work_needed.args[0])),
            #     forall(progress_args,
            #            lg.Implies(old_of(work_helpful.args[0]),
            #                       lg.Not(waiting_for_progress)))
            # tmp = lg.Implies(tmp,decreased)
            tmp = lg.And(
                    old_of(work_invar),
                    old_of(work_helpful.args[E]),
                    lg.Not(waiting_for_progress))
            tmp = lg.Implies(tmp,decreased)
            postconds.append(mklfs("l2s_progress",tmp))

            # invariant l2s_progress_invar

            # tmp = lg.Globally(proof_label,lg.Eventually(proof_label,work_progress.args[0]))
            # tmp = lg.Implies(l2s_init(progress_args,tmp)(*progress_args),tmp)
            # invars.append(mklfs("l2s_progress_invar",tmp))

            # invariant l2s_progress_eventually

            tmp = lg.And(
                old_of(work_invar),
                old_of(work_helpful.args[E]))
            tmp = lg.Implies(tmp, lg.Eventually(proof_label,work_progress.args[1]))
            postconds.append(mklfs("l2s_progress_eventually",tmp))

            # tmp = lg.Globally(proof_label,lg.Eventually(proof_label,work_progress.args[0]))
            # tmp = lg.Implies(l2s_init(progress_args,tmp)(*progress_args),tmp)
            # invars.append(mklfs("l2s_progress_invar",tmp))
            
            # postcond l2s_sched_stable

            tmp = forall(progress_args,
                         lg.Implies(
                             lg.And(
                                 old_of(work_invar),
                                 no_help,
                                 old_of(work_helpful.args[E]),
                                 waiting_for_progress),
                             work_helpful.args[E]))
            postconds.append(mklfs("l2s_sched_stable",tmp))
            if debug:
                print(' l2s_sched_stable printout: ', tmp)
                
        # l2s_sched_exists

        if sorted_tasks:
            sfx = sorted_tasks[0]
            work_invar = tasks[sfx]['work_invar'].args[D]
            work_start = triggers[sfx]['work_start']
            tmp = old_of(lg.Implies(work_invar,lg.Or(*helps)))
            postconds.append(mklf("l2s_sched_exists",tmp))
#            invars.append(mklf("l2s_eventually_start",l2s_init([],lg.Eventually(proof_label,work_start.args[1]))()))
            invars.append(mklf("l2s_eventually_start2",lg.Implies(lg.Not(work_invar),lg.Eventually(proof_label,work_start.args[1]))))

                

        else:
            raise iu.IvyError(proof,"tactic requires at least one ranking")


        
        tmp = lg.And(*list(l2s_d(s)(c)
                           for s in uninterpreted_sorts
                           if s.name not in finite_sorts
                           for c in list(ilg.sig.symbols.values()) if c.sort == s))
        invars.append(ivy_ast.LabeledFormula(ivy_ast.Atom("l2s_consts_d"),tmp).sln(proof.lineno))

        iinvs = []

        known_inits = set([])
        
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
            invars.append(mklf("l2s_init_glob_"+str(i),ninv))
        
        invars.append(mklf("neg_prop_init",tmp))
                          
        pprems = list(x for x in prems if ipr.goal_is_property(x))
        
        winvs = []
        for tmprl in list(iu.unique(ilu.temporals_asts(invars+pprems))):
            if isinstance(tmprl,lg.WhenOperator):
                if tmprl.name == 'first':
                    nws = lg.Or(lg.Not(l2s_waiting),lg.Not(l2s_w((),tmprl.t2)))
                    tmp = lg.Implies(lg.Not(nws),lg.Eq(tmprl,lg.WhenOperator('next',tmprl.t1,tmprl.t2)))
                    tmp = lg.Implies(l2s_init((),lg.Eventually(proof_label,tmprl.t2)),tmp)
                    winvs.append(tmp)

        for i,winv in enumerate(winvs):
            invars.append(mklf("l2s_when_"+str(i),winv))


        print ('--- invariants ---')
        for inv in invars:
            print('invariant {}'.format(inv))
        print ('---------------------------')

        print ('--- postconditions ---')
        for inv in postconds:
            print('assert {}'.format(inv))
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
        for i in range(len(postconds)):
            postconds[i] = transform(postconds[i])

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
    for b in ilu.named_binders_asts(model.invars+postconds):
#        print 'binder: {} {} {}'.format(b.name,b.environ,b.body)
        named_binders_conjs[b.name].append((b.variables, b.body))
            

    def list_transform(lst,trns):
        for i in range(0,len(lst)):
            if ipr.goal_is_property(lst[i]):
                lst[i] = trns(lst[i])

    named_binders_conjs = defaultdict(list,((k,list(set(v))) for k,v in named_binders_conjs.items()))

                    
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
            lg.And(*([lg.Not(t),
                        replace_temporals_by_l2s_g(lg.Not(lg.Globally(proof_label,ilu.negate(t))))]))
        ).set_lineno(lineno)
        for vs, t in to_wait
    ]

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
    
    # post_assert = [
    #     AssertAction(xyz).set_lineno(lineno)
    #     for xyz in postconds
    # ]

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
    model.postconds = defaultdict(list)
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
                reset_w + 
                # assume_w_axioms +
                [b.action.stmt] +
                add_consts_to_d
            )).set_lineno(lineno)
            b.action.stmt.copy_formals(stmt) # HACK: This shouldn't be needed
            b.action = b.action.clone([stmt])
            # model.postconds[b.name]=[x for x in postconds if x.name != 'l2s_sched_exists']
            model.postconds[b.name]=postconds

    # The idle action handles automaton state update and cycle checking

    idle_action = concat_actions(*(
        assume_g_axioms +  # could be added to model.asms
        assume_when_axioms +
        reset_w + 
        add_consts_to_d
    )).set_lineno(lineno)
    idle_action.formal_params = []
    idle_action.formal_returns = []
    model.bindings.append(itm.ActionTermBinding('_idle',itm.ActionTerm([],[],[],idle_action)))
    model.calls.append('_idle')
    model.postconds['_idle']=postconds
    
    l2s_init = []
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

    goal.trace_hook = lambda tr,fcs: auto_hook(tasks,triggers,subs,tr,fcs)
    # goal.trace_hook = lambda tr,fcs: renaming_hook(subs,tr,fcs)

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
    # tr.hidden_symbols = temporal_and_l2s
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
    #for fc in fcs:
    #    lf = fc.lf
    #    if lf.name.startswith('l2s_progress_eventually'):
    #        sfx = lf.name[len('l2s_progress_invar'):]
    #        gfmla = rsubs[lf.formula.args[1].rep]
    #        gargs = lf.formula.args[1].args
    #        jfmla = gfmla.body.args[0]
    #        jfmla = subs[jfmla.rep]
    #        print('Justice condition found: ', jfmla)
    #        justice_pred_map[sfx] = jfmla

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
            
    elif name.startswith('l2s_needed_preserved'):
        sfx = name[len('l2s_needed_preserved'):]

        print ('\n\nFailed to prove that work_needed{} is preserved.\n'.format(sfx,sfx))
        work_needed = tasks[sfx]['work_needed']
        vs = work_needed.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_needed.args[0].rep)(*vals)
            print ('Note: work_invar{} is true and {} changes from false to true.\n'.format(sfx,pred))

    elif name.startswith('l2s_progress'):
        sfx = name[len('l2s_progress'):]

        print ('\n\nFailed to prove that work_needed{} decreases when a helpful transition occurs\n'.format(sfx,sfx))
        #lhs = invar.args[0]
        #all_helpful_happened = lhs.args[4]
        #if (ilg.is_forall(all_helpful_happened)):
        #    was_helpful_pred_nonce = all_helpful_happened.body.args[0].rep
        #else:
        #    was_helpful_pred_nonce = all_helpful_happened.args[0].rep
        #work_helpful = tasks[sfx]['work_helpful']
        #helpful_map = dict()
        #for eqn in tr.states[0].clauses.fmlas:
        #    if eqn.args[0].rep == was_helpful_pred_nonce:
        #        helpful_map[tuple(eqn.args[0].args)] = eqn.args[1]
        #        print ('{} = {}'.format(work_helpful.args[0].rep(*eqn.args[0].args),eqn.args[1]))
        #if (ilg.is_forall(all_helpful_happened)):
        #    trigger_happened_pred_nonce = all_helpful_happened.body.args[1].args[0].rep
        #else:
        #    trigger_happened_pred_nonce = all_helpful_happened.args[1].args[0].rep
        #work_progress = tasks[sfx]['work_progress']
        #happened_maps = [dict(),dict()]
        #for idx in range(2):
        #    print ('')
        #    for eqn in tr.states[idx].clauses.fmlas:
        #        if eqn.args[0].rep == trigger_happened_pred_nonce:
        #            happened_maps[idx][tuple(eqn.args[0].args)] = eqn.args[1]
        #            print ('~happened {} = {}'.format(work_progress.args[0].rep(*eqn.args[0].args),eqn.args[1]))
        #justice_map = dict()
        #if sfx in justice_pred_map:
        #    print ('')
        #    justice_pred = justice_pred_map[sfx]
        #    for eqn in tr.states[0].clauses.fmlas:
        #        if eqn.args[0].rep == justice_pred:
        #            justice_map[tuple(eqn.args[0].args)] = eqn.args[1]
        #            print ('~eventually {} = {}'.format(work_progress.args[0].rep(*eqn.args[0].args),eqn.args[1]))
        #for args in helpful_map:
        #    if ilg.is_true(helpful_map[args]):
        #        if all(args in happened_maps[idx] for idx in range(2)):
        #            if ilg.is_true(happened_maps[0][args]) and ilg.is_false(happened_maps[1][args]):
        #                print ('\nNote: {} is true and {} occurs during the action, but work_needed is not reduced.\n'.format(work_helpful.args[0].rep(*args),work_progress.args[0].rep(*args)))
        #                break
        #for args in helpful_map:
        #    if ilg.is_true(helpful_map[args]):
        #        if args in justice_map:
        #            if ilg.is_true(happened_maps[0][args]) and ilg.is_true(justice_map[args]):
        #                print ('\nNote: {} is true and eventually {} is false.\n'.format(work_helpful.args[0].rep(*args),work_progress.args[0].rep(*args)))
        #                break
        work_needed = tasks[sfx]['work_needed']
        vs = work_needed.args[0].args
        sks = [ilg.Symbol('@'+v.name,v.sort) for v in vs]
        post_state = tr.states[-1]
        vals = [tr.eval_in_state(post_state,sk) for sk in sks]
        if None not in vals:
            pred = (work_needed.args[0].rep)(*vals)
            print ('Note: work_invar{} is true and {} changes from false to true.\n'.format(sfx,pred))

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
        
    elif name.startswith('l2s_sched_exists'):
        rank_names = ' and '.join('work_helpful'+sfx for sfx in tasks if 'work_helpful' in tasks[sfx])
        print ('The helpful set(s)  {} have become empty, but termination has not occurred'.format(rank_names))

    return tr
            
        
        
    
            
            

# Register the l2s tactics

ipr.register_tactic('ranking',l2s_tactic)
