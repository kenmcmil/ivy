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

debug = iu.BooleanParameter('compose_debug',False)

def compose_tactic(prover,goals,proof):
    tactic_name = proof.tactic_name
    vocab = ipr.goal_vocab(goals[0])
    with ilg.WithSymbols(vocab.symbols):
        with ilg.WithSorts(vocab.sorts):
            return compose_tactic_int(prover,goals,proof,tactic_name)

def get_aux_defn(prems, proof, name):
    defns = {}
    def dict_put(sfx,name,dfn):
        if name in defns:
            defns[name][sfx] = dfn
        else:
            defns[name] = {}
            defns[name][sfx] = dfn

    for prem in prems:
        if not isinstance(prem,ivy_ast.ConstantDecl) and hasattr(prem,"definition") and prem.definition:
            tmp = prem.formula
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
                dict_put(sfx,name,dfn)

    return defns

def create_ranking_defn(sfx, work_created_fmla, work_needed_fmla, work_progress_fmla, work_invar_fmla, work_helpful):
    work_created = ilg.Definition(ilg.Symbol("work_created"+sfx),lg.Boolean, work_created_fmla)
    work_needed = ilg.Definition(ilg.Symbol("work_needed"))
    for sfx in sorted_tasks:
        if not(sfx in triggers and 'work_start' in triggers[sfx]):
            gfmla = fmla
            while isinstance(gfmla,lg.Implies):
                gfmla = gfmla.args[1]
            if isinstance(gfmla,lg.Globally):
                work_start = ilg.Definition(ilg.Symbol('work_start'+sfx,lg.Boolean),lg.Not(gfmla.body))
                dict_put(triggers,sfx,'work_start',work_start)



def compose_tactic_int(prover,goals,proof,tactic_name):
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

    

ipr.register_tactic('ranking',compose_tactic)
