#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from typing import Any
from . import ivy_actions as ia
from . import ivy_ast as ast
from . import ivy_logic as il
from . import ivy_module as im
from . import ivy_proof as pf
from . import ivy_solver
from . import ivy_trace as it
from . import ivy_transrel as itr
from . import ivy_utils as iu

from . import logic as lg
from . import mypyvy_syntax as pyv

import time
from ivy.z3 import z3

logfile = None
verbose = False

opt_unfold_macros = iu.BooleanParameter("unfold_macros",True)
opt_simplify = iu.BooleanParameter("simplify",False)

# Ivy symbols have dots in them (due to the module system)
# but mypyvy doesn't allow dots in names, so we replace
# them with this string
DOT_REPLACEMENT = "_"
BRACE_REPLACEMENT = '_B_'
COLON_REPLACEMENT = "_c_"

# This is how Ivy internally represents true and false
_true = lg.And()
_false = lg.Or()

IVY_TEMPORARY_INDICATOR = '__m_'
IVY_TSEITIN_INDICATOR = '__ts'

def is_temporary_constant(f) -> bool:
    TEMP_INDICATORS = [IVY_TEMPORARY_INDICATOR, IVY_TSEITIN_INDICATOR, '__fml', '__new']
    return any(f.name.startswith(x) for x in TEMP_INDICATORS)

def check_simpl_equiv(orig, simp):
    '''Check that orig and simp are equivalent, via SMT'''
    orig_z3 = ivy_solver.formula_to_z3(orig)
    simp_z3 = ivy_solver.formula_to_z3(simp)
    s = z3.Solver()
    s.add(z3.Not(z3.Implies(orig_z3, simp_z3)))
    res = s.check()
    if res != z3.unsat:
        with open('orig.smt2', 'w') as f:
            f.write(orig_z3.sexpr())
        with open('simp.smt2', 'w') as f:
            f.write(simp_z3.sexpr())
    assert res == z3.unsat, "Solver returned {} | orig and simp are not equivalent: {}\n not equivalent to\n{}".format(res, orig_z3, simp_z3)

class Translation:
    '''Helper class for translating Ivy expressions to mypyvy expressions.'''
    def sort_type(ivy_sort):
        if il.is_function_sort(ivy_sort) and il.is_boolean_sort(ivy_sort.rng):
            return 'relation'
        elif il.is_function_sort(ivy_sort):
            return 'function'
        return 'individual'

    def to_pyv_sort(ivy_sort):
        if il.is_first_order_sort(ivy_sort) \
            or il.is_enumerated_sort(ivy_sort):
            return pyv.UninterpretedSort(ivy_sort.name)
        elif il.is_boolean_sort(ivy_sort):
            return pyv.BoolSort
        # Relation
        elif il.is_function_sort(ivy_sort) and il.is_boolean_sort(ivy_sort.rng):
            # FIXME: do we need the bool for rng?
            return tuple([Translation.to_pyv_sort(x) for x in ivy_sort.dom])
        elif il.is_function_sort(ivy_sort):
            return (tuple([Translation.to_pyv_sort(x) for x in ivy_sort.dom]), Translation.to_pyv_sort(ivy_sort.rng))
        else:
            raise NotImplementedError("translating sort {} to mypyvy ".format(repr(ivy_sort)))

    def to_pyv_name(ivy_name):
        if isinstance(ivy_name, str):
            name = ivy_name.replace(".", DOT_REPLACEMENT)
            name = name.replace('[', BRACE_REPLACEMENT)
            name = name.replace(']', BRACE_REPLACEMENT)
            name = name.replace(':', COLON_REPLACEMENT)
            return name
        raise Exception("cannot translate non-string name {} to mypyvy ".format(repr(ivy_name)))

    def translate_binders(binders) -> tuple[pyv.SortedVar]:
        '''Translate [var_name:var_sort] into mypyvy.'''
        vars = []
        for binder in binders:
            name = Translation.to_pyv_name(binder.name)
            sort = Translation.to_pyv_sort(binder.sort)
            vars.append(pyv.SortedVar(name, sort, None))
        return vars

    def smt_binder_name_to_ivy_name(name: str) -> str:
        # For some reason, SMT vars incorporate the sort,
        # like 'X:integer'; we only want the 'X'
        return name.split(':')[0]

    def smt_binders_to_ivy(sorts: dict[str, Any], fmla: z3.BoolRef):
        '''Convert the binders of an SMT formula to Ivy binders.
        sorts: dictionary from sort names to Ivy sorts
        '''
        assert z3.is_ast(fmla) and z3.is_expr(fmla) and z3.is_quantifier(fmla)
        num_binders = fmla.num_vars()
        binders = [lg.Var(Translation.smt_binder_name_to_ivy_name(fmla.var_name(i)), sorts[fmla.var_sort(i).name()]) for i in range(num_binders)]
        return binders

    def translate_symbol_decl(sym: il.Symbol, is_mutable=True) -> pyv.Decl:
        sort = sym.sort
        kind = Translation.sort_type(sort)
        name = Translation.to_pyv_name(sym.name)

        if kind == 'individual':
            pyv_sort = Translation.to_pyv_sort(sort)
            const = pyv.ConstantDecl(name, pyv_sort, is_mutable)
            return const
        elif kind == 'relation':
            assert sym.is_relation()
            pyv_sort = Translation.to_pyv_sort(sort)
            rel = pyv.RelationDecl(name, pyv_sort, is_mutable)
            return rel
        elif kind == 'function':
            (dom_sort, rng_sort) = Translation.to_pyv_sort(sort)
            fn = pyv.FunctionDecl(name, dom_sort, rng_sort, is_mutable)
            return fn
        else:
            raise NotImplementedError("translating symbol {} to mypyvy ".format(repr(sym)))
 
    def pyv_havoc_symbol(sym: il.Symbol) -> pyv.Expr:
        '''Return a two-state formula that havocs the given symbol.'''
        sort = sym.sort
        sym = itr.new(sym) # we want to talk about the new version
        vvar = lg.Var("V", sort.rng)

        fmla = None
        if len(sort.dom) == 0:
            # exists V in sort.rng. cst = V
            fmla = lg.Exists([vvar], lg.Eq(sym, vvar))
        else:
            # forall X0 X1 X2 in sort.dom. exists V in sort.rng. rel(X,Y,Z) = V
            uvars = [lg.Var("X{}".format(i), sort.dom[i]) for i in range(len(sort.dom))]
            ex = lg.Exists([vvar], lg.Eq(lg.Apply(sym, *uvars), vvar))
            fmla = lg.ForAll(uvars, ex)

        return Translation.translate_logic_fmla(fmla, is_twostate=True)

    def pyv_unchanged_symbol(sym: il.Symbol) -> pyv.Expr:
        '''Return a two-state formula that asserts the given symbol is unchanged.'''
        sort = sym.sort
        old_sym = sym
        sym = itr.new(sym) # we want to talk about the new version
        vvar = lg.Var("V", sort.rng)

        fmla = None
        if len(sort.dom) == 0:
            # new(cst) = cst
            fmla = lg.Eq(sym, old_sym)
        else:
            # forall X0 X1 X2 in sort.dom. new(rel(X,Y,Z)) = rel(X, Y, Z)
            uvars = [lg.Var("X{}".format(i), sort.dom[i]) for i in range(len(sort.dom))]
            eq = lg.Eq(lg.Apply(sym, *uvars), lg.Apply(old_sym, *uvars))
            fmla = lg.ForAll(uvars, eq)

        return Translation.translate_logic_fmla(fmla, is_twostate=True)
    
    def smt_to_ivy(fmla: z3.BoolRef, sorts: dict[str, Any], syms: dict[str, Any], binders=[]) -> lg.And:
        '''Convert an SMT formula to an Ivy formula.
        sorts: dict from sort names to Ivy sorts
        syms: dict from symbol names to Ivy symbols
        '''
        assert z3.is_ast(fmla) and z3.is_expr(fmla)

        # Quantifiers
        # https://stackoverflow.com/questions/13357509/is-it-possible-to-access-the-name-associated-with-the-de-bruijn-index-in-z3
        if z3.is_quantifier(fmla) and fmla.is_forall():
            # How to translate the sorts of the vars?
            new_binders = Translation.smt_binders_to_ivy(sorts, fmla)
            # XXX: this seems to work, but I'm not sure it's correct
            binders = list(reversed(new_binders)) + binders
            return lg.ForAll(new_binders, Translation.smt_to_ivy(fmla.body(), sorts, syms, binders))
        elif z3.is_quantifier(fmla): # strangely, there is no is_exists()
            new_binders = Translation.smt_binders_to_ivy(sorts, fmla)
            binders = list(reversed(new_binders)) + binders
            return lg.Exists(new_binders, Translation.smt_to_ivy(fmla.body(), sorts, syms, binders))
        # Unary ops
        elif z3.is_not(fmla):
            return lg.Not(Translation.smt_to_ivy(fmla.children()[0], sorts, syms, binders))
        # Binary ops
        elif z3.is_and(fmla):
            return lg.And(*[Translation.smt_to_ivy(x, sorts, syms, binders) for x in fmla.children()])
        elif z3.is_or(fmla):
            return lg.Or(*[Translation.smt_to_ivy(x, sorts, syms, binders) for x in fmla.children()])
        elif z3.is_eq(fmla):
            return lg.Eq(Translation.smt_to_ivy(fmla.children()[0], sorts, syms, binders), Translation.smt_to_ivy(fmla.children()[1], sorts, syms, binders))
        elif z3.is_app_of(fmla, z3.Z3_OP_IMPLIES):
            return lg.Implies(Translation.smt_to_ivy(fmla.children()[0], sorts, syms, binders), Translation.smt_to_ivy(fmla.children()[1], sorts, syms, binders))
        elif z3.is_app_of(fmla, z3.Z3_OP_IFF):
            return lg.Iff(Translation.smt_to_ivy(fmla.children()[0], sorts, syms, binders), Translation.smt_to_ivy(fmla.children()[1], sorts, syms, binders))
        # Ternary
        elif z3.is_app_of(fmla, z3.Z3_OP_ITE):
            return lg.Ite(Translation.smt_to_ivy(fmla.children()[0], sorts, syms, binders), Translation.smt_to_ivy(fmla.children()[1], sorts, syms, binders), Translation.smt_to_ivy(fmla.children()[2], sorts, syms, binders))
        # Constants
        elif z3.is_true(fmla):
            return _true
        elif z3.is_false(fmla):
            return _false
        elif z3.is_const(fmla):
            name = fmla.decl().name()
            sort = syms[name].sort
            return lg.Const(name, sort)
        # IMPORTANT: these must come after all the other operators,
        # because it's not really specific enough.
        # Application
        elif z3.is_app(fmla) and fmla.num_args() > 0:
            name = fmla.decl().name()
            sort = syms[name].sort
            args = [Translation.smt_to_ivy(x, sorts, syms, binders) for x in fmla.children()]
            try:
                return lg.Apply(lg.Const(name, sort), *args)
            except:
                # ivy.logic.SortError: in application of new_env.auth_required, at position 3, expected sort {_mint,_transfer}, got sort function_identifier
                import pdb; pdb.set_trace()

                # Constants
        elif z3.is_var(fmla):
            # FIXME: is this correct?
            return binders[z3.get_var_index(fmla)]
        else:
            import pdb; pdb.set_trace()
            assert False, "unhandled SMT formula: {}".format(fmla)


    def translate_logic_fmla(fmla, is_twostate=False) -> pyv.Expr:
        '''Translates a logic formula (as defined in logic.py) to a
        mypyvy expression. (Note: these for some reason are not AST nodes.)'''

        if isinstance(fmla, lg.ForAll):
            # fmla.variables & fmla.body
            return pyv.Forall(Translation.translate_binders(fmla.variables), Translation.translate_logic_fmla(fmla.body, is_twostate))
        elif isinstance(fmla, lg.Exists):
            # fmla.variables & fmla.body
            return pyv.Exists(Translation.translate_binders(fmla.variables), Translation.translate_logic_fmla(fmla.body, is_twostate))
        elif isinstance(fmla, lg.Ite):
            # fmla.sort & fmla.cond & fmla.t_then, fmla.t_else
            return pyv.IfThenElse(Translation.translate_logic_fmla(fmla.cond, is_twostate), Translation.translate_logic_fmla(fmla.t_then, is_twostate), Translation.translate_logic_fmla(fmla.t_else, is_twostate))
        elif isinstance(fmla, lg.And):
            # fmla.terms
            if len(fmla.terms) == 0:
                return pyv.TrueExpr
            return pyv.And(*tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
        elif isinstance(fmla, lg.Or):
            # fmla.terms
            if len(fmla.terms) == 0:
                return pyv.FalseExpr
            return pyv.Or(*tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
        elif isinstance(fmla, lg.Eq):
            # fmla.t1 & fmla.t2
            return pyv.Eq(Translation.translate_logic_fmla(fmla.t1, is_twostate), Translation.translate_logic_fmla(fmla.t2, is_twostate))
        elif isinstance(fmla, lg.Implies):
            # fmla.t1 & fmla.t2
            return pyv.Implies(Translation.translate_logic_fmla(fmla.t1, is_twostate), Translation.translate_logic_fmla(fmla.t2, is_twostate))
        elif isinstance(fmla, lg.Iff):
            # fmla.t1 & fmla.t2
            return pyv.Iff(Translation.translate_logic_fmla(fmla.t1, is_twostate), Translation.translate_logic_fmla(fmla.t2, is_twostate))
        elif isinstance(fmla, lg.Not):
            # fmla.body
            return pyv.Not(Translation.translate_logic_fmla(fmla.body, is_twostate))
        elif isinstance(fmla, lg.Apply):
            # fmla.func & fmla.terms
            if is_twostate and itr.is_new(fmla.func):
                # We need to add a new() around the application and rename 'new_rel' to 'rel'
                old_name = itr.new_of(fmla.func).name
                fm = pyv.Apply(Translation.to_pyv_name(old_name), tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
                return pyv.New(fm)
            else:
                return pyv.Apply(Translation.to_pyv_name(fmla.func.name), tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
        elif isinstance(fmla, lg.Const):
            if is_twostate and itr.is_new(fmla):
                # We need to add a new() around the application and rename 'new_rel' to 'rel'
                old_name = itr.new_of(fmla).name
                fm = pyv.Id(Translation.to_pyv_name(old_name))
                return pyv.New(fm)
            return pyv.Id(Translation.to_pyv_name(fmla.name))
        elif isinstance(fmla, lg.Var):
            return pyv.Id(Translation.to_pyv_name(fmla.name))
        else:
            raise NotImplementedError("translating logic formula {} to mypyvy ".format(repr(fmla)))

    def globals_in_fmla(fmla) -> set[str]:
        '''Returns the set of global names that appear in a formula.
        We use this to mark constants/relations/functions as immutable
        if they appear in axioms.'''
        if isinstance(fmla, lg.ForAll) or isinstance(fmla, lg.Exists):
            return Translation.globals_in_fmla(fmla.body)
        elif isinstance(fmla, lg.Ite):
            return Translation.globals_in_fmla(fmla.cond) | Translation.globals_in_fmla(fmla.t_then) | Translation.globals_in_fmla(fmla.t_else)
        elif isinstance(fmla, lg.And) or isinstance(fmla, lg.Or):
            if len(fmla.terms) == 0:
                return set()
            return set.union(*[Translation.globals_in_fmla(x) for x in fmla.terms])
        elif isinstance(fmla, lg.Eq) or isinstance(fmla, lg.Implies) or isinstance(fmla, lg.Iff):
            return Translation.globals_in_fmla(fmla.t1) | Translation.globals_in_fmla(fmla.t2)
        elif isinstance(fmla, lg.Not):
            return Translation.globals_in_fmla(fmla.body)
        elif isinstance(fmla, lg.Apply):
            return {fmla.func.name} | set.union(*[Translation.globals_in_fmla(x) for x in fmla.terms])
        elif isinstance(fmla, lg.Const):
            return {fmla.name}
        elif isinstance(fmla, lg.Var):
            return set()
        else:
            raise NotImplementedError("constants_in_fmla: {}".format(repr(fmla)))

    def filter_subterms(fmla, pred):
        s = set()
        if pred(fmla):
            s.add(fmla)
        
        if isinstance(fmla, lg.ForAll) or isinstance(fmla, lg.Exists):
            return s | Translation.filter_subterms(fmla.body, pred)
        elif isinstance(fmla, lg.Ite):
            return s | Translation.filter_subterms(fmla.cond, pred) | Translation.filter_subterms(fmla.t_then, pred) | Translation.filter_subterms(fmla.t_else, pred)
        elif isinstance(fmla, lg.And) or isinstance(fmla, lg.Or):
            if len(fmla.terms) == 0:
                return s
            return s | set.union(*[Translation.filter_subterms(x, pred) for x in fmla.terms])
        elif isinstance(fmla, lg.Eq) or isinstance(fmla, lg.Implies) or isinstance(fmla, lg.Iff):
            return s | Translation.filter_subterms(fmla.t1, pred) | Translation.filter_subterms(fmla.t2, pred)
        elif isinstance(fmla, lg.Not):
            return s | Translation.filter_subterms(fmla.body, pred)
        elif isinstance(fmla, lg.Apply):
            return s | set.union(*[Translation.filter_subterms(x, pred) for x in fmla.terms])
        elif isinstance(fmla, lg.Const) or isinstance(fmla, lg.Var):
            return s
        else:
            raise NotImplementedError("Translation.filter_subterms: {}".format(repr(fmla)))

    def replace_subterms(fmla: il.And, pred, with_fn=None) -> il.And:
        if with_fn is None:
            with_fn = lambda x: x
        if pred(fmla):
            with_fmla = with_fn(fmla)
            # print("replace {} with {}... ".format(fmla, with_fmla), end='\n', flush=True)
            return with_fmla
        
        if isinstance(fmla, lg.ForAll):
            return lg.ForAll(fmla.variables, Translation.replace_subterms(fmla.body, pred, with_fn))
        elif isinstance(fmla, lg.Exists):
            return lg.Exists(fmla.variables, Translation.replace_subterms(fmla.body, pred, with_fn))
        elif isinstance(fmla, lg.Ite):
            return lg.Ite(Translation.replace_subterms(fmla.cond, pred, with_fn), Translation.replace_subterms(fmla.t_then, pred, with_fn), Translation.replace_subterms(fmla.t_else, pred, with_fn))
        elif isinstance(fmla, lg.And):
            return lg.And(*[Translation.replace_subterms(x, pred, with_fn) for x in fmla.terms])
        elif isinstance(fmla, lg.Or):
            return lg.Or(*[Translation.replace_subterms(x, pred, with_fn) for x in fmla.terms])
        elif isinstance(fmla, lg.Eq):
            return lg.Eq(Translation.replace_subterms(fmla.t1, pred, with_fn), Translation.replace_subterms(fmla.t2, pred, with_fn))
        elif isinstance(fmla, lg.Implies):
            return lg.Implies(Translation.replace_subterms(fmla.t1, pred, with_fn), Translation.replace_subterms(fmla.t2, pred, with_fn))
        elif isinstance(fmla, lg.Iff):
            return lg.Iff(Translation.replace_subterms(fmla.t1, pred, with_fn), Translation.replace_subterms(fmla.t2, pred, with_fn))
        elif isinstance(fmla, lg.Not):
            return lg.Not(Translation.replace_subterms(fmla.body, pred, with_fn))
        elif isinstance(fmla, lg.Apply):
            return lg.Apply(fmla.func, *[Translation.replace_subterms(x, pred, with_fn) for x in fmla.terms])
        elif isinstance(fmla, lg.Const) or isinstance(fmla, lg.Var):
            return fmla
        else:
            raise NotImplementedError("Translation.filter_subterms: {}".format(repr(fmla)))

    def is_skolem_macro(f) -> bool:
        '''Returns true if the given formula is a macro
        that defines a Skolem relation.'''
        # Adapted from `ivy_proof.ivy:match_from_defn()`
        vs = set()
        while isinstance(f, il.ForAll):
            vs.update(f.variables)
            f = f.body

        # This code can handle constants as well, but we don't want it to
        # (using this code path), because we need more filtering to properly
        # identify equalities for constants (e.g., they shouldn't be under negation).
        if len(vs) == 0:
            return Translation.is_temp_definitional_equality(f)
        
        if il.is_eq(f) or isinstance(f, il.Iff):
            lhs, rhs = f.args
            # the or True is necessary because all() throws if list empty
            if il.is_app(lhs) and (all(x in vs for x in lhs.args) or True) and iu.distinct(lhs.args):
                try:
                    # for applications
                    return lhs.func.name.startswith(IVY_TEMPORARY_INDICATOR) \
                        or lhs.func.name.startswith(IVY_TSEITIN_INDICATOR)
                except:
                    # for constants
                    return lhs.name.startswith(IVY_TEMPORARY_INDICATOR) \
                        or lhs.name.startswith(IVY_TSEITIN_INDICATOR)
        return False

    def reduce_skolem_macros(fmla: lg.And, keep_symbols: set) -> lg.And:
        '''Reduce Skolem macros in an Ivy formula.'''
        def get_macro(f):
            '''Returns the macro definition for the given formula.
            This only has work to do for "macros" that are simply equalities,
            e.g. `const_a = integer.zero`. We want certain symbols to never be rewritten.'''
            if not Translation.is_temp_definitional_equality(f):
                return f
            else:
                # LHS MUST be a constant
                lhs, rhs = f.args
                if not(il.is_app(lhs) and len(lhs.args) == 0 and is_temporary_constant(lhs)):
                    lhs, rhs = rhs, lhs

                assert il.is_app(lhs) and len(lhs.args) == 0 and is_temporary_constant(lhs), "lhs {} should be a temporary constant".format(lhs)

                # Two cases:
                # LHS (constant) = constant
                # LHS (constant) = expr

                # If this is a definition where we must keep the LHS,
                # and we can't flip the equation because the RHS is
                # a constant that must be kept as well, there's nothing to do.
                if lhs in keep_symbols and rhs in keep_symbols:
                    return None

                # If LHS must be kept and RHS is a constant
                # that does not need to be kept, we flip the equality
                if lhs in keep_symbols and il.is_app(rhs) and len(rhs.args) == 0 and is_temporary_constant(rhs) and rhs not in keep_symbols:
                    lhs, rhs = rhs, lhs

                # The assertion below doesn't hold because we can have something of
                # the form __fml_owner = owner(key), where __fml_owner is in keep_symbols.
                # TODO: do we want to rewrite using such equalities?
                # assert lhs not in keep_symbols, "lhs {} should not be in keep_symbols: {}".format(lhs, keep_symbols)

                # try:
                #     iff_ver = lg.Iff(lhs, rhs)
                # except:
                #     iff_ver = None
                # if f != lg.Eq(lhs, rhs) and f != iff_ver:
                #     print("rewrote {} to {}... ".format(f, lg.Eq(lhs, rhs)), end='\n', flush=True)

                if lhs not in keep_symbols:
                    return lg.Eq(lhs, rhs)
                else:
                    return None

        _sfmla = fmla
        while True:
            _sfmla = Translation.remove_evident_tautologies(_sfmla)
            # Call unfold one by one; otherwise it seems there's some kind
            # of assertion failure; it seems the code wasn't tested for
            # multiple simoultaneous unfoldings.
            macros = [get_macro(x) for x in Translation.filter_positive_conjucts(_sfmla, Translation.is_skolem_macro) if get_macro(x) is not None]
            macro_defs = [ast.LabeledFormula(ast.Atom(f'_macro_{i}'), macro_fmla) for (i, macro_fmla) in enumerate(macros)]
            try:
                m = macro_defs.pop()
                # print(m)
            except:
                break
            # print("unfolding macro {}... ".format(m.formula), end='\n', flush=True)
            new_sfmla = pf.unfold_fmla(_sfmla, [[m]])
            # check_simpl_equiv(_sfmla, new_sfmla)
            _sfmla = new_sfmla
        return _sfmla

    def remove_evident_tautologies(fmla: lg.And) -> lg.And:
        _sfmla = fmla
        tautologies = Translation.filter_positive_conjucts(fmla, Translation.is_evident_tautology)
        for t in tautologies:
            # print("removing tautology {}... ".format(t), end='\n', flush=True)
            _sfmla = Translation.replace_subterms(_sfmla, lambda x: x == t, lambda x: _true)
        return _sfmla

    def filter_positive_conjucts(fmla, pred):
        # FIXME: make this into a generator, since we only
        # take the first element anyway
        s = set()
        if pred(fmla):
            s.add(fmla)
        if isinstance(fmla, lg.And):
            if len(fmla.terms) == 0:
                return s
            return s | set.union(*[Translation.filter_positive_conjucts(x, pred) for x in fmla.terms])
        return s

    def is_evident_tautology(f) -> bool:
        if il.is_eq(f) or isinstance(f, il.Iff):
            lhs, rhs = f.args
            return lhs == rhs

    def is_temp_definitional_equality(f) -> bool:
        '''
        Is this an equality that has a temporary constant on at least one side?
        '''
        if il.is_eq(f) or isinstance(f, il.Iff):
            lhs, rhs = f.args
            if il.is_app(lhs) and len(lhs.args) == 0 and is_temporary_constant(lhs):
                return True
            elif il.is_app(rhs) and len(rhs.args) == 0 and is_temporary_constant(rhs):
                return True
        return False

    def pyv_globals_under_new(globals: set[str], e: pyv.Expr, under_new=False) -> set[str]:
        '''Returns the set of global names that appear in a mypyvy formula
        under new(). Used to identify which relations/functions we need to
        declare as modified. Takes as argument the set of all mutable global symbols.
        IMPORTANT: because of mypyvy's conservative logic, some of these variables
        might not actually be modified. We need to identify those separately.'''
        if isinstance(e, pyv.Bool) or isinstance(e, pyv.Int):
            return set()
        elif isinstance(e, pyv.UnaryExpr):
            if e.op == 'NEW':
                return Translation.pyv_globals_under_new(globals, e.arg, under_new=True)
            return Translation.pyv_globals_under_new(globals, e.arg, under_new)
        elif isinstance(e, pyv.BinaryExpr):
            return Translation.pyv_globals_under_new(globals, e.arg1, under_new) | Translation.pyv_globals_under_new(globals, e.arg2, under_new)
        elif isinstance(e, pyv.NaryExpr):
            return set.union(*[Translation.pyv_globals_under_new(globals, x, under_new) for x in e.args])
        elif isinstance(e, pyv.AppExpr):
            res = set.union(*[Translation.pyv_globals_under_new(globals, x, under_new) for x in e.args])
            if under_new:
                res.add(e.callee)
            return res
        elif isinstance(e, pyv.QuantifierExpr):
            return Translation.pyv_globals_under_new(globals, e.body, under_new)
        elif isinstance(e, pyv.Id):
            if under_new and e.name in globals:
                return set([e.name])
            return set()
        elif isinstance(e, pyv.IfThenElse):
            return Translation.pyv_globals_under_new(globals, e.branch, under_new) \
                | Translation.pyv_globals_under_new(globals, e.then, under_new) \
                      | Translation.pyv_globals_under_new(globals, e.els, under_new)
        elif isinstance(e, pyv.Let):
            return Translation.pyv_globals_under_new(globals, e.val, under_new) \
                | Translation.pyv_globals_under_new(globals, e.body, under_new)
        else:
            assert False, e

    def translate_initializer(init: ia.Action) -> tuple[pyv.InitDecl, set[il.Symbol]]:
        '''Translate an Ivy (combined) initializer, i.e. one that calls in
        sequence all the initializer actions, to a mypyvy initializer.
        This might include intermediate versions of relations.
        To translate these to mypyvy, we collect them and return them as
        the second return value. Our caller then must ensure these are
        defined at the top-level in the mypyvy spec.
        '''
        print("Translating initializer... ", end='', flush=True)
        _start = time.monotonic()
        # This is substantially similar to translate_action, but instead
        # of defining a mypyvy transition, we explicitly add existential
        # quantifiers around the one-state formula for init.

        # We want a one-state formula in this context
        upd = it.make_vc(init).to_formula()
        # For some reason, make_vc() returns a conjuction
        # that has Not(And()) at the end. We remove that.
        # FIXME: are we supposed to negate the whole thing?
        assert isinstance(upd, lg.And) and upd.terms[-1] == lg.Not(lg.And())
        upd = lg.And(*upd.terms[:-1])

        symbols = {}
        for sym in upd.symbols():
            symbols[sym.name] = sym

        # Remove intermediary variables
        if opt_unfold_macros.get():
            print("unfolding macros... ", end='', flush=True)
            keep_symbols = set(im.module.sig.symbols.values())
            supd = Translation.reduce_skolem_macros(upd, keep_symbols)
            check_simpl_equiv(upd, supd)
            upd = supd

        # Simplify via SMT
        z3_fmla = ivy_solver.formula_to_z3(upd)
        sfmla = Translation.simplify_via_smt(z3_fmla, symbols)
        _sfmla = Translation.smt_to_ivy(sfmla, im.module.sig.sorts, symbols)
        _upd = upd # Save original formula
        upd = _sfmla

        # Add existential quantifiers for all implicitly existentially quantified variables
        exs = set(filter(itr.is_skolem, upd.symbols()))
        first_order_exs = set(filter(lambda x: il.is_first_order_sort(x.sort) | il.is_enumerated_sort(x.sort) | il.is_boolean_sort(x.sort), exs))
        second_order_exs = set(filter(lambda x: il.is_function_sort(x.sort), exs))
        assert exs == first_order_exs | second_order_exs, "exs != first_order_exs + second_order_exs: {} != {} + {}".format(exs, first_order_exs, second_order_exs)

        ex_quant = sorted(list(first_order_exs))
        # HACK: lg.Exists only takes Vars (ex_quant has Const), but mypyvy
        # does not distinguish between the two -- it's all pyv.Id, so
        # we add the existentials on the mypyvy side, rather than in Ivy.
        fmla = Translation.translate_logic_fmla(upd)
        ex_fmla = pyv.Exists(Translation.translate_binders(ex_quant), fmla)
        decl = pyv.InitDecl(None, ex_fmla)
        _end = time.monotonic()
        print("done in {:.2f}s! ({:.1f}% of original size)".format(_end - _start, ((len(str(_sfmla)) / len(str(_upd))) * 100)))
        return (decl, second_order_exs)

    def translate_action(pyv_mutable_symbols: set[str], name: str, action: ia.Action) -> tuple[pyv.DefinitionDecl, set[il.Symbol]]:
        '''Translate an Ivy action to a mypyvy action. The transition
        relation might include temporary/intermediate versions of relations.
        To translate these to mypyvy, we collect them and return them as
        the second return value. Our caller then must ensure these are
        defined at the top-level in the mypyvy spec.'''
        print("Translating action `{}`... ".format(name), end='', flush=True)
        _start = time.monotonic()
        # This gives us a two-state formula
        (_mod, tr, pre) = action.update(im.module,None)

        # The precondition is defined negatively, i.e. the action *fails*
        # if the precondition is true, so we negate it.
        fmla = lg.And(lg.Not(pre.to_formula()), tr.to_formula())
        symbols = {}
        for sym in fmla.symbols():
            symbols[sym.name] = sym

        # Remove intermediary variables
        if opt_unfold_macros.get():
            print("unfolding macros... ", end='', flush=True)
            # NOTE: `action.formal_params` do not show up in the formula with
            # their own names (e.g. `fml:depositor`), but with a `__` prefix
            # (`__fml:depositor`), i.e. as Skolems. Similarly, `action.formal_returns`
            # show up as `__new_fml:out`.
            keep_symbols = set(map(lambda sym: sym.prefix('__'), action.formal_params)) \
                | set(map(lambda sym: sym.prefix('__new_'), action.formal_returns)) \
                | set(im.module.sig.symbols.values()) \
                | set(map(itr.new, im.module.sig.symbols.values()))
            sfmla = Translation.reduce_skolem_macros(fmla, keep_symbols)
            check_simpl_equiv(fmla, sfmla)
            fmla = sfmla

        # Make sure round-tripping through SMT works        
        z3_fmla = ivy_solver.formula_to_z3(fmla)
        _fmla = Translation.smt_to_ivy(z3_fmla, im.module.sig.sorts, symbols)
        assert fmla == _fmla, "Round-tripping Ivy -> SMT -> Ivy is incorrect: BEFORE:\n{}\n!=\nAFTER:\n{}".format(fmla, _fmla)

        # then simplify via SMT
        sfmla = Translation.simplify_via_smt(z3_fmla, symbols)
        _sfmla = Translation.smt_to_ivy(sfmla, im.module.sig.sorts, symbols)
        _fmla = fmla # Save the original fmla
        fmla = _sfmla

        # Collect all implicitly existentially quantified variables
        # ...and add them as parameters to the transition after
        # the action's own formal params
        exs = set(filter(itr.is_skolem, fmla.symbols()))
        first_order_exs = set(filter(lambda x: il.is_first_order_sort(x.sort) | il.is_enumerated_sort(x.sort) | il.is_boolean_sort(x.sort), exs))

        # We can get intermediate versions of relations and functions,
        # e.g. __m_l.a.b.balance.map(V0,V1), and we can't translate those as parameters
        # We have to collect these and define them as relations/functions at the
        # top-level, and also define an action that sets them arbitrarily.
        second_order_exs = set(filter(lambda x: il.is_function_sort(x.sort), exs))
        assert exs == first_order_exs | second_order_exs, "exs != first_order_exs + second_order_exs: {} != {} + {}".format(exs, first_order_exs, second_order_exs)

        # Add to params
        # it seems exs already contains action.formal_params
        # but we might to use action.formal_params to prettify names
        params = sorted(list(first_order_exs))
        # what to do with action.formal_returns?
        # it seems they're already existentials, so we can just ignore them

        # Generate the transition
        pyv_name = Translation.to_pyv_name(name)
        pyv_params = Translation.translate_binders(params)
        pyv_fmla = Translation.translate_logic_fmla(fmla, is_twostate=True)

        # NOTE: mypyvy is less clever than Ivy when it comes to identifying
        # what is modified. In particular, if there is a clause of the form
        # new(env_historical_auth_required(O, t__this, _approve)), where
        # t__this is an individual, it will think that t__this is modified
        # by this clause, but that's not really the case.
        #
        # In any case, because we do simplification, some symbols from the
        # original formula might have disappeared, so we can't just use
        # what Ivy thought is modified by the action.
        #
        # Rather than relying on Ivy's output, we compute the set of modified
        # symbols ourselves, by mimicking mypyvy's logic.
        pyv_supposedly_modified: set[str] = Translation.pyv_globals_under_new(pyv_mutable_symbols, pyv_fmla)
        mods = tuple([pyv.ModifiesClause(x) for x in sorted(pyv_supposedly_modified)])

        # We still need to identify which relations are not really modified,
        # but only caught in mypyvy's conservative logic.
        # What we do is we look at the simplified formula (`fmla`) and see
        # which symbols start with new_. These should actually match
        # the Ivy modified symbols in the original formula.
        actually_modified = set(map(itr.new_of, filter(itr.is_new, fmla.symbols())))

        # Sanity check: simplification shouldn't have changed the set of
        # modified symbols.
        orig_modified = set(map(lambda x: x.name, _mod))
        simpl_modified = set(map(lambda x: x.name, actually_modified))
        assert orig_modified == simpl_modified, "orig_modified != simpl_modified: {} != {}".format(orig_modified, simpl_modified)

        # For each not actually modified relation, add a clause that
        # it hasn't changed (otherwise it will get havoc'ed).
        pyv_actually_modified: set[str] = set(map(Translation.to_pyv_name, simpl_modified))
        pyv_not_actually_modified = pyv_supposedly_modified - pyv_actually_modified
        if len(pyv_not_actually_modified) > 0:
            ivy_not_actually_modified = set(filter(lambda x: Translation.to_pyv_name(x.name) in pyv_not_actually_modified, fmla.symbols()))
            noop_clauses = [Translation.pyv_unchanged_symbol(x) for x in ivy_not_actually_modified]
            noop_fmla = pyv.And(*noop_clauses)
            pyv_fmla = pyv.And(pyv_fmla, noop_fmla)

        trans = pyv.DefinitionDecl(True, 2, pyv_name, pyv_params, mods, pyv_fmla)
        _end = time.monotonic()
        print("done in {:.2f}s! ({:.1f}% of original size)".format(_end - _start, (len(str(_sfmla)) / len(str(_fmla)) * 100)))
        return (trans, second_order_exs)

    def simplify_via_smt(fmla: z3.BoolRef, syms: dict[str, Any]) -> z3.BoolRef:
        '''Simplify an SMT formula.'''
        # TODO: check the options https://microsoft.github.io/z3guide/docs/strategies/summary/#tactic-ctx-solver-simplify
        if opt_simplify.get():
            # This can be very expensive, so it is off by default.
            print("simplifying via expensive SMT call... ", end='', flush=True)
            simpl = lambda goal: z3.Tactic('ctx-solver-simplify').apply(goal)
        else:
            print("simplifying via cheap SMT call... ", end='', flush=True)
            simpl = lambda goal: z3.Tactic('ctx-simplify').apply(goal, propagate_eq=True)
        fmla = simpl(fmla).as_expr()
        fmla = z3.Tactic('propagate-values').apply(fmla).as_expr()
        return fmla


# Our own class, which will be used to generate a mypyvy `Program`
class MypyvyProgram:
    # sort -> pyv.SortDecl
    # individual -> pyv.ConstantDecl (immutable)
    # axiom -> pyv.AxiomDecl

    def __init__(self):
        self.immutable_symbols: set[str] = set()

        self.actions = []
        self.axioms = []
        self.constants = []
        self.functions = []
        self.initializers = []
        self.invariants = []
        self.relations = []
        self.sorts = []
        # These are translation artifacts: declarations of intermediate relations/functions
        # and the action that sets them arbitrarily.
        self.second_order_existentials = set() # collects the names
        self.intermediate = [] # declarations
        self.havoc_action = [] # declarations

    def add_constant_if_not_exists(self, cst):
        if cst.name not in [x.name for x in self.constants]:
            self.constants.append(cst)

    def add_sort(self, sort):
        # i.e. UninterpretedSort
        if il.is_first_order_sort(sort):
            decl = pyv.SortDecl(sort.name)
            self.sorts.append(decl)
        elif il.is_enumerated_sort(sort):
            # Declare the sort
            decl = pyv.SortDecl(sort.name)
            pyv_sort = Translation.to_pyv_sort(sort)
            self.sorts.append(decl)

            # Add constants (individuals) for each enum value
            # For some reason, not all enum variants show up in sig.symbols,
            # so we cannot add them in `translate_ivy_sig`
            for enum_value in sort.defines():
                const = pyv.ConstantDecl(enum_value, pyv_sort, False)
                self.constants.append(const)

            # Add distinct axioms (if there are >=2 enum values)
            individuals = [pyv.Id(name) for name in sort.defines()]
            if len(individuals) >= 2:
                op = pyv.NaryExpr("DISTINCT", tuple(individuals))
                axiom = pyv.AxiomDecl("{}_distinct".format(sort.name), op)
                self.axioms.append(axiom)
        elif il.is_boolean_sort(sort):
            # No need to declare the bool sort
            pass
        else:
            # print("unhandled sort: {}".format(sort))
            raise NotImplementedError("sort {} not supported".format(sort))

    def mutable_symbols(self) -> set[str]:
        '''Returns the set of mutable symbols.'''
        mut = set()
        for c in self.constants + self.relations + self.functions:
            if c.mutable:
                mut.add(c.name)
        return mut

    def translate_ivy_sig(self, mod: im.Module, sig: il.Sig = None):
        '''Translate a module signature to the sorts, constants,
        relations, and functions of a mypyvy specification.
        '''
        # Identify immutable symbols: those which appear in axioms
        # and those which are functionally axioms in this isolate
        # (i.e. properties that are assumed to be true)
        for ax in mod.axioms:
            self.immutable_symbols |= Translation.globals_in_fmla(ax)
        for prop in mod.labeled_props:
            if prop.assumed:
                self.immutable_symbols |= Translation.globals_in_fmla(prop.formula)
        for dfn in mod.definitions:
            self.immutable_symbols |= Translation.globals_in_fmla(dfn.formula.lhs())
            self.immutable_symbols |= Translation.globals_in_fmla(dfn.formula.rhs())

        # If we are explicitly passed a signature to use, use that one
        sig: il.Sig = sig or mod.sig
        # Add sorts
        for (_sort_name, sort) in sig.sorts.items():
            self.add_sort(sort)

        # # Add symbols, replacing "." with DOT_REPLACEMENT
        for _sym_name, sym in sig.symbols.items():
            assert _sym_name == sym.name, "symbol name mismatch: {} != {}".format(_sym_name, sym.name)
            kind = Translation.sort_type(sym.sort)
            is_mutable = (sym.name not in self.immutable_symbols)
            pyv_sym_decl = Translation.translate_symbol_decl(sym, is_mutable)
            if kind == 'individual':
                self.add_constant_if_not_exists(pyv_sym_decl)
            elif kind == 'relation':
                assert sym.is_relation()
                self.relations.append(pyv_sym_decl)
            elif kind == 'function':
                self.functions.append(pyv_sym_decl)
            else:
                raise NotImplementedError("translating symbol {} to mypyvy ".format(repr(sym)))

    def add_axioms_props_defs(self, mod: im.Module):
        '''Add axioms, properties, and definitions to the mypyvy program.'''
        # Add axioms
        # For some reason, these are directly formulas, rather than AST nodes
        for ax in mod.axioms:
            # ...and therefore don't have axiom names
            fmla = Translation.translate_logic_fmla(ax)
            axiom = pyv.AxiomDecl(None, fmla)
            self.axioms.append(axiom)

        # Add properties that are assumed to be true in this isolate
        for prop in mod.labeled_props:
            if prop.assumed:
                fmla = Translation.translate_logic_fmla(prop.formula)
                axiom = pyv.AxiomDecl(Translation.to_pyv_name(prop.label.relname), fmla)
                self.axioms.append(axiom)

        # Add definitions as axioms
        for defn in mod.definitions:
            lhs, rhs = Translation.translate_logic_fmla(defn.formula.lhs()), Translation.translate_logic_fmla(defn.formula.rhs())
            fmla = pyv.Iff(lhs, rhs)
            axiom = pyv.AxiomDecl(Translation.to_pyv_name(defn.name), fmla)
            self.axioms.append(axiom)

    def add_conjectures(self, mod: im.Module):
        '''Add conjectures (claimed invariants) to the mypyvy program.'''
        # Add conjectures
        for conj in mod.labeled_conjs:
            fmla = Translation.translate_logic_fmla(conj.formula)
            inv = pyv.InvariantDecl(Translation.to_pyv_name(conj.label.relname), fmla, False, False)
            self.invariants.append(inv)

    def add_initializers(self, mod: im.Module):
        '''Add initializers to the mypyvy program. Note that we CANNOT
        translate initializers one-by-one, because (at least in Ivy 1.8)
        they are stateful: the second initializer might depend on the state
        modified by the first. Therefore, we create an artificial action
        that combines all initializers in sequence, and translate that.'''
        inits = list(map(lambda x: x[1], mod.initializers)) # get the actions
        init_action = ia.Sequence(*inits)
        (decl, sec_ord_exs) = Translation.translate_initializer(init_action)
        self.second_order_existentials |= sec_ord_exs
        self.initializers.append(decl)

    def add_public_actions(self, mod: im.Module):
        '''Add public actions to the mypyvy program.'''
        public_actions = filter(lambda x: x[0] in mod.public_actions, mod.actions.items())
        pyv_mutable_symbols = self.mutable_symbols()
        for (name, action) in public_actions:
            (decl, sec_ord_exs) = Translation.translate_action(pyv_mutable_symbols, name, action)
            self.second_order_existentials |= sec_ord_exs
            self.actions.append(decl)

    def add_intermediate_rels_fn_and_havoc_action(self, mod: im.Module):
        '''Declares relations and functions for the intermediate versions
        of variables, and defines an action that sets them arbitrarily.'''
        # Define second order existentials as (mutable) relations/functions
        for se_ex in self.second_order_existentials:
            pyv_decl = Translation.translate_symbol_decl(se_ex, True)
            self.intermediate.append(pyv_decl)

        # Create a havoc action that sets all second order existentials arbitrarily
        if len(self.second_order_existentials) > 0:
            modified = sorted([Translation.to_pyv_name(x.name) for x in self.second_order_existentials])
            mods = tuple([pyv.ModifiesClause(x) for x in modified])
            havoc_clauses: list[pyv.Expr] = [Translation.pyv_havoc_symbol(x) for x in self.second_order_existentials]
            havoc_fmla = pyv.And(*havoc_clauses)
            act = pyv.DefinitionDecl(True, 2, "_havoc_intermediaries", [], mods, havoc_fmla)
            self.havoc_action.append(act)

    def to_program(self) -> pyv.Program:
        decls = self.sorts + self.constants + self.relations + \
            self.functions + self.axioms + \
            self.intermediate + self.havoc_action + \
            self.initializers + self.actions + self.invariants
        return pyv.Program(decls)


def check_isolate():
    mod = im.module
    prog = MypyvyProgram()

    # FIXME: do we need to handle mod.aliases? (type aliases)

    # STEP 1: parse mod.sig to determine
    # sorts, relations, functions, and individuals
    # mod.sig.sorts & mod.sig.symbols

    # FIXME: Is using mod.old_sig correct?
    # An isolate's (call it X) signature does not contain symbols used internally
    # by isolates associated with it (e.g. Y) (e.g. via Ivy's `with` mechanism),
    # but such symbols might appear when we translate X's actions to mypyvy,
    # if X calls actions from Y.
    prog.translate_ivy_sig(mod, mod.old_sig)

    # STEP 2: add axioms, conjectures, and definitions
    # mod.axioms
    # mod.labeled_props -> properties (become axioms once checked)
    # mod.labeled_conjs -> invariants/conjectures (to be checked)
    prog.add_axioms_props_defs(mod)
    prog.add_conjectures(mod)

    # STEP 3: generate actions
    # - collect all implicitly existentially quantified variables (those starting with __)
    # mod.initializers -> after init
    # mod.public_actions
    # mod.actions
    print("If you pass simplify=true, the translation performs simplification via SMT. It might take on the order of minutes!")
    if opt_unfold_macros.get():
        print("Will remove intermediary relations in initializer and transition definitions.")
    else:
        print("Will NOT remove intermediary relations in initializer and transition definitions.")

    prog.add_initializers(mod)
    prog.add_public_actions(mod)
    prog.add_intermediate_rels_fn_and_havoc_action(mod)

    #  Generate the program
    pyv_prog = prog.to_program()

    out_file = "{}.pyv".format(mod.name)
    with open(out_file, "w") as f:
        f.write(str(pyv_prog))
        print("output written to {}".format(out_file))

    exit(0)
