from __future__ import annotations

from contextlib import contextmanager
import dataclasses
from dataclasses import dataclass
import functools
import itertools
import ply.lex
from typing import List, Union, Tuple, Optional, Dict, Iterator, \
    Callable, Any, Set, TypeVar, Generic, Iterable, Mapping, cast
from typing_extensions import Protocol
from . import mypyvy_utils as utils
import z3

OrderedSet = utils.OrderedSet
Token = ply.lex.LexToken
Span = Tuple[Token, Token]

B = TypeVar('B')

class Denotable:
    def __init__(self) -> None:
        self._hash: Optional[int] = None

    def _denote(self) -> Tuple:
        raise Exception('Unexpected denotable object %s does not implement _denote method' % repr(self))

    def __getstate__(self) -> Any:
        return dict(
            self.__dict__,
            _hash=None,
        )

    def __hash__(self) -> int:
        if self._hash is None:
            self._hash = hash((type(self), self._denote()))
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Denotable):
            return False

        return (type(self) is type(other) and
                self._denote() == other._denote())


class Sort(Denotable):
    def __init__(self) -> None:
        super().__init__()

    def __repr__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __str__ method' % repr(self))

    def __ne__(self, other: object) -> bool:
        return not (self == other)


class HasSortField(Protocol):
    sort: InferenceSort

class SortInferencePlaceholder:
    def __init__(self, d: Optional[HasSortField] = None) -> None:
        self.backpatches: List[HasSortField] = []
        self.sort: Optional[Sort] = None
        self.parent: Optional[SortInferencePlaceholder] = None

        if d is not None:
            self.add(d)

    def add(self, d: HasSortField) -> None:
        self.backpatches.append(d)

    def root(self) -> SortInferencePlaceholder:
        if self.parent is not None:
            return self.parent.root()
        else:
            return self

    def solve(self, sort: Sort) -> None:
        assert self.parent is None
        assert self.sort is None

        self.sort = sort

        for d in self.backpatches:
            d.sort = sort

    def merge(self, other: SortInferencePlaceholder) -> None:
        assert self.parent is None
        assert other.parent is None
        assert self.sort is None
        assert other.sort is None
        if self == other:
            return

        other.parent = self
        self.backpatches.extend(other.backpatches)

InferenceSort = Union[Sort, SortInferencePlaceholder, None]

# Returns a set describing the *mutable* symbols used by an expression.
# Immutable symbols and bound variables are *not* included.
# In the returned set, each element is a tuple (i, ts, s), where
#     - s is the name of the symbol used
#     - ts is a non-empty tuple of tokens describing the sequence of definitions by which
#       expr refers to the symbol s (useful for locating error messages). the tuple is ordered
#       from expr to the direct reference to s. if expr directly refers to s, then the tuple
#       has length one.
#     - i is the "state index" of the usage. in a single-vocabulary formula, this will
#       always be 0, but in a multi-vocabulary formula, it indicates how many new() operators
#       the usage is under.
def symbols_used(scope: Scope, expr: Expr, state_index: int = 0) -> Set[Tuple[int, Tuple[Optional[Span], ...], str]]:
    def add_caller_span(
            s: Set[Tuple[int, Tuple[Optional[Span], ...], str]]
    ) -> Set[Tuple[int, Tuple[Optional[Span], ...], str]]:
        return set((i, (expr.span,) + l, sym) for (i, l, sym) in s)

    if isinstance(expr, Bool) or isinstance(expr, Int):
        return set()
    elif isinstance(expr, UnaryExpr):
        if expr.op == 'NEW':
            return symbols_used(scope, expr.arg, state_index=state_index + 1)
        else:
            return symbols_used(scope, expr.arg, state_index)
    elif isinstance(expr, BinaryExpr):
        return symbols_used(scope, expr.arg1, state_index) | symbols_used(scope, expr.arg2, state_index)
    elif isinstance(expr, NaryExpr):
        ans: Set[Tuple[int, Tuple[Optional[Span], ...], str]] = set()
        for arg in expr.args:
            ans |= symbols_used(scope, arg, state_index)
        return ans
    elif isinstance(expr, AppExpr):
        args: Set[Tuple[int, Tuple[Optional[Span], ...], str]] = set()
        for arg in expr.args:
            args |= symbols_used(scope, arg, state_index)

        d = scope.get(expr.callee)
        assert d is not None and not isinstance(d, tuple), (d, expr.callee, expr)
        if isinstance(d, DefinitionDecl):
            with scope.fresh_stack():
                with scope.in_scope(d.binder, [None for i in range(len(d.binder.vs))]):
                    callee_symbols = symbols_used(scope, d.expr, state_index)
            return args | add_caller_span(callee_symbols)
        elif d.mutable:
            return args | {(state_index + expr.n_new, (expr.span,), expr.callee)}
        else:
            return args
    elif isinstance(expr, QuantifierExpr):
        with scope.in_scope(expr.binder, [None for i in range(len(expr.binder.vs))]):
            return symbols_used(scope, expr.body, state_index)
    elif isinstance(expr, Id):
        d = scope.get(expr.name)
        assert d is not None, expr.name
        if isinstance(d, RelationDecl) or \
           isinstance(d, ConstantDecl) or \
           isinstance(d, FunctionDecl):
            return {(state_index + expr.n_new, (expr.span,), expr.name)} if d.mutable else set()
        elif isinstance(d, DefinitionDecl):
            with scope.fresh_stack():
                return add_caller_span(symbols_used(scope, d.expr, state_index + expr.n_new))
        else:
            return set()
    elif isinstance(expr, IfThenElse):
        return symbols_used(scope, expr.branch, state_index) | \
            symbols_used(scope, expr.then, state_index) | \
            symbols_used(scope, expr.els, state_index)
    elif isinstance(expr, Let):
        s1 = symbols_used(scope, expr.val, state_index)
        with scope.in_scope(expr.binder, [None for i in range(len(expr.binder.vs))]):
            return s1 | symbols_used(scope, expr.body, state_index)
    else:
        assert False


def subst_vars_simple(expr: Expr, subst: Mapping[Id, Expr]) -> Expr:
    if isinstance(expr, Bool) or isinstance(expr, Int):
        return expr
    elif isinstance(expr, UnaryExpr):
        return UnaryExpr(op=expr.op, arg=subst_vars_simple(expr.arg, subst))
    elif isinstance(expr, BinaryExpr):
        return BinaryExpr(op=expr.op, arg1=subst_vars_simple(expr.arg1, subst),
                          arg2=subst_vars_simple(expr.arg2, subst))
    elif isinstance(expr, AppExpr):
        return AppExpr(callee=expr.callee, args=tuple(subst_vars_simple(a, subst) for a in expr.args))
    elif isinstance(expr, Id):
        return subst.get(expr, expr)
    else:
        print(expr)
        assert False

# NOTE(capture-avoiding-substitution)
# This function is carefully written to avoid capture by following a strategy taught in CSE 490P.
# See the first 10 slides here: https://drive.google.com/file/d/1jFGF3snnC2_4N7cqpH_c0D_S6NPFknWg/view
# When going under a binding form, we avoid clashes with three kinds of names:
#     - names otherwise free in the body of the binding form
#     - names in the domain of the substitution gamma
#     - names free in expressions in the codomain of the substitution gamma
# This strategy has undergone substantial testing and trial and error in the context of the course.
# Deviation is not recommended.
def subst(scope: Scope, e: Expr, gamma: Mapping[Id, Expr]) -> Expr:
    if isinstance(e, (Bool, Int)):
        return e
    elif isinstance(e, UnaryExpr):
        return UnaryExpr(e.op, subst(scope, e.arg, gamma))
    elif isinstance(e, BinaryExpr):
        return BinaryExpr(e.op, subst(scope, e.arg1, gamma), subst(scope, e.arg2, gamma))
    elif isinstance(e, NaryExpr):
        return NaryExpr(e.op, tuple(subst(scope, arg, gamma) for arg in e.args))
    elif isinstance(e, AppExpr):
        return AppExpr(e.callee, tuple(subst(scope, arg, gamma) for arg in e.args))
    elif isinstance(e, QuantifierExpr):
        # luv too avoid capture
        avoid = free_ids(e)
        avoid |= set(v.name for v in gamma)
        for v in gamma:
            avoid |= free_ids(gamma[v])

        renaming: Dict[Id, Expr] = {}
        fresh_svs = []
        for sv in e.binder.vs:
            fresh_name = scope.fresh(sv.name, also_avoid=list(avoid))
            renaming[Id(sv.name)] = Id(fresh_name)
            assert not isinstance(sv.sort, SortInferencePlaceholder)
            fresh_svs.append(SortedVar(fresh_name, sv.sort))

        fresh_body = subst(scope, e.body, renaming)

        return QuantifierExpr(e.quant, tuple(fresh_svs), subst(scope, fresh_body, gamma))
    elif isinstance(e, Id):
        if e in gamma:
            return gamma[e]
        else:
            return e
    elif isinstance(e, IfThenElse):
        return IfThenElse(subst(scope, e.branch, gamma), subst(scope, e.then, gamma), subst(scope, e.els, gamma))
    elif isinstance(e, Let):
        # luv too avoid capture
        avoid = free_ids(e)
        avoid |= set(v.name for v in gamma)
        for v in gamma:
            avoid |= free_ids(gamma[v])

        assert len(e.binder.vs) == 1
        sv = e.binder.vs[0]
        fresh_name = scope.fresh(sv.name, also_avoid=list(avoid))
        assert not isinstance(sv.sort, SortInferencePlaceholder)
        fresh_sv = SortedVar(fresh_name, sv.sort)

        fresh_body = subst(scope, e.body, {Id(sv.name): Id(fresh_name)})

        return Let(fresh_sv, subst(scope, e.val, gamma), subst(scope, fresh_body, gamma))
    else:
        assert False, (type(e), e)

def as_clauses_body(expr: Expr, negated: bool = False) -> List[List[Expr]]:
    '''
    Convert a quantifier-free formula to CNF
    '''
    if isinstance(expr, Bool):
        return [[Bool(expr.val != negated)]]
    elif isinstance(expr, UnaryExpr):
        assert expr.op == 'NOT'
        return as_clauses_body(expr.arg, not negated)
    elif isinstance(expr, BinaryExpr):
        if expr.op in ['EQUAL', 'NOTEQ']:
            op = 'NOTEQ' if (expr.op == 'NOTEQ') != negated else 'EQUAL'
            return [[BinaryExpr(op, expr.arg1, expr.arg2)]]
        elif expr.op == 'IMPLIES':
            return as_clauses_body(Or(Not(expr.arg1), expr.arg2), negated=negated)
        elif expr.op == 'IFF':
            return as_clauses_body(
                And(Or(Not(expr.arg1), expr.arg2),
                    Or(expr.arg1, Not(expr.arg2))),
                negated=negated
            )
        else:
            assert False, f'{expr.op}\n{expr}'
    elif isinstance(expr, NaryExpr):
        assert expr.op != 'DISTINCT', 'CNF normalization does not support "distinct" expressions'
        assert expr.op in ('AND', 'OR'), expr
        if negated:
            other_op = 'AND' if expr.op == 'OR' else 'OR'
            return as_clauses_body(NaryExpr(other_op, tuple(Not(arg) for arg in expr.args)), negated=False)
        elif expr.op == 'AND':
            return list(itertools.chain(*(as_clauses_body(arg, negated=False) for arg in expr.args)))
        elif expr.op == 'OR':
            return [list(itertools.chain(*tup))
                    for tup in itertools.product(*(as_clauses_body(arg, negated=False) for arg in expr.args))]
        else:
            assert False, expr
    elif isinstance(expr, AppExpr) or isinstance(expr, Id):
        if negated:
            return [[Not(expr)]]
        else:
            return [[expr]]
    else:
        assert False, f'unsupported expressions in as_clauses_body: {expr}'

def as_clauses_quant(expr: Expr, negated: bool = False) -> Tuple[Tuple[SortedVar, ...], List[List[Expr]]]:
    if isinstance(expr, QuantifierExpr):
        if negated:
            other_quant = 'EXISTS' if expr.quant == 'FORALL' else 'FORALL'
            return as_clauses_quant(QuantifierExpr(other_quant, expr.binder.vs, Not(expr.body)), negated=False)
        else:
            assert expr.quant == 'FORALL'
            new_vs, new_body = as_clauses_quant(expr.body, negated=False)
            return expr.binder.vs + tuple(new_vs), new_body
    elif isinstance(expr, UnaryExpr) and expr.op == 'NOT':
        return as_clauses_quant(expr.arg, not negated)
    else:
        return (), as_clauses_body(expr, negated)

def as_clauses(expr: Expr) -> List[Expr]:
    '''Conver expr to CNF (must be universally quantified, see as_clauses_quant'''
    vs, clauses = as_clauses_quant(expr)
    ans = []
    for clause in clauses:
        if len(clause) == 1:
            clause += [Bool(False)]
        e = Forall(vs, Or(*clause))
        # TODO: should we typecheck here? Also, can we not add false?
        # typechecker.typecheck_expr(the_program.scope, e, None)
        ans.append(e)
    return ans

# Produce an expression that guards all the variables in the given binder to be in the
# relation corresponding to their sort. See relativize_quantifiers.
def relativization_guard_for_binder(guards: Mapping[SortDecl, RelationDecl], b: Binder) -> Expr:
    conjs = []
    for v in b.vs:
        guard = Apply(guards[get_decl_from_sort(v.sort)].name, (Id(v.name),))
        conjs.append(guard)
    return And(*conjs)


# 'relativize' an expression by guarding quantifiers by the given relations, which should be
# unary relations of the given sort. The guard relations can be mutable or immutable, but
# note that if they are mutable, then they are always referred to in the "current" state.
#
# For example, if sort node is to be guarded by a relation A, then this would transform the
# expression
#     forall x:node. !(R(x) & S(x))
# into the relativized expression
#     forall x:node. A(x) -> !(R(x) & S(x))
# Universal quantifiers are guarded by implications, while existentials are guarded by
# conjunctions.
def relativize_quantifiers(guards: Mapping[SortDecl, RelationDecl], e: Expr) -> Expr:
    QUANT_GUARD_OP: Dict[str, Callable[[Expr, Expr], Expr]] = {
        'FORALL': Implies,
        'EXISTS': And,
    }

    # TODO: consider supporting a visitor pattern
    def go(e: Expr) -> Expr:
        if isinstance(e, (Bool, Int)):
            return e
        elif isinstance(e, UnaryExpr):
            return UnaryExpr(e.op, go(e.arg))
        elif isinstance(e, BinaryExpr):
            return BinaryExpr(e.op, go(e.arg1), go(e.arg2))
        elif isinstance(e, NaryExpr):
            return NaryExpr(e.op, tuple(go(arg) for arg in e.args))
        elif isinstance(e, AppExpr):
            return AppExpr(e.callee, tuple(go(arg) for arg in e.args), n_new=e.n_new)
        elif isinstance(e, QuantifierExpr):
            guard = relativization_guard_for_binder(guards, e.binder)
            return QuantifierExpr(e.quant, e.binder.vs,
                                  QUANT_GUARD_OP[e.quant](guard, go(e.body)))
        elif isinstance(e, Id):
            return e
        elif isinstance(e, IfThenElse):
            return IfThenElse(go(e.branch), go(e.then), go(e.els))
        elif isinstance(e, Let):
            return Let(e.binder.vs[0], go(e.val), go(e.body))
        else:
            assert False

    return go(e)

# checks if e is a universal formula with one quantifier out front (or is quantifier free)
# i.e. returns false if additional universal quantifiers are buried in the body
def is_universal(e: Expr) -> bool:
    if isinstance(e, QuantifierExpr):
        return e.quant == 'FORALL' and is_quantifier_free(e.body)
    else:
        return is_quantifier_free(e)

def is_quantifier_free(e: Expr) -> bool:
    if isinstance(e, Bool):
        return True
    elif isinstance(e, UnaryExpr):
        return is_quantifier_free(e.arg)
    elif isinstance(e, BinaryExpr):
        return is_quantifier_free(e.arg1) and is_quantifier_free(e.arg2)
    elif isinstance(e, NaryExpr):
        return all(is_quantifier_free(arg) for arg in e.args)
    elif isinstance(e, AppExpr):
        return all(is_quantifier_free(arg) for arg in e.args)
    elif isinstance(e, QuantifierExpr):
        return False
    elif isinstance(e, Id):
        return True
    elif isinstance(e, IfThenElse):
        return (is_quantifier_free(e.branch) and
                is_quantifier_free(e.then) and
                is_quantifier_free(e.els))
    elif isinstance(e, Let):
        return is_quantifier_free(e.val) and is_quantifier_free(e.body)
    else:
        assert False

def span_endlexpos(x: Union[Span, Expr, Decl]) -> Optional[int]:
    if not isinstance(x, tuple):
        s = x.span
    else:
        s = x

    if s is None:
        return None

    return s[1].lexpos + len(s[1].value)

class FaithfulPrinter:
    def __init__(self, prog: Program, skip_invariants: bool = False) -> None:
        self.prog = prog
        self.skip_invariants = skip_invariants
        self.pos = 0
        self.buf: List[str] = []

    def skip_to(self, new_pos: Optional[int]) -> None:
        if new_pos is not None:
            self.pos = new_pos

    def skip_to_start(self, x: Union[Expr, Decl]) -> None:
        assert x.span is not None
        self.skip_to(x.span[0].lexpos)

    def skip_to_end(self, x: Union[Expr, Decl]) -> None:
        self.skip_to(span_endlexpos(x))

    def skip_expect(self, expected: str) -> None:
        assert self.prog.input is not None
        end = self.pos + len(expected)
        assert end <= len(self.prog.input)
        assert self.prog.input[self.pos:end] == expected
        self.skip_to(end)

    def move_to(self, new_pos: Optional[int]) -> None:
        assert self.prog.input is not None
        if new_pos is None:
            return
        assert self.pos <= new_pos
        if self.pos < new_pos:
            data = self.prog.input[self.pos:new_pos]
            self.buf.append(data)
            self.skip_to(new_pos)

    def move_to_start(self, x: Union[Expr, Decl]) -> None:
        if x.span is None:
            assert isinstance(x, UnaryExpr)
            assert x.op == 'NEW'
            self.move_to_start(x.arg)
            return

        self.move_to(x.span[0].lexpos)

    def move_to_end(self, x: Union[Expr, Decl]) -> None:
        self.move_to(span_endlexpos(x))

    def process(self) -> str:
        assert self.prog.input is not None
        skip = False
        for d in self.prog.decls:
            if skip:
                self.skip_to_start(d)
                skip = False
            else:
                self.move_to_start(d)
            if self.skip_invariants and isinstance(d, InvariantDecl):
                skip = True
            else:
                self.process_decl(d)

        self.move_to(len(self.prog.input))

        return ''.join(self.buf)

    def process_decl(self, d: Decl) -> None:
        assert d.span is not None
        assert self.pos == d.span[0].lexpos

        if isinstance(d, DefinitionDecl):
            self.move_and_process_expr(d.expr)
        else:
            self.move_to_end(d)

    def move_and_process_expr(self, e: Expr) -> None:
        self.move_to_start(e)
        self.process_expr(e)

    def process_expr(self, e: Expr) -> None:
        assert e.span is not None or (isinstance(e, UnaryExpr) and e.op == 'NEW')

        if isinstance(e, NaryExpr):
            for arg in e.args:
                self.move_and_process_expr(arg)
            self.move_to_end(e)
        elif isinstance(e, QuantifierExpr):
            self.move_and_process_expr(e.body)
            self.move_to_end(e)
        elif isinstance(e, UnaryExpr):
            self.move_and_process_expr(e.arg)
            self.move_to_end(e)
        elif isinstance(e, BinaryExpr):
            self.process_expr(e.arg1)
            self.move_and_process_expr(e.arg2)
        elif isinstance(e, IfThenElse):
            self.move_and_process_expr(e.branch)
            self.move_and_process_expr(e.then)
            self.move_and_process_expr(e.els)
        elif isinstance(e, Let):
            self.move_and_process_expr(e.val)
            self.move_and_process_expr(e.body)
        elif isinstance(e, AppExpr):
            for arg in e.args:
                self.move_and_process_expr(arg)
            self.move_to_end(e)
        elif isinstance(e, (Id, Bool)):
            self.move_to_end(e)
        else:
            assert False, repr(e)

# Use prog.input to print prog as similarly as possible to the input. In particular,
# whitespace and comments are preserved where possible.
def faithful_print_prog(prog: Program, skip_invariants: bool = False) -> str:
    return FaithfulPrinter(prog, skip_invariants).process()


@functools.total_ordering
@dataclass(frozen=True)
class AbstractExpr:
    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, AbstractExpr):
            return NotImplemented
        vs1 = (str(type(self)), *(getattr(self, f.name) for f in dataclasses.fields(self) if f.compare))
        vs2 = (str(type(other)), *(getattr(other, f.name) for f in dataclasses.fields(other) if f.compare))
        return vs1 < vs2

@dataclass(frozen=True)
class Bool(AbstractExpr):
    val: bool
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __str__(self) -> str:
        return pretty(self)

TrueExpr = Bool(True)
FalseExpr = Bool(False)

@dataclass(frozen=True)
class Int(AbstractExpr):
    val: int
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

UNOPS = {
    'NOT',
    'NEW'
}

@dataclass(frozen=True)
class UnaryExpr(AbstractExpr):
    op: str
    arg: Expr
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __post_init__(self) -> None:
        assert self.op in UNOPS

    def __str__(self) -> str:
        return pretty(self)

def Not(e: Expr) -> Expr:
    return UnaryExpr('NOT', e)

def New(e: Expr, n: int = 1) -> Expr:
    # TODO: rename New -> Next
    assert n >= 0, 'are you trying to resurrect old()?'
    for i in range(n):
        e = UnaryExpr('NEW', e)
    return e

BINOPS = {
    'IMPLIES',
    'IFF',
    'EQUAL',
    'NOTEQ',
    'GE',
    'GT',
    'LE',
    'LT',
    'PLUS',
    'SUB',
    'MULT'
}

@dataclass(frozen=True)
class BinaryExpr(AbstractExpr):
    op: str
    arg1: Expr
    arg2: Expr
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __post_init__(self) -> None:
        assert self.op in BINOPS

    def __str__(self) -> str:
        return pretty(self)

NOPS = {
    'AND',
    'OR',
    'DISTINCT'
}

@dataclass(frozen=True)
class NaryExpr(AbstractExpr):
    op: str
    args: Tuple[Expr, ...]
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __post_init__(self) -> None:
        assert self.op in NOPS

    def __str__(self) -> str:
        return pretty(self)

def Forall(vs: Tuple[SortedVar, ...], body: Expr) -> Expr:
    if not vs:
        return body
    return QuantifierExpr('FORALL', vs, body)

def Exists(vs: Tuple[SortedVar, ...], body: Expr) -> Expr:
    if not vs:
        return body
    return QuantifierExpr('EXISTS', vs, body)

def And(*args: Expr) -> Expr:
    if not args:
        return TrueExpr
    elif len(args) == 1:
        return args[0]
    else:
        return NaryExpr('AND', tuple(args))

def Or(*args: Expr) -> Expr:
    if not args:
        return FalseExpr
    elif len(args) == 1:
        return args[0]
    else:
        return NaryExpr('OR', tuple(args))

def Eq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('EQUAL', arg1, arg2)

def Neq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('NOTEQ', arg1, arg2)

def Iff(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('IFF', arg1, arg2)

def Implies(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr('IMPLIES', arg1, arg2)

def Apply(callee: str, args: Tuple[Expr, ...]) -> Expr:
    return AppExpr(callee, args)

@dataclass(frozen=True)
class AppExpr(AbstractExpr):
    callee: str
    args: Tuple[Expr, ...]
    n_new: int = dataclasses.field(default=0)
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __str__(self) -> str:
        return pretty(self)

@dataclass(order=True)
class SortedVar(Denotable):
    name: str
    sort: InferenceSort
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __hash__(self) -> int:
        return hash(self.name)

    def __str__(self) -> str:
        if self.sort is None:
            return self.name
        else:
            return '%s:%s' % (self.name, self.sort)

def safe_cast_sort(s: InferenceSort) -> Sort:
    assert isinstance(s, Sort)
    return cast(Sort, s)

@dataclass(order=True, unsafe_hash=True)
class Binder(Denotable):
    vs: Tuple[SortedVar, ...]

@dataclass(frozen=True)
class QuantifierExpr(AbstractExpr):
    quant: str
    vs: dataclasses.InitVar[Tuple[SortedVar, ...]]
    binder: Binder = dataclasses.field(init=False)
    body: Expr
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __post_init__(self, vs: Tuple[SortedVar, ...]) -> None:
        assert self.quant in ['FORALL', 'EXISTS']
        assert len(vs) > 0
        super().__setattr__('binder', Binder(vs))  # hack around frozen

    def __str__(self) -> str:
        return pretty(self)

    def get_vs(self) -> Tuple[SortedVar, ...]:
        return self.binder.vs

@dataclass(frozen=True)
class Id(AbstractExpr):
    '''Unresolved symbol (might represent a constant or a nullary relation or a variable)'''
    name: str
    n_new: int = dataclasses.field(default=0)
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __str__(self) -> str:
        return pretty(self)

@dataclass(frozen=True)
class IfThenElse(AbstractExpr):
    branch: Expr
    then: Expr
    els: Expr
    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __str__(self) -> str:
        return pretty(self)

@dataclass(frozen=True)
class Let(AbstractExpr):
    var: dataclasses.InitVar[SortedVar]
    binder: Binder = dataclasses.field(init=False)
    val: Expr
    body: Expr

    span: Optional[Span] = dataclasses.field(default=None, compare=False)

    def __post_init__(self, var: SortedVar) -> None:
        super().__setattr__('binder', Binder((var,)))  # hack around frozen

    def __str__(self) -> str:
        return pretty(self)

def free_ids(e: Expr, into: Optional[OrderedSet[str]] = None) -> OrderedSet[str]:
    if into is None:
        into = OrderedSet()
    if isinstance(e, (Bool, Int)):
        pass
    elif isinstance(e, UnaryExpr):
        free_ids(e.arg, into)
    elif isinstance(e, BinaryExpr):
        free_ids(e.arg1, into)
        free_ids(e.arg2, into)
    elif isinstance(e, (NaryExpr, AppExpr)):
        for arg in e.args:
            free_ids(arg, into)
    elif isinstance(e, QuantifierExpr):
        bound_vars = set(v.name for v in e.binder.vs)
        into |= free_ids(e.body) - bound_vars
    elif isinstance(e, Id):
        into.add(e.name)
    elif isinstance(e, IfThenElse):
        free_ids(e.branch, into)
        free_ids(e.then, into)
        free_ids(e.els, into)
    elif isinstance(e, Let):
        free_ids(e.val, into)
        bound_vars = set(v.name for v in e.binder.vs)
        into |= free_ids(e.body) - bound_vars
    else:
        assert False, (type(e), e)

    return into

Expr = Union[Bool, Int, UnaryExpr, BinaryExpr, NaryExpr, AppExpr, Id, QuantifierExpr, IfThenElse, Let]

Arity = Tuple[Sort, ...]

class UninterpretedSort(Sort):
    def __init__(self, name: str, *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.name = name
        self.decl: Optional[SortDecl] = None

    def __repr__(self) -> str:
        return 'UninterpretedSort(name=%s)' % (repr(self.name),)

    def __str__(self) -> str:
        return self.name

    def _denote(self) -> Tuple:
        return ('uninterpreted', self.name,)

class _BoolSort(Sort):
    def __init__(self, *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span

    def __repr__(self) -> str:
        return 'bool'

    def __str__(self) -> str:
        return 'bool'

    def _denote(self) -> Tuple:
        return ('bool', )

BoolSort = _BoolSort()

class _IntSort(Sort):
    def __init__(self, *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span

    def __repr__(self) -> str:
        return 'int'

    def __str__(self) -> str:
        return 'int'

    def _denote(self) -> Tuple:
        return ('int',)

IntSort = _IntSort()

def get_decl_from_sort(s: InferenceSort) -> SortDecl:
    assert isinstance(s, UninterpretedSort)
    assert s.decl is not None
    return s.decl

class Decl(Denotable):
    def __init__(self, span: Optional[Span]) -> None:
        super().__init__()
        self.span = span

    def __repr__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __str__ method' % type(self))


class SortDecl(Decl):
    def __init__(self, name: str, *, annotations: Tuple[Annotation, ...] = (), span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.annotations = annotations
        self.z3: Optional[z3.SortRef] = None

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name,)

    def __repr__(self) -> str:
        return 'SortDecl(name=%s)' % (repr(self.name), )

    def __str__(self) -> str:
        return 'sort %s' % self.name

class FunctionDecl(Decl):
    def __init__(
            self, name: str, arity: Arity, sort: Sort, mutable: bool, *,
            annotations: Tuple[Annotation, ...] = (), span: Optional[Span] = None
    ) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.arity = arity
        self.sort = sort
        self.mutable = mutable
        self.annotations = annotations
        self.mut_z3: Dict[str, z3.FuncDeclRef] = {}
        self.immut_z3: Optional[z3.FuncDeclRef] = None

        assert len(self.arity) > 0

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            mut_z3={},
            immut_z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name, tuple(self.arity), self.sort, self.mutable)

    def __repr__(self) -> str:
        return 'FunctionDecl(name=%s, arity=%s, sort=%s, mutable=%s)' % (
            repr(self.name), self.arity, self.sort, self.mutable
        )

    def __str__(self) -> str:
        return '%s function %s(%s): %s' % (
            'mutable' if self.mutable else 'immutable',
            self.name,
            ', '.join([str(s) for s in self.arity]),
            self.sort
        )

class RelationDecl(Decl):
    def __init__(
            self, name: str, arity: Arity, mutable: bool, derived: Optional[Expr] = None, *,
            annotations: Tuple[Annotation, ...] = (), span: Optional[Span] = None
    ) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.derived_axiom = derived
        self.annotations = annotations
        self.mut_z3: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]] = {}
        self.immut_z3: Optional[Union[z3.FuncDeclRef, z3.ExprRef]] = None

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            mut_z3={},
            immut_z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name, tuple(self.arity), self.mutable, self.derived_axiom)

    def __repr__(self) -> str:
        return 'RelationDecl(name=%s, arity=%s, mutable=%s, derived=%s)' % \
            (repr(self.name), self.arity, self.mutable, self.derived_axiom)

    def __str__(self) -> str:
        return '%s relation %s(%s)%s' % ('derived' if self.derived_axiom is not None else
                                         'mutable' if self.mutable else 'immutable',
                                         self.name,
                                         ', '.join([str(s) for s in self.arity]),
                                         '' if not self.derived_axiom
                                         else (': %s' % str(self.derived_axiom)))

    def is_derived(self) -> bool:
        return self.derived_axiom is not None

class ConstantDecl(Decl):
    def __init__(
            self, name: str, sort: Sort, mutable: bool, *,
            annotations: Tuple[Annotation, ...] = (), span: Optional[Span] = None
    ) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.annotations = annotations
        self.mut_z3: Dict[str, z3.ExprRef] = {}
        self.immut_z3: Optional[z3.ExprRef] = None

    def __getstate__(self) -> Any:
        return dict(
            super().__getstate__(),
            mut_z3={},
            immut_z3=None,
        )

    def _denote(self) -> Tuple:
        return (self.name, self.sort, self.mutable)

    def __repr__(self) -> str:
        return 'ConstantDecl(name=%s, sort=%s, mutable=%s)' % (repr(self.name), self.sort, self.mutable)

    def __str__(self) -> str:
        return '%s constant %s: %s' % ('mutable' if self.mutable else 'immutable',
                                       self.name, self.sort)

def close_free_vars(expr: Expr, in_scope: List[str] = [], span: Optional[Span] = None) -> Expr:
    vs = [s for s in free_ids(expr) if s not in in_scope and s.isupper()]
    if vs == []:
        return expr
    else:
        return QuantifierExpr('FORALL', tuple(SortedVar(v, None, span=span) for v in vs), expr, span=span)

class InitDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.name, self.expr)

    def __repr__(self) -> str:
        return 'InitDecl(name=%s, expr=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr))

    def __str__(self) -> str:
        return 'init %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                              self.expr)

class ModifiesClause:
    def __init__(self, name: str, *, span: Optional[Span] = None) -> None:
        self.span = span
        self.name = name

    def __repr__(self) -> str:
        return 'ModifiesClause(name=%s)' % (repr(self.name),)

    def __str__(self) -> str:
        return self.name

def uses_new(e: Expr) -> bool:
    if isinstance(e, Bool) or isinstance(e, Int):
        return False
    elif isinstance(e, UnaryExpr):
        return e.op == 'NEW' or uses_new(e.arg)
    elif isinstance(e, BinaryExpr):
        return uses_new(e.arg1) or uses_new(e.arg2)
    elif isinstance(e, NaryExpr):
        return any(uses_new(x) for x in e.args)
    elif isinstance(e, AppExpr):
        return any(uses_new(x) for x in e.args)
    elif isinstance(e, QuantifierExpr):
        return uses_new(e.body)
    elif isinstance(e, Id):
        return False
    elif isinstance(e, IfThenElse):
        return uses_new(e.branch) or uses_new(e.then) or uses_new(e.els)
    elif isinstance(e, Let):
        return uses_new(e.val) or uses_new(e.body)
    else:
        assert False, e

class DefinitionDecl(Decl):
    def __init__(self, is_public_transition: bool, num_states: int,
                 name: str, params: Tuple[SortedVar, ...],
                 mods: Tuple[ModifiesClause, ...],
                 expr: Expr,
                 *, span: Optional[Span] = None) -> None:
        def implies(a: bool, b: bool) -> bool:
            return not a or b
        # these asserts are enforced by the parser
        assert num_states in (0, 1, 2)
        assert implies(is_public_transition, num_states == 2)
        assert len(mods) == 0 or num_states == 2

        super().__init__(span)
        self.span = span
        self.is_public_transition = is_public_transition
        self.num_states = num_states
        self.name = name
        self.binder = Binder(params)
        self.arity = [sv.sort for sv in params]
        self.sort = BoolSort
        self.mods = mods
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.is_public_transition, self.num_states, self.name, self.binder, self.mods, self.expr)

    def __repr__(self) -> str:
        return 'DefinitionDecl(is_public_transition=%s, num_states=%s, name=%s, params=%s, mods=%s, expr=%s)' % (
            self.is_public_transition,
            self.num_states,
            repr(self.name),
            self.binder.vs,
            self.mods, repr(self.expr))

    def __str__(self) -> str:
        if self.is_public_transition:
            prefix = 'transition'
        else:
            if self.num_states == 0:
                kstate = 'zerostate'
            elif self.num_states == 1:
                kstate = 'onestate'
            else:
                kstate = 'twostate'

            prefix = '%s definition' % (kstate,)

        if len(self.mods) > 0:
            mods = '\n  modifies %s\n' % (', '.join([str(m) for m in self.mods],))
        else:
            mods = ' =\n'

        return '%s %s(%s)%s  %s' % \
            (prefix,
             self.name,
             ', '.join([str(v) for v in self.binder.vs]),
             mods,
             self.expr)

    @staticmethod
    def _frame(scope: Scope, mods: Tuple[ModifiesClause, ...]) -> Tuple[Expr, ...]:
        frame = []
        R: Iterator[StateDecl] = iter(scope.relations.values())
        C: Iterator[StateDecl] = iter(scope.constants.values())
        F: Iterator[StateDecl] = iter(scope.functions.values())
        for d in itertools.chain(R, C, F):
            if not d.mutable or (isinstance(d, RelationDecl) and d.is_derived()) or \
               any(mc.name == d.name for mc in mods):
                continue

            if isinstance(d, ConstantDecl) or len(d.arity) == 0:
                e = Eq(New(Id(d.name)), Id(d.name))
            else:
                names: List[str] = []
                svs: List[SortedVar] = []
                ids: List[Id] = []
                for i, s in enumerate(d.arity):
                    name = scope.fresh('x' + str(i), also_avoid=names)
                    names.append(name)
                    svs.append(SortedVar(name, s))
                    ids.append(Id(name))

                e = Forall(tuple(svs), Eq(New(AppExpr(d.name, tuple(ids))), AppExpr(d.name, tuple(ids))))

            frame.append(e)

        return tuple(frame)

    def _framed_body(self, scope: Scope) -> Expr:
        return And(self.expr, *DefinitionDecl._frame(scope, self.mods))

    def as_twostate_formula(self, scope: Scope) -> Expr:
        return Exists(self.binder.vs, self._framed_body(scope))


class InvariantDecl(Decl):
    def __init__(
            self, name: Optional[str], expr: Expr, is_safety: bool, is_sketch: bool, *, span: Optional[Span] = None
    ) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.expr = expr
        self.is_safety = is_safety
        self.is_sketch = is_sketch

    def _denote(self) -> Tuple:
        return (self.name, self.expr)

    def __repr__(self) -> str:
        return 'InvariantDecl(name=%s, expr=%s, is_safety=%s, is_sketch=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr),
            repr(self.is_safety),
            repr(self.is_sketch)
        )

    def __str__(self) -> str:
        kwd = 'safety' if self.is_safety else 'invariant'
        pre = '' if not self.is_sketch else 'sketch '
        return '%s %s%s' % (pre + kwd,
                            ('[%s] ' % self.name) if self.name is not None else '',
                            self.expr)


class AxiomDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.name = name
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.name, self.expr)

    def __repr__(self) -> str:
        return 'AxiomDecl(name=%s, expr=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr))

    def __str__(self) -> str:
        return 'axiom %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                               self.expr)

class TheoremDecl(Decl):
    def __init__(self, name: Optional[str], expr: Expr, num_states: int, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        assert num_states in (0, 1, 2)  # enforced by parser
        self.span = span
        self.name = name
        self.expr = expr
        self.num_states = num_states

    def _denote(self) -> Tuple:
        return (self.name, self.expr, self.num_states)

    def __repr__(self) -> str:
        return 'TheoremDecl(name=%s, expr=%s, num_states=%s)' % (
            repr(self.name) if self.name is not None else 'None',
            repr(self.expr),
            self.num_states
        )

    def __str__(self) -> str:
        return '%stheorem %s%s' % (
            'twostate ' if self.num_states == 2 else
            'zerostate ' if self.num_states == 0 else '',
            ('[%s] ' % self.name) if self.name is not None else '',
            self.expr
        )

class AnyTransition(Denotable):
    def _denote(self) -> Tuple:
        return ()

    def __str__(self) -> str:
        return 'any transition'

class Star(Denotable):
    def _denote(self) -> Tuple:
        return ()

    def __str__(self) -> str:
        return '*'

class TransitionCall(Denotable):
    def __init__(self, target: str, args: Optional[List[Union[Star, Expr]]], *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.target = target
        self.args = args

    def _denote(self) -> Tuple:
        return (self.target, self.args)

    def __str__(self) -> str:
        return '%s%s' % (
            self.target,
            '' if self.args is None
            else '(%s)' % ', '.join(str(a) for a in self.args)
        )

class TransitionCalls(Denotable):
    def __init__(self, calls: List[TransitionCall]) -> None:
        super().__init__()
        self.calls = calls

    def _denote(self) -> Tuple:
        return tuple(self.calls)

    def __str__(self) -> str:
        return ' | '.join(str(c) for c in self.calls)

TransitionExpr = Union[AnyTransition, TransitionCalls]

class TraceTransitionDecl(Denotable):
    def __init__(self, transition: TransitionExpr) -> None:
        super().__init__()
        self.transition = transition

    def _denote(self) -> Tuple:
        return (self.transition,)

    def __str__(self) -> str:
        return str(self.transition)

    def __repr__(self) -> str:
        return 'TraceTransitionDecl(transition=%s)' % (repr(self.transition),)


class AssertDecl(Denotable):
    # expr may only be None in first step, where it means "init"
    def __init__(self, expr: Optional[Expr], *, span: Optional[Span] = None) -> None:
        super().__init__()
        self.span = span
        self.expr = expr

    def _denote(self) -> Tuple:
        return (self.expr, )

    def __str__(self) -> str:
        return 'assert %s' % (str(self.expr),)

    def __repr__(self) -> str:
        return 'AssertDecl(expr=%s)' % (repr(self.expr),)

TraceComponent = Union[TraceTransitionDecl, AssertDecl]  # , AxiomDecl, ConstantDecl]

class TraceDecl(Decl):
    def __init__(self, components: List[TraceComponent], sat: bool, *, span: Optional[Span] = None) -> None:
        super().__init__(span)
        self.span = span
        self.components = components
        self.sat = sat

    def _denote(self) -> Tuple:
        return (tuple(self.components), self.sat)

    def __str__(self) -> str:
        return 'trace {%s\n}' % (
            '\n  '.join([''] + [str(c) for c in self.components])
        )

    def __repr__(self) -> str:
        return 'TraceDecl(components=%s, sat=%s)' % (
            repr(self.components),
            repr(self.sat)
        )

    def transitions(self) -> Iterator[TraceTransitionDecl]:
        for c in self.components:
            if isinstance(c, TraceTransitionDecl):
                yield c

@dataclass
class Annotation:
    span: Optional[Span]
    name: str
    args: List[str]

class HasAnnotations(Protocol):
    annotations: Tuple[Annotation, ...]

def has_annotation(d: HasAnnotations, name: str) -> bool:
    return any(annot.name == name for annot in d.annotations)

def get_annotation(d: HasAnnotations, name: str) -> Optional[Annotation]:
    for annot in d.annotations:
        if annot.name == name:
            return annot

    return None

class Scope(Generic[B]):
    def __init__(self) -> None:
        self.stack: List[List[Tuple[str, B]]] = []
        self.sorts: Dict[str, SortDecl] = {}
        self.relations: Dict[str, RelationDecl] = {}
        self.constants: Dict[str, ConstantDecl] = {}
        self.functions: Dict[str, FunctionDecl] = {}
        self.definitions: Dict[str, DefinitionDecl] = {}

        # invariant: num_states > 0 ==> current_state_index < num_states
        self.num_states: int = 0
        self.current_state_index: int = 0

    def new_allowed(self, n: int = 1) -> bool:
        return self.current_state_index + n < self.num_states

    def mutable_allowed(self) -> bool:
        return self.num_states > 0

    # NOTE(calling-stateful-definitions)
    # A twostate definition cannot be called from a twostate context inside of a new(), since
    # by that point we are in the "next" state. In general, when calling a k-state definition,
    # the following must hold:
    #     current_state_index + (k - 1) < num_states
    # Also note that this correctly handles the case of calling a 0-state definition from a
    # 0-state context, since then current_state_index = 0 and num_states = 0, and -1 < 0.
    def call_allowed(self, d: DefinitionDecl, n_new: int = 0) -> bool:
        return self.new_allowed(d.num_states - 1 + n_new)

    def push(self, l: List[Tuple[str, B]]) -> None:
        self.stack.append(l)

    def pop(self) -> None:
        self.stack.pop()

    def get(self, name: str) -> Union[DefinitionDecl, RelationDecl, ConstantDecl, FunctionDecl, Tuple[B], None]:
        # first, check for bound variables in scope
        for l in reversed(self.stack):
            for v, b in l:
                if v == name:
                    return (b,)

        # otherwise, check for constants/relations/functions/definitions (whose domains are disjoint)
        d = self.constants.get(name) or self.relations.get(name) or \
            self.functions.get(name) or self.definitions.get(name)
        return d

    def _check_duplicate_name(self, span: Optional[Span], name: str) -> None:
        if name in self.constants:
            utils.print_error(span, 'Name %s is already declared as a constant' % (name,))

        if name in self.relations:
            utils.print_error(span, 'Name %s is already declared as a relation' % (name,))

        if name in self.functions:
            utils.print_error(span, 'Name %s is already declared as a function' % (name,))

        if name in self.definitions:
            utils.print_error(span, 'Name %s is already declared as a definition' % (name,))

    def add_sort(self, decl: SortDecl) -> None:
        assert len(self.stack) == 0

        span = decl.span
        sort = decl.name

        if sort in self.sorts:
            utils.print_error(span, 'Duplicate sort name %s' % (sort,))

        self.sorts[sort] = decl

    def get_sort(self, sort: str) -> Optional[SortDecl]:
        return self.sorts.get(sort)

    def get_sort_checked(self, sort: str) -> SortDecl:
        res = self.get_sort(sort)
        assert res is not None
        return res

    def known_sorts(self) -> Iterable[SortDecl]:
        return list(self.sorts.values())

    def add_constant(self, decl: ConstantDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.constants[decl.name] = decl

    def add_relation(self, decl: RelationDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.relations[decl.name] = decl

    def get_relation(self, relname: str) -> Optional[RelationDecl]:
        return self.relations.get(relname)

    def add_function(self, decl: FunctionDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.functions[decl.name] = decl

    def add_definition(self, decl: DefinitionDecl) -> None:
        assert len(self.stack) == 0

        self._check_duplicate_name(decl.span, decl.name)
        self.definitions[decl.name] = decl

    def get_definition(self, definition: str) -> Optional[DefinitionDecl]:
        return self.definitions.get(definition)

    @contextmanager
    def fresh_stack(self) -> Iterator[None]:
        stack = self.stack
        self.stack = []
        yield None
        assert self.stack == []
        self.stack = stack

    @contextmanager
    def next_state_index(self, n: int = 1) -> Iterator[None]:
        if n == 0 or self.current_state_index + n < self.num_states:
            self.current_state_index += n
            yield None
            self.current_state_index -= n
        else:
            assert utils.error_count > 0, (self.current_state_index, self.num_states)
            yield None

    @contextmanager
    def n_states(self, n: int) -> Iterator[None]:
        assert n >= 0
        assert self.num_states == 0 and self.current_state_index == 0
        self.num_states = n
        self.current_state_index = 0
        yield None
        self.num_states = 0
        self.current_state_index = 0

    @contextmanager
    def in_scope(self, b: Binder, annots: List[B]) -> Iterator[None]:
        n = len(self.stack)
        assert len(b.vs) == len(annots)
        self.push(list(zip((v.name for v in b.vs), annots)))
        yield
        self.pop()
        assert n == len(self.stack)

    def fresh(self, base_name: str, also_avoid: List[str] = []) -> str:
        if self.get(base_name) is None:
            return base_name
        counter = 0
        candidate = base_name + str(counter)
        while self.get(candidate) is not None or candidate in also_avoid:
            counter += 1
            candidate = base_name + str(counter)
        return candidate

StateDecl = Union[RelationDecl, ConstantDecl, FunctionDecl]
DeclContainingExpr = Union[InitDecl, DefinitionDecl, InvariantDecl, AxiomDecl, TheoremDecl]

class Program:
    def __init__(self, decls: List[Decl]) -> None:
        self.decls = decls
        self.scope: Scope[InferenceSort]
        self.input: Optional[str] = None

    def sorts(self) -> Iterator[SortDecl]:
        for d in self.decls:
            if isinstance(d, SortDecl):
                yield d

    def inits(self) -> Iterator[InitDecl]:
        for d in self.decls:
            if isinstance(d, InitDecl):
                yield d

    def invs(self) -> Iterator[InvariantDecl]:
        for d in self.decls:
            if isinstance(d, InvariantDecl):
                yield d

    def safeties(self) -> Iterator[InvariantDecl]:
        for d in self.decls:
            if isinstance(d, InvariantDecl) and d.is_safety:
                yield d

    def definitions(self) -> Iterator[DefinitionDecl]:
        for d in self.decls:
            if isinstance(d, DefinitionDecl):
                yield d

    def transitions(self) -> Iterator[DefinitionDecl]:
        for d in self.definitions():
            if d.is_public_transition:
                yield d

    def axioms(self) -> Iterator[AxiomDecl]:
        for d in self.decls:
            if isinstance(d, AxiomDecl):
                yield d

    def theorems(self) -> Iterator[TheoremDecl]:
        for d in self.decls:
            if isinstance(d, TheoremDecl):
                yield d

    def constants(self) -> Iterator[ConstantDecl]:
        for d in self.decls:
            if isinstance(d, ConstantDecl):
                yield d

    def functions(self) -> Iterator[FunctionDecl]:
        for d in self.decls:
            if isinstance(d, FunctionDecl):
                yield d

    def relations(self) -> Iterator[RelationDecl]:
        for d in self.decls:
            if isinstance(d, RelationDecl):
                yield d

    def relations_constants_and_functions(self) -> Iterator[StateDecl]:
        for d in self.decls:
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl) or \
               isinstance(d, FunctionDecl):
                yield d

    def derived_relations(self) -> Iterator[RelationDecl]:
        for d in self.decls:
            if isinstance(d, RelationDecl) and d.derived_axiom:
                yield d

    def decls_containing_exprs(self) -> Iterator[DeclContainingExpr]:
        for d in self.decls:
            if isinstance(d, InitDecl) or \
               isinstance(d, DefinitionDecl) or \
               isinstance(d, InvariantDecl) or \
               isinstance(d, AxiomDecl) or \
               isinstance(d, TheoremDecl):
                yield d

    def traces(self) -> Iterator[TraceDecl]:
        for d in self.decls:
            if isinstance(d, TraceDecl):
                yield d

    def __repr__(self) -> str:
        return 'Program(decls=%s)' % (self.decls,)

    def __str__(self) -> str:
        return '\n'.join(str(d) for d in self.decls)


the_program: Program = cast(Program, None)

@contextmanager
def prog_context(prog: Program) -> Iterator[None]:
    global the_program
    backup_prog = the_program
    the_program = prog
    yield None
    the_program = backup_prog

def expand_macros(scope: Scope, e: Expr) -> Expr:
    if isinstance(e, (Bool, Int)):
        return e
    elif isinstance(e, UnaryExpr):
        return UnaryExpr(e.op, expand_macros(scope, e.arg), span=e.span)
    elif isinstance(e, BinaryExpr):
        return BinaryExpr(e.op, expand_macros(scope, e.arg1), expand_macros(scope, e.arg2), span=e.span)
    elif isinstance(e, NaryExpr):
        return NaryExpr(e.op, tuple(expand_macros(scope, arg) for arg in e.args), span=e.span)
    elif isinstance(e, AppExpr):
        new_args = tuple(expand_macros(scope, arg) for arg in e.args)
        d = scope.get(e.callee)
        if isinstance(d, DefinitionDecl):
            assert len(e.args) == len(d.binder.vs)  # checked by typechecker
            gamma = {Id(v.name): arg for v, arg in zip(d.binder.vs, new_args)}
            # note we recurse in the same scope, as we know the only
            # free variables in a macro definition are global symbols,
            # and such symbols cannot be shadowed, so they cannot be
            # recaptured by the current scope
            return expand_macros(scope, subst(scope, d.expr, gamma))
        else:
            return AppExpr(e.callee, new_args, e.n_new, span=e.span)
    elif isinstance(e, QuantifierExpr):
        with scope.in_scope(e.binder, [() for v in e.binder.vs]):
            new_body = expand_macros(scope, e.body)
        return QuantifierExpr(e.quant, e.binder.vs, new_body, span=e.span)
    elif isinstance(e, Id):
        d = scope.get(e.name)
        if isinstance(d, DefinitionDecl):
            return expand_macros(scope, d.expr)
        else:
            return e
    elif isinstance(e, IfThenElse):
        return IfThenElse(expand_macros(scope, e.branch), expand_macros(scope, e.then), expand_macros(scope, e.els), span=e.span)
    elif isinstance(e, Let):
        assert len(e.binder.vs) == 1
        new_val = expand_macros(scope, e.val)
        with scope.in_scope(e.binder, [()]):
            new_body = expand_macros(scope, e.body)
        return Let(e.binder.vs[0], new_val, new_body, span=e.span)
    else:
        assert False, (type(e), e)

PREC_BOT = 0
PREC_NOT = 1
PREC_MULT = 2
PREC_PLUS = 3
PREC_EQ = 4
PREC_AND = 5
PREC_OR = 6
PREC_IMPLIES = 7
PREC_IFF = 8
PREC_QUANT = 9
PREC_TOP = 10

PREC_ASSOC = {
    PREC_BOT: 'NONE',
    PREC_NOT: 'NONE',
    PREC_MULT: 'LEFT',
    PREC_PLUS: 'LEFT',
    PREC_EQ: 'NONE',
    PREC_AND: 'LEFT',
    PREC_OR: 'LEFT',
    PREC_IMPLIES: 'RIGHT',
    PREC_IFF: 'NONE',
    PREC_QUANT: 'NONE',
    PREC_TOP: 'NONE'
}

def no_parens(ip: int, op: int, side: str) -> bool:
    return ip < op or (ip == op and side == PREC_ASSOC[ip])

def pretty(e: Expr) -> str:
    buf = _pretty(e)
    return ''.join(buf)

def _pretty(e: Expr, buf: Optional[List[str]] = None, prec: int = PREC_TOP, side: str = 'NONE') -> List[str]:
    if buf is None:
        buf = []
    needs_parens = not no_parens(pretty_precedence(e), prec, side)

    if needs_parens:
        buf.append('(')
        prec = PREC_TOP
        side = 'NONE'

    pretty_no_parens(e, buf, prec, side)

    if needs_parens:
        buf.append(')')

    return buf

__print_new_as_prime = False  # This is a little hack to print "(e)'" instead of "new(e)"
def pretty_no_parens(e: Expr, buf: List[str], prec: int, side: str) -> None:
    if isinstance(e, Bool):
        buf.append('true' if e.val else 'false')
    elif isinstance(e, Int):
        buf.append(str(e.val))
    elif isinstance(e, UnaryExpr):
        if e.op == 'NOT':
            buf.append('!')
            _pretty(e.arg, buf, PREC_NOT, 'NONE')
        elif e.op == 'NEW':
            buf.append('new(' if not __print_new_as_prime else '(')
            _pretty(e.arg, buf, PREC_TOP, 'NONE')
            buf.append(')' if not __print_new_as_prime else ')\'')
        else:
            assert False
    elif isinstance(e, BinaryExpr):
        p = pretty_precedence(e)
        _pretty(e.arg1, buf, p, 'LEFT')

        pretties = {
            'IMPLIES': '->',
            'IFF': '<->',
            'EQUAL': '=',
            'NOTEQ': '!=',
            'GE': '>=',
            'GT': '>',
            'LE': '<=',
            'LT': '<',
            'PLUS': '+',
            'SUB': '-',
            'MULT': '*',
        }

        assert e.op in pretties
        s = pretties[e.op]

        buf.append(' %s ' % s)

        _pretty(e.arg2, buf, p, 'RIGHT')
    elif isinstance(e, NaryExpr):
        assert len(e.args) >= 2, "NaryExpr {} has < 2 args".format(repr(e))

        p = pretty_precedence(e)

        if e.op == 'AND':
            sep = ' & '
        elif e.op == 'OR':
            sep = ' | '
        elif e.op == 'DISTINCT':
            sep = ', '
        else:
            assert False

        if e.op == 'DISTINCT':
            buf.append('distinct(')

        _pretty(e.args[0], buf, p, 'LEFT')

        for arg in e.args[1:-1]:
            buf.append('%s' % sep)
            _pretty(arg, buf, p, 'LEFT')

        buf.append('%s' % sep)

        _pretty(e.args[-1], buf, p, 'RIGHT')

        if e.op == 'DISTINCT':
            buf.append(')')
    elif isinstance(e, AppExpr):
        buf.append(e.callee)
        buf.append("'" * e.n_new)
        buf.append('(')
        started = False
        for arg in e.args:
            if started:
                buf.append(', ')
            started = True
            _pretty(arg, buf, PREC_TOP, 'NONE')
        buf.append(')')
    elif isinstance(e, QuantifierExpr):
        buf.append(e.quant.lower())
        buf.append(' ')

        started = False
        for sv in e.binder.vs:
            if started:
                buf.append(', ')
            started = True
            buf.append(str(sv))
        buf.append('. ')

        _pretty(e.body, buf, PREC_QUANT, 'NONE')
    elif isinstance(e, Id):
        buf.append(e.name)
    elif isinstance(e, IfThenElse):
        buf.append('if ')
        _pretty(e.branch, buf, PREC_TOP, 'NONE')
        buf.append(' then ')
        _pretty(e.then, buf, PREC_TOP, 'NONE')
        buf.append(' else ')
        _pretty(e.els, buf, PREC_TOP, 'NONE')
    elif isinstance(e, Let):
        buf.append('let ')
        buf.append(str(e.binder.vs[0]))
        buf.append(' = ')
        _pretty(e.val, buf, PREC_TOP, 'NONE')
        buf.append(' in ')
        _pretty(e.body, buf, PREC_TOP, 'NONE')
    else:
        assert False

def pretty_precedence(e: Expr) -> int:
    if isinstance(e, (Bool, Int)):
        return PREC_BOT
    elif isinstance(e, UnaryExpr):
        if e.op == 'NOT':
            return PREC_NOT
        elif e.op == 'NEW':
            return PREC_BOT
        else:
            assert False
    elif isinstance(e, BinaryExpr):
        if e.op == 'IMPLIES':
            return PREC_IMPLIES
        elif e.op == 'IFF':
            return PREC_IFF
        elif e.op in ['EQUAL', 'NOTEQ', 'GE', 'GT', 'LE', 'LT']:
            return PREC_EQ
        elif e.op in ['PLUS', 'SUB']:
            return PREC_PLUS
        elif e.op in ['MULT']:
            return PREC_MULT
        else:
            assert False
    elif isinstance(e, NaryExpr):
        if e.op == 'AND':
            return PREC_AND
        elif e.op == 'OR':
            return PREC_OR
        elif e.op == 'DISTINCT':
            return PREC_BOT
        else:
            assert False
    elif isinstance(e, AppExpr):
        return PREC_BOT
    elif isinstance(e, QuantifierExpr):
        return PREC_QUANT
    elif isinstance(e, Id):
        return PREC_BOT
    elif isinstance(e, IfThenElse):
        return PREC_TOP
    elif isinstance(e, Let):
        return PREC_TOP
    else:
        assert False, "Unknown expression type %s: %s" % (type(e), repr(e))
