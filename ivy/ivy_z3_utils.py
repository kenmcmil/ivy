from z3 import *

def _is_algebraic(ctx, a):
    return Z3_is_algebraic_number(ctx.ref(), a)

def _is_numeral(ctx, a):
    return Z3_is_numeral_ast(ctx.ref(), a)

def _to_expr_ref(a, ctx):
    if isinstance(a, Pattern):
        return PatternRef(a, ctx)
    ctx_ref = ctx.ref()
    k = Z3_get_ast_kind(ctx_ref, a)
    if k == Z3_QUANTIFIER_AST:
        return QuantifierRef(a, ctx)
    sk = Z3_get_sort_kind(ctx_ref, Z3_get_sort(ctx_ref, a))
    if sk == Z3_BOOL_SORT:
        return BoolRef(a, ctx)
    if sk == Z3_INT_SORT:
        if k == Z3_NUMERAL_AST:
            return IntNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_REAL_SORT:
        if k == Z3_NUMERAL_AST:
            return RatNumRef(a, ctx)
        if _is_algebraic(ctx, a):
            return AlgebraicNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_BV_SORT:
        if k == Z3_NUMERAL_AST:
            return BitVecNumRef(a, ctx)
        else:
            return BitVecRef(a, ctx)
    if sk == Z3_ARRAY_SORT:
        return ArrayRef(a, ctx)
    if sk == Z3_DATATYPE_SORT:
        return DatatypeRef(a, ctx)
    if sk == Z3_FLOATING_POINT_SORT:
        if k == Z3_APP_AST and _is_numeral(ctx, a):
            return FPNumRef(a, ctx)
        else:
            return FPRef(a, ctx)
    if sk == Z3_FINITE_DOMAIN_SORT:
        if k == Z3_NUMERAL_AST:
            return FiniteDomainNumRef(a, ctx)
        else:
            return FiniteDomainRef(a, ctx)
    if sk == Z3_ROUNDING_MODE_SORT:
        return FPRMRef(a, ctx)
    if sk == Z3_SEQ_SORT:
        return SeqRef(a, ctx)
    if sk == Z3_RE_SORT:
        return ReRef(a, ctx)
    return ExprRef(a, ctx)

def _to_ast_array(args):
    sz = len(args)
    _args = (Ast * sz)()
    for i in range(sz):
        _args[i] = args[i].as_ast()
    return _args, sz
