# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-11-27
License: MIT
"""

from lean4_lambda_calculator.level import Level, SuccLevel, MaxLevel, PreLevel, is_solvable
from lean4_lambda_calculator.expr import Expr, BoundVar, Const, Lambda, Forall, App, Sort, Arg, expr_rename_level, expr_todef, get_sort_eq_conditions


# 求解表达式的类型
# 返回化简后的表达式和类型
def calc(expr: Expr, context: list[Arg] = None, type_pool: dict[str, Expr] = None, def_pool: dict[str, Expr] = None, used_free_symbols: set[str] = None) -> tuple[Expr, Expr]:
    if context is None:
        context = []
    if type_pool is None:
        type_pool = {}
    if def_pool is None:
        def_pool = {}
    if used_free_symbols is None:
        used_free_symbols: set[str] = set()
    if isinstance(expr, Sort):
        used_free_symbols.update(str(s) for s in expr.level.symbol.free_symbols)
        return expr, Sort(SuccLevel(expr.level))
    elif isinstance(expr, Const):
        assert expr.label in type_pool, f"Const {expr.label} is not defined."
        # 常量的类型的定义不需要考虑上下文化简, 直接返回定义的类型 
        expr_type, new_used_free_symbols = expr_rename_level(type_pool[expr.label], used_free_symbols)
        used_free_symbols.update(new_used_free_symbols)
        return expr, expr_type
    elif isinstance(expr, Arg):
        arg_type, _ = calc(expr.type, context, type_pool, def_pool, used_free_symbols)
        return Arg(arg_type, expr.name), arg_type
    elif isinstance(expr, BoundVar):
        assert expr.index < len(
            context
        ), f"Index {expr.index} out of bounds for context: {context}"
        return expr, shift_expr(context[expr.index].type, offset=0, step=expr.index+1)
    elif isinstance(expr, Forall):
        assert isinstance(expr.var_type, Arg), f"Type of variable in Forall should be Arg, but got {expr.var_type}"
        var_type, _ = calc(expr.var_type, context, type_pool, def_pool, used_free_symbols)
        assert isinstance(var_type, Arg), f"Type of variable in Forall should be Arg, but got {var_type}"
        new_context = [var_type] + context
        new_body, body_type = calc(
            expr.body, new_context, type_pool, def_pool, used_free_symbols
        )
        return_expr = Forall(var_type, new_body)
        return_type = Sort(SuccLevel(MaxLevel(get_level(var_type, context, type_pool), get_level(new_body, new_context, type_pool))))
        return return_expr, return_type
    elif isinstance(expr, Lambda):
        assert isinstance(expr.var_type, Arg), f"Type of variable in Lambda should be Arg, but got {expr.var_type}"
        var_type, _ = calc(expr.var_type, context, type_pool, def_pool, used_free_symbols)
        assert isinstance(var_type, Arg), f"Type of variable in Forall should be Arg, but got {var_type}"
        new_context = [var_type] + context
        new_body, body_type = calc(
            expr.body, new_context, type_pool, def_pool, used_free_symbols
        )
        return_expr = Lambda(var_type, new_body)
        return_type = Forall(var_type, body_type)
        return return_expr, return_type
    elif isinstance(expr, App):
        arg, arg_type = calc(expr.arg, context, type_pool, def_pool, used_free_symbols)
        func, func_type = calc(expr.func, context, type_pool, def_pool, used_free_symbols)
        assert isinstance(func_type, Forall)
        assert DefEq(func_type.var_type, arg_type, context, type_pool, def_pool, used_free_symbols), f"Type mismatch: want\n  {func_type.var_type}\nget\n  {arg_type}\n\n"
        tmp = unshift_expr(func_type.body, head=arg, offset=0)
        unshifted_funcbody_type, _ = calc(tmp, context, type_pool, def_pool, used_free_symbols)
        if isinstance(func, Lambda):
            tmp = unshift_expr(func.body, head=arg, offset=0)
            unshifted_funcbody, _ = calc(tmp, context, type_pool, def_pool, used_free_symbols)
            return unshifted_funcbody, unshifted_funcbody_type
        return App(func, arg), unshifted_funcbody_type
    else:
        raise ValueError("Unknown expr", expr)

def DefEq(target: Expr, source: Expr, context: list[Arg], type_pool: dict[str, Expr], def_pool: dict[str, Expr], used_free_symbols: set[str]) -> bool:
    if target == source:
        return True
    subs_target = calc(expr_todef(target, def_pool), context, type_pool, None, used_free_symbols)[0]
    subs_source = calc(expr_todef(source, def_pool), context, type_pool, None, used_free_symbols)[0]
    if subs_target == subs_source:
        conditions = get_sort_eq_conditions(subs_target, subs_source)
        if is_solvable(conditions):
            return True
    return False

def shift_expr(expr: Expr, offset: int, step: int):
    if step == 0:
        return expr
    if isinstance(expr, Sort):
        return expr
    elif isinstance(expr, Const):
        return expr
    elif isinstance(expr, Arg):
        return Arg(shift_expr(expr.type, offset=offset, step=step), expr.name)
    elif isinstance(expr, BoundVar):
        if expr.index >= offset:
            return BoundVar(expr.index + step)
        return expr
    elif isinstance(expr, Forall):
        shifted_var_type = shift_expr(expr.var_type, offset=offset, step=step)
        shifted_body = shift_expr(expr.body, offset=offset + 1, step=step)
        return Forall(shifted_var_type, shifted_body)
    elif isinstance(expr, Lambda):
        shifted_var_type = shift_expr(expr.var_type, offset=offset, step=step)
        shifted_body = shift_expr(expr.body, offset=offset + 1, step=step)
        return Lambda(shifted_var_type, shifted_body)
    elif isinstance(expr, App):
        shifted_func = shift_expr(expr.func, offset=offset, step=step)
        shifted_arg = shift_expr(expr.arg, offset=offset, step=step)
        return App(shifted_func, shifted_arg)
    else:
        raise ValueError("Unknown expr", expr)

def unshift_expr(expr: Expr, offset: int, head: Expr):
    if isinstance(expr, Sort):
        return expr
    elif isinstance(expr, Const):
        return expr
    elif isinstance(expr, Arg):
        return Arg(unshift_expr(expr.type, offset=offset, head=head), expr.name)
    elif isinstance(expr, BoundVar):
        if expr.index >= offset:
            if expr.index == offset:
                return shift_expr(head, offset=0, step=offset)
            return BoundVar(expr.index - 1)
        return expr
    elif isinstance(expr, Forall):
        shifted_var_type = unshift_expr(expr.var_type, offset=offset, head=head)
        shifted_body = unshift_expr(expr.body, offset=offset + 1, head=head)
        return Forall(shifted_var_type, shifted_body)
    elif isinstance(expr, Lambda):
        shifted_var_type = unshift_expr(expr.var_type, offset=offset, head=head)
        shifted_body = unshift_expr(expr.body, offset=offset + 1, head=head)
        return Lambda(shifted_var_type, shifted_body)
    elif isinstance(expr, App):
        shifted_func = unshift_expr(expr.func, offset=offset, head=head)
        shifted_arg = unshift_expr(expr.arg, offset=offset, head=head)
        return App(shifted_func, shifted_arg)
    return expr

def get_level(expr: Expr, context: list[Arg], type_pool: dict[str, Expr]) -> Level:
    if isinstance(expr, Sort):
        result = expr.level
    elif isinstance(expr, Const):
        assert expr.label in type_pool, f"Const {expr.label} is not defined."
        expr_type = type_pool[expr.label]
        result = PreLevel(get_level(expr_type, context, type_pool))
    elif isinstance(expr, Arg):
        result = get_level(expr.type, context, type_pool)
    elif isinstance(expr, BoundVar):
        next_expr = context[expr.index]
        result = PreLevel(get_level(next_expr, context[expr.index+1:], type_pool))
    elif isinstance(expr, Forall):
        left = get_level(expr.var_type, context, type_pool)
        right = get_level(expr.body, [expr.var_type] + context, type_pool)
        result = MaxLevel(left, right)
    elif isinstance(expr, Lambda):
        left = get_level(expr.var_type, context, type_pool)
        right = get_level(expr.body, [expr.var_type] + context, type_pool)
        result = PreLevel(MaxLevel(left, SuccLevel(right)))
    elif isinstance(expr, App):
        _, func_type = calc(expr.func, context, type_pool)
        assert isinstance(func_type, Forall), f"Function application to a non-function: {func_type}"
        result = PreLevel(get_level(func_type.body, [func_type.var_type] + context, type_pool))
    else:
        raise ValueError("Unknown expr", expr)
    return result
