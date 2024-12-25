# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-11-27
License: MIT
"""

from level import Level, SuccLevel, MaxLevel, PreLevel
from expr import Expr, BoundVar, Const, Lambda, Forall, App, Sort, Proj, NatVar, StrVar

VarType = tuple[Expr, Expr]


def shift_context(context: list[VarType]):
    new_context = []
    for expr, type in context:
        shifted_expr = shift_expr(expr)
        shifted_type = shift_expr(type)
        new_context.append((shifted_expr, shifted_type))
    return new_context

def shift_expr(expr: Expr, offset=0):
    if isinstance(expr, BoundVar):
        if expr.index >= offset:
            return BoundVar(expr.index + 1)
        return expr
    elif isinstance(expr, Const):
        return expr
    elif isinstance(expr, Lambda):
        shifted_var_type = shift_expr(expr.var_type, offset=offset)
        shifted_body = shift_expr(expr.body, offset=offset + 1)
        return Lambda(shifted_var_type, shifted_body)
    elif isinstance(expr, Forall):
        shifted_var_type = shift_expr(expr.var_type, offset=offset)
        shifted_body = shift_expr(expr.body, offset=offset + 1)
        return Forall(shifted_var_type, shifted_body)
    elif isinstance(expr, App):
        shifted_func = shift_expr(expr.func, offset=offset)
        shifted_arg = shift_expr(expr.arg, offset=offset)
        return App(shifted_func, shifted_arg)
    return expr

def unshift_expr(expr: Expr, offset=0, head=None):
    if isinstance(expr, BoundVar):
        if expr.index >= offset:
            if expr.index == offset:
                return head
            return BoundVar(expr.index - 1)
        return expr
    elif isinstance(expr, Const):
        return expr
    elif isinstance(expr, Lambda):
        shifted_var_type = unshift_expr(expr.var_type, offset=offset, head=head)
        shifted_body = unshift_expr(expr.body, offset=offset + 1, head=shift_expr(head))
        return Lambda(shifted_var_type, shifted_body)
    elif isinstance(expr, Forall):
        shifted_var_type = unshift_expr(expr.var_type, offset=offset, head=head)
        shifted_body = unshift_expr(expr.body, offset=offset + 1, head=shift_expr(head))
        return Forall(shifted_var_type, shifted_body)
    elif isinstance(expr, App):
        shifted_func = unshift_expr(expr.func, offset=offset, head=head)
        shifted_arg = unshift_expr(expr.arg, offset=offset, head=head)
        return App(shifted_func, shifted_arg)
    return expr

# 全局缓存
level_cache = {}

def get_level(expr: Expr, context: list[VarType], type_pool: dict[str, Expr]) -> Level:
    if context is None:
        context = []
    # 生成缓存键
    cache_key = str(expr) + str(context)
    if cache_key in level_cache:
        return level_cache[cache_key]

    # 原始逻辑
    if isinstance(expr, Sort):
        result = expr.level
    elif isinstance(expr, Const):
        assert expr.label in type_pool, f"Const {expr.label} is not defined."
        expr_type = type_pool[expr.label]
        result = PreLevel(get_level(expr_type, context, type_pool))
    elif isinstance(expr, BoundVar):
        next_expr, next_expr_type = context[expr.index]
        if isinstance(next_expr, BoundVar):
            type_level = get_level(next_expr_type, context, type_pool)
            result = PreLevel(type_level)
        else:
            result = get_level(next_expr, context, type_pool)
    elif isinstance(expr, Forall):
        left = get_level(expr.var_type, context, type_pool)
        right = get_level(
            expr.body, [(BoundVar(0), shift_expr(expr.var_type))] + shift_context(context), type_pool
        )
        result = MaxLevel(left, right)
    elif isinstance(expr, Lambda):
        lambda_var_type = expr.var_type
        lambda_var_level = get_level(lambda_var_type, context, type_pool)
        lambda_new_items = [(BoundVar(0), shift_expr(lambda_var_type))] + shift_context(context)
        lambda_body_level = get_level(expr.body, lambda_new_items, type_pool)
        result = PreLevel(MaxLevel(lambda_var_level, SuccLevel(lambda_body_level)))
    elif isinstance(expr, App):
        _, func_type = calc(expr.func, context, type_pool)
        if not isinstance(func_type, Forall):
            raise ValueError('Function application to a non-function')
        func_context = [(BoundVar(0), shift_expr(func_type.var_type))] + shift_context(context)
        result = PreLevel(get_level(func_type.body, func_context, type_pool))
    else:
        result = Level(-1)

    # 存入缓存
    level_cache[cache_key] = result
    return result

def calc(expr: Expr, context: list[VarType], type_pool: dict[str, Expr], def_pool: dict[str, Expr] = None) -> VarType:
    if def_pool is None:
        def_pool = {}
    if isinstance(expr, Sort):
        return expr, Sort(SuccLevel(expr.level))
    elif isinstance(expr, Const):
        assert expr.label in type_pool, f"Const {expr.label} is not defined."
        expr_type, _ = calc(type_pool[expr.label], context, type_pool, def_pool)
        if expr.label in def_pool:
            expr_def, expr_def_type = calc(def_pool[expr.label], context, type_pool, def_pool)
            return expr_def, expr_def_type
        return expr, expr_type
    elif isinstance(expr, BoundVar):
        assert expr.index < len(
            context
        ), f"Index {expr.index} out of bounds for context: {context}"
        return context[expr.index]
    elif isinstance(expr, Forall):
        var_type, _ = calc(expr.var_type, context, type_pool, def_pool)
        shifted_var_type = shift_expr(var_type)
        shifted_context = [(BoundVar(0), shifted_var_type)] + shift_context(context)
        shifted_body, shifted_body_type = calc(
            expr.body, shifted_context, type_pool, def_pool
        )
        return_expr = Forall(var_type, shifted_body)
        return_type = Sort(MaxLevel(get_level(var_type, context, type_pool), get_level(shifted_body_type, shifted_context, type_pool)))
        return return_expr, return_type
    elif isinstance(expr, Lambda):
        var_type, _ = calc(expr.var_type, context, type_pool, def_pool)
        shifted_var_type = shift_expr(var_type)
        shifted_context = [(BoundVar(0), shifted_var_type)] + shift_context(context)
        shifted_body, shifted_body_type = calc(
            expr.body, shifted_context, type_pool, def_pool
        )
        return_expr = Lambda(var_type, shifted_body)
        return_type = Forall(var_type, shifted_body_type)
        return return_expr, return_type
    elif isinstance(expr, App):
        arg, arg_type = calc(expr.arg, context, type_pool, def_pool)
        func, func_type = calc(expr.func, context, type_pool, def_pool)
        assert isinstance(func_type, Forall)
        # BUG: 没有正确处理 sort
        if not isinstance(arg_type, Sort) and not isinstance(func_type.var_type, Sort):
            assert (
                arg_type == func_type.var_type
            ), f"Type mismatch: want\n  {func_type.var_type}\nget\n  {arg_type}\n\n"
        tmp = unshift_expr(func_type.body, head=arg)
        unshifted_funcbody_type, _ = calc(tmp, context, type_pool, def_pool)
        if isinstance(func, Lambda):
            tmp = unshift_expr(func.body, head=arg)
            unshifted_funcbody, _ = calc(tmp, context, type_pool, def_pool)
            return unshifted_funcbody, unshifted_funcbody_type
        return App(func, arg), unshifted_funcbody_type
    elif isinstance(expr, Proj):
        tuple_value, tuple_type = calc(expr.tuple_expr, context, type_pool, def_pool)
        # BUG: 暂时无法获得Type
        return Proj(expr.typename, expr.index, tuple_value), Sort('u')
    elif isinstance(expr, NatVar):
        return expr, Const("Nat")
    elif isinstance(expr, StrVar):
        return expr, Const("String")
    else:
        raise ValueError("Unknown expr", expr)


if __name__ == "__main__":
    Prop = Sort(0)
    Decidable = Const("Decidable")
    type_pool = {
        "Prop": Sort(1),
        "Decidable": Forall(Prop, Sort(1)),
        "Not": Forall(Prop, Prop),
        "Iff": Forall(Prop, Forall(Prop, Prop)),
        "Iff_intro": Forall(
            Prop,
            Forall(
                Prop,
                Forall(
                    Forall(BoundVar(1), BoundVar(1)),
                    Forall(
                        Forall(BoundVar(1), BoundVar(3)),
                        App(App(Const("Iff"), BoundVar(3)), BoundVar(2)),
                    ),
                ),
            ),
        ),
    }

    Eq = Forall(
        Prop,
        Forall(
            Forall(BoundVar(0), BoundVar(1)),
            Forall(BoundVar(1), BoundVar(2)),
        ),
    )
    Eq_proof = Lambda(
        Prop,
        Lambda(
            Forall(BoundVar(0), BoundVar(1)),
            Lambda(BoundVar(1), App(BoundVar(1), BoundVar(0))),
        ),
    )
    print("Eq:\n ", Eq)
    print("Eq_proof:\n ", Eq_proof)
    _, Eq_proof_calc_type = calc(Eq_proof, [], type_pool)
    print("Eq_proof_calc_type:\n ", Eq_proof_calc_type)
    print("Check proof of eq_proof_calc:\n ", Eq == Eq_proof_calc_type)

    Iff_refl = Forall(Prop, App(App(Const("Iff"), BoundVar(0)), BoundVar(0)))
    Iff_refl_proof = Lambda(
        Prop,
        App(
            App(
                App(App(Const("Iff_intro"), BoundVar(0)), BoundVar(0)),
                Lambda(BoundVar(0), BoundVar(0)),
            ),
            Lambda(BoundVar(0), BoundVar(0)),
        ),
    )

    print("Iff_intro_type:\n ", type_pool["Iff_intro"])
    print("Iff_refl:\n ", Iff_refl)
    print("Iff_refl_proof:\n ", Iff_refl_proof)
    _, Iff_refl_proof_calc_type = calc(Iff_refl_proof, [], type_pool)
    print("Iff_refl_proof_calc_type:\n ", Iff_refl_proof_calc_type)
    print("Check proof:\n ", Iff_refl == Iff_refl_proof_calc_type)

    # Decidable 类型相关表达式
    type_pool["Decidable.isTrue"] = Forall(
        Prop, Forall(BoundVar(0), App(Const("Decidable"), BoundVar(1)))
    )

    type_pool["Decidable.isFalse"] = Forall(
        Prop,
        Forall(App(Const("Not"), BoundVar(0)), App(Const("Decidable"), BoundVar(1))),
    )

    type_pool["Decidable.rec"] = Forall(
            Prop,
            Forall(
                Forall(
                    App(Const("Decidable"), BoundVar(0)),
                    Sort("u"),
                ),
                Forall(
                    Forall(
                        App(Const("Not"), BoundVar(1)),
                        App(
                            BoundVar(1),
                            App(
                                App(Const("Decidable.isFalse"), BoundVar(2)),
                                BoundVar(0),
                            ),
                        ),
                    ),
                    Forall(
                        Forall(
                            BoundVar(2),
                            App(
                                BoundVar(2),
                                App(
                                    App(Const("Decidable.isTrue"), BoundVar(3)),
                                    BoundVar(0),
                                ),
                            ),
                        ),
                        Forall(
                            App(Const("Decidable"), BoundVar(3)),
                            App(BoundVar(3), BoundVar(0)),
                        ),
                    ),
                ),
            ),
        )

    type_pool["Decidable.casesOn"] = Forall(
            Prop,
            Forall(
                Forall(
                    App(Const("Decidable"), BoundVar(0)),
                    Sort("u"),
                ),
                Forall(
                    App(Const("Decidable"), BoundVar(1)),
                    Forall(
                        Forall(
                            App(Const("Not"), BoundVar(2)),
                            App(
                                BoundVar(2),
                                App(
                                    App(Const("Decidable.isFalse"), BoundVar(3)),
                                    BoundVar(0),
                                ),
                            ),
                        ),
                        Forall(
                            Forall(
                                BoundVar(3),
                                App(
                                    BoundVar(3),
                                    App(
                                        App(Const("Decidable.isTrue"), BoundVar(4)),
                                        BoundVar(0),
                                    ),
                                ),
                            ),
                            App(BoundVar(3), BoundVar(2)),
                        ),
                    ),
                ),
            ),
        )

    Decidable_casesOn_proof = Lambda(
        Prop,
        Lambda(
            Forall(
                App(Const("Decidable"), BoundVar(0)),
                Sort("u"),
            ),
            Lambda(
                App(Const("Decidable"), BoundVar(1)),
                Lambda(
                    Forall(
                        App(Const("Not"), BoundVar(2)),
                        App(
                            BoundVar(2),
                            App(
                                App(Const("Decidable.isFalse"), BoundVar(3)),
                                BoundVar(0),
                            ),
                        ),
                    ),
                    Lambda(
                        Forall(
                            BoundVar(3),
                            App(
                                BoundVar(3),
                                App(
                                    App(Const("Decidable.isTrue"), BoundVar(4)),
                                    BoundVar(0),
                                ),
                            ),
                        ),
                        App(
                            App(
                                App(
                                    App(
                                        App(Const("Decidable.rec"), BoundVar(4)),
                                        BoundVar(3),
                                    ),
                                    Lambda(
                                        App(Const("Not"), BoundVar(4)),
                                        App(BoundVar(2), BoundVar(0)),
                                    ),
                                ),
                                Lambda(
                                    BoundVar(4),
                                    App(BoundVar(1), BoundVar(0)),
                                ),
                            ),
                            BoundVar(2),
                        ),
                    ),
                ),
            ),
        ),
    )

    # 验证 Decidable.casesOn 类型
    DecidableCasesOnType = type_pool["Decidable.casesOn"]
    print("casesOn_type:\n ", DecidableCasesOnType)
    print("casesOn_proof:\n ", Decidable_casesOn_proof)
    _, casesOn_proof_calc_type = calc(Decidable_casesOn_proof, [], type_pool)
    print("casesOn_proof_calc_type:\n ", casesOn_proof_calc_type)
    print("Check proof:\n ", DecidableCasesOnType == casesOn_proof_calc_type)
