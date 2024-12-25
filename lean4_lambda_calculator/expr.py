# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-12-12
License: MIT
"""

from level import Level

class Expr:
    def __hash__(self):
        return hash(repr(self))  # 默认以 __repr__ 为基础计算哈希

class Sort(Expr):
    def __init__(self, level: Level | int | str):
        if isinstance(level, Level):
            self.level: Level = level
        else:
            self.level: Level = Level(level)
    
    def __eq__(self, value):
        if isinstance(value, Sort):
            return self.level == value.level
        return False

    def __repr__(self) -> str:
        return f"(S {self.level})"

class Const(Expr):
    def __init__(self, label: str):
        self.label = label
    
    def __eq__(self, value):
        if isinstance(value, Const) and self.label == value.label:
            return True
        return False

    def __repr__(self):
        return f"(C {self.label})"


class BoundVar(Expr):
    def __init__(self, index: int):
        self.index = index
    
    def __eq__(self, value):
        if isinstance(value, BoundVar) and self.index == value.index:
            return True
        return False

    def __repr__(self):
        return f"#{self.index}"


class Forall(Expr):
    def __init__(self, var_type: Expr, body: Expr):
        self.var_type = var_type
        self.body = body

    def __eq__(self, value):
        if isinstance(value, Forall) and self.var_type == value.var_type and self.body == value.body:
            return True
        return False

    def __repr__(self) -> str:
        return f"(F {self.var_type} {self.body})"


class Lambda(Expr):
    def __init__(self, var_type: Expr, body: Expr):
        self.var_type = var_type
        self.body = body

    def __eq__(self, value):
        if isinstance(value, Lambda) and self.var_type == value.var_type and self.body == value.body:
            return True
        return False

    def __repr__(self) -> str:
        return f"(L {self.var_type} {self.body})"


class App(Expr):
    def __init__(self, func: Expr, arg: Expr):
        self.func = func
        self.arg = arg

    def __eq__(self, value):
        if isinstance(value, App) and self.func == value.func and self.arg == value.arg:
            return True
        return False

    def __repr__(self) -> str:
        return f"(A {self.func} {self.arg})"

class Proj(Expr):
    def __init__(self, typename: str, index: int, tuple_expr: Expr):
        self.typename = typename
        self.index = index
        self.tuple_expr = tuple_expr

    def __eq__(self, value):
        if isinstance(value, Proj) and self.typename == value.typename and self.index == value.index and self.tuple_expr== value.tuple_expr:
            return True
        return False

    def __repr__(self):
        return f"(P {self.typename} {self.index} {self.tuple_expr})"

class NatVar(Expr):
    def __init__(self, var: int):
        self.var = var

    def __eq__(self, value):
        if isinstance(value, NatVar) and self.var == value.var:
            return True
        return False

    def __repr__(self):
        return str(self.var)


class StrVar(Expr):
    def __init__(self, var: str):
        self.var = var

    def __eq__(self, value):
        if isinstance(value, StrVar) and self.var == value.var:
            return True
        return False

    def __repr__(self):
        return self.var
