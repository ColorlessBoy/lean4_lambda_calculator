# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-12-12
License: MIT
"""

from level import Level

# 优先级: Sort == Const == BoundVar == NatLiteral == StrLiteral > App > Lambda > Forall > Pair

class Expr:
    def __hash__(self):
        return hash(repr(self))  # 默认以 __repr__ 为基础计算哈希
    
    @property
    def predicate(self) -> int:
        return -1

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
        return f"S({self.level})"

    @property
    def predicate(self) -> int:
        return 100

class Const(Expr):
    def __init__(self, label: str):
        self.label = label
    
    def __eq__(self, value):
        if isinstance(value, Const) and self.label == value.label:
            return True
        return False

    def __repr__(self):
        return f"{self.label}"

    @property
    def predicate(self) -> int:
        return 100

class BoundVar(Expr):
    def __init__(self, index: int):
        self.index = index
    
    def __eq__(self, value):
        if isinstance(value, BoundVar) and self.index == value.index:
            return True
        return False

    def __repr__(self):
        return f"#{self.index}"

    @property
    def predicate(self) -> int:
        return 100

class Arg(Expr):
    def __init__(self, type: Expr, name: Expr | None):
        self.name = name
        self.type = type
    
    def __eq__(self, value):
        if isinstance(value, Arg):
            return self.type == value.type
        return self.type == value 
    
    def __repr__(self) -> str:
        if self.name is None:
            return f"{self.type}"
        return f"{self.name} : {self.type}"
    
    @property
    def predicate(self) -> int:
        if self.name is None:
            return self.type.predicate
        return 0

class Forall(Expr):
    def __init__(self, var_type: Expr, body: Expr):
        if isinstance(var_type, Arg):
            self.var_type = var_type
        else:
            self.var_type = Arg(var_type, None)
        self.body = body

    def __eq__(self, value):
        if isinstance(value, Forall) and self.var_type == value.var_type and self.body == value.body:
            return True
        return False

    def __repr__(self) -> str:
        # Forall 是右结合的，所以左边表达式判断包含等号，右边表达式判断不包含等号
        if self.var_type.predicate <= self.predicate:
            left = f"({self.var_type})"
        else:
            left = f"{self.var_type}"
        if self.body.predicate < self.predicate:
            right = f"({self.body})"
        else:
            right = f"{self.body}"
        return f"{left} -> {right}"

    @property
    def predicate(self) -> int:
        return 1

class Lambda(Expr):
    def __init__(self, var_type: Expr, body: Expr):
        if isinstance(var_type, Arg):
            self.var_type = var_type
        else:
            self.var_type = Arg(var_type, None)
        self.body = body

    def __eq__(self, value):
        if isinstance(value, Lambda) and self.var_type == value.var_type and self.body == value.body:
            return True
        return False

    def __repr__(self) -> str:
        # Lambda 是右结合的，所以左边表达式判断包含等号，右边表达式判断不包含等号
        if self.var_type.predicate <= self.predicate:
            left = f"({self.var_type})"
        else:
            left = f"{self.var_type}"
        if self.body.predicate < self.predicate:
            right = f"({self.body})"
        else:
            right = f"{self.body}"
        return f"{left} => {right}"

    @property
    def predicate(self) -> int:
        return 2

class App(Expr):
    def __init__(self, func: Expr, arg: Expr):
        self.func = func
        self.arg = arg

    def __eq__(self, value):
        if isinstance(value, App) and self.func == value.func and self.arg == value.arg:
            return True
        return False

    def __repr__(self) -> str:
        # App 是左结合的，所以右边表达式判断包含等号，左边表达式判断不包含等号
        if self.func.predicate < self.predicate:
            left = f"({self.func})"
        else:
            left = f"{self.func}"
        if self.arg.predicate <= self.predicate:
            right = f"({self.arg})"
        else:
            right = f"{self.arg}"
        return f"{left} {right}"

    @property
    def predicate(self) -> int:
        return 3

class NatLiteral(Expr):
    def __init__(self, var: int):
        self.var = var

    def __eq__(self, value):
        if isinstance(value, NatLiteral) and self.var == value.var:
            return True
        return False

    def __repr__(self):
        return str(self.var)

    @property
    def predicate(self) -> int:
        return 100

class StrLiteral(Expr):
    def __init__(self, var: str):
        self.var = var

    def __eq__(self, value):
        if isinstance(value, StrLiteral) and self.var == value.var:
            return True
        return False

    def __repr__(self):
        return self.var

    @property
    def predicate(self) -> int:
        return 100

# 优先级: Sort == Const == BoundVar == NatLiteral == StrLiteral > App > Lambda > Forall > Pair
def print_expr_by_name(expr: Expr, context: list[Arg] = None) -> str:
    if context is None:
        context = []
    if isinstance(expr, Sort) or isinstance(expr, Const) or isinstance(expr, NatLiteral) or isinstance(expr, StrLiteral):
        return str(expr)
    elif isinstance(expr, Arg):
        if expr.name is None:
            return f"{print_expr_by_name(expr.type, context)}"
        return f"{expr.name} : {print_expr_by_name(expr.type, context)}"
    elif isinstance(expr, BoundVar):
        assert expr.index < len(context), "Out of bound"
        pair = context[expr.index]
        if pair.name is None:
            return str(expr)
        return str(pair.name)
    elif isinstance(expr, App):
        if expr.func.predicate < expr.predicate:
            left = f"({print_expr_by_name(expr.func, context)})"
        else:
            left = f"{print_expr_by_name(expr.func, context)}"
        if expr.arg.predicate <= expr.predicate:
            right = f"({print_expr_by_name(expr.arg, context)})"
        else:
            right = f"{print_expr_by_name(expr.arg, context)}"
        return f"{left} {right}"
    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        if expr.var_type.predicate <= expr.predicate:
            left = f"({print_expr_by_name(expr.var_type, context)})"
        else:
            left = f"{print_expr_by_name(expr.var_type, context)}"
        if expr.body.predicate < expr.predicate:
            right = f"({print_expr_by_name(expr.body, [expr.var_type] + context)})"
        else:
            right = f"{print_expr_by_name(expr.body, [expr.var_type] + context)}"
        if isinstance(expr, Lambda):
            return f"{left} => {right}"
        else:
            return f"{left} -> {right}"
    
# 优先级: Sort == Const == BoundVar == NatLiteral == StrLiteral > App > Lambda > Forall > Pair
def print_expr_by_index(expr: Expr) -> str:
    if isinstance(expr, Sort) or isinstance(expr, Const) or isinstance(expr, NatLiteral) or isinstance(expr, StrLiteral):
        return str(expr)
    elif isinstance(expr, Arg):
        return f"{print_expr_by_index(expr.type)}"
    elif isinstance(expr, BoundVar):
        return f"#{expr.index}"
    elif isinstance(expr, App):
        if expr.func.predicate < expr.predicate:
            left = f"({print_expr_by_index(expr.func)})"
        else:
            left = f"{print_expr_by_index(expr.func)}"
        if expr.arg.predicate <= expr.predicate:
            right = f"({print_expr_by_index(expr.arg)})"
        else:
            right = f"{print_expr_by_index(expr.arg)}"
        return f"{left} {right}"
    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        if expr.var_type.type.predicate <= expr.predicate:
            left = f"({print_expr_by_index(expr.var_type.type)})"
        else:
            left = f"{print_expr_by_index(expr.var_type.type)}"
        if expr.body.predicate < expr.predicate:
            right = f"({print_expr_by_index(expr.body)})"
        else:
            right = f"{print_expr_by_index(expr.body)}"
        if isinstance(expr, Lambda):
            return f"{left} => {right}"
        else:
            return f"{left} -> {right}"

if __name__ == "__main__":
    Prop = Const("Prop")
    Iff = Const("Iff")
    expr1 = Forall(Prop, Forall(Prop, Forall(Forall(BoundVar(1), BoundVar(1)),
        Forall(Forall(BoundVar(1), BoundVar(3)), App(App(Iff, BoundVar(3)), BoundVar(2)))
    )))
    print("expr1 :", print_expr_by_name(expr1))
    # expr1 : Prop -> Prop -> (#1 -> #1) -> (#1 -> #3) -> Iff #3 #2
    expr2 = Forall(Arg(Prop, "a"), Forall(Arg(Prop, "b"), Forall(Forall(BoundVar(1), BoundVar(1)),
        Forall(Forall(BoundVar(1), BoundVar(3)), App(App(Iff, BoundVar(3)), BoundVar(2)))
    )))
    print("expr2 :", print_expr_by_name(expr2))
    print("expr2 :", print_expr_by_index(expr2))
    # expr2 : (a : Prop) -> (b : Prop) -> (a -> b) -> (b -> a) -> Iff a b

    expr3 = Lambda(Prop, Lambda(Prop, Forall(BoundVar(1), BoundVar(1))))
    print("expr3 :", print_expr_by_name(expr3))
    # expr3 : Prop => Prop => (#1 -> #1)

    expr4 = Lambda(Arg(Prop, "a"), Lambda(Arg(Prop, "b"), Forall(BoundVar(1), BoundVar(1))))
    print("expr4 :", print_expr_by_name(expr4))
    # expr4 : (a : Prop) => (b : Prop) => (a -> b)

    print("expr4 :", print_expr_by_index(expr4))
