# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-12-12
License: MIT
"""

from level import Level, normalize_level, NatLevel

class Expr:
    def __hash__(self):
        return hash(repr(self))  # 默认以 __repr__ 为基础计算哈希
    
    @property
    def predicate(self) -> int:
        return -1

class Sort(Expr):
    def __init__(self, level: Level):
        self.level: Level = level

    def __repr__(self) -> str:
        return f"Sort({self.level})"

    @property
    def predicate(self) -> int:
        return 100

Sort0 = Sort(NatLevel(0))
Sort1 = Sort(NatLevel(1))

class Const(Expr):
    def __init__(self, label: str):
        self.label = label

    def __repr__(self):
        return f"{self.label}"

    @property
    def predicate(self) -> int:
        return 100

class BoundVar(Expr):
    def __init__(self, index: int, name: str | None = None):
        self.index = index # De Bruijn 索引
        self.name = name

    def __repr__(self):
        return f"#{self.index}"

    @property
    def predicate(self) -> int:
        return 100

class Param(Expr):
    def __init__(self, type: Expr, name: str | None = None):
        self.type = type
        self.name = name
    
    def __repr__(self) -> str:
        if self.name is None:
            return f"{self.type}"
        return f"{self.name}:{self.type}"
    
    @property
    def predicate(self) -> int:
        if self.name is None:
            return self.type.predicate
        return 0

class Forall(Expr):
    def __init__(self, params: list[Param], body: Expr):
        assert len(params) > 0, "Forall must have at least one paramseter."
        self.params = params
        self.body = body

    def __repr__(self) -> str:
        # Forall 是右结合的，所以左边表达式判断包含等号，右边表达式判断不包含等号
        if len(self.params) == 1:
            if self.params[0].predicate <= self.predicate:
                left = f"({self.params[0]})"
            else:
                left = f"{self.params[0]}"
        else:
            left = f"({','.join([str(v) for v in self.params])})"
        if self.body.predicate < self.predicate:
            right = f"({self.body})"
        else:
            right = f"{self.body}"
        return f"{left}->{right}"

    @property
    def predicate(self) -> int:
        return 1

class Lambda(Expr):
    def __init__(self, params: list[Param], body: Expr):
        assert len(params) > 0, "Lambda must have at least one paramseter."
        self.params = params
        self.body = body

    def __repr__(self) -> str:
        # Lambda 是右结合的，所以左边表达式判断包含等号，右边表达式判断不包含等号
        if len(self.params) == 1:
            if self.params[0].predicate <= self.predicate:
                left = f"({self.params[0]})"
            else:
                left = f"{self.params[0]}"
        else:
            left = f"({','.join([str(v) for v in self.params])})"
        if self.body.predicate < self.predicate:
            right = f"({self.body})"
        else:
            right = f"{self.body}"
        return f"{left}=>{right}"

    @property
    def predicate(self) -> int:
        return 2

class App(Expr):
    def __init__(self, func: Expr, args: list[Expr]):
        assert len(args) > 0, "App must have at least one argument."
        self.func = func
        self.args = args

    def __repr__(self) -> str:
        # App 是左结合的，所以右边表达式判断包含等号，左边表达式判断不包含等号
        if self.func.predicate < self.predicate:
            left = f"({self.func})"
        else:
            left = f"{self.func}"
        right = f"({', '.join([str(a) for a in self.args])})"
        return f"{left}{right}"

    @property
    def predicate(self) -> int:
        return 3

# 优先级: Sort == Const == BoundVar > App > Lambda > Forall > Arg

# 表达式规范化，主要是将嵌套的 App、Lambda、Forall、Arg 进行展开
def normalize_expr(expr: Expr) -> Expr:
    # 目前不进行任何规范化，直接返回原表达式
    if isinstance(expr, App):
        func, args = normalize_expr(expr.func), [normalize_expr(a) for a in expr.args]
        while isinstance(func, App):
            args = func.args + args
            func = func.func
        return App(func, args)
    elif isinstance(expr, Lambda):
        var_types, body = [Param(normalize_expr(v.type),v.name) for v in expr.params], normalize_expr(expr.body)
        while isinstance(body, Lambda):
            var_types = body.params + var_types
            body = body.body
        return Lambda(var_types, body)
    elif isinstance(expr, Forall):
        var_types, body = [Param(normalize_expr(v.type),v.name) for v in expr.params], normalize_expr(expr.body)
        while isinstance(body, Forall):
            var_types = body.params + var_types
            body = body.body
        return Forall(var_types, body)
    elif isinstance(expr, Param):
        return Param(normalize_expr(expr.type), expr.name)
    elif isinstance(expr, Sort):
        return Sort(normalize_level(expr.level))
    return expr

def mk_normalize_forall(args: list[Param], body: Expr) -> Forall:
    # 将嵌套的 Forall 展开
    while isinstance(body, Forall):
        args = body.params + args
        body = body.body
    return Forall(args, body)

def mk_normalize_lambda(args: list[Param], body: Expr) -> Lambda:
    while isinstance(body, Lambda):
        args = body.params + args
        body = body.body
    return Lambda(args, body)

def is_equivalent(expr1: Expr, expr2: Expr) -> bool:
    # 目前直接比较规范化后的表达式是否相等
    return normalize_expr(expr1) == normalize_expr(expr2)

def to_string(expr: Expr, args: list[str]=[]) -> str:
    if isinstance(expr, Sort):
        if expr.level.is_zero():
            return "Prop" # 特例：Sort 0 就是 Prop
        if expr.level.is_one():
            return "Type" # 特例：Sort 1 就是 Type
        return str(expr)
    if isinstance(expr, Const):
        return str(expr)
    if isinstance(expr, BoundVar):
        if expr.index >= len(args):
            return str(expr)
        s = args[len(args) - 1 - expr.index] 
        if s:
            return s
        return str(expr)
    if isinstance(expr, Param):
        if expr.name:
            return f"{expr.name}:{to_string(expr.type, args)}"
        return to_string(expr.type, args)
    if isinstance(expr, Forall):
        params = []
        params_to_args = []
        for v in expr.params:
            param_str = to_string(v, args + params_to_args)
            params.append(param_str)
            param_to_arg_str = '' if v.name is None else v.name
            params_to_args.append(param_to_arg_str)
        if len(expr.params) == 1:
            if expr.params[0].predicate <= expr.predicate:
                left = f"({params[0]})->"
            else:
                left = f"{params[0]}->"
        else:
            left = f"({', '.join(params)})->"
        right = to_string(expr.body, args + params_to_args)
        if expr.body.predicate < expr.predicate:
            right = f"({right})"
        return f"{left}{right}" 
    if isinstance(expr, Lambda):
        params = []
        params_to_args = []
        for v in expr.params:
            param_str = to_string(v, args + params_to_args)
            params.append(param_str)
            param_to_arg_str = '' if v.name is None else v.name
            params_to_args.append(param_to_arg_str)
        if len(expr.params) == 1:
            if expr.params[0].predicate <= expr.predicate:
                left = f"({params[0]})=>"
            else:
                left = f"{params[0]}=>"
        else:
            left = f"({', '.join(params)})=>"
        right = to_string(expr.body, args + params_to_args)
        if expr.body.predicate < expr.predicate:
            right = f"({right})"
        return f"{left}{right}"
    if isinstance(expr, App):
        if expr.func.predicate < expr.predicate:
            func = f"({to_string(expr.func, args)})"
        else:
            func = to_string(expr.func, args)
        args_str = [to_string(a, args) for a in expr.args]
        right = f"({','.join(args_str)})"
        return f"{func}{right}"
    raise Exception(f"Unknown expression type: {type(expr)}")

    