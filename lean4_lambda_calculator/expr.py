# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-12-12
License: MIT
"""

from lean4_lambda_calculator.level import Level, level_subs_symbols, Eq, parse_level

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
        elif isinstance(level, int):
            self.level: Level = Level(level)
        else:
            self.level: Level = parse_level(level)
    
    def __eq__(self, value):
        if isinstance(value, Sort):
            return self.level == value.level
        return False

    def __repr__(self) -> str:
        return f"Sort({self.level})"

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
    def __init__(self, index: int, name: str = None):
        self.index = index
        self.name = name
    
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
    def __init__(self, type: Expr, name: str | None = None):
        self.type = type
        self.name = name
    
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

# 优先级: Sort == Const == BoundVar > App > Lambda > Forall > Arg
def print_expr_by_name(expr: Expr, context: list[Arg] = None) -> str:
    if context is None:
        context = []
    if isinstance(expr, Sort) or isinstance(expr, Const):
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
    
def print_expr_by_index(expr: Expr) -> str:
    if isinstance(expr, Sort) or isinstance(expr, Const):
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

def expr_rename_args(expr: Expr):
    # 1. 获取所有使用的变量
    # 2. 保留已经命名过的使用变量
    # 3. 为没有命名的使用变量赋予新的名字 
    used_vars = _get_used_args(expr, [])
    used_names = set([var.name for var in used_vars if var.name is not None])
    _arg_set_name(expr, used_vars, 0, used_names)

def _get_used_args(expr: Expr, context: list[Arg]) -> list[Arg]:
    if isinstance(expr, Sort) or isinstance(expr, Const) or isinstance(expr, Arg):
        return []
    elif isinstance(expr, BoundVar):
        assert expr.index < len(context), "Out of bound"
        return [context[expr.index]]
    elif isinstance(expr, App):
        return _get_used_args(expr.func, context) + _get_used_args(expr.arg, context)
    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        return _get_used_args(expr.body, [expr.var_type] + context)
    return []

def _arg_set_name(expr: Expr, used_vars: list[Arg], next_index: int, used_names: set[str]) -> int:
    if isinstance(expr, Sort) or isinstance(expr, Const):
        return next_index
    elif isinstance(expr, Arg):
        if expr in used_vars:
            if expr.name is None:
                expr.name, next_index = _get_new_name(next_index, used_names)
            return next_index
        else:
            expr.name = None
            return next_index
    elif isinstance(expr, App):
        index = _arg_set_name(expr.func, used_vars, next_index, used_names)
        return _arg_set_name(expr.arg, used_vars, index, used_names)
    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        index = _arg_set_name(expr.var_type, used_vars, next_index, used_names)
        return _arg_set_name(expr.body, used_vars, index, used_names)

def _get_new_name(index: int, used_names: set[str]) -> tuple[str, int]:
    while True:
        name = chr(ord('a') + index)
        if name not in used_names:
            return name, index + 1 
        index += 1

def expr_clean_unsed_name(expr: Expr):
    used_vars = _get_used_args(expr, [])
    _clean_unused_name(expr, used_vars)

def expr_clean_all_names(expr: Expr):
    _clean_unused_name(expr, [])

def _clean_unused_name(expr: Expr, used_vars: list[Arg]):
    if isinstance(expr, Arg):
        if len(used_vars) == 0 or expr not in used_vars:
            expr.name = None
    elif isinstance(expr, App):
        _clean_unused_name(expr.func, used_vars)
        _clean_unused_name(expr.arg, used_vars)
    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        _clean_unused_name(expr.var_type, used_vars)
        _clean_unused_name(expr.body, used_vars)

    
def expr_rename_level(expr: Expr, used_free_symbols: set[str]) -> Expr:
    if len(used_free_symbols) == 0: 
        return expr, []
    renamed_symbols = {} 
    new_expr = _set_new_level(expr, used_free_symbols, renamed_symbols) 
    return new_expr, renamed_symbols.values()

def _set_new_level(expr: Expr, used_free_symbols: set[str], renamed_symbols: dict[str, str]) -> Expr:
    if isinstance(expr, Sort):
        new_level = level_subs_symbols(expr.level, used_free_symbols, renamed_symbols)
        return Sort(new_level)
    elif isinstance(expr, Const):
        return expr
    elif isinstance(expr, Arg):
        return Arg(_set_new_level(expr.type, used_free_symbols, renamed_symbols), expr.name)
    elif isinstance(expr, BoundVar):
        return expr
    elif isinstance(expr, App):
        return App(_set_new_level(expr.func, used_free_symbols, renamed_symbols), _set_new_level(expr.arg, used_free_symbols, renamed_symbols))
    elif isinstance(expr, Lambda):
        return Lambda(_set_new_level(expr.var_type, used_free_symbols, renamed_symbols), _set_new_level(expr.body, used_free_symbols, renamed_symbols))
    elif isinstance(expr, Forall):
        return Forall(_set_new_level(expr.var_type, used_free_symbols, renamed_symbols), _set_new_level(expr.body, used_free_symbols, renamed_symbols))
    else:
        raise ValueError("Unknown expr", expr)

def expr_todef(expr: Expr, def_pool: dict[str, Expr]) -> Expr:
    if len(def_pool) == 0:
        return expr
    if isinstance(expr, Sort):
        return expr
    elif isinstance(expr, Const):
        if expr.label in def_pool:
            return def_pool[expr.label]
        return expr
    elif isinstance(expr, Arg):
        return Arg(expr_todef(expr.type, def_pool), expr.name)
    elif isinstance(expr, BoundVar):
        return expr
    elif isinstance(expr, App):
        return App(expr_todef(expr.func, def_pool), expr_todef(expr.arg, def_pool))
    elif isinstance(expr, Lambda):
        return Lambda(expr_todef(expr.var_type, def_pool), expr_todef(expr.body, def_pool))
    elif isinstance(expr, Forall):
        return Forall(expr_todef(expr.var_type, def_pool), expr_todef(expr.body, def_pool))
    else:
        raise ValueError("Unknown expr", expr)

def get_sort_eq_conditions(target: Expr, source: Expr) -> list[str]:
    if target != source:
        return []
    if isinstance(target, Arg):
        target = target.type
    if isinstance(source, Arg):
        source = source.type
    if isinstance(target, Sort):
        if isinstance(source, Sort):
            eq = Eq(target.level.symbol, source.level.symbol)
            if eq.has_free():
                return [str(eq)]
        return []
    elif isinstance(target, Const):
        return []
    elif isinstance(target, BoundVar):
        return []
    elif isinstance(target, App):
        return get_sort_eq_conditions(target.func, source.func) + get_sort_eq_conditions(target.arg, source.arg)
    elif isinstance(target, Lambda) or isinstance(target, Forall):
        return get_sort_eq_conditions(target.var_type, source.var_type) + get_sort_eq_conditions(target.body, source.body)
    else:
        raise ValueError("Unknown expr", target)

def const_to_boundvar(expr: Expr, context: list[Arg]):
    if isinstance(expr, Sort):
        return expr
    elif isinstance(expr, Const):
        for idx, arg in enumerate(context):
            if arg.name == expr.label:
                return BoundVar(idx)
        return expr
    elif isinstance(expr, Arg):
        return Arg(const_to_boundvar(expr.type, context), expr.name)
    elif isinstance(expr, BoundVar):
        return expr
    elif isinstance(expr, App):
        return App(const_to_boundvar(expr.func, context), const_to_boundvar(expr.arg, context))
    elif isinstance(expr, Lambda):
        return Lambda(const_to_boundvar(expr.var_type, context), const_to_boundvar(expr.body, [expr.var_type] + context))
    elif isinstance(expr, Forall):
        return Forall(const_to_boundvar(expr.var_type, context), const_to_boundvar(expr.body, [expr.var_type] + context))
    else:
        raise ValueError("Unknown expr", expr)

def set_boundvar_name(expr: Expr, context: list[Arg]) -> None:
    # inmemory change expr
    if isinstance(expr, Sort):
        return
    elif isinstance(expr, Const):
        return
    elif isinstance(expr, Arg):
        return set_boundvar_name(expr.type, context)
    elif isinstance(expr, BoundVar):
        if expr.name is not None:
            context[expr.index].name = expr.name
            expr.name = None
    elif isinstance(expr, App):
        set_boundvar_name(expr.func, context)
        set_boundvar_name(expr.arg, context)
    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        set_boundvar_name(expr.var_type, context)
        set_boundvar_name(expr.body, [expr.var_type] + context)
    else:
        raise ValueError("Unknown expr", expr)
