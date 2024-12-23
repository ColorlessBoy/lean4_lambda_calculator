from expr import Expr, Const, App, Lambda, Forall, Sort, BoundVar, Proj, NatVar, StrVar
from level import Level, SuccLevel, MaxLevel
import re
from typing import List
import os
from calculator import calc


def tokenize(expr: str) -> List[str]:
    """将输入字符串拆分为标记列表"""
    # 使用正则表达式匹配括号、标识符和数字
    pattern = r"[()]|[A-Za-z0-9_.\u00A0-\uFFFF]+|\S"
    tokens = re.findall(pattern, expr)
    return tokens


def parse(tokens: List[str]) -> Expr:
    """解析标记列表并生成表达式树"""
    if not tokens:
        raise ValueError("Unexpected end of tokens")

    token = tokens.pop(0)

    if token == "(":
        # 递归解析括号内的表达式
        expr = parse(tokens)
        if not tokens or tokens.pop(0) != ")":
            raise ValueError("Missing closing parenthesis")
        return expr

    elif token == "C":
        # Const: (C label)
        label = tokens.pop(0)
        return Const(label)

    elif token == "A":
        # App: (A func arg)
        func = parse(tokens)
        arg = parse(tokens)
        return App(func, arg)

    elif token == "L":
        # Lambda: (L var_type body)
        var_type = parse(tokens)
        body = parse(tokens)
        return Lambda(var_type, body)

    elif token == "F":
        # Forall: (F var_type body)
        var_type = parse(tokens)
        body = parse(tokens)
        return Forall(var_type, body)

    elif token == "S":
        # Sort: (S level)
        level = parse_level(tokens)
        return Sort(level)

    elif token == "#":
        # BoundVar: (#index)
        index = int(tokens.pop(0))
        return BoundVar(index)

    elif token == "P":
        # Proj: (Proj typename index tuple_expr)
        typename = tokens.pop(0)
        index = int(tokens.pop(0))
        tuple_expr = parse(tokens)
        return Proj(typename, index, tuple_expr)
    
    elif token == "NL":
        var = int(tokens.pop(0))
        return NatVar(var)
    
    elif token == "SL":
        var = tokens.pop(0).strip('"')
        return StrVar(var)

    else:
        raise ValueError(f"Unknown token: {token}")


def parse_level(tokens: List[str]) -> Level:
    """解析 Level 对象"""
    token = tokens.pop(0)
    if token == '(':
        level = parse_level(tokens)
        assert len(tokens) > 0 and tokens[0] == ')', "Missing closing parenthesis"
        tokens.pop(0)
        return level
    elif token.isdigit():
        return Level(int(token))
    elif token == "max":
        # MaxLevel: (max left right)
        left = parse_level(tokens)
        right = parse_level(tokens)
        return MaxLevel(left, right)
    else:
        if tokens[0] == "+" and tokens[1] == "1":
            tokens.pop(0)
            tokens.pop(0)
            return SuccLevel(Level(token))
        else:
            return Level(token)


def parse_expr(expr_str: str) -> Expr:
    """将字符串解析为表达式对象"""
    tokens = tokenize(expr_str)
    return parse(tokens)


def get_const(expr: Expr) -> list[str]:
    if isinstance(expr, Const):
        return [expr.label]

    elif isinstance(expr, App):
        return get_const(expr.func) + get_const(expr.arg)

    elif isinstance(expr, Lambda) or isinstance(expr, Forall):
        return get_const(expr.var_type) + get_const(expr.body)

    elif isinstance(expr, Sort) or isinstance(expr, BoundVar):
        return []

    elif isinstance(expr, Proj):
        return get_const(expr.tuple_expr)
    
    elif isinstance(expr, NatVar):
        return ["Nat"]
    
    elif isinstance(expr, StrVar):
        return ["String"]

    else:
        raise ValueError(f"Unknown expr: {expr}")


def load_thm(thmname: str):
    filepath = os.path.join("data", "thms", thmname + ".txt")
    with open(filepath, "r") as f:
        lines = [line.strip() for line in f.readlines()]
        if len(lines) == 2:
            lines.append('')
    return lines


class ThmsPool:
    def __init__(self):
        self.type_pool: dict[str, Expr] = {}
        self.def_pool: dict[str, Expr] = {}

    def update(self, expr: Expr):
        consts = get_const(expr)
        next_exprs: list[Expr] = []
        for const in consts:
            if const in self.type_pool:
                continue
            _, const_type, const_def = load_thm(const)
            parsed_type = parse_expr(const_type)
            self.type_pool[const] = parsed_type
            next_exprs.append(parsed_type)
            if len(const_def) > 0:
                parsed_def = parse_expr(const_def)
                self.def_pool[const] = parsed_def
                next_exprs.append(parsed_def)
        for next_expr in next_exprs:
            self.update(next_expr)

# 测试代码
if __name__ == "__main__":
    # 测试解析 mul_right_cancel_iff
    # thmname = "mul_right_cancel_iff"
    thmname = "PosMulReflectLE"
    _, thmtype, thmproof = load_thm(thmname)
    parsed_thmtype = parse_expr(thmtype)
    print(f"{thmname}:\n  {parsed_thmtype}")
    parsed_thmproof = parse_expr(thmproof)
    print(f"{thmname} proof:\n  {parsed_thmproof}")

    thmspool = ThmsPool()
    thmspool.update(parsed_thmtype)
    thmspool.update(parsed_thmproof)

    calc_thmproof, calc_thmtype = calc(parsed_thmproof, [], thmspool.type_pool, thmspool.def_pool)

    print(f"{thmname} calc proof:\n  {calc_thmproof}")
    print(f"{thmname} calc type:\n  {calc_thmtype}")

    print("Check:", parsed_thmtype == calc_thmtype)


