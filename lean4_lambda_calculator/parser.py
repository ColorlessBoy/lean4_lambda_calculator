from expr import Expr, Const, App, Lambda, Forall, Sort, BoundVar, Proj, NatVar, StrVar
from level import Level, SuccLevel, MaxLevel
import re
from typing import List
import os
from calculator import calc


def tokenize(expr: str) -> List[str]:
    """将输入字符串拆分为标记列表"""
    # 使用正则表达式匹配括号、标识符和数字
    pattern = r"[()+:]|->|=>|[A-Za-z0-9_.\u00A0-\uFFFF]+|\S"
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

Prop = str(Sort(0))

class ThmsPool:
    def __init__(self):
        self.type_pool: dict[str, Expr] = {}
        self.def_pool: dict[str, Expr] = {}

    def update(self, expr: Expr):
        consts = get_const(expr)
        next_exprs: list[Expr] = []
        defs: list[tuple[str, Expr]] = []
        for const in consts:
            if const in self.type_pool:
                continue
            _, const_type, const_def = load_thm(const)
            parsed_type = parse_expr(const_type)
            self.type_pool[const] = parsed_type
            next_exprs.append(parsed_type)
            if str(const_type) != Prop and len(const_def) > 0 and '(P' not in const_def:
                parsed_def = parse_expr(const_def)
                next_exprs.append(parsed_def)
                defs.append((const, parsed_def))
                self.def_pool[const] = parsed_def
        for next_expr in next_exprs:
            self.update(next_expr)
    
    def simplifyDef(self):
        for const, def_expr in self.def_pool.items():
            self.def_pool[const] = calc(def_expr, [], self.type_pool, self.def_pool)[0]
        
# 测试代码
if __name__ == "__main__":
    # thmname = "mul_right_cancel_iff"
    # thmname = "PosMulReflectLE"
    # thmname = "mul_le_mul_left"
    thmname = "Zero.toOfNat0"
    _, thmtype, thmproof = load_thm(thmname)
    parsed_thmtype = parse_expr(thmtype)
    print(f"{thmname}:\n  {parsed_thmtype}")
    parsed_thmproof = parse_expr(thmproof)
    print(f"{thmname} proof:\n  {parsed_thmproof}")

    thmspool = ThmsPool()
    thmspool.update(parsed_thmtype)
    thmspool.update(parsed_thmproof)
    thmspool.simplifyDef()

    calc_thmproof, calc_thmtype = calc(parsed_thmproof, [], thmspool.type_pool, thmspool.def_pool)

    print(f"{thmname} calc proof:\n  {calc_thmproof}")
    print(f"{thmname} calc type:\n  {calc_thmtype}")

    print("Check:", parsed_thmtype == calc_thmtype)


    parsed_proof1 = parse_expr("(L (S u+1) (F #0 (S 0)))")
    calc_proof1, calc_type1 = calc(parsed_proof1, [], {}, {})
    print("parsed_proof1:", parsed_proof1)
    print("calc_proof1:", calc_proof1)
    print("calc_type1:", calc_type1)

    parsed_proof2 = parse_expr("(L (S u+1) (L (F #0 (S 0)) #0))")
    calc_proof2, calc_type2 = calc(parsed_proof2, [], {}, {})
    print("parsed_proof2:", parsed_proof2)
    print("calc_proof2:", calc_proof2)
    print("calc_type2:", calc_type2)

    parsed_proof3 = parse_expr("(F (S u+1) (F (F #0 (S 0)) (A (C Set) #1)))")
    calc_proof3, calc_type3 = calc(parsed_proof3, [], {"Set": calc_type1}, {"Set": parsed_proof1})
    print("parsed_proof3:", parsed_proof3)
    print("calc_proof3:", calc_proof3)
    print("calc_type3:", calc_type3)

    print("Check:", calc_type2 == calc_proof3)
