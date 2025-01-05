from lark import Lark, Transformer, UnexpectedInput
from lean4_lambda_calculator.expr import BoundVar, Const, Lambda, Forall, App, Sort, Arg, print_expr_by_name, Expr, const_to_boundvar, set_boundvar_name
from lean4_lambda_calculator.level import SuccLevel, MaxLevel, Level
from lean4_lambda_calculator.calculator import calc

class TypeDef:
    def __init__(self, name: str, type: Expr):
        self.name = name
        self.type = type

class EqDef:
    def __init__(self, name: str, expr: Expr):
        self.name = name
        self.expr = expr

class ThmDef:
    def __init__(self, name: str, type: Expr):
        self.name = name
        self.type = type


# 优先级: Sort == Const == BoundVar > App > Lambda > Forall > Arg
# 定义 Lark 文法
expr_grammar = r"""
    start: definition | thm | expr

    definition: "def" identifier ":" expr -> typedef
              | "def" identifier "=" expr -> eqdef
    
    thm: "thm" identifier ":" expr -> thmdef

    // 优先级从高到低
    expr: primary | app | lambda | forall
    primary: sort | const | boundvar

    // App 是左结合
    app: app appexpr          -> app
       | appexpr appexpr      -> app
    appexpr: primary | "(" expr ")" 

    // Lambda 是右结合
    lambda: lambdaarg "=>" lambdabody -> lam
    lambdaarg: "(" const ":" expr ")" -> arg
        | lambdaargexpr
    lambdaargexpr: primary | app | "(" expr ")"
    lambdabody: lambda | lambdaargexpr

    // Forall 是右结合
    forall: forallarg "->" forallbody -> forall
    forallarg: "(" const ":" expr ")" -> arg
        | forallargexpr 
    forallargexpr: primary | app | lambda | "(" expr ")"
    forallbody: forall | forallargexpr

    // 基本类型
    sort: "Sort" "(" level ")"  -> sort 
    const: identifier  -> const 
    boundvar: "#" INT (":" identifier)? -> boundvar

    // 层级表达式
    level: level "+" "1" -> succlevel
         | INT -> unwrap
         | identifier -> unwrap
         | "Max" "(" level "," level ")"  -> maxlevel
    
    identifier: /[a-zA-Z_\.][\w_\.]*/ -> identifier

    %import common.INT
    %import common.WS
    %ignore WS
"""

# 定义 Transformer
class ExprTransformer(Transformer):
    # 默认行为
    def __default__(self, data, children, meta):
        return self.unwrap(children)

    def unwrap(self, items):
        rst = items[0]
        return rst
    
    def identifier(self, items):
        return str(items[0])
    
    def succlevel(self, items):
        return SuccLevel(Level(str(items[0])))
    
    def maxlevel(self, items):
        return MaxLevel(Level(str(items[0])), Level(str(items[1])))

    def sort(self, items):
        return Sort(items[0])

    def const(self, items):
        return Const(str(items[0]))

    def boundvar(self, items):
        if len(items) >= 2:
            return BoundVar(int(str(items[0])), items[1])
        return BoundVar(int(str(items[0])))
    
    def app(self, items):
        return App(items[0], items[1])
    
    def lam(self, items):
        arg, body = items
        return Lambda(arg, body)

    def forall(self, items):
        arg, body = items
        return Forall(arg, body)

    def arg(self, items):
        return Arg(items[1], str(items[0]))
    
    def typedef(self, items):
        return TypeDef(items[0], items[1])
    
    def eqdef(self, items):
        return EqDef(items[0], items[1])
    
    def thmdef(self, items):
        return ThmDef(items[0], items[1])

class Parser:
    def __init__(self):
        self.parser = Lark(expr_grammar, parser="lalr", transformer=ExprTransformer())

    def parse(self, code: str) -> Expr|str:
        try:
            expr = self.parser.parse(code)
            if isinstance(expr, Expr):
                expr = const_to_boundvar(expr, [])
                set_boundvar_name(expr, [])
            elif isinstance(expr, TypeDef):
                tmp = const_to_boundvar(expr.type, [])
                set_boundvar_name(tmp, [])
                expr = TypeDef(expr.name, tmp)
            elif isinstance(expr, EqDef):
                tmp = const_to_boundvar(expr.expr, [])
                set_boundvar_name(tmp, [])
                expr = EqDef(expr.name, tmp)
            elif isinstance(expr, ThmDef):
                tmp = const_to_boundvar(expr.type, [])
                set_boundvar_name(tmp, [])
                expr = ThmDef(expr.name, tmp)
            return expr
        except Exception as e:
            return self.handle_error(e)

    def handle_error(self, e: UnexpectedInput):
        expected = e.expected  # 获取预期的 token
        line, column = e.line, e.column  # 出错的位置
        message = f"Syntax error at line {line}, column {column}. Expected one of: {expected}"
        return message

if __name__ == "__main__":
    # 解析 Unicode 表达式
    Prop = Sort(0)
    Iff = Const("Iff")
    expr = Forall(Arg(Prop, "a"), Forall(Arg(Prop, "b"), Forall(Forall(BoundVar(1), BoundVar(1)),
        Forall(Forall(BoundVar(1), BoundVar(3)), App(App(Iff, BoundVar(3)), BoundVar(2)))
    )))
    code = print_expr_by_name(expr)
    parser = Parser()
    parsed_expr = parser.parse(code)
    print("expr:\n ", code)
    print("parsed_expr:\n ", print_expr_by_name(parsed_expr))
    print(parsed_expr == expr)

    code2 = "(Prop -> Prop) => Sort(0) => #1 #0"
    parsed_expr2 = parser.parse(code2)
    print(parsed_expr2)
    expr2, expr2_type = calc(parsed_expr2, [],  {"Prop":Sort(1)}, {"Prop":Sort(0)})
    print(expr2_type)

    thm = "thm Iff.refl : Prop -> Iff #0 #0"
    parsed_thm = parser.parse(thm)
    print(parsed_thm)

    thm2 = "def Forall = (a:Sort(u))=>(b:a->Prop)=>((c:a)->b c)"
    parsed_thm2 = parser.parse(thm2)
    assert isinstance(parsed_thm2, EqDef)
    thm2, thm2_type = calc(parsed_thm2.expr, [], {"Prop":Sort(1)}, {"Prop":Sort(0)})
    print(thm2_type)