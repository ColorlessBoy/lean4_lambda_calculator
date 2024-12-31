from lark import Lark, Transformer, UnexpectedInput
from lean4_lambda_calculator.expr import BoundVar, Const, Lambda, Forall, App, Sort, Arg, print_expr_by_name, Expr, const_to_boundvar
from lean4_lambda_calculator.level import SuccLevel, MaxLevel, Level

# 优先级: Sort == Const == BoundVar > App > Lambda > Forall > Arg
# 定义 Lark 文法
expr_grammar = r"""
    start: expr

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
    const: /[a-zA-Z_][\w_]*/  -> const 
    boundvar: "#" INT -> boundvar

    // 层级表达式
    level: level "+" "1" -> succlevel
         | INT -> unwrap
         | /[a-zA-Z_][\w_]*/ -> unwrap
         | "Max" "(" level "," level ")"  -> maxlevel

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
    
    def succlevel(self, items):
        return SuccLevel(Level(str(items[0])))
    
    def maxlevel(self, items):
        return MaxLevel(Level(str(items[0])), Level(str(items[1])))

    def sort(self, items):
        return Sort(items[0])

    def const(self, items):
        return Const(str(items[0]))

    def boundvar(self, items):
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

class Parser:
    def __init__(self):
        self.parser = Lark(expr_grammar, parser="lalr", transformer=ExprTransformer())

    def parse(self, code: str) -> Expr:
        try:
            expr = self.parser.parse(code)
            return const_to_boundvar(expr, [])
        except UnexpectedInput as e:
            return self.handle_error(e)

    def handle_error(self, e: UnexpectedInput):
        expected = e.expected  # 获取预期的 token
        line, column = e.line, e.column  # 出错的位置
        message = f"Syntax error at line {line}, column {column}. Expected one of: {expected}"
        return message

if __name__ == "__main__":
    # 解析 Unicode 表达式
    Prop = Sort("u+1")
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