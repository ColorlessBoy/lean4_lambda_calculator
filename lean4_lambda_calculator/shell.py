
from lean4_lambda_calculator.expr import print_expr_by_name, Expr
from lean4_lambda_calculator.calculator import calc, expr_todef
from lean4_lambda_calculator.parser import Parser, EqDef, TypeDef

def main():
    parser = Parser()
    type_pool: dict[str, Expr] = {}
    def_pool: dict[str, Expr] = {}
    while True:
        code = input(">> ")
        if code == ".exit":
            print("Existing...")
            break
        expr = parser.parse(code)
        if isinstance(expr, str):
            # error
            print(expr)
        elif isinstance(expr, EqDef):
            # 展开定义 
            try:
                definition, definition_type = calc(expr_todef(expr.expr, def_pool), [], type_pool, None, None)
            except Exception as e:
                print(e)
            def_pool[expr.name] = definition
            type_pool[expr.name] = definition_type
            print(expr.name, "=", print_expr_by_name(definition))
        elif isinstance(expr, TypeDef):
            type_pool[expr.name] = expr.type
            print(expr.name, ":", print_expr_by_name(expr.type))
        else:
            try: 
                expr, expr_type = calc(expr, [], type_pool, def_pool, None)
                print(print_expr_by_name(expr_type))
            except Exception as e:
                print(e)

if __name__ == "__main__":
    main()
        
