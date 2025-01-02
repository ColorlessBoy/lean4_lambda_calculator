
from lean4_lambda_calculator.expr import print_expr_by_name, Expr, print_expr_by_index
from lean4_lambda_calculator.calculator import calc, expr_todef, proof_step
from lean4_lambda_calculator.parser import Parser, EqDef, TypeDef, ThmDef

def main():
    parser = Parser()
    type_pool: dict[str, Expr] = {}
    def_pool: dict[str, Expr] = {}
    is_in_proof = False
    goals: list[Expr] = []
    while True:
        code = input(">> " if not is_in_proof else "[Proof] >> ")
        if code == ".exit":
            print("Existing...")
            break
        if code == ".giveup":
            is_in_proof = False
            continue
        expr = parser.parse(code)
        if isinstance(expr, str):
            # error
            print(expr)
            continue
        if is_in_proof:
            if isinstance(expr, Expr):
                try:
                    expr, expr_type = calc(expr, [], type_pool, def_pool, None)
                    print("[Proof]", print_expr_by_index(expr_type))
                    next_goals = proof_step(expr_type, goals[0])
                    goals = next_goals + goals[1:]
                    if len(goals) == 0:
                        print("[Proof] Q.E.D.")
                        is_in_proof = False
                    else:
                        for goal in goals:
                            print("[Proof] [Goal]", print_expr_by_name(goal))
                except Exception as e:
                    print(e)
                continue
            else:
                is_in_proof = False
        if isinstance(expr, EqDef):
            # 展开定义 
            try:
                definition, definition_type = calc(expr_todef(expr.expr, def_pool), [], type_pool, None, None)
            except Exception as e:
                print(e)
            def_pool[expr.name] = definition
            type_pool[expr.name] = definition_type
            print(expr.name, "=", print_expr_by_index(definition))
        elif isinstance(expr, TypeDef):
            type_pool[expr.name] = expr.type
            print(expr.name, ":", print_expr_by_index(expr.type))
        elif isinstance(expr, ThmDef):
            # 证明
            is_in_proof = True
            type_pool[expr.name] = expr.type
            goals = [expr.type]
            print("[Proof] [Goal]", print_expr_by_index(expr.type))
        else:
            try: 
                expr, expr_type = calc(expr, [], type_pool, def_pool, None)
                print(print_expr_by_index(expr_type))
            except Exception as e:
                print(e)

if __name__ == "__main__":
    main()
        
