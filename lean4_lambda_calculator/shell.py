import os
from lean4_lambda_calculator.expr import print_expr_by_name, Expr, print_expr_by_index
from lean4_lambda_calculator.calculator import calc, expr_todef, proof_step
from lean4_lambda_calculator.parser import Parser, EqDef, TypeDef, ThmDef

class Shell:
    def __init__(self):
        self.parser = Parser()
        self.type_pool: dict[str, Expr] = {}
        self.def_pool: dict[str, Expr] = {}
        self.is_in_proof = False
        self.goals: list[Expr] = []
        self.history_file = "./history.txt"
        self.load_history()

    def load_history(self):
        if os.path.exists(self.history_file):
            with open(self.history_file, "r") as f:
                for line in f:
                    self.execute(line.strip())

    def save_history(self, code: str):
        with open(self.history_file, "a") as f:
            f.write(code + "\n")

    def execute(self, code: str):
        if code == ".giveup":
            self.is_in_proof = False
            return True
        expr = self.parser.parse(code)
        if isinstance(expr, str):
            # error
            print(expr)
            return False
        if self.is_in_proof:
            if isinstance(expr, Expr):
                try:
                    expr, expr_type = calc(expr, [], self.type_pool, self.def_pool, None)
                    print("[Proof]", print_expr_by_index(expr_type))
                    next_goals = proof_step(expr_type, self.goals[0])
                    self.goals = next_goals + self.goals[1:]
                    if len(self.goals) == 0:
                        print("[Proof] Q.E.D.")
                        self.is_in_proof = False
                    else:
                        for goal in self.goals:
                            print("[Proof] [Goal]", print_expr_by_name(goal))
                    return True
                except Exception as e:
                    print(e)
                    return False
            else:
                self.is_in_proof = False
        if isinstance(expr, EqDef):
            # 展开定义 
            try:
                definition, definition_type = calc(expr_todef(expr.expr, self.def_pool), [], self.type_pool, None, None)
                self.def_pool[expr.name] = definition
                self.type_pool[expr.name] = definition_type
                print(expr.name, ":", print_expr_by_index(definition_type), "=", print_expr_by_index(definition))
            except Exception as e:
                print(e)
                return False
        elif isinstance(expr, TypeDef):
            self.type_pool[expr.name] = expr.type
            print(expr.name, ":", print_expr_by_index(expr.type))
        elif isinstance(expr, ThmDef):
            # 证明
            self.is_in_proof = True
            self.type_pool[expr.name] = expr.type
            self.goals = [expr.type]
            print(expr.name, ":", print_expr_by_index(expr.type))
            print("[Proof] [Goal]", print_expr_by_index(expr.type))
        else:
            try: 
                expr, expr_type = calc(expr, [], self.type_pool, self.def_pool, None)
                print(print_expr_by_index(expr_type))
            except Exception as e:
                print(e)
                return False
        return True

    def run(self):
        while True:
            code = input(">> " if not self.is_in_proof else "[Proof] >> ")
            if code == ".exit":
                print("Exiting...")
                break
            if self.execute(code):
                self.save_history(code)

if __name__ == "__main__":
    shell = Shell()
    shell.run()

