import os
from lean4_lambda_calculator.expr import print_expr_by_name, Expr, expr_clean_all_names 
from lean4_lambda_calculator.calculator import calc, expr_todef, proof_step
from lean4_lambda_calculator.parser import Parser, EqDef, TypeDef, ThmDef
from colorama import Fore, Style, init
from prompt_toolkit import prompt
from prompt_toolkit.shortcuts import CompleteStyle
from prompt_toolkit.completion import WordCompleter
from prompt_toolkit.history import FileHistory

init(autoreset=True)

class Shell:
    def __init__(self):
        self.parser = Parser()
        self.type_pool: dict[str, Expr] = {}
        self.def_pool: dict[str, Expr] = {}
        self.is_in_proof = False
        self.goals: list[Expr] = []
        self.history_file = "./history.txt"
        self.load_history()
        self.history = FileHistory("./prompt_history.txt")

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
                    print(Fore.GREEN + "[Proof]" + Style.RESET_ALL, print_expr_by_name(expr_type))
                    next_goals = proof_step(expr_type, self.goals[0], type_pool=self.type_pool, def_pool=self.def_pool)
                    if next_goals is not None:
                        self.goals = next_goals + self.goals[1:]
                    if len(self.goals) == 0:
                        print(Fore.GREEN + "[Proof] Q.E.D." + Style.RESET_ALL)
                        self.is_in_proof = False
                    else:
                        for goal in self.goals:
                            print(Fore.GREEN + "[Proof] [Goal]" + Style.RESET_ALL, print_expr_by_name(goal))
                    return True if next_goals is not None else False
                except Exception as e:
                    print(Fore.RED + str(e) + Style.RESET_ALL)
                    return False
            else:
                self.is_in_proof = False
        if isinstance(expr, EqDef):
            # 展开定义 
            try:
                definition, _ = calc(expr_todef(expr.expr, self.def_pool), [], self.type_pool, self.def_pool, None, type_no_check=True)
                self.def_pool[expr.name] = expr_clean_all_names(definition)
                _, expr_type = calc(expr.expr, [], self.type_pool, self.def_pool, None)
                self.type_pool[expr.name] = expr_clean_all_names(expr_type)
                print(Fore.CYAN + expr.name, ":" + Style.RESET_ALL, print_expr_by_name(expr_type), Fore.CYAN + "=" + Style.RESET_ALL, print_expr_by_name(expr.expr))
            except Exception as e:
                print(e)
                return False
        elif isinstance(expr, TypeDef):
            self.type_pool[expr.name] = expr_clean_all_names(expr.type)
            print(Fore.CYAN + expr.name, ":" + Style.RESET_ALL, print_expr_by_name(expr.type))
        elif isinstance(expr, ThmDef):
            # 证明
            self.is_in_proof = True
            self.type_pool[expr.name] = expr_clean_all_names(expr.type)
            self.goals = [expr.type]
            print(Fore.CYAN + expr.name, ":" + Style.RESET_ALL, print_expr_by_name(expr.type))
            print(Fore.GREEN + "[Proof] [Goal]" + Style.RESET_ALL, print_expr_by_name(expr.type))
        else:
            try: 
                expr, expr_type = calc(expr, [], self.type_pool, self.def_pool, None)
                print(print_expr_by_name(expr_type))
            except Exception as e:
                print(e)
                return False
        return True
    
    def get_default_input(self):
        if not self.is_in_proof:
            return ""
        
        goal = print_expr_by_name(self.goals[0])
        parts = []
        depth = 0
        current = []

        for char in goal:
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            
            if depth == 0 and char == '>' and current[-1] == '-':  # Top-level "->"
                parts.append("".join(current[:-1]).strip())
                current = []
            else:
                current.append(char)
        
        if current:
            parts.append("".join(current).strip())

        # Join the parts with "=>", excluding the final result
        if len(parts) <= 1 :
            return ""
        return " => ".join(parts[:-1]) + " => "

    def run(self):
        try:
            while True:
                completer = WordCompleter(['def', 'thm', '->', '=>', '.giveup', '.exit'] + list(self.type_pool.keys()))
                # 提示用户输入
                code = prompt(
                    ">> " if not self.is_in_proof else "[Proof] >> ", 
                    default=self.get_default_input(),           # 默认值，显示在输入框中
                    completer=completer,             # 自动补全（可选）
                    complete_style=CompleteStyle.READLINE_LIKE,  # 补全风格
                )
                # code = input(">> " if not self.is_in_proof else "[Proof] >> ")
                if code == ".exit":
                    print("Exiting...")
                    break
                prefix = "  " if self.is_in_proof else ""
                if self.execute(code):
                    self.save_history(prefix + code)
        except (KeyboardInterrupt, EOFError):
            print("Exiting...")

if __name__ == "__main__":
    shell = Shell()
    shell.run()

