import subprocess
import argparse
from lean4_lambda_calculator.expr import (
    get_all_consts,
    expr_rename_args,
    print_expr_by_name,
)
from lean4_lambda_calculator.parser import Parser, EqDef, TypeDef, ThmDef
import os
import re


def execute(cmd: str | list[str]) -> tuple[str, str]:
    """Execute the shell command ``cmd`` and optionally return its output.

    Args:
        cmd (Union[str, List[str]]): The shell command to execute.
        capture_output (bool, optional): Whether to capture and return the output. Defaults to False.

    Returns:
        Optional[Tuple[str, str]]: The command's output, including stdout and stderr (None if ``capture_output == False``).
    """
    res = subprocess.run(cmd, shell=True, capture_output=True, check=False)
    try:
        output = res.stdout.decode("utf-8")
    except UnicodeDecodeError:
        output = res.stdout.decode("utf-8", errors="replace")
    try:
        error = res.stderr.decode("utf-8")
    except UnicodeDecodeError:
        error = res.stderr.decode("utf-8", errors="replace")
    return output.strip(), error.strip()


def query_const(name: str) -> tuple[str, str]:
    if name == "Prop":
        return "def Prop := Sort(0)", ""
    elif name.isdigit():
        return f"def {name} : Nat", ""
    elif name == "proof_irrel":
        return "def proof_irrel : (a : Prop) -> (x : a) -> (y : a) -> Eq a x y", ""
    elif name == "HEq.of_eq":
        return """thm HEq.of_eq : (a : Sort(u)) -> (x : a) -> (y : a) -> Eq a x y -> HEq a x a y
  (a : Sort(u)) => (x : a) => Eq.rec a x ((z:a)=>Eq a x z=>HEq a x a z) (HEq.refl a x)""", ""
    elif name == "proof_irrel_heq_1":
        return """thm proof_irrel_heq_1 : (a : Prop) -> (x : a) -> (y : a) -> HEq a x a y
  (a : Prop) => (x : a) => (y : a) => HEq.of_eq a x y (proof_irrel a x y)""", ""
    elif name == "proof_irrel_heq":
        return """thm proof_irrel_heq : (a : Prop) -> (b : Prop) -> (c : a) -> (d : b) -> HEq a c b d
  (a : Prop) => (b : Prop) => (c : a) => (d : b) => Eq.casesOn Prop a ((e : Prop) => (f : Eq Prop a e) => (Eq Prop b e -> HEq (Eq Prop a b) (propext a b (iff_of_true a b c d)) (Eq Prop a e) f -> HEq a c b d)) b (propext a b (iff_of_true a b c d)) ((f : Eq Prop b a) => Eq.casesOn Prop a ((h:Prop)=>Eq Prop a h=>((i:h)->HEq (Eq Prop a h) (propext a h (iff_of_true a h c i)) (Eq Prop a a) (Eq.refl Prop a) -> HEq a c h i)) b (Eq.symm Prop b a f) ((i : a) => HEq (Eq Prop a a) (propext a a (iff_of_true a a c i)) (Eq Prop a a) (Eq.refl Prop a) => proof_irrel_heq_1 a c i) d) (Eq.refl Prop b) (HEq.refl (Eq Prop a b) (propext a b (iff_of_true a b c d)))""", ""
    elif name == "ite":
        return "def ite : (s0 : Sort(u)) -> (a : Prop) -> (b : Decidable a) -> (c : s0) -> (d : s0) -> s0", ""
    elif name == "if_pos":
        return "def if_pos : (a : Prop) -> (b : Decidable a) -> (c : a) -> (s0 : Sort(u)) -> (d : s0) -> (e : s0) -> Eq s0 (ite s0 a b d e) d", ""
    elif name == "if_neg":
        return "def if_neg : (a : Prop) -> (b : Decidable a) -> Not a -> (s0 : Sort(u)) -> (c : s0) -> (d : s0) -> Eq s0 (ite s0 a b c d) d", ""
    cmd = f'lake env lean --run lean4_lambda_calculator/QueryConst.lean "{name}"'
    return execute(cmd)


class QueryPool:
    def __init__(self, query_file:str):
        self.query_file = query_file
        self.parser = Parser()
        self.query_pool: set[str] = set()
        self.load()

    def load(self):
        if os.path.exists(self.query_file):
            with open(self.query_file, "r") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("def ") or line.startswith("thm "):
                        name = line.split(" ")[1]
                        self.query_pool.add(name)

    def save(self, code: str):
        with open(self.query_file, "a") as f:
            f.write(code + "\n")

    def query(self, name: str):
        if name in self.query_pool:
            return
        codes, error = query_const(name)
        if len(error) > 0:
            print("failed", name, error)
            return
        codes = codes.strip()
        if len(codes) == 0:
            print("failed", name)
            return
        output = []
        for code in codes.split("\n"):
            try :
                expr = self.parser.parse(code)
            except Exception:
                print(name, "parse failed", code)
                return
            if isinstance(expr, str):
                continue
            elif isinstance(expr, ThmDef):
                expr_rename_args(expr.type)
                consts = get_all_consts(expr.type)
                if "Proj" in codes:
                    output.append(
                        "def " + expr.name + " : " + print_expr_by_name(expr.type)
                    )
                else:
                    output.append(
                        "thm " + expr.name + " : " + print_expr_by_name(expr.type)
                    )
            elif isinstance(expr, TypeDef):
                expr_rename_args(expr.type)
                consts = get_all_consts(expr.type)
                output.append(
                    "def " + expr.name + " : " + print_expr_by_name(expr.type)
                )
            elif isinstance(expr, EqDef):
                expr_rename_args(expr.expr)
                consts = get_all_consts(expr.expr)
                output.append(
                    "def " + expr.name + " := " + print_expr_by_name(expr.expr)
                )
            elif "Proj" not in code:
                expr_rename_args(expr)
                consts = get_all_consts(expr)
                output.append("  " + print_expr_by_name(expr))
            for const in consts:
                self.query(const)

        if name not in self.query_pool:
            self.save("\n".join(output))
            self.query_pool.add(name)


def extract_theorem_list(filepath: str):
    namespaces_pattern = re.compile(r"^\s*namespace\s+([\w.']+)", re.MULTILINE)  # 匹配 open 命令
    theorem_pattern = re.compile(r"^\s*(theorem|lemma)\s+([\w.']+)", re.MULTILINE)
    namespace = None
    names = []
    in_comment = False
    with open(filepath, "r") as f:
        for line in f.readlines():
            line = line.strip()
            if line.startswith('--'):
                continue
            if line.startswith('/-'):
                in_comment = True
            if in_comment:
                if line.endswith('-/'):
                    in_comment = False
                continue
            # 处理 open 命令
            namespace_match = namespaces_pattern.match(line)
            if namespace_match:
                namespace = namespace_match.group(1)
                continue
            thms = theorem_pattern.findall(line)
            if namespace is not None:
                names.extend([namespace + "." + thm for _, thm in thms])
            else:
                names.extend([thm for _, thm in thms])
    return names

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Lean4 Query Consts")
    parser.add_argument("--output", type=str, default="./query_file.txt", help="Path of output file")
    # parser.add_argument("--input", type=str, default="/Users/penglingwei/.elan/toolchains/leanprover--lean4---v4.14.0-rc2/src/lean/Init/PropLemmas.lean", help="Path of input file")
    parser.add_argument("--input", type=str, default="/Users/penglingwei/.elan/toolchains/leanprover--lean4---v4.14.0-rc2/src/lean/Init/SimpLemmas.lean", help="Path of input file")
    args = parser.parse_args()

    query_pool = QueryPool(args.output)
    filepath = args.input
    names = extract_theorem_list(filepath)
    for name in names:
        query_pool.query(name)

