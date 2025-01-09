import subprocess
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
        return "def Prop = Sort(0)", ""
    if name.isdigit():
        return f"def {name} : Nat", ""
    cmd = f'lake env lean --run lean4_lambda_calculator/QueryConst.lean "{name}"'
    return execute(cmd)


class QueryPool:
    def __init__(self):
        self.query_file = "./query_file.txt"
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
                    "def " + expr.name + " = " + print_expr_by_name(expr.expr)
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
    name = "of_eq_true"
    query_pool = QueryPool()
    filepath = "/Users/penglingwei/.elan/toolchains/leanprover--lean4---v4.14.0-rc2/src/lean/Init/PropLemmas.lean"
    names = extract_theorem_list(filepath)
    for name in names:
        query_pool.query(name)

