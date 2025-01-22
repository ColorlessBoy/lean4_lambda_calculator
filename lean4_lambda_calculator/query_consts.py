import subprocess
import argparse
import re
from tqdm import tqdm


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
    cmd = f'lake env lean --run lean4_lambda_calculator/QueryConst.lean "{name}"'
    return execute(cmd)

def query_deps(name: str) -> tuple[list[str], str]:
    cmd = f'lake env lean --run lean4_lambda_calculator/QueryDeps.lean "{name}"'
    code, error = execute(cmd)
    deps = [name for name in code.split('\t') if len(name) > 0]
    return deps, error

class QueryPool:
    def __init__(self, query_file:str):
        self.cache: dict[str, str] = {"Prop" : ""}

    def query(self, name: str) -> str:
        if name in self.cache.keys():
            return self.cache[name]
        code, error = query_const(name)
        if len(error) > 0:
            print("query_const() failed", name, error)
            return ""
        self.cache[name] = code
        return code

def extract_theorem_list(filepath: str) -> list[str]:
    namespaces_pattern = re.compile(r"^\s*namespace\s+([\w.']+)", re.MULTILINE)  # 匹配 open 命令
    theorem_pattern = re.compile(r"^\s*(theorem|lemma|def)\s+([\w.']+)", re.MULTILINE)
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

def dfs_deps(name: str, deps: list[str], visited: set[str], axioms: set[str], noncomputable: set[str]):
    # 深度优先搜索优化
    if name in visited:
        return
    visited.add(name)

    tmp_deps, error = query_deps(name)
    if len(error) > 0:
        print(f"query_deps() failed for {name}: {error}")
    else:
        t = tmp_deps[0] 
        if t == "axiom":
            axioms.add(name)
        for tmp_name in tmp_deps[1:]:
            dfs_deps(tmp_name, deps, visited, axioms, noncomputable)
            if tmp_name in axioms:
                noncomputable.add(name) # uncomputable deps 
        deps.append(name)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Lean4 Query Consts")
    parser.add_argument("--output", type=str, default="./query_const.lean", help="Path of output file")
    # parser.add_argument("--input", type=str, default="/Users/penglingwei/.elan/toolchains/leanprover--lean4---v4.14.0-rc2/src/lean/Init/PropLemmas.lean", help="Path of input file")
    parser.add_argument("--input", type=str, default="/Users/penglingwei/.elan/toolchains/leanprover--lean4---v4.14.0-rc2/src/lean/Init/SimpLemmas.lean", help="Path of input file")
    args = parser.parse_args()

    query_pool = QueryPool(args.output)
    filepath = args.input
    names = extract_theorem_list(filepath)
    deps: list[str] = []
    visited = set()
    axioms = set()
    noncomputable = set()
    for name in tqdm(names):
        dfs_deps(name, deps, visited, axioms, noncomputable)
    for name in tqdm(deps):
        code = query_pool.query(name)
        with open(args.output, '+a') as f:
            f.write(code + '\n')

