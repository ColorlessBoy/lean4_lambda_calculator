from sympy import symbols, Eq, solve, Max, Expr as SymExpr, simplify, satisfiable, sympify
from typing import Union, List, Set

# LevelType 可以是整数或 sympy 表达式
LevelType = Union[int, SymExpr]

class Level:
    def __init__(self, level: LevelType | str) -> None:
        if isinstance(level, str):
            self.symbol = symbols(level, integer=True, nonnegative=True)
        else:
            self.symbol: SymExpr = simplify(level)  # 将输入简化为 sympy 表达式

    def __repr__(self) -> str:
        return str(self.symbol)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Level):
            # 构造方程 self.symbol == other.symbol
            equation = Eq(self.symbol, other.symbol)
            rst = satisfiable(equation)
            return bool(rst)
        return False

    def __lt__(self, other: "Level") -> bool:
        return self.symbol < other.symbol

    def __le__(self, other: "Level") -> bool:
        return self.symbol <= other.symbol

    def __add__(self, other: Union[int, SymExpr]) -> "Level":
        return Level(self.symbol + other)

    def get_variables(self) -> Set[str]:
        """获取表达式中的所有变量名字符串"""
        return {str(symbol) for symbol in self.symbol.free_symbols}

    def match(self, level):
        if not isinstance(level, Level):
            return False, None
        if simplify(self.symbol - level.symbol) == 0:
            return True, None
        eq = Eq(self.symbol, level.symbol)
        solution = solve(eq)
        # 如果有解，返回 True 和 solution 
        if solution:
            return True, solution
        return False, None

class SuccLevel(Level):
    def __init__(self, level: Level) -> None:
        super().__init__(level.symbol + 1)


class MaxLevel(Level):
    def __init__(self, left: Level, right: Level) -> None:
        super().__init__(Max(left.symbol, right.symbol))


class PreLevel(Level):
    def __init__(self, level: Level) -> None:
        super().__init__(level.symbol - 1)

def level_subs_symbols(level: Level, used_free_symbols: set[str], renamed_symbols: dict[str, str]) -> Level:
    rst_symbol = level.symbol
    for symbol in rst_symbol.free_symbols:
        s_symbol = str(symbol)
        if s_symbol not in used_free_symbols:
            continue
        if s_symbol in renamed_symbols:
            new_name = renamed_symbols[s_symbol]
        else:
            new_name = _get_new_name(used_free_symbols, set(renamed_symbols.values()))
            renamed_symbols[s_symbol] = new_name
        new_symbol = symbols(new_name, integer=True, nonnegative=True)
        rst_symbol = rst_symbol.subs(symbol, new_symbol)
    return Level(rst_symbol) 

def _get_new_name(used_names: set[str], used_new_names: set[str]) -> str:
    index = 0
    while True:
        name = f"u{index}"
        if name not in used_names:
            return name
        index += 1

def is_solvable(equations_str: List[str]) -> bool:
    """
    检查一个字符串列表形式的方程组是否有解。

    参数:
        equations_str (List[str]): 方程组的字符串列表，例如 ["x + y = 10", "y - z = 2"]。
    
    返回:
        bool: 如果方程组有解，返回 True；否则返回 False。
    """
    if not equations_str:
        return True  # 空方程组默认有解

    # 第一次解析，收集自由符号
    parsed_equations = []
    all_symbols = set()
    
    for eq_str in equations_str:
        # 暂时解析字符串
        parsed_eq = sympify(eq_str.replace("=", "-(") + ")")  # 转换为表达式格式
        parsed_equations.append(parsed_eq)
        all_symbols.update(parsed_eq.free_symbols)

    # 创建统一的符号上下文
    symbol_context = {str(sym): symbols(str(sym)) for sym in all_symbols}

    # 使用统一的符号上下文重新解析方程组
    equations = [
        Eq(sympify(eq_str.split("=")[0], locals=symbol_context), 
           sympify(eq_str.split("=")[1], locals=symbol_context))
        for eq_str in equations_str
    ]

    # 检查是否有解
    logical_expression = Eq(0, 0)
    for eq in equations:
        logical_expression = logical_expression & eq

    return bool(satisfiable(logical_expression))
