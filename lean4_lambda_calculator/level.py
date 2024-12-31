from sympy import symbols, Eq, solve, Max, Expr as SymExpr, simplify
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
            return simplify(self.symbol - other.symbol) == 0
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

# 测试代码
if __name__ == "__main__":
    # 基本层级
    l1 = Level(3)
    l2 = SuccLevel(Level("n1"))

    print(f"l1: {l1}")  # 输出: 3
    print(f"l2: {l2}")  # 输出: n1 + 1

    # 创建一个方程 l2 == l1，即 n2 + 1 = 3
    equation = Eq(l2.symbol, l1.symbol)
    print(f"Equation: {equation}")  # 输出: Eq(n2 + 1, 3)

    # 求解 n2 
    solution: List = solve(equation)
    print(f"Solution: {solution}")  # 输出: [2]

    # 提取表达式中的变量名
    print(f"Variables in l2: {l2.get_variables()}")  # 输出: {'n2'}

    # 验证求解结果
    if solution:
        custom_var1_value = solution[0]
        print(f"n1 = {custom_var1_value}")  # 输出: n1 = 2

    l3 = Level(custom_var1_value + 1)
    print(f"l3: {l3}")  # 输出: 3
    print(l3 == l1)     # 输出: True

    # 测试 MaxLevel
    l4 = MaxLevel(Level(2), SuccLevel(Level("n2")))
    print(f"l4: {l4}")  # 输出: Max(2, n2 + 1)
    print(f"Variables in l4: {l4.get_variables()}")  # 输出: {'n2'}

    u1 = SuccLevel(Level('u_1'))
    u2 = SuccLevel(Level('u_2'))
    print(u1.match(u2))

    # 测试 MaxLevel
    l5 = MaxLevel(Level(0), SuccLevel(Level("n2")))
    print("l5:", l5)