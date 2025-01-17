from sympy import symbols, Eq, solve, Max, simplify, satisfiable, sympify, Piecewise, Integer, Expr as SymExpr
import re


class Level:
    def __init__(self, level: str | int | SymExpr) -> None:
        if isinstance(level, str):
            try:
                int_level = int(level)  # 尝试将level转换为整数
                assert int_level >= 0, f"Invalid level {level}, which is small than 0."
                self.symbol = Integer(int_level)
            except ValueError:
                # 如果转换失败，说明level不是有效的整数
                self.symbol = symbols(level, integer=True, nonnegative=True)
        elif isinstance(level, int):
            assert level >= 0, f"Invalid level number {level}, which is small than 0."
            self.symbol = Integer(level)  # 将输入简化为 sympy 表达式
        elif isinstance(level, SymExpr):
            self.symbol = level
        else:
            raise TypeError("input arg level should be str, int")

    def __repr__(self) -> str:
        return str(self.symbol)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Level):
            # 构造方程 self.symbol == other.symbol
            equation = Eq(self.symbol, other.symbol)
            rst = satisfiable(equation)
            return bool(rst)
        return False

    def get_variables(self) -> set[str]:
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

LevelType = str | int | Level

class SuccLevel(Level):
    def __init__(self, level: LevelType) -> None:
        self.origin_level = level if isinstance(level, Level) else Level(level)
        self.symbol = simplify(self.origin_level.symbol + 1)

    def __repr__(self) -> str:
        super_str = super().__repr__()
        if "Piecewise" in super_str:
            return f"{self.origin_level}+1"
        return super_str

class MaxLevel(Level):
    def __init__(self, left: LevelType, right: LevelType) -> None:
        self.left = left if isinstance(left, Level) else Level(left)
        self.right = right if isinstance(right, Level) else Level(right) 
        self.symbol = simplify(Max(self.left.symbol, self.right.symbol))
    
    def __repr__(self) -> str:
        super_str = super().__repr__()
        if "Piecewise" in super_str:
            return f"Max({self.left},{self.right})"
        return super_str

class IMaxLevel(Level):
    def __init__(self, left: Level, right: Level) -> None:
        self.left = left if isinstance(left, Level) else Level(left)
        self.right = right if isinstance(right, Level) else Level(right) 
        self.symbol = simplify(Piecewise(
            (0, Eq(self.right.symbol, 0)), # 如果 b = 0, 则返回 0
            (Max(self.left.symbol, self.right.symbol), True),  # 如果 b ≠ 0，返回 max(succ(a), b)
        ))
    
    def __repr__(self) -> str:
        super_str = super().__repr__()
        if "Piecewise" in super_str:
            return f"IMax({self.left},{self.right})"
        return super_str

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

def is_solvable(equations_str: list[str]) -> bool:
    """
    检查一个字符串列表形式的方程组是否有解。

    参数:
        equations_str (list[str]): 方程组的字符串列表，例如 ["x + y = 10", "y - z = 2"]。
    
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
        if "=" in eq_str:
            rep_eq_str = eq_str.replace("=", "-(") + ")"
        else:
            rep_eq_str = eq_str
        parsed_eq = sympify(rep_eq_str)  # 转换为表达式格式
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

def parse_level(code: str) -> Level:
    tokens = _tokenize(code)
    return _parse_level(tokens)

def _parse_level(tokens: list[str]) -> Level:
    """解析 Level 对象"""
    token = tokens.pop(0)
    if token.isdigit():
        return Level(int(token))
    elif token == "Max":
        assert tokens[0] == '(', "Max does not followed by `(`"
        tokens.pop(0)
        left = _parse_level(tokens)
        assert tokens[0] == ',', "need a comma `,`"
        tokens.pop(0)
        right = _parse_level(tokens)
        assert tokens[0] == ')', "Max does not ended with `)`"
        tokens.pop(0)
        return MaxLevel(left, right)
    elif token == "IMax":
        assert tokens[0] == '(', "Max does not followed by `(`"
        tokens.pop(0)
        left = _parse_level(tokens)
        assert tokens[0] == ',', "need a comma `,`"
        tokens.pop(0)
        right = _parse_level(tokens)
        assert tokens[0] == ')', "Max does not ended with `)`"
        tokens.pop(0)
        return IMaxLevel(left, right)
    else:
        if len(tokens) >= 2 and tokens[0] == "+" and tokens[1] == "1":
            tokens.pop(0)
            tokens.pop(0)
            return SuccLevel(Level(token))
        else:
            return Level(token)

def _tokenize(expr: str) -> list[str]:
    """将输入字符串拆分为标记列表"""
    # 使用正则表达式匹配括号、标识符和数字
    pattern = r"[()+]|[A-Za-z0-9_.\u00A0-\uFFFF]+|\S"
    tokens = re.findall(pattern, expr)
    return tokens