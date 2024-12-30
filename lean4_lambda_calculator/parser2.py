import re

class Tokenizer:
    def __init__(self):
        self.token_spec = [
            ("NUMBER", r"\d+"),  # 数字
            ("IDENTIFIER", r"[A-Za-z0-9_.\u00A0-\uFFFF]+"),  # 可以包括更多 Unicode 字符
            ("SYMBOL", r"[(),:#]|\S"),   # 符号
            ("WHITESPACE", r"\s+"),  # 空白字符
        ]
        self.token_regex = "|".join(f"(?P<{name}>{regex})" for name, regex in self.token_spec)
        self.operator_table:set[str] = set()

    def add_operator(self, symbol:str):
        self.operator_table.add(symbol)
        operator_regex = '|'.join(re.escape(op) for op in self.operator_table)
        token_spec = [("OPERATOR", operator_regex)] + self.token_spec
        self.token_regex = "|".join(f"(?P<{name}>{regex})" for name, regex in token_spec)
    
    def tokenize(self, code):
        tokens = []
        for match in re.finditer(self.token_regex, code):
            kind = match.lastgroup
            value = match.group(kind)
            if kind == "WHITESPACE":
                continue
            tokens.append((kind, value))
        return tokens

def test_tokenizer():
    tokenizer = Tokenizer()
    tokenizer.add_operator("=>")
    tokenizer.add_operator("->")
    code1 = "Sort u -> (#0 -> Prop) -> Prop -> Exists #2 (#2 =>#2 #0) -> (#3 -> #3 #0 -> #3) -> #2"
    tokens1 = tokenizer.tokenize(code1)
    print(tokens1)
    code2 = "(a : Sort u) -> (b : a -> Prop) -> (c : Prop) -> Exists a b -> ((e : a) -> b e -> c) -> c"
    tokens2 = tokenizer.tokenize(code2)
    print(tokens2)
    code3 = "Sort u => #0 -> Prop => #1 -> #1 #0"
    tokens3 = tokenizer.tokenize(code3)
    print(tokens3)
    code4 = "(a:Sort u+1)=>(b:a->Prop)=>(c:a)->b c"
    tokens4 = tokenizer.tokenize(code4)
    print(tokens4)
    
# 解析器类
class Parser:
    def __init__(self):
        self.tokens = []
        self.current = 0
        self.operator_table = {}  # 存储动态运算符的优先级和结合性
        self.macro_table = {}

    def define_infix(self, symbol, precedence, associativity):
        # 动态设置运算符
        self.operator_table[symbol] = {"precedence": precedence, "associativity": associativity}
    
    def define_macro(self, pattern, expansion):
        # 定义宏
        self.macros[pattern] = expansion
    
    def peek(self):
        return self.tokens[self.current] if self.current < len(self.tokens) else None

    def consume(self):
        token = self.peek()
        self.current += 1
        return token
    
    def parse(self):
        return self.parse_expression(0)

    def parse_expression(self, min_precedence):
        left = self.parse_primary()

        while (self.peek() and
               self.peek()[1] in self.operator_table and
               self.operator_table[self.peek()[1]]["precedence"] >= min_precedence):
            op = self.consume()[1]
            precedence = self.operator_table[op]["precedence"]
            associativity = self.operator_table[op]["associativity"]

            next_min_precedence = precedence + (0 if associativity == "left" else 1)
            right = self.parse_expression(next_min_precedence)
            left = {"type": "binary", "operator": op, "left": left, "right": right}

        return left

    def parse_primary(self):
        token = self.consume()
        if token[0] == "NUMBER":
            return {"type": "number", "value": int(token[1])}
        elif token[0] == "IDENTIFIER":
            return {"type": "variable", "name": token[1]}
        elif token[0] == "SYMBOL" and token[1] == "(":
            expr = self.parse()
            if self.peek() and self.peek()[1] == ")":
                self.consume()  # Consume ')'
            return expr
        raise SyntaxError(f"Unexpected token: {token}")


# 宏系统
macros = {}

def define_macro(pattern, expansion):
    macros[pattern] = expansion

def expand_macros(ast):
    if isinstance(ast, dict) and ast["type"] == "binary":
        operator = ast["operator"]
        left = expand_macros(ast["left"])
        right = expand_macros(ast["right"])
        pattern = (operator, left["type"], right["type"])

        if pattern in macros:
            return macros[pattern](left, right)

        return {"type": "binary", "operator": operator, "left": left, "right": right}
    return ast


# 示例：如何定义运算符和宏
def test_parser_and_macros():
    # 定义动态运算符
    parser = Parser([])
    parser.define_infix("+", 10, "left")  # 定义加法运算符，优先级 10，左结合
    parser.define_infix("*", 20, "left")  # 定义乘法运算符，优先级 20，左结合

    # 定义宏
    define_macro(("+", "number", "number"), lambda left, right: {"type": "number", "value": left["value"] + right["value"]})
    define_macro(("*", "number", "number"), lambda left, right: {"type": "number", "value": left["value"] * right["value"]})

    """
    # 输入代码
    code = "1 + 2 * 3 + 4"
    tokens = tokenize(code)
    print("Tokens:", tokens)

    # 解析代码
    parser = Parser(tokens)
    ast = parser.parse()
    print("AST before macro expansion:", ast)

    # 宏展开
    expanded_ast = expand_macros(ast)
    print("AST after macro expansion:", expanded_ast)
    """


if __name__ == "__main__":
    test_tokenizer()