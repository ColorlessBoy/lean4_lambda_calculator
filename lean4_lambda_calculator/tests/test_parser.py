import unittest
from parser import tokenize, parse_expr, get_const
from expr import Const, App, Lambda, Forall, Sort, Proj, NatLiteral, StrLiteral

class TestParser(unittest.TestCase):

    def test_tokenize(self):
        self.assertEqual(tokenize("(A (C f) (C x))"), ["(", "A", "(", "C", "f", ")", "(", "C", "x", ")", ")"])
        self.assertEqual(tokenize("(L (S u+1) (F #0 (S 0)))"), ["(", "L", "(", "S", "u+1", ")", "(", "F", "#0", "(", "S", "0", ")", ")", ")"])
        self.assertEqual(tokenize("(P typename 1 (C tuple))"), ["(", "P", "typename", "1", "(", "C", "tuple", ")", ")"])
        self.assertEqual(tokenize("(NL 42)"), ["(", "NL", "42", ")"])
        self.assertEqual(tokenize('(SL "string")'), ["(", "SL", '"string"', ")"])

    def test_parse_expr(self):
        expr = parse_expr("(C f)")
        self.assertIsInstance(expr, Const)
        self.assertEqual(expr.label, "f")

        expr = parse_expr("(A (C f) (C x))")
        self.assertIsInstance(expr, App)
        self.assertIsInstance(expr.func, Const)
        self.assertEqual(expr.func.label, "f")
        self.assertIsInstance(expr.arg, Const)
        self.assertEqual(expr.arg.label, "x")

        expr = parse_expr("(L (S u+1) (F #0 (S 0)))")
        self.assertIsInstance(expr, Lambda)
        self.assertIsInstance(expr.var_type, Sort)
        self.assertIsInstance(expr.body, Forall)

        expr = parse_expr("(P typename 1 (C tuple))")
        self.assertIsInstance(expr, Proj)
        self.assertEqual(expr.typename, "typename")
        self.assertEqual(expr.index, 1)
        self.assertIsInstance(expr.tuple_expr, Const)
        self.assertEqual(expr.tuple_expr.label, "tuple")

        expr = parse_expr("(NL 42)")
        self.assertIsInstance(expr, NatLiteral)
        self.assertEqual(expr.var, 42)

        expr = parse_expr('(SL "string")')
        self.assertIsInstance(expr, StrLiteral)
        self.assertEqual(expr.var, "string")

    def test_get_const(self):
        expr = parse_expr("(C f)")
        self.assertEqual(get_const(expr), ["f"])

        expr = parse_expr("(A (C f) (C x))")
        self.assertEqual(get_const(expr), ["f", "x"])

        expr = parse_expr("(L (S u+1) (F #0 (S 0)))")
        self.assertEqual(get_const(expr), [])

        expr = parse_expr("(P typename 1 (C tuple))")
        self.assertEqual(get_const(expr), ["tuple"])

        expr = parse_expr("(NL 42)")
        self.assertEqual(get_const(expr), ["Nat"])

        expr = parse_expr('(SL "string")')
        self.assertEqual(get_const(expr), ["String"])

if __name__ == "__main__":
    unittest.main()
