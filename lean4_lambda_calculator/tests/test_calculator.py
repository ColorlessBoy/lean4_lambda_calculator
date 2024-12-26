import unittest
from calculator import calc, get_level
from expr import Const, Lambda, Forall, App, Sort, BoundVar

class TestCalculator(unittest.TestCase):

    def setUp(self):
        self.type_pool = {
            "Prop": Sort(1),
            "Nat": Sort(0),
            "String": Sort(0),
            "Decidable": Forall(Sort(0), Sort(1)),
        }

    def test_calc_const(self):
        expr = Const("Nat")
        result_expr, result_type = calc(expr, [], self.type_pool)
        self.assertEqual(result_expr, expr)
        self.assertEqual(result_type, Sort(0))

    def test_calc_lambda(self):
        expr = Lambda(Const("Nat"), BoundVar(0))
        result_expr, result_type = calc(expr, [], self.type_pool)
        self.assertIsInstance(result_expr, Lambda)
        self.assertIsInstance(result_type, Forall)

    def test_calc_app(self):
        func = Lambda(Const("Nat"), BoundVar(0))
        arg = Const("Nat")
        expr = App(func, arg)
        result_expr, result_type = calc(expr, [], self.type_pool)
        self.assertIsInstance(result_expr, App)
        self.assertEqual(result_type, Const("Nat"))

    def test_get_level(self):
        expr = Sort(0)
        level = get_level(expr, [], self.type_pool)
        self.assertEqual(level.value, 0)

if __name__ == "__main__":
    unittest.main()
