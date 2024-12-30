import pytest
from lean4_lambda_calculator.expr import Const, Sort, BoundVar, Arg, Forall, Lambda, App, print_expr_by_name, print_expr_by_index, rename_expr
from lean4_lambda_calculator.level import Level

def test_sort():
    expr = Sort(0)
    assert expr.level.value == 0
    assert expr.predicate == 100
    assert repr(expr) == "S(0)"

def test_const():
    expr = Const("Nat")
    assert expr.label == "Nat"
    assert expr.predicate == 100
    assert repr(expr) == "Nat"

def test_bound_var():
    expr = BoundVar(1)
    assert expr.index == 1
    assert expr.predicate == 100
    assert repr(expr) == "#1"

def test_arg():
    expr = Arg(Const("Nat"), None)
    assert expr.type == Const("Nat")
    assert expr.name is None
    assert expr.predicate == 100
    assert repr(expr) == "Nat"

def test_forall():
    expr = Forall(Const("Nat"), BoundVar(0))
    assert isinstance(expr.var_type, Arg)
    assert expr.body == BoundVar(0)
    assert expr.predicate == 1
    assert repr(expr) == "Nat -> #0"

def test_lambda():
    expr = Lambda(Const("Nat"), BoundVar(0))
    assert isinstance(expr.var_type, Arg)
    assert expr.body == BoundVar(0)
    assert expr.predicate == 2
    assert repr(expr) == "Nat => #0"

def test_app():
    func = Lambda(Const("Nat"), BoundVar(0))
    arg = Const("Nat")
    expr = App(func, arg)
    assert expr.func == func
    assert expr.arg == arg
    assert expr.predicate == 3
    assert repr(expr) == "(Nat => #0) Nat"

def test_print_expr_by_name():
    expr = Forall(Const("Prop"), Forall(Const("Prop"), App(Const("Iff"), BoundVar(1))))
    result = print_expr_by_name(expr)
    assert result == "Prop -> Prop -> Iff #1"

def test_print_expr_by_index():
    expr = Forall(Const("Prop"), Forall(Const("Prop"), App(Const("Iff"), BoundVar(1))))
    result = print_expr_by_index(expr)
    assert result == "Prop -> Prop -> Iff #1"

def test_rename_expr():
    expr = Forall(Const("Prop"), Forall(Const("Prop"), App(Const("Iff"), BoundVar(1))))
    rename_expr(expr)
    result = print_expr_by_name(expr)
    assert result == "(a : Prop) -> (b : Prop) -> Iff b"

def test_sort_with_level():
    level = Level(1)
    expr = Sort(level)
    assert expr.level == level
    assert expr.predicate == 100
    assert repr(expr) == "S(1)"

def test_nested_lambda():
    expr = Lambda(Const("Nat"), Lambda(Const("Nat"), BoundVar(1)))
    assert isinstance(expr.var_type, Arg)
    assert expr.body.var_type == Arg(Const("Nat"), None)
    assert expr.body.body == BoundVar(1)
    assert repr(expr) == "Nat => Nat => #1"

def test_nested_forall():
    expr = Forall(Const("Nat"), Forall(Const("Nat"), BoundVar(1)))
    assert isinstance(expr.var_type, Arg)
    assert expr.body.var_type == Arg(Const("Nat"), None)
    assert expr.body.body == BoundVar(1)
    assert repr(expr) == "Nat -> Nat -> #1"

if __name__ == "__main__":
    pytest.main()