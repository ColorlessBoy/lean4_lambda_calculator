import pytest
from lean4_lambda_calculator.calculator import calc, get_level
from lean4_lambda_calculator.expr import Const, Lambda, Forall, App, Sort, BoundVar

@pytest.fixture
def type_pool():
    return {
        "Prop": Sort(1),
        "Nat": Sort(0),
        "String": Sort(0),
        "Decidable": Forall(Sort(0), Sort(1)),
    }

def test_calc_const(type_pool):
    expr = Const("Nat")
    result_expr, result_type = calc(expr, [], type_pool)
    assert result_expr == expr
    assert result_type == Sort(0)

def test_calc_lambda(type_pool):
    expr = Lambda(Const("Nat"), BoundVar(0))
    result_expr, result_type = calc(expr, [], type_pool)
    assert isinstance(result_expr, Lambda)
    assert isinstance(result_type, Forall)

def test_calc_app(type_pool):
    func = Lambda(Const("Nat"), BoundVar(0))
    arg = Const("Nat")
    expr = App(func, arg)
    result_expr, result_type = calc(expr, [], type_pool)
    assert isinstance(result_expr, App)
    assert result_type == Const("Nat")

def test_get_level(type_pool):
    expr = Sort(0)
    level = get_level(expr, [], type_pool)
    assert level.value == 0
