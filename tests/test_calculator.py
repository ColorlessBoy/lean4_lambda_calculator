import pytest
from lean4_lambda_calculator.calculator import calc, get_level
from lean4_lambda_calculator.expr import Const, Lambda, Forall, App, Sort, BoundVar, Level

@pytest.fixture
def type_pool():
    Prop = Const("Prop")
    return {
        "Prop": Sort(1),
        "Iff": Forall(Prop, Forall(Prop, Prop)),
        "Iff.intro": Forall(Prop, Forall( Prop, Forall(Forall(BoundVar(1), BoundVar(1)), Forall(Forall(BoundVar(1), BoundVar(3)), App(App(Const("Iff"), BoundVar(3)), BoundVar(2)))))),
        "Not": Forall(Prop, Prop),
        "Decidable": Forall(Prop, Sort(1)),
    }

def test_calc_const(type_pool):
    expr = Const("Prop")
    result_expr, result_type = calc(expr, [], type_pool)
    assert result_expr == expr
    assert result_type == Sort(1)

def test_calc_lambda(type_pool):
    expr = Lambda(Const("Prop"), BoundVar(0))
    result_expr, result_type = calc(expr, [], type_pool)
    assert result_expr == expr
    assert result_type == Forall(Const("Prop"), Const("Prop"))

def test_calc_app(type_pool):
    expr = Lambda(Const("Prop"), App(Const("Iff"), BoundVar(0)))
    result_expr, result_type = calc(expr, [], type_pool)
    assert result_expr == expr
    assert result_type == Forall(Const("Prop"), Forall(Const("Prop"), Const("Prop")))

def test_get_level(type_pool):
    expr = Lambda(Const("Prop"), App(Const("Iff"), BoundVar(0)))
    level = get_level(expr, [], type_pool, def_pool={})
    assert level == Level(-1)

def test_iff_refl(type_pool):
    Prop = Const("Prop")
    Iff_refl = Forall(Prop, App(App(Const("Iff"), BoundVar(0)), BoundVar(0)))
    Iff_refl_proof = Lambda(
        Prop,
        App(
            App(
                App(App(Const("Iff.intro"), BoundVar(0)), BoundVar(0)),
                Lambda(BoundVar(0), BoundVar(0)),
            ),
            Lambda(BoundVar(0), BoundVar(0)),
        ),
    )
    _, result_type = calc(Iff_refl_proof, [], type_pool)
    assert Iff_refl == result_type
