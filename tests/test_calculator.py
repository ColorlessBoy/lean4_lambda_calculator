import pytest
from lean4_lambda_calculator.calculator import calc, get_level, proof_step
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
    level = get_level(expr, [], type_pool)
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

def test_proof_step(type_pool):
    Prop = Const("Prop")
    Iff_intro = Const("Iff.intro")
    Iff_refl = Forall(Prop, App(App(Const("Iff"), BoundVar(0)), BoundVar(0)))
    action1 = Lambda(Prop, App(App(Iff_intro, BoundVar(0)), BoundVar(0)))
    _, action1_type = calc(action1, [], type_pool)
    goals1 = proof_step(action1_type, Iff_refl)
    assert len(goals1) == 2

    action2 = Lambda(Prop, Lambda(Forall(BoundVar(0), BoundVar(1)), BoundVar(0)))
    _, action2_type = calc(action2, [], type_pool)
    goals2 = proof_step(action2_type, goals1[0])
    assert len(goals2) == 0

    action3 = Lambda(Prop, Lambda(BoundVar(0), BoundVar(0)))
    _, action3_type = calc(action3, [], type_pool)
    goals3 = proof_step(action3_type, goals1[1])
    assert len(goals3) == 0
