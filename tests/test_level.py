import pytest

from lean4_lambda_calculator.level import (
    Level,
    ParamLevel,
    MVarLevel,
    NatLevel,
    SuccLevel,
    MaxLevel,
    IMaxLevel,
    is_sufficient_equal,
    mk_normalize_succ_level,
    mk_normalize_imax_level,
    type_code,
    is_norm_lt,
    mk_normalize_max_level,
    normalize_level,
    is_equivalent,
    is_geq,
    is_geq_core,
)


# helpers for readability

def lvl(x):
    """quick constructor for NatLevel or reuse existing Level"""
    if isinstance(x, Level):
        return x
    return NatLevel(x)


def test_repr_and_bounds():
    assert repr(ParamLevel("u")) == "u"
    assert repr(MVarLevel("x")) == "?x"
    assert repr(NatLevel(3)) == "3"
    s = SuccLevel(NatLevel(2), 5)
    assert repr(s) == "2+5"
    m = MaxLevel([NatLevel(1), ParamLevel("u")])
    assert repr(m) == "Max(1, u)"
    im = IMaxLevel(NatLevel(0), NatLevel(5))
    assert repr(im) == "IMax(0, 5)"
    
    # bounds
    assert ParamLevel("u").lower_bound() == 0
    assert ParamLevel("u").upper_bound() == float('inf')
    assert NatLevel(4).is_constant()
    assert NatLevel(4).lower_bound() == 4
    assert NatLevel(4).upper_bound() == 4
    assert SuccLevel(NatLevel(1), 2).lower_bound() == 3
    assert SuccLevel(NatLevel(1), 2).upper_bound() == 3
    assert MaxLevel([NatLevel(1), NatLevel(5)]).lower_bound() == 5
    assert MaxLevel([NatLevel(1), NatLevel(5)]).upper_bound() == 5
    # imax special bounds
    im_nonzero = IMaxLevel(NatLevel(3), NatLevel(0))
    assert im_nonzero.lower_bound() == 0
    assert im_nonzero.upper_bound() == 0
    im_zero = IMaxLevel(NatLevel(3), NatLevel(2))
    assert im_zero.lower_bound() == 3
    assert im_zero.upper_bound() == 3


def test_is_sufficient_equal_simple():
    assert is_sufficient_equal(NatLevel(2), NatLevel(2))
    assert not is_sufficient_equal(NatLevel(2), NatLevel(3))
    assert is_sufficient_equal(ParamLevel("a"), ParamLevel("a"))
    assert not is_sufficient_equal(ParamLevel("a"), ParamLevel("b"))
    assert is_sufficient_equal(MVarLevel("m"), MVarLevel("m"))
    assert not is_sufficient_equal(MVarLevel("m"), MVarLevel("n"))


def test_is_sufficient_equal_succ():
    a = SuccLevel(ParamLevel("u"), 1)
    b = SuccLevel(ParamLevel("u"), 1)
    assert is_sufficient_equal(a, b)
    c = SuccLevel(ParamLevel("u"), 2)
    # offset difference should reduce to comparison of inside
    assert is_sufficient_equal(c, SuccLevel(ParamLevel("u"), 1)) is False
    assert is_sufficient_equal(SuccLevel(ParamLevel("u"), 3), SuccLevel(ParamLevel("u"), 1)) is False
    # but using the algorithm: offset > other offset
    assert not is_sufficient_equal(a, c)


def test_is_sufficient_equal_max_and_imax():
    m1 = MaxLevel([NatLevel(1), NatLevel(2)])
    m2 = MaxLevel([NatLevel(1), NatLevel(2)])
    assert is_sufficient_equal(m1, m2)
    m3 = MaxLevel([NatLevel(2), NatLevel(1)])
    assert not is_sufficient_equal(m1, m3)  # ordering matters currently
    im1 = IMaxLevel(NatLevel(0), NatLevel(1))
    im2 = IMaxLevel(NatLevel(0), NatLevel(1))
    assert is_sufficient_equal(im1, im2)
    im3 = IMaxLevel(NatLevel(1), NatLevel(0))
    assert not is_sufficient_equal(im1, im3)


def test_mk_normalize_succ_level():
    const = NatLevel(2)
    assert is_sufficient_equal(mk_normalize_succ_level(const, 3), NatLevel(5))
    s = SuccLevel(NatLevel(1), 2)
    result = mk_normalize_succ_level(s, 4)
    assert isinstance(result, SuccLevel)
    assert result.offset == 6
    assert result.level == NatLevel(1)
    m = MaxLevel([NatLevel(1), SuccLevel(NatLevel(2), 1)])
    norm = mk_normalize_succ_level(m, 2)
    # both branches increased by offset
    assert isinstance(norm, MaxLevel)
    assert any(is_sufficient_equal(arg, SuccLevel(NatLevel(1), 2)) for arg in norm.levels)


def test_mk_normalize_imax_level():
    # right constant zero -> zero
    assert is_sufficient_equal(mk_normalize_imax_level(NatLevel(10), NatLevel(0)), NatLevel(0))
    # left constant <=1 -> right
    assert mk_normalize_imax_level(NatLevel(1), ParamLevel("u")) == ParamLevel("u")
    # sufficient equal -> left returned
    p = ParamLevel("u")
    assert mk_normalize_imax_level(p, p) is p
    # lower_bound>0 -> max
    left = ParamLevel("a")
    right = ParamLevel("b")
    # force non-constant; lower_bound default 0 so adjust using Succ to make >0
    left_s = SuccLevel(left, 1)
    right_s = SuccLevel(right, 2)
    norm = mk_normalize_imax_level(left_s, right_s)
    assert isinstance(norm, MaxLevel)


def test_type_code():
    assert type_code(NatLevel(0)) == 1
    assert type_code(SuccLevel(NatLevel(0))) == 2
    assert type_code(MaxLevel([])) == 3
    assert type_code(IMaxLevel(NatLevel(0), NatLevel(0))) == 4
    assert type_code(ParamLevel("x")) == 5
    assert type_code(MVarLevel("y")) == 6


def test_is_norm_lt_simple():
    assert is_norm_lt(NatLevel(1), NatLevel(2)) < 0
    assert is_norm_lt(NatLevel(2), NatLevel(1)) > 0
    assert is_norm_lt(NatLevel(2), NatLevel(2)) == 0
    # compare by type code when bounds equal
    assert is_norm_lt(ParamLevel("a"), MVarLevel("a")) < 0
    # compare names for params
    assert is_norm_lt(ParamLevel("a"), ParamLevel("b")) < 0
    assert is_norm_lt(ParamLevel("b"), ParamLevel("a")) > 0


def test_is_norm_lt_succ_and_max():
    s1 = SuccLevel(NatLevel(1), 1)
    s2 = SuccLevel(NatLevel(1), 2)
    assert is_norm_lt(s1, s2) < 0
    assert is_norm_lt(s2, s1) > 0
    m1 = MaxLevel([NatLevel(1), NatLevel(3)])
    m2 = MaxLevel([NatLevel(1), NatLevel(4)])
    assert is_norm_lt(m1, m2) < 0
    assert is_norm_lt(m2, m1) > 0


def test_mk_normalize_max_level():
    # single item
    assert is_sufficient_equal(mk_normalize_max_level([NatLevel(5)]), NatLevel(5))
    # drop dominated items
    a = NatLevel(2)
    b = SuccLevel(NatLevel(1), 1)  # lower bound 2, upper 2
    c = NatLevel(1)
    m = mk_normalize_max_level([a, b, c])
    # a and b are equivalent; c is smaller, so result should equal a
    assert is_sufficient_equal(m, a)
    # with nested max
    nested = MaxLevel([NatLevel(1), NatLevel(4)])
    result = mk_normalize_max_level([nested, NatLevel(3)])
    assert isinstance(result, MaxLevel)
    assert any(is_sufficient_equal(arg, NatLevel(4)) for arg in result.levels)


def test_normalize_level_and_equivalence():
    # constants
    assert is_sufficient_equal(normalize_level(NatLevel(3)), NatLevel(3))
    assert normalize_level(ParamLevel("u")) == ParamLevel("u")
    # succ flattening
    s = SuccLevel(SuccLevel(NatLevel(1), 2), 3)
    assert normalize_level(s) == SuccLevel(NatLevel(1), 5)
    # imax normalization
    im = IMaxLevel(NatLevel(1), NatLevel(0))
    assert normalize_level(im) == NatLevel(0)
    # max normalization with duplicates/orderings
    m = MaxLevel([NatLevel(2), NatLevel(2)])
    norm_m = normalize_level(m)
    assert isinstance(norm_m, NatLevel) or (isinstance(norm_m, MaxLevel) and len(norm_m.levels) == 1)
    # equivalence
    assert is_equivalent(NatLevel(2), NatLevel(2))
    assert is_equivalent(SuccLevel(NatLevel(1), 1), NatLevel(2))
    # inequality
    assert not is_equivalent(ParamLevel("a"), ParamLevel("b"))


def test_is_geq_and_core():
    assert is_geq(NatLevel(3), NatLevel(2))
    assert not is_geq(NatLevel(1), NatLevel(2))
    # max/imax interactions
    m = MaxLevel([NatLevel(1), NatLevel(5)])
    assert is_geq(m, NatLevel(4))
    assert not is_geq(NatLevel(4), m)
    im = IMaxLevel(NatLevel(2), NatLevel(1))
    assert is_geq(im, NatLevel(1))
    assert not is_geq(NatLevel(1), im)

    # more complex combinations
    left = SuccLevel(NatLevel(1), 2)
    right = SuccLevel(NatLevel(1), 1)
    assert is_geq(left, right)
    assert not is_geq(right, left)

    # core with max on left
    leftmax = MaxLevel([NatLevel(2), NatLevel(4)])
    assert is_geq_core(leftmax, NatLevel(3))
    assert not is_geq_core(NatLevel(3), leftmax)

    # core with max on right
    rightmax = MaxLevel([NatLevel(2), NatLevel(6)])
    assert is_geq_core(NatLevel(6), rightmax)
    assert not is_geq_core(NatLevel(5), rightmax)

    # geq_core with Succ vs non-succ
    slevel = SuccLevel(NatLevel(1), 1)
    assert is_geq_core(slevel, NatLevel(1))

if __name__ == "__main__":
    pytest.main()