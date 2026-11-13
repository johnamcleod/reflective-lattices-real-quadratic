"""Field profiles: hypotheses (H1)/(H2) checked, derived data computed exactly."""
import pytest

from zphi.fields import FieldProfile, HypothesisError, register, PROFILES
from zphi.ring import Ring, get_ring


def _ring(key, **kw):
    register(FieldProfile(key=key, name=f"test{key}", symbol="w", degree=2, **kw))
    try:
        return Ring(key)
    finally:
        PROFILES.pop(key)


def test_known_profiles_and_gammas():
    assert {m: str(g) for m, g in get_ring(2).gammas.items()} == \
        {2: "0", 3: "1", 4: "2", 6: "3", 8: "2+1√2"}
    assert {m: str(g) for m, g in get_ring(5).gammas.items()} == \
        {2: "0", 3: "1", 4: "2", 5: "1+1φ", 6: "3", 10: "2+1φ"}
    assert sorted(get_ring(1).gammas) == [2, 3, 4, 6]


def test_rejects_sqrt3_no_norm_minus_one_unit():
    # Q(sqrt3): disc 12, norm-Euclidean, but eps = 2 + sqrt3 has norm +1: (N2) fails
    with pytest.raises(HypothesisError, match="N2"):
        _ring(103, c0=3, c1=0, eps=(2, 1))


def test_sqrt13_profile():
    from fractions import Fraction as Fr
    from zphi.ring import factor, ediv
    R = get_ring(13)
    assert R.profile.disc == 13
    assert {m: str(g) for m, g in R.gammas.items()} == {2: "0", 3: "1", 4: "2", 6: "3"}
    eps = R(*R.profile.eps)
    assert eps.norm_num() == -1 and eps * eps.conj() == R(-1)
    # 2 inert, 3 split, 13 ramified
    assert [e for _, e in factor(R(2))] == [1] and abs(factor(R(2))[0][0].norm_num()) == 4
    assert sorted(abs(p.norm_num()) for p, _ in factor(R(3))) == [3, 3]
    assert [e for _, e in factor(R(13))] == [2]
    # rounding division reduces the norm (bound 13/16)
    for a in range(-7, 8):
        for b in range(-7, 8):
            for c, d in ((3, 1), (2, -1), (5, 2), (1, 3)):
                if (a, b) != (0, 0):
                    q, r = ediv(R(a, b), R(c, d))
                    assert abs(r.norm_num()) < abs(R(c, d).norm_num())


def test_rejects_non_euclidean():
    with pytest.raises(HypothesisError, match="H1"):
        _ring(110, c0=10, c1=0, eps=(3, 1))          # Q(sqrt10), class number 2


def test_rejects_non_maximal_order():
    with pytest.raises(HypothesisError, match="maximal"):
        _ring(120, c0=5, c1=0, eps=(2, 1))           # Z[sqrt5] is not O


def test_rejects_non_fundamental_unit():
    with pytest.raises(HypothesisError, match="smaller unit"):
        _ring(102, c0=2, c1=0, eps=(3, 2))           # (1+sqrt2)^2


def test_rejects_degree_3():
    register(FieldProfile(key=130, name="cubic", symbol="w", degree=3))
    try:
        with pytest.raises(HypothesisError, match="H2"):
            Ring(130)
    finally:
        PROFILES.pop(130)
