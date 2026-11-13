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


def test_new_field_sqrt3():
    # Q(sqrt3): disc 12, norm-Euclidean, eps = 2 + sqrt3; gamma(12) = 2 + sqrt3
    R = _ring(103, c0=3, c1=0, eps=(2, 1))
    assert {m: g.coords() for m, g in R.gammas.items()}[12] == (2, 1, 1)
    assert 5 not in R.gammas and 8 not in R.gammas


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
