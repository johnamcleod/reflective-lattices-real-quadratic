"""Vinberg, polygon certificates and chamber isometries on entries of Mark's table."""
import json
import os
import random

import pytest

from zphi.ring import ZS2 as R, from_json
from zphi.linalg import det, inv, mat_mul, transpose, mat_vec
from zphi.vinberg import vinberg, check_polygon
from zphi.isometry import find_isometry, invariant_key

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
pytestmark = pytest.mark.gate1


def entries():
    return json.load(open(os.path.join(ROOT, "data", "mark_zsqrt2_432.json")))


def load(e):
    G = [[from_json(R, x) for x in row] for row in e["gram"]]
    rts = [[from_json(R, x) for x in r] for r in e["roots"]]
    return G, rts


def mirror(r):
    x = next(c for c in r if not c.is_zero())
    return tuple((y / x).coords() for y in r)


@pytest.mark.parametrize("i", [0, 1, 3, 5])
def test_vinberg_reproduces_mark(i):
    G, rts = load(entries()[i])
    out = vinberg(G, rts[:2], orient=rts[2])
    assert out["status"] == "reflective"
    assert {mirror(r) for r in out["roots"]} == {mirror(r) for r in rts}
    assert check_polygon(G, rts)["ok"]


def test_check_polygon_rejects_bad_chamber():
    G, rts = load(entries()[3])        # a quadrilateral
    assert not check_polygon(G, rts[:3])["ok"]          # not closed
    assert not check_polygon(G, rts[::-1][:2] + rts[2:])["ok"]


def _unimodular(rng):
    while True:
        P = [[R(rng.randint(-2, 2), rng.randint(-1, 1)) for _ in range(3)] for _ in range(3)]
        if det(P).is_unit():
            return P


@pytest.mark.parametrize("i", [0, 1, 4])
def test_isometry_after_basis_change(i):
    rng = random.Random(i)
    G, rts = load(entries()[i])
    P = _unimodular(rng)
    G2 = mat_mul(mat_mul(transpose(P), G), P)
    Pi = inv(P)
    rts2 = [mat_vec(Pi, r) for r in rts]
    # rotate the cycle and scale roots by unit squares: still the same chamber
    k = rng.randrange(len(rts2))
    rts2 = rts2[k:] + rts2[:k]
    eta = R.eta
    rts2 = [[eta * x for x in r] if j % 2 else r for j, r in enumerate(rts2)]
    assert invariant_key(G, rts) == invariant_key(G2, rts2)
    phi = find_isometry(G, rts, G2, rts2)
    assert phi is not None
    assert mat_mul(mat_mul(transpose(phi), G2), phi) == G
    assert det(phi).is_unit()


def test_non_isometric_distinct_det():
    E = entries()
    G1, r1 = load(E[0])
    G2, r2 = load(E[1])
    assert find_isometry(G1, r1, G2, r2) is None


@pytest.mark.parametrize("i", [0, 2, 7, 11])
def test_sublattice_enumeration_same_roots(i):
    """roots_upto on L_m equals roots_upto on the full lattice O^3."""
    from zphi.vinberg import Lattice, vertex_vector
    from zphi.linalg import ident
    G, rts = load(entries()[i])
    v0 = vertex_vector(G, rts[0], rts[1])
    a = Lattice(G, v0)
    b = Lattice(G, v0)
    I = ident(R, 3)
    b._sublattice = lambda m: (I, G, v0)
    for D in (1, 4):
        assert sorted(map(str, a.roots_upto(D))) == sorted(map(str, b.roots_upto(D)))
