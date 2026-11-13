"""Certificates from the candidate run (gate A.3.4): reflectivity (closed polygon,
check_polygon) and non-reflectivity (chamber automorphism of infinite order,
check_nonreflective). Samples are real run outputs (tests/data/cand_samples.json);
tampered copies must be rejected."""
import copy
import json
import os

import pytest

from zphi.ring import from_json, get_ring
from zphi.vinberg import check_polygon
from zphi.nonrefl import check_nonreflective

HERE = os.path.dirname(__file__)
S = json.load(open(os.path.join(HERE, "data", "cand_samples.json")))
R = get_ring(2)


def gram(r):
    return [[from_json(R, e) for e in row] for row in r["gram"]]


def roots(r):
    return [[from_json(R, e) for e in v] for v in r["roots"]]


@pytest.mark.parametrize("r", S["reflective"])
def test_reflective_certificate(r):
    assert check_polygon(gram(r), roots(r))["ok"]


@pytest.mark.parametrize("r", S["reflective"])
def test_polygon_missing_wall_rejected(r):
    assert not check_polygon(gram(r), roots(r)[:-1])["ok"]


@pytest.mark.parametrize("r", S["nonreflective"])
def test_nonreflective_certificate(r):
    c = check_nonreflective(gram(r), r["cert"])
    assert c["ok"], c["issues"]


def _tamper(cert, fn):
    c = copy.deepcopy(cert)
    fn(c)
    return c


TAMPERS = {
    "g_identity": lambda c: c.__setitem__("g", [[[int(i == j), 0] for j in range(3)] for i in range(3)]),
    "g_entry": lambda c: c["g"][0].__setitem__(0, [c["g"][0][0][0] + 1, c["g"][0][0][1]]),
    "swap_corners": lambda c: (c.__setitem__("c", cert_copy(c, "a")), c.__setitem__("d", cert_copy(c, "b"))),
    "neg_root": lambda c: c.__setitem__("a", [[-e[0], -e[1]] for e in c["a"]]),
}


def cert_copy(c, k):
    return copy.deepcopy(c[k])


@pytest.mark.parametrize("name", sorted(TAMPERS))
@pytest.mark.parametrize("r", S["nonreflective"][:1])
def test_nonreflective_tampered_rejected(r, name):
    assert not check_nonreflective(gram(r), _tamper(r["cert"], TAMPERS[name]))["ok"]


def test_cover_balls_cover_the_simplex():
    """Random positive combinations of the triangle's corners (points of the triangle)
    lie in some ball of the cover; the ball radii respect the threshold."""
    import random
    from fractions import Fraction as Fr
    from zphi.vinberg import cover_balls, _cosh2, vertex_vector
    from zphi.linalg import bil
    r = S["reflective"][0]
    G, rts = gram(r), roots(r)
    n = len(rts)
    P = []
    for i in range(n):
        p = vertex_vector(G, rts[i], rts[(i + 1) % n])
        if bil(G, rts[(i + 2) % n], p).sign() > 0:
            p = [-x for x in p]
        P.append(p)
    # a large triangle: push the corners apart by reflections (images stay in the sheet)
    def reflect(G, r, y):
        k = 2 * bil(G, r, y) / bil(G, r, r)
        return [a - k * b for a, b in zip(y, r)]
    far = P[0]
    for k in range(6):
        far = reflect(G, rts[k % n], far)
    tri = (P[0], P[1], far)
    balls = list(cover_balls(G, [tri], thresh=Fr(2)))
    assert len(balls) > 1 and all(D <= 2 for _, D in balls)
    rnd = random.Random(1)
    for _ in range(30):
        w = [Fr(rnd.randint(1, 50)) for _ in range(3)]
        y = [sum((p[j] * wi for p, wi in zip(tri, w)), G[0][0].R.zero) for j in range(3)]
        assert any(((_cosh2(G, c, y) - 1) - G[0][0].R(D)).sign() <= 0 for c, D in balls)


@pytest.mark.parametrize("r", S["reflective"])
def test_boundary_walk_closes_reflective(r):
    from zphi.walk import boundary_walk
    from zphi.vinberg import vertex_vector
    from zphi.linalg import bil
    G, rts = gram(r), roots(r)
    n = len(rts)
    v = vertex_vector(G, rts[0], rts[1])
    if bil(G, rts[2 % n], v).sign() > 0:
        v = [-c for c in v]
    w = boundary_walk(G, rts[0], rts[1], v)
    assert w["status"] == "closed"
    assert check_polygon(G, w["roots"])["ok"]
    assert len(w["roots"]) == n


@pytest.mark.parametrize("r", S["nonreflective"])
def test_boundary_walk_certifies_nonreflective(r):
    from zphi.walk import boundary_walk
    from zphi.vinberg import vertex_vector
    from zphi.linalg import bil
    G = gram(r)
    c = r["cert"]
    a, b, x = ([from_json(R, e) for e in c[k]] for k in "abx")
    v = vertex_vector(G, a, b)
    if bil(G, v, x).sign() > 0:
        v = [-e for e in v]
    w = boundary_walk(G, a, b, v)
    assert w["status"] == "translation"
    assert check_nonreflective(G, w["cert"])["ok"]
