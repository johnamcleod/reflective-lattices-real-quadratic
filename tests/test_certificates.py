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
