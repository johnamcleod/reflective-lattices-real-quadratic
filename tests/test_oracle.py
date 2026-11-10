"""Production code vs the supplied prototype (oracle), on configurations and
candidate lattices."""
import random
from fractions import Fraction

import pytest

from zphi import configs as C
from zphi.lattices import candidates
from zphi.ring import ZZ, ZS2, ZPHI, get_ring

pytestmark = pytest.mark.gate1


def from_proto(z, R):
    if R.D == 1:
        return R(Fraction(z.x))
    if R.D == 2:
        return R(Fraction(z.x), Fraction(z.y))
    # x + y sqrt5 = (x - y) + 2y phi
    return R(Fraction(z.x - z.y), Fraction(2 * z.y))


def to_proto(z, P):
    if z.R.D == 1:
        return P(Fraction(z.a, z.n))
    if z.R.D == 2:
        return P(Fraction(z.a, z.n), Fraction(z.b, z.n))
    return P(Fraction(2 * z.a + z.b, 2 * z.n), Fraction(z.b, 2 * z.n))


def key_of(GM):
    return tuple(e.coords() for row in GM for e in row)


@pytest.mark.parametrize("D", [2, 5])
def test_short_edge_keys_match_prototype(D):
    """Same configuration counts per type (the prototype exposes counts only)."""
    import quadring as q
    import rank3
    R = get_ring(D)
    _, st = rank3.enumerate_short_edge(q.Ring(D), lattices=False)
    ours = [cfg.mark_type for cfg in C.short_edge(R)]
    assert st["configs_Ap"] == ours.count("15")
    assert st["configs_Ap0"] == ours.count("16")


def _same_lattice(B1, B2):
    from zphi.linalg import inv, mat_mul, is_integral_mat
    return is_integral_mat(mat_mul(inv(B1), B2)) and is_integral_mat(mat_mul(inv(B2), B1))


def _same_sets(L1, L2):
    """Equal as sets of sublattices of K^3 (each list free of repeats)."""
    if len(L1) != len(L2):
        return False
    return all(any(_same_lattice(a, b) for b in L2) for a in L1)


@pytest.mark.parametrize("D,n", [(2, 40), (5, 40)])
def test_candidates_match_prototype(D, n):
    """Same candidate lattices, compared as sublattices of K^3 (Gram matrices
    depend on the basis the HNF happens to pick)."""
    import quadring as q
    import rank3
    R = get_ring(D)
    P = q.Ring(D)
    cfgs = list(C.short_edge(R))
    rng = random.Random(D)
    sample = rng.sample(cfgs, n)
    captured = []
    orig = rank3._finish

    def spy(G, Mb, roots):
        out = orig(G, Mb, roots)
        if out is not None:
            captured.append(Mb)
        return out

    rank3._finish = spy
    try:
        nonempty = 0
        for cfg in sample:
            ours = [Mb for _, Mb in candidates(cfg.G, cfg.roots, with_basis=True)]
            Gp = [[to_proto(e, P) for e in row] for row in cfg.G]
            rootsp = [[to_proto(e, P) for e in v] for v in cfg.roots]
            captured.clear()
            rank3.candidates_from_roots(Gp, rootsp)
            theirs = [[[from_proto(e, R) for e in row] for row in Mb] for Mb in captured]
            assert _same_sets(ours, theirs), cfg.key
            nonempty += bool(ours)
        assert nonempty > 0
    finally:
        rank3._finish = orig
