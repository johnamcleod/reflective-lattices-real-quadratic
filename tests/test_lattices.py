"""Gate A.3.1: SNF, local enumeration, hulls; corner facts of step-1 §4."""
import random
from itertools import product

import pytest

from zphi.linalg import det, hnf_basis, inv, mat_mul, transpose, bil, gram_of, ident
from zphi.lattices import (snf, local_superlattices, local_count_formula,
                           _count_subgroups)
from zphi.ring import (ZZ, ZS2, ZPHI, divides, gcd_list, ideal_eq, residues,
                       tp_divisors, primes_above)
from pari_bridge import pari, nf, mat_to_pari, ideal

pytestmark = pytest.mark.gate1
rng = random.Random(7)


def rand_mat(R, B=6):
    while True:
        M = [[R(rng.randint(-B, B), rng.randint(-B, B) if R.D != 1 else 0)
              for _ in range(3)] for _ in range(3)]
        if not det(M).is_zero():
            return M


@pytest.mark.parametrize("R", [ZZ, ZS2, ZPHI], ids=lambda R: R.name)
def test_snf_properties(R):
    for _ in range(60):
        A = rand_mat(R)
        U, S, V = snf(A)
        assert mat_mul(mat_mul(U, A), V) == S
        assert all(S[i][j].is_zero() for i in range(3) for j in range(3) if i != j)
        assert divides(S[0][0], S[1][1]) and divides(S[1][1], S[2][2])
        assert det(U).is_unit() and det(V).is_unit()
        assert all(e.is_integral() for M in (U, V) for row in M for e in row)


@pytest.mark.parametrize("R", [ZS2, ZPHI], ids=lambda R: R.name)
def test_snf_vs_pari(R):
    K = nf(R)
    for _ in range(40):
        A = rand_mat(R)
        _, S, _ = snf(A)
        one = pari("[1,0]~")
        res = pari.nfsnf(K, [mat_to_pari(A), [1, 1, 1], [1, 1, 1]])
        # PARI returns the elementary divisor ideals d_1 ⊆ d_2 ⊆ d_3 (largest first)
        ours = sorted([abs(S[i][i].norm_num()) for i in range(3)])
        theirs = sorted(int(pari.idealnorm(K, res[i])) for i in range(3))
        assert ours == theirs
        for i in range(3):
            assert any(pari.idealhnf(K, res[j]) == ideal(R, S[i][i]) for j in range(3))


def _canon(N):
    """Canonical form of the lattice spanned by the columns of N (HNF)."""
    B = hnf_basis([[N[i][j] for i in range(3)] for j in range(3)])
    return tuple(e.coords() for row in B for e in row)


@pytest.mark.parametrize("R,p", [(ZZ, 2), (ZZ, 3), (ZS2, None), (ZPHI, 2), (ZPHI, 3),
                                 (ZPHI, "pi")], ids=str)
def test_local_superlattices(R, p):
    if p is None:
        p = R.w                 # sqrt2
    elif p == "pi":
        p = R(3) - R.w
    else:
        p = R(p)
    for e in [(0, 0, 1), (0, 1, 1), (1, 1, 1), (0, 0, 2), (0, 1, 2), (1, 1, 2), (0, 2, 2)]:
        Ns = local_superlattices(e, p)
        D = [[p ** e[i] if i == j else R.zero for j in range(3)] for i in range(3)]
        keys = set()
        for N in Ns:
            assert all(x.is_integral() for row in N for x in row)
            T = mat_mul(inv(N), D)          # D <= N  iff  N^-1 D integral
            assert all(x.is_integral() for row in T for x in row)
            keys.add(_canon(N))
        assert len(keys) == len(Ns), "duplicates"
        assert len(Ns) == local_count_formula(e, p)


@pytest.mark.parametrize("D,p", [(13, 2), (13, "w"), (13, "1-w"), (13, "2w-1"),
                                 (1, 2), (2, "sqrt2"), (5, 2), (5, "pi")], ids=str)
def test_local_superlattices_ext(D, p):
    """Section 6.2: Z[omega] (2 inert, 3 split as (w)(1-w), 13 ramified), and exponents 3."""
    from zphi.ring import get_ring
    R = get_ring(D)
    w = R.w if D != 1 else None
    p = {"w": w, "1-w": R.one - w if w is not None else None, "2w-1": 2 * w - R.one if w is not None else None,
         "sqrt2": w, "pi": R(3) - w if w is not None else None}.get(p, p)
    p = R(p) if isinstance(p, int) else p
    types = [(0, 0, 1), (0, 1, 1), (1, 1, 1), (0, 0, 2), (0, 1, 2), (1, 1, 2), (0, 2, 2)]
    types += [(0, 0, 3), (0, 1, 3), (1, 1, 3), (0, 2, 3)]
    for e in types:
        Ns = local_superlattices(e, p)
        D3 = [[p ** e[i] if i == j else R.zero for j in range(3)] for i in range(3)]
        keys = set()
        for N in Ns:
            assert all(x.is_integral() for row in N for x in row)
            T = mat_mul(inv(N), D3)
            assert all(x.is_integral() for row in T for x in row)
            keys.add(_canon(N))
        assert len(keys) == len(Ns), "duplicates"
        assert len(Ns) == local_count_formula(e, p), (e, len(Ns))


# Every module type O/p^e1 + O/p^e2 + O/p^e3 with max e >= 2 that the candidate stage
# meets (tools/hull_exponents.py, logs/hull_exponents.json): (D, N(p), sorted e).
_CENSUS = {
    2: {2: ["002", "003", "004", "005", "006", "007", "008", "009", "012", "013", "014",
            "015", "016", "017", "018", "022", "023", "024", "025", "026", "027", "112",
            "113", "114", "115", "116", "117", "122", "123", "124", "222", "223", "224"],
        7: ["002"], 9: ["002"]},
    5: {4: ["002", "003", "004", "012", "013"], 5: ["002", "003", "012"], 9: ["002"],
        11: ["002"]},
    13: {3: ["002", "003", "012"], 4: ["002", "003", "004", "012", "112"]},
}


@pytest.mark.parametrize("D", sorted(_CENSUS))
def test_local_superlattices_census(D):
    """Section 6.2: every occurring type, including exponents up to 9 at sqrt2."""
    from zphi.ring import get_ring
    from zphi.lattices import prime_list
    R = get_ring(D)
    for q, types in _CENSUS[D].items():
        r = q if all(q % k for k in range(2, q)) else int(round(q ** 0.5))
        p = next(t for t in prime_list(R(r)) if abs(int(t.norm())) == q)
        for s in types:
            e = tuple(int(c) for c in s)
            Ns = local_superlattices(e, p)
            D3 = [[p ** e[i] if i == j else R.zero for j in range(3)] for i in range(3)]
            keys = set()
            for N in Ns:
                assert all(x.is_integral() for row in N for x in row)
                T = mat_mul(inv(N), D3)
                assert all(x.is_integral() for row in T for x in row)
                keys.add(_canon(N))
            assert len(keys) == len(Ns), ("duplicates", D, q, e)
            assert len(Ns) == local_count_formula(e, p), (D, q, e, len(Ns))


def test_birkhoff_count_vs_brute_force():
    """Number of subgroups of Z/p^a x Z/p^b x Z/p^c, by brute force."""
    cases = [(2, lam) for lam in [(1,), (1, 1), (2, 1), (1, 1, 1), (2, 2), (2, 1, 1),
                                  (3,), (3, 1), (3, 2), (3, 1, 1)]] \
        + [(3, lam) for lam in [(1,), (1, 1), (2, 1), (1, 1, 1), (3,), (3, 1)]]
    for p, lam in cases:
        if True:
            mods = [p ** x for x in lam]
            elems = list(product(*[range(m) for m in mods]))
            subs = set()
            # every subgroup of a rank <= 3 group is generated by <= 3 elements
            for gens in product(elems, repeat=min(3, len(lam))):
                H = {tuple(0 for _ in mods)}
                frontier = list(H)
                while frontier:
                    h = frontier.pop()
                    for g in gens:
                        s = tuple((x + y) % m for x, y, m in zip(h, g, mods))
                        if s not in H:
                            H.add(s)
                            frontier.append(s)
                subs.add(frozenset(H))
            assert len(subs) == _count_subgroups(sorted(lam, reverse=True), p)


# ------------------------------------------------- corner hulls (step-1 §4)

def hull_index(G2):
    """Order ideal generator of hull/<r,s> for the binary lattice with Gram G2."""
    R = G2[0][0].R
    e = [[R.one, R.zero], [R.zero, R.one]]
    duals = [[2 * c / G2[i][i] for c in e[i]] for i in range(2)]
    Pb = hnf_basis(duals)
    Hb = inv(mat_mul(transpose(Pb), G2))
    return det(Hb).inv()   # [H : <r,s>] = 1/det(Hb) up to units


def test_corner_hulls():
    R = ZPHI
    phi = R.w
    pi = R(3) - phi
    rho = R(2) + phi
    cases = {
        "A2": ([[R(2), R(-1)], [R(-1), R(2)]], R(3), R(3)),
        "B2": ([[R(1), R(-1)], [R(-1), R(2)]], R(1), R(2)),
        "G2": ([[R(2), R(-3)], [R(-3), R(6)]], R(3), R(1)),
        "H2": ([[R(2), -phi], [-phi, R(2)]], pi, pi),
        "I2(10)": ([[2 * rho, -rho], [-rho, R(2)]], pi, R(1)),
    }
    for name, (G2, d, idx) in cases.items():
        assert ideal_eq(det(G2), d), name
        assert ideal_eq(hull_index(G2), idx), name


# ---------------------------------------- mirror-line counts (corner_check)

def roots_orthogonal(G, p_vec, B=4):
    """Roots r of the totally positive definite lattice (O^3, G) with r.p = 0,
    up to sign; norms from the totally positive divisors of 2 det G. Coordinates
    are searched in a box; the box is shown large enough by checking that no root
    found touches its boundary."""
    R = G[0][0].R
    d2 = 2 * det(G)
    norms = tp_divisors(d2)
    coeffs = [R(a, b) for a in range(-B, B + 1) for b in range(-B, B + 1)]
    found = []
    edge = False
    for v in product(coeffs, repeat=3):
        v = list(v)
        if all(x.is_zero() for x in v) or not bil(G, v, p_vec).is_zero():
            continue
        m = bil(G, v, v)
        if not any(m == n for n in norms):
            continue
        if not gcd_list(v, R).is_unit():
            continue
        Gv = [sum((G[i][j] * v[j] for j in range(3)), R.zero) for i in range(3)]
        if not all((2 * x / m).is_integral() for x in Gv):
            continue
        found.append(v)
        if any(abs(x.a) == B or abs(x.b) == B for x in v):
            edge = True
    assert not edge, "search box too small"
    return len(found) // 2


@pytest.mark.slow
def test_mirror_counts_A2_H2():
    R = ZPHI
    phi = R.w
    pi = R(3) - phi
    Z = R.zero
    # unglued A2 ⊥ <1>: 6 mirrors (G2 corner); glued (r,s,g), g = (2r+s)/3 + p/3: 3
    G_un = [[R(2), R(-1), Z], [R(-1), R(2), Z], [Z, Z, R(1)]]
    assert roots_orthogonal(G_un, [Z, Z, R(1)], B=3) == 6
    G_gl = [[R(2), R(-1), R(1)], [R(-1), R(2), Z], [R(1), Z, R(1)]]
    assert det(G_gl) == R(1)
    p = [R(-2), R(-1), R(3)]   # 3g - 2r - s = p
    assert bil(G_gl, p, [R(1), Z, Z]).is_zero() and bil(G_gl, p, [Z, R(1), Z]).is_zero()
    assert roots_orthogonal(G_gl, p, B=3) == 3
    # unglued H ⊥ <1>: 10 mirrors (I2(10) corner); glued: 5
    H_un = [[R(2), -phi, Z], [-phi, R(2), Z], [Z, Z, R(1)]]
    assert roots_orthogonal(H_un, [Z, Z, R(1)], B=3) == 10
    # glue g = v_r + p/pi with det L = 3: g^2 = 5/pi, r.g = 1, s.g = 0
    G_h = [[R(2), -phi, R(1)], [-phi, R(2), Z], [R(1), Z, R(5) / pi]]
    assert det(G_h) == R(3)
    # p = pi g - (2r + phi s)
    p = [R(-2), -phi, pi]
    assert bil(G_h, p, [R(1), Z, Z]).is_zero() and bil(G_h, p, [Z, R(1), Z]).is_zero()
    assert roots_orthogonal(G_h, p, B=3) == 5


def test_H2_glue_example():
    """step-1 §4.5 check: det L = -3, alpha = 2."""
    R = ZPHI
    phi = R.w
    G = [[R(2), -phi, R(2)], [-phi, R(2), R(0)], [R(2), R(0), R(2) + phi]]
    assert det(G) == R(-3)


def test_reduced_short_vectors_same_set():
    import random
    from zphi.definite import short_vectors, short_vectors_reduced, _int_det, lll_gram
    rng = random.Random(7)
    for _ in range(40):
        n = rng.choice([2, 3, 4])
        while True:
            A = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
            if _int_det(A):
                break
        T = [[sum(A[k][i] * A[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        assert abs(_int_det(lll_gram(T))) == 1
        b = rng.randint(1, 80)
        assert set(short_vectors(T, b)) == set(short_vectors_reduced(T, b))


def test_integer_fincke_pohst_matches_fraction_reference():
    import random
    from fractions import Fraction as F
    from zphi.definite import short_vectors, short_vectors_fraction, _int_det
    rng = random.Random(3)
    for _ in range(150):
        n = rng.choice([1, 2, 3, 4, 5, 6])
        while True:
            A = [[rng.randint(-7, 7) for _ in range(n)] for _ in range(n)]
            if _int_det(A):
                break
        den = rng.choice([1, 3, 64])
        T = [[F(sum(A[k][i] * A[k][j] for k in range(n)), den) + (F(1, 5) if i == j else 0)
              for j in range(n)] for i in range(n)]
        b = F(rng.randint(1, 40), rng.choice([1, 2, 3]))
        got = sorted(short_vectors(T, b))
        assert got == sorted(short_vectors_fraction(T, b))
        assert all(sum(z[i] * T[i][j] * z[j] for i in range(n) for j in range(n)) <= b
                   for z in got)
