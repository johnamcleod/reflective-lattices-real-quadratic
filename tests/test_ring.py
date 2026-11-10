"""Gate A.3.1: ring arithmetic, units, primes, divisors (step-1 §1)."""
import random
from fractions import Fraction

import pytest

from zphi.ring import (ZZ, ZS2, ZPHI, El, assoc_key, divides, egcd, factor,
                       ideal_eq, is_squarefree, primes_above, residues, tp_divisors,
                       tp_normalise, unit_sqrt)
from pari_bridge import pari, nf, to_pari

pytestmark = pytest.mark.gate1
RINGS = [ZZ, ZS2, ZPHI]
rng = random.Random(20261110)


def rand_el(R, lo=-30, hi=30, den=False):
    n = rng.choice([1, 1, 2, 3, 6]) if den else 1
    return R(rng.randint(lo, hi), rng.randint(lo, hi) if R.D != 1 else 0, n)


def to_proto(z):
    import quadring as q
    P = q.Ring(z.R.D)
    if z.R.D == 1:
        return P(Fraction(z.a, z.n))
    if z.R.D == 2:
        return P(Fraction(z.a, z.n), Fraction(z.b, z.n))
    # a + b phi = (a + b/2) + (b/2) sqrt5
    return P(Fraction(2 * z.a + z.b, 2 * z.n), Fraction(z.b, 2 * z.n))


@pytest.mark.parametrize("R", RINGS, ids=lambda R: R.name)
def test_field_ops_vs_prototype(R):
    for _ in range(400):
        x, y = rand_el(R, den=True), rand_el(R, den=True)
        X, Y = to_proto(x), to_proto(y)
        assert to_proto(x + y) == X + Y
        assert to_proto(x - y) == X - Y
        assert to_proto(x * y) == X * Y
        if not y.is_zero():
            assert to_proto(x / y) == X / Y
        assert to_proto(x.conj()) == X.conj()
        # prototype's "norm" over Z is x^2; ours is the field norm N_{Q/Q}(x) = x
        assert (x.norm() ** 2 if R.D == 1 else x.norm()) == X.norm()
        assert x.sign() == X.sign()
        assert x.ssign() == X.ssign()
        assert x.is_integral() == X.is_integral()


@pytest.mark.parametrize("R", RINGS, ids=lambda R: R.name)
def test_sign_vs_float(R):
    for _ in range(2000):
        z = rand_el(R, -10 ** 6, 10 ** 6)
        f, fs = float(z), z.sfloat()
        if abs(f) > 1e-6:
            assert z.sign() == (1 if f > 0 else -1)
        if abs(fs) > 1e-6:
            assert z.ssign() == (1 if fs > 0 else -1)


def test_golden_facts():
    R = ZPHI
    phi = R.w
    assert phi * phi == phi + 1
    assert phi.norm_num() == -1
    sqrt5 = 2 * phi - 1
    assert sqrt5 * sqrt5 == R(5)
    pi = R(3) - phi
    assert pi.norm_num() == 5 and pi == sqrt5 / phi and pi == R(4) - phi * phi
    rho = R(5, 0) / 2 + sqrt5 / 2
    assert rho == R(2, 1) and rho == phi * sqrt5 and rho.tpos()
    import math
    assert abs(float(rho) - 4 * math.cos(math.pi / 10) ** 2) < 1e-12
    assert abs(float(phi * phi) - 4 * math.cos(math.pi / 5) ** 2) < 1e-12
    # rho (4 - rho) = rho phi^-2 = pi  (step-1 §4 table, I2(10) determinant)
    assert rho * (4 - rho) == pi and rho / (phi * phi) == pi


@pytest.mark.parametrize("R", [ZS2, ZPHI], ids=lambda R: R.name)
def test_totally_positive_units_are_squares(R):
    """(U2): +-eps^k is totally positive iff the sign is + and k is even."""
    for k in range(-12, 13):
        for s in (1, -1):
            u = s * R.eps ** k
            assert u.is_unit()
            assert u.tpos() == (s == 1 and k % 2 == 0)
            if u.tpos():
                e = unit_sqrt(u)
                assert e * e == u and e.sign() > 0


def _order_mod(u, p):
    R = u.R
    x = u
    for k in range(1, 200):
        if divides(p, x - 1):
            return k
        x = x * u
    raise AssertionError


def test_residue_unit_groups():
    """phi generates (O/2)^x (order 3), (O/3)^x (order 8), (O/pi)^x (order 4)."""
    R = ZPHI
    phi, pi = R.w, R(3) - R.w
    assert _order_mod(phi, R(2)) == 3
    assert _order_mod(phi, R(3)) == 8
    assert _order_mod(phi, pi) == 4
    assert len(residues(R(2))) == 4 and len(residues(R(3))) == 9 and len(residues(pi)) == 5


def test_prime_decomposition_2_3_5():
    R = ZPHI
    assert [p.coords() for p in primes_above(2, R)] == [R(2).coords()]
    assert [p.coords() for p in primes_above(3, R)] == [R(3).coords()]
    f5 = factor(R(5))
    assert len(f5) == 1 and f5[0][1] == 2 and ideal_eq(f5[0][0], R(3) - R.w)
    # Z[sqrt2]: 2 ramified, 3 and 5 inert
    S = ZS2
    f2 = factor(S(2))
    assert len(f2) == 1 and f2[0][1] == 2 and ideal_eq(f2[0][0], S.w)
    assert len(factor(S(3))) == 1 and factor(S(3))[0][1] == 1
    assert len(factor(S(5))) == 1 and factor(S(5))[0][1] == 1


@pytest.mark.parametrize("R", [ZS2, ZPHI], ids=lambda R: R.name)
def test_factor_vs_pari(R):
    K = nf(R)
    for _ in range(150):
        z = rand_el(R, -200, 200)
        if z.is_zero():
            continue
        ours = sorted((abs(p.norm_num()), e) for p, e in factor(z))
        F = pari.idealfactor(K, to_pari(z))
        theirs = sorted((int(pari.idealnorm(K, F[i, 0])), int(F[i, 1]))
                        for i in range(int(pari.matsize(F)[0])))
        assert ours == theirs
        for p, e in factor(z):
            assert divides(p ** e, z) and not divides(p ** (e + 1), z)


@pytest.mark.parametrize("R", RINGS, ids=lambda R: R.name)
def test_divisors_vs_brute_force(R):
    for _ in range(25):
        z = rand_el(R, -40, 40)
        if z.is_zero():
            continue
        divs = tp_divisors(z)
        assert all(d.tpos() and divides(d, z) for d in divs)
        assert len({assoc_key(d) for d in divs}) == len(divs)
        # brute force: all d with |N(d)| dividing |N(z)|, small coordinates
        Nz = abs(z.norm_num())
        brute = set()
        B = 2 * int(Nz ** 0.5) + 6
        for a in range(-B, B + 1):
            for b in (range(-B, B + 1) if R.D != 1 else [0]):
                d = R(a, b)
                if d.is_zero() or Nz % abs(d.norm_num()):
                    continue
                if divides(d, z):
                    brute.add(assoc_key(d))
        assert brute <= {assoc_key(d) for d in divs}
        # number of ideal divisors = prod (e_i + 1)
        n = 1
        for _, e in factor(z):
            n *= e + 1
        assert len(divs) == n


@pytest.mark.parametrize("R", RINGS, ids=lambda R: R.name)
def test_egcd_and_normalise(R):
    for _ in range(200):
        a, b = rand_el(R), rand_el(R)
        if a.is_zero() and b.is_zero():
            continue
        g, x, y = egcd(a, b) if not b.is_zero() else (a, R.one, R.zero)
        assert x * a + y * b == g
        if not a.is_zero():
            assert divides(g, a)
        if not b.is_zero():
            assert divides(g, b)
        if not a.is_zero():
            t = tp_normalise(a)
            assert t.tpos() and ideal_eq(t, a)
            for k in range(-3, 4):
                assert tp_normalise(a * R.eta ** k) == t
                assert tp_normalise(-a * R.eps ** k) == t


@pytest.mark.parametrize("R", RINGS, ids=lambda R: R.name)
def test_residues_complete(R):
    for _ in range(30):
        d = rand_el(R, -9, 9)
        if d.is_zero():
            continue
        res = residues(d)
        assert len(res) == abs(d.norm_num())
        for i, x in enumerate(res):
            for y in res[:i]:
                assert not divides(d, x - y)


def test_squarefree():
    R = ZPHI
    pi = R(3) - R.w
    assert is_squarefree(R(2) * R(3) * pi)
    assert not is_squarefree(R(5))
    assert not is_squarefree(R(4))
    assert is_squarefree(R.w)  # unit
