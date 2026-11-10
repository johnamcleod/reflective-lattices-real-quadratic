"""Gate A.3.1: boxes and factorisation classes (step-1 §5), exact bounds."""
import math
import random

import pytest

from zphi.boxes import box, factorisations, gammas, lam_lt_K, K_upper_int
from zphi.ring import ZS2, ZPHI

pytestmark = pytest.mark.gate1


@pytest.mark.parametrize("lo,hi,n,ncls", [(0, 4, 7, 11), (4, 36, 57, 147),
                                          (0, 196, 350, 1126), (4, 455, 807, 2902),
                                          (4, 900, 1603, 6217)])
def test_zphi_box_counts(lo, hi, n, ncls):
    b = box(ZPHI, lo, hi)
    assert len(b) == n
    assert sum(len(factorisations(z)) for z in b) == ncls
    for z in b:
        assert z.is_integral() and lo < float(z) < hi and 0 < z.sfloat() < 4


def test_first_box_elements():
    R = ZPHI
    phi = R.w
    expected = {phi ** -2, R(1), R(3) - phi, R(2), phi * phi, R(3), R(2) + phi}
    assert set(box(R, 0, 4)) == expected


def test_box_brute_force():
    for R in (ZS2, ZPHI):
        b = set(box(R, 4, 36))
        brute = set()
        for a in range(-80, 81):
            for c in range(-80, 81):
                z = R(a, c)
                if z.sign() > 0 and (z - 4).sign() > 0 and (36 - z).sign() > 0 \
                        and z.ssign() > 0 and (4 - z).ssign() > 0:
                    brute.add(z)
        assert b == brute


def test_gammas_are_4cos2():
    for R, ms in ((ZS2, [2, 3, 4, 6, 8]), (ZPHI, [2, 3, 4, 5, 6, 10])):
        g = gammas(R)
        assert sorted(g) == ms
        for m in ms:
            assert abs(float(g[m]) - 4 * math.cos(math.pi / m) ** 2) < 1e-12


def test_lam_lt_K_vs_float():
    rng = random.Random(1)
    R = ZPHI
    for _ in range(3000):
        AB = rng.choice(box(R, 0, 36))
        ApBp = rng.choice(box(R, 0, 4) + [None])
        z = rng.choice(box(R, 0, 900))
        mu = math.sqrt(float(AB)) / 2
        mup = 0 if ApBp is None else math.sqrt(float(ApBp)) / 2
        K = (math.sqrt(1 + mu) + math.sqrt(1 + mup)) ** 2 - 1
        lam = math.sqrt(float(z)) / 2
        if abs(lam - K) > 1e-9:
            assert lam_lt_K(z, AB, ApBp) == (lam < K)
        assert K_upper_int(AB, ApBp) > 4 * K * K
