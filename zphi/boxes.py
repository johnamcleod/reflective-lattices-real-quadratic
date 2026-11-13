"""Boxes of ring elements, good factorisations (Mark Lemma 8, §3.2) and exact
comparisons of the real numbers that appear in Allcock's thin-part bounds.

Exactness: elements are enumerated over a float-enlarged coordinate range and then
every inequality is re-tested exactly (El.sign / El.ssign). Comparisons involving
square roots (lambda < K) are decided by rigorous integer interval arithmetic with
increasing precision; see `lam_lt_K`.
"""
from __future__ import annotations

from math import isqrt, floor, ceil
from typing import Dict, List, Optional, Tuple

from .ring import El, Ring, tp_divisors, tp_normalise

# ------------------------------------------------------------------ boxes

_BOX_CACHE: Dict[Tuple, List[El]] = {}


def _as_el(R: Ring, v) -> El:
    return v if isinstance(v, El) else R(v)


def elements_in_box(R: Ring, lo, hi, slo=0, shi=4) -> List[El]:
    """All z in O with lo < z < hi at id and slo < sigma(z) < shi (strict, exact).

    For R = Z the sigma bounds are ignored. Bounds are ints or elements of K."""
    key = (R.D, str(lo), str(hi), str(slo), str(shi))
    if key in _BOX_CACHE:
        return list(_BOX_CACHE[key])
    Lo, Hi = _as_el(R, lo), _as_el(R, hi)
    out: List[El] = []
    if R.degree == 1:
        for a in range(floor(float(Lo)) - 1, ceil(float(Hi)) + 2):
            z = R(a)
            if (z - Lo).sign() > 0 and (Hi - z).sign() > 0:
                out.append(z)
    else:
        SLo, SHi = _as_el(R, slo), _as_el(R, shi)
        fl, fh, fsl, fsh = float(Lo), float(Hi), float(SLo), float(SHi)
        sd = R.disc ** 0.5
        # z - sigma z = b sqrt(disc);  z + sigma z = 2a + c1 b
        bmin = floor((fl - fsh) / sd) - 2
        bmax = ceil((fh - fsl) / sd) + 2
        for b in range(bmin, bmax + 1):
            tmin = fl + fsl
            tmax = fh + fsh
            amin = floor((tmin - R.c1 * b) / 2) - 2
            amax = ceil((tmax - R.c1 * b) / 2) + 2
            for a in range(amin, amax + 1):
                z = R(a, b)
                if ((z - Lo).sign() > 0 and (Hi - z).sign() > 0
                        and (z - SLo).ssign() > 0 and (SHi - z).ssign() > 0):
                    out.append(z)
    out.sort(key=lambda z: (float(z), z.coords()))
    _BOX_CACHE[key] = out
    return list(out)


def box(R: Ring, lo, hi) -> List[El]:
    """Mark's boxes: lo < z < hi at id, 0 < sigma(z) < 4."""
    return elements_in_box(R, lo, hi, 0, 4)


def factorisations(z: El) -> List[Tuple[El, El]]:
    """Good factorisations z = u v (u, v totally positive), one per class modulo unit
    squares, i.e. one per ideal divisor (u) of (z). u canonical, v = z/u."""
    return [(u, z / u) for u in tp_divisors(z)]


def gammas(R: Ring) -> Dict[int, El]:
    """gamma(m) = 4cos^2(pi/m) for the m with gamma(m) in O; m = 2 gives 0.
    From the field profile (computed and exactly verified in zphi.fields)."""
    return dict(R.gammas)


# ------------------------------------------------- exact real comparisons
# Real numbers here are id-values of square roots of elements of K. We work with
# integer intervals [lo, hi] representing [lo/S, hi/S], S = 2^p.

def _iv_el(z: El, p: int) -> Tuple[int, int]:
    """Interval for id(z) at scale 2^p."""
    R = z.R
    S = 1 << p
    if R.degree == 1 or z.b == 0:
        x = z.a * S
        lo = x // z.n
        hi = -((-x) // z.n)
        return lo, hi
    # id(z) = (2a + c1 b + b sqrt(disc)) / (2n)
    x = (2 * z.a + R.c1 * z.b) * S
    r2 = R.disc * z.b * z.b * S * S
    r = isqrt(r2)
    if z.b > 0:
        num_lo, num_hi = x + r, x + r + 1
    else:
        num_lo, num_hi = x - r - 1, x - r
    d = 2 * z.n
    return num_lo // d, -((-num_hi) // d)


def _iv_sqrt(iv: Tuple[int, int], p: int) -> Tuple[int, int]:
    lo, hi = iv
    S = 1 << p
    lo = max(lo, 0)
    return isqrt(lo * S), isqrt(hi * S) + 1


def _iv_add(x, y):
    return x[0] + y[0], x[1] + y[1]


def _iv_mul(x, y, p):
    c = [x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1]]
    S = 1 << p
    return min(c) // S, -((-max(c)) // S)


def _K_iv(AB: El, ApBp: Optional[El], p: int):
    """K = 1 + mu + mu' + 2 sqrt((1+mu)(1+mu')), mu = sqrt(AB)/2."""
    S = 1 << p
    one = (S, S)
    mu = _iv_sqrt(_iv_el(AB, p), p)
    mu = (mu[0] // 2, -((-mu[1]) // 2))
    if ApBp is None or ApBp.is_zero():
        mup = (0, 0)
    else:
        mup = _iv_sqrt(_iv_el(ApBp, p), p)
        mup = (mup[0] // 2, -((-mup[1]) // 2))
    a = _iv_add(one, mu)
    b = _iv_add(one, mup)
    root = _iv_sqrt(_iv_mul(a, b, p), p)
    K = _iv_add(_iv_add(_iv_add(one, mu), mup), (2 * root[0], 2 * root[1]))
    return K


UNDECIDED_LOG: List[Tuple] = []


def lam_lt_K(z: El, AB: El, ApBp: Optional[El]) -> bool:
    """Decide id(sqrt(z))/2 < K(mu, mu') rigorously.

    If the intervals still overlap at 4096 bits (which would mean equality, a
    measure-zero boundary case), return True (keep the configuration: a superset
    is safe) and log it in UNDECIDED_LOG."""
    p = 64
    while p <= 4096:
        lam = _iv_sqrt(_iv_el(z, p), p)
        lam = (lam[0] // 2, -((-lam[1]) // 2))
        K = _K_iv(AB, ApBp, p)
        if lam[1] < K[0]:
            return True
        if lam[0] > K[1]:
            return False
        p *= 2
    UNDECIDED_LOG.append((z, AB, ApBp))
    return True


def K_upper_int(AB: El, ApBp: Optional[El]) -> int:
    """An integer strictly greater than 4 K^2 (for the C C' box)."""
    p = 64
    K = _K_iv(AB, ApBp, p)
    S2 = 1 << (2 * p)
    return -((-(4 * K[1] * K[1])) // S2) + 1
