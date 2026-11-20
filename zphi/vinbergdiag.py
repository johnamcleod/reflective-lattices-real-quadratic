"""Vinberg's algorithm for the diagonal forms L = <-d, 1^n> over O (rank n + 1), v0 = e0.
Exact; a fast path of zphi.vinbergn for D1 (same acceptance rule and termination).

Roots r = (x0; x1, ..., xn) of norm m: m runs over the totally positive divisors of
2 det G modulo unit squares (as in vinbergn), r primitive, m | 2 d x0 and m | 2 x_i.

  * Stabiliser of v0. Its roots are the roots with x0 = 0. If (checked here, for every
    norm) the only such roots with x1 >= ... >= xn >= 0 (at id) are e1 (norm 1) and
    e1 + e2 (norm 2), the stabiliser root system is B_n, and we take its simple roots
    -e_i + e_{i+1} (1 <= i < n), -e_n (AlVin's convention). Otherwise ValueError (use
    vinbergn).
  * Every further accepted root has (r, a) <= 0 for these, i.e. x1 >= ... >= xn >= 0.
    So only sorted coordinates are searched: for each x0 (x0 >= 0 at id, finitely many
    for delta = d x0^2 / m <= Delta, since sigma(x0)^2 <= sigma(m) / |sigma(d)|) we find
    the sorted representations of N = m + d x0^2 as x1^2 + ... + xn^2 in O, by a
    recursive search over boxes (x_i^2 >= N_rem / k at id, as the k remaining
    coordinates are <= x_i) and an exact square root for the last coordinate.
  * Delta is processed in slices (Delta_prev, Delta], each candidate once.

Every inclusion test is exact (floats only bound the boxes, with a margin, and every box
element is re-checked exactly). The other roots of L (unsorted, or with x0 < 0) are never
accepted by Vinberg's rule, so the accepted sequence is the one vinbergn produces.
"""
from __future__ import annotations

import time as _time
from fractions import Fraction as Fr
from functools import cmp_to_key
from math import ceil, floor, sqrt
from typing import Dict, List, Optional

from .definite import is_root
from .linalg import bil, det
from .ring import gcd_list, tp_divisors
from .vinbergn import coxiter, coxiter_graph

EPS = 1e-9


def _embeds(R):
    rt = sqrt(R.disc)
    return (R.c1 + rt) / 2, (R.c1 - rt) / 2


def box(R, lo, hi, B):
    """Elements x of O with lo <= id(x) <= hi and |sigma(x)| <= B (float bounds with a
    margin; callers re-check exactly)."""
    w1, w2 = _embeds(R)
    lo, hi, B = lo - EPS * (1 + abs(lo)), hi + EPS * (1 + abs(hi)), B + EPS * (1 + B)
    if hi < lo or B < 0:
        return
    s = w1 - w2  # > 0
    # id - sigma = b s, so b in [(lo - B)/s, (hi + B)/s]
    for b in range(ceil((lo - B) / s), floor((hi + B) / s) + 1):
        a_lo = max(lo - b * w1, -B - b * w2)
        a_hi = min(hi - b * w1, B - b * w2)
        for a in range(ceil(a_lo), floor(a_hi) + 1):
            yield R(a, b)


def sqrt_el(R, N):
    """x in O with x^2 = N and id(x) >= 0, or None."""
    if N.is_zero():
        return R.zero
    f1, f2 = float(N), N.sfloat()
    if f1 < -EPS or f2 < -EPS:
        return None
    s1, w = sqrt(max(f1, 0)), _embeds(R)
    for s2 in (sqrt(max(f2, 0)), -sqrt(max(f2, 0))):
        b = round((s1 - s2) / (w[0] - w[1]))
        a = round(s1 - b * w[0])
        for x in (R(a, b),):
            if (x * x - N).is_zero() and x.sign() >= 0:
                return x
    return None


def _tnonneg(x):
    return x.sign() >= 0 and x.ssign() >= 0


def sorted_reps(R, N, k, upper, ok):
    """All (x_1 >= ... >= x_k >= 0 at id) in O with x_1 <= upper (None: no bound),
    sum x_i^2 = N, ok(x_i) for each."""
    if not _tnonneg(N):
        return
    if N.is_zero():
        if ok(R.zero):
            yield (R.zero,) * k
        return
    if k == 1:
        x = sqrt_el(R, N)
        if x is not None and ok(x) and (upper is None or (upper - x).sign() >= 0):
            yield (x,)
        return
    f1, f2 = float(N), N.sfloat()
    hi = sqrt(max(f1, 0))
    if upper is not None:
        hi = min(hi, float(upper))
    lo = sqrt(max(f1, 0) / k)
    for x in box(R, lo, hi, sqrt(max(f2, 0))):
        if x.sign() < 0 or (upper is not None and (upper - x).sign() < 0):
            continue
        x2 = x * x
        rem = N - x2
        if not _tnonneg(rem) or (k * x2 - N).sign() < 0 or not ok(x):
            continue
        for rest in sorted_reps(R, rem, k - 1, x, ok):
            yield (x,) + rest


class DiagLattice:
    def __init__(self, d, n: int):
        R = d.R
        self.R, self.d, self.n = R, d, n
        if not (d.sign() > 0 and d.ssign() < 0):
            raise ValueError("d must be positive at id and negative at sigma")
        self.G = [[(-d if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n + 1)]
                  for i in range(n + 1)]
        self.norms = tp_divisors(2 * det(self.G))

    def _ok(self, m):
        return lambda x: (2 * x / m).is_integral()

    def check_stabiliser(self):
        """The x0 = 0 roots with sorted coordinates are exactly e1 (norm 1), e1+e2 (norm 2)."""
        R, n = self.R, self.n
        found = []
        for m in self.norms:
            for xs in sorted_reps(R, m, n, None, self._ok(m)):
                r = [R.zero] + list(xs)
                if gcd_list(r, R).is_unit():
                    found.append((m, tuple(r)))
        e1 = tuple([R.zero, R.one] + [R.zero] * (n - 1))
        e12 = tuple([R.zero, R.one, R.one] + [R.zero] * (n - 2))
        want = {(R.one, e1), (R(2), e12)}
        got = {(m, r) for m, r in found}
        if got != want:
            raise ValueError(f"stabiliser is not B_{n}: {[(str(m), [str(x) for x in r]) for m, r in got]}")

    def stab_roots(self):
        R, n = self.R, self.n
        out = []
        for i in range(1, n):
            v = [R.zero] * (n + 1)
            v[i], v[i + 1] = -R.one, R.one
            out.append(v)
        v = [R.zero] * (n + 1)
        v[n] = -R.one
        out.append(v)
        return out

    def candidates(self, D1: Fr, D2: Fr, deadline: Optional[float] = None):
        """(delta, m, r) with D1 < delta <= D2 (D1 = None: delta > 0), r a root, x0 > 0,
        x1 >= ... >= xn >= 0. Raises _Timeout once time.time() > deadline (checked per x0)."""
        R, d, n = self.R, self.d, self.n
        out = []
        sd = -d.sfloat()
        for m in self.norms:
            ok = self._ok(m)
            hi = sqrt(float(D2) * float(m) / float(d))
            B = sqrt(max(m.sfloat(), 0) / sd)
            for x0 in box(R, 0, hi, B):
                if deadline is not None and _time.time() > deadline:
                    raise _Timeout
                if x0.sign() <= 0:
                    continue
                if not (2 * d * x0 / m).is_integral():
                    continue
                delta = d * x0 * x0 / m
                if (delta - R(D2)).sign() > 0:
                    continue
                if D1 is not None and (delta - R(D1)).sign() <= 0:
                    continue
                N = m + d * x0 * x0
                for xs in sorted_reps(R, N, n, None, ok):
                    r = [x0] + list(xs)
                    if not gcd_list(r, R).is_unit():
                        continue
                    assert bil(self.G, r, r) == m and is_root(self.G, r)
                    out.append((delta, m, tuple(r)))
        return out


class _Timeout(Exception):
    pass


def _cmp(a, b):
    return (a[0] - b[0]).sign()


def vinberg_diag(d, n: int, Delta0: Fr = Fr(1, 4), Delta_max: Fr = Fr(10 ** 6),
                 max_roots: int = 400, time_limit: Optional[float] = None) -> Dict:
    """As vinbergn.vinberg_n for G = diag(-d, 1^n), v0 = e0. Returns dict(status, roots,
    n_start, graph, coxiter, Delta, secs | reason)."""
    L = DiagLattice(d, n)
    G = L.G
    t0 = _time.time()
    L.check_stabiliser()
    acc = L.stab_roots()
    n_start = len(acc)
    lo, Delta = None, Fr(Delta0)
    last_check = -1
    while Delta <= Delta_max:
        try:
            # the slice is abandoned unfinished at the deadline; the roots accepted so far
            # (all from completed slices) are still a prefix of the accepted sequence
            cands = sorted(L.candidates(lo, Delta, None if time_limit is None else t0 + time_limit),
                           key=cmp_to_key(_cmp))
        except _Timeout:
            return dict(status="undetermined", roots=acc, n_start=n_start, Delta=lo,
                        reason="time_limit")
        i = 0
        while i < len(cands):
            j = i
            while j < len(cands) and cands[j][0] == cands[i][0]:
                j += 1
            batch = [list(c[2]) for c in cands[i:j]]
            surv = [r for r in batch if all(bil(G, a, r).sign() <= 0 for a in acc)]
            for a in range(len(surv)):
                for b in range(a + 1, len(surv)):
                    if bil(G, surv[a], surv[b]).sign() > 0:
                        raise AssertionError("same-batch obtuse pair")
            acc.extend(surv)
            if len(acc) > max_roots:
                return dict(status="undetermined", roots=acc, n_start=n_start, Delta=Delta,
                            reason="max_roots")
            if surv and len(acc) > n and len(acc) != last_check:
                last_check = len(acc)
                graph = coxiter_graph(G, acc)
                cx = coxiter(graph)
                if cx["finite_covolume"] == "yes":
                    return dict(status="reflective", roots=acc, n_start=n_start, graph=graph,
                                coxiter=cx, Delta=Delta, secs=round(_time.time() - t0, 1))
            i = j
        if time_limit is not None and _time.time() - t0 > time_limit:
            return dict(status="undetermined", roots=acc, n_start=n_start, Delta=Delta,
                        reason="time_limit")
        lo, Delta = Delta, Delta * 2
    return dict(status="undetermined", roots=acc, n_start=n_start, Delta=Delta,
                reason="Delta_max")
