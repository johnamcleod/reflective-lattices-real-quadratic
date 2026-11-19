"""Vinberg's algorithm (Bugaenko's version for totally real quadratic fields) in any rank
n >= 3, for an arbitrary admissible Gram matrix G over O (signature (n-1, 1) at id,
positive definite at sigma). Exact; D1 stage 2 (ROADMAP).

This is the rank-3 enumeration of zphi.vinberg, written for general n:
  * roots: primitive r, (r, r) = m totally positive, 2 G r in m O^n; m runs over the
    totally positive divisors of 2 det G modulo unit squares (r primitive and m | 2 G r
    give m | 2 det G r, hence m | 2 det G);
  * a root of norm m lies in L_m = O^n ∩ (m/2) G^-1 O^n; for delta(r) = (r, v0)^2 /
    (m |(v0, v0)|) <= Delta it is a lattice point of the restriction of scalars Z^{2n}
    with T(x) = H_id(x)/Ci + Q_sigma(x)/Cs <= 2 (H the positive majorant at v0), which is
    enumerated exactly on a rational lower bound of T (as in zphi.vinberg);
  * the stabiliser of v0: the roots with (r, v0) = 0 form a finite root system; its
    simple roots (for the Weyl chamber containing a generic direction u in v0^perp) are
    obtained by the same acceptance rule, ordered by (r, u)^2 / (r, r);
  * then roots by increasing delta, accepted when (r, a) <= 0 for every accepted a;
  * termination: after each batch that adds roots, the Coxeter diagram of the accepted
    roots is given to CoxIter; the algorithm stops when CoxIter reports finite covolume.
    The accepted roots are then exactly the walls of the chamber (Vinberg). Over a
    field != Q with sigma(G) definite the form is anisotropic, so the polytope must be
    compact: CoxIter must also report cocompact.

The CoxIter verdict is the only non-exact-arithmetic ingredient (it is a combinatorial
test on the Coxeter diagram, which is computed exactly here).
"""
from __future__ import annotations

import pathlib
import random
import subprocess
import time as _time
from fractions import Fraction as Fr
from functools import cmp_to_key
from math import lcm
from typing import Dict, List, Optional, Sequence

from .definite import short_vectors, is_root as _is_root
from .linalg import Mat, Vec, bil, det, inv, mat_vec, mat_mul, transpose, hnf_basis, is_integral_mat
from .ring import tp_divisors
from .boxes import gammas
from .vinberg import (PREC, _sqrt_bounds, _emb_val, _is_pd, _lll_exact, _round_down_pd,
                      json_key)

COXITER = pathlib.Path(__file__).resolve().parent.parent / "tools/src/CoxIter/build/coxiter"


# ------------------------------------------------------- restriction of scalars (rank n)

def _forms_exact_n(G: Mat, v0: Vec):
    """2n x 2n matrices A, B over K: for y in Z^{2n}, x = M y (x_j = y_2j + y_2j+1 w),
    H_id(x) = id(y^T A y), Q_sigma(x) = sigma(y^T B y); H = G - 2 (G v0)(G v0)^T / Q(v0)."""
    R = G[0][0].R
    n = len(G)
    Gv = mat_vec(G, v0)
    q0 = bil(G, v0, v0)
    H = [[G[i][j] - 2 * Gv[i] * Gv[j] / q0 for j in range(n)] for i in range(n)]
    c = [R.one, R.w]

    def pull(X):
        return [[X[p // 2][q // 2] * c[p % 2] * c[q % 2] for q in range(2 * n)]
                for p in range(2 * n)]

    return pull(H), pull(G)


def _lower_form_n(G: Mat, v0: Vec, Ci: Fr, Cs: Fr, prec: int = PREC):
    """Rational T_lo <= T on R^{2n}: as zphi.vinberg._lower_form (affine in s, diagonal
    margin)."""
    R = G[0][0].R
    A, B = _forms_exact_n(G, v0)
    N = len(A)
    s_lo, s_hi = _sqrt_bounds(R.disc, prec)

    def T(s):
        return [[_emb_val(A[p][q], s) / Ci + _emb_val(B[p][q], -s) / Cs for q in range(N)]
                for p in range(N)]

    Tl, Th = T(s_lo), T(s_hi)
    e = [[abs(Th[p][q] - Tl[p][q]) for q in range(N)] for p in range(N)]
    return [[Tl[p][q] - (sum(e[p]) if p == q else 0) for q in range(N)] for p in range(N)]


def _int_norm_forms_n(Gm: Mat, U):
    """Integer N0, N1, den: Q(x) = (z^T N0 z + (z^T N1 z) w) / den for x from y = U z."""
    R = Gm[0][0].R
    n = len(Gm)
    N = 2 * n
    c = [R.one, R.w]
    B = [[Gm[k // 2][l // 2] * c[k % 2] * c[l % 2] for l in range(N)] for k in range(N)]
    den = 1
    for row in B:
        for x in row:
            den = lcm(den, x.n)
    A0 = [[B[k][l].a * (den // B[k][l].n) for l in range(N)] for k in range(N)]
    A1 = [[B[k][l].b * (den // B[k][l].n) for l in range(N)] for k in range(N)]

    def conj(A):
        return [[sum(U[p][a] * A[p][q] * U[q][b] for p in range(N) for q in range(N))
                 for b in range(N)] for a in range(N)]

    return conj(A0), conj(A1), den


class LatticeN:
    def __init__(self, G: Mat, v0: Vec):
        self.G = G
        self.R = G[0][0].R
        self.n = len(G)
        self.v0 = list(v0)
        self.Q0 = bil(G, v0, v0)
        if self.Q0.sign() >= 0:
            raise ValueError("v0 must be timelike at id")
        self.norms = tp_divisors(2 * det(G))
        self._sub: Dict = {}
        self._lll: Dict = {}

    def _sublattice(self, m):
        key = json_key(m.to_json())
        if key not in self._sub:
            R, n = self.R, self.n
            gens = [[R.one if i == j else R.zero for i in range(n)] for j in range(n)]
            gens += [[2 * self.G[i][j] / m for i in range(n)] for j in range(n)]
            P = hnf_basis(gens)
            Bm = transpose(inv(P))
            assert is_integral_mat(Bm)
            Gm = mat_mul(mat_mul(transpose(Bm), self.G), Bm)
            self._sub[key] = (Bm, Gm, mat_vec(inv(Bm), self.v0))
        return self._sub[key]

    def roots_upto(self, Delta: Fr):
        """All (delta, m, r): r a root of norm m, (r, v0) <= 0, delta(r) <= Delta.
        Roots with (r, v0) = 0 come with both signs."""
        Delta = Fr(Delta)
        R, n = self.R, self.n
        N = 2 * n
        out = []
        for m in self.norms:
            sb = _sqrt_bounds(R.disc)
            mi = max(_emb_val(m, x) for x in sb)
            ms = max(_emb_val(m.conj(), x) for x in sb)
            Ci = mi * (1 + 2 * Delta) * (1 + Fr(1, 10 ** 12))
            Cs = ms * (1 + Fr(1, 10 ** 12))
            Bm, Gm, v0m = self._sublattice(m)
            prec = PREC
            T = _lower_form_n(Gm, v0m, Ci, Cs, prec)
            while not _is_pd(T):
                prec *= 2
                if prec > 1 << 14:
                    raise ValueError("lower form not positive definite")
                T = _lower_form_n(Gm, v0m, Ci, Cs, prec)
            ck = json_key(m.to_json())
            U = _lll_exact(T, U0=self._lll.get(ck))
            self._lll[ck] = U
            TU = [[sum(U[p][a] * T[p][q] * U[q][b] for p in range(N) for q in range(N))
                   for b in range(N)] for a in range(N)]
            TL = _round_down_pd(TU)
            N0, N1, den = _int_norm_forms_n(Gm, U)
            ta, tb, mn = m.a * den, m.b * den, m.n
            rng = range(N)
            for z in short_vectors(TL, 2):
                if not any(z):
                    continue
                N0z = [sum(N0[p][q] * z[q] for q in rng) for p in rng]
                if sum(z[p] * N0z[p] for p in rng) * mn != ta:
                    continue
                N1z = [sum(N1[p][q] * z[q] for q in rng) for p in rng]
                if sum(z[p] * N1z[p] for p in rng) * mn != tb:
                    continue
                y = [sum(U[p][k] * z[k] for k in rng) for p in rng]
                w = [R(y[2 * j], y[2 * j + 1]) for j in range(n)]
                r = mat_vec(Bm, w)
                if bil(self.G, r, r) != m:
                    continue
                t = bil(self.G, r, self.v0)
                if t.sign() > 0:
                    continue
                if not _is_root(self.G, r):
                    continue
                d = t * t / (m * (-self.Q0))
                if (d - R(Delta)).sign() <= 0:
                    out.append((d, m, tuple(r)))
        return out


# ------------------------------------------------------------- Coxeter diagram

def coxeter_weight(G: Mat, r: Vec, s: Vec) -> int:
    """CoxIter weight of the pair: m (angle pi/m), 2 = orthogonal (no edge), 0 = parallel,
    1 = ultraparallel (dotted). Requires (r, s) <= 0."""
    R = G[0][0].R
    rs = bil(G, r, s)
    if rs.sign() > 0:
        raise ValueError("obtuse pair")
    if rs.is_zero():
        return 2
    c = 4 * rs * rs / (bil(G, r, r) * bil(G, s, s))
    d4 = (c - 4).sign()
    if d4 == 0:
        return 0
    if d4 > 0:
        return 1
    for m, g in gammas(R).items():
        if c == g:
            return m
    raise ValueError(f"non-Coxeter angle 4cos^2 = {c}")


def coxiter_graph(G: Mat, roots: Sequence[Vec]) -> str:
    k = len(roots)
    lines = [f"{k} {len(G) - 1}", "vertices labels: " + " ".join(str(i + 1) for i in range(k))]
    for i in range(k):
        for j in range(i + 1, k):
            w = coxeter_weight(G, roots[i], roots[j])
            if w != 2:
                lines.append(f"{i + 1} {j + 1} {w}")
    return "\n".join(lines) + "\n"


def coxiter(graph: str) -> Dict:
    import re
    p = subprocess.run([str(COXITER), "-c", "-fv"], input=graph, capture_output=True,
                       text=True, timeout=3600)
    grab = lambda pat: (re.search(pat, p.stdout) or [None, None])[1]
    return dict(cocompact=grab(r"Cocompact: (\w+)"),
                finite_covolume=grab(r"Finite covolume: (\w+)"))


# ------------------------------------------------------------- the algorithm

def _cmp(a, b):
    return (a[0] - b[0]).sign()


def stabiliser_simple_roots(G: Mat, zero_roots: Sequence[Vec], seed: int = 1) -> List[Vec]:
    """Simple roots of the finite reflection group generated by the roots orthogonal to
    v0 (given with both signs), for the Weyl chamber containing a generic direction u.
    Vinberg's rule in the spherical case: roots with (r, u) < 0, by increasing
    (r, u)^2 / (r, r), accepted when (r, a) <= 0 for all accepted a."""
    if not zero_roots:
        return []
    R = G[0][0].R
    n = len(G)
    rng = random.Random(seed)
    for _ in range(100):
        u = [R(rng.randint(-50, 50), rng.randint(-50, 50)) for _ in range(n)]
        vals = [bil(G, list(r), u) for r in zero_roots]
        if all(not v.is_zero() for v in vals):
            break
    else:
        raise ValueError("no generic direction found")
    neg = [(v * v / bil(G, list(r), list(r)), list(r)) for v, r in zip(vals, zero_roots)
           if v.sign() < 0]
    neg.sort(key=cmp_to_key(lambda a, b: (a[0] - b[0]).sign()))
    acc: List[Vec] = []
    for _, r in neg:
        if all(bil(G, a, r).sign() <= 0 for a in acc):
            acc.append(r)
    return acc


def vinberg_n(G: Mat, v0: Vec, Delta0: Fr = Fr(1, 4), Delta_max: Fr = Fr(10 ** 6),
              max_roots: int = 400, time_limit: Optional[float] = None) -> Dict:
    """Returns dict(status = 'reflective' | 'undetermined', roots, graph, coxiter, Delta,
    reason)."""
    L = LatticeN(G, v0)
    t0 = _time.time()
    zero = [list(c[2]) for c in L.roots_upto(Fr(0)) if c[0].is_zero()]
    acc = stabiliser_simple_roots(G, zero)
    n_start = len(acc)
    Delta = Fr(Delta0)
    done = None
    last_check = -1
    while Delta <= Delta_max:
        if time_limit is not None and _time.time() - t0 > time_limit:
            return dict(status="undetermined", roots=acc, n_start=n_start, Delta=Delta,
                        reason="time_limit")
        cands = [c for c in L.roots_upto(Delta) if not c[0].is_zero()]
        if done is not None:
            cands = [c for c in cands if (c[0] - done).sign() > 0]
        cands.sort(key=cmp_to_key(_cmp))
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
            if surv and len(acc) > len(G) - 1 and len(acc) != last_check:
                last_check = len(acc)
                graph = coxiter_graph(G, acc)
                cx = coxiter(graph)
                if cx["finite_covolume"] == "yes":
                    return dict(status="reflective", roots=acc, n_start=n_start,
                                graph=graph, coxiter=cx, Delta=Delta,
                                secs=round(_time.time() - t0, 1))
            done = cands[i][0]
            i = j
        if time_limit is not None and _time.time() - t0 > time_limit:
            return dict(status="undetermined", roots=acc, n_start=n_start, Delta=Delta,
                        reason="time_limit")
        Delta *= 2
    return dict(status="undetermined", roots=acc, n_start=n_start, Delta=Delta,
                reason="Delta_max")
