"""Vinberg's algorithm (Bugaenko's version for totally real fields), rank 3, exact.

Lattice: (O^3, G), G admissible (signature (2,1) at id, positive definite at sigma).
Roots: primitive r, Q(r) = m totally positive, 2 G r in m O^3 (so r lies in the
sublattice L_m = O^3 ∩ (m/2) G^-1 O^3, on which norm-m roots are enumerated); m runs over canonical
representatives of the totally positive divisors of 2 det G modulo unit squares, so
each mirror carries exactly one root pair +-r of each listed norm it supports.

Control vector v0 (timelike at id). The distance of a root is
    delta(r) = (r.v0)^2 / (m |v0^2|)    ( = sinh^2 d(v0, H_r) ).
For delta(r) <= Delta:  H(r) := Q(r) - 2 (r.v0)^2 / Q(v0) = m (1 + 2 delta) at id
(H is the positive majorant at v0) and Q(r) = sigma(m) at sigma. So r is a lattice
point of the restriction of scalars Z^6 with
    T(x) = H_id(x)/Ci + Q_sigma(x)/Cs <= 2,  Ci = m(1+2Delta), Cs = sigma(m).
Rigour: T has irrational entries. We build a rational form T'' with T'' <= T on all
of R^6 (rational approximation of sqrt(disc) to 2^-200, minus an explicit diagonal
margin; then rounding down to a 2^-48 grid with a diagonally dominant correction),
enumerate {T'' <= 2} exactly (zphi.definite.short_vectors), and test every candidate
exactly in K. Floats are used only to choose an LLL basis (any unimodular basis is
valid) and to order candidates before exact tie-breaking.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from functools import cmp_to_key
from math import isqrt
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

from .definite import short_vectors, cross, is_root as _is_root
from .linalg import (Mat, Vec, bil, det, inv, mat_vec, mat_mul, transpose, hnf_basis,
                     is_integral_mat)


def json_key(x):
    import json
    return json.dumps(x)
from .ring import El, Ring, gcd_list, tp_divisors
from .boxes import gammas

PREC = 200  # bits for the rational approximation of sqrt(disc)


# ------------------------------------------------------- restriction of scalars

def _sqrt_bounds(disc: int, prec: int = PREC) -> Tuple[Fr, Fr]:
    """s_lo < sqrt(disc) < s_hi, s_hi - s_lo = 2^-prec."""
    S = 1 << prec
    r = isqrt(disc * S * S)
    return Fr(r, S), Fr(r + 1, S)


def _emb_val(z: El, s: Fr) -> Fr:
    """Value of z at the embedding w -> (c1 + s)/2 (s ~ +-sqrt(disc))."""
    R = z.R
    if R.D == 1:
        return Fr(z.a, z.n)
    w = (R.c1 + s) / 2
    return (z.a + z.b * w) / z.n


def _forms_exact(G: Mat, v0: Vec):
    """6x6 matrices A, B over K with, for y in Z^6 and x = M y (x_j = a_j + b_j w):
        H_id(x) = id(y^T A y),   Q_sigma(x) = sigma(y^T B y),
    where H = G - 2 (G v0)(G v0)^T / Q(v0) and B = M^T G M. Exact in K."""
    R = G[0][0].R
    Gv = mat_vec(G, v0)
    q0 = bil(G, v0, v0)
    H = [[G[i][j] - 2 * Gv[i] * Gv[j] / q0 for j in range(3)] for i in range(3)]
    M = [[R.zero] * 6 for _ in range(3)]
    for j in range(3):
        M[j][2 * j] = R.one
        M[j][2 * j + 1] = R.w

    def pull(X):
        return [[sum((M[i][p] * X[i][j] * M[j][q] for i in range(3) for j in range(3)),
                     R.zero) for q in range(6)] for p in range(6)]

    return pull(H), pull(G)


def _lower_form(G: Mat, v0: Vec, Ci: Fr, Cs: Fr, prec: int = PREC):
    """Rational T_lo with T_lo(y) <= T(y) := id(y^T A y)/Ci + sigma(y^T B y)/Cs for all
    y in R^6 (A, B from _forms_exact).

    Rigour: each entry T_pq(s) = emb(A_pq, s)/Ci + emb(B_pq, -s)/Cs is an affine
    function of s, and the true value is at s* = sqrt(disc) in [s_lo, s_hi]. With
    T_lo := T(s_lo) - E, the error e_pq := |T_pq(s_hi) - T_pq(s_lo)| bounds
    |T_pq(s*) - T_pq(s_lo)| (affine), and y^T (T(s*) - T(s_lo)) y >= -sum_p y_p^2
    sum_q e_pq (|y_p y_q| <= (y_p^2 + y_q^2)/2). So subtracting sum_q e_pq from the
    p-th diagonal entry gives a lower bound."""
    R = G[0][0].R
    if R.D == 1:
        raise NotImplementedError("Z: use a 3-dim enumeration")
    A, B = _forms_exact(G, v0)
    s_lo, s_hi = _sqrt_bounds(R.disc, prec)

    def T(s):
        return [[_emb_val(A[p][q], s) / Ci + _emb_val(B[p][q], -s) / Cs for q in range(6)]
                for p in range(6)]

    Tl, Th = T(s_lo), T(s_hi)
    e = [[abs(Th[p][q] - Tl[p][q]) for q in range(6)] for p in range(6)]
    return [[Tl[p][q] - (sum(e[p]) if p == q else 0) for q in range(6)] for p in range(6)]


def _lll_float(T) -> List[List[int]]:
    """Unimodular U (columns) making T well-conditioned (float LLL; correctness does
    not depend on it)."""
    A = np.array([[float(x) for x in row] for row in T])
    n = A.shape[0]
    U = np.eye(n, dtype=object)
    B = A.copy()
    Ui = [[int(i == j) for j in range(n)] for i in range(n)]

    def gso(B):
        mu = np.zeros((n, n))
        Bs = np.zeros(n)
        for i in range(n):
            for j in range(i):
                mu[i][j] = (B[i][j] - sum(mu[j][k] * mu[i][k] * Bs[k] for k in range(j))) / Bs[j]
            Bs[i] = B[i][i] - sum(mu[i][k] ** 2 * Bs[k] for k in range(i))
        return mu, Bs

    def gram(Ui):
        M = np.array(Ui, dtype=float)
        return M.T @ A @ M

    k = 1
    it = 0
    while k < n and it < 10000:
        it += 1
        B = gram(Ui)
        mu, Bs = gso(B)
        for j in range(k - 1, -1, -1):
            c = int(round(mu[k][j]))
            if c:
                for r in range(n):
                    Ui[r][k] -= c * Ui[r][j]
                B = gram(Ui)
                mu, Bs = gso(B)
        if Bs[k] >= (0.75 - mu[k][k - 1] ** 2) * Bs[k - 1]:
            k += 1
        else:
            for r in range(n):
                Ui[r][k], Ui[r][k - 1] = Ui[r][k - 1], Ui[r][k]
            k = max(k - 1, 1)
    return Ui


def _round_down(T, bits=48):
    """Rational T'' on a 2^-bits grid with T'' <= T (as quadratic forms)."""
    S = 1 << bits
    n = len(T)
    out = [[Fr(round(T[p][q] * S), S) for q in range(n)] for p in range(n)]
    # T - out = E with |E_pq| <= 1/(2S); subtract n/S on the diagonal: then
    # T - T'' = E + (n/S) I is diagonally dominant with positive diagonal, hence PSD.
    for p in range(n):
        out[p][p] -= Fr(n, S)
    return out


def _is_pd(T) -> bool:
    from .definite import _ldl
    q = _ldl(T) if all(T[i][i] > 0 for i in range(len(T))) else None
    return q is not None and all(q[i][i] > 0 for i in range(len(T)))


def _pivots(T):
    from .definite import _ldl
    q = _ldl(T)
    return [q[i][i] for i in range(len(T))]


def _lll_exact(T, max_rounds: int = 12) -> List[List[int]]:
    """Unimodular U making the rational PD form T well-conditioned. Repeated exact
    integer LLL on round(S * U^T T U), with S chosen from the smallest exact LDL pivot
    of the current form, until the exact pivots of U^T T U satisfy the Lovasz-type
    bound d_{k} >= d_{k-1}/4 (or max_rounds). Any unimodular U is valid for the
    enumeration; only speed depends on the reduction."""
    from .definite import lll_gram
    n = len(T)
    U = [[int(i == j) for j in range(n)] for i in range(n)]

    def conj(U):
        return [[sum(U[p][a] * T[p][q] * U[q][b] for p in range(n) for q in range(n))
                 for b in range(n)] for a in range(n)]

    Tc = T
    for _ in range(max_rounds):
        d = _pivots(Tc)
        if all(d[k] * 4 >= d[k - 1] for k in range(1, n)):
            break
        dmin = min(d)
        k = max(0, 40 - (dmin.numerator.bit_length() - dmin.denominator.bit_length()))
        while True:
            S = 1 << k
            Ti = [[round(Tc[p][q] * S) for q in range(n)] for p in range(n)]
            if _is_pd(Ti):
                break
            k += 20
        V = lll_gram(Ti)
        U = [[sum(U[i][j] * V[j][c] for j in range(n)) for c in range(n)] for i in range(n)]
        Tc = conj(U)
    return U


def _round_down_pd(T):
    """_round_down with the grid refined until the result is positive definite (it is
    a lower bound for T at every precision)."""
    d = min(_pivots(T))
    bits = max(48, 48 - (d.numerator.bit_length() - d.denominator.bit_length()))
    while True:
        TL = _round_down(T, bits)
        if _is_pd(TL):
            return TL
        bits *= 2
        if bits > 4096:
            raise ValueError("form not positive definite at 2^-4096 resolution")


def _int_norm_forms(Gm: Mat, U):
    """Integer 6x6 matrices N0, N1 and den > 0 with, for z in Z^6 and the vector
    x = sum_j (y_2j + y_2j+1 w) e_j, y = U z:   Q(x) = (z^T N0 z + (z^T N1 z) w) / den.
    Exact (from the Gram entries in K)."""
    from math import lcm
    R = Gm[0][0].R
    c = [R.one, R.w]
    B = [[Gm[k // 2][l // 2] * c[k % 2] * c[l % 2] for l in range(6)] for k in range(6)]
    den = 1
    for row in B:
        for x in row:
            den = lcm(den, x.n)
    A0 = [[B[k][l].a * (den // B[k][l].n) for l in range(6)] for k in range(6)]
    A1 = [[B[k][l].b * (den // B[k][l].n) for l in range(6)] for k in range(6)]

    def conj(A):
        return [[sum(U[p][a] * A[p][q] * U[q][b] for p in range(6) for q in range(6))
                 for b in range(6)] for a in range(6)]

    return conj(A0), conj(A1), den


# ------------------------------------------------------------- the lattice

class Lattice:
    def __init__(self, G: Mat, v0: Vec):
        self.G = G
        self.R = G[0][0].R
        self.v0 = list(v0)
        self.Q0 = bil(G, v0, v0)
        if self.Q0.sign() >= 0:
            raise ValueError("v0 must be timelike at id")
        self.det = det(G)
        self.norms = tp_divisors(2 * self.det)
        self._cache: Dict[Tuple, List] = {}
        self._sub: Dict = {}

    def _sublattice(self, m: El):
        """Basis Bm (columns) of L_m = O^3 ∩ (m/2) G^-1 O^3, which contains every root
        of norm m (2 G r in m O^3); with Gram Bm^T G Bm and v0 in Bm-coordinates.
        L_m is the dual (w.r.t. the dot product) of O^3 + (2/m) G O^3."""
        key = m.to_json() if hasattr(m, "to_json") else repr(m)
        key = json_key(key)
        if key not in self._sub:
            R = self.R
            n = len(self.G)
            gens = [[R.one if i == j else R.zero for i in range(n)] for j in range(n)]
            gens += [[2 * self.G[i][j] / m for i in range(n)] for j in range(n)]
            P = hnf_basis(gens)
            Bm = transpose(inv(P))
            assert is_integral_mat(Bm)
            Gm = mat_mul(mat_mul(transpose(Bm), self.G), Bm)
            self._sub[key] = (Bm, Gm, mat_vec(inv(Bm), self.v0))
        return self._sub[key]

    def is_root(self, r: Vec) -> bool:
        return _is_root(self.G, r)

    def distance(self, r: Vec, m: El) -> El:
        t = bil(self.G, r, self.v0)
        return t * t / (m * (-self.Q0))

    def roots_upto(self, Delta: Fr) -> List[Tuple[El, El, Tuple]]:
        """All (delta, m, r) with r a root of norm m in self.norms, (r, v0) <= 0, and
        delta(r) <= Delta (exact at id). Roots with (r, v0) = 0 are returned with
        both signs."""
        Delta = Fr(Delta)
        out = []
        R = self.R
        for m in self.norms:
            sb = _sqrt_bounds(R.disc)
            mi = max(_emb_val(m, x) for x in sb)          # >= id(m)
            ms = max(_emb_val(m.conj(), x) for x in sb)   # >= sigma(m)
            Ci = mi * (1 + 2 * Delta) * (1 + Fr(1, 10 ** 12))
            Cs = ms * (1 + Fr(1, 10 ** 12))
            Bm, Gm, v0m = self._sublattice(m)
            prec = PREC
            T = _lower_form(Gm, v0m, Ci, Cs, prec)
            while not _is_pd(T):
                prec *= 2
                if prec > 1 << 14:
                    raise ValueError("lower form not positive definite")
                T = _lower_form(Gm, v0m, Ci, Cs, prec)
            U = _lll_exact(T)
            TU = [[sum(U[p][a] * T[p][q] * U[q][b] for p in range(6) for q in range(6))
                   for b in range(6)] for a in range(6)]
            TL = _round_down_pd(TU)
            N0, N1, den = _int_norm_forms(Gm, U)
            ta, tb = m.a * den, m.b * den      # Q(r) = m  <=>  (zN0z, zN1z) m.n = (ta, tb)
            mn = m.n
            rng6 = range(6)
            for z in short_vectors(TL, 2):
                if not any(z):
                    continue
                # exact integer pre-filter on the norm (no field arithmetic)
                N0z = [sum(N0[p][q] * z[q] for q in rng6) for p in rng6]
                if sum(z[p] * N0z[p] for p in rng6) * mn != ta:
                    continue
                N1z = [sum(N1[p][q] * z[q] for q in rng6) for p in rng6]
                if sum(z[p] * N1z[p] for p in rng6) * mn != tb:
                    continue
                y = [sum(U[p][k] * z[k] for k in range(6)) for p in range(6)]
                w = [R(y[2 * j], y[2 * j + 1]) for j in range(3)]
                r = mat_vec(Bm, w)
                if bil(self.G, r, r) != m:
                    continue
                t = bil(self.G, r, self.v0)
                if t.sign() > 0:
                    continue
                if not self.is_root(r):
                    continue
                d = t * t / (m * (-self.Q0))
                if (d - R(Delta)).sign() <= 0:
                    out.append((d, m, tuple(r)))
        return out


# --------------------------------------------------------- polygon geometry

def vertex_vector(G: Mat, r: Vec, s: Vec) -> Vec:
    """p with p.r = p.s = 0: p^T G r = (Gr) . p (Euclidean), so p = (G r) x (G s)."""
    return cross(mat_vec(G, r), mat_vec(G, s))


def coxeter_m(G: Mat, r: Vec, s: Vec) -> Optional[int]:
    """m if r, s meet at angle pi/m (4cos^2 = gamma(m), r.s <= 0); None if they do not
    meet (|cos| >= 1)."""
    R = G[0][0].R
    rs = bil(G, r, s)
    c = 4 * rs * rs / (bil(G, r, r) * bil(G, s, s))
    if (c - 4).sign() >= 0:
        return None
    for m, g in gammas(R).items():
        if c == g:
            if rs.sign() > 0:
                raise ValueError("obtuse pair")
            return m
    raise ValueError(f"non-Coxeter angle 4cos^2 = {c}")


def polygon(G: Mat, roots: Sequence[Vec], v0: Vec):
    """For accepted roots (all with r.v0 <= 0, pairwise non-obtuse), the vertices of
    P = {x : r.x <= 0 for all r} (in the cone of v0).

    Returns (compact, cycle) where cycle is the cyclic order of root indices if P is a
    compact polygon with every accepted root a side (and every vertex angle Coxeter),
    else (False, None)."""
    n = len(roots)
    on_wall = {i: [] for i in range(n)}
    verts = []
    for i in range(n):
        for j in range(i + 1, n):
            m = coxeter_m(G, roots[i], roots[j])
            if m is None:
                continue
            p = vertex_vector(G, roots[i], roots[j])
            if bil(G, p, v0).sign() > 0:
                p = [-x for x in p]
            if not bil(G, p, p).sign() < 0:
                continue
            ok = True
            for k in range(n):
                if k in (i, j):
                    continue
                if bil(G, roots[k], p).sign() > 0:
                    ok = False
                    break
            if ok:
                verts.append((i, j, m))
                on_wall[i].append(j)
                on_wall[j].append(i)
    if n < 3 or any(len(v) != 2 for v in on_wall.values()):
        return False, None
    # follow the cycle
    cyc = [0]
    prev, cur = None, 0
    while True:
        a, b = on_wall[cur]
        nxt = a if a != prev else b
        if nxt == 0:
            break
        cyc.append(nxt)
        prev, cur = cur, nxt
        if len(cyc) > n:
            return False, None
    if len(cyc) != n:
        return False, None
    return True, cyc


# ------------------------------------------------------------ the algorithm

def _cmp(a, b):
    return (a[0] - b[0]).sign()


def vinberg(G: Mat, start: Sequence[Vec], Delta0: Fr = Fr(1), Delta_max: Fr = Fr(10 ** 6),
            max_roots: int = 60, orient: Optional[Vec] = None,
            time_limit: Optional[float] = None) -> Dict:
    """Vinberg's algorithm with v0 = the vertex r_1^⊥ ∩ r_2^⊥ of the two given simple
    roots `start` (they must meet at a Coxeter angle and be the simple roots of the
    stabiliser of v0; this is asserted by counting mirrors through v0).

    `orient`: a root that must be a wall of the same chamber (r.v0 < 0 fixes the
    sheet of v0, i.e. which of the two opposite sectors at the vertex is built).
    Without it the sheet is arbitrary (the result is then a chamber of the same
    reflection group, congruent but possibly with other root representatives).

    Returns dict(status = 'reflective' | 'undetermined', roots, cycle, Delta)."""
    from .definite import mirrors_through_vertex
    r1, r2 = list(start[0]), list(start[1])
    m12 = coxeter_m(G, r1, r2)
    if m12 is None:
        raise ValueError("start roots do not meet")
    if mirrors_through_vertex(G, r1, r2) != m12:
        raise ValueError("start roots are not simple at their vertex")
    v0 = vertex_vector(G, r1, r2)
    if orient is not None:
        sgn = bil(G, list(orient), v0).sign()
        if sgn == 0:
            raise ValueError("orient root passes through the start vertex")
        if sgn > 0:
            v0 = [-x for x in v0]
    # orient v0 so that r1.v0... v0 is orthogonal to r1, r2; choose the sheet with
    # a fixed sign convention: any timelike v0 works (the chamber is in its cone)
    return _vinberg_loop(G, v0, [r1, r2], Delta0, Delta_max, max_roots, time_limit,
                         interior=False)


def vinberg_interior(G: Mat, v0: Vec, Delta0: Fr = Fr(1), Delta_max: Fr = Fr(10 ** 6),
                     max_roots: int = 200, time_limit: Optional[float] = None) -> Dict:
    """Vinberg's algorithm from a control vector v0 in the interior of a chamber (no
    initial roots). Valid when v0 lies on no mirror: this is checked, since a root
    with r.v0 = 0 is enumerated at distance 0 and then raises."""
    return _vinberg_loop(G, v0, [], Delta0, Delta_max, max_roots, time_limit,
                         interior=True)


def _vinberg_loop(G, v0, acc, Delta0, Delta_max, max_roots, time_limit, interior):
    L = Lattice(G, v0)
    acc = [list(r) for r in acc]
    Delta = Fr(Delta0)
    done = None   # exact distance already processed (El) or None
    import time as _time
    t_start = _time.time()
    while Delta <= Delta_max:
        if time_limit is not None and _time.time() - t_start > time_limit:
            return {"status": "undetermined", "roots": acc, "cycle": None,
                    "Delta": Delta, "reason": "time_limit"}
        allc = L.roots_upto(Delta)
        if interior and any(c[0].is_zero() for c in allc):
            raise ValueError("v0 lies on a mirror")
        cands = [c for c in allc if not c[0].is_zero()]
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
                return {"status": "undetermined", "roots": acc, "cycle": None,
                        "Delta": Delta, "reason": "max_roots"}
            if surv and len(acc) >= 3:
                comp, cyc = polygon(G, acc, _interior_hint(G, acc, v0))
                if comp:
                    return {"status": "reflective", "roots": acc, "cycle": cyc,
                            "Delta": Delta}
            done = cands[i][0]
            i = j
        Delta *= 4
    return {"status": "undetermined", "roots": acc, "cycle": None, "Delta": Delta,
            "reason": "Delta_max"}


def _interior_hint(G, acc, v0):
    """A timelike vector in the cone of the chamber, used only to orient vertex
    vectors (v0 itself lies on the boundary; any vector of the same sheet works)."""
    return v0


# ------------------------------------------------------ certificate check

def check_polygon(G: Mat, roots: Sequence[Vec]) -> Dict:
    """Verify that `roots` (cyclically ordered) are the simple roots of a chamber of
    the reflection group of (O^3, G), and that the chamber is a compact Coxeter polygon:
      1. each is a root; consecutive pairs meet at a Coxeter angle pi/m;
      2. the vertices p_i = R_i ∩ R_{i+1} lie strictly inside all other half-planes,
         so P = ∩ {r_i . x <= 0} is the compact polygon with these sides;
      3. no mirror of the lattice meets the interior of P: every root r with
         delta(r, v) <= max_i sinh^2 d(v, p_i) (v = an interior point) is checked to
         have all vertices on one side (a crossing mirror separates v from a vertex
         and so is at most that far from v).
    Returns dict(ok, angles, issues)."""
    R = G[0][0].R
    n = len(roots)
    issues = []
    for r in roots:
        if not _is_root(G, list(r)):
            issues.append(f"not a root: {r}")
    angles, verts = [], []
    for i in range(n):
        a, b = list(roots[i]), list(roots[(i + 1) % n])
        try:
            m = coxeter_m(G, a, b)
        except ValueError as e:
            issues.append(str(e))
            m = None
        if m is None:
            issues.append(f"r{i+1}, r{(i+2-1)%n+1} do not meet")
            angles.append(None)
            continue
        angles.append(m)
        verts.append(vertex_vector(G, a, b))
    if issues:
        return {"ok": False, "angles": angles, "issues": issues}
    # orient vertices into one sheet: use the sign of r_k . p for a non-incident k
    v_int = None
    oriented = []
    for i, p in enumerate(verts):
        k = (i + 2) % n
        if bil(G, list(roots[k]), p).sign() > 0:
            p = [-x for x in p]
        oriented.append(p)
        for k2 in range(n):
            if k2 in (i, (i + 1) % n):
                continue
            if bil(G, list(roots[k2]), p).sign() >= 0:
                issues.append(f"vertex {i+1} not strictly inside half-plane {k2+1}")
        if bil(G, p, p).sign() >= 0:
            issues.append(f"vertex {i+1} not timelike")
    if issues:
        return {"ok": False, "angles": angles, "issues": issues}
    # interior point: sum of the vertices (in the same sheet, hence timelike, inside)
    v = [sum((p[j] for p in oriented), R.zero) for j in range(3)]
    q = bil(G, v, v)
    # max_i sinh^2 d(v, p_i) = (v.p)^2/(v^2 p^2) - 1
    Delta_el = max(((bil(G, v, p) ** 2 / (q * bil(G, p, p)) - 1) for p in oriented),
                   key=lambda z: float(z))
    for p in oriented:  # exact max
        d = bil(G, v, p) ** 2 / (q * bil(G, p, p)) - 1
        if (d - Delta_el).sign() > 0:
            Delta_el = d
    Delta = Fr(int(float(Delta_el)) + 1)
    while (Delta_el - Delta_el.R(Delta)).sign() > 0:   # exact: Delta >= Delta_el
        Delta += 1
    L = Lattice(G, v)
    crossing = 0
    for d, m, r in L.roots_upto(Delta):
        sides = [bil(G, list(r), p).sign() for p in oriented]
        if any(s > 0 for s in sides) and any(s < 0 for s in sides):
            crossing += 1
            issues.append(f"mirror of {r} crosses P")
            break
    return {"ok": not issues, "angles": angles, "issues": issues,
            "Delta": str(Delta)}
