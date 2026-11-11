"""Exact short-vector enumeration (Fincke-Pohst) and roots of definite sublattices.

`short_vectors(T, bound)`: all z in Z^n with z^T T z <= bound for a positive definite
integer (or rational) matrix T. The LDL^T decomposition is exact (Fractions); integer
ranges are computed with a float estimate widened by 1 and every candidate is
re-tested exactly, so no vector is lost to rounding.

For an O-lattice (O = Z[sqrt2] or Z[phi]) with Gram Q totally positive definite, the
trace form Tr(Q) on the Z-basis (b_i, w b_i) is positive definite, and Q(v) = n
implies Tr(Q(v)) = Tr(n).
"""
from __future__ import annotations

from fractions import Fraction as Fr
from math import floor, ceil, sqrt, isqrt
from typing import Iterator, List, Sequence, Tuple

from .linalg import Mat, Vec, bil, det, mat_vec
from .ring import El, Ring, egcd, gcd_list, tp_divisors, tp_normalise


def _ldl(T):
    n = len(T)
    q = [[Fr(T[i][j]) for j in range(n)] for i in range(n)]
    # Fincke-Pohst form: Q(x) = sum_i q_ii (x_i + sum_{j>i} q_ij x_j)^2
    for i in range(n):
        for j in range(i + 1, n):
            q[j][i] = q[i][j]
            q[i][j] = q[i][j] / q[i][i]
        for k in range(i + 1, n):
            for l in range(k, n):
                q[k][l] = q[k][l] - q[k][i] * q[i][l]
    return q


def short_vectors(T, bound) -> Iterator[Tuple[int, ...]]:
    """All integer vectors z (including 0) with z^T T z <= bound, T positive definite.

    Pure integer arithmetic: with q = LDL^T coefficients (exact rationals) put over a
    common denominator D (Qd = D q), the Fincke-Pohst recursion
        Q(x) = sum_i q_ii (x_i - c_i)^2,  c_i = -sum_{j>i} q_ij x_j
    is run with every quantity scaled to an integer, and the range of x_i comes from
    |x_i - c_i| <= sqrt(R / q_ii) <= isqrt(floor(R / q_ii)) + 1. No floats."""
    from math import lcm
    n = len(T)
    q = _ldl(T)
    for i in range(n):
        if q[i][i] <= 0:
            raise ValueError("not positive definite")
    D = 1
    for i in range(n):
        for j in range(i, n):
            D = lcm(D, q[i][j].denominator)
    Qd = [[int(q[i][j] * D) if j >= i else 0 for j in range(n)] for i in range(n)]
    bound = Fr(bound)
    bd = bound.denominator
    D3 = D ** 3
    Rs0 = bound.numerator * D3        # R scaled by K = D^3 * bd
    x = [0] * n

    def rec(i, Rs):
        # C = D * (-c_i);  dD := (x_i - c_i) D = x_i D + C
        C = sum(Qd[i][j] * x[j] for j in range(i + 1, n))
        qii = Qd[i][i]
        # R / q_ii = (Rs / (D^3 bd)) / (qii / D) = Rs / (D^2 bd qii)
        s = isqrt(Rs // (D * D * bd * qii)) + 1
        # centre -C / D:  x_i in [floor(-C/D) - s, ceil(-C/D) + s]
        lo = (-C) // D - s
        hi = -((C) // D) + s
        for xi in range(lo, hi + 1):
            dD = xi * D + C
            rem = Rs - qii * dD * dD * bd
            if rem < 0:
                continue
            x[i] = xi
            if i == 0:
                yield tuple(x)
            else:
                yield from rec(i - 1, rem)
        x[i] = 0

    yield from rec(n - 1, Rs0)


def short_vectors_fraction(T, bound) -> Iterator[Tuple[int, ...]]:
    """Reference implementation (exact Fractions, float-guided ranges widened by 1);
    kept for testing short_vectors."""
    n = len(T)
    q = _ldl(T)
    for i in range(n):
        if q[i][i] <= 0:
            raise ValueError("not positive definite")
    bound = Fr(bound)
    x = [0] * n

    def rec(i, R):
        # centre c = -sum_{j>i} q_ij x_j
        c = -sum((q[i][j] * x[j] for j in range(i + 1, n)), Fr(0))
        t = R / q[i][i]
        s = sqrt(float(t)) if t > 0 else 0.0
        lo, hi = floor(float(c) - s) - 1, ceil(float(c) + s) + 1
        for xi in range(lo, hi + 1):
            d = xi - c
            rem = R - q[i][i] * d * d
            if rem < 0:
                continue
            x[i] = xi
            if i == 0:
                yield tuple(x)
            else:
                yield from rec(i - 1, rem)
        x[i] = 0

    yield from rec(n - 1, bound)


def lll_gram(T) -> List[List[int]]:
    """Exact LLL (delta = 3/4) on a positive definite integer Gram matrix T.

    Returns an integer matrix U (columns = new basis) with det U = +-1; U^T T U is
    LLL-reduced. Exact rational arithmetic throughout. Correctness of callers only
    needs U unimodular (asserted), not reducedness: reduction only speeds up
    Fincke-Pohst, whose output is mapped back through U."""
    n = len(T)
    U = [[int(i == j) for j in range(n)] for i in range(n)]

    def g(a, b):        # <u_a, u_b>_T
        return sum(U[i][a] * T[i][j] * U[j][b] for i in range(n) for j in range(n))

    def gso():
        mu = [[Fr(0)] * n for _ in range(n)]
        Bs = [Fr(0)] * n
        for i in range(n):
            for j in range(i):
                mu[i][j] = (Fr(g(i, j)) - sum((mu[j][k] * mu[i][k] * Bs[k] for k in range(j)),
                                              Fr(0))) / Bs[j]
            Bs[i] = g(i, i) - sum((mu[i][k] ** 2 * Bs[k] for k in range(i)), Fr(0))
        return mu, Bs

    k = 1
    while k < n:
        mu, Bs = gso()
        for j in range(k - 1, -1, -1):
            c = round(mu[k][j])
            if c:
                for r in range(n):
                    U[r][k] -= c * U[r][j]
                mu, Bs = gso()
        if Bs[k] >= (Fr(3, 4) - mu[k][k - 1] ** 2) * Bs[k - 1]:
            k += 1
        else:
            for r in range(n):
                U[r][k], U[r][k - 1] = U[r][k - 1], U[r][k]
            k = max(k - 1, 1)
    assert abs(_int_det(U)) == 1
    return U


def _int_det(M) -> int:
    """Exact determinant of a square integer matrix (Fraction elimination)."""
    A = [[Fr(x) for x in row] for row in M]
    n, d = len(A), Fr(1)
    for i in range(n):
        p = next((r for r in range(i, n) if A[r][i] != 0), None)
        if p is None:
            return 0
        if p != i:
            A[i], A[p] = A[p], A[i]
            d = -d
        d *= A[i][i]
        for r in range(i + 1, n):
            f = A[r][i] / A[i][i]
            for c in range(i, n):
                A[r][c] -= f * A[i][c]
    assert d.denominator == 1
    return int(d)


def short_vectors_reduced(T, bound) -> Iterator[Tuple[int, ...]]:
    """Same set as short_vectors(T, bound), enumerated on an LLL-reduced basis."""
    n = len(T)
    U = lll_gram(T)
    T2 = [[sum(U[i][a] * T[i][j] * U[j][b] for i in range(n) for j in range(n))
           for b in range(n)] for a in range(n)]
    for y in short_vectors(T2, bound):
        yield tuple(sum(U[i][a] * y[a] for a in range(n)) for i in range(n))


# ---------------------------------------------------- O-lattices, restriction

def trace_form(Q: Mat) -> List[List[int]]:
    """Integer Gram of Tr(Q) on the Z-basis (e_1, w e_1, ..., e_m, w e_m)."""
    R = Q[0][0].R
    m = len(Q)
    basis = []
    for i in range(m):
        for c in (R.one, R.w):
            v = [R.zero] * m
            v[i] = c
            basis.append(v)
    T = [[0] * (2 * m) for _ in range(2 * m)]
    for a in range(2 * m):
        for b in range(a, 2 * m):
            tr = bil(Q, basis[a], basis[b]).trace()
            T[a][b] = T[b][a] = tr
    return T, basis


def vectors_of_norms(Q: Mat, norms: Sequence[El]) -> List[Tuple[Vec, El]]:
    """All v in O^m with Q(v) in `norms` (exact equality), Q totally positive definite."""
    R = Q[0][0].R
    T, basis = trace_form(Q)
    bound = max(n.trace() for n in norms)
    out = []
    m = len(Q)
    for z in short_vectors_reduced(T, bound):
        if not any(z):
            continue
        v = [R(z[2 * i], z[2 * i + 1]) for i in range(m)]
        n = bil(Q, v, v)
        for t in norms:
            if n == t:
                out.append((v, n))
                break
    return out


def kernel_basis(c: Vec) -> Mat:
    """O-basis (as columns, 3x2) of {v in O^3 : c . v = 0} (Euclidean dot), c != 0 in K^3."""
    R = c[0].R
    from math import lcm
    den = 1
    for x in c:
        den = lcm(den, x.n)
    c = [x * den for x in c]
    V = [[R.one if i == j else R.zero for j in range(3)] for i in range(3)]
    c = list(c)
    # column operations on the row vector c until c = (g, 0, 0)
    for j in (1, 2):
        if c[j].is_zero():
            continue
        if c[0].is_zero():
            c[0], c[j] = c[j], c[0]
            for row in V:
                row[0], row[j] = row[j], row[0]
            continue
        g, x, y = egcd(c[0], c[j])
        a, b = c[0] / g, c[j] / g
        # new col0 = x col0 + y colj ; new colj = -b col0 + a colj  (det = 1)
        for row in V:
            u, w = row[0], row[j]
            row[0], row[j] = x * u + y * w, -b * u + a * w
        c[0], c[j] = g, R.zero
    return [[V[i][1], V[i][2]] for i in range(3)]


def cross(u: Vec, v: Vec) -> Vec:
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]


def root_norm_reps(GM: Mat) -> List[El]:
    """Possible root norms of the lattice (O^3, GM) modulo unit squares: totally
    positive divisors of 2 det GM (a primitive root r has 2 GM r / r^2 integral and
    hence r^2 | 2 det)."""
    return tp_divisors(2 * det(GM))


def is_root(GM: Mat, v: Vec) -> bool:
    R = GM[0][0].R
    n = bil(GM, v, v)
    if not n.tpos() or not gcd_list(v, R).is_unit():
        return False
    return all((2 * x / n).is_integral() for x in mat_vec(GM, v))


def mirrors_through_vertex(GM: Mat, r: Vec, t: Vec) -> int:
    """Number of mirrors of the lattice (O^3, GM) through the point r^⊥ ∩ t^⊥, i.e.
    root lines in span(r, t) ∩ O^3 (r, t in lattice coordinates, Gram of span(r,t)
    totally positive definite)."""
    R = GM[0][0].R
    B = kernel_basis(cross(r, t))
    Q = [[bil(GM, [B[i][a] for i in range(3)], [B[i][b] for i in range(3)])
          for b in range(2)] for a in range(2)]
    if not (Q[0][0].tpos() and det(Q).tpos()):
        raise ValueError("vertex plane not totally positive definite")
    norms = root_norm_reps(GM)
    count = 0
    for w, n in vectors_of_norms(Q, norms):
        v = [sum((B[i][a] * w[a] for a in range(2)), R.zero) for i in range(3)]
        if is_root(GM, v):
            count += 1
    assert count % 2 == 0
    return count // 2
