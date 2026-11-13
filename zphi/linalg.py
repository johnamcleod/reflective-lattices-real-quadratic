"""Small dense matrices over K (lists of lists of El). Exact."""
from __future__ import annotations

from math import lcm
from typing import List, Sequence

from .ring import El, Ring, egcd, tp_normalise

Mat = List[List[El]]
Vec = List[El]


def zeros(R: Ring, n: int, m: int) -> Mat:
    return [[R.zero for _ in range(m)] for _ in range(n)]


def ident(R: Ring, n: int = 3) -> Mat:
    return [[R.one if i == j else R.zero for j in range(n)] for i in range(n)]


def mat_mul(A: Mat, B: Mat) -> Mat:
    R = A[0][0].R
    n, k, m = len(A), len(B), len(B[0])
    C = zeros(R, n, m)
    for i in range(n):
        Ai = A[i]
        for j in range(m):
            s = R.zero
            for l in range(k):
                x = Ai[l]
                if x.a or x.b:
                    y = B[l][j]
                    if y.a or y.b:
                        s = s + x * y
            C[i][j] = s
    return C


def mat_vec(A: Mat, v: Vec) -> Vec:
    R = A[0][0].R
    out = []
    for row in A:
        s = R.zero
        for x, y in zip(row, v):
            if (x.a or x.b) and (y.a or y.b):
                s = s + x * y
        out.append(s)
    return out


def transpose(A: Mat) -> Mat:
    return [list(r) for r in zip(*A)]


def det(M: Mat) -> El:
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    if n == 3:
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    # Laplace along first row (n small)
    R = M[0][0].R
    s = R.zero
    for j in range(n):
        if M[0][j].is_zero():
            continue
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        t = M[0][j] * det(minor)
        s = s + t if j % 2 == 0 else s - t
    return s


def inv(M: Mat) -> Mat:
    """Inverse via adjugate (n <= 5)."""
    n = len(M)
    d = det(M)
    R = d.R
    C = zeros(R, n, n)
    for i in range(n):
        for j in range(n):
            minor = [[M[r][c] for c in range(n) if c != i] for r in range(n) if r != j]
            cof = det(minor) if n > 1 else R.one
            C[i][j] = cof / d if (i + j) % 2 == 0 else -cof / d
    return C


def col(M: Mat, j: int) -> Vec:
    return [M[i][j] for i in range(len(M))]


def bil(G: Mat, u: Vec, v: Vec) -> El:
    R = G[0][0].R
    s = R.zero
    for i, ui in enumerate(u):
        if not (ui.a or ui.b):
            continue
        Gi = G[i]
        for j, vj in enumerate(v):
            if (vj.a or vj.b) and (Gi[j].a or Gi[j].b):
                s = s + ui * Gi[j] * vj
    return s


def gram_of(G: Mat, B: Mat) -> Mat:
    """B^T G B (columns of B are the basis)."""
    return mat_mul(mat_mul(transpose(B), G), B)


def is_integral_mat(M: Mat) -> bool:
    return all(e.n == 1 for row in M for e in row)


def common_denominator(vals: Sequence[El]) -> int:
    d = 1
    for v in vals:
        d = lcm(d, v.n)
    return d


def hnf_basis(gens: Sequence[Vec]) -> Mat:
    """Lower-triangular O-basis (as columns) of the O-span of vectors in K^3 that
    span K^3. Pivots are totally positive canonical representatives."""
    R = gens[0][0].R
    n = len(gens[0])
    den = common_denominator([c for g in gens for c in g])
    cols = [[c * den for c in g] for g in gens]
    basis = []
    for row in range(n):
        piv = None
        rest = []
        for c in cols:
            if c[row].is_zero():
                rest.append(c)
                continue
            if piv is None:
                piv = c
                continue
            g, x, y = egcd(piv[row], c[row])
            a, b = piv[row] / g, c[row] / g
            newp = [x * piv[i] + y * c[i] for i in range(n)]
            other = [b * piv[i] - a * c[i] for i in range(n)]
            piv = newp
            rest.append(other)
        if piv is None:
            raise ValueError("generators do not span K^n")
        u = tp_normalise(piv[row]) / piv[row]
        piv = [u * e for e in piv]
        basis.append(piv)
        cols = [c for c in rest if any(not e.is_zero() for e in c)]
    return [[basis[j][i] / den for j in range(n)] for i in range(n)]


def leading_minors(G: Mat) -> List[El]:
    return [det([row[:k] for row in G[:k]]) for k in range(1, len(G) + 1)]


def admissible(G: Mat) -> bool:
    """Rank 3: signature (2,1) at id and positive definite at sigma (exact).

    At sigma: all leading principal minors > 0 (Sylvester). At id: det < 0 gives
    signature (2,1) or (0,3); (0,3) = negative definite iff the leading minors
    have signs (-, +, -) (Sylvester applied to -G)."""
    R = G[0][0].R
    m = leading_minors(G)
    if m[2].sign() >= 0:
        return False
    if m[0].sign() < 0 and m[1].sign() > 0:
        return False  # negative definite (Sylvester criterion is exact for definiteness)
    if R.degree == 1:
        # signature (2,1) over R: det < 0 and not negative definite
        return True
    return all(m.ssign() > 0 for m in leading_minors(G))
