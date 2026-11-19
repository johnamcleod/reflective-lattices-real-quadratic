"""Per-norm sublattices for the cell searches (prototype).

A root r of norm m satisfies m | 2 (r, x) for all x in L = O^3, i.e. r lies in
    L_m = { r in O^3 : (2/m) G r in O^3 }.
Its dual (for the dot product) is L_m^* = O^3 + (2/m) G O^3. We compute an O-basis N of L_m^*
by an O-HNF that tracks each basis vector as p + (2/m) G q (p, q in O^3); then B = N^{-T} is
an O-basis of L_m, and B^{-1} = N^T = P + Q (2/m) G with P, Q the O-matrices of rows p^T, q^T.
So for a root r of norm m, y = B^{-1} r = P r + Q s with s = (2/m) G r in O^3 (integral).
"""
from __future__ import annotations

import sys

sys.path.insert(0, ".")
from zphi.ring import egcd  # noqa: E402
from zphi.linalg import common_denominator, inv, mat_mul, transpose  # noqa: E402


def tp_unit(R, x):
    from zphi.linalg import tp_normalise  # noqa: F401
    return tp_normalise(x) / x


def sub_basis(R, G, m):
    """(B, P, Q): B an O-basis (columns) of L_m, B^{-1} = P + Q (2/m) G."""
    two_m = R(2, 0) / m
    T = [[two_m * G[i][j] for j in range(3)] for i in range(3)]
    gens = []  # (vector in K^3, tag p in O^3, tag q in O^3)
    for j in range(3):
        gens.append(([R.one if i == j else R.zero for i in range(3)],
                     [R.one if i == j else R.zero for i in range(3)], [R.zero] * 3))
    for j in range(3):
        gens.append(([T[i][j] for i in range(3)], [R.zero] * 3,
                     [R.one if i == j else R.zero for i in range(3)]))
    den = common_denominator([c for g in gens for c in g[0]])
    cols = [([c * den for c in v], p, q) for v, p, q in gens]

    def comb(x, A, y, Bv):
        return tuple([x * A[k][i] + y * Bv[k][i] for i in range(3)] for k in range(3))

    basis = []
    for row in range(3):
        piv, rest = None, []
        for c in cols:
            if c[0][row].is_zero():
                rest.append(c)
                continue
            if piv is None:
                piv = c
                continue
            g, x, y = egcd(piv[0][row], c[0][row])
            a_, b_ = piv[0][row] / g, c[0][row] / g
            newp = comb(x, piv, y, c)
            other = comb(b_, piv, -a_, c)
            piv = newp
            rest.append(other)
        basis.append(piv)
        cols = [c for c in rest if any(not e.is_zero() for e in c[0])]
    N = [[basis[j][0][i] / den for j in range(3)] for i in range(3)]  # columns n_j
    # check n_j = p_j + T q_j
    for j in range(3):
        for i in range(3):
            lhs = N[i][j]
            rhs = basis[j][1][i] + sum((T[i][k] * basis[j][2][k] for k in range(3)), R.zero)
            assert (lhs - rhs).is_zero()
    P = [[basis[i][1][k] for k in range(3)] for i in range(3)]  # rows p_i^T
    Q = [[basis[i][2][k] for k in range(3)] for i in range(3)]
    B = transpose(inv(N))
    for x in (e for row in B for e in row):
        assert x.is_integral()
    # B^{-1} = N^T = P + Q T
    NT = transpose(N)
    QT = mat_mul(Q, T)
    for i in range(3):
        for k in range(3):
            assert (NT[i][k] - P[i][k] - QT[i][k]).is_zero()
    return B, P, Q


def complete2(C):
    """Unimodular 6x6 integer U6 whose first two columns are the 6x2 matrix C (C must be
    saturated). Row-reduce C by unimodular E: E C = [H; 0], U6 = E^-1 diag(H, I)."""
    from fractions import Fraction as Fr
    from math import lcm
    from zphi.definite import _ldl, lll_gram, trace_form
    from zphi.ring import gcd_list
    from tools import emit_polyenum as E
    from tools.emit_cert import count_capped
    n = len(C)
    M = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(C)]  # [C | I]
    r = 0
    for c in range(2):
        while True:
            nz = [i for i in range(r, n) if M[i][c] != 0]
            if not nz:
                raise ValueError("rank")
            p = min(nz, key=lambda i: abs(M[i][c]))
            M[r], M[p] = M[p], M[r]
            done = True
            for i in range(r + 1, n):
                q = M[i][c] // M[r][c]
                if q:
                    M[i] = [x - q * y for x, y in zip(M[i], M[r])]
                if M[i][c] != 0:
                    done = False
            if done:
                break
        r += 1
    Em = [row[2:] for row in M]          # E (rows), E C = [H; 0]
    H = [[M[i][j] for j in range(2)] for i in range(2)]
    dH = H[0][0] * H[1][1] - H[0][1] * H[1][0]
    if abs(dH) != 1:
        raise ValueError("not saturated")
    D = [[int(i == j) for j in range(n)] for i in range(n)]
    for i in range(2):
        for j in range(2):
            D[i][j] = H[i][j]
    U6 = E.matmul(E.int_inv(Em), D)
    for i in range(n):
        assert U6[i][0] == C[i][0] and U6[i][1] == C[i][1]
    return U6


def o_dir(R, z):
    """The Z^6 vector z as an O^3 vector, made O-primitive; columns (c0, w c0) as 6x2."""
    from fractions import Fraction as Fr
    from math import lcm
    from zphi.definite import _ldl, lll_gram, trace_form
    from zphi.ring import gcd_list
    from tools import emit_polyenum as E
    from tools.emit_cert import count_capped
    v = [R(z[2 * i], z[2 * i + 1]) for i in range(3)]
    g = gcd_list(v, R)
    v = [x / g for x in v]
    wv = [R.w * x for x in v]
    C = []
    for i in range(3):
        C.append([v[i].a, wv[i].a])
        C.append([v[i].b, wv[i].b])
    return C


def finish(A, U, K, cap):
    """LLL the projection orthogonal to the first two columns of U; node count etc."""
    from fractions import Fraction as Fr
    from math import lcm
    from zphi.definite import _ldl, lll_gram, trace_form
    from zphi.ring import gcd_list
    from tools import emit_polyenum as E
    from tools.emit_cert import count_capped
    A1 = E.matmul(E.transpose(U), E.matmul(A, U))
    q = _ldl(A1)
    T4 = [[Fr(0)] * 4 for _ in range(4)]
    for i in range(2, 6):
        for j in range(2, 6):
            s = Fr(0)
            for r in range(2, 6):
                li = (Fr(1) if r == i else q[r][i] if r < i else Fr(0))
                lj = (Fr(1) if r == j else q[r][j] if r < j else Fr(0))
                s += q[r][r] * li * lj
            T4[i - 2][j - 2] = s
    den = 1
    for row in T4:
        for x in row:
            den = lcm(den, x.denominator)
    V4 = lll_gram([[int(x * den) for x in row] for row in T4])
    Bm = [[int(i == j) for j in range(6)] for i in range(6)]
    for i in range(4):
        for j in range(4):
            Bm[2 + i][2 + j] = V4[i][j]
    U2 = E.matmul(U, Bm)
    F = E.matmul(E.transpose(U2), E.matmul(A, U2))
    a, w, S = E.ldl_int(F)
    return count_capped(a, w, S * K, cap), a, w, S, U2


def enum_psi(R, Psi, K, cap, extra=6):
    """As emit_cert.enum_data, for a given O-form Psi (3x3) instead of (G, V, mu, qC).

    The search solves one O-coordinate exactly at the leaf (the first two columns of U are
    c0, w c0) and runs Fincke-Pohst on the LLL-reduced projection of the other four. The
    solved direction c0 is chosen per cell: one of the three original O-coordinates, or the
    O-primitive vector through a short vector of the LLL-reduced trace form, whichever gives
    the smallest tree. (Far from the well-reduced region the original coordinates give very
    skewed searches: class 137 vertex cells 47.7M -> 133 nodes.) Only U unimodular with
    column 1 = w column 0 matters for correctness; the Lean check is unchanged."""
    from fractions import Fraction as Fr
    A, _ = trace_form(Psi)
    cands = []
    for k in range(3):
        order = [2 * k, 2 * k + 1] + [i for i in range(6) if i // 2 != k]
        cands.append(("orig", k, [[int(order[c] == r) for c in range(6)] for r in range(6)]))
    L = lll_gram(A)
    for j in range(min(extra, 6)):
        z = [L[i][j] for i in range(6)]
        try:
            cands.append(("lll", j, complete2(o_dir(R, z))))
        except ValueError:
            pass
    best = None
    for tag, k, U in cands:
        nodes, a, w, S, U2 = finish(A, U, K, cap if best is None else min(cap, best[0]))
        if best is None or nodes < best[0]:
            best = (nodes, a, w, S, U2, E.int_inv(U2), (tag, k))
    return best
