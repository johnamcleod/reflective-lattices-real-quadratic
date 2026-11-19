"""Prototype: enum_psi with the solved O-coordinate chosen per cell from short vectors of the
full trace form (instead of only the three original O-coordinates)."""
from fractions import Fraction as Fr
from math import lcm
from zphi.definite import _ldl, lll_gram, trace_form
from zphi.ring import gcd_list
from tools import emit_polyenum as E
from tools.emit_cert import count_capped


def complete2(C):
    """Unimodular 6x6 integer U6 whose first two columns are the 6x2 matrix C (C must be
    saturated). Row-reduce C by unimodular E: E C = [H; 0], U6 = E^-1 diag(H, I)."""
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


def enum_psi2(R, Psi, K, cap, extra=6):
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
