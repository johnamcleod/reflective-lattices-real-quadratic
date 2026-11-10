"""Prime-by-prime enumeration of intermediate lattices R <= M <= H with M SSF.

Uses the Smith normal form of R inside H over O (a Euclidean PID), and the fact
that squarefreeness of the primitive rescaling of det M is a local condition.
"""
from quadring import (divides, egcd, gcd, tp_normalise, factor_int, primes_above,
                      assoc_key, is_squarefree)
import rank3 as r3


def ident(R):
    return [[R(1) if i == j else R(0) for j in range(3)] for i in range(3)]


def snf(A):
    """Return (U, S, V) with U A V = S diagonal, U, V unimodular over O."""
    R = A[0][0].R
    S = [row[:] for row in A]
    U, V = ident(R), ident(R)

    def row_op(M, i, j, a, b, c, d):  # rows (i, j) <- [[a, b], [c, d]] (rows i, j)
        ri, rj = M[i], M[j]
        M[i] = [a * x + b * y for x, y in zip(ri, rj)]
        M[j] = [c * x + d * y for x, y in zip(ri, rj)]

    def col_op(M, i, j, a, b, c, d):  # cols (i, j) <- cols * [[a, c], [b, d]]
        for row in M:
            x, y = row[i], row[j]
            row[i] = a * x + b * y
            row[j] = c * x + d * y

    for k in range(3):
        while True:
            # choose pivot of minimal |norm| among nonzero entries in submatrix
            best = None
            for i in range(k, 3):
                for j in range(k, 3):
                    if not S[i][j].is_zero():
                        n = abs(S[i][j].norm())
                        if best is None or n < best[0]:
                            best = (n, i, j)
            if best is None:
                return U, S, V
            _, i, j = best
            S[k], S[i] = S[i], S[k]; U[k], U[i] = U[i], U[k]
            for row in S: row[k], row[j] = row[j], row[k]
            for row in V: row[k], row[j] = row[j], row[k]
            done = True
            for i in range(k + 1, 3):            # clear column k
                if not S[i][k].is_zero() and divides(S[k][k], S[i][k]):
                    q = S[i][k] / S[k][k]
                    row_op(S, k, i, R(1), R(0), -q, R(1)); row_op(U, k, i, R(1), R(0), -q, R(1))
                elif not S[i][k].is_zero():
                    g, x, y = egcd(S[k][k], S[i][k])
                    a, b = S[k][k] / g, S[i][k] / g
                    row_op(S, k, i, x, y, -b, a); row_op(U, k, i, x, y, -b, a)
            for j in range(k + 1, 3):            # clear row k
                if not S[k][j].is_zero() and divides(S[k][k], S[k][j]):
                    q = S[k][j] / S[k][k]
                    col_op(S, k, j, R(1), R(0), -q, R(1)); col_op(V, k, j, R(1), R(0), -q, R(1))
                elif not S[k][j].is_zero():
                    g, x, y = egcd(S[k][k], S[k][j])
                    a, b = S[k][k] / g, S[k][j] / g
                    col_op(S, k, j, x, y, -b, a); col_op(V, k, j, x, y, -b, a)
            if any(not S[i][k].is_zero() for i in range(k + 1, 3)) or \
               any(not S[k][j].is_zero() for j in range(k + 1, 3)):
                continue
            # divisibility: pivot must divide the rest
            bad = None
            for i in range(k + 1, 3):
                for j in range(k + 1, 3):
                    if not divides(S[k][k], S[i][j]) if not S[i][j].is_zero() else False:
                        bad = (i, j)
            if bad:
                i, j = bad
                row_op(S, k, i, R(1), R(1), R(0), R(1)); row_op(U, k, i, R(1), R(1), R(0), R(1))
                continue
            break
    return U, S, V


def val(z, p):
    if z.is_zero():
        return 10 ** 9
    v = 0
    while divides(p, z):
        z = z / p
        v += 1
    return v


def prime_list(z):
    out = []
    for q in factor_int(z.norm()):
        for p in primes_above(q, z.R):
            if divides(p, z):
                out.append(p)
    return out


def local_superlattices(e, p):
    """Superlattices N of diag(p^e1, p^e2, p^e3) inside O^3 (index a power of p).

    N is in lower-triangular column form with diagonal p^k1, p^k2, p^k3; the
    containment conditions are solved directly, so every N is produced exactly once.
    """
    R = p.R
    from rank3 import residues
    out = []

    def mult_reps(m, k):
        # elements of p^m O modulo p^k (m <= k)
        if m >= k:
            return [R(0)]
        return [p ** m * r for r in residues(p ** (k - m))]

    for k1 in range(e[0] + 1):
        for k2 in range(e[1] + 1):
            for k3 in range(e[2] + 1):
                d1, d2, d3 = p ** k1, p ** k2, p ** k3
                m1 = e[0] - k1
                for b32 in mult_reps(max(0, k3 - (e[1] - k2)), k3):
                    for b21 in mult_reps(max(0, k2 - m1), k2):
                        x2 = -(p ** m1) * b21 / d2
                        c = -x2 * b32
                        if m1 >= k3:
                            if not divides(d3, c) and not c.is_zero():
                                continue
                            b31s = residues(d3)
                        else:
                            if not c.is_zero() and not divides(p ** m1, c):
                                continue
                            base = c / p ** m1
                            b31s = [base + p ** (k3 - m1) * t for t in residues(p ** m1)]
                        for b31 in b31s:
                            out.append([[d1, R(0), R(0)], [b21, d2, R(0)], [b31, b32, d3]])
    return out
