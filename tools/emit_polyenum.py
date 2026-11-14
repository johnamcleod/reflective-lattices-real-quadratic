"""Emit the B8 enumeration certificate of one reflective class as a Lean test file.

The certificate is the data of `ReflectZphi.PolyEnum.hone_of_enum2` (single centre):
vertices Ps, centre V with cosh bound pC/qC, window (u = eps, p/q > rho, Y, S'), the window
norms (kernel-recomputed), mu and K, and the enumeration data (aL, w, S, U, Uinv) of the
trace form of the majorant, with the last O-coordinate solved exactly.

Usage: python tools/emit_polyenum.py D class_index out.lean
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction as Fr
from math import isqrt, lcm, sqrt, floor

sys.path.insert(0, ".")
from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.linalg import bil, det, mat_vec  # noqa: E402
from zphi.definite import _ldl, lll_gram, trace_form, _int_det  # noqa: E402
from tools.b8_size import FILES  # noqa: E402
from tools.b8_split import vertices, centre_real  # noqa: E402


def centre_exact(R, G, corners, Vr, tol=1.10):
    """V in O^3 near the real centre Vr, scaled up until its cosh^2 bound is within tol of
    the real one (Vr normalised)."""
    rt = sqrt(R.disc)
    wb, wc = (R.c1 + rt) / 2, (R.c1 - rt) / 2
    f = lambda u, v: float(bil(G, u, v))
    target = max(fr ** 2 for fr in [-sum(float(G[i][j]) * Vr[i] * float(p[j])
                                         for i in range(3) for j in range(3))
                                    / sqrt(-f(p, p)) for p in corners])
    best = None
    scale = 4
    while scale < 2 ** 40:
        tgt = [scale * x for x in Vr]
        V = [R(round(-t * wc / (wb - wc)), round(t / (wb - wc))) for t in tgt]
        VV = bil(G, V, V)
        if float(VV) < 0 and all(f(V, p) < 0 for p in corners):
            C2 = max(f(V, p) ** 2 / (float(VV) * f(p, p)) for p in corners)
            if best is None or C2 < best[1]:
                best = (V, C2)
            if C2 <= target * tol:
                break
        scale *= 2
    V, C2 = best
    # exact rational bound pC/qC >= max cosh^2, checked exactly below
    C2q = Fr(C2).limit_denominator(64) + Fr(1, 64)
    return V, C2q


def window_norms(R, D, p, q, Y, S):
    """Exactly the list `ReflectZphi.RootNorms.windowNorms` computes."""
    a, b = R.c0, R.c1
    d = b * b + 4 * a
    ND = abs(D.norm_num()) if hasattr(D, "norm_num") else abs(int(D.norm()))
    out = []
    for y in range(Y):
        for s in range(S):
            if (s - b * y) % 2 != 0 or not 0 < s:
                continue
            if not q * d * y * y < p * ND:
                continue
            if not q * s * s < 4 * p * ND:
                continue
            x = (s - b * y) // 2
            m = R(x, y)
            if not m.conj().sign() > 0:      # iota_2 m > 0
                continue
            if not (p * m.conj() - q * m).sign() > 0:   # q iota_1 m < p iota_2 m
                continue
            if not (D / m).is_integral():
                continue
            out.append(m)
    return out


def floor_el(X):
    """Exact floor of iota_1(X), X = a + b w integral, w = (c1 + sqrt d)/2."""
    R = X.R
    assert X.n == 1
    a, b = X.a, X.b
    d = R.c1 ** 2 + 4 * R.c0
    r = isqrt(b * b * d)
    ft = r if b >= 0 else (-r if r * r == b * b * d else -r - 1)
    return (2 * a + b * R.c1 + ft) // 2


def ldl_int(F):
    """S F = sum_i w_i (sum_{j>=i} a_ij z_j)^2 with integers (a_ii > 0, w_i > 0)."""
    n = len(F)
    q = _ldl(F)
    a = [[0] * n for _ in range(n)]
    wr = []
    for i in range(n):
        di = 1
        for j in range(i + 1, n):
            di = lcm(di, q[i][j].denominator)
        a[i][i] = di
        for j in range(i + 1, n):
            a[i][j] = int(q[i][j] * di)
        from math import gcd
        g = 0
        for j in range(i, n):
            g = gcd(g, a[i][j])
        for j in range(i, n):
            a[i][j] //= g
        di //= g
        wr.append(q[i][i] / (di * di))
    S = 1
    for x in wr:
        S = lcm(S, x.denominator)
    w = [int(x * S) for x in wr]
    # exact check
    for j in range(n):
        for l in range(n):
            lhs = S * F[j][l]
            rhs = sum(w[i] * (a[i][j] if i <= j else 0) * (a[i][l] if i <= l else 0)
                      for i in range(n))
            assert lhs == rhs, (j, l)
    assert all(x > 0 for x in w)
    return a, w, S


def int_inv(M):
    n = len(M)
    A = [[Fr(M[i][j]) for j in range(n)] + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                fct = A[r][c]
                A[r] = [x - fct * y for x, y in zip(A[r], A[c])]
    inv = [[A[i][n + j] for j in range(n)] for i in range(n)]
    assert all(x.denominator == 1 for row in inv for x in row)
    return [[int(x) for x in row] for row in inv]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def enum_data(R, G, V, mu, qC, K):
    GV = mat_vec(G, V)
    VV = bil(G, V, V)
    Psi = [[2 * qC * GV[i] * GV[j] + (mu - qC * VV) * G[i][j] for j in range(3)]
           for i in range(3)]
    A, _ = trace_form(Psi)
    best = None
    for k in range(3):
        # permutation: new coords (0,1) = old (2k, 2k+1), then the others
        order = [2 * k, 2 * k + 1] + [i for i in range(6) if i // 2 != k]
        P = [[int(order[c] == r) for c in range(6)] for r in range(6)]
        A1 = matmul(transpose(P), matmul(A, P))
        # Schur complement on coords 2..5 after eliminating 0,1 (rational), LLL it
        q = _ldl(A1)
        # LLL on the 4x4 tail of the Fincke-Pohst form: rebuild its Gram
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
        T4i = [[int(x * den) for x in row] for row in T4]
        V4 = lll_gram(T4i)
        B = [[int(i == j) for j in range(6)] for i in range(6)]
        for i in range(4):
            for j in range(4):
                B[2 + i][2 + j] = V4[i][j]
        U = matmul(P, B)
        Uinv = int_inv(U)
        F = matmul(transpose(U), matmul(A, U))
        a, w, S = ldl_int(F)
        nodes = count_stopped(a, w, S * K)
        if best is None or nodes < best[0]:
            best = (nodes, a, w, S, U, Uinv, k)
    return best


def count_stopped(a, w, B):
    """Nodes of the stopped search (levels 5..2), mirroring enumAuxS."""
    n = 6
    z = [0] * n
    cnt = 0

    def rec(k, B):
        nonlocal cnt
        if k <= 2:
            cnt += 1
            return
        if B < 0:
            return
        i = k - 1
        c = sum(a[i][j] * z[j] for j in range(i + 1, n))
        s = isqrt(B // w[i])
        lo, hi = (-s - c) // a[i][i], (s - c) // a[i][i]
        for t in range(lo, hi + 1):
            cnt += 1
            z[i] = t
            rec(i, B - w[i] * (a[i][i] * t + c) ** 2)
        z[i] = 0

    rec(n, B)
    return cnt


def el(x):
    assert x.n == 1, x
    return f"⟨{x.a}, {x.b}⟩"


def vec(v):
    return "![" + ", ".join(el(x) for x in v) + "]"


def lmat(M):
    return "[" + ", ".join("[" + ", ".join(str(x) for x in r) + "]" for r in M) + "]"


def main():
    D, ci, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    R = get_ring(D)
    assert R.c0 == 1 and R.c1 == 1, "Z[phi] only for now"
    data = json.load(open(FILES[D]))
    c = data["classes"][ci]
    G = [[from_json(R, e) for e in row] for row in c["gram"]]
    roots = [[from_json(R, e) for e in r] for r in c["polygon"]["roots"]]
    P = vertices(R, G, roots)
    n = len(P)
    Vr, _ = centre_real(G, P)
    V, C2 = centre_exact(R, G, P, Vr)
    pC, qC = C2.numerator, C2.denominator
    VV = bil(G, V, V)
    for p_ in P:
        X = pC * VV * bil(G, p_, p_) - qC * bil(G, V, p_) ** 2
        assert X.sign() >= 0
    # window: u = phi, rho = phi^4 < 7
    p, q = 7, 1
    Dd = 2 * det(G)
    ND = abs(Dd.norm_num())
    d = R.c1 ** 2 + 4 * R.c0
    Y = isqrt(p * ND // (q * d)) + 1
    while not p * ND <= q * d * Y * Y:
        Y += 1
    Sp = isqrt(4 * p * ND // q) + 1
    while not 4 * p * ND <= q * Sp * Sp:
        Sp += 1
    norms = window_norms(R, Dd, p, q, Y, Sp)
    # mu: mu1 ~ 0, mu2 balancing
    VV1, VV2 = float(VV), VV.sfloat()
    rt = sqrt(R.disc)
    wb = (R.c1 + rt) / 2
    best = None
    for fac in (0.5, 1.0, 2.0):
        target = max(fac * (2 * float(C2) - 1) * abs(VV1) * qC - qC * VV2, 1.5 * qC * VV2)
        y = -round(target / rt)
        x = round(-y * wb)
        mu = R(x, y)
        if not (abs(float(mu)) < qC * abs(VV1) and mu.sfloat() > qC * VV2):
            continue
        Xs = [(2 * pC - qC) * m * (-VV) + mu * m + (qC * m * VV + mu * m).conj() for m in norms]
        K = max(floor_el(X) + 1 for X in Xs)
        assert all((K - X).sign() >= 0 for X in Xs)
        ed = enum_data(R, G, V, mu, qC, K)
        if best is None or ed[0] < best[0][0]:
            best = (ed, mu, K)
    (nodes, a, w, S, U, Uinv, k), mu, K = best
    print(f"class {ci}: n={n} C2={float(C2):.3f} norms={len(norms)} K={K} S={S} "
          f"stopped-search nodes={nodes} (solve coordinate {k})", flush=True)
    lines = [
        "import ReflectZphi.Cert.PolyEnum",
        "",
        f"/-! Generated by tools/emit_polyenum.py (class {ci} of {FILES[D]}). Do not edit. -/",
        "",
        f"namespace ReflectZphi.Data.PolyEnumTest{ci}",
        "",
        "open ReflectZphi ReflectZphi.PolyEnum ReflectZphi.RootNorms ReflectZphi.Enum",
        "",
        "abbrev O5 := QuadraticAlgebra ℤ 1 1",
        "",
        "def G : Matrix (Fin 3) (Fin 3) O5 := !![" + "; ".join(
            ", ".join(el(x) for x in row) for row in G) + "]",
        "def PsL : List (Fin 3 → O5) := [" + ", ".join(vec(p_) for p_ in P) + "]",
        "def Ps (i : ℕ) : Fin 3 → O5 := PsL.getD i ![0, 0, 0]",
        f"def D2 : O5 := {el(Dd)}",
        "def normsL : List O5 := [" + ", ".join(el(m) for m in norms) + "]",
        f"theorem norms_eq : windowNorms 1 1 D2 {p} {q} {Y} {Sp} = normsL := by decide +kernel",
        "def aM : List (List ℤ) := " + lmat(a),
        "def UM : List (List ℤ) := " + lmat(U),
        "def UiM : List (List ℤ) := " + lmat(Uinv),
        "def aL (i j : ℕ) : ℤ := (aM.getD i []).getD j 0",
        "def U (i j : ℕ) : ℤ := (UM.getD i []).getD j 0",
        "def Uinv (i j : ℕ) : ℤ := (UiM.getD i []).getD j 0",
        "def w (i : ℕ) : ℤ := ([" + ", ".join(map(str, w)) + "] : List ℤ).getD i 0",
        f"def V : Fin 3 → O5 := {vec(V)}",
        f"def μ : O5 := {el(mu)}",
        "",
        "theorem col_ok : colCheck (a := 1) (b := 1) U = true := by decide +kernel",
        "theorem inv_ok : invCheck U Uinv = true := by decide +kernel",
        f"theorem quad_ok : quadCheck aL w 6 (gramU U (traceGram G V μ {qC})) {S} = true := by",
        "  decide +kernel",
        f"theorem enum_ok : enumS aL w 6 2 (leaf2 G {n} Ps normsL U) ({S} * {K}) = true := by",
        "  decide +kernel",
        "",
        f"end ReflectZphi.Data.PolyEnumTest{ci}",
        "",
    ]
    open(out, "w").write("\n".join(lines))


if __name__ == "__main__":
    main()
