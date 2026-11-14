"""Prototype for Lean step B8: size of the single-centre enumeration per polygon.

For a reflective class (roots r_0..r_{n-1}, Gram G over O):
  vertices P_i = adj(G)(r_i x r_{i+1}), made future;
  centre V in Z^3 near the barycentre of the normalised vertices;
  C^2 >= max_i (V.P_i)^2 / ((V.V)(P_i.P_i)) at iota_1;
  majorant psi(r) = 2(r.V)^2 - (r.r)(V.V) + mu (r.r), F = Tr psi on Z^6;
  K = max over window norms m of (2C^2-1) m1 |VV1| + m2 VV2 + Tr(mu m).
Every root whose mirror crosses the polygon (rescaled into the window) has F <= K.
Prints the Fincke-Pohst node count (LLL-reduced basis) for each class.

Usage: python tools/b8_size.py D [max_classes]
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as Fr
from math import isqrt, lcm, sqrt

sys.path.insert(0, ".")
from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.linalg import bil, det, mat_vec  # noqa: E402
from zphi.definite import _ldl, lll_gram, trace_form, cross, root_norm_reps  # noqa: E402

FILES = {5: "data/zphi_rank3.json", 2: "data/zsqrt2_rank3.json", 13: "data/zsqrt13_rank3.json"}


def adj(G):
    R = G[0][0].R
    A = [[R.zero] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            rows = [r for r in range(3) if r != j]
            cols = [c for c in range(3) if c != i]
            m = G[rows[0]][cols[0]] * G[rows[1]][cols[1]] - G[rows[0]][cols[1]] * G[rows[1]][cols[0]]
            A[i][j] = m if (i + j) % 2 == 0 else -m
    return A


def count_nodes(T, bound):
    """Fincke-Pohst node count (the same recursion as zphi.definite.short_vectors)."""
    n = len(T)
    q = _ldl(T)
    assert all(q[i][i] > 0 for i in range(n)), "not PD"
    D = 1
    for i in range(n):
        for j in range(i, n):
            D = lcm(D, q[i][j].denominator)
    Qd = [[int(q[i][j] * D) if j >= i else 0 for j in range(n)] for i in range(n)]
    bound = Fr(bound)
    bd = bound.denominator
    x = [0] * n
    nodes = 0
    leaves = 0

    def rec(i, Rs):
        nonlocal nodes, leaves
        C = sum(Qd[i][j] * x[j] for j in range(i + 1, n))
        qii = Qd[i][i]
        s = isqrt(Rs // (D * D * bd * qii)) + 1
        lo = (-C) // D - s
        hi = -(C // D) + s
        for xi in range(lo, hi + 1):
            nodes += 1
            dD = xi * D + C
            rem = Rs - qii * dD * dD * bd
            if rem < 0:
                continue
            x[i] = xi
            if i == 0:
                leaves += 1
            else:
                rec(i - 1, rem)
        x[i] = 0

    rec(n - 1, bound.numerator * D ** 3)
    return nodes, leaves


def window_norms(R, Dd):
    eta = R.eta
    rho = float(eta) / eta.conj().sfloat() if hasattr(eta, "sfloat") else None
    out = []
    for m in root_norm_reps_list(R, Dd):
        out.append(m)
    return out


def root_norm_reps_list(R, Dd):
    from zphi.ring import tp_divisors
    reps = tp_divisors(Dd)
    eta = R.eta
    res = []
    for m in reps:
        # move into window 1 <= m1/m2 < rho by eta^k
        for _ in range(200):
            r = float(m) / m.sfloat()
            rho = float(eta) / eta.sfloat()
            if r < 1:
                m = m * eta
            elif r >= rho:
                m = m / eta
            else:
                break
        res.append(m)
    return res


def analyse(R, G, roots):
    n = len(roots)
    A = adj(G)
    P = [mat_vec(A, cross(roots[i], roots[(i + 1) % n])) for i in range(n)]
    # future: same side as P[0] (iota_1)
    for i in range(1, n):
        if float(bil(G, P[i], P[0])) > 0:
            P[i] = [-c for c in P[i]]
    # orient so that roots are <= 0 on the vertices
    f = lambda u, v: float(bil(G, u, v))
    Pr = [[float(c) for c in p] for p in P]
    tau = [sqrt(-f(p, p)) for p in P]
    # minimax centre: minimise max_i cosh d(V, P_i) over V = sum w_i P_i / tau_i
    Pn = [[Pr[i][k] / tau[i] for k in range(3)] for i in range(n)]
    def fr(u, v):
        return sum(float(G[i][j]) * u[i] * v[j] for i in range(3) for j in range(3))
    w = [1.0] * n
    for it in range(400):
        Vr = [sum(w[i] * Pn[i][k] for i in range(n)) for k in range(3)]
        tv = sqrt(-fr(Vr, Vr))
        ch = [-fr(Vr, Pn[i]) / tv for i in range(n)]
        j = max(range(n), key=lambda i: ch[i])
        w[j] *= 1.0 + 0.5 / (1 + it / 20)
        tot = sum(w)
        w = [x / tot for x in w]
    rt5 = sqrt(R.disc)
    wb = (R.c1 + rt5) / 2      # iota_1(w)
    wc = (R.c1 - rt5) / 2      # iota_2(w)
    best = None
    for scale in (8, 16, 32, 64):
        nr = sqrt(-fr(Vr, Vr))
        tgt = [scale * Vr[k] / nr for k in range(3)]
        # x + y wb = t, x + y wc = 0
        V = [R(round(-t * wc / (wb - wc)), round(t / (wb - wc))) for t in tgt]
        VV = bil(G, V, V)
        if not float(VV) < 0:
            continue
        if any(f(V, p) > 0 for p in P):
            V = [-c for c in V]
        if any(f(V, p) >= 0 for p in P):
            continue
        C2 = max(f(V, p) ** 2 / (float(VV) * f(p, p)) for p in P)
        C2q = Fr(C2).limit_denominator(1000) + Fr(1, 1000)
        if best is None or C2q < best[2] * Fr(101, 100):
            best = (V, VV, C2q)
    V, VV, C2 = best
    Dd = 2 * det(G)
    norms = root_norm_reps_list(R, Dd)
    GV = mat_vec(G, V)
    VV1, VV2 = float(VV), VV.sfloat()
    results = []
    # mu with mu1 ~ 0 and mu2 balancing the two embeddings:
    # (VV2 + mu2) m2 ~ (2C^2 - 1) m1 |VV1|  (m1 ~ m2 ~ 1 here)
    rt = sqrt(R.disc)
    wb = (R.c1 + rt) / 2
    cands = []
    for fac in (0.25, 0.5, 1.0, 2.0, 4.0):
        target = max(fac * (2 * float(C2) - 1) * abs(VV1) - VV2, 1.5 * VV2)
        y = -round(target / rt)
        x = round(-y * wb)
        mu = R(x, y)
        if abs(float(mu)) < abs(VV1) and mu.sfloat() > VV2:
            cands.append(mu)
    for mu in cands[:40]:
        Psi = [[2 * GV[i] * GV[j] + (mu - VV) * G[i][j] for j in range(3)] for i in range(3)]
        T, _ = trace_form(Psi)
        try:
            _ldl_ok = all(v > 0 for v in [_ldl(T)[i][i] for i in range(6)])
        except ZeroDivisionError:
            continue
        if not _ldl_ok:
            continue
        K = max((2 * float(C2) - 1) * float(m) * abs(VV1) + m.sfloat() * VV2
                + (mu * m).trace() for m in norms)
        U = lll_gram(T)
        T2 = [[sum(U[i][a] * T[i][j] * U[j][b] for i in range(6) for j in range(6))
               for b in range(6)] for a in range(6)]
        nodes, leaves = count_nodes(T2, Fr(int(K) + 1))
        results.append((nodes, leaves, mu, K))
    results.sort(key=lambda t: t[0])
    return results[0] if results else None, float(C2), len(norms)


def main():
    D = int(sys.argv[1])
    lim = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    R = get_ring(D)
    data = json.load(open(FILES[D]))
    tot = 0
    for ci, c in enumerate(data["classes"][:lim]):
        G = [[from_json(R, e) for e in row] for row in c["gram"]]
        roots = [[from_json(R, e) for e in r] for r in c["polygon"]["roots"]]
        t0 = time.time()
        best, C2, nn = analyse(R, G, roots)
        nodes, leaves, mu, K = best
        tot += nodes
        print(f"class {ci} sides {len(roots)} C2 {C2:.2f} norms {nn} mu {mu} K {K:.0f} "
              f"nodes {nodes} leaves {leaves} ({time.time() - t0:.1f}s)", flush=True)
    print("total nodes", tot)


if __name__ == "__main__":
    main()
