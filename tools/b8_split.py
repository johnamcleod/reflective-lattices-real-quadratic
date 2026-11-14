"""Prototype for Lean step B8 with subdivision: total enumeration size per polygon.

The polygon is cut into the fan triangles (P_0, P_k, P_{k+1}); a triangle (A, B, C) whose
best centre has C^2 > thr is split along its longest edge AB at M = kA + lB (k, l > 0
small integers chosen so that M is near the hyperbolic midpoint), recursively. Each leaf
triangle gets its own centre V, majorant and Fincke-Pohst count (as in b8_size.py).

Usage: python tools/b8_split.py D thr [first last]
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as Fr
from math import sqrt

sys.path.insert(0, ".")
from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.linalg import bil, det, mat_vec  # noqa: E402
from zphi.definite import _ldl, lll_gram, trace_form, cross  # noqa: E402
from tools.b8_size import adj, count_nodes, root_norm_reps_list, FILES  # noqa: E402


def vertices(R, G, roots):
    n = len(roots)
    A = adj(G)
    P = [mat_vec(A, cross(roots[i], roots[(i + 1) % n])) for i in range(n)]
    for i in range(1, n):
        if float(bil(G, P[i], P[0])) > 0:
            P[i] = [-c for c in P[i]]
    return P


def fr(G, u, v):
    return sum(float(G[i][j]) * u[i] * v[j] for i in range(3) for j in range(3))


def centre_real(G, corners):
    """Minimax centre (floats) of the corners; returns (Vr, max cosh^2)."""
    Pr = [[float(c) for c in p] for p in corners]
    Pn = []
    for p in Pr:
        t = sqrt(-fr(G, p, p))
        Pn.append([x / t for x in p])
    n = len(Pn)
    w = [1.0] * n
    for it in range(300):
        Vr = [sum(w[i] * Pn[i][k] for i in range(n)) for k in range(3)]
        tv = sqrt(-fr(G, Vr, Vr))
        ch = [-fr(G, Vr, Pn[i]) / tv for i in range(n)]
        j = max(range(n), key=lambda i: ch[i])
        w[j] *= 1.0 + 0.5 / (1 + it / 20)
        tot = sum(w)
        w = [x / tot for x in w]
    Vr = [sum(w[i] * Pn[i][k] for i in range(n)) for k in range(3)]
    tv = sqrt(-fr(G, Vr, Vr))
    Vr = [x / tv for x in Vr]
    return Vr, max((fr(G, Vr, p)) ** 2 for p in Pn)


def centre_exact(R, G, corners, Vr):
    rt = sqrt(R.disc)
    wb, wc = (R.c1 + rt) / 2, (R.c1 - rt) / 2
    f = lambda u, v: float(bil(G, u, v))
    best = None
    for scale in (8, 16, 32, 64, 128):
        tgt = [scale * x for x in Vr]
        V = [R(round(-t * wc / (wb - wc)), round(t / (wb - wc))) for t in tgt]
        VV = bil(G, V, V)
        if not float(VV) < 0 or any(f(V, p) >= 0 for p in corners):
            continue
        C2 = max(f(V, p) ** 2 / (float(VV) * f(p, p)) for p in corners)
        C2q = Fr(C2).limit_denominator(1000) + Fr(1, 1000)
        if best is None or C2q < best[2] * Fr(101, 100):
            best = (V, VV, C2q)
    return best


def leaf_cost(R, G, corners, norms, cap=10 ** 8):
    Vr, _ = centre_real(G, corners)
    V, VV, C2 = centre_exact(R, G, corners, Vr)
    GV = mat_vec(G, V)
    VV1, VV2 = float(VV), VV.sfloat()
    rt = sqrt(R.disc)
    wb = (R.c1 + rt) / 2
    best = None
    for fac in (0.5, 1.0, 2.0):
        target = max(fac * (2 * float(C2) - 1) * abs(VV1) - VV2, 1.5 * VV2)
        y = -round(target / rt)
        x = round(-y * wb)
        mu = R(x, y)
        if not (abs(float(mu)) < abs(VV1) and mu.sfloat() > VV2):
            continue
        Psi = [[2 * GV[i] * GV[j] + (mu - VV) * G[i][j] for j in range(3)] for i in range(3)]
        T, _ = trace_form(Psi)
        q = _ldl(T)
        if not all(q[i][i] > 0 for i in range(6)):
            continue
        K = max((2 * float(C2) - 1) * float(m) * abs(VV1) + m.sfloat() * VV2
                + (mu * m).trace() for m in norms)
        U = lll_gram(T)
        T2 = [[sum(U[i][a] * T[i][j] * U[j][b] for i in range(6) for j in range(6))
               for b in range(6)] for a in range(6)]
        nodes, leaves = count_nodes(T2, Fr(int(K) + 1))
        if best is None or nodes < best[0]:
            best = (nodes, leaves, float(C2))
    return best


def split_point(G, X, Y):
    tx = sqrt(-fr(G, [float(c) for c in X], [float(c) for c in X]))
    ty = sqrt(-fr(G, [float(c) for c in Y], [float(c) for c in Y]))
    r = ty / tx            # midpoint direction X/tx + Y/ty ~ r X + Y
    best = None
    for k in range(1, 9):
        for l in range(1, 9):
            err = abs(k / l - r) / r
            if best is None or err < best[0]:
                best = (err, k, l)
    _, k, l = best
    return [k * a + l * b for a, b in zip(X, Y)], (k, l)


def subdivide(G, tri, thr, depth=0, maxdepth=12):
    _, c2 = centre_real(G, tri)
    if c2 <= thr or depth >= maxdepth:
        return [tri]
    A, B, C = tri
    # longest edge
    def ch(X, Y):
        Xr = [float(c) for c in X]
        Yr = [float(c) for c in Y]
        return -fr(G, Xr, Yr) / sqrt(fr(G, Xr, Xr) * fr(G, Yr, Yr))
    edges = [(ch(A, B), 0), (ch(B, C), 1), (ch(C, A), 2)]
    _, e = max(edges)
    if e == 1:
        A, B, C = B, C, A
    elif e == 2:
        A, B, C = C, A, B
    M, _ = split_point(G, A, B)
    return subdivide(G, [A, M, C], thr, depth + 1) + subdivide(G, [M, B, C], thr, depth + 1)


def main():
    D = int(sys.argv[1])
    thr = float(sys.argv[2])
    first = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    last = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    R = get_ring(D)
    data = json.load(open(FILES[D]))
    tot = 0
    for ci, c in enumerate(data["classes"]):
        if ci < first or ci > last:
            continue
        G = [[from_json(R, e) for e in row] for row in c["gram"]]
        roots = [[from_json(R, e) for e in r] for r in c["polygon"]["roots"]]
        t0 = time.time()
        P = vertices(R, G, roots)
        norms = root_norm_reps_list(R, 2 * det(G))
        tris = []
        for k in range(1, len(P) - 1):
            tris += subdivide(G, [P[0], P[k], P[k + 1]], thr)
        nodes = 0
        c2max = 0
        for t in tris:
            nd, lv, c2 = leaf_cost(R, G, t, norms)
            nodes += nd
            c2max = max(c2max, c2)
        tot += nodes
        print(f"class {ci} sides {len(P)} leaves {len(tris)} maxC2 {c2max:.2f} "
              f"nodes {nodes} ({time.time() - t0:.1f}s)", flush=True)
    print("total nodes", tot)


if __name__ == "__main__":
    main()
