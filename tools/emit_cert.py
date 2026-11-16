"""Emit a complete reflectivity certificate (Lean, checked by `reflective_of_check`).

Data: the polygon (roots rs, vertices Ps, Bezout coefficients cf of each root, an
orthogonal basis f with f 2 = Ps 0, interior point Xs = sum of the vertices), the window
of B7 (u = fundamental unit, p/q >= rho), and a chain Bs through the vertices
Ps 0, ..., Ps (n-1) (refined by points kA + lB on long edges), cut into cells. Each cell has
its own centre and enumeration certificate; a cell is split (recursively, by halving its
run of segments, or by subdividing a single segment) until its stopped search has at most
`cap` nodes.

Usage: python tools/emit_cert.py D class_index out.lean [cap] [chunk]
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as Fr
from math import isqrt, ceil

sys.path.insert(0, ".")
from zphi.ring import get_ring, from_json, egcd, gcd_list  # noqa: E402
from zphi.linalg import bil, det, mat_vec  # noqa: E402
from zphi.definite import _ldl, lll_gram, trace_form  # noqa: E402
from tools.b8_size import FILES  # noqa: E402
from tools.b8_split import vertices, centre_real, split_point  # noqa: E402
from tools import emit_polyenum as E  # noqa: E402

sys.setrecursionlimit(10000)


MAX_PREFIXES = 40000  # bounds the emitter's memory and the file size


class Cap(Exception):
    pass


def count_capped(a, w, B, cap):
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
            if cnt > cap:
                raise Cap
            z[i] = t
            rec(i, B - w[i] * (a[i][i] * t + c) ** 2)
        z[i] = 0

    try:
        rec(n, B)
    except Cap:
        return cap + 1
    return cnt


def prefixes(a, w, B, chunk, with_sizes=False):
    """Cut the stopped search (as `enumAuxS`, n = 6, stop = 2) into subtrees of at most
    `chunk` nodes: the list of prefixes (top coordinate first) at which `coverAux` stops."""
    n = 6
    z = [0] * n

    def size(k, B):
        if k <= 2:
            return 1
        if B < 0:
            return 0
        i = k - 1
        c = sum(a[i][j] * z[j] for j in range(i + 1, n))
        s = isqrt(B // w[i])
        tot = 0
        for t in range((-s - c) // a[i][i], (s - c) // a[i][i] + 1):
            z[i] = t
            tot += 1 + size(i, B - w[i] * (a[i][i] * t + c) ** 2)
        z[i] = 0
        return tot

    out = []

    def rec(k, B, p):
        sz = 1 if k <= 2 else size(k, B)
        if sz <= chunk:
            out.append(list(p))
            sizes.append(sz)
            if len(out) > MAX_PREFIXES:
                raise RuntimeError(f"more than {MAX_PREFIXES} subtrees in one cell")
            return
        if B < 0:
            return
        i = k - 1
        c = sum(a[i][j] * z[j] for j in range(i + 1, n))
        s = isqrt(B // w[i])
        for t in range((-s - c) // a[i][i], (s - c) // a[i][i] + 1):
            z[i] = t
            rec(i, B - w[i] * (a[i][i] * t + c) ** 2, p + [t])
        z[i] = 0

    sizes = []
    rec(n, B, [])
    if with_sizes:
        return out, sizes
    return out


def enum_data(R, G, V, mu, qC, K, cap):
    """As emit_polyenum.enum_data, with a capped node count."""
    GV = mat_vec(G, V)
    VV = bil(G, V, V)
    Psi = [[2 * qC * GV[i] * GV[j] + (mu - qC * VV) * G[i][j] for j in range(3)]
           for i in range(3)]
    A, _ = trace_form(Psi)
    best = None
    for k in range(3):
        order = [2 * k, 2 * k + 1] + [i for i in range(6) if i // 2 != k]
        P = [[int(order[c] == r) for c in range(6)] for r in range(6)]
        A1 = E.matmul(E.transpose(P), E.matmul(A, P))
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
        from math import lcm
        for row in T4:
            for x in row:
                den = lcm(den, x.denominator)
        V4 = lll_gram([[int(x * den) for x in row] for row in T4])
        B = [[int(i == j) for j in range(6)] for i in range(6)]
        for i in range(4):
            for j in range(4):
                B[2 + i][2 + j] = V4[i][j]
        U = E.matmul(P, B)
        Uinv = E.int_inv(U)
        F = E.matmul(E.transpose(U), E.matmul(A, U))
        a, w, S = E.ldl_int(F)
        nodes = count_capped(a, w, S * K, cap if best is None else min(cap, best[0]))
        if best is None or nodes < best[0]:
            best = (nodes, a, w, S, U, Uinv, k)
    return best


def make_cell(R, G, pts, norms, cap):
    """Centre, bound and enumeration data for the points `pts`, or None."""
    Vr, _ = centre_real(G, pts)
    try:
        V, C2 = E.centre_exact(R, G, pts, Vr)
    except (TypeError, ValueError):
        return None
    pC, qC = C2.numerator, C2.denominator
    VV = bil(G, V, V)
    for p_ in pts:
        X = pC * VV * bil(G, p_, p_) - qC * bil(G, V, p_) ** 2
        if X.sign() < 0:
            return None
    VV1, VV2 = float(VV), VV.sfloat()
    rt = R.disc ** 0.5
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
        K = max(E.floor_el(X) + 1 for X in Xs)
        ed = enum_data(R, G, V, mu, qC, K, cap)
        if best is None or ed[0] < best[0][0]:
            best = (ed, mu, K)
    if best is None:
        return None
    (nodes, a, w, S, U, Uinv, k), mu, K = best
    return dict(V=V, pC=pC, qC=qC, mu=mu, K=K, a=a, w=w, S=S, U=U, Uinv=Uinv, nodes=nodes)


def primitive_future(R, G, M, ref):
    g = gcd_list(M, R)
    M = [x / g for x in M]
    if bil(G, M, ref).sign() > 0:
        M = [-x for x in M]
    return M


def cover(R, G, pts, norms, cap, depth=0, maxcell=None):
    """List of (points, cell) covering the chain `pts` (consecutive points). A cell is
    accepted when its stopped search has at most `cap` nodes, or (single segment) when
    subdividing it no longer reduces the total."""
    maxcell = maxcell or 50 * cap
    cell = make_cell(R, G, pts, norms, maxcell)
    nodes = cell["nodes"] if cell is not None else None
    print(f"  {'  ' * min(depth, 20)}{len(pts)} pts: "
          f"{'-' if nodes is None else nodes}", file=sys.stderr, flush=True)
    if cell is not None and nodes <= cap:
        return [(pts, cell)]
    if len(pts) >= 3:
        m = len(pts) // 2
        return (cover(R, G, pts[:m + 1], norms, cap, depth + 1, maxcell)
                + cover(R, G, pts[m:], norms, cap, depth + 1, maxcell))
    A, B = pts
    M, _ = split_point(G, A, B)
    M = primitive_future(R, G, M, A)
    if cell is not None and nodes <= maxcell:  # an exact count (not capped)
        cA = make_cell(R, G, [A, M], norms, maxcell)
        cB = make_cell(R, G, [M, B], norms, maxcell)
        if (depth >= 30 or cA is None or cB is None
                or cA["nodes"] + cB["nodes"] >= 0.8 * nodes):
            return [(pts, cell)]
    elif depth >= 30:
        raise RuntimeError("cover: depth limit without an acceptable cell")
    return (cover(R, G, [A, M], norms, cap, depth + 1, maxcell)
            + cover(R, G, [M, B], norms, cap, depth + 1, maxcell))


def bezout(R, r):
    """c with c0 r0 + c1 r1 + c2 r2 = 1 (r primitive)."""
    g1, x1, y1 = egcd(r[0], r[1])
    g, x2, y2 = egcd(g1, r[2])
    # g is a unit: divide
    gi = g.inv()
    c = [x2 * x1 * gi, x2 * y1 * gi, y2 * gi]
    assert all(x.is_integral() for x in c)
    assert c[0] * r[0] + c[1] * r[1] + c[2] * r[2] == R.one
    return c


def det3(x, y, z):
    return (x[0] * (y[1] * z[2] - y[2] * z[1]) - x[1] * (y[0] * z[2] - y[2] * z[0])
            + x[2] * (y[0] * z[1] - y[1] * z[0]))


def polygon_data(R, G, roots):
    n = len(roots)
    P = vertices(R, G, roots)
    # orient P on the sheet of P[0]; roots outward (r . P_j <= 0)
    rs = []
    for r in roots:
        vals = [bil(G, r, p).sign() for p in P]
        if any(v > 0 for v in vals):
            r = [-x for x in r]
            vals = [bil(G, r, p).sign() for p in P]
        assert all(v <= 0 for v in vals)
        rs.append(r)
    f0 = rs[0]
    f1 = [bil(G, f0, f0) * y - bil(G, f0, rs[1]) * x for x, y in zip(f0, rs[1])]
    f1 = [x / gcd_list(f1, R) for x in f1]
    f2 = P[0]
    if (det3(f0, f1, f2) * det3(P[0], P[1], P[2])).sign() < 0:
        f1 = [-x for x in f1]
    f = [f0, f1, f2]
    Xs = [sum((p[k] for p in P), R.zero) for k in range(3)]
    cf = [bezout(R, r) for r in rs]
    # mirror polyCheck / admCheck
    bl = lambda u, v: bil(G, u, v)
    assert all(bl(f[i], f[j]).is_zero() for i in range(3) for j in range(3) if i != j)
    assert bl(f0, f0).sign() > 0 and bl(f1, f1).sign() > 0 and bl(f2, f2).sign() < 0
    assert all(bl(x, x).ssign() > 0 for x in f)
    assert det3(*f).norm_num() != 0 and det(G).sign() < 0
    for i in range(n):
        assert bl(rs[i], P[i]).is_zero() and bl(rs[(i + 1) % n], P[i]).is_zero()
    assert bl(rs[1], P[2]).sign() < 0 and bl(rs[0], P[n - 2]).sign() < 0
    assert all(bl(rs[j], P[0]).sign() < 0 for j in range(2, n))
    d0 = det3(*f)
    assert all((d0 * det3(P[0], P[i], P[i + 1])).sign() > 0 for i in range(1, n - 1))
    assert all(bl(p, p).sign() < 0 and bl(p, f2).sign() < 0 for p in P)
    assert bl(Xs, Xs).sign() < 0 and bl(Xs, f2).sign() < 0
    assert all(bl(r, Xs).sign() < 0 for r in rs)
    for r in rs:
        m = bl(r, r)
        assert m.tpos()
        GR = mat_vec(G, r)
        assert all((2 * x / m).is_integral() for x in GR)
    return rs, P, f, Xs, cf


def window(R, G):
    u = R.eps
    if float(u) < 0:
        u = -u
    if abs(float(u)) < abs(u.sfloat()):
        u = u.conj()
    rho = (float(u) / u.sfloat()) ** 2
    q = 1
    p = ceil(rho * 1.0001)
    uinv = u.inv()
    assert (u * u - u.conj() * u.conj()).sign() > 0
    assert (p * u.conj() * u.conj() - q * u * u).sign() >= 0
    Dd = 2 * det(G)
    ND = abs(Dd.norm_num())
    d = R.c1 ** 2 + 4 * R.c0
    Y = isqrt(p * ND // (q * d)) + 1
    while not p * ND <= q * d * Y * Y:
        Y += 1
    Sp = isqrt(4 * p * ND // q) + 1
    while not 4 * p * ND <= q * Sp * Sp:
        Sp += 1
    return u, uinv, p, q, Y, Sp, Dd


def build(D, ci, cap, maxcell=None):
    R = get_ring(D)
    data = json.load(open(FILES[D]))
    c = data["classes"][ci]
    G = [[from_json(R, e) for e in row] for row in c["gram"]]
    roots = [[from_json(R, e) for e in r] for r in c["polygon"]["roots"]]
    rs, P, f, Xs, cf = polygon_data(R, G, roots)
    u, uinv, p, q, Y, Sp, Dd = window(R, G)
    norms = E.window_norms(R, Dd, p, q, Y, Sp)
    maxcell = maxcell or 50 * cap
    pieces = cover(R, G, P, norms, cap, maxcell=maxcell)
    big = [cell["nodes"] for _, cell in pieces if cell["nodes"] > maxcell]
    if big:  # the count was capped: the true size is unknown (possibly huge)
        raise RuntimeError(f"{len(big)} cell(s) above the node cap {maxcell}")
    Bs = list(pieces[0][0])
    seg = [0] * (len(Bs) - 1)
    cells = [pieces[0][1]]
    for k, (pts, cell) in enumerate(pieces[1:], start=1):
        assert pts[0] == Bs[-1]
        Bs += pts[1:]
        seg += [k] * (len(pts) - 1)
        cells.append(cell)
    idx = []
    for p_ in P:
        idx.append(next(j for j, b in enumerate(Bs) if b == p_))
    return dict(R=R, G=G, rs=rs, P=P, f=f, Xs=Xs, cf=cf, u=u, uinv=uinv, p=p, q=q, Y=Y,
                Sp=Sp, Dd=Dd, norms=norms, Bs=Bs, seg=seg, cells=cells, idx=idx)


def lean_file(D, ci, C, ns, chunk=300, header_only=False):
    R = C["R"]
    a, b = R.c0, R.c1
    el, vec, lmat = E.el, E.vec, E.lmat
    vlist = lambda vs: "[" + ", ".join(vec(v) for v in vs) + "]"
    n = len(C["P"])
    pid = ("isPrincipalIdealRing_of_boxBound boxBound_three_one" if (a, b) == (3, 1)
           else "isPrincipalIdealRing (by norm_num)")
    ringmod = {(1, 1): "ZPhi", (3, 1): "ZSqrt13", (2, 0): "ZSqrt2"}[(a, b)]
    L = [
        "import ReflectZphi.Cert.FastLeaf",
        f"import ReflectZphi.Ring.{ringmod}",
        "",
        f"/-! Generated by tools/emit_cert.py (class {ci} of {FILES[D]}). Do not edit. -/",
        "",
        f"namespace {ns}",
        "",
        "open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms",
        "  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf",
        "",
        f"abbrev OK := QuadraticAlgebra ℤ {a} {b}",
        "",
        "def G : Matrix (Fin 3) (Fin 3) OK := !![" + "; ".join(
            ", ".join(el(x) for x in row) for row in C["G"]) + "]",
        f"def n : ℕ := {n}",
        "def rsL : List (Fin 3 → OK) := " + vlist(C["rs"]),
        "def PsL : List (Fin 3 → OK) := " + vlist(C["P"]),
        "def cfL : List (Fin 3 → OK) := " + vlist(C["cf"]),
        "def rs (i : ℕ) : Fin 3 → OK := rsL.getD i ![0, 0, 0]",
        "def Ps (i : ℕ) : Fin 3 → OK := PsL.getD i ![0, 0, 0]",
        "def cf (i : ℕ) : Fin 3 → OK := cfL.getD i ![0, 0, 0]",
        "def f : Fin 3 → Fin 3 → OK := ![" + ", ".join(vec(v) for v in C["f"]) + "]",
        f"def Xs : Fin 3 → OK := {vec(C['Xs'])}",
        f"def D2 : OK := {el(C['Dd'])}",
        f"def u : OK := {el(C['u'])}",
        f"def uinv : OK := {el(C['uinv'])}",
        "def normsL : List OK := [" + ", ".join(el(m) for m in C["norms"]) + "]",
        f"def N : ℕ := {len(C['Bs'])}",
        "def BsL : List (Fin 3 → OK) := " + vlist(C["Bs"]),
        "def Bs (j : ℕ) : Fin 3 → OK := BsL.getD j ![0, 0, 0]",
        "def idx (i : ℕ) : ℕ := (" + str(C["idx"]) + " : List ℕ).getD i 0",
        "def seg (j : ℕ) : ℕ := (" + str(C["seg"]) + " : List ℕ).getD j 0",
        f"def nc : ℕ := {len(C['cells'])}",
        "",
    ]
    for k, c in enumerate(C["cells"]):
        L += [
            f"def aM{k} : List (List ℤ) := " + lmat(c["a"]),
            f"def UM{k} : List (List ℤ) := " + lmat(c["U"]),
            f"def UiM{k} : List (List ℤ) := " + lmat(c["Uinv"]),
            f"def wL{k} : List ℤ := [" + ", ".join(map(str, c["w"])) + "]",
            f"def cell{k} : CellData {a} {b} where",
            f"  V := {vec(c['V'])}",
            f"  pC := {c['pC']}",
            f"  qC := {c['qC']}",
            f"  μ := {el(c['mu'])}",
            f"  K := {c['K']}",
            f"  aL i j := (aM{k}.getD i []).getD j 0",
            f"  w i := wL{k}.getD i 0",
            f"  S := {c['S']}",
            f"  U i j := (UM{k}.getD i []).getD j 0",
            f"  Uinv i j := (UiM{k}.getD i []).getD j 0",
            "",
        ]
    nc = len(C["cells"])
    L += [
        "def cellsL : List (CellData " + f"{a} {b}) := [" +
        ", ".join(f"cell{k}" for k in range(nc)) + "]",
        "def cells (k : ℕ) : CellData " + f"{a} {b} := cellsL.getD k cell0",
        "",
        "theorem poly_ok : polyCheck G n f rs Ps Xs cf = true := by decide +kernel",
        "theorem adm_ok : admCheck G f = true := by decide +kernel",
        f"theorem win_ok : winCheck G D2 u uinv {C['p']} {C['q']} {C['Y']} {C['Sp']} = true := by",
        "  decide +kernel",
        f"theorem norms_eq : windowNorms {a} {b} D2 {C['p']} {C['q']} {C['Y']} {C['Sp']} = normsL := by",
        "  decide +kernel",
        "theorem chain_ok : chainCheck G f n Ps N Bs idx nc cells seg = true := by decide +kernel",
    ]
    for k, c in enumerate([] if header_only else C["cells"]):
        pre = prefixes(c["a"], c["w"], c["S"] * c["K"], chunk)
        c["npre"] = len(pre)
        lst = lambda p: "[" + ", ".join(map(str, p)) + "]"
        # the fast leaf's table: A = u0.u0, Bc j = u0.c_j, Q j l = c_j.c_l, Am = [A m]
        U = c["U"]
        col = [[R(U[2 * i][j], U[2 * i + 1][j]) for i in range(3)] for j in range(6)]
        A_ = bil(C["G"], col[0], col[0])
        Bc = [R(0, 0)] * 2 + [bil(C["G"], col[0], col[j]) for j in range(2, 6)]
        Q = [[R(0, 0)] * 6 for _ in range(2)] + [
            [R(0, 0)] * 2 + [bil(C["G"], col[j], col[l]) for l in range(2, 6)]
            for j in range(2, 6)]
        L += [
            f"def ld{k} : LeafData {a} {b} where",
            f"  A := {el(A_)}",
            "  Bc j := ([" + ", ".join(el(x) for x in Bc) + "] : List OK).getD j 0",
            "  Q j l := ((" + "[" + ", ".join(
                "[" + ", ".join(el(x) for x in row) + "]" for row in Q) +
            "] : List (List OK)).getD j []).getD l 0",
            "  Am := [" + ", ".join(el(A_ * m) for m in C["norms"]) + "]",
            f"theorem ld_ok{k} : ldCheck G cell{k}.U normsL ld{k} = true := by decide +kernel",
        ]
        L += [
            "",
        ]
        blocks = [list(range(i0, min(i0 + 32, len(pre)))) for i0 in range(0, len(pre), 32)]
        for bi, blk in enumerate(blocks):
            L += [
                "set_option maxHeartbeats 0 in",
                f"def blk{k}_{bi} : List (List ℤ) := [" + ", ".join(lst(pre[i]) for i in blk) + "]",
            ]

        def app(xs):
            return xs[0] if len(xs) == 1 else f"{xs[0]} ++ ({app(xs[1:])})"

        def glue(hs):
            return hs[0] if len(hs) == 1 else f"List.forall_mem_append.2 ⟨{hs[0]}, {glue(hs[1:])}⟩"

        L += [
            f"def preL{k} : List (List ℤ) := " + app([f"blk{k}_{bi}" for bi in range(len(blocks))]),
            f"def sub{k} : List ℤ → Bool := sub cell{k}.aL cell{k}.w 6 2 "
            f"(leaf4 G n Ps normsL cell{k}.U ld{k}) (6, fun _ => 0, cell{k}.S * cell{k}.K)",
            f"theorem cover{k} : coverAux cell{k}.aL cell{k}.w 6 2 preL{k} 6 (fun _ => 0) "
            f"(cell{k}.S * cell{k}.K) [] = true := by decide +kernel",
        ]
        for i, p in enumerate(pre):
            L += [f"theorem sub{k}_{i} : sub{k} {lst(p)} = true := by decide +kernel"]
        for bi, blk in enumerate(blocks):
            L += [
                f"theorem sb{k}_{bi} : ∀ q ∈ blk{k}_{bi}, sub{k} q = true := by",
                f"  unfold blk{k}_{bi}",
                "  exact " + "".join(f"List.forall_mem_cons.2 ⟨sub{k}_{i}, " for i in blk)
                + "List.forall_mem_nil _" + "⟩" * len(blk),
            ]
        L += [
            f"theorem subs{k} : ∀ q ∈ preL{k}, sub{k} q = true := by",
            f"  unfold preL{k}",
            "  exact " + glue([f"sb{k}_{bi}" for bi in range(len(blocks))]),
            f"theorem cell_ok{k} : cellCheck G f n Ps normsL cell{k} = true :=",
            f"  cellCheck_fast4 (by decide +kernel) ld_ok{k} (enumS_of_cover cover{k} subs{k})",
        ]
    L += [
        "theorem cells_ok : ∀ k, k < nc → cellCheck G f n Ps normsL (cells k) = true := by",
        "  intro k hk",
        "  simp only [nc] at hk",
        "  interval_cases k",
        "  exacts [" + ", ".join(f"cell_ok{k}" for k in range(nc)) + "]",
        "",
        f"theorem hd : (0 : ℝ) < (({b} : ℤ) : ℝ) ^ 2 + 4 * (({a} : ℤ) : ℝ) := by norm_num",
        "",
        "/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/",
        "theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by",
        f"  haveI : IsPrincipalIdealRing OK := {pid}",
        "  exact reflective_of_check hV (by",
        f"      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr ({a} : ℤ) {b}))).out",
        "      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok",
        "    cells_ok",
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(L)


def lean_files(D, ci, C, ns, chunk=300, budget=15000):
    """Split form of `lean_file`: {module suffix: text}. "" is the main module (cover
    theorems, gluing, `reflective`); "Base" holds the data, the cheap checks and each
    cell's table; "P###" hold the subtree theorems, at most `budget` search nodes each.
    Each module is checked in its own process, so the kernel's memory is per module."""
    mono = lean_file(D, ci, C, ns, chunk, header_only=True)  # header and tail only
    lines = mono.split("\n")
    head_end = lines.index("theorem poly_ok : polyCheck G n f rs Ps Xs cf = true := by decide +kernel")
    header = lines[:head_end]           # imports, namespace, open, data defs, cells
    imports = [l for l in header if l.startswith("import ")]
    body = header[len(imports):]
    base_ns = f"{ns}"
    lst = lambda p: "[" + ", ".join(map(str, p)) + "]"
    R = C["R"]
    a, b = R.c0, R.c1
    el = E.el
    nc = len(C["cells"])
    # pieces of the monolithic file, regrouped
    base_tail = lines[head_end:head_end + 7]   # poly_ok .. chain_ok
    base = imports + body + base_tail
    main = [f"import {ns}.Base"]
    parts = []        # list of line lists
    cur, cur_nodes, cur_names = [], 0, []
    part_of = {}
    for k, c in enumerate(C["cells"]):
        pre, sizes = prefixes(c["a"], c["w"], c["S"] * c["K"], chunk, with_sizes=True)
        U = c["U"]
        col = [[R(U[2 * i][j], U[2 * i + 1][j]) for i in range(3)] for j in range(6)]
        A_ = bil(C["G"], col[0], col[0])
        Bc = [R(0, 0)] * 2 + [bil(C["G"], col[0], col[j]) for j in range(2, 6)]
        Q = [[R(0, 0)] * 6 for _ in range(2)] + [
            [R(0, 0)] * 2 + [bil(C["G"], col[j], col[l]) for l in range(2, 6)]
            for j in range(2, 6)]
        base += [
            f"def ld{k} : LeafData {a} {b} where",
            f"  A := {el(A_)}",
            "  Bc j := ([" + ", ".join(el(x) for x in Bc) + "] : List OK).getD j 0",
            "  Q j l := ((" + "[" + ", ".join(
                "[" + ", ".join(el(x) for x in row) + "]" for row in Q) +
            "] : List (List OK)).getD j []).getD l 0",
            "  Am := [" + ", ".join(el(A_ * m) for m in C["norms"]) + "]",
            f"theorem ld_ok{k} : ldCheck G cell{k}.U normsL ld{k} = true := by decide +kernel",
            "",
        ]
        blocks = [list(range(i0, min(i0 + 32, len(pre)))) for i0 in range(0, len(pre), 32)]
        for bi, blk in enumerate(blocks):
            base += [
                "set_option maxHeartbeats 0 in",
                f"def blk{k}_{bi} : List (List ℤ) := [" + ", ".join(lst(pre[i]) for i in blk) + "]",
            ]

        # balanced: nesting depth log2(#blocks), not #blocks (the elaborator's recursion limit)
        def app(xs):
            if len(xs) == 1:
                return xs[0]
            h = len(xs) // 2
            return f"({app(xs[:h])}) ++ ({app(xs[h:])})"

        def glue(hs):
            if len(hs) == 1:
                return hs[0]
            h = len(hs) // 2
            return f"List.forall_mem_append.2 ⟨{glue(hs[:h])}, {glue(hs[h:])}⟩"

        base += [
            f"def preL{k} : List (List ℤ) := " + app([f"blk{k}_{bi}" for bi in range(len(blocks))]),
            f"def sub{k} : List ℤ → Bool := sub cell{k}.aL cell{k}.w 6 2 "
            f"(leaf4 G n Ps normsL cell{k}.U ld{k}) (6, fun _ => 0, cell{k}.S * cell{k}.K)",
            "",
        ]
        for bi, blk in enumerate(blocks):
            nodes = sum(sizes[i] for i in blk)
            if cur and cur_nodes + nodes > budget:
                parts.append(cur); cur, cur_nodes = [], 0
            cur += [f"theorem sub{k}_{i} : sub{k} {lst(pre[i])} = true := by decide +kernel" for i in blk]
            cur += [
                f"theorem sb{k}_{bi} : ∀ q ∈ blk{k}_{bi}, sub{k} q = true := by",
                f"  unfold blk{k}_{bi}",
                "  exact " + "".join(f"List.forall_mem_cons.2 ⟨sub{k}_{i}, " for i in blk)
                + "List.forall_mem_nil _" + "⟩" * len(blk),
            ]
            cur_nodes += nodes
        main += [
            f"theorem cover{k} : (coverL cell{k}.aL cell{k}.w 6 2 6 (fun _ => 0) "
            f"(cell{k}.S * cell{k}.K) [] preL{k}).isSome = true := by decide +kernel",
            f"theorem subs{k} : ∀ q ∈ preL{k}, sub{k} q = true := by",
            f"  unfold preL{k}",
            "  exact " + glue([f"sb{k}_{bi}" for bi in range(len(blocks))]),
            f"theorem cell_ok{k} : cellCheck G f n Ps normsL cell{k} = true :=",
            f"  cellCheck_fast4 (by decide +kernel) ld_ok{k} (enumS_of_coverL cover{k} subs{k})",
        ]
        c["npre"] = len(pre)
    if cur:
        parts.append(cur)
    tail_start = lines.index("theorem cells_ok : ∀ k, k < nc → cellCheck G f n Ps normsL (cells k) = true := by")
    opener = [l for l in body if l.startswith("namespace ") or l.startswith("open ") or l.startswith("  ReflectZphi.Enum")]
    main_hdr = ["import ReflectZphi.Cert.Cover"] + main[:1] + [f"import {ns}.P{j:03d}" for j in range(len(parts))] + ["", *opener, ""]
    main = main_hdr + main[1:] + lines[tail_start:]
    out = {"Base": "\n".join(base + ["", f"end {ns}", ""]), "": "\n".join(main)}
    for j, pl in enumerate(parts):
        out[f"P{j:03d}"] = "\n".join([f"import {ns}.Base", "", *opener, "", *pl, "", f"end {ns}", ""])
    return out


def main():
    D, ci, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    chunk = int(sys.argv[5]) if len(sys.argv) > 5 else 300
    t0 = time.time()
    C = build(D, ci, cap)
    nodes = [c["nodes"] for c in C["cells"]]
    print(f"class {ci}: n={len(C['P'])} chain={len(C['Bs'])} cells={len(nodes)} "
          f"nodes={sum(nodes)} max={max(nodes)} ({time.time() - t0:.1f}s)", flush=True)
    ns = f"ReflectZphi.Data.Cert{D}_{ci:03d}"
    open(out, "w").write(lean_file(D, ci, C, ns, chunk))
    print("prefixes per cell:", [c["npre"] for c in C["cells"]])


if __name__ == "__main__":
    main()
