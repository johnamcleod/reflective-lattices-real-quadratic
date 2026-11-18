"""Emit a reflectivity certificate in the per-norm sublattice form (Lean: Cert/Sublat.lean).

For each cell (centre V, pC, qC, mu from emit_cert.build) and each window norm m, the roots of
norm m are searched in L_m = {r : (2/m) G r in O^3} (tools/sublat.py) with the bound K_m of m
alone. Per (cell, norm) the certificate carries the search basis U (6x6 integer, columns in
L_m, column 1 = w * column 0), the coordinate certificate (Pz, Qz) checked by `subCheck`,
the LDL data (aL, w, S) of the form in U-coordinates, the fast-leaf table, and the subtree
prefixes of the stopped search. Modules: C###/Base.lean (data, cheap checks), C###/P###.lean
(subtree theorems, at most `budget` nodes each), C###.lean (covers, glue, `reflective`).

Usage (library): lean_files_sub(D, ci, C, ns, chunk, budget) -> {suffix: text}
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")
from zphi.linalg import bil, mat_mul, mat_vec, transpose  # noqa: E402
from tools import emit_polyenum as E  # noqa: E402
from tools.emit_cert import prefixes  # noqa: E402
from tools.sublat import enum_psi, sub_basis  # noqa: E402


def zmat(R, M):
    """6x6 integer matrix of the O-matrix M on the Z-basis (e_0, w e_0, e_1, w e_1, ...)."""
    Z = [[0] * 6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            for t, c in enumerate((R.one, R.w)):
                x = M[i][j] * c
                a, b = Fr(x.a, x.n), Fr(x.b, x.n)
                assert a.denominator == 1 and b.denominator == 1, x
                Z[2 * i][2 * j + t] = int(a)
                Z[2 * i + 1][2 * j + t] = int(b)
    return Z


def bndK(R, G, c, m):
    VV = bil(G, c["V"], c["V"])
    pC, qC, mu = c["pC"], c["qC"], c["mu"]
    return E.floor_el((2 * pC - qC) * m * (-VV) + mu * m + (qC * m * VV + mu * m).conj()) + 1


def group_basis(R, bases, g):
    """O-basis (columns) of the sum of the L_m, m in the group g (indices into bases)."""
    from zphi.linalg import hnf_basis
    gens = [[bases[i][0][r][j] for r in range(3)] for i in g for j in range(3)]
    return hnf_basis(gens)


def psi_of(G, c):
    V, qC, mu = c["V"], c["qC"], c["mu"]
    VV = bil(G, V, V)
    GV = mat_vec(G, V)
    return [[2 * qC * GV[i] * GV[j] + (mu - qC * VV) * G[i][j] for j in range(3)] for i in range(3)]


def group_count(R, G, c, norms, bases, g, cap):
    B = group_basis(R, bases, g)
    Psi = psi_of(G, c)
    K = max(bndK(R, G, c, norms[i]) for i in g)
    return enum_psi(R, mat_mul(transpose(B), mat_mul(Psi, B)), K, cap)[0]


def subcell_group(R, G, c, norms, bases, g, cap=10 ** 9):
    """The search data of the norm group g (indices) in cell c: lattice = sum of the L_m."""
    from zphi.linalg import inv
    Bg = group_basis(R, bases, g) if len(g) > 1 else bases[g[0]][0]
    Bgi = inv(Bg)
    Psi = psi_of(G, c)
    Psi2 = mat_mul(transpose(Bg), mat_mul(Psi, Bg))
    K = max(bndK(R, G, c, norms[i]) for i in g)
    nodes, a, w, S, Uo, Uoi, _ = enum_psi(R, Psi2, K, cap)
    U = E.matmul(zmat(R, Bg), Uo)
    Pzs, Qzs = [], []
    for i in g:
        m = norms[i]
        B, P, Q = bases[i]
        T = mat_mul(Bgi, B)  # L_m in L_g: integral
        Pz = E.matmul(Uoi, zmat(R, mat_mul(T, P)))
        Qz = E.matmul(Uoi, zmat(R, mat_mul(T, Q)))
        Nm = m.norm_num()
        assert m.n == 1 and Nm != 0
        Tp = zmat(R, [[m.conj() * 2 * G[r][j] for j in range(3)] for r in range(3)])
        UP = E.matmul(U, Pz)
        UQT = E.matmul(U, E.matmul(Qz, Tp))
        for r in range(6):
            for j in range(6):
                assert Nm * (UP[r][j] - int(r == j)) + UQT[r][j] == 0
        Pzs.append(Pz)
        Qzs.append(Qz)
    col = lambda j: [R(U[2 * i][j], U[2 * i + 1][j]) for i in range(3)]
    for x, y in zip(col(1), [R.w * e for e in col(0)]):
        assert (x - y).is_zero()
    return dict(ms=[norms[i] for i in g], g=list(g), K=K, a=a, w=w, S=S, U=U, Pz=Pzs, Qz=Qzs,
                nodes=nodes)


def choose_groups(R, G, c, norms, bases):
    """Greedy merging of norm groups (start: singletons) while a merge lowers the total."""
    groups = [[i] for i in range(len(norms))]
    cnt = {(i,): group_count(R, G, c, norms, bases, [i], 10 ** 9) for i in range(len(norms))}
    while True:
        best = None
        for x in range(len(groups)):
            for y in range(x + 1, len(groups)):
                gk = tuple(sorted(groups[x] + groups[y]))
                sm = cnt[tuple(groups[x])] + cnt[tuple(groups[y])]
                if gk not in cnt:
                    cnt[gk] = group_count(R, G, c, norms, bases, list(gk), sm)
                if cnt[gk] < sm and (best is None or sm - cnt[gk] > best[0]):
                    best = (sm - cnt[gk], x, y, gk)
        if best is None:
            return groups
        _, x, y, gk = best
        groups = [gg for k, gg in enumerate(groups) if k not in (x, y)] + [list(gk)]


def subcell(R, G, c, m, basis, cap=10 ** 9):
    """The per-norm search data of norm m in cell c."""
    B, P, Q = basis
    V, qC, mu = c["V"], c["qC"], c["mu"]
    VV = bil(G, V, V)
    GV = mat_vec(G, V)
    Psi = [[2 * qC * GV[i] * GV[j] + (mu - qC * VV) * G[i][j] for j in range(3)] for i in range(3)]
    Psi2 = mat_mul(transpose(B), mat_mul(Psi, B))
    K = bndK(R, G, c, m)
    nodes, a, w, S, Uo, Uoi, _ = enum_psi(R, Psi2, K, cap)
    Bz = zmat(R, B)
    U = E.matmul(Bz, Uo)
    Pz = E.matmul(Uoi, zmat(R, P))
    Qz = E.matmul(Uoi, zmat(R, Q))
    # the subCheck identity: Nm(m) (U Pz - I) + U Qz T' = 0, T' = zmat(conj(m) 2 G)
    Nm = m.norm_num() if m.n == 1 else None
    assert Nm is not None and Nm != 0
    Tp = zmat(R, [[m.conj() * 2 * G[i][j] for j in range(3)] for i in range(3)])
    UP = E.matmul(U, Pz)
    UQT = E.matmul(U, E.matmul(Qz, Tp))
    for i in range(6):
        for j in range(6):
            assert Nm * (UP[i][j] - int(i == j)) + UQT[i][j] == 0
    # column 1 = w * column 0 (for the leaf)
    col = lambda j: [R(U[2 * i][j], U[2 * i + 1][j]) for i in range(3)]
    for x, y in zip(col(1), [R.w * e for e in col(0)]):
        assert (x - y).is_zero()
    return dict(m=m, K=K, a=a, w=w, S=S, U=U, Pz=Pz, Qz=Qz, nodes=nodes)


def make_cell_sub(R, G, pts, norms, bases, cap):
    """As emit_cert.make_cell, choosing mu by the total of the per-norm sublattice searches.
    Returns the cell with "nodes" (capped total) and "subs" (per-norm data), or None."""
    from tools.emit_cert import centre_real
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
        c = dict(V=V, pC=pC, qC=qC, mu=mu)
        subs = [subcell(R, G, c, m, bases[i], cap) for i, m in enumerate(norms)]
        tot = sum(d["nodes"] for d in subs)
        if best is None or tot < best["nodes"]:
            best = dict(c, nodes=tot, subs=subs)
    return best


def cover_sub(R, G, pts, norms, bases, cap, maxcell, depth=0):
    """As emit_cert.cover, with the per-norm sublattice node counts."""
    from tools.emit_cert import split_point, primitive_future
    cell = make_cell_sub(R, G, pts, norms, bases, maxcell)
    nodes = cell["nodes"] if cell is not None else None
    print(f"  {'  ' * min(depth, 20)}{len(pts)} pts: {'-' if nodes is None else nodes}",
          file=sys.stderr, flush=True)
    if cell is not None and nodes <= cap:
        return [(pts, cell)]
    if len(pts) >= 3:
        h = len(pts) // 2
        return (cover_sub(R, G, pts[:h + 1], norms, bases, cap, maxcell, depth + 1)
                + cover_sub(R, G, pts[h:], norms, bases, cap, maxcell, depth + 1))
    A, B = pts
    M, _ = split_point(G, A, B)
    M = primitive_future(R, G, M, A)
    exact = cell is not None and all(d["nodes"] < maxcell for d in cell["subs"])
    if depth >= 24 or M == A or M == B:
        if exact:
            return [(pts, cell)]
        raise RuntimeError("cover_sub: depth limit without an acceptable cell")
    split = []
    for seg in ([A, M], [M, B]):
        ch = make_cell_sub(R, G, seg, norms, bases, maxcell)
        ch_exact = ch is not None and all(d["nodes"] < maxcell for d in ch["subs"])
        if ch_exact and (ch["nodes"] <= cap or (exact and ch["nodes"] >= 0.95 * nodes)):
            split.append((seg, ch))  # small enough, or no progress (a vertex floor)
            continue
        try:
            split += cover_sub(R, G, seg, norms, bases, cap, maxcell, depth + 1)
        except RuntimeError:
            if not ch_exact:
                if exact:
                    return [(pts, cell)]
                raise
            split.append((seg, ch))
    if exact and sum(cl["nodes"] for _, cl in split) >= nodes:
        return [(pts, cell)]
    return split


def build_sub(D, ci, cap=5000, maxcell=2000000):
    """As emit_cert.build, with cells chosen by the per-norm sublattice counts."""
    import json
    from tools.b8_size import FILES
    from tools.emit_cert import polygon_data, window
    from zphi.ring import get_ring, from_json
    R = get_ring(D)
    c = json.load(open(FILES[D]))["classes"][ci]
    G = [[from_json(R, e) for e in row] for row in c["gram"]]
    roots = [[from_json(R, e) for e in r] for r in c["polygon"]["roots"]]
    rs, P, f, Xs, cf = polygon_data(R, G, roots)
    u, uinv, p, q, Y, Sp, Dd = window(R, G)
    norms = E.window_norms(R, Dd, p, q, Y, Sp)
    bases = [sub_basis(R, G, m) for m in norms]
    pieces = cover_sub(R, G, P, norms, bases, cap, maxcell)
    for _, cell in pieces:
        if any(d["nodes"] >= maxcell for d in cell["subs"]):
            raise RuntimeError(f"a per-norm search above the node cap {maxcell}")
    Bs = list(pieces[0][0])
    seg = [0] * (len(Bs) - 1)
    cells = [pieces[0][1]]
    for k, (pts, cell) in enumerate(pieces[1:], start=1):
        assert pts[0] == Bs[-1]
        Bs += pts[1:]
        seg += [k] * (len(pts) - 1)
        cells.append(cell)
    idx = [next(j for j, b in enumerate(Bs) if b == p_) for p_ in P]
    # groups chosen on a small cell (exact counts in Python are slow on large ones); the
    # groups found on different cells of one class are nearly the same
    import time as _t
    t0 = _t.time()
    rep = min((cl for cl in cells if cl["nodes"] >= 500), key=lambda cl: cl["nodes"],
              default=max(cells, key=lambda cl: cl["nodes"]))
    groups = choose_groups(R, G, rep, norms, bases)
    print(f"groups {groups} (on a cell of {rep['nodes']} nodes, {_t.time() - t0:.0f} s)",
          file=sys.stderr, flush=True)
    for cl in cells:
        cl["groups"] = [subcell_group(R, G, cl, norms, bases, g) for g in groups]
        cl["nodes_single"] = cl["nodes"]
        cl["nodes"] = sum(d["nodes"] for d in cl["groups"])
    return dict(groups=groups, R=R, G=G, rs=rs, P=P, f=f, Xs=Xs, cf=cf, u=u, uinv=uinv, p=p, q=q, Y=Y,
                Sp=Sp, Dd=Dd, norms=norms, Bs=Bs, seg=seg, cells=cells, idx=idx, bases=bases)


WIN_POINTS = 2000  # window points per kernel computation of norms_eq (one decide: > 4 GB at 50k)


def norms_chunks(C, a_, b_):
    """`norms_eq` via ReflectZphi.RootNorms.windowNorms_of_chunks: the rows y < Y in chunks of
    c rows, each its own `decide +kernel`. The rows of a chunk give the norms with ω-coefficient
    in its range (windowNorms walks y outermost), so the chunk lists are sublists of normsL."""
    el = E.el
    p, q, Y, S, norms = C["p"], C["q"], C["Y"], C["Sp"], C["norms"]
    c = max(1, WIN_POINTS // max(S, 1))
    k, r = divmod(Y, c)
    rows = lambda y0, n: "[" + ", ".join(el(m) for m in norms if y0 <= m.b < y0 + n) + "]"
    w = f"winRows {a_} {b_} D2 {p} {q} {S}"
    out = ["def winCsL : List (List OK) := [" + ", ".join(rows(c * i, c) for i in range(k)) + "]"]
    out += [f"theorem nw{i} : {w} ({c} * {i}) {c} = winCsL.getD {i} [] := by decide +kernel"
            for i in range(k)]
    out += [
        f"theorem nwr : {w} ({c} * {k}) {r} = {rows(c * k, r)} := by decide +kernel",
        f"theorem norms_eq : windowNorms {a_} {b_} D2 {p} {q} {Y} {S} = normsL :=",
        f"  (windowNorms_of_chunks D2 {p} {q} {S} {c} {k} {r} (fun i => winCsL.getD i []) _",
        "    (by intro i hi; interval_cases i" + (f"; exacts [{', '.join(f'nw{i}' for i in range(k))}]" if k else "") + ") nwr).trans",
        "    (by decide +kernel)",
    ]
    return out


PRE_COST = 1500  # budget weight of one group's ld_ok + pre_ok (in search nodes)


def lean_files_sub(D, ci, C, ns, chunk=300, budget=15000):
    from tools.b8_size import FILES
    R = C["R"]
    a_, b_ = R.c0, R.c1
    el, vec, lmat = E.el, E.vec, E.lmat
    G, norms = C["G"], C["norms"]
    n = len(C["P"])
    pid = ("isPrincipalIdealRing_of_boxBound boxBound_three_one" if (a_, b_) == (3, 1)
           else "isPrincipalIdealRing (by norm_num)")
    ringmod = {(1, 1): "ZPhi", (3, 1): "ZSqrt13", (2, 0): "ZSqrt2"}[(a_, b_)]
    vlist = lambda vs: "[" + ", ".join(vec(v) for v in vs) + "]"
    lst = lambda p: "[" + ", ".join(map(str, p)) + "]"
    opener = ["open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms",
              "  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split",
              "  ReflectZphi.FastLeaf ReflectZphi.Sublat"]
    base = [
        "import ReflectZphi.Cert.Sublat",
        "import ReflectZphi.Cert.WinSplit",
        f"import ReflectZphi.Ring.{ringmod}",
        "",
        f"/-! Generated by tools/emit_sub.py (class {ci} of {FILES[D]}). Do not edit. -/",
        "",
        f"namespace {ns}",
        "",
        *opener,
        "",
        f"abbrev OK := QuadraticAlgebra ℤ {a_} {b_}",
        "",
        "def G : Matrix (Fin 3) (Fin 3) OK := !![" + "; ".join(
            ", ".join(el(x) for x in row) for row in G) + "]",
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
        "def normsL : List OK := [" + ", ".join(el(m) for m in norms) + "]",
        f"def N : ℕ := {len(C['Bs'])}",
        "def BsL : List (Fin 3 → OK) := " + vlist(C["Bs"]),
        "def Bs (j : ℕ) : Fin 3 → OK := BsL.getD j ![0, 0, 0]",
        "def idx (i : ℕ) : ℕ := (" + str(C["idx"]) + " : List ℕ).getD i 0",
        "def seg (j : ℕ) : ℕ := (" + str(C["seg"]) + " : List ℕ).getD j 0",
        f"def nc : ℕ := {len(C['cells'])}",
        "",
    ]
    for k, c in enumerate(C["cells"]):
        base += [
            f"def cell{k} : CellData {a_} {b_} where",
            f"  V := {vec(c['V'])}",
            f"  pC := {c['pC']}",
            f"  qC := {c['qC']}",
            f"  μ := {el(c['mu'])}",
            "  K := 0",
            "  aL _ _ := 0",
            "  w _ := 0",
            "  S := 1",
            "  U _ _ := 0",
            "  Uinv _ _ := 0",
        ]
    nc = len(C["cells"])
    base += [
        "def cellsL : List (CellData " + f"{a_} {b_}) := [" +
        ", ".join(f"cell{k}" for k in range(nc)) + "]",
        "def cells (k : ℕ) : CellData " + f"{a_} {b_} := cellsL.getD k cell0",
        "",
    ]
    # Base holds data only; the checks go to Pchk (class-level) and the parts (per group),
    # so no single module accumulates them (class 88: 98 groups' checks in Base > 4 GB)
    chk = [
        "theorem poly_ok : polyCheck G n f rs Ps Xs cf = true := by decide +kernel",
        "theorem adm_ok : admCheck G f = true := by decide +kernel",
        "theorem basis_ok : basisCheck G f = true := by decide +kernel",
        f"theorem win_ok : winCheck G D2 u uinv {C['p']} {C['q']} {C['Y']} {C['Sp']} = true := by",
        "  decide +kernel",
        "theorem chain_ok : chainCheck G f n Ps N Bs idx nc cells seg = true := by decide +kernel",
    ]
    bases = C.get("bases") or [sub_basis(R, G, m) for m in norms]
    main = [f"import {ns}.Base"]
    parts, cur, cur_nodes = [], [], 0
    stats = []
    for k, c in enumerate(C["cells"]):
        names = []
        groups = c.get("groups") or [subcell_group(R, G, c, norms, bases, [i])
                                     for i in range(len(norms))]
        for i, d in enumerate(groups):
            nm = f"d{k}_{i}"
            names.append(nm)
            stats.append(d["nodes"])
            U = d["U"]
            col = [[R(U[2 * r][j], U[2 * r + 1][j]) for r in range(3)] for j in range(6)]
            A_ = bil(G, col[0], col[0])
            Bc = [R(0, 0)] * 2 + [bil(G, col[0], col[j]) for j in range(2, 6)]
            Q = [[R(0, 0)] * 6 for _ in range(2)] + [
                [R(0, 0)] * 2 + [bil(G, col[j], col[l]) for l in range(2, 6)] for j in range(2, 6)]
            base += [
                f"def {nm} : SubCell {a_} {b_} where",
                "  ms := [" + ", ".join(el(m) for m in d["ms"]) + "]",
                f"  K := {d['K']}",
                f"  aL i j := ({lmat(d['a'])} : List (List ℤ)).getD i [] |>.getD j 0",
                f"  w i := ({lst(d['w'])} : List ℤ).getD i 0",
                f"  S := {d['S']}",
                f"  U i j := ({lmat(U)} : List (List ℤ)).getD i [] |>.getD j 0",
                "  Pz g i j := ([" + ", ".join(lmat(M) for M in d["Pz"]) +
                "] : List (List (List ℤ))).getD g [] |>.getD i [] |>.getD j 0",
                "  Qz g i j := ([" + ", ".join(lmat(M) for M in d["Qz"]) +
                "] : List (List (List ℤ))).getD g [] |>.getD i [] |>.getD j 0",
                f"def ld{nm} : LeafData {a_} {b_} where",
                f"  A := {el(A_)}",
                "  Bc j := ([" + ", ".join(el(x) for x in Bc) + "] : List OK).getD j 0",
                "  Q j l := ((" + "[" + ", ".join(
                    "[" + ", ".join(el(x) for x in row) + "]" for row in Q) +
                "] : List (List OK)).getD j []).getD l 0",
                "  Am := [" + ", ".join(el(A_ * m) for m in d["ms"]) + "]",
            ]
            if cur and cur_nodes + PRE_COST > budget:
                parts.append(cur)
                cur, cur_nodes = [], 0
            cur += [
                f"theorem ld_ok{nm} : ldCheck G {nm}.U {nm}.ms ld{nm} = true := by decide +kernel",
                f"theorem pre_ok{nm} : subPre G cell{k} {nm} = true := by decide +kernel",
            ]
            cur_nodes += PRE_COST
            pre, sizes = prefixes(d["a"], d["w"], d["S"] * d["K"], chunk, with_sizes=True)
            blocks = [list(range(i0, min(i0 + 32, len(pre)))) for i0 in range(0, len(pre), 32)]
            for bi, blk in enumerate(blocks):
                base += [
                    "set_option maxHeartbeats 0 in",
                    f"def blk{nm}_{bi} : List (List ℤ) := [" + ", ".join(lst(pre[t]) for t in blk) + "]",
                ]

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
                f"def preL{nm} : List (List ℤ) := " + app([f"blk{nm}_{bi}" for bi in range(len(blocks))]),
                f"def sub{nm} : List ℤ → Bool := sub {nm}.aL {nm}.w 6 2 "
                f"(leaf4 G n Ps {nm}.ms {nm}.U ld{nm}) (6, fun _ => 0, {nm}.S * {nm}.K)",
                "",
            ]
            for bi, blk in enumerate(blocks):
                nodes = sum(sizes[t] for t in blk)
                if cur and cur_nodes + nodes > budget:
                    parts.append(cur)
                    cur, cur_nodes = [], 0
                cur += [f"theorem sub{nm}_{t} : sub{nm} {lst(pre[t])} = true := by decide +kernel"
                        for t in blk]
                cur += [
                    f"theorem sb{nm}_{bi} : ∀ q ∈ blk{nm}_{bi}, sub{nm} q = true := by",
                    f"  unfold blk{nm}_{bi}",
                    "  exact " + "".join(f"List.forall_mem_cons.2 ⟨sub{nm}_{t}, " for t in blk)
                    + "List.forall_mem_nil _" + "⟩" * len(blk),
                ]
                cur_nodes += nodes
            main += [
                f"theorem cover{nm} : (coverL {nm}.aL {nm}.w 6 2 6 (fun _ => 0) "
                f"({nm}.S * {nm}.K) [] preL{nm}).isSome = true := by decide +kernel",
                f"theorem subs{nm} : ∀ q ∈ preL{nm}, sub{nm} q = true := by",
                f"  unfold preL{nm}",
                "  exact " + glue([f"sb{nm}_{bi}" for bi in range(len(blocks))]),
                f"theorem en_ok{nm} : subEnum G n Ps {nm} = true :=",
                f"  subEnum_fast ld_ok{nm} (enumS_of_coverL cover{nm} subs{nm})",
            ]
        dl = "[" + ", ".join(names) + "]"
        main += [
            f"theorem cov_ok{k} : normsCovered normsL {dl} = true := by decide +kernel",
            f"theorem cell_ok{k} : CellOK hd G n Ps normsL cell{k} :=",
            f"  cellOK_of hd adm (by decide +kernel) cov_ok{k} (by",
            "    intro d hd",
            "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd",
            "    rcases hd with " + " | ".join("rfl" for _ in names),
        ]
        main += [f"    · exact ⟨pre_ok{nm}, en_ok{nm}⟩" for nm in names]
        main += ["  )"]
    if cur:
        parts.append(cur)
    hdr = ["import ReflectZphi.Cert.Sublat", f"import {ns}.Base", f"import {ns}.Pchk", f"import {ns}.Pnorms"] + \
        [f"import {ns}.P{j:03d}" for j in range(len(parts))] + ["", f"namespace {ns}", "", *opener, ""]
    pre_main = [
        f"theorem hd : (0 : ℝ) < (({b_} : ℤ) : ℝ) ^ 2 + 4 * (({a_} : ℤ) : ℝ) := by norm_num",
        "theorem adm : Admissible hd.le G := admCheck_sound hd basis_ok adm_ok",
        "",
    ]
    tail = [
        "theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by",
        "  intro k hk",
        "  simp only [nc] at hk",
        "  interval_cases k <;> decide +kernel",
        "theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by",
        "  intro k hk",
        "  simp only [nc] at hk",
        "  interval_cases k",
        "  exacts [" + ", ".join(f"cell_ok{k}" for k in range(nc)) + "]",
        "",
        "/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/",
        "theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by",
        f"  haveI : IsPrincipalIdealRing OK := {pid}",
        "  exact reflective_of_checkM hV (by",
        f"      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr ({a_} : ℤ) {b_}))).out",
        "      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok",
        "    cen_ok cells_ok",
        "",
        f"end {ns}",
        "",
    ]
    out = {"Base": "\n".join(base + ["", f"end {ns}", ""]),
           "": "\n".join(hdr + pre_main + main[1:] + [""] + tail)}
    mod = lambda body: "\n".join([f"import {ns}.Base", "", f"namespace {ns}", "", *opener, "",
                                   *body, "", f"end {ns}", ""])
    out["Pchk"] = mod(chk)
    out["Pnorms"] = mod(norms_chunks(C, a_, b_))  # its own module (class 87: > 4 GB with the rest)
    for j, pl in enumerate(parts):
        out[f"P{j:03d}"] = "\n".join([f"import {ns}.Base", "", f"namespace {ns}", "", *opener, "",
                                     *pl, "", f"end {ns}", ""])
    return out, stats
