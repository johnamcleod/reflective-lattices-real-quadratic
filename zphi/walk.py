"""Boundary walk of a chamber (heuristic search; every step exact, the output is
certified separately by check_polygon / check_nonreflective).

From a corner (a, b) of the chamber C at vertex v (a, b simple roots of the vertex
stabiliser, C locally {a.y < 0, b.y < 0}), the side of C on H_b runs from v along the
ray y(s) = v + s u (u tangent to H_b at v, a.u < 0, s > 0) until the first point
where another mirror meets H_b. That point w is the next vertex of C, and the next wall
c is the mirror through w at angle pi/m_w to H_b on the side of v (m_w = number of
mirrors through w). The first crossing is found exactly: the ray is covered by small
balls (vinberg.cover_balls) out to the crossing, and every mirror meeting a ball is
enumerated.

The walk records the corners (a_i, b_i, v_i). It stops when it returns to the first
corner (C is the compact polygon: status "closed") or when an isometry g of L maps an
earlier corner onto the latest one with tr g > 3 (status "translation", with a
certificate for nonrefl.check_nonreflective).
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Dict, List, Optional

from .definite import cross
from .linalg import Mat, Vec, bil, det, inv, mat_mul, mat_vec, transpose, is_integral_mat
from .ring import unit_sqrt
from .vinberg import Lattice, cover_balls, coxeter_m, vertex_vector


def _key(r):
    x = next(c for c in r if not c.is_zero())
    return tuple((y / x).coords() for y in r)


def _orient(G, p, ref):
    """p or -p, in the sheet of the timelike ref."""
    return [-c for c in p] if bil(G, p, ref).sign() > 0 else p


def mirrors_through(G: Mat, w: Vec, cache=None) -> List[Vec]:
    """All mirrors through the timelike point w (one root per mirror)."""
    out, seen = [], set()
    for d, m, r in Lattice(G, w, lll_cache=cache).roots_upto(Fr(1)):
        if bil(G, list(r), w).is_zero():
            k = _key(list(r))
            if k not in seen:
                seen.add(k)
                out.append(list(r))
    return out


def next_corner(G: Mat, a: Vec, b: Vec, v: Vec, cache=None, step: float = 1.5,
                max_len: float = 40.0) -> Optional[Dict]:
    """The next corner after (a, b) at v, walking along H_b away from H_a.
    None if no mirror meets the ray within hyperbolic length max_len."""
    R = G[0][0].R
    u = cross(mat_vec(G, b), mat_vec(G, v))          # u.b = u.v = 0
    if bil(G, a, u).sign() > 0:
        u = [-c for c in u]
    uu, vv = bil(G, u, u), bil(G, v, v)
    S = math.sqrt(-float(vv) / float(uu))            # y(s) timelike iff s < S
    best = None
    prev = list(v)
    k = 0
    while True:
        k += 1
        t = k * step
        if t > max_len:
            return None
        s = Fr(S * math.tanh(t)).limit_denominator(1 << 40)
        y = [v[i] + u[i] * s for i in range(3)]
        if bil(G, y, y).sign() >= 0:
            return None
        for c, D in cover_balls(G, [(prev, y)]):
            for d, m, r in Lattice(G, c, lll_cache=cache).roots_upto(D):
                r = list(r)
                rv, ru = bil(G, r, v), bil(G, r, u)
                if rv.is_zero() or ru.is_zero():
                    continue
                sr = -rv / ru
                if sr.sign() <= 0 or (sr * sr * uu + vv).sign() >= 0:
                    continue
                if best is None or (sr - best[0]).sign() < 0:
                    best = (sr, r)
        # every mirror meeting [v, y] has been enumerated
        if best is not None and (best[0] - R(s)).sign() <= 0:
            break
        prev = y
    sr = best[0]
    w = [v[i] + u[i] * sr for i in range(3)]
    thru = mirrors_through(G, w, cache)
    mw = len(thru)
    kb = _key(b)
    cand = []
    for r in thru:
        if _key(r) == kb:
            continue
        if bil(G, r, v).sign() > 0:
            r = [-c for c in r]
        if bil(G, b, r).sign() > 0:
            continue
        try:
            m = coxeter_m(G, b, r)
        except ValueError:
            continue
        if m == mw:
            cand.append(r)
    if len(cand) != 1:
        raise RuntimeError(f"next wall not unique at vertex ({len(cand)} candidates, m={mw})")
    c = cand[0]
    w = _orient(G, vertex_vector(G, b, c), v)
    return {"a": b, "b": c, "v": w, "m": mw}


def _try_map(G, a, b, v, c, d, w):
    """g in O(L) with g a = lam c, g b = lam' d (lam, lam' > 0), g v ~ w, tr g > 3."""
    na, nb, nc, nd = (bil(G, x, x) for x in (a, b, c, d))
    la, lb = na / nc, nb / nd
    if not (la.is_unit() and lb.is_unit()):
        return None
    lam, lam2 = unit_sqrt(la), unit_sqrt(lb)
    if lam is None or lam2 is None:
        return None
    for sgn in (1, -1):
        mu = lam * lam2 * sgn
        A = [[x[i] for x in (a, b, v)] for i in range(3)]
        B = [[x[i] for x in ([lam * e for e in c], [lam2 * e for e in d], [mu * e for e in w])]
             for i in range(3)]
        g = mat_mul(B, inv(A))
        if not is_integral_mat(g) or not det(g).is_unit():
            continue
        if mat_mul(mat_mul(transpose(g), G), g) != G:
            continue
        if bil(G, mat_vec(g, v), w).sign() >= 0:
            continue
        if (g[0][0] + g[1][1] + g[2][2] - 3).sign() <= 0:
            continue
        return g
    return None


def boundary_walk(G: Mat, a: Vec, b: Vec, sheet: Vec, max_corners: int = 80,
                  time_check=None) -> Dict:
    """Walk the boundary of the chamber with corner (a, b) (vertex oriented into the
    sheet of `sheet`). Returns {"status": "closed", "roots": cyclic walls} or
    {"status": "translation", "cert": ...} or {"status": "open", ...}."""
    from .nonrefl import make_certificate
    from .vinberg import _centre
    cache = {}
    v = _orient(G, vertex_vector(G, a, b), sheet)
    corners = [{"a": list(a), "b": list(b), "v": v, "m": coxeter_m(G, a, b)}]
    k0 = (_key(corners[0]["a"]), _key(corners[0]["b"]))
    for _ in range(max_corners):
        cur = corners[-1]
        nxt = next_corner(G, cur["a"], cur["b"], cur["v"], cache)
        if nxt is None:
            return {"status": "open", "reason": "long side", "corners": len(corners),
                    "roots": [c["a"] for c in corners] + [corners[-1]["b"]]}
        if (_key(nxt["a"]), _key(nxt["b"])) == k0:
            return {"status": "closed", "roots": [c["a"] for c in corners],
                    "corners": len(corners)}
        corners.append(nxt)
        # an earlier corner mapped onto the new one (rotation or reflection type)
        for p in corners[:-1]:
            if p["m"] != nxt["m"]:
                continue
            for (c, d) in ((nxt["a"], nxt["b"]), (nxt["b"], nxt["a"])):
                g = _try_map(G, p["a"], p["b"], p["v"], c, d, nxt["v"])
                if g is not None:
                    pts = [q["v"] for q in corners]
                    x = _centre(G, pts)
                    return {"status": "translation", "corners": len(corners),
                            "roots": [q["a"] for q in corners] + [nxt["b"]],
                            "cert": make_certificate(G, x, p["a"], p["b"], c, d, g)}
    return {"status": "open", "reason": "corner budget", "corners": len(corners),
            "roots": [c["a"] for c in corners] + [corners[-1]["b"]]}
