"""Chamber search by hopping control points (heuristic search, rigorous certificate).

Vinberg's algorithm from an interior control point x, run up to distance Delta,
returns exactly the walls H of the chamber C containing x with sinh^2 d(x, H) <=
Delta. Hence no wall of C meets the open ball B(x, rho), sinh^2 rho = Delta, except
those found, and every point y of B(x, rho) satisfying the found inequalities lies
in C. We hop to such a point y near the unexplored part of the boundary of B, run
Vinberg from y, and repeat, collecting walls until they close up into a compact
polygon. Every hop point is verified exactly (in K) to satisfy

    r.y < 0 for all walls found so far,   y.y < 0,   cosh^2 d(x, y) < 1 + Delta,

so y really is an interior point of C. Floats are used only to *choose* y.

The output is not trusted: the caller certifies the closed polygon with
zphi.vinberg.check_polygon, which is a complete proof that it is the chamber of the
reflection group of L (and that L is reflective).
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Dict, List, Optional, Sequence

from .linalg import Mat, Vec, bil
from .vinberg import (vinberg, vinberg_interior, polygon, vertex_vector, _emb_val,
                      _sqrt_bounds)


def _mirror_key(r):
    x = next(c for c in r if not c.is_zero())
    return tuple((y / x).coords() for y in r)


class _Frame:
    """Exact rational frame diagonalising the real (id) form: with the rational
    approximation G~ of id(G) (sqrt(disc) -> s), an exact LDL^T with symmetric
    pivoting gives y = T x (T rational) with  x^T G~ x = sum_i d_i y_i^2. Floats
    are taken only of y_i * sqrt|d_i|, so float geometry never sees the (possibly
    huge, ill-conditioned) entries of G. Used only to steer the search."""

    def __init__(self, G, centre=None):
        R = G[0][0].R
        self.R = R
        self.s = _sqrt_bounds(R.disc)[0]
        A = [[_emb_val(G[i][j], self.s) for j in range(3)] for i in range(3)]
        # Gram-Schmidt on the standard basis w.r.t. A (exact), with reordering to
        # avoid isotropic pivots: rows of T are the dual coordinates
        n = 3
        E = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
        basis, d = [], []
        cand = [E[0], E[1], E[2], [Fr(1), Fr(1), Fr(0)], [Fr(0), Fr(1), Fr(1)],
                [Fr(1), Fr(0), Fr(1)], [Fr(1), Fr(1), Fr(1)]]
        if centre is not None:
            # start Gram-Schmidt at the (rational image of the) centre: the frame is
            # then a boost to the centre, well conditioned near it
            cand = [[_emb_val(c, self.s) for c in centre]] + cand

        def dot(u, v):
            return sum(u[i] * A[i][j] * v[j] for i in range(n) for j in range(n))

        for c in cand:
            u = list(c)
            for b, db in zip(basis, d):
                t = dot(u, b) / db
                u = [u[i] - t * b[i] for i in range(n)]
            du = dot(u, u)
            if du != 0 and any(u):
                basis.append(u)
                d.append(du)
            if len(basis) == n:
                break
        # x = sum_k y_k b_k  =>  y = B^-1 x with B = [b_k as columns]
        B = [[basis[k][i] for k in range(n)] for i in range(n)]
        self.B = B
        self.Binv = _inv3(B)
        self.d = d
        self.sq = [math.sqrt(abs(float(x))) for x in d]
        self.sg = [1.0 if x > 0 else -1.0 for x in d]

    def to_f(self, v):
        xs = [_emb_val(c, self.s) for c in v]
        y = [sum(self.Binv[i][j] * xs[j] for j in range(3)) for i in range(3)]
        return [float(y[i]) * self.sq[i] for i in range(3)]

    def dot(self, a, b):
        return sum(self.sg[i] * a[i] * b[i] for i in range(3))

    def from_f(self, p, digits=12):
        """Small integral vector on (approximately) the ray of the float frame point p:
        exact rational preimage, scaled so its largest coordinate is ~10^digits, then
        rounded (a control point only matters up to positive scaling; the caller
        verifies it exactly)."""
        from math import gcd
        y = [Fr(p[i] / self.sq[i]) for i in range(3)]
        x = [sum(self.B[i][k] * y[k] for k in range(3)) for i in range(3)]
        mx = max(abs(c) for c in x)
        xi = [round(c / mx * 10 ** digits) for c in x]
        g = 0
        for c in xi:
            g = gcd(g, c)
        g = g or 1
        return [self.R(c // g) for c in xi]


def _inv3(M):
    a, b, c = M[0]
    d, e, f = M[1]
    g, h, i = M[2]
    det = a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    adj = [[e * i - f * h, c * h - b * i, b * f - c * e],
           [f * g - d * i, a * i - c * g, c * d - a * f],
           [d * h - e * g, b * g - a * h, a * e - b * d]]
    return [[adj[r][k] / det for k in range(3)] for r in range(3)]


def _hop_target(F, x, walls, Delta, visited, ndir=720, frac=0.85, walk=0.0):
    """Float choice of next control points (in the frame F): on the sphere of radius
    frac*rho about x, directions satisfying the found walls, ordered by distance from
    previously visited centres (prefer unexplored)."""
    xf = F.to_f(x)
    q = F.dot(xf, xf)
    if not q < 0:
        return []
    xh = [c / math.sqrt(-q) for c in xf]
    basis = []
    for e in ([1.0, 0, 0], [0, 1.0, 0], [0, 0, 1.0]):
        u = e[:]
        t = F.dot(u, xh)
        u = [u[i] + t * xh[i] for i in range(3)]
        for b in basis:
            t = F.dot(u, b)
            u = [u[i] - t * b[i] for i in range(3)]
        n = F.dot(u, u)
        if n > 1e-12:
            basis.append([c / math.sqrt(n) for c in u])
        if len(basis) == 2:
            break
    if len(basis) < 2:
        return []
    rho = math.asinh(math.sqrt(float(Delta))) * frac
    wf = []
    for r in walls:
        w = F.to_f(r)
        nw = math.sqrt(max(F.dot(w, w), 1e-300))
        wf.append([c / nw for c in w])
    pts = []
    for k in range(ndir):
        th = 2 * math.pi * k / ndir
        u = [math.cos(th) * basis[0][i] + math.sin(th) * basis[1][i] for i in range(3)]
        p = [math.cosh(rho) * xh[i] + math.sinh(rho) * u[i] for i in range(3)]
        if all(F.dot(w, p) < -1e-9 for w in wf):
            pts.append(p)
    if not pts:
        return []

    vis = []
    for v in visited:
        vf = F.to_f(v)
        qv = F.dot(vf, vf)
        if qv < 0:
            vis.append([c / math.sqrt(-qv) for c in vf])

    def score(p):
        # prefer unexplored points (far from visited centres) that stay close to the
        # boundary of the chamber (near a found wall): this walks along the boundary,
        # where the corners are
        e = 0.0 if not vis else \
            min(math.acosh(max(1.0, -F.dot(p, v))) for v in vis)
        if not wf:
            return e
        dw = min(math.asinh(abs(F.dot(w, p))) for w in wf)
        return e - walk * dw

    pts.sort(key=lambda p: -score(p))
    return pts[:8]


def chamber_search(G: Mat, v0: Optional[Vec] = None, Delta_hop: Fr = Fr(64),
                   max_hops: int = 40, max_roots: int = 400, start=None,
                   orient: Optional[Vec] = None, try_translation: bool = False) -> Dict:
    """Walls of the chamber containing the interior point v0, found by hopping.
    Returns dict(status='closed'|'open', roots (walls, cyclic order if closed),
    hops, centres)."""
    R = G[0][0].R
    F = _Frame(G)
    walls: List[Vec] = []
    keys = set()
    if start is not None:
        x = vertex_vector(G, list(start[0]), list(start[1]))
        if orient is not None and bil(G, list(orient), x).sign() > 0:
            x = [-c for c in x]
    else:
        x = list(v0)
    centres = [] if start is not None else [list(x)]   # exact interior points of C
    lll_cache = {}                                      # warm-start LLL across hops
    visited = []
    hops = 0
    while hops < max_hops:
        hops += 1
        if hops == 1 and start is not None:
            # Vinberg from the vertex of two simple roots (Bugaenko start); x = vertex
            v = vinberg(G, list(start), Delta0=Fr(Delta_hop), Delta_max=Fr(Delta_hop),
                        max_roots=max_roots, orient=orient)
            if v["status"] == "reflective":
                return {"status": "closed", "roots": [v["roots"][i] for i in v["cycle"]],
                        "hops": 1}
        else:
            # one round at the full radius (valid for any starting radius)
            v = vinberg_interior(G, x, Delta0=Fr(Delta_hop), Delta_max=Fr(Delta_hop),
                                 max_roots=max_roots, lll_cache=lll_cache)
        for r in v["roots"]:
            k = _mirror_key(r)
            if k not in keys:
                keys.add(k)
                walls.append(list(r))
        visited.append(list(x))
        F = _Frame(G, centre=x)
        if len(walls) >= 3:
            comp, cyc = polygon(G, walls, x)
            if comp:
                return {"status": "closed", "roots": [walls[i] for i in cyc],
                        "hops": hops}
        if try_translation and centres and len(walls) >= 4:
            from .nonrefl import find_translation, make_certificate
            t = find_translation(G, walls, centres[-1])
            if t is not None:
                a, b, c, d, g = t
                xc = _best_centre(G, centres, a, b, c, d)
                return {"status": "translation", "roots": walls, "hops": hops,
                        "cert": make_certificate(G, xc, a, b, c, d, g)}
        # choose and verify the next control point
        nxt = None
        targets = []
        for frac in (0.85, 0.5, 0.25, 0.1):      # thin regions: smaller spheres
            targets = _hop_target(F, x, walls, Delta_hop, visited, frac=frac,
                                  walk=1.0 if try_translation else 0.0)
            if targets:
                break
        for p in targets:
            y = F.from_f(p)
            if not all(bil(G, r, y).sign() < 0 for r in walls):
                continue
            yy = bil(G, y, y)
            if yy.sign() >= 0:
                continue
            xy = bil(G, x, y)
            if (xy * xy - R(1 + Fr(Delta_hop)) * yy * bil(G, x, x)).sign() >= 0:
                continue                      # not inside the certified ball
            nxt = y
            break
        if nxt is None:
            break
        x = nxt
        centres.append(list(nxt))
    return {"status": "open", "roots": walls, "hops": hops}


def _best_centre(G, centres, a, b, c, d):
    """The interior point minimising the larger cosh^2-distance to the two corners
    (the certificate's enumeration radius); must satisfy the four open half-spaces."""
    from .nonrefl import _oriented_vertex
    best, bv = None, None
    for x in centres:
        if not all(bil(G, r, x).sign() < 0 for r in (a, b, c, d)):
            continue
        v = _oriented_vertex(G, a, b, x)
        w = _oriented_vertex(G, c, d, x)
        cost = max(float(bil(G, x, p) ** 2 / (bil(G, x, x) * bil(G, p, p))) for p in (v, w))
        if bv is None or cost < bv:
            best, bv = x, cost
    return best if best is not None else centres[-1]
