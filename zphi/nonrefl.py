"""Non-reflectivity certificates (rank 3).

A certificate is (x, a, b, c, d, g) with:
  (1) a, b, c, d roots of L; a, b meet at angle pi/m at v = vertex(a, b), and c, d at
      angle pi/m at v' = vertex(c, d); exactly m mirrors pass through v and through v'
      (so (a, b) and (c, d) are the simple roots of the local dihedral groups);
  (2) x timelike, in the open sectors a.x, b.x, c.x, d.x < 0, with v, v' on the sheet
      of x;
  (3) no mirror of L crosses the open segments (x, v) or (x, v') (exact enumeration of
      every root whose mirror is within distance d(x, v) of x), and x lies on no
      mirror.
  Then the chamber C containing x has corners v (walls a, b) and v' (walls c, d).
  (4) g in GL_3(O), g^T G g = G, g a = lam c, g b = lam' d with lam, lam' > 0 at id,
      g v on the sheet of v'. Then g maps the corner of C at v onto the corner of C
      at v', hence g C = C.
  (5) tr(g) > 3 at id: g is hyperbolic, so it has infinite order.
Conclusion: Stab(C) is infinite, so the reflection subgroup has infinite index in
O'(L): L is not reflective. `check_nonreflective` verifies (1)-(5) exactly.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from typing import Dict, List, Optional, Sequence

from .definite import mirrors_through_vertex
from .linalg import Mat, Vec, bil, det, inv, mat_mul, mat_vec, transpose, is_integral_mat
from .ring import El, unit_sqrt
from .vinberg import Lattice, coxeter_m, cover_balls, vertex_vector, _is_root


def _cols(cols):
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def _oriented_vertex(G, a, b, x):
    v = vertex_vector(G, a, b)
    if bil(G, v, x).sign() > 0:
        v = [-c for c in v]
    return v


def _ceil_el(z: El) -> Fr:
    D = Fr(int(float(z)) + 1)
    while (z - z.R(D)).sign() > 0:
        D += 1
    return D


def _segment_clear(G: Mat, x: Vec, v: Vec, walls_at_v=None) -> Optional[str]:
    """None if no mirror crosses the open segment (x, v) and x is on no mirror; else a
    reason. The segment [x, v] is covered by small balls (vinberg.cover_balls); a
    mirror meeting it (or through x) is listed by the enumeration of some ball."""
    cache = {}
    for c, Delta in cover_balls(G, [(x, v)], thresh=Fr(256)):
        for d, m, r in Lattice(G, c, lll_cache=cache).roots_upto(Delta):
            sx = bil(G, list(r), x).sign()
            sv = bil(G, list(r), v).sign()
            if sx == 0:
                return f"x lies on the mirror of {r}"
            if sx * sv < 0:
                return f"mirror of {r} crosses (x, v)"
    return None


def make_certificate(G, x, a, b, c, d, g) -> Dict:
    js = lambda v: [e.to_json() for e in v]
    return {"x": js(x), "a": js(a), "b": js(b), "c": js(c), "d": js(d),
            "g": [js(row) for row in g]}


def check_nonreflective(G: Mat, cert: Dict) -> Dict:
    from .ring import from_json
    R = G[0][0].R
    v_ = lambda key: [from_json(R, e) for e in cert[key]]
    x, a, b, c, d = (v_(k) for k in "xabcd")
    g = [[from_json(R, e) for e in row] for row in cert["g"]]
    issues = []
    for name, r in zip("abcd", (a, b, c, d)):
        if not _is_root(G, r):
            issues.append(f"{name} is not a root")
    if issues:
        return {"ok": False, "issues": issues}
    m1 = coxeter_m(G, a, b)
    m2 = coxeter_m(G, c, d)
    if m1 is None or m1 != m2:
        return {"ok": False, "issues": [f"angles {m1} {m2}"]}
    if bil(G, x, x).sign() >= 0:
        return {"ok": False, "issues": ["x not timelike"]}
    for name, r in zip("abcd", (a, b, c, d)):
        if bil(G, r, x).sign() >= 0:
            issues.append(f"x not in the open half-space of {name}")
    v = _oriented_vertex(G, a, b, x)
    w = _oriented_vertex(G, c, d, x)
    for p in (v, w):
        if bil(G, p, p).sign() >= 0:
            issues.append("vertex not timelike")
    if issues:
        return {"ok": False, "issues": issues}
    if mirrors_through_vertex(G, a, b) != m1 or mirrors_through_vertex(G, c, d) != m1:
        return {"ok": False, "issues": ["corner roots not simple (mirror count)"]}
    for p in (v, w):
        why = _segment_clear(G, x, p, None)
        if why:
            return {"ok": False, "issues": [why]}
    # (4) g
    if not is_integral_mat(g) or not det(g).is_unit():
        return {"ok": False, "issues": ["g not in GL_3(O)"]}
    if mat_mul(mat_mul(transpose(g), G), g) != G:
        return {"ok": False, "issues": ["g not an isometry"]}
    for src, dst in ((a, c), (b, d)):
        ga = mat_vec(g, src)
        k = next(i for i in range(3) if not dst[i].is_zero())
        lam = ga[k] / dst[k]
        if [lam * e for e in dst] != ga or lam.sign() <= 0:
            return {"ok": False, "issues": ["g does not map the corner roots positively"]}
    if bil(G, mat_vec(g, v), w).sign() >= 0:
        return {"ok": False, "issues": ["g does not preserve the sheet"]}
    tr = g[0][0] + g[1][1] + g[2][2]
    if (tr - 3).sign() <= 0:
        return {"ok": False, "issues": ["g not hyperbolic (tr <= 3)"]}
    return {"ok": True, "issues": [], "m": m1, "trace": tr.to_json()}


# ------------------------------------------------------------------ search

def _corners(G, walls, x):
    """Pairs (i, j) of found walls meeting at a Coxeter angle whose vertex satisfies
    every found wall (a vertex of the partial polygon). Not certified (the verifier
    certifies)."""
    out = []
    n = len(walls)
    for i in range(n):
        for j in range(i + 1, n):
            try:
                m = coxeter_m(G, walls[i], walls[j])
            except ValueError:
                continue
            if m is None:
                continue
            v = _oriented_vertex(G, walls[i], walls[j], x)
            if bil(G, v, v).sign() >= 0:
                continue
            if all(bil(G, walls[k], v).sign() < 0 for k in range(n) if k not in (i, j)):
                out.append((m, i, j, v))
    return out


def find_translation(G: Mat, walls: Sequence[Vec], x: Vec) -> Optional[Mat]:
    """Search for a hyperbolic g mapping one corner of the partial polygon to another
    (both orders). Returns (a, b, c, d, g) or None."""
    W = [list(r) for r in walls]
    cs = _corners(G, W, x)
    nrm = [bil(G, r, r) for r in W]
    best = None
    for p in range(len(cs)):
        for q in range(len(cs)):
            if p == q or cs[p][0] != cs[q][0]:
                continue
            _, i, j, v = cs[p]
            _, k, l, w = cs[q]
            for (c, d) in ((k, l), (l, k)):
                for (a, b) in ((i, j),):
                    la = nrm[a] / nrm[c]
                    lb = nrm[b] / nrm[d]
                    if not (la.is_unit() and lb.is_unit()):
                        continue
                    lam, lam2 = unit_sqrt(la), unit_sqrt(lb)
                    if lam is None or lam2 is None:
                        continue
                    for mu_sign in (1, -1):
                        mu = lam * lam2 * mu_sign
                        A = _cols([W[a], W[b], v])
                        B = _cols([[lam * e for e in W[c]], [lam2 * e for e in W[d]],
                                   [mu * e for e in w]])
                        g = mat_mul(B, inv(A))
                        if not is_integral_mat(g):
                            continue
                        if mat_mul(mat_mul(transpose(g), G), g) != G:
                            continue
                        if not det(g).is_unit():
                            continue
                        tr = g[0][0] + g[1][1] + g[2][2]
                        if (tr - 3).sign() <= 0:
                            continue
                        if bil(G, mat_vec(g, v), w).sign() >= 0:
                            continue
                        cand = (W[a], W[b], W[c], W[d], g)
                        if best is None or float(tr) < best[0]:
                            best = (float(tr), cand)
    return best[1] if best else None
