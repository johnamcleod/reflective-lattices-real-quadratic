"""Root configurations from the thin part (Allcock Thm 1; Mark Lemmas 9-11).

Two descriptions are implemented and compared in tests/test_configs.py:

(R) re-derived (notes/step2 §1): G = Gram(r, t, r') at scale r^2 = 2A,
    s = -(2/(k (G^-1)_33)) G^-1 e3,  s' = -(2/(k' (G^-1)_11)) G^-1 e1.
(M) Mark's printed matrices (15), (16), (22), (23), (27) and conditions (14), (21),
    (25), (26), transcribed from arXiv:1512.01133 pp. 18-21 (`mark_matrix`).

A configuration is identified by its key (A,B,A',B',C,C'[,k[,k']]) with every entry
a canonical representative (zphi.ring.tp_normalise), A' = B' = 0 meaning T ⊥ R'.

Ranges (see methods.md §4.2 and OPEN_QUESTIONS Q2):
  * AB, A'B' at a vertex: gamma(m) = 4cos^2(pi/m), m >= 3 ("coxeter=True"),
    or Mark's printed full box 0 < z < 4 ("coxeter=False", for comparison).
  * short edge CC': gamma(m) (triangle) or 4 < CC' < 4K^2;   lambda < K exactly.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterator, List, Optional, Tuple

from .boxes import K_upper_int, box, factorisations, gammas, lam_lt_K
from .linalg import admissible, bil, inv, mat_vec, Mat, Vec
from .ring import El, Ring, tp_divisors, unit_sqrt

Key = Tuple[El, ...]


@dataclass
class Config:
    kind: str            # "short_edge" | "short_pair" | "close_pair"
    key: Key             # (A,B,Ap,Bp,C,Cp[,k[,kp]])
    G: Mat               # Gram of the basis (r, t, r') of K^3, scale r^2 = 2A
    roots: List[Vec]     # configuration roots in the basis (r, t, r'):
                         # short edge [r,t,r'], short pair [r,t,r',s],
                         # close pair [r,t,r',s,s']
    eps: Optional[El] = None   # unit with w = eps^2 (A'B' > 0)

    @property
    def mark_type(self) -> str:
        Ap = self.key[2]
        perp = Ap.is_zero()
        return {"short_edge": "16" if perp else "15",
                "short_pair": "23" if perp else "22",
                "close_pair": "27"}[self.kind]

    def key_json(self):
        return [x.to_json() for x in self.key]


# ------------------------------------------------------------- Lemma 9 Gram

def gram_rtr(A: El, B: El, Ap: El, Bp: El, C: El, Cp: El):
    """Gram matrix of (r, t, r') with r^2 = 2A, t^2 = 2B, or None if the
    compatibility condition fails. Returns (G, eps)."""
    R = A.R
    if Ap.is_zero():
        rp2 = 2 * A * Cp / C
        return [[2 * A, -A * B, -A * Cp], [-A * B, 2 * B, R.zero],
                [-A * Cp, R.zero, rp2]], None
    w = (A * Bp * Cp) / (Ap * B * C)
    if not (w.is_unit() and w.tpos()):
        return None
    eps = unit_sqrt(w)
    if eps is None:
        return None
    rp2 = 2 * B * Ap * w / Bp
    rt, rpt, rrp = -A * B, -Ap * B * eps, -A * Cp
    return [[2 * A, rt, rrp], [rt, 2 * B, rpt], [rrp, rpt, rp2]], eps


def _e(R: Ring, i: int) -> Vec:
    return [R.one if j == i else R.zero for j in range(3)]


def _vertex_values(R: Ring, coxeter: bool) -> List[El]:
    if coxeter:
        return [g for m, g in sorted(gammas(R).items()) if m != 2]
    return box(R, 0, 4)


# ------------------------------------------------------------ enumerators

def short_edge(R: Ring, coxeter: bool = True, AB_filter=None) -> Iterator[Config]:
    """Lemma 9. If AB_filter is given, only (A,B) with AB_filter(A,B) True."""
    vert = _vertex_values(R, coxeter)
    AB = [f for z in vert for f in factorisations(z)]
    ApBp = AB + [(R.zero, R.zero)]
    for (A, B) in AB:
        if AB_filter is not None and not AB_filter(A, B):
            continue
        for (Ap, Bp) in ApBp:
            ApBpz = None if Ap.is_zero() else Ap * Bp
            hi = K_upper_int(A * B, ApBpz)
            zs = list(vert) + box(R, 4, hi)
            for z in zs:
                if not lam_lt_K(z, A * B, ApBpz):
                    continue
                for (C, Cp) in factorisations(z):
                    r = gram_rtr(A, B, Ap, Bp, C, Cp)
                    if r is None:
                        continue
                    G, eps = r
                    if not admissible(G):
                        continue
                    yield Config("short_edge", (A, B, Ap, Bp, C, Cp), G,
                                 [_e(R, 0), _e(R, 1), _e(R, 2)], eps)


def short_pair(R: Ring, coxeter: bool = True, AB_filter=None) -> Iterator[Config]:
    """Lemma 10: R, S, T, R' consecutive, S ⊥ R, T; 1 < mu < 3."""
    vert = _vertex_values(R, coxeter)
    ABlist = [f for z in box(R, 4, 36) for f in factorisations(z)]
    ApBp = [f for z in vert for f in factorisations(z)] + [(R.zero, R.zero)]
    for (A, B) in ABlist:
        if AB_filter is not None and not AB_filter(A, B):
            continue
        for (Ap, Bp) in ApBp:
            ApBpz = None if Ap.is_zero() else Ap * Bp
            hi = K_upper_int(A * B, ApBpz)
            for z in box(R, 4, hi):
                if not lam_lt_K(z, A * B, ApBpz):
                    continue
                for (C, Cp) in factorisations(z):
                    r = gram_rtr(A, B, Ap, Bp, C, Cp)
                    if r is None:
                        continue
                    G, eps = r
                    if not admissible(G):
                        continue
                    Gi = inv(G)
                    g33 = Gi[2][2]
                    N = 4 / (G[2][2] * g33)
                    if not N.is_integral():
                        continue
                    v = [Gi[i][2] for i in range(3)]
                    for k in tp_divisors(N):
                        a = -2 / (k * g33)
                        s = [a * c for c in v]
                        yield Config("short_pair", (A, B, Ap, Bp, C, Cp, k), G,
                                     [_e(R, 0), _e(R, 1), _e(R, 2), s], eps)


def close_pair(R: Ring, ultraparallel: bool = True, AB_filter=None,
               stats: Optional[dict] = None) -> Iterator[Config]:
    """Lemma 11: R, S, T, S', R' consecutive; S ⊥ R, T; S' ⊥ T, R'; 1 < mu, mu' < 3.

    Conditions: N, N' in O; k | N, k' | N'; 2 s.s'/s^2, 2 s.s'/s'^2 in O (= Mark's
    (25)); and, if `ultraparallel`, s.s' < 0 and (s.s')^2 > s^2 s'^2 (S, S'
    non-adjacent edges of an acute-angled polygon have ultraparallel lines)."""
    ABlist = [f for z in box(R, 4, 36) for f in factorisations(z)]
    for (A, B) in ABlist:
        if AB_filter is not None and not AB_filter(A, B):
            continue
        for (Ap, Bp) in ABlist:
            hi = K_upper_int(A * B, Ap * Bp)
            for z in box(R, 4, hi):
                if not lam_lt_K(z, A * B, Ap * Bp):
                    continue
                for (C, Cp) in factorisations(z):
                    r = gram_rtr(A, B, Ap, Bp, C, Cp)
                    if r is None:
                        continue
                    G, eps = r
                    if not admissible(G):
                        continue
                    Gi = inv(G)
                    N = 4 / (G[2][2] * Gi[2][2])
                    Np = 4 / (G[0][0] * Gi[0][0])
                    if not (N.is_integral() and Np.is_integral()):
                        continue
                    v = [Gi[i][2] for i in range(3)]
                    vp = [Gi[i][0] for i in range(3)]
                    for k in tp_divisors(N):
                        a = -2 / (k * Gi[2][2])
                        s = [a * c for c in v]
                        s2 = bil(G, s, s)
                        for kp in tp_divisors(Np):
                            b = -2 / (kp * Gi[0][0])
                            sp = [b * c for c in vp]
                            sp2 = bil(G, sp, sp)
                            ss = bil(G, s, sp)
                            if not ((2 * ss / s2).is_integral()
                                    and (2 * ss / sp2).is_integral()):
                                continue
                            if stats is not None:
                                stats["integral"] = stats.get("integral", 0) + 1
                            if ultraparallel and (ss.sign() >= 0
                                                  or (ss * ss - s2 * sp2).sign() <= 0):
                                continue
                            yield Config("close_pair", (A, B, Ap, Bp, C, Cp, k, kp), G,
                                         [_e(R, 0), _e(R, 1), _e(R, 2), s, sp], eps)


ENUMERATORS = {"short_edge": short_edge, "short_pair": short_pair,
               "close_pair": close_pair}


# ------------------------------------------------------ Mark's matrices (M)

def mark_beta(A, B, Ap, Bp, C, Cp):
    """beta = A'BCu with u^2 = AB'C'/(A'BC), u > 0 (Mark (14)); 0 if A'=B'=0."""
    R = A.R
    if Ap.is_zero():
        return R.zero, None
    w = (A * Bp * Cp) / (Ap * B * C)
    u = unit_sqrt(w)
    return Ap * B * C * u, u


def mark_N(A, B, Ap, Bp, C, Cp, beta):
    """(21): N = 4 + 4 (CC' + beta + A'B') / (AB - 4)."""
    return 4 + 4 * (C * Cp + beta + Ap * Bp) / (A * B - 4)


def mark_gamma(A, B, Ap, Bp, C, Cp, beta, k, kp):
    """(26): gamma = (2 beta/(k k')) (2 + beta/CC' - (2CC'+beta)^3 /
    ((AB-4)(A'B'-4)(CC')^2))."""
    CC = C * Cp
    return (2 * beta / (k * kp)) * (2 + beta / CC - (2 * CC + beta) ** 3
                                    / ((A * B - 4) * (Ap * Bp - 4) * CC * CC))


def mark_matrix(kind: str, key: Key) -> Mat:
    """Mark's printed inner-product matrix for the configuration `key`.

    Orders: (15),(16): r, t, r'.  (22),(23): r, s, t, r'.  (27): r, s, t, s', r'."""
    A, B, Ap, Bp, C, Cp = key[:6]
    R = A.R
    Z = R.zero
    beta, _ = mark_beta(A, B, Ap, Bp, C, Cp)
    perp = Ap.is_zero()
    if kind == "short_edge":
        if not perp:   # (15)
            return [[2 * A * Bp, -A * B * Bp, -beta],
                    [-A * B * Bp, 2 * B * Bp, -Ap * Bp * B],
                    [-beta, -Ap * Bp * B, 2 * Ap * B]]
        return [[2 * A * C, -A * B * C, -A * C * Cp],      # (16)
                [-A * B * C, 2 * B * C, Z],
                [-A * C * Cp, Z, 2 * A * Cp]]
    N = mark_N(A, B, Ap, Bp, C, Cp, beta)
    if kind == "short_pair":
        k = key[6]
        if not perp:   # (22)
            return [[2 * A * Bp, Z, -A * B * Bp, -beta],
                    [Z, 2 * Ap * B * N / (k * k), Z, -Ap * B * N / k],
                    [-A * B * Bp, Z, 2 * B * Bp, -Ap * Bp * B],
                    [-beta, -Ap * B * N / k, -Ap * Bp * B, 2 * Ap * B]]
        return [[2 * A * C, Z, -A * B * C, -A * C * Cp],   # (23)
                [Z, 2 * A * Cp * N / (k * k), Z, -A * Cp * N / k],
                [-A * B * C, Z, 2 * B * C, Z],
                [-A * C * Cp, -A * Cp * N / k, Z, 2 * A * Cp]]
    # (27)
    k, kp = key[6], key[7]
    Np = 4 + 4 * (C * Cp + beta + A * B) / (Ap * Bp - 4)   # primes swapped
    g = mark_gamma(A, B, Ap, Bp, C, Cp, beta, k, kp)
    return [[2 * A * Bp, Z, -A * B * Bp, -A * Bp * Np / kp, -beta],
            [Z, 2 * Ap * B * N / (k * k), Z, g, -Ap * B * N / k],
            [-A * B * Bp, Z, 2 * B * Bp, Z, -Ap * Bp * B],
            [-A * Bp * Np / kp, g, Z, 2 * A * Bp * Np / (kp * kp), Z],
            [-beta, -Ap * B * N / k, -Ap * Bp * B, Z, 2 * Ap * B]]


def mark_order(cfg: Config) -> List[Vec]:
    """The configuration roots of `cfg` in Mark's order, rescaled to Mark's scale:
    (16),(23): all roots times 1 (scale factor C applied to the Gram);
    (15),(22),(27): Gram scaled by B', and r', s divided by u."""
    r, t, rp = cfg.roots[0], cfg.roots[1], cfg.roots[2]
    extra = list(cfg.roots[3:])
    A, B, Ap, Bp, C, Cp = cfg.key[:6]
    if not Ap.is_zero():
        # Mark's r' and s are ours divided by the unit u (u^2 = w): same mirrors.
        _, u = mark_beta(A, B, Ap, Bp, C, Cp)
        rp = [x / u for x in rp]
        if extra:
            extra[0] = [x / u for x in extra[0]]
    if cfg.kind == "short_edge":
        return [r, t, rp]
    if cfg.kind == "short_pair":
        return [r, extra[0], t, rp]
    return [r, extra[0], t, extra[1], rp]


def scaled_gram(cfg: Config) -> Mat:
    """Gram of mark_order(cfg) at Mark's scale."""
    A, B, Ap, Bp, C, Cp = cfg.key[:6]
    scale = C if Ap.is_zero() else Bp
    vs = mark_order(cfg)
    return [[scale * bil(cfg.G, x, y) for y in vs] for x in vs]
