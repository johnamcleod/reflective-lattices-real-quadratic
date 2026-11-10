"""From a root configuration to candidate SSF lattices (notes/step2 §2).

For configuration roots x_1..x_k in K^3 (Gram G in the basis of K^3):
  R  = O-span of the x_i                                  (hnf_basis)
  H  = {v : x_i . v in (x_i^2/2) O} = dual of span{2 x_i / x_i^2}
  U N0 V = S  (Smith normal form of R inside H, N0 = Hb^-1 Rb)
  for each prime p | S_33: the p-primary intermediate lattices, kept iff
      v_p(det M) - 3 min v_p(Gram M) <= 1          (local SSF after rescaling)
  CRT-combine, rescale to primitive, keep M if det M squarefree and every x_i is
  primitive in M.
Every lattice M in which the x_i are roots satisfies R <= M <= H, so the output
contains every SSF lattice having the configuration among its roots.
"""
from __future__ import annotations

from itertools import product
from typing import List, Optional, Sequence, Tuple

from .linalg import (Mat, Vec, col, det, gram_of, hnf_basis, ident, inv,
                     is_integral_mat, mat_mul, transpose, bil, mat_vec)
from .ring import (El, Ring, divides, egcd, factor, gcd, gcd_list, ideal_eq,
                   is_squarefree, residues, tp_normalise, valuation)


# ------------------------------------------------------------------- SNF

def snf(A: Mat) -> Tuple[Mat, Mat, Mat]:
    """(U, S, V) with U A V = S diagonal, s_1 | s_2 | s_3, U, V in GL_3(O).

    A must be a nonsingular 3x3 matrix over O."""
    R = A[0][0].R
    n = len(A)
    S = [row[:] for row in A]
    U, V = ident(R, n), ident(R, n)

    def row_op(M, i, j, a, b, c, d):
        ri, rj = M[i], M[j]
        M[i] = [a * x + b * y for x, y in zip(ri, rj)]
        M[j] = [c * x + d * y for x, y in zip(ri, rj)]

    def col_op(M, i, j, a, b, c, d):
        for row in M:
            x, y = row[i], row[j]
            row[i] = a * x + b * y
            row[j] = c * x + d * y

    one, zero = R.one, R.zero
    for k in range(n):
        while True:
            best = None
            for i in range(k, n):
                for j in range(k, n):
                    if not S[i][j].is_zero():
                        nn = abs(S[i][j].norm_num())
                        if best is None or nn < best[0]:
                            best = (nn, i, j)
            if best is None:
                return U, S, V
            _, i, j = best
            S[k], S[i] = S[i], S[k]
            U[k], U[i] = U[i], U[k]
            for row in S:
                row[k], row[j] = row[j], row[k]
            for row in V:
                row[k], row[j] = row[j], row[k]
            for i in range(k + 1, n):
                if S[i][k].is_zero():
                    continue
                if divides(S[k][k], S[i][k]):
                    q = S[i][k] / S[k][k]
                    row_op(S, k, i, one, zero, -q, one)
                    row_op(U, k, i, one, zero, -q, one)
                else:
                    g, x, y = egcd(S[k][k], S[i][k])
                    a, b = S[k][k] / g, S[i][k] / g
                    row_op(S, k, i, x, y, -b, a)
                    row_op(U, k, i, x, y, -b, a)
            for j in range(k + 1, n):
                if S[k][j].is_zero():
                    continue
                if divides(S[k][k], S[k][j]):
                    q = S[k][j] / S[k][k]
                    col_op(S, k, j, one, zero, -q, one)
                    col_op(V, k, j, one, zero, -q, one)
                else:
                    g, x, y = egcd(S[k][k], S[k][j])
                    a, b = S[k][k] / g, S[k][j] / g
                    col_op(S, k, j, x, y, -b, a)
                    col_op(V, k, j, x, y, -b, a)
            if any(not S[i][k].is_zero() for i in range(k + 1, n)) or \
               any(not S[k][j].is_zero() for j in range(k + 1, n)):
                continue
            bad = None
            for i in range(k + 1, n):
                for j in range(k + 1, n):
                    if not S[i][j].is_zero() and not divides(S[k][k], S[i][j]):
                        bad = (i, j)
            if bad:
                i, _ = bad
                row_op(S, k, i, one, one, zero, one)
                row_op(U, k, i, one, one, zero, one)
                continue
            break
    # normalise diagonal to canonical totally positive generators
    for k in range(n):
        d = S[k][k]
        if d.is_zero():
            continue
        u = tp_normalise(d) / d
        S[k] = [u * x for x in S[k]]
        U[k] = [u * x for x in U[k]]
    return U, S, V


# ------------------------------------------------- local superlattices

def local_superlattices(e: Sequence[int], p: El) -> List[Mat]:
    """All lattices N with diag(p^e1, p^e2, p^e3) O^3 <= N <= O^3 (p-power index),
    each exactly once, as lower-triangular column bases with diagonal p^k_i.

    Containment conditions are solved in closed form (prototype localenum.py)."""
    R = p.R
    out: List[Mat] = []
    pw = [p ** i for i in range(max(e) + 1)]

    def mult_reps(m, k):
        if m >= k:
            return [R.zero]
        return [pw[m] * r for r in residues(pw[k - m])]

    for k1 in range(e[0] + 1):
        for k2 in range(e[1] + 1):
            for k3 in range(e[2] + 1):
                d1, d2, d3 = pw[k1], pw[k2], pw[k3]
                m1 = e[0] - k1
                for b32 in mult_reps(max(0, k3 - (e[1] - k2)), k3):
                    for b21 in mult_reps(max(0, k2 - m1), k2):
                        x2 = -(pw[m1]) * b21 / d2
                        c = -x2 * b32
                        if m1 >= k3:
                            if not c.is_zero() and not divides(d3, c):
                                continue
                            b31s = residues(d3)
                        else:
                            if not c.is_zero() and not divides(pw[m1], c):
                                continue
                            base = c / pw[m1]
                            b31s = [base + pw[k3 - m1] * t for t in residues(pw[m1])]
                        for b31 in b31s:
                            out.append([[d1, R.zero, R.zero], [b21, d2, R.zero],
                                        [b31, b32, d3]])
    return out


def local_count_formula(e: Sequence[int], p: El) -> int:
    """Number of lattices between diag(p^e) and O^3 (= number of submodules of
    ⊕ O/p^{e_i}), by the Hall-polynomial-free brute formula: count via the
    enumeration's structure is not independent, so this uses a direct count of
    subgroups of a finite abelian p-group of type e over the residue field size q,
    computed by the standard recursion (Delsarte / Birkhoff)."""
    q = abs(p.norm_num())
    lam = sorted(e, reverse=True)
    return _count_subgroups(lam, q)


def _count_subgroups(lam: List[int], q: int) -> int:
    """Number of submodules of ⊕ O/p^{lam_i} (q = |O/p|): sum over all types mu ⊆ lam
    of the Birkhoff formula."""
    from itertools import product as prod
    total = 0
    lam = [x for x in lam if x > 0]
    if not lam:
        return 1
    ranges = [range(x + 1) for x in lam]
    seen = set()
    for mu in prod(*ranges):
        mus = tuple(sorted(mu, reverse=True))
        if mus in seen:
            continue
        seen.add(mus)
        # mu must be contained in lam (as partitions): mus_i <= lam_i
        if any(m > l for m, l in zip(mus, lam)):
            continue
        total += _birkhoff(lam, list(mus), q)
    return total


def _conj(part: List[int]) -> List[int]:
    if not part or max(part) == 0:
        return []
    return [sum(1 for x in part if x >= i) for i in range(1, max(part) + 1)]


def _birkhoff(lam: List[int], mu: List[int], q: int) -> int:
    """Number of subgroups of type mu in an abelian p-group of type lam (|F| = q)."""
    a = _conj(lam)
    b = _conj(mu)
    b = b + [0] * (len(a) - len(b))
    res = 1
    for i in range(len(a)):
        ai, bi = a[i], b[i]
        ai1 = a[i + 1] if i + 1 < len(a) else 0
        bi1 = b[i + 1] if i + 1 < len(b) else 0
        res *= q ** (bi1 * (ai - bi))
        # q-binomial [ai - bi1 ; bi - bi1]
        res *= _qbinom(ai - bi1, bi - bi1, q)
    return res


def _qbinom(n: int, k: int, q: int) -> int:
    if k < 0 or k > n:
        return 0
    num, den = 1, 1
    for i in range(k):
        num *= q ** (n - i) - 1
        den *= q ** (i + 1) - 1
    return num // den


# ------------------------------------------------------- candidates

def prime_list(z: El) -> List[El]:
    return [q for q, _ in factor(z)]


def hull_data(G: Mat, roots: Sequence[Vec]):
    """(Rb, Hb, N0): bases (columns) of the root lattice and the reflective hull,
    and N0 = Hb^-1 Rb (integral iff the roots are mutually crystallographic)."""
    Rb = hnf_basis(roots)
    duals = []
    for x in roots:
        n = bil(G, x, x)
        duals.append([2 * c / n for c in x])
    Pb = hnf_basis(duals)
    Hb = inv(mat_mul(transpose(Pb), G))
    N0 = mat_mul(inv(Hb), Rb)
    return Rb, Hb, N0


def primitive_gram(GM: Mat) -> Tuple[Mat, El]:
    R = GM[0][0].R
    g = tp_normalise(gcd_list([e for row in GM for e in row], R))
    return [[e / g for e in row] for row in GM], g


def is_primitive_in(Mb: Mat, x: Vec) -> bool:
    c = mat_vec(inv(Mb), x)
    if not all(e.is_integral() for e in c):
        return False
    return gcd_list(c, x[0].R).is_unit()


def finish(G: Mat, Mb: Mat, roots: Sequence[Vec]) -> Optional[Mat]:
    GM, _ = primitive_gram(gram_of(G, Mb))
    if not is_integral_mat(GM) or not is_squarefree(det(GM)):
        return None
    Minv = inv(Mb)
    for x in roots:
        c = mat_vec(Minv, x)
        if not all(e.is_integral() for e in c) or not gcd_list(c, x[0].R).is_unit():
            return None
    return GM


def candidates(G: Mat, roots: Sequence[Vec], with_basis: bool = False,
               ssf_prune: bool = True):
    """Lattices M with span(roots) <= M <= hull in which every root is primitive.

    ssf_prune=True (default): only SSF M (primitive rescaling has squarefree det),
    enumerated prime by prime with local pruning; returns Gram matrices (or
    (Gram, basis) pairs).
    ssf_prune=False: every such M ("reflection-stable enlargements", Mark §3.5);
    returns triples (Gram, basis, is_ssf)."""
    R = G[0][0].R
    Rb, Hb, N0 = hull_data(G, roots)
    if not is_integral_mat(N0):
        return []
    U, S, V = snf(N0)
    HU = mat_mul(Hb, inv(U))
    a = [S[i][i] for i in range(3)]
    primes: List[El] = []
    for ai in a:
        for p in prime_list(ai):
            if not any(ideal_eq(p, q) for q in primes):
                primes.append(p)
    local_choices = []
    for p in primes:
        e = [valuation(ai, p) for ai in a]
        b = [ai / p ** ei for ai, ei in zip(a, e)]
        keep = []
        for N2 in local_superlattices(e, p):
            Np = [[b[i] * N2[i][j] for j in range(3)] for i in range(3)]
            if ssf_prune:
                GM = gram_of(G, mat_mul(HU, Np))
                s = min(valuation(x, p) for row in GM for x in row if not x.is_zero())
                if valuation(det(GM), p) - 3 * s > 1:
                    continue
            keep.append(Np)
        if not keep:
            return []
        local_choices.append(keep)
    out = []
    for combo in (product(*local_choices) if local_choices else [()]):
        if combo:
            Nfull = hnf_basis([col(Nm, j) for Nm in combo for j in range(3)])
        else:
            Nfull = S
        Mb = mat_mul(HU, Nfull)
        if ssf_prune:
            GM = finish(G, Mb, roots)
            if GM is not None:
                out.append((GM, Mb) if with_basis else GM)
        else:
            Minv = inv(Mb)
            ok = True
            for x in roots:
                c = mat_vec(Minv, x)
                if not gcd_list(c, R).is_unit():
                    ok = False
                    break
            if not ok:
                continue
            GM, _ = primitive_gram(gram_of(G, Mb))
            out.append((GM, Mb, is_squarefree(det(GM))))
    return out


# ------------------------------------------------------ local simplicity

def vertex_pairs(kind: str, n_roots: int) -> List[Tuple[int, int]]:
    """Index pairs (into cfg.roots) of configuration roots meeting at a vertex of the
    chamber (consecutive edges). roots = [r, t, r'] (+ [s]) (+ [s, s'])."""
    if kind == "short_edge":
        return [(0, 1), (2, 1)]            # R∩T, R'∩T  (+ R∩R' for triangles)
    if kind == "short_pair":
        return [(0, 3), (3, 1), (2, 1)]    # R∩S, S∩T, T∩R'
    return [(0, 3), (3, 1), (1, 4), (4, 2)]  # R∩S, S∩T, T∩S', S'∩R'


def dihedral_order(G: Mat, x: Vec, y: Vec) -> int:
    """m with 4 (x.y)^2 / (x^2 y^2) = 4 cos^2(pi/m); raises if not a Coxeter angle."""
    from .boxes import gammas
    R = G[0][0].R
    g = 4 * bil(G, x, y) ** 2 / (bil(G, x, x) * bil(G, y, y))
    for m, v in gammas(R).items():
        if g == v:
            return m
    raise ValueError(f"not a Coxeter angle: {g}")


def local_simplicity(G: Mat, Mb: Mat, roots: Sequence[Vec], kind: str,
                     triangle: bool) -> Tuple[bool, List[Tuple[int, int]]]:
    """At every vertex of the configuration with angle pi/m, the lattice M must have
    exactly m mirrors through that vertex (otherwise the two configuration roots
    are not simple roots there: some mirror of M passes between them).

    Returns (ok, [(m, mirrors)] per vertex)."""
    from .definite import mirrors_through_vertex
    GM, _ = primitive_gram(gram_of(G, Mb))   # roots are invariant under rescaling
    Minv = inv(Mb)
    pairs = list(vertex_pairs(kind, len(roots)))
    if triangle:
        pairs.append((0, 2))
    info = []
    ok = True
    for i, j in pairs:
        m = dihedral_order(G, roots[i], roots[j])
        cnt = mirrors_through_vertex(GM, mat_vec(Minv, roots[i]), mat_vec(Minv, roots[j]))
        info.append((m, cnt))
        if cnt != m:
            ok = False
    return ok, info
