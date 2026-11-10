"""Field-generic enumeration of candidate rank-3 reflective SSF lattices
(Allcock's method as adapted by Mark), for O = Z, Z[sqrt2], Z[phi].

Pipeline:
  thin-part configuration (short edge / short pair / close pair)
  -> Gram matrix of the configuration roots, up to scale (Lemmas 9-11, re-derived)
  -> root lattice R = O-span of the roots, reflective hull H
  -> every lattice M with R <= M <= H, rescaled to be primitive
  -> keep M if det M is squarefree and the configuration roots are primitive in M.
Every SSF reflective lattice with that thin part appears in the output
(necessary conditions only; reflectivity is decided later).
"""
import math
from itertools import product
from fractions import Fraction as Fr
from quadring import (Ring, El, divides, gcd, egcd, tp_normalise, assoc_key, tp_divisors,
                      is_squarefree, ideal_eq, round_el)

# ----------------------------------------------------------------- matrices over K

def zeros(R, n, m):
    return [[R(0) for _ in range(m)] for _ in range(n)]


def mat_mul(A, B):
    R = A[0][0].R
    n, k, m = len(A), len(B), len(B[0])
    C = zeros(R, n, m)
    for i in range(n):
        for j in range(m):
            s = R(0)
            for l in range(k):
                if not A[i][l].is_zero() and not B[l][j].is_zero():
                    s = s + A[i][l] * B[l][j]
            C[i][j] = s
    return C


def transpose(A):
    return [list(r) for r in zip(*A)]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def inv3(M):
    d = det3(M)
    R = d.R
    C = zeros(R, 3, 3)
    for i in range(3):
        for j in range(3):
            rows = [r for r in range(3) if r != j]
            cols = [c for c in range(3) if c != i]
            minor = (M[rows[0]][cols[0]] * M[rows[1]][cols[1]]
                     - M[rows[0]][cols[1]] * M[rows[1]][cols[0]])
            C[i][j] = minor * ((-1) ** (i + j)) / d
    return C


def col(M, j):
    return [M[i][j] for i in range(len(M))]


def bil(G, u, v):
    R = G[0][0].R
    s = R(0)
    for i in range(3):
        if u[i].is_zero():
            continue
        for j in range(3):
            if not v[j].is_zero() and not G[i][j].is_zero():
                s = s + u[i] * G[i][j] * v[j]
    return s


# ------------------------------------------------------------- lattices over O

def common_denominator(vals):
    d = 1
    for v in vals:
        d = math.lcm(d, v.x.denominator, v.y.denominator)
    return d * 2  # factor 2 covers half-integral phi coordinates


def hnf_basis(gens):
    """O-basis (3 columns, lower triangular) of the O-span of vectors in K^3."""
    R = gens[0][0].R
    den = common_denominator([c for g in gens for c in g])
    cols = [[c * den for c in g] for g in gens]
    basis = []
    for row in range(3):
        # combine all columns' entries in this row into one pivot column
        piv = None
        rest = []
        for c in cols:
            if c[row].is_zero():
                rest.append(c)
                continue
            if piv is None:
                piv = c
                continue
            g, x, y = egcd(piv[row], c[row])
            a, b = piv[row] / g, c[row] / g
            newp = [x * piv[i] + y * c[i] for i in range(3)]
            other = [b * piv[i] - a * c[i] for i in range(3)]  # row entry 0
            piv = newp
            rest.append(other)
        if piv is None:
            raise ValueError("generators do not span K^3")
        # normalise pivot by a unit
        u = tp_normalise(piv[row]) / piv[row]
        piv = [u * e for e in piv]
        basis.append(piv)
        cols = [c for c in rest if any(not e.is_zero() for e in c)]
    B = [[basis[j][i] / den for j in range(3)] for i in range(3)]
    return B  # columns are basis vectors, B[i][j] = i-th coordinate of j-th vector


def residues(d):
    """Representatives of O/dO."""
    R = d.R
    if R.D == 1:
        return [R(a) for a in range(abs(int(d.x)))]
    n = abs(int(d.norm()))
    # Z-basis of dO in coordinates (1, omega): d, d*omega
    v1 = R.basis_coords(d)
    v2 = R.basis_coords(d * R.omega)
    # integer HNF of [[v1],[v2]] rows -> reps a in [0,p), b in [0,q)
    a1, b1 = int(v1[0]), int(v1[1])
    a2, b2 = int(v2[0]), int(v2[1])
    # find q = gcd(b1, b2) and p = n / q
    from math import gcd as igcd
    q = igcd(abs(b1), abs(b2))
    p = n // q
    return [R.from_basis(a, b) for a in range(p) for b in range(q)]


def is_integral_mat(M):
    return all(e.is_integral() for row in M for e in row)


def superlattices(N0):
    """All O-lattices N with N0 <= N <= O^3 (N0 integral 3x3, columns), as bases."""
    R = N0[0][0].R
    dN = det3(N0)
    divs = tp_divisors(dN)
    out = []
    for d1 in divs:
        for d2 in divs:
            if not divides(d1 * d2, dN):
                continue
            for d3 in divs:
                if not divides(d1 * d2 * d3, dN):
                    continue
                r1, r2 = residues(d1), residues(d2)
                # columns: c1 = (d1, b21, b31), c2 = (0, d2, b32), c3 = (0, 0, d3)
                # reduce b21 mod d2, b31 mod d3, b32 mod d3
                r3 = residues(d3)
                for b21 in r2:
                    for b31 in r3:
                        for b32 in r3:
                            N = [[d1, R(0), R(0)], [b21, d2, R(0)], [b31, b32, d3]]
                            if is_integral_mat(mat_mul(inv3(N), N0)):
                                out.append(N)
    return out


# ----------------------------------------------------------------- configurations

def gammas(R):
    """4cos^2(pi/m) for the admissible finite m >= 3 (and 0 for m = 2)."""
    vals = {2: R(0), 3: R(1), 4: R(2), 6: R(3)}
    if R.D == 2:
        vals[8] = R(2, 1)
    if R.D == 5:
        vals[5] = R(Fr(3, 2), Fr(1, 2))
        vals[10] = R(Fr(5, 2), Fr(1, 2))
    return vals


def factorisations(z):
    """Good factorisation classes z = u v (u, v totally positive)."""
    return [(u, z / u) for u in tp_divisors(z)]


def box(R, lo, hi):
    if R.D == 1:
        return R.elements_in_box(lo, hi)
    return R.elements_in_box(lo, hi, 0, 4)


def K_bound(mu, mup):
    return (math.sqrt(1 + mu) + math.sqrt(1 + mup)) ** 2 - 1


def gram_rtr(A, B, Ap, Bp, C, Cp):
    """Gram matrix of (r, t, r') with r^2 = 2A, t^2 = 2B (scale fixed by r, t).

    (A',B') = (0,0) means T is orthogonal to R'. Returns None if inconsistent.
    """
    R = A.R
    if Ap.is_zero():
        rp2 = 2 * A * Cp / C
        rt, rpt, rrp = -A * B, R(0), -A * Cp
        return [[2 * A, rt, rrp], [rt, 2 * B, rpt], [rrp, rpt, rp2]]
    w = (A * Bp * Cp) / (Ap * B * C)
    if not w.is_unit() or not w.tpos():
        return None
    # w = eps^2 with eps a unit, eps > 0 at id
    eps = unit_sqrt(w)
    if eps is None:
        return None
    rp2 = 2 * B * Ap * w / Bp
    rt = -A * B
    rpt = -Ap * B * eps
    rrp = -A * Cp
    return [[2 * A, rt, rrp], [rt, 2 * B, rpt], [rrp, rpt, rp2]]


def unit_sqrt(w):
    R = w.R
    if w == R(1):
        return R(1)
    e = R(1)
    for k in range(1, 200):
        e = e * R.eps
        if e * e == w:
            return e if e.sign() > 0 else -e
        if (e * e).inv() == w:
            ei = e.inv()
            return ei if ei.sign() > 0 else -ei
    return None


def admissible(G):
    """Signature (2,1) at id (positive diagonal, det < 0), positive definite at sigma."""
    R = G[0][0].R
    if det3(G).sign() >= 0:
        return False
    if any(G[i][i].sign() <= 0 for i in range(3)):
        return False
    if R.D == 1:
        return True
    m1 = G[0][0]
    m2 = G[0][0] * G[1][1] - G[0][1] * G[1][0]
    return m1.ssign() > 0 and m2.ssign() > 0 and det3(G).ssign() > 0


# ------------------------------------------------------------ lattices from roots

def candidates_from_roots(G, roots):
    """G: Gram of basis (r, t, r'); roots: coordinate vectors of the configuration
    roots. Returns the list of SSF candidate lattices (primitive Gram matrices)."""
    R = G[0][0].R
    Rb = hnf_basis(roots)
    duals = []
    for x in roots:
        n = bil(G, x, x)
        duals.append([2 * c / n for c in x])
    Pb = hnf_basis(duals)
    Hb = inv3(mat_mul(transpose(Pb), G))
    N0 = mat_mul(inv3(Hb), Rb)
    if not is_integral_mat(N0):
        return []   # roots not mutually crystallographic
    out = []
    for N in superlattices(N0):
        Mb = mat_mul(Hb, N)
        GM = mat_mul(mat_mul(transpose(Mb), G), Mb)
        g = R(0)
        for row in GM:
            for e in row:
                g = gcd(g, e) if not e.is_zero() else g
        g = tp_normalise(g)
        GM = [[e / g for e in row] for row in GM]
        if not is_integral_mat(GM):
            continue
        d = det3(GM)
        if not is_squarefree(d):
            continue
        # configuration roots primitive in M
        Minv = inv3(Mb)
        ok = True
        for x in roots:
            c = [sum((Minv[i][j] * x[j] for j in range(3)), R(0)) for i in range(3)]
            gg = R(0)
            for e in c:
                if not e.is_zero():
                    gg = gcd(gg, e)
            if not gg.is_unit():
                ok = False
                break
        if ok:
            out.append(GM)
    return out


def config_roots_short_edge(G):
    R = G[0][0].R
    return [[R(1), R(0), R(0)], [R(0), R(1), R(0)], [R(0), R(0), R(1)]]


def ginv_col(G, j):
    Gi = inv3(G)
    return [Gi[i][j] for i in range(3)], Gi


def enumerate_short_edge(R, verbose=False, coxeter=True, lattices=True):
    """Lemma 9 (short edge; includes triangles via C C' in Gamma).

    coxeter=True restricts the angles at R∩T and R'∩T to pi/m (always valid for a
    chamber); coxeter=False uses Mark's full box 0 < AB < 4 (for comparison)."""
    Gam = gammas(R)
    gpos = [g for m, g in Gam.items() if m != 2]
    abz = gpos if coxeter else box(R, 0, 4)
    AB = [f for z in abz for f in factorisations(z)]
    ApBp = AB + [(R(0), R(0))]
    results = []
    stats = {"configs": 0, "lattices": 0}
    for (A, B) in AB:
        mu = math.sqrt(float(A * B)) / 2
        for (Ap, Bp) in ApBp:
            mup = math.sqrt(float(Ap * Bp)) / 2 if not Ap.is_zero() else 0.0
            K = K_bound(mu, mup)
            zs = (list(gpos) if coxeter else box(R, 0, 4)) + box(R, 4, math.ceil(4 * K * K) + 1)
            for z in zs:
                lam = math.sqrt(float(z)) / 2
                if lam >= K + 1e-12:
                    continue
                for (C, Cp) in factorisations(z):
                    G = gram_rtr(A, B, Ap, Bp, C, Cp)
                    if G is None or not admissible(G):
                        continue
                    stats["configs"] += 1
                    key = "configs_Ap0" if Ap.is_zero() else "configs_Ap"
                    stats[key] = stats.get(key, 0) + 1
                    if not lattices:
                        continue
                    for GM in candidates_from_roots(G, config_roots_short_edge(G)):
                        results.append(("short_edge", (A, B, Ap, Bp, C, Cp), GM))
    stats["lattices"] = len(results)
    return results, stats


def enumerate_short_pair(R, lattices=True):
    """Lemma 10: R, S, T, R' consecutive, S short and orthogonal to R and T."""
    Gam = gammas(R)
    gpos = [g for m, g in Gam.items() if m != 2]
    ABlist = [f for z in box(R, 4, 36) for f in factorisations(z)]
    ApBp = [f for z in gpos for f in factorisations(z)] + [(R(0), R(0))]
    results = []
    stats = {"configs": 0, "lattices": 0}
    for (A, B) in ABlist:
        mu = math.sqrt(float(A * B)) / 2
        for (Ap, Bp) in ApBp:
            mup = math.sqrt(float(Ap * Bp)) / 2 if not Ap.is_zero() else 0.0
            K = K_bound(mu, mup)
            for z in box(R, 4, math.ceil(4 * K * K) + 1):
                if math.sqrt(float(z)) / 2 >= K + 1e-12:
                    continue
                for (C, Cp) in factorisations(z):
                    G = gram_rtr(A, B, Ap, Bp, C, Cp)
                    if G is None or not admissible(G):
                        continue
                    v, Gi = ginv_col(G, 2)        # v ⊥ r, t ; v . r' = 1
                    g33 = Gi[2][2]
                    N = 4 / (G[2][2] * g33)
                    if not N.is_integral():
                        continue
                    for k in tp_divisors(N):
                        a = -2 / (k * g33)
                        s = [a * c for c in v]
                        stats["configs"] += 1
                        key = "configs_Ap0" if Ap.is_zero() else "configs_Ap"
                        stats[key] = stats.get(key, 0) + 1
                        if not lattices:
                            continue
                        roots = config_roots_short_edge(G) + [s]
                        for GM in candidates_from_roots(G, roots):
                            results.append(("short_pair", (A, B, Ap, Bp, C, Cp, k), GM))
    stats["lattices"] = len(results)
    return results, stats


def enumerate_close_pair(R, zmax=None, lattices=True):
    """Lemma 11: R, S, T, S', R' consecutive; S, S' short, orthogonal to neighbours."""
    ABlist = [f for z in box(R, 4, 36) for f in factorisations(z)]
    results = []
    stats = {"configs": 0, "lattices": 0}
    for (A, B) in ABlist:
        mu = math.sqrt(float(A * B)) / 2
        for (Ap, Bp) in ABlist:
            mup = math.sqrt(float(Ap * Bp)) / 2
            K = K_bound(mu, mup)
            hi = math.ceil(4 * K * K) + 1
            if zmax:
                hi = min(hi, zmax)
            for z in box(R, 4, hi):
                if math.sqrt(float(z)) / 2 >= K + 1e-12:
                    continue
                for (C, Cp) in factorisations(z):
                    G = gram_rtr(A, B, Ap, Bp, C, Cp)
                    if G is None or not admissible(G):
                        continue
                    Gi = inv3(G)
                    v = [Gi[i][2] for i in range(3)]    # ⊥ r, t
                    vp = [Gi[i][0] for i in range(3)]   # ⊥ t, r'
                    N = 4 / (G[2][2] * Gi[2][2])
                    Np = 4 / (G[0][0] * Gi[0][0])
                    if not (N.is_integral() and Np.is_integral()):
                        continue
                    for k in tp_divisors(N):
                        s = [(-2 / (k * Gi[2][2])) * c for c in v]
                        s2 = bil(G, s, s)
                        for kp in tp_divisors(Np):
                            sp = [(-2 / (kp * Gi[0][0])) * c for c in vp]
                            sp2 = bil(G, sp, sp)
                            ss = bil(G, s, sp)
                            if ss.sign() >= 0 or (ss * ss - s2 * sp2).sign() <= 0:
                                continue
                            if not ((2 * ss / s2).is_integral() and (2 * ss / sp2).is_integral()):
                                continue
                            stats["configs"] += 1
                            if not lattices:
                                continue
                            roots = config_roots_short_edge(G) + [s, sp]
                            for GM in candidates_from_roots(G, roots):
                                results.append(("close_pair", (A, B, Ap, Bp, C, Cp, k, kp), GM))
    stats["lattices"] = len(results)
    return results, stats


# --------------------------------------------------------------- identification

def find_orthonormal_pair(GM, Rg, bound=2):
    """Search for e1, e2 in M with e1^2 = e2^2 = 1, e1.e2 = 0 (small coordinates)."""
    R = Rg
    coeffs = [R.from_basis(a, b) for a in range(-bound, bound + 1)
              for b in (range(-bound, bound + 1) if R.D != 1 else [0])]
    ones = []
    for c in product(coeffs, repeat=3):
        v = list(c)
        if bil(GM, v, v) == R(1):
            ones.append(v)
    for i in range(len(ones)):
        for j in range(i + 1, len(ones)):
            if bil(GM, ones[i], ones[j]).is_zero():
                return ones[i], ones[j]
    return None


def is_diag_minus_d_1_1(GM, d):
    """Certificate that M is isometric to <-d, 1, 1> (d up to unit squares)."""
    R = d.R
    if not ideal_eq(det3(GM), d):
        return False
    return find_orthonormal_pair(GM, R) is not None


# --------------------------------------------- local (prime-by-prime) version

def _finish(G, Mb, roots):
    R = G[0][0].R
    GM = mat_mul(mat_mul(transpose(Mb), G), Mb)
    g = R(0)
    for row in GM:
        for e in row:
            if not e.is_zero():
                g = gcd(g, e)
    g = tp_normalise(g)
    GM = [[e / g for e in row] for row in GM]
    if not is_integral_mat(GM) or not is_squarefree(det3(GM)):
        return None
    Minv = inv3(Mb)
    for x in roots:
        c = [sum((Minv[i][j] * x[j] for j in range(3)), R(0)) for i in range(3)]
        gg = R(0)
        for e in c:
            if not e.is_zero():
                gg = gcd(gg, e)
        if not gg.is_unit():
            return None
    return GM


def candidates_from_roots(G, roots):
    """SSF lattices M with span(roots) <= M <= reflective hull (prime-by-prime)."""
    import localenum as le
    R = G[0][0].R
    Rb = hnf_basis(roots)
    duals = []
    for x in roots:
        n = bil(G, x, x)
        duals.append([2 * c / n for c in x])
    Pb = hnf_basis(duals)
    Hb = inv3(mat_mul(transpose(Pb), G))
    N0 = mat_mul(inv3(Hb), Rb)
    if not is_integral_mat(N0):
        return []
    U, S, V = le.snf(N0)
    Ui = inv3(U)
    a = [S[i][i] for i in range(3)]
    HU = mat_mul(Hb, Ui)
    primes = []
    for ai in a:
        for p in le.prime_list(ai):
            if not any(ideal_eq(p, q) for q in primes):
                primes.append(p)
    local_choices = []
    for p in primes:
        e = [le.val(ai, p) for ai in a]
        b = [ai / p ** ei for ai, ei in zip(a, e)]
        keep = []
        for N2 in le.local_superlattices(e, p):
            Np = [[b[i] * N2[i][j] for j in range(3)] for i in range(3)]
            Mb = mat_mul(HU, Np)
            GM = mat_mul(mat_mul(transpose(Mb), G), Mb)
            s = min(le.val(x, p) for row in GM for x in row if not x.is_zero())
            if le.val(det3(GM), p) - 3 * s <= 1:
                keep.append(Np)
        if not keep:
            return []
        local_choices.append(keep)
    out = []
    for combo in product(*local_choices) if local_choices else [()]:
        if combo:
            gens = [col(N, j) for N in combo for j in range(3)]
            Nfull = hnf_basis(gens)
        else:
            Nfull = S
        GM = _finish(G, mat_mul(HU, Nfull), roots)
        if GM is not None:
            out.append(GM)
    return out
