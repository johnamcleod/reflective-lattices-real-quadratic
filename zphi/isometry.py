"""Isometry certificates between reflective rank-3 lattices via their chambers.

If phi: (O^3, G1) -> (O^3, G2) is an isometry and C1, C2 are chambers, composing
with an element of W(L2) we may assume phi(C1) = C2, so phi maps the cyclically
ordered simple roots of L1 to unit multiples of the simple roots of L2, preserving
the cyclic order up to a dihedral symmetry. We try every alignment, solve for phi on
three linearly independent simple roots, and accept phi iff
    phi in GL_3(O)   and   phi^T G2 phi = G1
(phi maps every simple root of L1 to a unit multiple of the aligned one: checked).
A returned phi is an explicit, independently checkable certificate. If no alignment
works the lattices are NOT isometric (given that the chambers are correct).
"""
from __future__ import annotations

from typing import List, Optional, Sequence

from .linalg import Mat, Vec, bil, det, inv, mat_mul, transpose, mat_vec, is_integral_mat
from .ring import El, assoc_key, unit_sqrt


def cycle_invariant(G: Mat, roots: Sequence[Vec]):
    """Dihedral-invariant data: the cyclic sequence of (norm class, angle to next)."""
    n = len(roots)
    seq = []
    for i in range(n):
        a, b = roots[i], roots[(i + 1) % n]
        ab = bil(G, a, b)
        c = 4 * ab * ab / (bil(G, a, a) * bil(G, b, b))
        seq.append((assoc_key(bil(G, a, a)), c.coords()))
    return seq


def _canon_dihedral(seq):
    n = len(seq)
    best = None
    for rev in (False, True):
        s = list(reversed(seq)) if rev else list(seq)
        if rev:
            # reversed position t holds original root i = n-1-t; its angle to the next
            # reversed root is the original angle between i-1 and i, i.e. s[t+1]
            s = [(s[t][0], s[(t + 1) % n][1]) for t in range(n)]
        for k in range(n):
            t = tuple(s[k:] + s[:k])
            if best is None or t < best:
                best = t
    return best


def invariant_key(G: Mat, roots: Sequence[Vec]):
    return (assoc_key(det(G)), _canon_dihedral(cycle_invariant(G, roots)))


def _basis_matrix(cols: Sequence[Vec]) -> Mat:
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def find_isometry(G1: Mat, roots1: Sequence[Vec], G2: Mat, roots2: Sequence[Vec]) -> Optional[Mat]:
    """phi with phi^T G2 phi = G1, phi in GL_3(O), mapping chamber to chamber; or None."""
    n = len(roots1)
    if n != len(roots2):
        return None
    if assoc_key(det(G1)) != assoc_key(det(G2)):
        return None
    # pick three consecutive roots of L1 that are linearly independent
    idx = None
    for s in range(n):
        tri = [roots1[(s + k) % n] for k in range(3)]
        if not det(_basis_matrix(tri)).is_zero():
            idx = [(s + k) % n for k in range(3)]
            break
    if idx is None:
        return None
    A = _basis_matrix([roots1[i] for i in idx])
    Ainv = inv(A)
    n1 = [bil(G1, r, r) for r in roots1]
    n2 = [bil(G2, r, r) for r in roots2]
    for rev in (False, True):
        for k in range(n):
            perm = [((-i if rev else i) + k) % n for i in range(n)]
            imgs = []
            ok = True
            for i in range(n):
                j = perm[i]
                q = n1[i] / n2[j]
                u = unit_sqrt(q) if q.is_unit() else None
                if u is None:
                    ok = False
                    break
                imgs.append([u * x for x in roots2[j]])
            if not ok:
                continue
            B = _basis_matrix([imgs[i] for i in idx])
            phi = mat_mul(B, Ainv)
            if not is_integral_mat(phi) or not det(phi).is_unit():
                continue
            if mat_mul(mat_mul(transpose(phi), G2), phi) != G1:
                continue
            if all(mat_vec(phi, roots1[i]) == imgs[i] for i in range(n)):
                return phi
    return None
