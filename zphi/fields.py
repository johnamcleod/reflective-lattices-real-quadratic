"""Field profiles: the only field-specific data the pipeline uses.

Every algorithm (configurations, hull, SNF, local enumeration, Vinberg, certificates,
isometries) takes a Ring and never branches on which field it is. A Ring is the
generic order arithmetic of Z[w], w^2 = c0 + c1 w (zphi.ring), composed with a
FieldProfile: plain data, validated here.

Standing hypotheses (paper, Section 2), checked by `validate`:
  (H1) O is (norm-)Euclidean. HNF/SNF/egcd over O use Euclidean division by |N|.
       Checked against the complete list of norm-Euclidean real quadratic fields
       Q(sqrt d), d = 2, 3, 5, 6, 7, 11, 13, 17, 19, 21, 29, 33, 37, 41, 57, 73
       (Chatland-Davenport 1950; Barnes-Swinnerton-Dyer 1952).
  (H2) [K:Q] = 2 (restriction of scalars to Z^6, a single conjugate sigma), or
       K = Q (degree 1; used only by the oracle tests).
  (N2) the fundamental unit has norm -1 (equivalently (U2) under (H2)).
  Also checked: Z[w] is the maximal order (fundamental discriminant), and the
  stored unit is a fundamental unit.

Derived data (computed and verified exactly, not typed in):
  gammas: gamma(m) = 4cos^2(pi/m) for every m with gamma(m) in O. As
  [Q(cos(2pi/m)):Q] = phi(m)/2 <= 2 forces m in {2,3,4,5,6,8,10,12}, only those are
  tried. Each candidate is verified exactly: c = gamma - 2 satisfies C_m(c) = 2 and
  C_k(c) != 2 for 0 < k < m, where C_0 = 2, C_1 = c, C_{k+1} = c C_k - C_{k-1}
  (so c = 2cos(2 pi j/m) with gcd(j, m) = 1); the embedding id is fixed by a float
  comparison with 4cos^2(pi/m) (steering only, the candidates are 2+2cos(2pi j/m)
  with distinct values).
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

# fundamental discriminants of the norm-Euclidean real quadratic fields
NORM_EUCLIDEAN_DISCS = {8, 12, 5, 24, 28, 44, 13, 17, 76, 21, 29, 33, 37, 41, 57, 73}


@dataclass(frozen=True)
class FieldProfile:
    key: int                  # registry key (D): 1 = Z, 2 = Z[sqrt2], 5 = Z[phi]
    name: str
    symbol: str               # printed name of w
    degree: int               # 1 or 2
    c0: int = 0               # w^2 = c0 + c1 w
    c1: int = 0
    eps: Tuple[int, int] = (1, 0)   # fundamental unit a + b w (degree 2)
    pari_poly: str = "y"      # minimal polynomial of w (cross-checks only)
    reference: Dict[str, object] = field(default_factory=dict, compare=False, hash=False)

    @property
    def disc(self) -> int:
        return 1 if self.degree == 1 else self.c1 * self.c1 + 4 * self.c0


ZZ_PROFILE = FieldProfile(key=1, name="Z", symbol="", degree=1)

ZSQRT2_PROFILE = FieldProfile(
    key=2, name="Z[sqrt2]", symbol="√2", degree=2, c0=2, c1=0, eps=(1, 1),
    pari_poly="y^2-2",
    reference={  # Mark (arXiv:1512.01133), Table 1, and gate A.3.4
        "configs": {"15": 282, "16": 1736, "22": 5777, "23": 88836, "27": 97526},
        "reflective_classes": 146,
    })

ZPHI_PROFILE = FieldProfile(
    key=5, name="Z[phi]", symbol="φ", degree=2, c0=1, c1=1, eps=(0, 1),
    pari_poly="y^2-y-1",
    reference={"configs": {"15": 298, "16": 1636, "22": 2946, "23": 36961}})

# Q(sqrt13): w = (1 + sqrt13)/2, w^2 = 3 + w; fundamental unit (3 + sqrt13)/2 = 1 + w, norm -1.
# (H1): norm-Euclidean (disc 13 is on the Chatland-Davenport list); (N2) holds.
# 2 is inert (13 = 5 mod 8), 3 splits (13 = 1 mod 3), 13 ramifies. No reference counts.
ZSQRT13_PROFILE = FieldProfile(
    key=13, name="Z[(1+sqrt13)/2]", symbol="ω", degree=2, c0=3, c1=1, eps=(1, 1),
    pari_poly="y^2-y-3", reference={})

PROFILES: Dict[int, FieldProfile] = {p.key: p for p in (ZZ_PROFILE, ZSQRT2_PROFILE,
                                                         ZPHI_PROFILE, ZSQRT13_PROFILE)}

# file names of the final outputs, per profile key
OUTPUT_NAMES: Dict[int, str] = {2: "zsqrt2_rank3.json", 5: "zphi_rank3.json",
                                13: "zsqrt13_rank3.json"}


def register(profile: FieldProfile) -> None:
    """Add a profile (validated when its Ring is first built)."""
    PROFILES[profile.key] = profile


def _is_squarefree_int(n: int) -> bool:
    n = abs(n)
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True


def _is_fundamental(D: int) -> bool:
    if D % 4 == 1:
        return _is_squarefree_int(D)
    if D % 4 == 0:
        m = D // 4
        return m % 4 in (2, 3) and _is_squarefree_int(m)
    return False


class HypothesisError(ValueError):
    pass


def validate(P: FieldProfile, R) -> None:
    """Check (H1), (H2), maximality and the fundamental unit; raise HypothesisError."""
    if P.degree == 1:
        return
    if P.degree != 2:
        raise HypothesisError(f"{P.name}: (H2) needs degree 2")
    D = P.disc
    if D <= 0 or math.isqrt(D) ** 2 == D:
        raise HypothesisError(f"{P.name}: not a real quadratic field (disc {D})")
    if not _is_fundamental(D):
        raise HypothesisError(f"{P.name}: Z[w] is not the maximal order (disc {D})")
    if D not in NORM_EUCLIDEAN_DISCS:
        raise HypothesisError(f"{P.name}: (H1) O is not norm-Euclidean (disc {D})")
    eps = R(*P.eps)
    if not eps.is_unit():
        raise HypothesisError(f"{P.name}: eps is not a unit")
    if eps.sign() < 0:
        raise HypothesisError(f"{P.name}: eps must be > 0 at id")
    # fundamental: no unit u with 1 < u < eps at id. Such u has |sigma u| = 1/u < 1,
    # so u - sigma(u) = b sqrt(D) and u + sigma(u) = 2a + c1 b are bounded by eps + 1.
    e = float(eps)
    if e <= 1:
        raise HypothesisError(f"{P.name}: eps must be > 1 at id")
    bmax = int((e + 1) / math.sqrt(D)) + 2
    for b in range(-bmax, bmax + 1):
        for a in range(-int(e) - 4 - abs(P.c1 * b), int(e) + 5 + abs(P.c1 * b)):
            u = R(a, b)
            if u.is_zero() or not u.is_unit() or u == eps:
                continue
            if (u - 1).sign() > 0 and (eps - u).sign() > 0:
                raise HypothesisError(f"{P.name}: {u} is a smaller unit than eps")
    a, b = P.eps
    if a * a + P.c1 * a * b - P.c0 * b * b != -1:
        raise HypothesisError(f"{P.name}: (N2) fails: the fundamental unit has norm +1")


def compute_gammas(R) -> Dict[int, object]:
    """gamma(m) = 4cos^2(pi/m) in O for all m with gamma(m) in O (exactly verified)."""
    out = {2: R(0)}
    for m in (3, 4, 5, 6, 8, 10, 12):
        target = 4 * math.cos(math.pi / m) ** 2
        cands = []
        if R.degree == 1:
            if abs(target - round(target)) < 1e-9:
                cands = [R(round(target))]
        else:
            # gamma = a + b w; conjugate 2 + 2cos(2 pi j/m), gcd(j, m) = 1
            w1 = (R.c1 + math.sqrt(R.disc)) / 2
            w2 = (R.c1 - math.sqrt(R.disc)) / 2
            for j in range(1, m):
                if math.gcd(j, m) != 1:
                    continue
                g2 = 2 + 2 * math.cos(2 * math.pi * j / m)
                b = (target - g2) / (w1 - w2)
                a = target - b * w1
                if abs(b - round(b)) < 1e-9 and abs(a - round(a)) < 1e-9:
                    cands.append(R(round(a), round(b)))
        for g in cands:
            if _verify_gamma(R, g, m) and abs(float(g) - target) < 1e-9:
                out[m] = g
                break
    return dict(sorted(out.items()))


def _verify_gamma(R, g, m: int) -> bool:
    """Exact: c = g - 2 is 2cos(2 pi j/m) for some j coprime to m."""
    c = g - 2
    C = [R(2), c]
    for k in range(1, m):
        C.append(c * C[k] - C[k - 1])
    if C[m] != R(2):
        return False
    return all(C[k] != R(2) for k in range(1, m))
