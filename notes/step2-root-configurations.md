# Rank-3 reflective lattices over ℤ[φ]: Step 2, root configurations and candidate lattices

9 November 2026. Code: `quadring.py` (exact arithmetic in ℤ, ℤ[√2], ℤ[φ]),
`rank3.py` (configurations and candidate lattices), `localenum.py` (Smith normal
form and prime-by-prime enumeration). Status: work in progress (see §5).

The goal of step 2 is one implementation, parametrised by the ring, that produces
for each thin-part configuration every SSF lattice that could have it. It is
validated against ℤ and against Mark's ℤ[√2] counts before it is run on ℤ[φ].

---

## 1. Re-derived configuration Gram matrices (Mark's Lemmas 9–11)

I could not recover Mark's matrices (3.7), (3.8), (3.14), (3.15) and (3.19)
verbatim, so they are re-derived here from Allcock's lemmas. All statements are
field-generic over O = ℤ, ℤ[√2] or ℤ[φ] (each a PID with a unit of norm −1, so
totally positive units are squares).

**Notation.** r, t, r′ are the roots of consecutive (or nearly consecutive) edges
R, T, R′, with μ = −r̂·t̂, μ′ = −r̂′·t̂ and λ = −r̂·r̂′. Lemma 8 gives good
factorisations

- (A, B) for the pair (r, t), with AB = 4μ²;
- (A′, B′) for (r′, t), with A′B′ = 4μ′², or (0, 0) when T ⊥ R′;
- (C, C′) for (r, r′), with CC′ = 4λ².

**Compatibility.** Comparing r²/t², r′²/t² and r²/r′² shows that

  w := AB′C′ / (A′BC)

must be a totally positive unit; equivalently, the ideals (A′BC) and (AB′C′) are
equal. Because each root may be rescaled by any unit, and totally positive units are
squares, this is the only condition. (Mark's "square-unit" condition (3.12)/(14)
becomes vacuous once w is absorbed into the choice of r′.) Write w = ε² with ε a
unit, ε > 0 at id.

### 1.1 Short edge (Lemma 9)

Scaling so that r² = 2A, the Gram matrix of (r, t, r′) is

  G = [[2A, −AB, −AC′], [−AB, 2B, −A′Bε], [−AC′, −A′Bε, 2A′Bw/B′]],

and, when T ⊥ R′ (A′ = B′ = 0),

  G = [[2A, −AB, −AC′], [−AB, 2B, 0], [−AC′, 0, 2AC′/C]].

*Derivation.* We have r² = 2A, t² = 2B, r·t = −AB, and r′²/t² = (A′/B′)·w. Then
(r′·t)² = r′²t²μ′² = A′²B²w, and (r·r′)² = r²r′²λ² = A²C′² after substituting w.
The signs come from the acute-angle condition at id.

**Ranges.**
- (A,B) and (A′,B′): R ∩ T and R′ ∩ T are vertices of a Coxeter polygon, so
  AB, A′B′ ∈ {4cos²(π/m)}. Over ℤ[φ] these are {1, 2, φ², 3, ρ}, and A′B′ may also
  be 0.
- (C,C′): either CC′ = 4cos²(π/m) (the polygon is a triangle), or 4 < CC′ < 4K²,
  where K = (√(1+μ) + √(1+μ′))² − 1 < 7.
- Every G must satisfy λ < K, have signature (2,1) at id, and be positive definite at σ.

### 1.2 Short pair (Lemma 10)

Here R, S, T, R′ are consecutive, S ⊥ R and S ⊥ T, with 1 < μ < 3 (so 4 < AB < 36),
μ′ = cos(π/m) and 4 < CC′ < 4K². Let G be the (r, t, r′) Gram matrix from §1.1 and
v = G⁻¹e₃, which in the basis (r, t, r′) satisfies v ⊥ r, v ⊥ t and v·r′ = 1.

Then s = a·v for some a, and the two crystallographic conditions give

  N := 4(s·r′)²/(s²r′²) = 4 / (r′²·(G⁻¹)₃₃) ∈ O.

This is Allcock's 4s₀² = 4 + 4(λ² + 2λμμ′ + μ′²)/(μ² − 1), re-derived; it settles
the 2μ′² versus μ′² discrepancy in favour of μ′². For each ideal divisor k of N:

  s = −(2 / (k·(G⁻¹)₃₃))·v,  s·r′ = −2/(k(G⁻¹)₃₃),  2(s·r′)/s² = −k.

### 1.3 Close pair (Lemma 11)

Here R, S, T, S′, R′ are consecutive with S ⊥ R, T and S′ ⊥ T, R′; both pairs (r,t)
and (r′,t) are ultraparallel, so 4 < AB, A′B′ < 36, and 4 < CC′ < 4K² with K < 15.
Put s = a·G⁻¹e₃ and s′ = b·G⁻¹e₁. Then:

- N = 4/(r′²(G⁻¹)₃₃) and N′ = 4/(r²(G⁻¹)₁₁) must lie in O;
- for divisors k | N and k′ | N′, a = −2/(k(G⁻¹)₃₃) and b = −2/(k′(G⁻¹)₁₁);
- we keep (s, s′) only if 2(s·s′)/s² ∈ O, 2(s·s′)/s′² ∈ O, s·s′ < 0 and
  (s·s′)² > s²s′². The last two say that S and S′ are ultraparallel (non-adjacent
  edges of a compact chamber).

## 2. From a configuration to candidate lattices

For each configuration (roots x₁, …, x_k in K³, k = 3, 4 or 5):

1. **Root lattice.** R = O-span of the xᵢ (an HNF over O).
2. **Reflective hull.** H = {v : xᵢ·v ∈ (xᵢ²/2)O for all i}, computed as the dual
   of the span of the 2xᵢ/xᵢ². Any lattice M in which the xᵢ are roots satisfies
   R ⊆ M ⊆ H.
3. **Smith normal form** of R inside H: H/R ≅ ⊕ O/aᵢ.
4. **Prime by prime.** For each prime 𝔭 dividing a₃, enumerate the 𝔭-primary
   intermediate lattices. The containment conditions are solved in closed form, so
   there is no filtering, and the result is checked against brute force on 7 test
   cases. Keep a local choice only if
   v_𝔭(det M) − 3·min v_𝔭(Gram entries) ≤ 1,
   i.e. the primitive rescaling is squarefree at 𝔭. This is valid because both
   squarefreeness and the rescaling are local.
5. **Combine** the surviving local choices (CRT), rescale to a primitive Gram
   matrix (divide by a totally positive generator of the content ideal), and keep M
   if det M is squarefree and every xᵢ is primitive in M.

The output contains every SSF lattice with the given configuration among its
roots. It is a superset of what Mark keeps, since her hull uses all roots of R
rather than only the configuration roots.

## 3. Validation

| Test | Result |
|---|---|
| Local superlattice enumeration vs brute force (ℤ, ℤ[√2], ℤ[φ]; 7 cases) | exact agreement |
| SNF over all three rings (up to 60 random matrices each) | U·A·V = S, divisibility chain, U, V unimodular |
| **ℤ[√2], short-edge configurations** | **282 with A′B′ > 0 and 1736 with T ⊥ R′, exactly Mark's Table 1 rows (15) and (16)** |
| ℤ[√2], short-edge SSF lattices | 134 and 351, vs Mark's 130 and 341 (close; ours is a superset by construction, §2) |
| ℤ, short edge: contains every ⟨−d, 1, 1⟩ for d ∈ {1,2,3,5,6,7,10,11,13,15,17,19,21,23} | yes, each certified by an explicit orthonormal pair |
| ℤ, short edge | 1843 configurations, 315 SSF lattices, 159 distinct determinants |

The exact match on configuration counts is the strongest check so far. It
confirms the re-derived Lemma 9, the boxes, the factorisation classes and the
Coxeter-angle restriction (Mark evidently imposed it too: without it the counts
are 360 and 1794).

**Short pairs.** Over ℤ[√2] the short-pair configuration counts are **5777 with
A′B′ > 0 and 88836 with T ⊥ R′, exactly Mark's Table 1 rows (22) and (23)**. This
confirms the re-derived Lemma 10, including N = 4/(r′²(G⁻¹)₃₃) and the divisor
loop over k.

**Close pairs.** Mark's row (27) is 97526 configurations. My count over ℤ[√2] was
still running when computation was stopped, so it is unverified.

**First counts over ℤ[φ]:**

| Configuration | A′B′ > 0 | T ⊥ R′ | Total |
|---|---|---|---|
| short edge | 298 | 1636 | 1934 |
| short pair | 2946 | 36961 | 39907 |
| close pair | — | — | not yet computed |

No ℤ[φ] candidate lattices have been computed yet; only configurations.

## 4. Performance

Pure Python with exact Fractions:

- short edge over ℤ: about 33 s;
- short-edge configurations over ℤ[√2]: about 4 s after replacing the divisor search
  with factorisation (190 s before), plus about 320 s for the lattices;
- short-pair configurations: about 210 s over ℤ[√2], about 200 s over ℤ[φ];
- close-pair configurations over ℤ[√2]: more than 40 minutes, unfinished.

The lattice stage costs about 0.2 s per configuration, so the short pairs alone
would take hours in Python (about 5 h over ℤ[√2], 2 h over ℤ[φ]).

Mark reports about 10 days of PARI/C for the ℤ[√2] close pairs, so close pairs over
ℤ[φ] will need either a port (PARI/GP or C) or more pruning before enumeration. The
pruning I plan is: apply λ < K before factorising, and pre-filter (C, C′) by the
ideal compatibility condition, which determines (C) from (z) and (A,B,A′,B′).

## 5. Status and next steps

1. Finish the ℤ[√2] close-pair count against Mark's row (27) (97526). Rows (22)
   and (23) already match.
2. Run ℤ[φ] short edge and short pair; plan the close-pair run (port or prune).
3. Remove duplicates up to isometry (genus invariants first, then an explicit
   isometry search).
4. Decide reflectivity: Vinberg's algorithm (Bugaenko's version) and Mark's
   walking method, with H₂ glue signs handled as in step 1 §4.5.
5. Final check: over ℤ[√2] reproduce exactly the 432; over ℤ[φ] the list must
   contain the calibration lattices from step 1 §8.
