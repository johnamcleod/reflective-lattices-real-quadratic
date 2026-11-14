# Lean plan

## Toolchain

- **Pins.** Lean `leanprover/lean4:v4.35.0` (`lean/lean-toolchain`) and Mathlib tag `v4.35.0` (`lean/lakefile.toml`; the exact commit is in `lake-manifest.json`).
- **Build.** `lake exe cache get && lake build`.
- **Kernel only.** The proofs use no `native_decide`, no `Lean.ofReduceBool` and no `implemented_by` in anything a theorem depends on. (User decision, 10 Nov 2026.)
- **No `sorry`, `admit` or custom `axiom`s**, except the imported theorems listed in §5, and only once each has been approved.

## 1. Library layout (`lean/ReflectZphi/`)

| File | Content |
|---|---|
| `Ring/ZPhi.lean` | O = ℤ[φ] as `QuadraticAlgebra ℤ 1 1` if Mathlib v4.35 has it (else a custom `structure ZPhi` with a proved `CommRing`): conj, norm, `DecidableEq`, embeddings `ι₁, ι₂ : O →+* ℝ` (φ ↦ goldenRatio / goldenConj) |
| `Ring/Euclid.lean` | norm-Euclidean, hence `EuclideanDomain`, hence PID |
| `Ring/Units.lean` | units = ±φⁿ; totally positive units = squares (U2); (N2) |
| `Ring/Primes.lean` | 2 and 3 inert, 5 = φ²·π², and the residue fields O/2 ≅ 𝔽₄, O/3 ≅ 𝔽₉, O/π ≅ 𝔽₅; φ generates each unit group |
| `Ring/ZSqrt2.lean` | the same facts for `Zsqrtd 2` (used by the ℤ[√2] validation certificates) |
| `Ring/Sign.lean` | exact, decidable sign at each embedding, as a computable function on coordinates, proved equal to the sign of `ι` |
| `Lattice/Basic.lean` | Gram matrices over O, admissibility (signature (2,1) at ι₁, definite at ι₂), roots, primitivity, SSF ⇔ det squarefree (rank 3) |
| `Lattice/RootNorm.lean` | Lemma 2.1 (two cases; r² ∣ 2 det L) and Cor 2.2 |
| `Lattice/Angles.lean` | the norm-ratio table; cos²(π/m) ∈ ℚ(√5) ⇔ m ∈ {2,3,4,5,6,10} (via `Polynomial.cyclotomic` degree / `Nat.totient` ≤ 4); cos(π/k) not an algebraic integer for odd k ≥ 3 |
| `Lattice/Corners.lean` | A₂, G₂, H₂, I₂(10) and B₂ normal forms; glue existence ⇔ residue condition; the B₂ ⇒ ⟨−d,1,1⟩ theorem |
| `Config/Gram.lean` | Lemmas 9–11 (algebraic part): given the inner products, the Gram matrix has the stated form, and N, N′, k, k′ and the close-pair conditions hold. Includes Mark's γ ⇔ re-derived s·s′ conditions |
| `Config/Boxes.lean` | a computable box enumeration with a proof of completeness (box ⊆ an explicit finite range, by bounding the coordinates from the two embeddings) |
| `Hull/SNF.lean` | the reflective hull is the dual of span{2xᵢ/xᵢ²}; SNF reduction; local SSF criterion (v_𝔭(det) − 3 min v_𝔭 ≤ 1 ⇔ squarefree at 𝔭 after rescaling) |
| `Cert/*.lean` | checkers (§3) with soundness theorems |
| `Main.lean` | the main theorems, each a wrapper over the checkers and the imported theorems |

## 2. Main theorems (names are provisional and will be kept in `paper/lean-map.md`)

- **The ring.**
  - `ZPhi.isPID`
  - `ZPhi.units_eq`
  - `ZPhi.totallyPositive_unit_iff_sq`
  - `ZPhi.two_inert`, `ZPhi.three_inert`, `ZPhi.five_ramified`
- **Lattice lemmas.**
  - `rootNorm_two_cases`
  - `normRatio_table`
  - `cos_pi_div_odd_not_isIntegral`
  - `corner_A2`, `corner_G2`, `corner_H2`, `corner_I2_10`, `corner_B2`
  - `B2_iff_diagonal`
  - `shortEdge_gram`, `shortPair_gram`, `closePair_gram`, `closePair_mark_iff_rederived`
  - `hull_correct`, `localSSF_correct`
- **Classification.**
  - `classification_zphi`: every SSF reflective rank-3 lattice over ℤ[φ] is isometric to one in `Data.zphiList`, and every element of that list is reflective. The statement is conditional on the imported theorems.

## 3. Certificates and checkers

Every checker is a total, computable `Bool` function on concrete data (integer coordinates only), together with a soundness theorem `check x = true → P x`. Evaluation is by `decide` / `Nat.decEq` in the kernel, with GMP-accelerated `Nat` literals.

| Certificate | Checker proves |
|---|---|
| isometry `(G₁, G₂, P, P⁻¹)` | Pᵀ G₁ P = G₂, P·P⁻¹ = I |
| Coxeter polygon `(G, roots)` | each rᵢ is a root of G; the consecutive angles are π/mᵢ exactly; non-consecutive pairs are ultraparallel; the angle sum and cycle closure give a compact polygon (Vinberg's combinatorial compactness criterion in rank 3, formalised in the finite form "a cyclically ordered list of pairwise non-obtuse roots whose consecutive pairs span positive-definite planes bounds a compact polygon") |
| non-reflectivity `(G, γ, chamber data)` | γ integral, γᵀGγ = G, γ preserves the finite root set bounding the partial chamber, and the trace condition gives infinite order (an eigenvalue argument over ℝ, proved once) |
| configuration chunk `(keys, lattices)` | per key: recompute G from the key (cheap); the hull basis, SNF data U, S, V with inverses (checked by matrix identities); the local superlattice lists with their size equal to the closed-form count; the surviving lattices |
| index-set certificate | box elements and factorisation classes: computed in Lean by the verified enumerator; the list of configuration keys is checked to equal the Lean-generated list |

**Completeness strategy** (TASK.md B.2, option "Lean verifies a certificate that every configuration was processed").

- Lean generates the configuration *keys* itself. These are boxes × factorisations × divisors. This is cheap: on the order of 10⁵ keys, from integer loops that are proved complete.
- For each key, Lean checks the externally produced certificate.
- **Feasibility risk.** The per-key work in the kernel may be too slow for about 2·10⁵ keys. Mitigations:
  - (a) split the certificates over many `.lean` files built in parallel by `lake`;
  - (b) make the checks proof-producing (the certificate carries U⁻¹ and V⁻¹, so only multiplication is needed);
  - (c) prune keys first with proved lemmas (for example the B₂ fast path).

  If the build time is still impractical, **stop and report** rather than switch to `native_decide`.

## 4. Trusted computing base

1. The Lean 4 kernel (v4.35.0), including GMP-accelerated `Nat` operations.
2. The axioms `propext`, `Classical.choice` and `Quot.sound`.
3. The imported theorems in §5, each declared as a single `axiom` in `ReflectZphi/Imported.lean`, with a docstring citation.
4. The JSON → Lean data generator (`tools/emit_lean.py`). It emits plain literals. The data are re-validated by the checkers, so the generator is trusted only for not *omitting* data, and Lean-side key generation covers that.

`scripts/check_axioms.lean` runs `#print axioms` on every main theorem. CI fails if anything outside (2) ∪ (3) appears.

## 5. Imported theorems (approved by the user on 2026-11-13; nothing else is added without asking)

| Name | Statement | Citation | Why not formalised |
|---|---|---|---|
| `allcock_thin_part` | every compact Coxeter polygon in ℍ² has a short edge, a short pair or a close pair, with the stated bounds on λ (paper Thm 5.1) | Allcock, Mem. AMS 220 (2012), Thm 1 and Lemmas 3–5; arXiv:1010.0486 | hyperbolic plane geometry not available in Mathlib |
| `vinberg_chamber` | W(L) acts simply transitively on its chambers; O′(L) = W(L) ⋊ Stab(C); L is reflective iff a chamber is a compact polygon (paper Appendix A.1) | Vinberg 1972 | needs hyperbolic geometry and discrete group theory |

Each is to be declared as a single `axiom` in `ReflectZphi/Imported.lean` once the lattice layer exists, so that the statement is the approved one verbatim, and `scripts/check_axioms.sh` is to allow exactly these two names.

The earlier proposals `vinberg_finite_index` and `vinberg_algorithm_correct` are withdrawn. The first is contained in `vinberg_chamber`. The second is not needed, because reflectivity decisions rest on certificates that are checked independently of how they were found.

To try first: formalising the finite linear-algebra part of Vinberg's compactness criterion for rank 3 (polygons), which would remove part of `vinberg_finite_index`.

## 6. Feasibility measurements for the certificate checkers (2026-11-13)

**Kernel throughput.** `decide +kernel` on a divide-and-conquer integer loop, with no Mathlib import (spike files, not kept):
- **Speed:** about 2,300 simple steps per second per core, with CPU time linear in the number of steps (2¹³, 2¹⁴, 2¹⁵ steps: 5 s, 8 s, 16 s).
- **Memory:** about 60 KB per step inside one declaration (1.0 GB at 2¹³, 1.5 GB at 2¹⁴). A linear recursion of 10⁵ steps did not finish in 600 s.
- **Consequence:** the work must be split into many small declarations (about 10³–10⁴ steps each), built in parallel.

**Enumeration work in the current certificates.** Fincke–Pohst nodes visited by `check_polygon` and `check_nonreflective` (ball covers), sampled on 25 + 25 ℤ[φ] candidates and extrapolated:

| certificates | nodes | enumerations |
|---|---|---|
| 1140 polygon (reflective) | ≈ 1.5·10⁷ | ≈ 5.8·10⁴ |
| 1290 translation (non-reflective) | ≈ 7.7·10⁷ | ≈ 1.2·10⁵ |

**Estimate.**
- A node is about 15 big-integer operations if the certificate supplies square roots (the checker then verifies s² ≤ X < (s+1)² rather than computing isqrt). That gives roughly 200–800 nodes per second per core.
- Total: about 9·10⁷ nodes, i.e. 30–130 core-hours, i.e. 4–16 h on 8 cores. Per-enumeration setup and root tests come on top, perhaps doubling it.
- So this is **slow but not impractical**. No switch to `native_decide` is needed.
- The configuration-completeness certificates (§3) have not been measured yet.

**Reformulation to avoid hyperbolic geometry.** The mirror-crossing test can be made purely algebraic.
- The mirror of r meets the polygon P exactly when r·pᵢ takes both signs over the vertices pᵢ.
- At a timelike point x of P with r·x = 0, the majorant M_x(r) = r·r − 2(r·x)²/(x·x) equals r², and r² ranges over a finite set of root norms.
- An explicit comparison M_x ≤ c·M_v (v the centre) for x in P then reduces the test to finitely many definite enumerations. This is linear algebra and needs no hyperbolic geometry in Lean.
- The ball cover becomes a list of such (v, c) pairs supplied by the certificate.

## 7. How the approved imports enter Lean (design, 2026-11-13)

**Hypotheses, not axioms.**
- `allcock_thin_part` and `vinberg_chamber` are stated as named propositions (`def AllcockThinPart : Prop`, `def VinbergChamber : Prop`) in `ReflectZphi/Imported.lean`.
- The main theorems take them as hypotheses: `theorem classification_zphi (hA : AllcockThinPart) (hV : VinbergChamber) : …`.
- Consequences:
  - `#print axioms` stays within {propext, Classical.choice, Quot.sound};
  - the dependence on the imports is visible in every statement;
  - the axiom check needs no allow-list at all.
- §5 is updated accordingly: no `axiom` declarations.

**Faithfulness.**
- The approved statements are geometric (chambers, compact polygons). They are stated with geometric definitions in the cone model of ℍ²: points are rays of {x ∈ ℝ³ : ι₁-form(x) < 0} in one sheet, mirrors are r^⊥, a chamber is the closure of a connected component of the complement of the mirrors, and a compact polygon is a chamber that is compact.
- The bridge from the algebraic polygon certificate to "P is a compact chamber" is then **proved in Lean** (cone-model linear algebra over ℝ), not imported.
- The exact Lean text of the two propositions was shown to the user and **approved on 2026-11-14** (`ReflectZphi/Imported.lean`, commit 3bd79e2). The approval covers these differences from the §5 wording:
  - O′(L) = W ⋊ Stab(C) is omitted;
  - Allcock's configuration may be read in either cyclic direction;
  - Allcock requires signature (2,1), and Vinberg requires b² + 4a to be a non-square (both rule out vacuous falsity).

**Done so far** (`Lattice/Basic.lean`): `Admissible`, `IsRoot`, `IsReflectionOf` (division-free), `isometryGroup` = O(L), `reflectionGroup` = W(L), and `Reflective` (finite index), together with `Cert/Mat3.lean` and `Cert/Iso.lean` (isometry checker with soundness).

## 8. The certificate-to-chamber bridge (design, 2026-11-14)

**Goal.** Prove in Lean: if the polygon checker accepts `(G, r₀ … r_{n−1}, data)`, then the polygon P cut out by the rᵢ is a compact chamber of W(L). Then `VinbergChamber` gives `Reflective`.

**Steps.**

| step | file | statement | kind |
|---|---|---|---|
| B1 | `Geometry/Minkowski.lean` | reverse Cauchy–Schwarz, and the reverse triangle inequality √(−q(x+y)) ≥ √(−q x) + √(−q y) for x, y in the same timelike cone | real linear algebra |
| B2 | `Geometry/Minkowski.lean` | **majorant bound:** if x is timelike, r·x = 0 and v is timelike, then (r·v)² ≤ (r·r)·(v·v − (v·x)²/(x·x)), where the second factor is ≥ 0 because x·x < 0 | Cauchy–Schwarz on x^⊥ |
| B3 | `Geometry/Minkowski.lean` | the ball {x : (v·x)² ≤ C²(v·v)(x·x)} is convex in the timelike cone, by concavity of √(−q) | from B1 |
| B4 | `Geometry/Polygon.lean` | if consecutive vertices pᵢ = rᵢ^⊥ ∩ r_{i+1}^⊥ are timelike and sign conditions hold, then P is the cone hull of the pᵢ, compact, with nonempty interior, and its edges are exactly the rᵢ | linear algebra |
| B5 | `Geometry/Polygon.lean` | a root mirror meets the interior of P iff r·pᵢ takes both strict signs | from B4 |
| B6 | `Geometry/Chamber.lean` | if no root mirror meets int P, then P is a chamber (`IsChamber`) | topology (cone ↔ sheet by normalisation) |
| B7 | `Cert/RootNorms.lean` | every root is ε^k times a root whose norm m is totally positive, m ∣ 2 det G, and ι₁(m)/ι₂(m) ∈ [1, ε₁⁴). The finite list of such m is checked by `decide` | uses only that ε is a unit (no unit-group theorem); PID for `m ∣ 2 det G` |
| B8 | `Cert/Enum.lean` | finite enumeration: all y ∈ O³ with M_v(y) ≤ K at ι₁ and y·y = σ(m) at ι₂, with bounds certified by the certificate (squares supplied, as in §6) | kernel computation |
| B9 | `Cert/Polygon.lean` | `checkPolygon` and `checkPolygon_sound`: the combination of B2–B8 | soundness proof |

**Coordinates.** B1–B5 are proved for the standard form J = diag(1, 1, −1). The certificate supplies an exact factorisation G = Lᵀ D L over K, with D = diag(d₁, d₂, d₃) and ι₁(d₁), ι₁(d₂) > 0 > ι₁(d₃), checked by ring arithmetic. Then P = diag(√d₁, √d₂, √−d₃)·L (over ℝ) carries G at ι₁ to J. So no Sylvester law is needed.

**Progress (2026-11-14).**
- Proved: B1–B3 (`Geometry/Minkowski.lean`).
- Proved: B4 and B5 in Minkowski coordinates (`Geometry/Polygon.lean`):
  - `hull`: every point of the half-planes is a nonnegative combination of three fan vertices;
  - `isCompact_polySet`;
  - `nonpos_on_polySet`;
  - `crossing_bound`: if `r^⊥` meets the polygon, then (r·v)² ≤ (r·r)(−v·v)(C² − 1).
- Proved: B6 (`Geometry/Chamber.lean`, `polySet_eq_chamber`). If the edges are roots, every root has one sign on the vertices, and an interior point is given, then the polygon is the closure of the connected component of sheet \ mirrors through that point. This is for an abstract set of spacelike root vectors in J coordinates.
- Proved: the transfer (`Geometry/Transfer.lean`, `Cert/Bridge.lean`). The certificate supplies a G-orthogonal basis f₀, f₁, f₂ over O with ι₁-signs (+, +, −), giving T = diag(√c)·F⁻¹ with ι₁(G) = Tᵀ J T (no spectral theorem).
  - `reflective_of_cert (hV : VinbergChamber) …`: from a `PolyCert` and the one-sign hypothesis `hone`, L is `Reflective`. Every PolyCert field is an equation in O or a sign at ι₁. Axioms: propext, Classical.choice, Quot.sound only.
- Proved: B7 (`Cert/RootNorms.lean`). Root norms divide 2 det G (PID, primitive vector); rescaling by a unit keeps roots and one-sign behaviour; every root has a unit multiple with norm in the window ι₂ m ≤ ι₁ m < ρ ι₂ m (only that u is a unit is used); such norms lie in an integer box and in the kernel-computed list `windowNorms` (box + exact window test + `m ∣ 2 det G`).
- Proved: B8 (`Cert/Enum.lean`, `Cert/Crossing.lean`, `Cert/QuadSolve.lean`, `Cert/PolyEnum.lean`).
  - `enum_sound`/`enumS_sound`: a Fincke–Pohst search over ℤⁿ, from a certificate S·A = Σ wᵢ aᵢᵀaᵢ (triangular integer rows). Integer square roots come from Newton's iteration and are checked (s+1)² > B, r² ≤ n < (r+1)²; the iteration itself is never proved.
  - `crossing_lat`: a root with both signs on the vertices satisfies q (r·V)² ≤ (p − q)(r·r)(−V·V) at ι₁, for a future centre V with q (V·Pᵢ)² ≤ p (V·V)(Pᵢ·Pᵢ). Plus Cauchy–Schwarz at ι₂.
  - The majorant ψ = 2q(x·V)(y·V) + (μ − qV·V)(x·y); Tr ψ is an integer form on ℤ⁶ (`trace_psi_eq`), bounded by K for crossing window roots.
  - **Stopped search** (`hone_of_enum2`): the search stops two levels early and solves the last O-coordinate exactly (`solveQuad`, via N and Tr square roots). The two innermost levels held about 95% of the nodes.
  - `reflective_of_enum2 (hV : VinbergChamber) …`: Reflective from PolyCert + centre + window + enumeration certificate. Axioms: propext, Classical.choice, Quot.sound only.
- Measured (2026-11-14, `tools/emit_polyenum.py`): ℤ[φ] classes 2 and 0 (triangles), stopped search 155 and 841 nodes; `decide +kernel` accepts both in 5 s and 13 s CPU. Negative control: the class-0 triangle enlarged by its reflection in one wall is rejected (the kernel proves the search returns `false`).
- Size (`tools/b8_size.py`, `tools/b8_split.py`): one centre per polygon is too large for long polygons (up to 5·10⁷ full-search nodes, class 58). Subdivision of the fan triangles (split point kA + lB) helps 2–3× on the full search; with the stopped search the per-piece cost falls ~30×.
- Next:
  1. B8′: several centres per polygon. Cover the fan triangles by a split tree (x = αA + βB + γC lies in (A, kA+lB, C) or (kA+lB, B, C)); one centre and enumeration per leaf.
  2. B9: computable deciders for every remaining hypothesis (PolyCert fields, hvert, hC, hK, Admissible, the window conditions on u) via `posCode`, with `Mat3` for det; then emit certificates for all classes and time them.

**Why this needs no ball cover.**
- By B2, a root r whose mirror meets P at x has M_v(r) = r² + 2(r·v)²/|v·v| ≤ r²·(2C² − 1), where C = max cosh d(v, pᵢ).
- By B3, the bound at the vertices holds on all of P.
- One centre v per polygon therefore suffices. If the single enumeration is too large, P can be split into a fan of triangles (v, pᵢ, p_{i+1}) with one centre each.
