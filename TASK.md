# Brief for Claude Code: rank-3 reflective lattices over ℤ[φ]

## 0. The project in one paragraph

Classify the strongly squarefree (SSF) reflective hyperbolic lattices of rank 3
over O = ℤ[φ], φ = (1+√5)/2. These are integral O-lattices of signature (2,1) at
the identity embedding, positive definite at the Galois conjugate σ, with
squarefree determinant, whose reflection subgroup has finite index in O′(L). This
is the ℚ(√5) analogue of A. Mark, "The classification of rank 3 reflective
hyperbolic lattices over ℤ[√2]" (Math. Proc. Camb. Phil. Soc. 164 (2018) 221–257,
arXiv:1512.01133; UT Austin thesis 2015), which follows D. Allcock, "The reflective
Lorentzian lattices of rank 3" (Mem. AMS 220 (2012), arXiv:1010.0486).

The work has two parts:

- **Part A:** code that completes the computation.
- **Part B:** a manuscript with all lemmas and proofs, every proof checked in
  Lean 4 with Mathlib.

Reference material I will supply:
- `step1-zphi-lemmas.md` (field-specific lemmas);
- `step2-root-configurations.md` (configuration lemmas, pipeline, validation);
- prototype Python code: `quadring.py`, `rank3.py`, `localenum.py`, `qsqrt5.py`,
  `step1_compute.py`, `corner_check.py`.

Read all of these first. Treat the Python as a specification and a correctness
oracle, not as the production code.

---

## 1. What is already established (to be re-checked, not trusted blindly)

**Field facts**
- O is a PID; N(φ) = −1, so the totally positive units are exactly the squares
  (Mark's (U2)/(N2)).
- The primes 2 and 3 are inert, and 5 = (π)² ramifies, with π = 3 − φ = √5·φ⁻¹.
- φ generates (O/2)^×, (O/3)^× and (O/π)^×.
- ρ := (5+√5)/2 = φ√5 = 4cos²(π/10).

**Root norms.** For a root r, r² | 2·det L. Because 2 is inert there are two
cases (L = ⟨r⟩ ⊥ r^⊥, or glue ≅ O/2). For an SSF lattice, r² ∈ {e, 2e} with e a
totally positive divisor of det L.

**Angles.** cos²(π/m) ∈ ℚ(√5) exactly for m ∈ {2, 3, 4, 5, 6, 10}. The norm ratios
at a corner are:

| m | 3 | 4 | 5 | 6 | 10 |
|---|---|---|---|---|---|
| r²/s² | 1 | 2 (ratio 1 impossible) | 1 | 3 | ρ ∼ π |

**Corner normal forms** (SSF lattices; p generates ⟨r,s⟩^⊥ ∩ L):

| Corner | Normal form |
|---|---|
| A₂ (π/3) | r² = s² = 2; always glued; p² = 3·det L; det L a nonzero square in O/3 ≅ 𝔽₉; exactly one of g± = ±α(2r+s)/3 + p/3 lies in L |
| G₂ (π/6) | the unglued A₂ case: L = A₂ ⊥ ⟨p²⟩, 3 ∤ p² (the unglued A₂ lattice acquires the norm-6 root r − s) |
| H₂ (π/5) | r² = s² = 2, Gram H = [[2,−φ],[−φ,2]]; always glued; p² = π·det L; det L a quadratic non-residue mod π; exactly one of ±α(2r+φs)/π + p/π lies in L |
| I₂(10) (π/10) | the unglued H case: L = H ⊥ ⟨p²⟩, π ∤ p². The I₂(10) root pair (norms 2, 2ρ) spans the same binary lattice H |
| B₂ (π/4) | **Theorem.** L is SSF with two roots at angle π/4 ⇔ L has a π/4 corner ⇔ L ≅ ⟨−d, 1, 1⟩ with d squarefree, d > 0, σ(d) < 0. (No glue is possible; the binary lattice [[1,−1],[−1,2]] ≅ ⟨1,1⟩.) The full proof is in my notes. |

**Thin part** (Allcock Thm 1; field-independent geometry). Every compact Coxeter
polygon has one of:
- a short edge (λ < K < 7);
- a short pair (λ < K < 5 + 4√2);
- a close pair (λ < K < 15);

where K = (√(1+μ) + √(1+μ′))² − 1. Over ℚ(√5) every admissible rank-3 lattice is
anisotropic, so every chamber is compact.

**Configuration Gram matrices** (re-derived; see step-2 notes §1). Short edge,
r² = 2A:

  G = [[2A, −AB, −AC′], [−AB, 2B, −A′Bε], [−AC′, −A′Bε, 2A′Bw/B′]],

where w = AB′C′/(A′BC) must be a totally positive unit and w = ε². When T ⊥ R′,

  G = [[2A, −AB, −AC′], [−AB, 2B, 0], [−AC′, 0, 2AC′/C]].

For a short pair, s = −(2/(k·(G⁻¹)₃₃))·G⁻¹e₃ with k | N := 4/(r′²(G⁻¹)₃₃) ∈ O
(this settles Allcock's μ′² versus 2μ′² in favour of μ′²). Close pairs work the same
way with s′ = −(2/(k′(G⁻¹)₁₁))·G⁻¹e₁ and the conditions on s·s′.

Edges meeting at a vertex satisfy the Coxeter restriction AB, A′B′ ∈ {4cos²(π/m)}.
Mark evidently imposed it too, because the counts match only with it.

**Validated prototype results**
- Over ℤ[√2], the configuration counts equal Mark's Table 1 exactly: short edge
  282 / 1736; short pair 5777 / 88836.
- Over ℤ[√2], the short-edge SSF lattice counts are 134 / 351 versus Mark's
  130 / 341. Ours is meant to be a superset, since the hull uses only the
  configuration roots. Explain the difference.
- Over ℤ, the short-edge candidates contain every ⟨−d,1,1⟩ with d ≤ 23 that was
  checked.
- Over ℤ[φ]: short edge 1934 configurations (298 / 1636), short pair 39907
  (2946 / 36961). Close pairs not yet counted, and no ℤ[φ] lattices computed yet.

**Arithmetic Coxeter triangles over ℚ(√5)** (computed; check against Takeuchi,
J. Math. Soc. Japan 29 (1977)). These twelve:

  (2,3,10), (2,4,5), (2,4,10), (2,5,5), (2,5,6), (2,5,10), (2,10,10), (3,3,5),
  (3,5,5), (4,4,5), (5,5,5), (5,10,10).

Non-arithmetic with Vinberg field ℚ(√5): (2,6,10), (3,10,10), (5,6,6).

**Calibration lattices** (must appear as reflective in the final list):
- ⟨−φ, 1, 1⟩ (Bugaenko);
- ⟨−√5, 1, 1⟩ ≡ ⟨−(5+3√5)/2, 1, 1⟩ (Guglielmetti thesis 2017);
- ⟨−(3+2√5), 1, 1⟩ and ⟨−(−3+2√5), 1, 1⟩ (Mcleod thesis 2013, §3.2);
- ⟨−φ, 2+φ, 1⟩ (Guglielmetti);
- lattices realising the twelve triangles.

The Guglielmetti and Takeuchi data were read secondhand: verify them against the
sources.

**Caveat.** Mark's papers were read only through an extraction tool. Fetch the
originals (arXiv:1512.01133, arXiv:1010.0486). If that fails, stop and ask me for
the PDFs.

---

## 2. Part A: code that completes the computation

### A.1 Technology
- Port the prototype to a fast exact system: PARI/GP (as Mark did), SageMath, or
  C++ with FLINT/Antic. Choose one, justify the choice in `methods.md`, and keep
  the Python prototype as the test oracle. **Exact arithmetic only**: floats are
  allowed solely for ordering heuristics and for pruning tests with a proven
  safety margin.
- Write the code for any ring in {ℤ, ℤ[√2], ℤ[φ]}. Every stage must run over
  ℤ[√2] for validation before it is trusted over ℤ[φ].
- Make long runs restartable (checkpoint per configuration chunk) and
  parallelisable.

### A.2 Pipeline
1. **Configurations** (short edge, short pair, close pair), exactly as in
   step-2 §1.
2. **Candidate lattices.** Root lattice R, reflective hull H (with respect to the
   configuration roots), Smith normal form of R in H, prime-by-prime enumeration of
   intermediate lattices with the local SSF test, CRT combination, primitive
   rescaling, and the final checks (det squarefree, configuration roots primitive).
3. **Triangles** (the short-edge case with CC′ ∈ {4cos²(π/m)}): cross-check
   against the twelve arithmetic triangles.
4. **Isometry classes.** Use genus invariants as a first filter, then explicit
   isometry certificates (a basis change over O). Use the B₂ theorem as a fast
   path: any lattice with a π/4 pair of roots is ⟨−d,1,1⟩ for d = −det L.
5. **Reflectivity.**
   - Vinberg's algorithm, in Bugaenko's version for totally real fields (the
     conjugate-definite bounds make each batch finite).
   - Mark's "walking" method along a boundary component, using the A₂ and H₂ glue
     signs. The H₂ analogue of her Lemmas 6–7 (glue sign constant along a boundary
     component) must first be proved in Part B.
   - Each reflective lattice must output its Coxeter polygon with exact Gram
     matrix and a compactness certificate.
   - Each non-reflective lattice must output a certificate: an infinite-order
     element of O′(L) preserving the fundamental domain of the reflection group,
     or an infinite symmetric chain of simple roots.
   - Record "undetermined" cases separately. Never guess.
6. **Maximality and summary:** for each final lattice give its determinant, the
   number of sides, the angles and the triangle type where relevant.

### A.3 Validation gates (each must pass before going on)
1. **Unit tests:** ring arithmetic, SNF (U·A·V = S, divisibility chain, unimodular
   U and V), local enumeration versus brute force, divisors versus brute force.
2. **ℤ[√2] configurations:** exactly 282 / 1736 / 5777 / 88836 / 97526 (Mark's
   Table 1 rows (15), (16), (22), (23), (27)).
3. **ℤ[√2] lattices:** compare with Mark's squarefree-enlargement counts
   130 / 341 / 233 / 1096 / 581, and explain every difference.
4. **ℤ[√2] final:** reproduce exactly the 432 SSF reflective lattices of Mark's
   Theorem 1 (her appendix). Mismatches go to `DISCREPANCIES.md` with a resolution.
5. **ℤ[φ]:** every calibration lattice in §1 appears and is classified as
   reflective.
6. **Diagonal check:** the ℤ[φ] lattices with a π/4 corner must be exactly the
   reflective ⟨−d, 1, 1⟩.

### A.4 Outputs
- `data/zphi_rank3.json`: every lattice with Gram matrix, determinant, Coxeter
  polygon, and the certificate for reflectivity or non-reflectivity.
- `data/zsqrt2_rank3.json`: the reproduction of Mark's list.
- `certificates/`: machine-checkable files consumed by the Lean checker (Part B).
- `report.md`: counts per stage, runtimes, the final table, and the comparison
  with Mark.

---

## 3. Part B: manuscript, with every proof verified in Lean

### B.1 Manuscript (LaTeX, `paper/`)
Proposed structure:

1. Introduction and statement of the main theorem: the classification over
   ℤ[φ], plus the B₂ ⇒ diagonal theorem as a separate result.
2. Preliminaries: admissible lattices, roots, SSF, reflective hulls, Vinberg's
   criterion.
3. Arithmetic of ℤ[φ]: units, (U2)/(N2), residue fields, prime decomposition of
   2, 3 and 5.
4. Root norms (the two-case lemma).
5. Angles and norm ratios.
6. Corner normal forms: A₂, G₂, H₂, I₂(10), B₂, including the glued/unglued
   pairing and the H₂ glue-sign lemma.
7. The B₂ theorem and its corollary for the diagonal family.
8. The thin part (Allcock, cited) and the configuration lemmas (Lemmas 9–11
   analogues, with the re-derived Gram matrices).
9. From configurations to candidate lattices: correctness of the hull, the SNF
   reduction and the local SSF criterion.
10. Reflectivity decisions: the algorithms and the certificate formats.
11. Results: tables and Coxeter polygons.
12. Appendix: the full list.

Write a full proof for every lemma, not a sketch. Credit results that transfer
from Mark or Allcock as such, and mark new results clearly (the H₂ and I₂(10)
corners, the B₂ theorem). The step-1 notes include a literature-status table.

### B.2 Lean 4 + Mathlib verification (`lean/`)
- Use Lean 4 with a current Mathlib, and pin the toolchain and Mathlib version.
- **No `sorry`, no `admit`, no custom `axiom`s, except the explicitly listed
  imported theorems below.** CI must run `lake build` and `#print axioms` on every
  main theorem and fail if anything unexpected appears.
- **The ring.** Model ℤ[φ] either with Mathlib's quadratic-algebra structures
  (check what exists: `Zsqrtd` covers ℤ[√d] but not ℤ[φ]; recent Mathlib may have
  `QuadraticAlgebra`) or as a custom structure with a proved `CommRing` instance,
  the norm, conjugation, and the embedding into ℝ. Prove Euclidean (hence PID),
  the unit group (±φⁿ), (U2)/(N2), the inertness of 2 and 3, the ramification of 5,
  and the residue-field facts.
- **Formalise and prove:**
  - the root-norm lemma;
  - the norm-ratio table;
  - the corner normal-form lemmas for A₂, G₂, H₂, I₂(10) and B₂;
  - the full B₂ ⇒ ⟨−d,1,1⟩ theorem;
  - the configuration Gram-matrix lemmas (the algebraic part: given the inner
    products, the Gram matrix has the stated form and the divisibility conditions
    hold);
  - the hull/SNF/local-SSF correctness lemmas;
  - the lemma that cos(π/k) is not an algebraic integer for odd k ≥ 3, which the
    odd-angle arguments use.
- **Imported theorems** (stated as clearly labelled hypotheses or axioms, each
  with a citation and a comment saying why it is not formalised here):
  - Allcock's thin-part theorem (hyperbolic plane geometry);
  - Vinberg's compactness and arithmeticity criteria;
  - the correctness of Vinberg's algorithm.

  Keep this list as short as possible. If formalising any of them is feasible
  (for example the finite linear-algebra parts of Vinberg's criterion), do it.
- **Computational results.** The Lean development must check the certificates
  produced by Part A rather than trust them:
  - isometries (matrix identities over ℤ[φ], checked by `decide`, `norm_num` or a
    verified reflective checker);
  - Gram matrices of Coxeter polygons and their compactness data;
  - non-reflectivity witnesses (an integral isometry preserving the form, with a
    proof of infinite order).

  The enumeration itself (that the candidate list is complete) must be justified
  in one of two ways: implement the enumeration in Lean and evaluate it, or have
  Lean verify a certificate that every configuration was processed. Choose one,
  and document the trusted computing base exactly.
- Keep a mapping file `paper/lean-map.md` from each manuscript lemma to its Lean
  theorem name.

---

## 4. Ground rules and stopping points
- Start in plan mode. Write `methods.md` and a Lean plan before coding.
- Commit after each gate. Record every doubt in `OPEN_QUESTIONS.md`, and never
  assume a doubt away.
- **Stop and report:**
  - after gate A.3.2 (the ℤ[√2] configuration counts);
  - after gate A.3.4 (Mark's 432 reproduced or not);
  - before the long ℤ[φ] close-pair run (give the estimated runtime);
  - if any Lean lemma turns out to be false as stated (report the counterexample);
  - before adding anything to the list of imported theorems.

