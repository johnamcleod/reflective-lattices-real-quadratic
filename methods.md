# Methods

The task: classify the strongly squarefree (SSF) reflective rank-3 hyperbolic lattices over O = ℤ[φ]. The method is validated end to end over ℤ[√2] against Mark (arXiv:1512.01133) before it is trusted over ℤ[φ].

## 1. Conventions

- **Rings.**
  - O ∈ {ℤ, ℤ[√2], ℤ[φ]}, with ω = 1, √2 or φ, and K = Frac O.
  - Each is a norm-Euclidean PID with a fundamental unit ε of norm −1: ε = 1+√2, or ε = φ.
  - Hence the totally positive units are exactly (O^×)², which is Mark's (U2).
- **Embeddings.**
  - id: √D > 0. σ: √D ↦ −√D.
  - "x > 0" without qualification means id(x) > 0. The conjugate x̄ means σ(x).
- **Lattices.**
  - An *admissible* lattice is an O-lattice L ≅ O³ with symmetric Gram matrix G ∈ M₃(O), of signature (2,1) at id and positive definite at σ.
  - So det G < 0 < σ(det G). This is Mark's convention, with norms r² = r·r.
- **Roots.**
  - A root is a primitive r ∈ L with r² ≫ 0 (totally positive) and 2(r·x)/r² ∈ O for all x ∈ L.
  - Equivalently, 2Gr ∈ r²·O³.
- **SSF.** In rank 3, SSF is the same as det L squarefree (Mark §2.7).
- **Up to scale.** A lattice is *primitive* if the content ideal of its Gram entries is (1). Every lattice is rescaled to be primitive by a totally positive generator of the content ideal (which exists by (U2)/(N2)).

## 2. Technology

**Choice:** PARI/GP 2.17.4 as the exact number-theory engine, through `cypari2` from Python 3.10. A C kernel is added only where profiling demands it.

- **Native and exact in PARI:**
  - module HNF and SNF over O_K: `nfhnf`, `nfsnf`;
  - ideal factorisation: `idealfactor`, `idealprimedec`;
  - units: `bnfinit`;
  - signatures: `qfsign`, `nfeltsign`;
  - automorphism and isometry testing over ℤ (`qfauto`, `qfisom`) on the restriction of scalars.
- **Reasons for PARI.** These are exactly the hard parts of the pipeline. It is installed; Mark used it (her C program linked libpari), so runtimes are comparable.
- **Why not the alternatives.**
  - SageMath: not installed, heavy, and its number-field module code calls PARI anyway.
  - FLINT/Antic: fast element arithmetic, but no module HNF/SNF over O_K and no ideal machinery; those live in Hecke.jl, which would mean adding Julia.
- **Python.** Used for orchestration, checkpointing, `multiprocessing`, JSON and pytest.
- **Element representation.** Hot loops do not use `Fraction` objects. An element of K is an integer triple (a, b, n) meaning (a + bω)/n, with n > 0 and gcd(a,b,n) = 1.
  - Signs are decided exactly: sign(a + b√D) by comparing a² with D·b² when the signs of a and b differ. For φ, write a + bφ = (2a + b + b√5)/2.
- **C kernel.** The plan is to move the configuration loops to C (GMP via libpari) only if profiling shows the ℤ[√2] close-pair run needs more than about 24 h on 8 cores. That decision will be recorded here with measurements.
- **Measured (gate A.3.2).** With integer-triple arithmetic the full ℤ[√2] close-pair configuration enumeration takes 76 CPU-minutes, about 10 min wall on 8 workers. So **no C kernel is needed for the configurations.** The lattice stage will be profiled at gate A.3.3 before deciding.
- **Oracle.** `prototype/` holds the supplied Python, unmodified. Tests compare the production code with it wherever the prototype is fast enough.

## 3. Exactness policy

- **Exact everywhere.** Every accept/reject decision (signature, integrality, divisibility, squarefreeness, root conditions, angle labels, compactness) is made in exact arithmetic.
- **Floats** are allowed only for:
  - ordering heuristics (batch order in Vinberg, the order of walking);
  - enclosing boxes. Box bounds are enlarged by a margin, and every element is then re-tested exactly against the strict inequalities.
- **Irrational bounds** such as λ < K, where K involves square roots of elements of K, are decided exactly by squaring with sign bookkeeping (`zphi/exact_bounds.py`). The prototype's `1e-12` tolerance is not used as a decision.

## 4. Pipeline

### 4.1 Boxes and factorisations (Mark §3.2, Lemma 8)

- **Elements.** All z ∈ O with lo < z < hi and 0 < σ(z) < 4. A good factorisation is z = uv with u, v ≫ 0.
- **Classes.** Factorisations are counted modulo unit squares, i.e. as pairs of ideals ((u), (v)) with (u)(v) = (z).
- **Representatives.** Each ideal gets a canonical totally positive generator, reduced so that 1 ≤ u/ū < η², where η = ε² is the fundamental totally positive unit.
- **Expected over ℤ[φ]** (step-1 §5): 7/57/350/807/1603 elements and 11/147/1126/2902/6217 classes.

### 4.2 Configurations (Mark Lemmas 9–11; step-2 §1)

**Two implementations, compared by a test:**

- **(M)** Mark's printed matrices (15), (16), (22), (23), (27) and conditions (14), (21), (25), (26), transcribed from arXiv:1512.01133 pp. 18–21.
- **(R)** The re-derived forms (step-2 §1): G = Gram(r, t, r′); s = −(2/(k·(G⁻¹)₃₃))·G⁻¹e₃, and likewise s′.

Both must give the same configurations up to scale.

**Coxeter restriction.**
- When R∩T (or R′∩T) is a vertex, AB (resp. A′B′) ∈ {4cos²(π/m)}. Without this the ℤ[√2] counts are 360/1794, not 282/1736. So Mark evidently imposed it, although her Lemma 9 is printed with the full box 0 < AB < 4.
- When CC′ < 4 (the triangle case), CC′ ∈ {4cos²(π/m)} likewise.

**Counts.**
- A *root configuration* is one choice of (A,B,A′,B′,C,C′) (+ k, + k′) giving an admissible matrix.
- **Gate A.3.2:** over ℤ[√2], (15)/(16)/(22)/(23)/(27) = 282 / 1736 / 5777 / 88836 / 97526.

### 4.3 Candidate lattices (step-2 §2)

For each configuration with roots x₁…x_k ∈ K³:

1. **R** = O-span of the xᵢ (`nfhnf`).
2. **H** = {v : xᵢ·v ∈ (xᵢ²/2)O} = the dual of span{2xᵢ/xᵢ²} (the reflective hull of the configuration roots).
3. **SNF** of R in H (`nfsnf`): H/R ≅ ⊕ O/aᵢ.
4. **Prime by prime.** For each prime 𝔭 | a₃, enumerate the 𝔭-primary intermediate lattices in closed form (prototype `local_superlattices`, re-implemented). Keep the local choices with v_𝔭(det M) − 3·min v_𝔭(Gram) ≤ 1.
5. **Combine (CRT).** Rescale to a primitive Gram matrix. Keep M if det M is squarefree, every xᵢ is primitive in M, and (as in Mark §3.5) the configuration is *locally simple* in M. Local simplicity means that no root of M of a norm allowed by Lemma 2.1 separates two consecutive configuration roots. It is checked exactly by the rank-3 Vinberg kernel restricted to the corners of the configuration.

**Gate A.3.3:** compare the counts with Mark's squarefree column, 130 / 341 / 233 / 1096 / 581.

### 4.4 Isometry classes

1. **Invariants** (a filter only, never a proof of isometry):
   - det up to unit squares;
   - local invariants at 𝔭 | 2·det: the Jordan decomposition, plus Hasse invariants at finite primes and at σ.
2. **Isometry certificates.** An explicit P ∈ GL₃(O) with Pᵀ G₁ P = G₂, found by:
   - (i) matching chambers: map simple roots to simple roots, as in `reflect-z2/reflect/isometry.py`;
   - (ii) a fallback: `qfisom` on the ℤ-restriction of scalars of the trace forms Tr(G) and Tr(√D·G), with any solution checked to be O-linear.
3. **B₂ fast path.** By Lemma 4.3 (step-1), a lattice with a π/4 pair of roots is ⟨−d,1,1⟩ with d = −det L. The certificate is an explicit orthonormal pair.

### 4.5 Reflectivity

- **Vinberg (Bugaenko).** The control vector is v₀ ∈ L with v₀² < 0. Candidate roots of norm m at distance ≤ Δ lie in a bounded ellipsoid of the ℤ-restriction of scalars (the positive majorant at id plus σ(Q) at σ). They are found by Fincke–Pohst on an exactly LLL-reduced basis, and each one is verified exactly.
  - **Termination test.** P is compact iff every vertex is elliptic of rank 2 and the edge cycle closes, checked exactly (no floats) on the Gram matrix. All chambers are compact, since every admissible lattice over ℚ(√5) or ℚ(√2) is anisotropic.
  - Adapted from `reflect-z2/reflect/vinberg3.py`, generalised to a ring parameter.
- **Walking (Mark §4).** Used along a boundary component with the A₂ (and, once Lemma H₂-glue-sign is proved, the H₂) glue signs. It is used only where Vinberg's batch count explodes.
- **Outputs.**
  - Reflective: the Coxeter polygon with exact Gram matrix and a compactness certificate.
  - Non-reflective: an integral isometry γ with γᵀGγ = G preserving P, with |tr γ| > 3 at id (hence infinite order, loxodromic), or an infinite symmetric chain.
  - Otherwise `undetermined`.

### 4.6 Checkpointing and parallelism

- **Chunks.** Configurations are generated deterministically, sorted by (A,B,A′,B′,C,C′,k,k′) in canonical form, and split into chunks of fixed size.
- **Checkpoints.** Each chunk writes `checkpoints/<ring>/<lemma>/<chunk>.jsonl` plus a `.done` marker, and reruns skip finished chunks. Workers run under `multiprocessing.Pool`.
- **Determinism.** Every output record carries the configuration key, so results can be merged in any order.

## 5. Validation gates

These are the gates of TASK.md §A.3, each a pytest marker:

| Gate | Content |
|---|---|
| A.3.1 `gate1` | unit tests: ring, SNF, local enumeration, divisors |
| A.3.2 `gate2` | ℤ[√2] configuration counts 282 / 1736 / 5777 / 88836 / 97526 |
| A.3.3 `gate3` | ℤ[√2] lattice counts vs 130 / 341 / 233 / 1096 / 581; differences explained |
| A.3.4 `gate4` | Mark's 432 reproduced exactly |
| A.3.5 `gate5` | ℤ[φ] calibration lattices present and reflective |
| A.3.6 `gate6` | ℤ[φ] π/4-corner lattices = reflective ⟨−d,1,1⟩ |

## 6. Sources

The PDFs and their text conversions are in `papers/`.

| Ref | Status |
|---|---|
| Mark, arXiv:1512.01133 | fetched; Lemmas 9–11 and Table 1 read in the original |
| Allcock, arXiv:1010.0486 | fetched |
| Takeuchi, J. Math. Soc. Japan 29 (1977) | to fetch (Project Euclid) |
| Guglielmetti, thesis (Fribourg 2017) | to fetch |
| Mcleod, thesis (Durham 2013) | copy in `../reflect-z2/papers/`; to be copied here |
| Bugaenko 1984/1990 | probably unavailable; cited secondhand, flagged |

## Field profiles (done after gate A.3.4)

The algorithms never branch on the field. A `Ring` (`zphi/ring.py`) is the generic order arithmetic of ℤ[ω] with ω² = c₀ + c₁ω, composed with a `FieldProfile` (`zphi/fields.py`). The profile is plain data: c₀, c₁, the fundamental unit, the printed symbol, the PARI polynomial (cross-checks only), and reference values for the tests.

- **Hypotheses are checked when a ring is built, not assumed.** A field failing any check is rejected with `HypothesisError` (tested in `tests/test_fields.py`):
  - (H2): degree 2, or degree 1 (ℤ, oracle tests only).
  - ℤ[ω] is the maximal order: the discriminant is fundamental.
  - (H1): O is norm-Euclidean, checked against the complete list of norm-Euclidean real quadratic fields.
  - The stored unit is fundamental: an exact search shows no unit between 1 and ε.
- **Derived data is computed, not typed in.** γ(m) = 4cos²(π/m) ∈ O is found for every m with [ℚ(cos 2π/m):ℚ] ≤ 2, that is m ∈ {2, 3, 4, 5, 6, 8, 10, 12}. Each value is verified exactly through the Chebyshev recursion C_m(γ−2) = 2, primitive. This replaces the old `D == 2` / `D == 5` branches in `boxes.gammas`; for example ℚ(√3) automatically gets γ(12) = 2+√3.
- The remaining `degree == 1` branches are the ℤ special case.
- Field-specific lemmas stay out of the generic layer and live in the specialisation part of the paper: corner normal forms, glue conditions, (U2)/(N2).

Regression after the refactor: gates A.3.1–A.3.3 by the full test suite; gate A.3.4 by re-verifying every stored certificate and re-running the classification (see report.md).
