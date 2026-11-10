# Rank-3 reflective lattices over ℤ[φ]: Step 1, the field-specific lemmas

9 November 2026 (revised the same evening: corner normal forms in §4.2, §4.5 and
§4.6 corrected; literature status added as §10). Companion files: `qsqrt5.py`
(exact arithmetic in ℚ(√5)), `step1_compute.py`, `step1_results.json`,
`corner_check.py`.

**Notation.** O = ℤ[φ], with φ = (1+√5)/2. K = ℚ(√5), with id(√5) > 0 and
σ(√5) < 0. Let π = 3 − φ = 4 − φ² = √5·φ⁻¹, a generator of the ramified prime
above 5 (N(π) = 5), and ρ = (5+√5)/2 = φ√5 = 4cos²(π/10). "SSF" means strongly
squarefree; in rank 3 that is the same as det L squarefree (Mark §2.7). Lattices
are integral O-lattices of signature (2,1) at id that are positive definite at σ.
So det L < 0 < σ(det L), and N(det L) < 0.

The template is Mark's ℤ[√2] classification (thesis, UT Austin 2015; *Math. Proc.
Camb. Phil. Soc.* 164 (2018)), which follows Allcock's rank-3 classification over ℤ.
**Caveat:** I read Mark's text only through an extraction tool. Where her exact
statements matter, they are marked *(check against Mark)*.

---

## 0. Summary

| Ingredient | Over ℤ[√2] (Mark) | Over ℤ[φ] (this note) |
|---|---|---|
| Fundamental unit | 1+√2, norm −1, so (U2)/(N2) | φ, norm −1, so (U2)/(N2) hold, verified |
| The prime 2 | ramified, (√2)² | **inert**, O/2 ≅ 𝔽₄ |
| The prime 3 | inert | inert, O/3 ≅ 𝔽₉ |
| The prime 5 | inert | **ramified**, (π)², O/π ≅ 𝔽₅ |
| Chamber angles π/m | m ∈ {2,3,4,6,8} | **m ∈ {2,3,4,5,6,10}** |
| Norm ratio at π/4 | 1 or 2 | **2 only** |
| New corner types | — | **H₂ (π/5), I₂(10) (π/10)** |
| Thin-part constants 7, 5+4√2, 15 | geometric | unchanged (geometric) |
| Arithmetic Coxeter triangles | 3 maximal (of 8) | **12 arithmetic triangles**, §7 |

Three new structural facts come out of this:

1. **π/4 corners force a diagonal lattice.** An SSF lattice with a corner of angle
   π/4 is isometric to ⟨1, 1, det L⟩ (§4.3). This links directly to the diagonal
   family −d·x₀² + x₁² + x₂².
2. **Glued and unglued corners pair up.** Each binary root lattice gives two corner
   types, depending on whether there is glue:

   | Binary lattice | Glued | Unglued |
   |---|---|---|
   | A₂ | A₂ corner (π/3); always glued, p² = 3 det L (Mark's Lemma 4) | G₂ corner (π/6); L = A₂ ⊥ ⟨p²⟩ |
   | H = [[2,−φ],[−φ,2]] | H₂ corner (π/5); always glued, p² = π det L | I₂(10) corner (π/10); L = H ⊥ ⟨p²⟩ |

   In the unglued lattice, extra roots of norm 6 (resp. 2ρ) appear orthogonal to
   p, and they double the dihedral group (§4.2, §4.5, §4.6).
3. **H₂ glue criterion.** H₂ corners occur exactly when det L is a quadratic
   non-residue mod π (§4.5).

---

## 1. Units and norm classes

- φ² = φ + 1 and N(φ) = −1. So the totally positive units are exactly
  {φ^{2k}} = (O^×)². This is Mark's condition (U2), and (N2) follows.
- Hence every principal ideal (O is a PID, class number 1) has a totally positive
  generator, unique up to unit squares. Good factorisations z = uv (§5) correspond
  to ideal divisors of (z).
- **Residue unit groups.** φ has multiplicative order 3 mod 2, 8 mod 3 and 4 mod π
  (computed). So units surject onto (O/2)^×, (O/3)^× and (O/π)^×. This is what lets
  glue vectors be normalised by rescaling with units (§4).

## 2. Root norms (the analogue of Mark §2.10)

**Lemma 2.1.** Let r be a root of L, M = ⟨r⟩ ⊥ r^⊥, and G = L/M. Then G embeds in
(½O·r)/(O·r) ≅ O/2 ≅ 𝔽₄. Since 2 is inert, **G = 0 or G ≅ 𝔽₄**. There are two
cases, where Mark had three:

- (a) G = 0: L = ⟨r⟩ ⊥ r^⊥, and r² | det L.
- (b) G ≅ 𝔽₄: r²/2 ∈ O, r²/2 | det L, and 4·det L = r²·det(r^⊥).

In both cases r² | 2·det L.

*Proof.* Projection of L onto Kr lands in {x r : r·(xr) ∈ (r²/2)O} = ½O·r, by the
root condition. So G embeds in ½O·r / O·r ≅ O/2O, which is a field.

In case (b), some x ∈ L has r·x = r²/2. Then 2r/r² ∈ L* has order ideal
(r²/2) in L*/L, and that order divides det L. The discriminant relation is
[L:M]² = (2)², which gives the last formula. ∎

**Corollary 2.2 (SSF root norms).** If det L is squarefree, every root norm is, up
to unit squares, e or 2e for a totally positive divisor e of det L. That is a
finite, explicit list.

## 3. Chamber angles and norm ratios (the analogue of Mark §2.12, Lemma 3)

cos²(π/m) ∈ K exactly for m ∈ {2, 3, 4, 5, 6, 10}. Indeed ℚ(cos 2π/m) ⊆ ℚ(√5)
forces φ(m) ≤ 4, and m = 8, 12 give ℚ(√2), ℚ(√3). Let γ(m) = 4cos²(π/m).

For roots r, s at angle π/m, put x = 2(r·s)/r² and y = 2(r·s)/s². Both lie in O,
xy = γ(m), and r²/s² = y/x. Norms are totally positive, so the ratio is a totally
positive element up to unit squares. That gives:

| m | γ(m) | Factorisation of γ in O | r²/s² up to unit squares (and inversion) |
|---|---|---|---|
| 3 | 1 | unit | **1** |
| 4 | 2 | 2 inert (prime) | **2** (ratio 1 impossible, unlike ℚ(√2)) |
| 5 | φ² = (3+√5)/2 | unit | **1** (odd m forces conjugate reflections) |
| 6 | 3 | 3 inert (prime) | **3** |
| 10 | ρ = φ√5 | π·(unit) | **ρ ∼ π** (ρ is totally positive) |

## 4. Corner normal forms in SSF lattices

Let r, s be simple roots at a corner, with p a generator of ⟨r,s⟩^⊥ ∩ L, and
M = ⟨r,s⟩ ⊥ O·p. The reflective hull of ⟨r,s⟩ is
{v : r·v ∈ (r²/2)O, s·v ∈ (s²/2)O}, and L/M embeds in hull/⟨r,s⟩ (glue).
The computed order ideals of hull/⟨r,s⟩ (`corner_hulls` in the results file) are:

| Corner | Normalised Gram of ⟨r,s⟩ | det | hull/⟨r,s⟩ |
|---|---|---|---|
| A₂ (π/3) | b·[[2,−1],[−1,2]] | 3b² | O/3 ≅ 𝔽₉ |
| B₂ (π/4) | a·[[1,−1],[−1,2]] | a² | O/2 ≅ 𝔽₄ |
| G₂ (π/6) | b·[[2,−3],[−3,6]] | 3b² | 0 |
| H₂ (π/5) | b·[[2,−φ],[−φ,2]] | b²π | O/π ≅ 𝔽₅ |
| I₂(10) (π/10) | b·[[2ρ,−ρ],[−ρ,2]] | b²π (since ρ(4−ρ) = ρφ⁻² = π) | 0 |

The factor 2 in A₂, H₂, G₂ and I₂(10) is forced, since 2 is inert. For example, at an
H₂ corner r·s = −r²φ/2 must lie in O.

### 4.1 SSF forces b (or a) to be a unit

In every case below, a prime 𝔭 dividing b (or a) leads to 𝔭² | det L, either
directly or through the integrality of the glue vector. So b (or a) is a totally
positive unit, i.e. a unit square, and can be normalised to 1 by rescaling r and s
by units. The A₂, B₂ and H₂ arguments are written out below; G₂ and I₂(10) have no
glue, so det L = (unit)·det⟨r,s⟩·p², and b must be a unit.

### 4.2 A₂ corners (the analogue of Mark's Lemmas 4–5)

Let v_r = (2r+s)/3, so that r·v_r = 1, s·v_r = 0 and v_r² = 2/3. Up to O/3-scaling
of the glue, any glue vector is g = α v_r + p/3 with α ∈ (O/3)^×. Then

  g² = (2α² + det L)/3, with p² = 3·det L.

So:

- **Glued:** possible if and only if det L ≡ −2α² ≡ α² (mod 3), i.e. det L is a
  nonzero square in 𝔽₉. In coordinates a + bφ mod 3, the allowed residues are
  {1, 1+φ, 2, 2+2φ} = {φ⁰, φ², φ⁴, φ⁶}. Then α is determined up to sign, and
  exactly one of g± = ±α v_r + p/3 lies in L. With α = 1 these are Mark's
  g± = (r+s)/2 ± (r−s)/6 + p/3; note that (2r+s)/3 = (r+s)/2 + (r−s)/6.
- **Unglued:** the corner is **not** of type A₂. In L = A₂ ⊥ Op with 3 ∤ p², the
  vector r − s has norm 6 and (r−s)·r = 3, (r−s)·s = −3, (r−s)·p = 0. So
  (r−s)·x ∈ 3O for all x ∈ L, and r − s is a root. The roots orthogonal to p form
  a G₂ system, so the corner at p is a G₂ corner; this is §4.4. With glue,
  (r−s)·g = 1 ∉ 3O, so r − s is not a root, and the corner is genuinely A₂.
  (Checked by `corner_check.py`: 6 mirror lines unglued, 3 glued.)

**Conclusion (agrees with Mark's Lemma 4).** At an A₂ corner of an SSF lattice,
r² = s² = 2 up to unit squares, there is always glue, p² = 3 det L, and det L is a
nonzero square mod 3. An earlier version of this note flagged Mark's Lemma 4 as
possibly missing a hypothesis; that was a mistake, since the unglued "A₂" lattice
actually has a G₂ corner. Her Lemmas 6–7 and Corollary 1 (glue signs along a
boundary component) are orientation arguments and should transfer unchanged.

### 4.3 B₂ corners: L is diagonal

**Lemma 4.3.** If L is SSF and has a corner of angle π/4, then there is no glue,
r² = 1 and s² = 2 (up to unit squares), and

  L = ⟨r,s⟩ ⊥ O·p ≅ ⟨1, 1, det L⟩.

*Proof.* The hull/⟨r,s⟩ is O/2, generated by s/2. A glue vector, normalised, is
g = α s/2 + p/2 with α ∈ 𝔽₄^×. Then 4g² = 2α²a + p² ∈ 4O, and det L = a²p²/4.

- If 2 ∤ a, then v₂(p²) = 1 exactly, so v₂(det L) = −1: impossible.
- If 2 | a, then 4 | p², so 4 | det L: not SSF.

So there is no glue, det L = a²p², and a is a unit, which can be normalised to 1.
The lattice [[1,−1],[−1,2]] is unimodular, with orthogonal basis r, r+s of norms
1, 1. ∎

**Consequence.** Every SSF reflective lattice over ℤ[φ] with a π/4 corner belongs to
the diagonal family ⟨−d, 1, 1⟩ with d = −det L.

### 4.4 G₂ corners

There is no glue, and b = 1. The binary lattice [[2,−3],[−3,6]] ≅ A₂ (basis r, r+s
has Gram [[2,−1],[−1,2]]). So L = A₂ ⊥ ⟨p²⟩ with 3 ∤ p², and det L = 3p².

### 4.5 H₂ corners (new)

Let v_r = (2r + φs)/π. Then r·v_r = 1, s·v_r = 0 and v_r² = 2/π. A glue vector is
g = α v_r + p/π with α ∈ 𝔽₅^×, and

  g² = (2α² + det L)/π, with p² = π·det L.

So:

- **Glued:** possible if and only if det L ≡ −2α² (mod π). The values −2α² mod 5
  are {2, 3}, the non-residues. So H₂ glue exists exactly when det L is a quadratic
  non-residue mod π. Then α is determined up to sign, and exactly one of
  g± = ±α v_r + p/π lies in L.
- **Unglued:** the corner is **not** of type H₂. In L = H ⊥ Op, the vector r′ that
  completes the I₂(10) basis (norm 2ρ, see §4.6) is a root, so the roots orthogonal
  to p form an I₂(10) system: this is the I₂(10) corner of §4.6. With glue, r′ is
  no longer a root. (Checked by `corner_check.py`: 10 mirror lines unglued, 5
  glued.)

**Conclusion (the analogue of Mark's Lemma 4).** At an H₂ corner of an SSF
lattice, r² = s² = 2 up to unit squares, there is always glue, p² = π·det L, and
det L is a quadratic non-residue mod π.

*Check.* With det L = −3 and α = 2, the basis (r, s, g) has the integral Gram
matrix [[2,−φ,2],[−φ,2,0],[2,0,2+φ]] with determinant −3; with α = 1, g² is not
integral (verified). That example is not admissible, since it is negative at σ;
it only tests the glue algebra.

Whether the analogues of Mark's Lemmas 6–7 (glue sign constant along a boundary
component) hold for H₂ glue is to be proved.

### 4.6 I₂(10) corners (new)

There is no glue, and b = 1. With basis s, r+s the I₂(10) lattice has Gram
[[2,−φ],[−φ,2]], so it is the same binary lattice H as at H₂ corners (verified). For
I₂(10) roots, the asymmetric norms 2 and 2ρ make the reflective hull trivial. So
L = H ⊥ ⟨p²⟩ with det L = π·p² (up to units) and π ∤ p². Conversely, every lattice
H ⊥ ⟨p²⟩ has an I₂(10) corner at p (§4.5). So the I₂(10) corners are exactly the
unglued H-corners, just as G₂ corners are the unglued A₂-corners.

### 4.7 Right-angled corners (A₁²)

The hull/⟨r,s⟩ is (O/2)², with the norms constrained only by Corollary 2.2. These
are handled generically by Lemma 8 and the root-configuration lemmas, as in Mark.

---

## 5. The thin-part lemma and the boxes

**Geometry (field-independent).** Every finite-sided compact hyperbolic polygon has
a short edge T in one of three configurations (Allcock, Thm 1; Mark §3.1):

1. a short edge with neighbours R, R′ (R ⊥̸ T);
2. a short pair (S, T), in polygons with at least 5 edges;
3. a close pair (S, S′), in polygons with at least 6 edges.

Over ℚ(√5) every admissible rank-3 lattice is anisotropic, so all chambers are
compact. Set μ = −r̂·t̂, μ′ = −r̂′·t̂, λ = −r̂·r̂′ and

  K = 1 + μ + μ′ + 2√((1+μ)(1+μ′)).

The bounds are:

| Configuration | Ranges | Bound on λ |
|---|---|---|
| short edge | 0 < μ < 1, 0 ≤ μ′ < 1 | λ < K < 7 |
| short pair | 1 < μ < 3, 0 ≤ μ′ < 1 | λ < K < 5 + 4√2 |
| close pair | 1 < μ, μ′ < 3 | λ < K < 15 |

These constants are pure geometry. Substituting the extreme values of μ and μ′
gives exactly 7, 5 + 4√2 = 1+3+1+2√8, and 15. So **5 + 4√2 is not specific to
ℚ(√2)**. (One extraction of Mark's arXiv version wrote K with 2√(1+μ′); the
thesis's product form is the one that reproduces all three constants.)

**Lemma 8 (field-generic).** If −â·b̂ = k > 0, then the Gram matrix of a, b is a
K-multiple of [[2u, −uv], [−uv, 2v]] with u, v totally positive in O, uv = 4k² and
σ(uv) < 4. Under (U2), good factorisations of z modulo unit squares correspond to
the ideal divisors of (z).

**The boxes over ℤ[φ]** (computed exactly; all z ∈ O with σ(z) ∈ (0,4)):

| Box | Use | #z | #factorisation classes |
|---|---|---|---|
| 0 < z < 4 | (A,B), (A′,B′) for short edges; (A′,B′) generally | 7 | 11 |
| 4 < z < 36 | (A,B) for short and close pairs | 57 | 147 |
| 0 < z < 196 | (C,C′) for short edges (4K² < 196) | 350 | 1126 |
| 4 < z < 455 | (C,C′) for short pairs (4K² < 4(57+40√2) ≈ 454.5; 455 is a safe enclosure) | 807 | 2902 |
| 4 < z < 900 | (C,C′) for close pairs | 1603 | 6217 |

The seven elements of the first box are:
φ⁻² ≈ 0.382; 1; π ≈ 1.382; 2; φ² ≈ 2.618; 3; ρ ≈ 3.618.
Each class count is the number of ideal divisors.

**Lemmas 9–11** (the root-configuration lemmas, giving the 3×3, 4×4 and 5×5 Gram
matrices). Their derivations are field-generic algebra with o = O. The only
field-specific inputs are:

- the boxes above;
- the factorisation classes;
- the square-unit compatibility condition (Mark's (3.12)/(14)), which under (U2)
  reads exactly as for ℤ[√2];
- the integrality and divisibility conditions on N, N′, k, k′ and γ in O.

*(Check against Mark.)* I could not recover the explicit matrices (3.7), (3.8),
(3.14), (3.15) and (3.19) verbatim. Step 2 should re-derive them from Allcock's
Lemmas 4–5 and Mark §3.3, and test them over ℤ[√2] by reproducing her Table 1
counts (282, 1736, 5777, 88836, 97526 root configurations).

## 6. Field bound

Mark's Theorem 2 (no reflective lattices over ℚ(√D) for D > 27935, …) obviously
allows D = 5. Her short-pair and close-pair bound (D > 1296, …) is also satisfied,
and the 4 < z < 36 box is non-empty (57 elements). So all three configurations
occur in principle over ℤ[φ].

## 7. The triangle case

Here the CC′ ∈ (0,4) case means R and R′ meet, so P is a triangle. Labels must lie in
{2, 3, 4, 5, 6, 10}. The Vinberg field is ℚ(cos²(π/p), cos²(π/q), cos²(π/r),
cos(π/p)cos(π/q)cos(π/r)). The triangle is arithmetic over ℚ(√5) exactly when this
field is ℚ(√5) and σ(det G) > 0 (the 2×2 minors are automatically positive at σ).

Computed exactly (15 compact triangles have Vinberg field ℚ(√5)):

- **Arithmetic (12):** (2,3,10), (2,4,5), (2,4,10), (2,5,5), (2,5,6), (2,5,10),
  (2,10,10), (3,3,5), (3,5,5), (4,4,5), (5,5,5), (5,10,10).
- **Non-arithmetic (3):** (2,6,10), (3,10,10), (5,6,6).

The twelve agree with the ℚ(√5) entries of Takeuchi's list as I recall it. They
fall into his three commensurability classes:

- {(2,3,10), (2,5,5), (3,3,5), (5,5,5)};
- {(2,5,6), (3,5,5)};
- {(2,4,5), (2,4,10), (2,5,10), (2,10,10), (4,4,5), (5,10,10)}.

Confirm against Takeuchi 1977. For each triangle, the next step is to list the SSF
lattices it realises and keep the maximal ones (Mark found 3 maximal out of 8 over
ℚ(√2)).

## 8. Calibration data for later steps

Known reflective rank-3 lattices over ℤ[φ] that the classification must contain:

- ⟨−φ, 1, 1⟩ (Bugaenko);
- ⟨−(5+3√5)/2, 1, 1⟩ (≡ ⟨−√5, 1, 1⟩ up to unit squares; Guglielmetti);
- ⟨−(3+2√5), 1, 1⟩ and ⟨−(−3+2√5), 1, 1⟩ (Mcleod thesis §3.2);
- ⟨−φ, 2+φ, 1⟩ (Guglielmetti);
- lattices realising the 12 arithmetic triangles.

By Lemma 4.3, every diagonal entry with a π/4 corner is automatically of the form
⟨−d, 1, 1⟩. This gives an independent check on the diagonal project.

## 9. Open items before Step 2

1. ~~Recover Mark's Lemma 4 hypotheses.~~ Resolved: her lemma is correct (§4.2).
   Still to do: recover or re-derive the explicit Lemma 9–11 matrices (step 2).
2. Prove the H₂ analogue of Mark's Lemmas 6–7 (glue sign constancy along a boundary
   component), which is needed for walking.
3. Refine the B₂ result: it shows every π/4-corner SSF lattice is ⟨1,1,−d⟩. Check
   whether this also prunes the root-configuration lists (any configuration
   containing a π/4 corner can be replaced by a diagonal check).
4. Check §4.1's "b is a unit" for A₁² corners, which is not covered above.
5. Confirm the triangle list against Takeuchi and find the maximal lattices.

---

## 10. Literature status of the step-1 results

| Item | Status | Where |
|---|---|---|
| Units, (U2)/(N2), good factorisations (Lemma 8) | already in the literature, stated for any real quadratic field | Mark, thesis §§2–3 |
| Root norms divide 2·det L | standard | Vinberg, Nikulin, Bugaenko; Mark §2.10 |
| Two-case root-norm lemma (2 inert) | specialisation of Mark's three cases | §2 |
| Admissible angles m ∈ {2,3,4,5,6,10} | standard | Vinberg's arithmeticity criterion; Bugaenko over ℤ[φ] |
| Norm-ratio table | routine transfer of Mark's Lemma 3 | §3 |
| Thin-part lemma and constants 7, 5+4√2, 15 | already in the literature; geometric | Allcock (Mem. AMS 220, 2012), Thm 1; Mark §3.1/§3.3 |
| Field bound covering ℚ(√5) | already in the literature | Mark, Theorem 2 |
| Box pictures for D = 5 | partly there (figures only, no enumeration) | Mark, thesis Fig. 3.1 |
| Box counts and factorisation classes over ℤ[φ] | new, routine computation | §5, `step1_results.json` |
| A₂ corner lemmas | already there over ℤ[√2]; proofs transfer | Mark, Lemmas 4–7; Allcock over ℤ |
| G₂ = unglued A₂ | elementary; implicit in Mark and Allcock | §4.2, §4.4 |
| H = [[2,−φ],[−φ,2]] as root lattice of H₂ and I₂(10) | known as a definite lattice (the ℤ[φ] lattice of the non-crystallographic H₂ system) | quasicrystal and icosian literature (Moody–Patera; Conway–Sloane) |
| H₂ / I₂(10) corner lemmas for hyperbolic lattices | new, as far as I can find | §4.5, §4.6 |
| π/4 corner ⇒ L ≅ ⟨1, 1, det L⟩ | new as stated, as far as I can find; the proof also works over ℤ, so it may be implicit in Nikulin's or Allcock's tables | §4.3 |
| The 12 arithmetic triangles over ℚ(√5) | re-derivation of part of Takeuchi's classification | Takeuchi, J. Math. Soc. Japan 29 (1977) |
