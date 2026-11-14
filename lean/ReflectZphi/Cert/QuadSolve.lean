import ReflectZphi.Cert.Enum
import ReflectZphi.Ring.Euclid
import ReflectZphi.Lattice.Basic

/-!
# Solving `A t² + 2B t + C = 0` in `O = ℤ[ω]` exactly (kernel-computable)

`solveQuad A B C` returns a flag and a list of candidates. If the flag is `true`, every
solution `t ∈ O` is in the list (`solveQuad_sound`). The flag records that the integer
square roots computed by Newton's iteration passed the check `r² ≤ n < (r+1)²`, so the
iteration itself needs no proof.

Method: `s = A t + B` satisfies `s² = Δ = B² − AC`. For `s² = Δ`, the norm `n = N s`
has `n² = N Δ`, the trace `t = Tr s` has `t² = Tr Δ + 2n`, and `t s = Δ + n`. So `s` is
`(Δ + n)/t` when `t ≠ 0`; when `t = 0`, `Δ = −n ∈ ℤ` and `s = (−by/2) + yω` with
`d y² = 4Δ`. Then `t = (s − B)/A` by exact division.
-/

namespace ReflectZphi.QuadSolve

open QuadraticAlgebra ReflectZphi.Enum ReflectZphi.Lattice

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-! ### Checked integer square roots -/

/-- `isqrt n` passes the floor check. -/
def sqrtOK (n : ℕ) : Bool :=
  isqrt n * isqrt n ≤ n && n < (isqrt n + 1) * (isqrt n + 1)

lemma eq_isqrt_of_sqrtOK {n : ℕ} (h : sqrtOK n = true) {k : ℕ} (hk : k * k = n) :
    k = isqrt n := by
  simp only [sqrtOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rcases lt_trichotomy k (isqrt n) with hlt | heq | hgt
  · exfalso
    have h3 : (k + 1) * (k + 1) ≤ isqrt n * isqrt n := Nat.mul_le_mul hlt hlt
    have h4 : k * k < (k + 1) * (k + 1) := by nlinarith
    omega
  · exact heq
  · exfalso
    have : (isqrt n + 1) * (isqrt n + 1) ≤ k * k := Nat.mul_le_mul hgt hgt
    omega

/-- The candidate square roots `±r` of an integer `n` (empty unless `n` is a square), and
whether the check passed. -/
def sqrtsZ (n : ℤ) : Bool × List ℤ :=
  if n < 0 then (true, []) else
  let r : ℤ := (isqrt n.toNat : ℕ)
  (sqrtOK n.toNat, if r * r = n then [r, -r] else [])

lemma mem_sqrtsZ {n : ℤ} (hok : (sqrtsZ n).1 = true) {k : ℤ} (hk : k * k = n) :
    k ∈ (sqrtsZ n).2 := by
  have hn : 0 ≤ n := by rw [← hk]; exact mul_self_nonneg k
  simp only [sqrtsZ, not_lt.mpr hn, if_false] at hok ⊢
  have hkk : k.natAbs * k.natAbs = n.toNat := by
    have : ((k.natAbs * k.natAbs : ℕ) : ℤ) = n := by
      push_cast; rw [abs_mul_abs_self]; exact hk
    omega
  have he := eq_isqrt_of_sqrtOK hok hkk
  have hrk : ((isqrt n.toNat : ℕ) : ℤ) = |k| := by rw [← he]; simp
  rw [hrk]
  have hr : |k| * |k| = n := by rw [abs_mul_abs_self]; exact hk
  rw [if_pos hr]
  rcases abs_choice k with h | h
  · rw [h]; simp
  · rw [h]; simp

/-! ### Square roots in `O` -/

/-- The candidates `s` for one value `n` of `N s` and `t` of `Tr s`. -/
def candFor (Δ : O a b) (n t : ℤ) : Bool × List (O a b) :=
  if t ≠ 0 then
    (true, [⟨(Δ.re + n) / t, Δ.im / t⟩])
  else
    -- `t = 0`: `d y² = 4 Δ.re`, `x = −b y/2`
    let d := b ^ 2 + 4 * a
    if d ≠ 0 ∧ (4 * Δ.re) % d = 0 then
      let ys := sqrtsZ ((4 * Δ.re) / d)
      (ys.1, ys.2.map fun y => ⟨(-b * y) / 2, y⟩)
    else (true, [])

/-- All candidate square roots of `Δ` in `O`, with the check flag. -/
def sqrtsO (Δ : O a b) : Bool × List (O a b) :=
  let ns := sqrtsZ (Nm Δ)
  let parts := ns.2.map fun n =>
    let ts := sqrtsZ (trace Δ + 2 * n)
    let cs := ts.2.map fun t => candFor Δ n t
    (ts.1 && cs.all (·.1), cs.flatMap (·.2))
  (ns.1 && parts.all (·.1), parts.flatMap (·.2))

lemma sq_re (s : O a b) : (s * s).re = s.re * s.re + a * s.im * s.im := by
  simp only [re_mul]; try ring

lemma sq_im (s : O a b) : (s * s).im = 2 * s.re * s.im + b * s.im * s.im := by
  simp only [im_mul]; try ring

theorem mem_sqrtsO (hd : b ^ 2 + 4 * a ≠ 0) {Δ : O a b} (hok : (sqrtsO Δ).1 = true) {s : O a b}
    (hs : s * s = Δ) :
    s ∈ (sqrtsO Δ).2 := by
  have hre := sq_re s
  have him := sq_im s
  rw [hs] at hre him
  set n := Nm s
  set t := trace s
  have hn : n * n = Nm Δ := by rw [← hs, map_mul]
  have ht : t * t = trace Δ + 2 * n := by
    simp only [t, n, trace_def, QuadraticAlgebra.norm_def]
    rw [hre, him]; ring
  simp only [sqrtsO, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hok1, hok2⟩ := hok
  have hnm := mem_sqrtsZ hok1 hn
  have hpart := hok2 _ (List.mem_map_of_mem hnm)
  simp only [Bool.and_eq_true, List.all_eq_true] at hpart
  obtain ⟨hpt1, hpt2⟩ := hpart
  have htm := mem_sqrtsZ hpt1 ht
  have hc := hpt2 _ (List.mem_map_of_mem htm)
  simp only [sqrtsO]
  rw [List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem hnm, ?_⟩
  dsimp only
  rw [List.mem_flatMap]
  refine ⟨_, List.mem_map_of_mem htm, ?_⟩
  -- the candidate for (n, t) contains s
  have htS : t = 2 * s.re + b * s.im := rfl
  have hnS : n = s.re * s.re + b * s.re * s.im - a * s.im * s.im := rfl
  unfold candFor at hc ⊢
  by_cases ht0 : t ≠ 0
  · simp only [ht0, ne_eq, not_false_eq_true, if_true, List.mem_singleton]
    have e1 : Δ.re + n = t * s.re := by rw [hre, htS, hnS]; ring
    have e2 : Δ.im = t * s.im := by rw [him, htS]; ring
    ext
    · show s.re = (Δ.re + n) / t; rw [e1, Int.mul_ediv_cancel_left _ ht0]
    · show s.im = Δ.im / t; rw [e2, Int.mul_ediv_cancel_left _ ht0]
  · push Not at ht0
    simp only [ht0, ne_eq, not_true_eq_false, if_false] at hc ⊢
    have hx : 2 * s.re = -b * s.im := by rw [htS] at ht0; linarith
    have h4 : 4 * Δ.re = (b ^ 2 + 4 * a) * (s.im * s.im) := by
      rw [hre]; linear_combination (2 * s.re - b * s.im) * hx
    have hdiv : (4 * Δ.re) % (b ^ 2 + 4 * a) = 0 := by
      rw [h4]; exact Int.mul_emod_right _ _
    simp only [hd, hdiv, ne_eq, not_false_eq_true, and_self, if_true] at hc ⊢
    have hq : (4 * Δ.re) / (b ^ 2 + 4 * a) = s.im * s.im := by
      rw [h4, Int.mul_ediv_cancel_left _ hd]
    rw [hq] at hc ⊢
    have hy := mem_sqrtsZ hc rfl
    refine List.mem_map.mpr ⟨s.im, hy, ?_⟩
    ext
    · show (-b * s.im) / 2 = s.re; rw [← hx]; simp
    · rfl


/-! ### Exact division and the quadratic -/

/-- `x / A` if it is in `O`. -/
def divO (x A : O a b) : Option (O a b) :=
  let w := x * star A
  let N := Nm A
  if N ≠ 0 ∧ w.re % N = 0 ∧ w.im % N = 0 then some ⟨w.re / N, w.im / N⟩ else none

lemma divO_mul [IsDomain (O a b)] {A : O a b} (hA : A ≠ 0) (t : O a b) :
    divO (A * t) A = some t := by
  have hN : Nm A ≠ 0 := fun h => hA ((nm_eq_zero_iff A).mp h)
  have e : A * t * star A = t * algebraMap ℤ (O a b) (Nm A) := by
    rw [algebraMap_norm_eq_mul_star]; ring
  have hre : (A * t * star A).re = t.re * Nm A := by rw [e]; simp [re_mul]
  have him : (A * t * star A).im = t.im * Nm A := by rw [e]; simp [im_mul]
  unfold divO
  simp only [hre, him, Int.mul_emod_left, ne_eq, hN, not_false_eq_true, and_self, if_true,
    Int.mul_ediv_cancel _ hN]

/-- Candidates for `A t² + 2B t + C = 0`, with the check flag. -/
def solveQuad (A B C : O a b) : Bool × List (O a b) :=
  let r := sqrtsO (B * B - A * C)
  (r.1 && decide (A ≠ 0), r.2.filterMap fun s => divO (s - B) A)

theorem mem_solveQuad [IsDomain (O a b)] (hd : b ^ 2 + 4 * a ≠ 0) {A B C : O a b}
    (hok : (solveQuad A B C).1 = true) {t : O a b} (ht : A * t * t + 2 * B * t + C = 0) :
    t ∈ (solveQuad A B C).2 := by
  simp only [solveQuad, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok1, hA⟩ := hok
  have hs : (A * t + B) * (A * t + B) = B * B - A * C := by
    linear_combination A * ht
  have hm := mem_sqrtsO hd hok1 hs
  simp only [solveQuad]
  rw [List.mem_filterMap]
  refine ⟨A * t + B, hm, ?_⟩
  rw [add_sub_cancel_right, divO_mul hA]

end ReflectZphi.QuadSolve
