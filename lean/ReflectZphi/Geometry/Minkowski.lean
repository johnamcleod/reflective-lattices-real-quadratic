import Mathlib

/-!
# Minkowski space ℝ^{2,1}: the inequalities behind the polygon certificate

`mink x y = x₀y₀ + x₁y₁ − x₂y₂` (lean-plan.md §8, steps B1–B3).

* `rev_cs`: reverse Cauchy–Schwarz. If `x` is timelike, then `(x·y)² ≥ (x·x)(y·y)`.
* `perp_nonneg`: vectors orthogonal to a timelike vector are spacelike or zero.
* `cs_perp`: Cauchy–Schwarz on `x^⊥`.
* `majorant_bound` (B2): if `x` is timelike and `r·x = 0`, then
  `−(x·x)(r·v)² ≤ (r·r)((v·x)² − (x·x)(v·v))`.
-/

namespace ReflectZphi.Minkowski

/-- The Minkowski form of signature `(2,1)`. -/
def mink (x y : Fin 3 → ℝ) : ℝ := x 0 * y 0 + x 1 * y 1 - x 2 * y 2

lemma mink_comm (x y : Fin 3 → ℝ) : mink x y = mink y x := by
  unfold mink; ring

/-- Reverse Cauchy–Schwarz: for timelike `x` and any `y`, `(x·x)(y·y) ≤ (x·y)²`. -/
theorem rev_cs (x y : Fin 3 → ℝ) (hx : mink x x < 0) :
    mink x x * mink y y ≤ mink x y ^ 2 := by
  unfold mink at *
  -- with a = (x₀,x₁), c = x₂·(y₀,y₁) − y₂·a:
  --   x₂²·((x·y)² − (x·x)(y·y)) = x₂²|c|² − cross(a,c)² ≥ |a|²|c|² − cross(a,c)² = (a·c)²
  set c0 := x 2 * y 0 - y 2 * x 0
  set c1 := x 2 * y 1 - y 2 * x 1
  have hx2 : 0 < x 2 ^ 2 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have key : x 2 ^ 2 * ((x 0 * y 0 + x 1 * y 1 - x 2 * y 2) ^ 2 -
      (x 0 * x 0 + x 1 * x 1 - x 2 * x 2) * (y 0 * y 0 + y 1 * y 1 - y 2 * y 2)) =
      x 2 ^ 2 * (c0 ^ 2 + c1 ^ 2) - (x 0 * c1 - x 1 * c0) ^ 2 := by
    simp only [c0, c1]; ring
  have h2 : 0 ≤ x 2 ^ 2 * (c0 ^ 2 + c1 ^ 2) - (x 0 * c1 - x 1 * c0) ^ 2 := by
    have hid : (x 0 * c1 - x 1 * c0) ^ 2 + (x 0 * c0 + x 1 * c1) ^ 2 =
        (x 0 ^ 2 + x 1 ^ 2) * (c0 ^ 2 + c1 ^ 2) := by ring
    have hle : (x 0 ^ 2 + x 1 ^ 2) * (c0 ^ 2 + c1 ^ 2) ≤ x 2 ^ 2 * (c0 ^ 2 + c1 ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith [sq_nonneg (x 0 * c0 + x 1 * c1)]
  have : 0 ≤ (x 0 * y 0 + x 1 * y 1 - x 2 * y 2) ^ 2 -
      (x 0 * x 0 + x 1 * x 1 - x 2 * x 2) * (y 0 * y 0 + y 1 * y 1 - y 2 * y 2) := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg hx2 h
    linarith
  linarith

/-- A vector orthogonal to a timelike vector has nonnegative norm. -/
theorem perp_nonneg {x y : Fin 3 → ℝ} (hx : mink x x < 0) (h : mink x y = 0) :
    0 ≤ mink y y := by
  have := rev_cs x y hx
  rw [h] at this
  by_contra hy
  push Not at hy
  nlinarith

/-- Cauchy–Schwarz on the orthogonal complement of a timelike vector. -/
theorem cs_perp {x u w : Fin 3 → ℝ} (hx : mink x x < 0) (hu : mink x u = 0)
    (hw : mink x w = 0) : mink u w ^ 2 ≤ mink u u * mink w w := by
  -- the quadratic t ↦ (t u + s w)·(t u + s w) is ≥ 0 on x^⊥
  have hq : ∀ t s : ℝ, 0 ≤ t ^ 2 * mink u u + 2 * t * s * mink u w + s ^ 2 * mink w w := by
    intro t s
    have hperp : mink x (fun i => t * u i + s * w i) = 0 := by
      unfold mink at *; linear_combination t * hu + s * hw
    have := perp_nonneg hx hperp
    unfold mink at this ⊢; nlinarith [this]
  have huu : 0 ≤ mink u u := by simpa using hq 1 0
  have hww : 0 ≤ mink w w := by simpa using hq 0 1
  rcases eq_or_lt_of_le hww with h0 | hpos
  · -- w·w = 0: then u·w = 0, else t = 1, s = −(u·u + 1)/(u·w) makes the quadratic negative
    rw [← h0, mul_zero]
    by_contra hc
    push Not at hc
    have hc0 : mink u w ≠ 0 := by
      intro h; rw [h] at hc; norm_num at hc
    have h := hq 1 (-(mink u u + 1) / mink u w)
    rw [← h0] at h
    have : 2 * 1 * (-(mink u u + 1) / mink u w) * mink u w = -2 * (mink u u + 1) := by
      field_simp
    nlinarith
  · have h := hq (mink w w) (-(mink u w))
    nlinarith

/-- **Majorant bound (B2).** If `x` is timelike and `r·x = 0`, then for every `v`,
`−(x·x)(r·v)² ≤ (r·r)((v·x)² − (x·x)(v·v))`. -/
theorem majorant_bound {x r : Fin 3 → ℝ} (v : Fin 3 → ℝ) (hx : mink x x < 0)
    (hr : mink x r = 0) :
    -(mink x x) * mink r v ^ 2 ≤ mink r r * (mink v x ^ 2 - mink x x * mink v v) := by
  -- w = (x·x) v − (v·x) x is orthogonal to x
  set w : Fin 3 → ℝ := fun i => mink x x * v i - mink v x * x i with hw_def
  have hw : mink x w = 0 := by
    simp only [hw_def, mink]; ring
  have hcs := cs_perp hx hr hw
  have hrw : mink r w = mink x x * mink r v := by
    simp only [hw_def, mink] at hr ⊢
    linear_combination (-(v 0 * x 0 + v 1 * x 1 - v 2 * x 2)) * hr
  have hww : mink w w = mink x x * (mink x x * mink v v - mink v x ^ 2) := by
    simp only [hw_def, mink]; ring
  rw [hrw, hww] at hcs
  -- divide (x·x)² (r·v)² ≤ (r·r)(x·x)((x·x)(v·v) − (v·x)²) by x·x < 0
  have hneg : mink x x < 0 := hx
  nlinarith [hcs]

/-! ### B3: the future cone, the reverse triangle inequality, convexity of balls -/

/-- Future timelike: `x₂ > 0` and `x·x < 0`. -/
def Future (x : Fin 3 → ℝ) : Prop := 0 < x 2 ∧ mink x x < 0

/-- Future timelike or zero: closed under sums and nonnegative multiples. -/
def FutureOrZero (x : Fin 3 → ℝ) : Prop := x = 0 ∨ Future x

/-- Proper time `τ(x) = √(−x·x)`. -/
noncomputable def tau (x : Fin 3 → ℝ) : ℝ := Real.sqrt (-(mink x x))

lemma mink_neg_of_future {x y : Fin 3 → ℝ} (hx : Future x) (hy : Future y) :
    mink x y < 0 := by
  obtain ⟨hx2, hxx⟩ := hx
  obtain ⟨hy2, hyy⟩ := hy
  unfold mink at *
  have hcs : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have hlt : (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) < (x 2 * y 2) ^ 2 := by
    have h1 : x 0 ^ 2 + x 1 ^ 2 < x 2 ^ 2 := by nlinarith
    have h2 : y 0 ^ 2 + y 1 ^ 2 < y 2 ^ 2 := by nlinarith
    calc (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) ≤ (x 0 ^ 2 + x 1 ^ 2) * y 2 ^ 2 :=
          mul_le_mul_of_nonneg_left h2.le (by positivity)
      _ < x 2 ^ 2 * y 2 ^ 2 := by
          apply mul_lt_mul_of_pos_right h1; positivity
      _ = (x 2 * y 2) ^ 2 := by ring
  have hpos : 0 < x 2 * y 2 := mul_pos hx2 hy2
  by_contra h
  push Not at h
  have h' : x 2 * y 2 ≤ x 0 * y 0 + x 1 * y 1 := by linarith
  nlinarith

lemma future_add {x y : Fin 3 → ℝ} (hx : Future x) (hy : Future y) : Future (x + y) := by
  have hxy := mink_neg_of_future hx hy
  obtain ⟨hx2, hxx⟩ := hx
  obtain ⟨hy2, hyy⟩ := hy
  refine ⟨by simp only [Pi.add_apply]; linarith, ?_⟩
  unfold mink at *
  simp only [Pi.add_apply]
  nlinarith

lemma future_smul {x : Fin 3 → ℝ} {c : ℝ} (hc : 0 < c) (hx : Future x) :
    Future (c • x) := by
  obtain ⟨hx2, hxx⟩ := hx
  refine ⟨by simp only [Pi.smul_apply, smul_eq_mul]; positivity, ?_⟩
  unfold mink at *
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_pos hc hc]

lemma futureOrZero_add {x y : Fin 3 → ℝ} (hx : FutureOrZero x) (hy : FutureOrZero y) :
    FutureOrZero (x + y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  exact Or.inr (future_add hx hy)

lemma futureOrZero_smul {x : Fin 3 → ℝ} {c : ℝ} (hc : 0 ≤ c) (hx : FutureOrZero x) :
    FutureOrZero (c • x) := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · left; simp
  rcases hx with rfl | hx
  · left; simp
  exact Or.inr (future_smul hc hx)

lemma mink_self_nonpos {x : Fin 3 → ℝ} (hx : FutureOrZero x) : mink x x ≤ 0 := by
  rcases hx with rfl | hx
  · simp [mink]
  exact hx.2.le

/-- Reverse triangle inequality: `τ(x) + τ(y) ≤ τ(x + y)` on the closed future cone. -/
theorem tau_add {x y : Fin 3 → ℝ} (hx : FutureOrZero x) (hy : FutureOrZero y) :
    tau x + tau y ≤ tau (x + y) := by
  rcases hx with rfl | hx
  · simp [tau, mink]
  rcases hy with rfl | hy
  · simp [tau, mink]
  have hxy := mink_neg_of_future hx hy
  have hcs := rev_cs x y hx.2
  have hexp : mink (x + y) (x + y) = mink x x + 2 * mink x y + mink y y := by
    unfold mink; simp only [Pi.add_apply]; ring
  unfold tau
  rw [hexp]
  have ha : 0 ≤ -mink x x := by linarith [hx.2]
  have hb : 0 ≤ -mink y y := by linarith [hy.2]
  -- (√a + √b)² = a + b + 2√(ab) ≤ a + b − 2 x·y, since √(ab) ≤ −x·y
  have hab : Real.sqrt (-mink x x) * Real.sqrt (-mink y y) ≤ -mink x y := by
    rw [← Real.sqrt_mul ha]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    nlinarith
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith

lemma tau_smul {x : Fin 3 → ℝ} {c : ℝ} (hc : 0 ≤ c) : tau (c • x) = c * tau x := by
  unfold tau mink
  simp only [Pi.smul_apply, smul_eq_mul]
  have : -(c * x 0 * (c * x 0) + c * x 1 * (c * x 1) - c * x 2 * (c * x 2)) =
      c ^ 2 * -(x 0 * x 0 + x 1 * x 1 - x 2 * x 2) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

lemma tau_nonneg (x : Fin 3 → ℝ) : 0 ≤ tau x := Real.sqrt_nonneg _

/-- Superadditivity over a finite nonnegative combination. -/
theorem tau_sum {ι : Type*} (s : Finset ι) (l : ι → ℝ) (p : ι → Fin 3 → ℝ)
    (hl : ∀ i ∈ s, 0 ≤ l i) (hp : ∀ i ∈ s, FutureOrZero (p i)) :
    FutureOrZero (∑ i ∈ s, l i • p i) ∧
      ∑ i ∈ s, l i * tau (p i) ≤ tau (∑ i ∈ s, l i • p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Or.inl (by simp), by simp [tau, mink]⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hl' : ∀ i ∈ s, 0 ≤ l i := fun i hi => hl i (Finset.mem_insert_of_mem hi)
    have hp' : ∀ i ∈ s, FutureOrZero (p i) := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    obtain ⟨hF, hT⟩ := ih hl' hp'
    have hlj := hl j (Finset.mem_insert_self j s)
    have hpj := futureOrZero_smul hlj (hp j (Finset.mem_insert_self j s))
    refine ⟨futureOrZero_add hpj hF, ?_⟩
    have := tau_add hpj hF
    rw [tau_smul hlj] at this
    linarith

/-- **Balls are convex (B3).** If every `p i` satisfies the cosh-bound
`−(v·p) ≤ C τ(v) τ(p)`, then so does every nonnegative combination of them. -/
theorem ball_convex {ι : Type*} (s : Finset ι) (l : ι → ℝ) (p : ι → Fin 3 → ℝ)
    (v : Fin 3 → ℝ) (C : ℝ) (hC : 0 ≤ C) (hl : ∀ i ∈ s, 0 ≤ l i)
    (hp : ∀ i ∈ s, FutureOrZero (p i))
    (hb : ∀ i ∈ s, -mink v (p i) ≤ C * tau v * tau (p i)) :
    -mink v (∑ i ∈ s, l i • p i) ≤ C * tau v * tau (∑ i ∈ s, l i • p i) := by
  have hlin : -mink v (∑ i ∈ s, l i • p i) = ∑ i ∈ s, l i * -mink v (p i) := by
    unfold mink
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hlin]
  have hCv : 0 ≤ C * tau v := mul_nonneg hC (tau_nonneg v)
  calc ∑ i ∈ s, l i * -mink v (p i) ≤ ∑ i ∈ s, l i * (C * tau v * tau (p i)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hb i hi) (hl i hi)
    _ = C * tau v * ∑ i ∈ s, l i * tau (p i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ C * tau v * tau (∑ i ∈ s, l i • p i) :=
        mul_le_mul_of_nonneg_left (tau_sum s l p hl hp).2 hCv

end ReflectZphi.Minkowski
