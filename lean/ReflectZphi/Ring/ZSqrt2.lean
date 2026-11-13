import ReflectZphi.Ring.Embed

/-!
# The ring `ℤ[√2]` (profile `(a, b) = (2, 0)`), used for the validation against Mark

Domain, PID (norm-Euclidean), the two real embeddings, `N(1 + √2) = -1`.
-/

namespace ReflectZphi

open QuadraticAlgebra

abbrev ZSqrt2 := QuadraticAlgebra ℤ 2 0

local notation "Nm" => QuadraticAlgebra.norm

/-- √2. -/
def sqrt2 : ZSqrt2 := ⟨0, 1⟩

/-- The fundamental unit `1 + √2`. -/
def epsSqrt2 : ZSqrt2 := ⟨1, 1⟩

instance fact_discr_zsqrt2 : Fact (¬ IsSquare (discr (2 : ℤ) 0)) := ⟨by
  rw [discr_def]
  rintro ⟨r, hr⟩
  have h : r * r = 8 := by norm_num at hr; linarith
  have h3 : -3 < r ∧ r < 3 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := h3
  interval_cases r <;> omega⟩

theorem zsqrt2_isPID : IsPrincipalIdealRing ZSqrt2 :=
  isPrincipalIdealRing (by norm_num)

theorem sqrt2_mul_sqrt2 : sqrt2 * sqrt2 = 2 := by decide

theorem norm_epsSqrt2 : Nm epsSqrt2 = -1 := by decide

theorem isUnit_epsSqrt2 : IsUnit epsSqrt2 :=
  isUnit_iff_norm_isUnit.mpr (by rw [norm_epsSqrt2]; exact isUnit_one.neg)

/-- `ι₁ : √2 ↦ √2` and `ι₂ = σ : √2 ↦ -√2` (as `(0 ± √8)/2`). -/
noncomputable def iota1S : ZSqrt2 →+* ℝ := emb 2 0 1 (by norm_num) (by norm_num)
noncomputable def iota2S : ZSqrt2 →+* ℝ := emb 2 0 (-1) (by norm_num) (by norm_num)

theorem iota1S_sqrt2 : iota1S sqrt2 = Real.sqrt 2 := by
  simp only [iota1S, emb_apply, sqrt2, root]
  have : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  norm_num [this]

end ReflectZphi
