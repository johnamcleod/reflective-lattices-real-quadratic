import ReflectZphi.Ring.Embed

/-!
# The ring `ℤ[ω]`, `ω = (1 + √13)/2` (profile `(a, b) = (3, 1)`)

`ZSqrt13 = QuadraticAlgebra ℤ 3 1`, with `ω² = 3 + ω`. Kernel-checked facts:
- the ring is a domain and a PID, norm-Euclidean via the sharp box bound `13/16`
  (`boxBound_three_one`; the crude bound used for `ℤ[φ]` and `ℤ[√2]` fails here);
- `N(1 + ω) = -1`, so (N2) holds;
- `2` is inert (prime);
- `3 = -ω·(1 - ω)` splits, and `13 = (2ω - 1)²` ramifies.
-/

namespace ReflectZphi

open QuadraticAlgebra

abbrev ZSqrt13 := QuadraticAlgebra ℤ 3 1

local notation "Nm" => QuadraticAlgebra.norm

/-- `ω = (1 + √13)/2`. -/
def omega13 : ZSqrt13 := ⟨0, 1⟩

/-- The fundamental unit `(3 + √13)/2 = 1 + ω`. -/
def eps13 : ZSqrt13 := ⟨1, 1⟩

instance fact_discr_zsqrt13 : Fact (¬ IsSquare (discr (3 : ℤ) 1)) := ⟨by
  rw [discr_def]
  rintro ⟨r, hr⟩
  have h : r * r = 13 := by norm_num at hr; linarith
  have h3 : -4 < r ∧ r < 4 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := h3
  interval_cases r <;> omega⟩

theorem zsqrt13_isPID : IsPrincipalIdealRing ZSqrt13 :=
  isPrincipalIdealRing_of_boxBound boxBound_three_one

theorem omega13_mul_self : omega13 * omega13 = 3 + omega13 := by decide

theorem norm_eps13 : Nm eps13 = -1 := by decide

theorem isUnit_eps13 : IsUnit eps13 :=
  isUnit_iff_norm_isUnit.mpr (by rw [norm_eps13]; exact isUnit_one.neg)

/-- `3 = -ω (1 - ω)`: 3 splits, with `N ω = -3`. -/
theorem three_eq : (3 : ZSqrt13) = -(omega13 * (1 - omega13)) := by decide

theorem norm_omega13 : Nm omega13 = -3 := by decide

/-- `13 = (2ω - 1)²`: 13 ramifies. -/
theorem thirteen_eq : (13 : ZSqrt13) = (2 * omega13 - 1) ^ 2 := by decide

/-- Norms are `4N = (2x + y)² - 13y²`, so modulo 13 they are `4⁻¹` times a square:
never `±2`. -/
theorem norm_mod_thirteen (z : ZSqrt13) :
    ((Nm z : ℤ) : ZMod 13) ≠ 2 ∧ ((Nm z : ℤ) : ZMod 13) ≠ -2 := by
  rw [norm_def]
  push_cast
  generalize ((z.re : ℤ) : ZMod 13) = x
  generalize ((z.im : ℤ) : ZMod 13) = y
  revert x y
  decide

theorem norm_ne_two (z : ZSqrt13) : Nm z ≠ 2 ∧ Nm z ≠ -2 := by
  obtain ⟨h2, h2'⟩ := norm_mod_thirteen z
  refine ⟨?_, ?_⟩ <;> intro h <;> rw [h] at h2 h2' <;>
    first | exact h2 (by decide) | exact h2' (by decide)

private theorem unit_of_norm_mul_two (x y : ZSqrt13)
    (h : Nm x * Nm y = (2 : ℤ) ^ 2) : IsUnit x ∨ IsUnit y := by
  have pp : (2 : ℕ).Prime := by norm_num
  have hn := congrArg Int.natAbs h
  rw [Int.natAbs_mul, Int.natAbs_pow] at hn
  have hdx : (Nm x).natAbs ∣ 2 ^ 2 := ⟨_, hn.symm⟩
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow pp).mp hdx
  rw [hix] at hn
  rw [isUnit_iff_norm_isUnit, isUnit_iff_norm_isUnit, Int.isUnit_iff_natAbs_eq,
    Int.isUnit_iff_natAbs_eq]
  interval_cases i
  · left; simpa using hix
  · exfalso
    have hx := norm_ne_two x
    simp only [pow_one] at hix
    omega
  · right
    have h0 : 0 < 2 ^ 2 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left h0 (hn.trans (mul_one _).symm)

/-- 2 is inert: prime in `ℤ[ω]`. -/
theorem prime_two_13 : Prime (2 : ZSqrt13) := by
  have := zsqrt13_isPID
  have hirr : Irreducible (2 : ZSqrt13) := by
    constructor
    · rw [isUnit_iff_norm_isUnit, show (2 : ZSqrt13) = ((2 : ℕ) : ZSqrt13) by norm_num,
        QuadraticAlgebra.norm_natCast, Int.isUnit_iff]
      norm_num
    · intro x y hxy
      have := congrArg Nm hxy
      rw [show (2 : ZSqrt13) = ((2 : ℕ) : ZSqrt13) by norm_num,
        QuadraticAlgebra.norm_natCast, map_mul] at this
      exact unit_of_norm_mul_two x y (by rw [← this]; norm_num)
  exact hirr.prime

end ReflectZphi
