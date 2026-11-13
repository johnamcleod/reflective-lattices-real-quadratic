import ReflectZphi.Ring.Embed

/-!
# The ring `ℤ[φ]` (profile `(a, b) = (1, 1)`)

`ZPhi = QuadraticAlgebra ℤ 1 1`, ω = φ with φ² = 1 + φ. Kernel-checked facts used by the
paper (Section 9): domain, PID (norm-Euclidean), the two real embeddings
(φ ↦ golden ratio / its conjugate), `N φ = -1`, `5 = φ² π²` with `π = 3 - φ`, and the
primes 2 and 3 are inert (prime in `ℤ[φ]`).
-/

namespace ReflectZphi

open QuadraticAlgebra

abbrev ZPhi := QuadraticAlgebra ℤ 1 1

local notation "Nm" => QuadraticAlgebra.norm

/-- φ. -/
def phi : ZPhi := ⟨0, 1⟩

/-- The ramified prime `π = 3 - φ` above 5. -/
def piZ : ZPhi := ⟨3, -1⟩

instance fact_discr_zphi : Fact (¬ IsSquare (discr (1 : ℤ) 1)) := ⟨by
  rw [discr_def]
  rintro ⟨r, hr⟩
  have h : r * r = 5 := by norm_num at hr; linarith
  have h3 : -3 < r ∧ r < 3 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := h3
  interval_cases r <;> omega⟩

theorem zphi_isPID : IsPrincipalIdealRing ZPhi :=
  isPrincipalIdealRing (by norm_num)

theorem phi_mul_phi : phi * phi = 1 + phi := by decide

theorem norm_phi : Nm phi = -1 := by decide

theorem isUnit_phi : IsUnit phi :=
  isUnit_iff_norm_isUnit.mpr (by rw [norm_phi]; exact isUnit_one.neg)

theorem five_eq : (5 : ZPhi) = phi ^ 2 * piZ ^ 2 := by decide

theorem norm_piZ : Nm piZ = 5 := by decide

/-- The embedding `ι₁` (φ ↦ golden ratio). -/
noncomputable def iota1 : ZPhi →+* ℝ := emb 1 1 1 (by norm_num) (by norm_num)
/-- The embedding `ι₂ = σ` (φ ↦ conjugate golden ratio). -/
noncomputable def iota2 : ZPhi →+* ℝ := emb 1 1 (-1) (by norm_num) (by norm_num)

theorem iota1_phi : iota1 phi = Real.goldenRatio := by
  simp [iota1, emb_apply, phi, root, Real.goldenRatio]; norm_num

theorem iota2_phi : iota2 phi = Real.goldenConj := by
  simp [iota2, emb_apply, phi, root, Real.goldenConj]; norm_num; ring

/-- Norms are `0, ±1 mod 5`. -/
theorem norm_mod_five (z : ZPhi) : ((Nm z : ℤ) : ZMod 5) ≠ 2 ∧ ((Nm z : ℤ) : ZMod 5) ≠ 3 := by
  rw [norm_def]
  push_cast
  generalize ((z.re : ℤ) : ZMod 5) = x
  generalize ((z.im : ℤ) : ZMod 5) = y
  revert x y
  decide

theorem norm_ne_two_three (z : ZPhi) : Nm z ≠ 2 ∧ Nm z ≠ -2 ∧ Nm z ≠ 3 ∧ Nm z ≠ -3 := by
  obtain ⟨h2, h3⟩ := norm_mod_five z
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at h2 h3 <;>
    first | exact h2 (by decide) | exact h3 (by decide)

/-- If `N x · N y = p²` with `p ∈ {2,3}` then `x` or `y` is a unit. -/
private theorem unit_of_norm_mul (p : ℕ) (hp : p = 2 ∨ p = 3) (x y : ZPhi)
    (h : Nm x * Nm y = (p : ℤ) ^ 2) : IsUnit x ∨ IsUnit y := by
  have pp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hn := congrArg Int.natAbs h
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hn
  have hdx : (Nm x).natAbs ∣ p ^ 2 := ⟨_, hn.symm⟩
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow pp).mp hdx
  rw [hix] at hn
  rw [isUnit_iff_norm_isUnit, isUnit_iff_norm_isUnit, Int.isUnit_iff_natAbs_eq,
    Int.isUnit_iff_natAbs_eq]
  interval_cases i
  · left; simpa using hix
  · exfalso
    have hx := norm_ne_two_three x
    simp only [pow_one] at hix
    rcases hp with rfl | rfl <;> omega
  · right
    have h0 : 0 < p ^ 2 := pow_pos pp.pos 2
    exact Nat.eq_of_mul_eq_mul_left h0 (hn.trans (mul_one _).symm)

private theorem irreducible_of (p : ℕ) (hp : p = 2 ∨ p = 3) : Irreducible (p : ZPhi) := by
  constructor
  · rw [isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_natCast, Int.isUnit_iff]
    rcases hp with rfl | rfl <;> norm_num
  · intro x y hxy
    have := congrArg Nm hxy
    rw [QuadraticAlgebra.norm_natCast, map_mul] at this
    exact unit_of_norm_mul p hp x y this.symm

/-- 2 is inert: prime in `ℤ[φ]`. -/
theorem prime_two : Prime (2 : ZPhi) := by
  have := zphi_isPID
  have := irreducible_of 2 (Or.inl rfl)
  exact_mod_cast this.prime

/-- 3 is inert: prime in `ℤ[φ]`. -/
theorem prime_three : Prime (3 : ZPhi) := by
  have := zphi_isPID
  have := irreducible_of 3 (Or.inr rfl)
  exact_mod_cast this.prime

end ReflectZphi
