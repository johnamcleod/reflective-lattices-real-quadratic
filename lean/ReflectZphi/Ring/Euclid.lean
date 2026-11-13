import Mathlib

/-!
# Norm-Euclidean quadratic orders (generic)

For `a b : ℤ` with `discr a b` not a square and `|a| + |b| ≤ 2`, the order
`ℤ[ω] = QuadraticAlgebra ℤ a b` (ω² = a + bω) is Euclidean for `|N|`, hence a PID.
This is the Lean side of standing hypothesis (H1) for the field profiles of the
paper: `ℤ[φ]` is `(a, b) = (1, 1)`, `ℤ[√2]` is `(2, 0)`. For `ℚ(√13)`, `(a, b) = (3, 1)`,
the crude bound fails and the sharp box bound `boxBound_three_one` is used instead;
the general statement takes the box bound `BoxBound a b` as hypothesis.
-/

namespace ReflectZphi

open QuadraticAlgebra

local notation "Nm" => QuadraticAlgebra.norm

/-- Centred division with remainder in `ℤ`. -/
theorem int_exists_near (u n : ℤ) (hn : n ≠ 0) : ∃ q : ℤ, 2 * |u - n * q| ≤ |n| := by
  have hm : 0 < |n| := abs_pos.mpr hn
  set m := |n| with hmdef
  have h2m : 0 < 2 * m := by linarith
  have hdiv := Int.mul_ediv_add_emod (2 * u + m) (2 * m)
  have hr0 := Int.emod_nonneg (2 * u + m) (ne_of_gt h2m)
  have hr1 := Int.emod_lt_of_pos (2 * u + m) h2m
  set q0 := (2 * u + m) / (2 * m)
  set r := (2 * u + m) % (2 * m)
  have hb : 2 * |u - m * q0| ≤ m := by
    have h := abs_le.mpr
      (⟨by linarith, by linarith⟩ : -m ≤ 2 * (u - m * q0) ∧ 2 * (u - m * q0) ≤ m)
    rwa [abs_mul, abs_two] at h
  rcases le_or_gt 0 n with hpos | hneg
  · refine ⟨q0, ?_⟩
    have : m = n := abs_of_nonneg hpos
    rw [← this]; exact hb
  · refine ⟨-q0, ?_⟩
    have : m = -n := abs_of_neg hneg
    have e : u - n * -q0 = u - m * q0 := by rw [this]; ring
    rw [e]; exact hb

variable {a b : ℤ}

/-- In a domain, `N z = 0 ↔ z = 0`. -/
theorem nm_eq_zero_iff [IsDomain (QuadraticAlgebra ℤ a b)] (z : QuadraticAlgebra ℤ a b) :
    Nm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have e := algebraMap_norm_eq_mul_star z
    rw [h, map_zero] at e
    rcases mul_eq_zero.mp e.symm with h0 | h0
    · exact h0
    · simpa using congrArg star h0
  · rintro rfl; simp

/-- The box bound behind coordinate rounding: the norm form is `< N²` in absolute value
on the box `2|e₁|, 2|e₂| ≤ N`. -/
def BoxBound (a b : ℤ) : Prop :=
  ∀ e1 e2 N : ℤ, 0 < N → 2 * |e1| ≤ N → 2 * |e2| ≤ N →
    |e1 * e1 + b * e1 * e2 - a * e2 * e2| < N * N

/-- `|a| + |b| ≤ 2` gives the box bound (crude estimate `(1 + |a| + |b|)/4 < 1`). -/
theorem boxBound_of_small (hab : |a| + |b| ≤ 2) : BoxBound a b := by
  intro e1 e2 N hNpos h1 h2
  set E1 := |e1|; set E2 := |e2|
  have hE1 : 0 ≤ E1 := abs_nonneg _
  have hE2 : 0 ≤ E2 := abs_nonneg _
  have habs : |e1 * e1 + b * e1 * e2 - a * e2 * e2| ≤ E1 * E1 + |b| * (E1 * E2) + |a| * (E2 * E2) := by
    calc |e1 * e1 + b * e1 * e2 - a * e2 * e2|
        ≤ |e1 * e1 + b * e1 * e2| + |a * e2 * e2| := abs_sub _ _
      _ ≤ |e1 * e1| + |b * e1 * e2| + |a * e2 * e2| := by gcongr; exact abs_add_le _ _
      _ = E1 * E1 + |b| * (E1 * E2) + |a| * (E2 * E2) := by
          simp only [abs_mul, E1, E2]; ring
  have p1 : 4 * (E1 * E1) ≤ N * N := by nlinarith
  have p2 : 4 * (E1 * E2) ≤ N * N := by nlinarith
  have p3 : 4 * (E2 * E2) ≤ N * N := by nlinarith
  have hb0 := abs_nonneg b
  have ha0 := abs_nonneg a
  have q2' : |b| * (4 * (E1 * E2)) ≤ |b| * (N * N) := mul_le_mul_of_nonneg_left p2 hb0
  have q3' : |a| * (4 * (E2 * E2)) ≤ |a| * (N * N) := mul_le_mul_of_nonneg_left p3 ha0
  have hNN : 0 < N * N := mul_pos hNpos hNpos
  nlinarith

/-- The box bound for `ω² = 3 + ω` (`ℚ(√13)`): `|e₁² + e₁e₂ - 3e₂²| ≤ (13/16) N²`.
The crude estimate of `boxBound_of_small` gives `5/4` and fails; completing the square
`e₁² + e₁e₂ ≥ -e₂²/4` gives the sharp lower bound. -/
theorem boxBound_three_one : BoxBound 3 1 := by
  intro e1 e2 N hNpos h1 h2
  have a1 : 4 * (e1 * e1) ≤ N * N := by
    have := abs_nonneg e1
    have : (2 * |e1|) * (2 * |e1|) ≤ N * N := by nlinarith
    nlinarith [abs_mul_abs_self e1]
  have a2 : 4 * (e2 * e2) ≤ N * N := by
    have := abs_nonneg e2
    have : (2 * |e2|) * (2 * |e2|) ≤ N * N := by nlinarith
    nlinarith [abs_mul_abs_self e2]
  have a12 : 4 * |e1 * e2| ≤ N * N := by
    rw [abs_mul]; nlinarith [abs_nonneg e1, abs_nonneg e2]
  have sq : 0 ≤ (2 * e1 + e2) * (2 * e1 + e2) := mul_self_nonneg _
  have hNN : 0 < N * N := mul_pos hNpos hNpos
  rw [abs_lt]
  constructor
  · -- 16 (e1² + e1 e2 - 3 e2²) ≥ -13 · 4 e2² ≥ -13 N² > -16 N²
    nlinarith
  · -- e1² + e1 e2 - 3e2² ≤ e1² + |e1 e2| ≤ N²/2
    nlinarith [neg_abs_le (e1 * e2), le_abs_self (e1 * e2)]

/-- The Euclidean step: a remainder of smaller `|N|`, given the box bound. -/
theorem exists_rem_of_boxBound (hB : BoxBound a b) (x y : QuadraticAlgebra ℤ a b)
    (hy : Nm y ≠ 0) : ∃ q : QuadraticAlgebra ℤ a b, |Nm (x - q * y)| < |Nm y| := by
  set n := Nm y with hn
  set w := x * star y with hw
  obtain ⟨q1, h1⟩ := int_exists_near w.re n hy
  obtain ⟨q2, h2⟩ := int_exists_near w.im n hy
  refine ⟨⟨q1, q2⟩, ?_⟩
  set e1 := w.re - n * q1 with he1
  set e2 := w.im - n * q2 with he2
  have hyy : y * star y = QuadraticAlgebra.C n := by
    rw [← algebraMap_norm_eq_mul_star]; rfl
  have hr : (x - ⟨q1, q2⟩ * y) * star y = ⟨e1, e2⟩ := by
    rw [sub_mul, mul_assoc, hyy]
    ext <;> simp [hw, he1, he2] <;> ring
  have hN : Nm (x - ⟨q1, q2⟩ * y) * n = e1 * e1 + b * e1 * e2 - a * e2 * e2 := by
    have := congrArg Nm hr
    rw [map_mul, QuadraticAlgebra.norm_star] at this
    rw [this, QuadraticAlgebra.norm_def]
  set N := |n|
  have hNpos : 0 < N := abs_pos.mpr hy
  have hbd := hB e1 e2 N hNpos h1 h2
  have hprod : |Nm (x - ⟨q1, q2⟩ * y)| * N < N * N := by
    rw [← abs_mul, hN]; exact hbd
  exact lt_of_mul_lt_mul_right hprod hNpos.le

/-- The Euclidean step when `|a| + |b| ≤ 2`. -/
theorem exists_rem (hab : |a| + |b| ≤ 2) (x y : QuadraticAlgebra ℤ a b)
    (hy : Nm y ≠ 0) : ∃ q : QuadraticAlgebra ℤ a b, |Nm (x - q * y)| < |Nm y| :=
  exists_rem_of_boxBound (boxBound_of_small hab) x y hy

/-- `ℤ[ω]` is a Euclidean domain for `|N|`, given the box bound. -/
noncomputable def euclideanDomainOfBoxBound (hB : BoxBound a b)
    [IsDomain (QuadraticAlgebra ℤ a b)] : EuclideanDomain (QuadraticAlgebra ℤ a b) := by
  classical
  exact
  { (inferInstance : CommRing (QuadraticAlgebra ℤ a b)),
    (inferInstance : Nontrivial (QuadraticAlgebra ℤ a b)) with
    quotient := fun x y => if h : y = 0 then 0 else
      Classical.choose (exists_rem_of_boxBound hB x y ((nm_eq_zero_iff y).not.mpr h))
    quotient_zero := fun x => by simp
    remainder := fun x y => x - y * (if h : y = 0 then 0 else
      Classical.choose (exists_rem_of_boxBound hB x y ((nm_eq_zero_iff y).not.mpr h)))
    quotient_mul_add_remainder_eq := fun x y => by ring
    r := fun u v => (Nm u).natAbs < (Nm v).natAbs
    r_wellFounded := (measure fun u : QuadraticAlgebra ℤ a b => (Nm u).natAbs).wf
    remainder_lt := fun x y hy => by
      simp only [dif_neg hy]
      have := Classical.choose_spec
        (exists_rem_of_boxBound hB x y ((nm_eq_zero_iff y).not.mpr hy))
      rw [mul_comm y]
      zify
      exact this
    mul_left_not_lt := fun x y hy => by
      simp only [map_mul, Int.natAbs_mul, not_lt]
      have : 1 ≤ (Nm y).natAbs := by
        have := (nm_eq_zero_iff y).not.mpr hy
        omega
      exact Nat.le_mul_of_pos_right _ this }

/-- `ℤ[ω]` is a Euclidean domain for `|N|` when `|a| + |b| ≤ 2`. -/
noncomputable def euclideanDomain (hab : |a| + |b| ≤ 2) [IsDomain (QuadraticAlgebra ℤ a b)] :
    EuclideanDomain (QuadraticAlgebra ℤ a b) :=
  euclideanDomainOfBoxBound (boxBound_of_small hab)

theorem isPrincipalIdealRing_of_boxBound (hB : BoxBound a b)
    [IsDomain (QuadraticAlgebra ℤ a b)] : IsPrincipalIdealRing (QuadraticAlgebra ℤ a b) :=
  @EuclideanDomain.instIsPrincipalIdealRing _ (euclideanDomainOfBoxBound hB)

theorem isPrincipalIdealRing (hab : |a| + |b| ≤ 2) [IsDomain (QuadraticAlgebra ℤ a b)] :
    IsPrincipalIdealRing (QuadraticAlgebra ℤ a b) :=
  isPrincipalIdealRing_of_boxBound (boxBound_of_small hab)

end ReflectZphi
