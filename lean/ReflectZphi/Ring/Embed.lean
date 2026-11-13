import ReflectZphi.Ring.Euclid

/-!
# Real embeddings and an exact sign test (generic)

For `ℤ[ω]`, ω² = a + bω with `d = b² + 4a > 0`, the two real embeddings send
ω ↦ (b ± √d)/2. With `z = x + yω`, `2 ι_e(z) = (2x + by) + (e y)√d`, so the sign of
`ι_e(z)` is decided by integer arithmetic (`posCode`). This is what the
certificate checkers use for "totally positive", admissibility and Coxeter angles.
-/

namespace ReflectZphi

open QuadraticAlgebra

/-- `(b + e√d)/2`, a root of `X² - bX - a` when `e² = 1`. -/
noncomputable def root (a b e : ℤ) : ℝ := (b + e * Real.sqrt ((b : ℝ) ^ 2 + 4 * a)) / 2

theorem root_mul_self {a b e : ℤ} (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (he : e * e = 1) :
    root a b e * root a b e = a • (1 : ℝ) + b • root a b e := by
  have ht := Real.mul_self_sqrt hd
  have he' : (e : ℝ) * e = 1 := by exact_mod_cast he
  simp only [root, zsmul_eq_mul, mul_one]
  set t := Real.sqrt ((b : ℝ) ^ 2 + 4 * a)
  linear_combination (t * t / 4) * he' + (1 / 4 : ℝ) * ht

/-- The real embedding `ω ↦ (b + e√d)/2`. -/
noncomputable def emb (a b e : ℤ) (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (he : e * e = 1) :
    QuadraticAlgebra ℤ a b →+* ℝ :=
  (lift ⟨root a b e, root_mul_self hd he⟩).toRingHom

theorem emb_apply {a b e : ℤ} (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (he : e * e = 1)
    (z : QuadraticAlgebra ℤ a b) : emb a b e hd he z = z.re + z.im * root a b e := by
  simp [emb, zsmul_eq_mul]

/-- Exact sign code: `posCode s y D = true ↔ 0 < s + y√D` (for `D > 0`). -/
def posCode (s y D : ℤ) : Bool :=
  (y == 0 && 0 < s) || (0 < y && (0 ≤ s || s * s < D * y * y)) ||
    (y < 0 && 0 < s && D * y * y < s * s)

theorem pos_iff_posCode (s y D : ℤ) (t : ℝ) (ht0 : 0 < t) (ht : t * t = D) :
    0 < (s : ℝ) + y * t ↔ posCode s y D = true := by
  simp only [posCode, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hyR : (y : ℝ) < 0 := by exact_mod_cast hy
    constructor
    · intro h
      have hs : (0 : ℝ) < s := by nlinarith
      have hsZ : 0 < s := by exact_mod_cast hs
      refine Or.inr ⟨⟨hy, hsZ⟩, ?_⟩
      have hyt : 0 ≤ -((y : ℝ) * t) := by nlinarith
      have hlt : -((y : ℝ) * t) < s := by linarith
      have hsq := mul_self_lt_mul_self hyt hlt
      have : (D : ℝ) * y * y < s * s := by rw [← ht]; nlinarith
      exact_mod_cast this
    · rintro ((⟨h1, _⟩ | ⟨h1, _⟩) | ⟨⟨_, hs⟩, hD⟩)
      · omega
      · omega
      · have hsR : (0 : ℝ) < s := by exact_mod_cast hs
        have hDR : (D : ℝ) * y * y < s * s := by exact_mod_cast hD
        rw [← ht] at hDR
        nlinarith
  · subst hy
    simp only [Int.cast_zero, zero_mul, add_zero, Int.cast_pos, lt_self_iff_false,
      false_and, or_false, true_and]
  · have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    constructor
    · intro h
      refine Or.inl (Or.inr ⟨hy, ?_⟩)
      by_cases hs : 0 ≤ s
      · exact Or.inl hs
      · right
        have hsR : (s : ℝ) < 0 := by exact_mod_cast (not_le.mp hs)
        have : (s : ℝ) * s < D * y * y := by rw [← ht]; nlinarith
        exact_mod_cast this
    · rintro ((⟨h1, _⟩ | ⟨_, hs | hD⟩) | ⟨⟨h1, _⟩, _⟩)
      · omega
      · have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs
        nlinarith
      · have hDR : (s : ℝ) * s < D * y * y := by exact_mod_cast hD
        rw [← ht] at hDR
        by_contra hneg
        have hyt : 0 ≤ (y : ℝ) * t := by positivity
        have hle : (y : ℝ) * t ≤ -(s : ℝ) := by linarith
        have hsq := mul_self_le_mul_self hyt hle
        nlinarith
      · omega

/-- Generic exact sign test at the embedding `e`. -/
theorem emb_pos_iff {a b e : ℤ} (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) (he : e * e = 1)
    (z : QuadraticAlgebra ℤ a b) :
    0 < emb a b e hd0.le he z ↔ posCode (2 * z.re + b * z.im) (e * z.im) (b ^ 2 + 4 * a) = true := by
  rw [← pos_iff_posCode _ _ _ (Real.sqrt ((b : ℝ) ^ 2 + 4 * a)) (Real.sqrt_pos.mpr hd0)
    (by rw [Real.mul_self_sqrt hd0.le]; push_cast; ring)]
  rw [emb_apply, root]
  push_cast
  constructor <;> intro h <;> nlinarith

end ReflectZphi
