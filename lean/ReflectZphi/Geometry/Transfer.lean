import ReflectZphi.Geometry.Chamber
import ReflectZphi.Geometry.Hyperbolic

/-!
# Transfer between a real form `B = Tᵀ J T` and the standard Minkowski form `J`

If `B = Tᵀ J T`, with `T` invertible and `T v₀ = (0, 0, c)` for some `c > 0`, then
`x ↦ T x` carries:
* the sheet of `B` through `v₀` onto the upper sheet;
* the mirrors of a set `RsB` onto the mirrors of `T '' RsB`.

So a polygon that B6 shows to be a chamber in `J` coordinates (`polySet_eq_chamber`) is a
chamber of `B`, and it is compact (`chamber_of_J`).
-/

namespace ReflectZphi.Transfer

open Matrix Set ReflectZphi.Minkowski ReflectZphi.Geometry

/-- The matrix of `mink`. -/
def Jmat : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 1, -1]

lemma mink_eq (x y : Fin 3 → ℝ) : mink x y = x ⬝ᵥ (Jmat *ᵥ y) := by
  simp [mink, Jmat, dotProduct, Fin.sum_univ_three, mulVec, Matrix.diagonal]; ring

lemma form_eq_mink {B T : Matrix (Fin 3) (Fin 3) ℝ} (hB : B = Tᵀ * Jmat * T)
    (x y : Fin 3 → ℝ) : form B x y = mink (T *ᵥ x) (T *ᵥ y) := by
  rw [mink_eq, form, hB, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- `x ↦ T x` as a homeomorphism, given a two-sided inverse `Ti`. -/
def homeo (T Ti : Matrix (Fin 3) (Fin 3) ℝ) (h1 : Ti * T = 1) (h2 : T * Ti = 1) :
    (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) where
  toFun x := T *ᵥ x
  invFun x := Ti *ᵥ x
  left_inv x := by simp only [mulVec_mulVec, h1, one_mulVec]
  right_inv x := by simp only [mulVec_mulVec, h2, one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

/-- The mirrors of a set of vectors in the sheet of `B` through `v₀`. -/
def mirrorsB (B : Matrix (Fin 3) (Fin 3) ℝ) (v₀ : Fin 3 → ℝ) (RsB : Set (Fin 3 → ℝ)) :
    Set (Fin 3 → ℝ) :=
  {x | x ∈ sheet B v₀ ∧ ∃ r ∈ RsB, form B r x = 0}

/-- **Transfer.** A polygon that is a chamber in `J` coordinates is a compact chamber of `B`.
-/
theorem chamber_of_J {B T Ti : Matrix (Fin 3) (Fin 3) ℝ} (hB : B = Tᵀ * Jmat * T)
    (h1 : Ti * T = 1) (h2 : T * Ti = 1) {v₀ : Fin 3 → ℝ} {c : ℝ} (hc : 0 < c)
    (hv₀ : T *ᵥ v₀ = ![0, 0, c]) {RsB : Set (Fin 3 → ℝ)} {n : ℕ} {E P : ℕ → Fin 3 → ℝ}
    {XsB : Fin 3 → ℝ}
    (hCD : ChamberData n (fun i => T *ᵥ E i) (fun i => T *ᵥ P i) ((T *ᵥ ·) '' RsB)
      (T *ᵥ XsB)) :
    ∃ x ∈ sheet B v₀ \ mirrorsB B v₀ RsB,
      (Ti *ᵥ ·) '' polySet n (fun i => T *ᵥ E i) =
        closure (connectedComponentIn (sheet B v₀ \ mirrorsB B v₀ RsB) x) ∧
      IsCompact ((Ti *ᵥ ·) '' polySet n (fun i => T *ᵥ E i)) := by
  set h := homeo T Ti h1 h2
  have hsheet : ∀ x, x ∈ sheet B v₀ ↔ h x ∈ upperSheet := by
    intro x
    change form B x x = -1 ∧ form B x v₀ < 0 ↔ mink (T *ᵥ x) (T *ᵥ x) = -1 ∧ 0 < (T *ᵥ x) 2
    rw [form_eq_mink hB, form_eq_mink hB, hv₀]
    have : mink (T *ᵥ x) ![0, 0, c] = -(c * (T *ᵥ x) 2) := by simp [mink]; ring
    rw [this]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith⟩
  have hdiff : sheet B v₀ \ mirrorsB B v₀ RsB =
      h.symm '' (upperSheet \ mirrorSet ((T *ᵥ ·) '' RsB)) := by
    rw [Homeomorph.image_symm]
    ext x
    simp only [mem_sdiff, mem_preimage, mirrorsB, mirrorSet, mem_ofPred_eq, mem_image,
      exists_exists_and_eq_and, ← hsheet]
    constructor
    · rintro ⟨hs, hm⟩
      refine ⟨hs, fun ⟨_, r, hr, hrx⟩ => hm ⟨hs, r, hr, ?_⟩⟩
      rw [form_eq_mink hB]; exact hrx
    · rintro ⟨hs, hm⟩
      refine ⟨hs, fun ⟨_, r, hr, hrx⟩ => hm ⟨hs, r, hr, ?_⟩⟩
      rw [form_eq_mink hB] at hrx; exact hrx
  obtain ⟨hmem, heq⟩ := polySet_eq_chamber hCD
  have himg : (Ti *ᵥ ·) '' polySet n (fun i => T *ᵥ E i) =
      h.symm '' polySet n (fun i => T *ᵥ E i) := rfl
  refine ⟨h.symm (nrm (T *ᵥ XsB)), by rw [hdiff]; exact mem_image_of_mem _ hmem, ?_, ?_⟩
  · rw [himg, heq, h.symm.image_closure, h.symm.image_connectedComponentIn hmem, hdiff]
  · rw [himg]
    exact (isCompact_polySet hCD.poly hCD.fut).image h.symm.continuous

end ReflectZphi.Transfer
