import ReflectZphi.Cert.Mat3

/-!
# Isometry certificates

`checkIso G₁ G₂ P` checks `Pᵀ G₂ P = G₁` and `N(det P) = ±1`, i.e. `P ∈ GL₃(𝒪)` and `P` is
an isometry from `(𝒪³, G₁)` to `(𝒪³, G₂)`. It is evaluated by `decide +kernel`, and
`checkIso_sound` turns a successful check into the statement about Mathlib matrices.
-/

namespace ReflectZphi

open QuadraticAlgebra

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-- The isometry check. -/
def checkIso (G₁ G₂ P : Mat3 (QuadraticAlgebra ℤ a b)) : Bool :=
  decide ((P.transpose.mul G₂).mul P = G₁) && decide (Nm P.det = 1 ∨ Nm P.det = -1)

theorem checkIso_sound {G₁ G₂ P : Mat3 (QuadraticAlgebra ℤ a b)}
    (h : checkIso G₁ G₂ P = true) :
    P.toMatrix.transpose * G₂.toMatrix * P.toMatrix = G₁.toMatrix ∧
      IsUnit P.toMatrix.det := by
  simp only [checkIso, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← h1, Mat3.toMatrix_mul, Mat3.toMatrix_mul, Mat3.toMatrix_transpose]
  · rw [Mat3.det_toMatrix, isUnit_iff_norm_isUnit, Int.isUnit_iff]
    exact h2

end ReflectZphi
