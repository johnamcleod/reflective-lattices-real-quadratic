import Mathlib

/-!
# Concrete 3×3 matrices for kernel-evaluated certificate checks

`Mat3 R` stores nine entries; multiplication, transpose and determinant are written out
explicitly, so that `decide +kernel` evaluates them quickly. Each operation is proved to
agree with Mathlib's `Matrix (Fin 3) (Fin 3) R`, so a check on `Mat3` is a statement about
`Matrix`.
-/

namespace ReflectZphi

structure Mat3 (R : Type*) where
  a00 : R
  a01 : R
  a02 : R
  a10 : R
  a11 : R
  a12 : R
  a20 : R
  a21 : R
  a22 : R
  deriving DecidableEq

namespace Mat3

variable {R : Type*} [CommRing R]

/-- The Mathlib matrix of a `Mat3`. -/
def toMatrix (A : Mat3 R) : Matrix (Fin 3) (Fin 3) R :=
  !![A.a00, A.a01, A.a02; A.a10, A.a11, A.a12; A.a20, A.a21, A.a22]

def mul (A B : Mat3 R) : Mat3 R where
  a00 := A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20
  a01 := A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21
  a02 := A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22
  a10 := A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20
  a11 := A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21
  a12 := A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22
  a20 := A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20
  a21 := A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21
  a22 := A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22

def transpose (A : Mat3 R) : Mat3 R :=
  ⟨A.a00, A.a10, A.a20, A.a01, A.a11, A.a21, A.a02, A.a12, A.a22⟩

def det (A : Mat3 R) : R :=
  A.a00 * (A.a11 * A.a22 - A.a12 * A.a21) - A.a01 * (A.a10 * A.a22 - A.a12 * A.a20)
    + A.a02 * (A.a10 * A.a21 - A.a11 * A.a20)

theorem toMatrix_mul (A B : Mat3 R) : (A.mul B).toMatrix = A.toMatrix * B.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem toMatrix_transpose (A : Mat3 R) : A.transpose.toMatrix = A.toMatrix.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, transpose]

theorem det_toMatrix (A : Mat3 R) : A.toMatrix.det = A.det := by
  simp [toMatrix, det, Matrix.det_fin_three]
  ring

theorem toMatrix_injective : Function.Injective (toMatrix : Mat3 R → _) := by
  intro A B h
  have e : ∀ i j, A.toMatrix i j = B.toMatrix i j := fun i j => by rw [h]
  cases A; cases B
  have := e 0 0; have := e 0 1; have := e 0 2
  have := e 1 0; have := e 1 1; have := e 1 2
  have := e 2 0; have := e 2 1; have := e 2 2
  simp_all [toMatrix]

end Mat3

end ReflectZphi
