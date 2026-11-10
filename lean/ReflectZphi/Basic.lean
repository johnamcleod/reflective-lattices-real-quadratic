import Mathlib

/-! Smoke test of the pinned toolchain: ℤ[φ] as `QuadraticAlgebra ℤ 1 1`
(ω² = 1 + ω). The development proper follows `lean-plan.md`. -/

namespace ReflectZphi

abbrev ZPhi := QuadraticAlgebra ℤ 1 1

/-- φ, the generator ω. -/
def phi : ZPhi := ⟨0, 1⟩

/-- Checked by kernel evaluation (no `native_decide`). -/
theorem phi_sq : phi * phi = phi + 1 := by
  rfl

/-- `decide` works on `QuadraticAlgebra ℤ 1 1` equalities (kernel evaluation). -/
example : phi * phi * phi = phi * phi + phi := by
  decide

end ReflectZphi
