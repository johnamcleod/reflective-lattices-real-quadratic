import Mathlib

/-!
# The hyperboloid model of ℍ², for a real form of signature (2,1)

These are the geometric notions in which the imported theorems are stated
(`ReflectZphi/Imported.lean`; lean-plan.md §7).

* `B` is a real symmetric 3×3 matrix, used through `form B x y = x ⬝ᵥ B y`.
* `v₀` is a timelike vector, `form B v₀ v₀ < 0`. It selects one sheet of the hyperboloid.
* `sheet B v₀ = {x | form B x x = -1 ∧ form B x v₀ < 0}` is the model of ℍ².
* A spacelike `e` defines the closed half-plane `{x ∈ sheet | form B e x ≤ 0}`. Its
  boundary is the line (mirror) `e^⊥ ∩ sheet`.

A *compact Coxeter polygon* is given by its outward unit normals `e 0, …, e (n-1)`,
listed in cyclic order around the boundary. See `CompactCoxeterPolygon`.
-/

namespace ReflectZphi.Geometry

open Matrix

/-- The bilinear form of `B`. -/
def form (B : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) : ℝ := x ⬝ᵥ (B *ᵥ y)

/-- The sheet of the hyperboloid `form B x x = -1` that contains `v₀` (up to scaling). -/
def sheet (B : Matrix (Fin 3) (Fin 3) ℝ) (v₀ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {x | form B x x = -1 ∧ form B x v₀ < 0}

/-- The polygon cut out by the normals `e i`: the intersection of the half-planes. -/
def polygon (B : Matrix (Fin 3) (Fin 3) ℝ) (v₀ : Fin 3 → ℝ) {n : ℕ}
    (e : Fin n → Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {x | x ∈ sheet B v₀ ∧ ∀ i, form B (e i) x ≤ 0}

/-- The next and previous index, cyclically. -/
def succ' {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i + 1
def pred' {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i - 1

/-- A compact Coxeter polygon with outward unit normals `e 0, …, e (n-1)` in cyclic order.
* `interior`: the polygon has a point strictly inside every half-plane.
* `edge`: every `e i` is a genuine edge (irredundant). Some point of the polygon lies on
  the line of `e i` and strictly inside all the other half-planes.
* `vertex`: consecutive edges meet in a vertex of the polygon (this fixes the cyclic order).
* `coxeter`: the angle at that vertex is `π/m` for an integer `m ≥ 2`. For unit outward
  normals this means `form B (e i) (e (i+1)) = -cos (π/m)`.
* `compact`: the polygon is compact. -/
structure CompactCoxeterPolygon (B : Matrix (Fin 3) (Fin 3) ℝ) (v₀ : Fin 3 → ℝ) (n : ℕ)
    [NeZero n] (e : Fin n → Fin 3 → ℝ) : Prop where
  three_le : 3 ≤ n
  unit : ∀ i, form B (e i) (e i) = 1
  interior : ∃ x ∈ sheet B v₀, ∀ i, form B (e i) x < 0
  edge : ∀ i, ∃ x ∈ sheet B v₀, form B (e i) x = 0 ∧ ∀ j, j ≠ i → form B (e j) x < 0
  vertex : ∀ i, ∃ x ∈ polygon B v₀ e, form B (e i) x = 0 ∧ form B (e (succ' i)) x = 0
  coxeter : ∀ i, ∃ m : ℕ, 2 ≤ m ∧ form B (e i) (e (succ' i)) = -Real.cos (Real.pi / m)
  compact : IsCompact (polygon B v₀ e)

/-- Allcock's bound function `K(μ, μ') = (√(1+μ) + √(1+μ'))² - 1`. -/
noncomputable def allcockK (μ μ' : ℝ) : ℝ :=
  (Real.sqrt (1 + μ) + Real.sqrt (1 + μ')) ^ 2 - 1

/-- Short edge at `T = e i`: `R = e (i-1)`, `R' = e (i+1)`, with `μ = -R·T`,
`μ' = -R'·T`, `λ = -R·R'`, `0 < μ < 1`, `0 ≤ μ' < 1` and `λ < K(μ,μ') < 7`. -/
def ShortEdgeAt (B : Matrix (Fin 3) (Fin 3) ℝ) {n : ℕ} [NeZero n] (e : Fin n → Fin 3 → ℝ)
    (i : Fin n) : Prop :=
  let R := e (pred' i); let T := e i; let R' := e (succ' i)
  let μ := -form B R T; let μ' := -form B R' T; let l := -form B R R'
  0 < μ ∧ μ < 1 ∧ 0 ≤ μ' ∧ μ' < 1 ∧ l < allcockK μ μ' ∧ allcockK μ μ' < 7

/-- Short pair at `T = e i`: edges `R, S, T, R'` = `e (i-2), e (i-1), e i, e (i+1)`
(so `n ≥ 4`), with `S ⊥ R`, `S ⊥ T`, `1 < μ < 3`, `0 ≤ μ' < 1` and
`λ < K(μ,μ') < 5 + 4√2`. -/
def ShortPairAt (B : Matrix (Fin 3) (Fin 3) ℝ) {n : ℕ} [NeZero n] (e : Fin n → Fin 3 → ℝ)
    (i : Fin n) : Prop :=
  let R := e (pred' (pred' i)); let S := e (pred' i); let T := e i; let R' := e (succ' i)
  let μ := -form B R T; let μ' := -form B R' T; let l := -form B R R'
  4 ≤ n ∧ form B S R = 0 ∧ form B S T = 0 ∧ 1 < μ ∧ μ < 3 ∧ 0 ≤ μ' ∧ μ' < 1 ∧
    l < allcockK μ μ' ∧ allcockK μ μ' < 5 + 4 * Real.sqrt 2

/-- Close pair at `T = e i`: edges `R, S, T, S', R'` = `e (i-2), …, e (i+2)` (so `n ≥ 5`),
with `S ⊥ R, T`, `S' ⊥ T, R'`, `1 < μ < 3`, `1 < μ' < 3` and `λ < K(μ,μ') < 15`. -/
def ClosePairAt (B : Matrix (Fin 3) (Fin 3) ℝ) {n : ℕ} [NeZero n] (e : Fin n → Fin 3 → ℝ)
    (i : Fin n) : Prop :=
  let R := e (pred' (pred' i)); let S := e (pred' i); let T := e i
  let S' := e (succ' i); let R' := e (succ' (succ' i))
  let μ := -form B R T; let μ' := -form B R' T; let l := -form B R R'
  5 ≤ n ∧ form B S R = 0 ∧ form B S T = 0 ∧ form B S' T = 0 ∧ form B S' R' = 0 ∧
    1 < μ ∧ μ < 3 ∧ 1 < μ' ∧ μ' < 3 ∧ l < allcockK μ μ' ∧ allcockK μ μ' < 15

end ReflectZphi.Geometry
