import ReflectZphi.Cert.RootNorms

/-!
# The window norm list, computed in chunks of rows

`windowNorms a b D p q Y S` walks a `Y × S` box; for a large box one `decide +kernel` on
`windowNorms … = normsL` needs more than 4 GB (class 87 of ℤ[φ]: 106 × 471 points). Here
the walk over `y` is cut into chunks of `c` rows: each chunk is a separate (small) kernel
computation, and `windowNorms_of_chunks` reassembles them.
-/

namespace ReflectZphi.RootNorms

open Matrix QuadraticAlgebra ReflectZphi.Lattice

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-- One row (fixed `y`) of `windowNorms`. -/
def winRow (a b : ℤ) (D : O a b) (p q : ℤ) (S : ℕ) (y : ℕ) : List (O a b) :=
  (List.range S).filterMap fun (s : ℕ) =>
    let yi : ℤ := y
    let si : ℤ := s
    let m : O a b := ⟨(si - b * yi) / 2, yi⟩
    if (si - b * yi) % 2 == 0 && 0 < si &&
        decide (q * (b ^ 2 + 4 * a) * yi ^ 2 < p * |Nm D|) &&
        decide (q * si ^ 2 < 4 * p * |Nm D|) &&
        posCode si (-yi) (b ^ 2 + 4 * a) &&
        winCode p q m && dvdCode m D
    then some m else none

/-- Rows `y0, …, y0 + len - 1`. -/
def winRows (a b : ℤ) (D : O a b) (p q : ℤ) (S : ℕ) (y0 len : ℕ) : List (O a b) :=
  (List.range' y0 len).flatMap (winRow a b D p q S)

theorem windowNorms_eq_winRows (D : O a b) (p q : ℤ) (Y S : ℕ) :
    windowNorms a b D p q Y S = winRows a b D p q S 0 Y := by
  unfold windowNorms winRows winRow
  simp only [List.range_eq_range']

theorem winRows_add (D : O a b) (p q : ℤ) (S y0 l₁ l₂ : ℕ) :
    winRows a b D p q S y0 (l₁ + l₂) =
      winRows a b D p q S y0 l₁ ++ winRows a b D p q S (y0 + l₁) l₂ := by
  unfold winRows
  rw [← List.flatMap_append, List.range'_append_1]

theorem winRows_chunks (D : O a b) (p q : ℤ) (S c : ℕ) (cs : ℕ → List (O a b)) :
    ∀ k : ℕ, (∀ i < k, winRows a b D p q S (c * i) c = cs i) →
      winRows a b D p q S 0 (c * k) = (List.range k).flatMap cs := by
  intro k
  induction k with
  | zero => intro _; simp [winRows]
  | succ k ih =>
    intro h
    rw [Nat.mul_succ, winRows_add, ih (fun i hi => h i (by omega)), Nat.zero_add,
      h k (by omega), List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- **Reassembly.** If the chunks of `c` rows give `cs 0, …, cs (k-1)` and the last `r` rows
give `rest`, then `windowNorms` is their concatenation. -/
theorem windowNorms_of_chunks (D : O a b) (p q : ℤ) (S c k r : ℕ) (cs : ℕ → List (O a b))
    (rest : List (O a b)) (h : ∀ i < k, winRows a b D p q S (c * i) c = cs i)
    (hr : winRows a b D p q S (c * k) r = rest) :
    windowNorms a b D p q (c * k + r) S = (List.range k).flatMap cs ++ rest := by
  rw [windowNorms_eq_winRows, winRows_add, winRows_chunks D p q S c cs k h, Nat.zero_add, hr]

end ReflectZphi.RootNorms
