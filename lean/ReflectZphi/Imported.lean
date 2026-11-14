import ReflectZphi.Geometry.Hyperbolic
import ReflectZphi.Lattice.Basic

/-!
# The two imported theorems, as named propositions

Approved by the user on 2026-11-13 (lean-plan.md §5). They are **not** axioms. Main
theorems take them as hypotheses (`(hA : AllcockThinPart) (hV : VinbergChamber)`), so
`#print axioms` stays within `propext`, `Classical.choice` and `Quot.sound`, and the
dependence is visible in every statement that uses them (lean-plan.md §7).

* `AllcockThinPart`: Allcock, *Infinitely many hyperbolic Coxeter groups through
  dimension 19*, Geom. Topol. / Mem. AMS 220 (2012), Thm 1 with Lemmas 3–5
  (arXiv:1010.0486). This is paper Theorem `thm:thin`.
* `VinbergChamber`: Vinberg, *On groups of unit elements of certain quadratic forms*,
  Math. USSR Sb. 16 (1972). It covers the chamber structure of `W(L)` and the
  reflectivity criterion. This is paper Appendix A.1.
-/

namespace ReflectZphi

open ReflectZphi.Geometry ReflectZphi.Lattice Matrix

/-- The polygon read in the opposite direction. -/
def revIdx {n : ℕ} [NeZero n] (e : Fin n → Fin 3 → ℝ) : Fin n → Fin 3 → ℝ :=
  fun j => e (-j)

/-- **Allcock's thin-part theorem.** Every compact Coxeter polygon in ℍ² (for any real
form of signature (2,1)) has a short edge, a short pair or a close pair. The edges are
read in one of the two cyclic directions.

Signature (2,1) is imposed as for `Admissible`: `det B < 0` and some vector of positive
norm. Without it, a compact "polygon" on a one-sheeted hyperboloid could satisfy
`CompactCoxeterPolygon` and falsify the proposition. -/
def AllcockThinPart : Prop :=
  ∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (v₀ : Fin 3 → ℝ) (n : ℕ) [NeZero n]
    (e : Fin n → Fin 3 → ℝ),
    Bᵀ = B → B.det < 0 → (∃ v, 0 < form B v v) → form B v₀ v₀ < 0 →
    CompactCoxeterPolygon B v₀ n e →
    ∃ f ∈ ({e, revIdx e} : Set (Fin n → Fin 3 → ℝ)), ∃ i : Fin n,
      ShortEdgeAt B f i ∨ ShortPairAt B f i ∨ ClosePairAt B f i

section chambers

variable {a b : ℤ} (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (G : Matrix (Fin 3) (Fin 3) (O a b))

/-- The real form of `L` at `ι₁`. -/
noncomputable def realForm : Matrix (Fin 3) (Fin 3) ℝ := G.map (ι₁ hd)

/-- A vector of `O³` viewed in `ℝ³` via `ι₁`. -/
noncomputable def realVec (r : Fin 3 → O a b) : Fin 3 → ℝ := fun i => ι₁ hd (r i)

/-- The union of the mirrors of all roots of `L`, inside the sheet. -/
noncomputable def mirrors (v₀ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {x | x ∈ sheet (realForm hd G) v₀ ∧
    ∃ r, IsRoot hd G r ∧ form (realForm hd G) (realVec hd r) x = 0}

/-- A chamber of `W(L)`: the closure of a connected component of the complement of the
mirrors in the sheet. -/
def IsChamber (v₀ : Fin 3 → ℝ) (C : Set (Fin 3 → ℝ)) : Prop :=
  ∃ x ∈ sheet (realForm hd G) v₀ \ mirrors hd G v₀,
    C = closure (connectedComponentIn (sheet (realForm hd G) v₀ \ mirrors hd G v₀) x)

/-- The action of `g ∈ GL₃(O)` on `ℝ³` through `ι₁`. -/
noncomputable def act (g : GL (Fin 3) (O a b)) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (g.val.map (ι₁ hd)) *ᵥ x

end chambers

/-- **Vinberg's chamber theorem**, for an admissible rank-3 lattice `L = (O³, G)` and either
sheet (given by any timelike `v₀`):
1. `W(L)` acts transitively on the chambers;
2. the action is free: an element of `W(L)` fixing a chamber is the identity;
3. `L` is reflective (`W(L)` of finite index in `O(L)`) iff some chamber is compact.

The part `O′(L) = W(L) ⋊ Stab(C)` of the approved statement is omitted: nothing uses it.
This makes the hypothesis weaker.

`b² + 4a` must not be a square, so that `O` is an order in a real quadratic field. If it
were a square, `O` would embed in `ℤ × ℤ`, `ι₁` would not be injective, and freeness
(item 2) could fail, making the proposition false. -/
def VinbergChamber : Prop :=
  ∀ (a b : ℤ) (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (G : Matrix (Fin 3) (Fin 3) (O a b))
    (v₀ : Fin 3 → ℝ),
    ¬ IsSquare (b ^ 2 + 4 * a) → Admissible hd G → form (realForm hd G) v₀ v₀ < 0 →
    (∀ C C', IsChamber hd G v₀ C → IsChamber hd G v₀ C' →
        ∃ w ∈ reflectionGroup hd G, act hd w '' C = C') ∧
    (∀ C, IsChamber hd G v₀ C → ∀ w ∈ reflectionGroup hd G, act hd w '' C = C → w = 1) ∧
    (Reflective hd G ↔ ∃ C, IsChamber hd G v₀ C ∧ IsCompact C)

end ReflectZphi
