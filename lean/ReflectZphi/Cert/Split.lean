import ReflectZphi.Cert.Check

/-!
# Splitting one enumeration into separately checked subtrees

The kernel keeps every intermediate value of one `decide` until that declaration is checked,
so one large search costs memory linear in its size. Here the search `enumS` is cut along a
list `L` of *prefixes* (values of the top coordinates): `coverAux` walks the tree from the
root and stops at every node whose prefix is in `L`; each such subtree is evaluated by `sub`
in its own declaration. `enumS_of_cover` glues them back together.
-/

namespace ReflectZphi.Split

open Matrix QuadraticAlgebra ReflectZphi.Lattice ReflectZphi.Bridge ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.PolyEnum ReflectZphi.Check ReflectZphi.Cells

/-- One step down the tree: fix coordinate `k` to `t` and charge its cost to the budget. -/
def step (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) : ℕ × (ℕ → ℤ) × ℤ → ℤ → ℕ × (ℕ → ℤ) × ℤ
  | (k + 1, z, B), t => (k, Function.update z k t, B - w k * (a k k * t + cent a n k z) ^ 2)
  | (0, z, B), _ => (0, z, B)

/-- The node reached from `s` by the prefix `p`. -/
def replay (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (s : ℕ × (ℕ → ℤ) × ℤ) (p : List ℤ) :
    ℕ × (ℕ → ℤ) × ℤ :=
  p.foldl (step a w n) s

/-- The subtree below the prefix `p`. -/
def sub (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n stop : ℕ) (leaf : (ℕ → ℤ) → Bool)
    (s : ℕ × (ℕ → ℤ) × ℤ) (p : List ℤ) : Bool :=
  let r := replay a w n s p
  enumAuxS a w n stop leaf r.1 r.2.1 r.2.2

/-- The top of the tree, down to the prefixes in `L` (which are then not entered). -/
def coverAux (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n stop : ℕ) (L : List (List ℤ)) :
    ℕ → (ℕ → ℤ) → ℤ → List ℤ → Bool
  | 0, _, _, p => decide (p ∈ L)
  | k + 1, z, B, p => decide (p ∈ L) || (decide (stop < k + 1) && (decide (B < 0) ||
    (let c := cent a n k z
     let akk := a k k
     let wk := w k
     let s : ℤ := (isqrt (B.toNat / wk.toNat) : ℕ)
     decide (B < wk * (s + 1) ^ 2) && decide (0 < akk) && decide (0 < wk) &&
      allRange (fun t => coverAux a w n stop L k (Function.update z k t)
        (B - wk * (akk * t + c) ^ 2) (p ++ [t])) ((-s - c) / akk)
        ((s - c) / akk - (-s - c) / akk + 1).toNat)))

lemma allRange_of_forall {f : ℤ → Bool} {lo : ℤ} {len : ℕ}
    (h : ∀ t, lo ≤ t → t < lo + len → f t = true) : allRange f lo len = true := by
  induction len generalizing lo with
  | zero => rfl
  | succ len ih =>
    simp only [allRange, Bool.and_eq_true]
    refine ⟨h lo le_rfl (by push_cast; omega), ih fun t h1 h2 => h t (by omega) ?_⟩
    push_cast at h2 ⊢; omega

lemma replay_snoc (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (s : ℕ × (ℕ → ℤ) × ℤ) (p : List ℤ)
    (t : ℤ) : replay a w n s (p ++ [t]) = step a w n (replay a w n s p) t := by
  simp [replay, List.foldl_append]

theorem coverAux_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf : (ℕ → ℤ) → Bool}
    {L : List (List ℤ)} {s₀ : ℕ × (ℕ → ℤ) × ℤ} (hL : ∀ q ∈ L, sub a w n stop leaf s₀ q = true) :
    ∀ k z B p, coverAux a w n stop L k z B p = true → replay a w n s₀ p = (k, z, B) →
      enumAuxS a w n stop leaf k z B = true := by
  intro k
  induction k with
  | zero =>
    intro z B p h hr
    simp only [coverAux, decide_eq_true_eq] at h
    have := hL p h
    simpa [sub, hr] using this
  | succ k ih =>
    intro z B p h hr
    simp only [coverAux, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with hp | ⟨hst, hB | hg⟩
    · have := hL p hp
      simpa [sub, hr] using this
    · have hs : ¬ k + 1 ≤ stop := by omega
      simp only [enumAuxS, hs, hB, ↓reduceIte]
    · have hs : ¬ k + 1 ≤ stop := by omega
      by_cases hB : B < 0
      · simp only [enumAuxS, hs, hB, ↓reduceIte]
      simp only [enumAuxS, hs, hB, ↓reduceIte]
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hg
      simp only [h1, h2, h3, decide_true, Bool.and_self, ite_true]
      refine allRange_of_forall fun t ht1 ht2 => ?_
      refine ih _ _ (p ++ [t]) (allRange_spec h4 t ht1 ht2) ?_
      rw [replay_snoc, hr, step]

/-- **The glue.** If the top of the tree is covered by `L` and every subtree below a prefix
in `L` passes, the whole stopped search passes. -/
theorem enumS_of_cover {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf : (ℕ → ℤ) → Bool}
    {B : ℤ} {L : List (List ℤ)} (hc : coverAux a w n stop L n (fun _ => 0) B [] = true)
    (hL : ∀ q ∈ L, sub a w n stop leaf (n, fun _ => 0, B) q = true) :
    enumS a w n stop leaf B = true :=
  coverAux_sound hL n _ B [] hc rfl

/-- `cellCheck` without its enumeration (which is `cellCheck`'s last conjunct). -/
def cellPre {a b : ℤ} (G : Matrix (Fin 3) (Fin 3) (O a b)) (f : Fin 3 → Fin 3 → O a b) (n : ℕ)
    (Ps : ℕ → Fin 3 → O a b) (norms : List (O a b)) (c : CellData a b) : Bool :=
  neg1 (bilE G c.V c.V) && neg1 (bilE G c.V (f 2)) &&
  decide (0 < c.qC) &&
  (norms.all fun m => nonneg1 ((c.K : O a b) - bndElt G c.V c.μ c.pC c.qC m)) &&
  ((List.range 6).all fun i => decide (0 ≤ c.w i)) && decide (0 < c.S) &&
  quadCheck c.aL c.w 6 (gramU c.U (traceGram G c.V c.μ c.qC)) c.S &&
  invCheck c.U c.Uinv && colCheck (a := a) (b := b) c.U

theorem cellCheck_of {a b : ℤ} {G : Matrix (Fin 3) (Fin 3) (O a b)} {f : Fin 3 → Fin 3 → O a b}
    {n : ℕ} {Ps : ℕ → Fin 3 → O a b} {norms : List (O a b)} {c : CellData a b}
    (h0 : cellPre G f n Ps norms c = true)
    (he : enumS c.aL c.w 6 2 (leaf2 G n Ps norms c.U) (c.S * c.K) = true) :
    cellCheck G f n Ps norms c = true := by
  rw [cellCheck]; rw [cellPre] at h0; rw [h0, he]; rfl

end ReflectZphi.Split
