import ReflectZphi.Cert.Split

/-!
# A linear-time cover of the top of the tree

`Split.coverAux` tests `p ∈ L` at every node of the top of the tree, which costs
(top nodes) × |L| list comparisons: quadratic in the number of subtrees. Here the prefix list
is consumed in the order of the walk (depth first, coordinates ascending, exactly the order
in which the emitter lists the prefixes): at each node, if the head of the remaining list is
the current prefix, it is popped and the subtree is not entered. The walk threads the
remaining list through `foldRange`; it succeeds (`isSome`) only if every node it reaches is
either popped or expanded. Every popped prefix is an element of the original list, so the
glue `enumS_of_coverL` needs the subtree checks only for the elements of `L`.
-/

namespace ReflectZphi.Split

open ReflectZphi.Enum

/-- Pop `p` off the head of `L`. -/
def pop (p : List ℤ) : List (List ℤ) → Option (List (List ℤ))
  | q :: r => if q = p then some r else none
  | [] => none

/-- Thread a state through `f lo, f (lo+1), …, f (lo+len-1)`, failing if any step fails. -/
def foldRange {α : Type} (f : ℤ → α → Option α) : ℤ → ℕ → α → Option α
  | _, 0, x => some x
  | lo, len + 1, x => (f lo x).bind (foldRange f (lo + 1) len)

/-- The top of the tree, popping the prefixes of `L` in walk order. -/
def coverL (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n stop : ℕ) :
    ℕ → (ℕ → ℤ) → ℤ → List ℤ → List (List ℤ) → Option (List (List ℤ))
  | 0, _, _, p, L => pop p L
  | k + 1, z, B, p, L =>
    match pop p L with
    | some r => some r
    | none =>
      if stop < k + 1 then
        if B < 0 then some L else
        let c := cent a n k z
        let akk := a k k
        let wk := w k
        let s : ℤ := (isqrt (B.toNat / wk.toNat) : ℕ)
        if decide (B < wk * (s + 1) ^ 2) && decide (0 < akk) && decide (0 < wk) then
          foldRange (fun t L' => coverL a w n stop k (Function.update z k t)
            (B - wk * (akk * t + c) ^ 2) (p ++ [t]) L') ((-s - c) / akk)
            ((s - c) / akk - (-s - c) / akk + 1).toNat L
        else none
      else none

lemma pop_spec {p : List ℤ} {L R : List (List ℤ)} (h : pop p L = some R) :
    p ∈ L ∧ ∀ q ∈ R, q ∈ L := by
  cases L with
  | nil => simp [pop] at h
  | cons q r =>
    simp only [pop] at h
    split_ifs at h with hq
    · cases h; subst hq; exact ⟨List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ hx⟩

lemma foldRange_spec {α : Type} {f : ℤ → α → Option α} {P : α → Prop} {Q : ℤ → Prop}
    (hf : ∀ t x y, P x → f t x = some y → Q t ∧ P y) :
    ∀ (len : ℕ) (lo : ℤ) (x y : α), P x → foldRange f lo len x = some y →
      (∀ t, lo ≤ t → t < lo + len → Q t) ∧ P y := by
  intro len
  induction len with
  | zero =>
    intro lo x y hx h
    simp only [foldRange, Option.some.injEq] at h
    subst h
    exact ⟨fun t h1 h2 => by push_cast at h2; omega, hx⟩
  | succ len ih =>
    intro lo x y hx h
    simp only [foldRange] at h
    cases hfx : f lo x with
    | none => simp [hfx] at h
    | some x' =>
      rw [hfx, Option.bind_some] at h
      obtain ⟨hq, hx'⟩ := hf lo x x' hx hfx
      obtain ⟨hall, hy⟩ := ih (lo + 1) x' y hx' h
      refine ⟨fun t h1 h2 => ?_, hy⟩
      rcases eq_or_lt_of_le h1 with h1 | h1
      · exact h1 ▸ hq
      · exact hall t (by omega) (by push_cast at h2 ⊢; omega)

theorem coverL_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf : (ℕ → ℤ) → Bool}
    {L₀ : List (List ℤ)} {s₀ : ℕ × (ℕ → ℤ) × ℤ}
    (hL : ∀ q ∈ L₀, sub a w n stop leaf s₀ q = true) :
    ∀ k z B p L R, (∀ q ∈ L, q ∈ L₀) → coverL a w n stop k z B p L = some R →
      replay a w n s₀ p = (k, z, B) →
      enumAuxS a w n stop leaf k z B = true ∧ ∀ q ∈ R, q ∈ L := by
  intro k
  induction k with
  | zero =>
    intro z B p L R hL0 h hr
    simp only [coverL] at h
    obtain ⟨hp, hR⟩ := pop_spec h
    have := hL p (hL0 p hp)
    exact ⟨by simpa [sub, hr] using this, hR⟩
  | succ k ih =>
    intro z B p L R hL0 h hr
    simp only [coverL] at h
    cases hpop : pop p L with
    | some r =>
      rw [hpop] at h
      cases h
      obtain ⟨hp, hR⟩ := pop_spec hpop
      have := hL p (hL0 p hp)
      exact ⟨by simpa [sub, hr] using this, hR⟩
    | none =>
      rw [hpop] at h
      simp only at h
      split_ifs at h with hst hB hg
      · cases h
        have hs : ¬ k + 1 ≤ stop := by omega
        exact ⟨by simp only [enumAuxS, hs, hB, ↓reduceIte], fun q hq => hq⟩
      · have hs : ¬ k + 1 ≤ stop := by omega
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        obtain ⟨⟨h1, h2⟩, h3⟩ := hg
        obtain ⟨hall, hR⟩ := foldRange_spec
          (P := fun L' => ∀ q ∈ L', q ∈ L)
          (Q := fun t => enumAuxS a w n stop leaf k (Function.update z k t)
            (B - w k * (a k k * t + cent a n k z) ^ 2) = true)
          (fun t x y hx hfy => by
            have hr' : replay a w n s₀ (p ++ [t]) = (k, Function.update z k t,
                B - w k * (a k k * t + cent a n k z) ^ 2) := by
              rw [replay_snoc, hr, step]
            obtain ⟨he, hy⟩ := ih _ _ _ x y (fun q hq => hL0 q (hx q hq)) hfy hr'
            exact ⟨he, fun q hq => hx q (hy q hq)⟩)
          _ _ L R (fun q hq => hq) h
        refine ⟨?_, hR⟩
        simp only [enumAuxS, hs, hB, ↓reduceIte, h1, h2, h3, decide_true, Bool.and_self]
        exact allRange_of_forall hall

/-- **The glue (linear form).** If the walk consumes `L` without failing and every subtree
below a prefix in `L` passes, the whole stopped search passes. -/
theorem enumS_of_coverL {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf : (ℕ → ℤ) → Bool}
    {B : ℤ} {L : List (List ℤ)} (hc : (coverL a w n stop n (fun _ => 0) B [] L).isSome = true)
    (hL : ∀ q ∈ L, sub a w n stop leaf (n, fun _ => 0, B) q = true) :
    enumS a w n stop leaf B = true := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hc
  exact (coverL_sound hL n _ B [] L R (fun q hq => hq) hR rfl).1

end ReflectZphi.Split
