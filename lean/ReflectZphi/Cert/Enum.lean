import Mathlib

/-!
# B8 (part 1): a kernel-checkable Fincke–Pohst enumerator over `ℤⁿ`

The certificate writes a positive definite integer quadratic form as a sum of weighted
squares of triangular integer linear forms,
`S · zᵀ A z = ∑_{i<n} wᵢ (Lᵢ z)²`, `Lᵢ z = ∑_{j ≥ i} a i j · z j`.
`enum` visits every `z` with `∑ wᵢ (Lᵢ z)² ≤ B` (from the last coordinate down) and
evaluates a Boolean `leaf` on it; `enum_sound` says that if `enum` returns `true`, then
`leaf z = true` for every such `z`.

Nothing about the search needs proving except the interval bounds:
* integer square roots come from Newton's iteration (`isqrt`), and the enumerator checks
  `B < w (s+1)²` itself, so the iteration's correctness is not needed;
* the interval of `z k` is `[(−s − c)/a, (s − c)/a]` (floor division, `a > 0`).

`quadCheck` checks the identity `S · A = ∑ wᵢ aᵢᵀ aᵢ` coefficientwise, and
`quadCheck_sound` turns it into the identity of quadratic forms.
-/

namespace ReflectZphi.Enum

/-- `∑_{j<m} f j`, by structural recursion (fast in the kernel). -/
def lsum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => lsum f m + f m

lemma lsum_eq (f : ℕ → ℤ) (m : ℕ) : lsum f m = ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => rfl
  | succ m ih => rw [lsum, ih, Finset.sum_range_succ]

/-- Newton's iteration for `⌊√n⌋` (with fuel). Its correctness is never used. -/
def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | fuel + 1, n, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtAux fuel n y else x

/-- Bisection for the bit length: the smallest `h ∈ (lo, hi]` with `n >>> h = 0`, provided
`n >>> hi = 0` (with fuel). Only a starting point for Newton; its correctness is never used.
(`Nat.log2` is not evaluated natively by the kernel; `>>>` is.) -/
def blen : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, hi => hi
  | fuel + 1, n, lo, hi =>
    if hi ≤ lo + 1 then hi else
    let m := (lo + hi) / 2
    if n >>> m = 0 then blen fuel n lo m else blen fuel n m hi

/-- `⌊√n⌋` for `n < 2^4096`, by Newton from `2^(bitlen/2 + 1) ≥ √n`. -/
def isqrt (n : ℕ) : ℕ := if n = 0 then 0 else isqrtAux 256 n (1 <<< (blen 16 n 0 4096 / 2 + 1))

/-- `f t` for `t = lo, lo+1, …, lo+len-1`. -/
def allRange (f : ℤ → Bool) : ℤ → ℕ → Bool
  | _, 0 => true
  | lo, len + 1 => f lo && allRange f (lo + 1) len

lemma allRange_spec {f : ℤ → Bool} {lo : ℤ} {len : ℕ} (h : allRange f lo len = true) :
    ∀ t, lo ≤ t → t < lo + len → f t = true := by
  induction len generalizing lo with
  | zero => intro t h1 h2; push_cast at h2; omega
  | succ len ih =>
    simp only [allRange, Bool.and_eq_true] at h
    intro t h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih h.2 t (by omega) (by push_cast at h2 ⊢; omega)

/-- Row `i` of the triangular system: `∑_{i ≤ j < n} a i j z j`. -/
def Lrow (a : ℕ → ℕ → ℤ) (n i : ℕ) (z : ℕ → ℤ) : ℤ :=
  lsum (fun j => if i ≤ j then a i j * z j else 0) n

/-- The part of row `k` above the diagonal: `∑_{k < j < n} a k j z j`. -/
def cent (a : ℕ → ℕ → ℤ) (n k : ℕ) (z : ℕ → ℤ) : ℤ :=
  lsum (fun j => if k < j then a k j * z j else 0) n

/-- The partial sum `∑_{i<k} wᵢ (Lᵢ z)²`. -/
def psum (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (z : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, w i * Lrow a n i z ^ 2

/-- The enumerator. Level `k` fixes `z k-1, …, z 0`, the coordinates `≥ k` being those of
the current `z`; `B` is the remaining budget. -/
def enumAux (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (leaf : (ℕ → ℤ) → Bool) :
    ℕ → (ℕ → ℤ) → ℤ → Bool
  | 0, z, _ => leaf z
  | k + 1, z, B =>
    if B < 0 then true else
    let c := cent a n k z
    let akk := a k k
    let wk := w k
    let s : ℤ := (isqrt (B.toNat / wk.toNat) : ℕ)
    if decide (B < wk * (s + 1) ^ 2) && decide (0 < akk) && decide (0 < wk) then
      let lo := (-s - c) / akk
      let hi := (s - c) / akk
      allRange (fun t => enumAux a w n leaf k (Function.update z k t)
        (B - wk * (akk * t + c) ^ 2)) lo (hi - lo + 1).toNat
    else false

/-- The whole search, from `z = 0`. -/
def enum (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (leaf : (ℕ → ℤ) → Bool) (B : ℤ) : Bool :=
  enumAux a w n leaf n (fun _ => 0) B

lemma Lrow_split (a : ℕ → ℕ → ℤ) {n k : ℕ} (hk : k < n) {z z₀ : ℕ → ℤ}
    (hz : ∀ j, k < j → z j = z₀ j) :
    Lrow a n k z = a k k * z k + cent a n k z₀ := by
  unfold Lrow cent
  rw [lsum_eq, lsum_eq]
  have e : ∀ j ∈ Finset.range n, (if k ≤ j then a k j * z j else 0) =
      (if k = j then a k k * z k else 0) + (if k < j then a k j * z₀ j else 0) := by
    intro j _
    rcases lt_trichotomy k j with h | rfl | h
    · rw [if_pos h.le, if_neg h.ne, if_pos h, hz j h, zero_add]
    · simp
    · rw [if_neg (by omega), if_neg h.ne', if_neg (by omega), add_zero]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp [Finset.mem_range, hk]

lemma Lrow_congr (a : ℕ → ℕ → ℤ) (n i : ℕ) {z z' : ℕ → ℤ} (hz : ∀ j, i ≤ j → z j = z' j) :
    Lrow a n i z = Lrow a n i z' := by
  unfold Lrow
  rw [lsum_eq, lsum_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [hz j h]
  · rfl

/-- **Soundness of the enumerator** (one level at a time). -/
theorem enumAux_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n : ℕ} {leaf : (ℕ → ℤ) → Bool}
    (hw : ∀ i, i < n → 0 ≤ w i) :
    ∀ k, k ≤ n → ∀ z₀ B, enumAux a w n leaf k z₀ B = true →
      ∀ z : ℕ → ℤ, (∀ j, k ≤ j → z j = z₀ j) → psum a w n z k ≤ B → leaf z = true := by
  intro k
  induction k with
  | zero =>
    intro _ z₀ B h z hz _
    have : z = z₀ := funext fun j => hz j (Nat.zero_le j)
    rw [this]; exact h
  | succ k ih =>
    intro hkn z₀ B h z hz hB
    have hnonneg : ∀ m, m ≤ n → 0 ≤ psum a w n z m := by
      intro m hm
      exact Finset.sum_nonneg fun i hi =>
        mul_nonneg (hw i (by simp at hi; omega)) (sq_nonneg _)
    have hsplit : psum a w n z (k + 1) = psum a w n z k + w k * Lrow a n k z ^ 2 := by
      unfold psum; rw [Finset.sum_range_succ]
    have hBnn : 0 ≤ B := le_trans (hnonneg _ hkn) hB
    simp only [enumAux, not_lt.mpr hBnn, ite_false] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hs, hakk⟩, hwk⟩ := hc
    set c := cent a n k z₀
    set s : ℤ := ((isqrt (B.toNat / (w k).toNat) : ℕ) : ℤ)
    have hL := Lrow_split a (by omega : k < n) (fun j hj => hz j (by omega) : ∀ j, k < j → z j = z₀ j)
    set t := z k
    have hwt : w k * (a k k * t + c) ^ 2 ≤ B := by
      rw [← hL]; have := hnonneg k (by omega); linarith
    -- |a t + c| ≤ s
    have habs : |a k k * t + c| ≤ s := by
      by_contra hcon; push Not at hcon
      have h1 : s + 1 ≤ |a k k * t + c| := hcon
      have h0 : 0 ≤ s + 1 := by positivity
      have h2 : (s + 1) ^ 2 ≤ (a k k * t + c) ^ 2 := by
        rw [← sq_abs (a k k * t + c)]; exact pow_le_pow_left₀ h0 h1 2
      have := mul_le_mul_of_nonneg_left h2 hwk.le
      linarith
    obtain ⟨hab1, hab2⟩ := abs_le.mp habs
    have hlo : (-s - c) / a k k ≤ t := by
      have := Int.ediv_mul_le (-s - c) hakk.ne'
      by_contra hcon; push Not at hcon
      have : a k k * (t + 1) ≤ a k k * ((-s - c) / a k k) :=
        mul_le_mul_of_nonneg_left (by omega) hakk.le
      nlinarith
    have hhi : t ≤ (s - c) / a k k := by
      have := Int.lt_ediv_add_one_mul_self (s - c) hakk
      by_contra hcon; push Not at hcon
      have : a k k * ((s - c) / a k k + 1) ≤ a k k * t :=
        mul_le_mul_of_nonneg_left (by omega) hakk.le
      nlinarith
    have hrange := allRange_spec h t hlo (by
      have : (((s - c) / a k k - (-s - c) / a k k + 1).toNat : ℤ) =
          (s - c) / a k k - (-s - c) / a k k + 1 := Int.toNat_of_nonneg (by omega)
      rw [this]; omega)
    apply ih (by omega) _ _ hrange z
    · intro j hj
      rcases eq_or_lt_of_le hj with rfl | hlt
      · simp [t]
      · rw [Function.update_of_ne (by omega)]; exact hz j (by omega)
    · rw [hsplit, hL] at hB; linarith

theorem enum_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n : ℕ} {leaf : (ℕ → ℤ) → Bool} {B : ℤ}
    (hw : ∀ i, i < n → 0 ≤ w i) (h : enum a w n leaf B = true) (z : ℕ → ℤ)
    (hz : ∀ j, n ≤ j → z j = 0) (hB : psum a w n z n ≤ B) : leaf z = true :=
  enumAux_sound hw n le_rfl _ B h z hz hB

/-! ### The quadratic identity -/

/-- The masked row entries `a' i j = a i j` for `i ≤ j`, else `0`. -/
def am (a : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ := if i ≤ j then a i j else 0

/-- Coefficientwise check of `S · A = ∑ᵢ wᵢ a'ᵢᵀ a'ᵢ` on `[0, n)²`. -/
def quadCheck (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (A : ℕ → ℕ → ℤ) (S : ℤ) : Bool :=
  (List.range n).all fun j => (List.range n).all fun l =>
    S * A j l == lsum (fun i => w i * am a i j * am a i l) n

/-- The quadratic form `zᵀ A z` on `[0, n)`. -/
def qform (A : ℕ → ℕ → ℤ) (n : ℕ) (z : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, A j l * z j * z l

theorem quadCheck_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n : ℕ} {A : ℕ → ℕ → ℤ} {S : ℤ}
    (h : quadCheck a w n A S = true) (z : ℕ → ℤ) :
    psum a w n z n = S * qform A n z := by
  simp only [quadCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hL : ∀ i, Lrow a n i z = ∑ j ∈ Finset.range n, am a i j * z j := by
    intro i; unfold Lrow; rw [lsum_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold am; split_ifs <;> simp
  unfold psum qform
  simp_rw [hL, sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have := h j (Finset.mem_range.mp hj) l (Finset.mem_range.mp hl)
  rw [lsum_eq] at this
  calc ∑ i ∈ Finset.range n, w i * (am a i j * z j * (am a i l * z l))
      = (∑ i ∈ Finset.range n, w i * am a i j * am a i l) * z j * z l := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = S * (A j l * z j * z l) := by rw [← this]; ring


/-! ### Stopping early -/

/-- The enumerator stopped at level `stop`: the coordinates below `stop` are left at their
initial values and `leaf` handles them (for instance by solving for them exactly). -/
def enumAuxS (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n stop : ℕ) (leaf : (ℕ → ℤ) → Bool) :
    ℕ → (ℕ → ℤ) → ℤ → Bool
  | 0, z, _ => leaf z
  | k + 1, z, B =>
    if k + 1 ≤ stop then leaf z else
    if B < 0 then true else
    let c := cent a n k z
    let akk := a k k
    let wk := w k
    let s : ℤ := (isqrt (B.toNat / wk.toNat) : ℕ)
    if decide (B < wk * (s + 1) ^ 2) && decide (0 < akk) && decide (0 < wk) then
      let lo := (-s - c) / akk
      let hi := (s - c) / akk
      allRange (fun t => enumAuxS a w n stop leaf k (Function.update z k t)
        (B - wk * (akk * t + c) ^ 2)) lo (hi - lo + 1).toNat
    else false

/-- `∑_{stop ≤ i < k} wᵢ (Lᵢ z)²`. -/
def psumR (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n : ℕ) (z : ℕ → ℤ) (stop k : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ico stop k, w i * Lrow a n i z ^ 2

theorem enumAuxS_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf : (ℕ → ℤ) → Bool}
    (hw : ∀ i, i < n → 0 ≤ w i) :
    ∀ k, k ≤ n → stop ≤ k → ∀ z₀ B, enumAuxS a w n stop leaf k z₀ B = true →
      ∀ z : ℕ → ℤ, (∀ j, k ≤ j → z j = z₀ j) → psumR a w n z stop k ≤ B →
        leaf (fun j => if stop ≤ j then z j else z₀ j) = true := by
  intro k
  induction k with
  | zero =>
    intro _ hs z₀ B h z hz _
    have : (fun j => if stop ≤ j then z j else z₀ j) = z₀ := by
      funext j; split_ifs <;> first | exact hz j (Nat.zero_le j) | rfl
    rw [this]; exact h
  | succ k ih =>
    intro hkn hsk z₀ B h z hz hB
    by_cases hstop : k + 1 ≤ stop
    · have hst : stop = k + 1 := le_antisymm hsk hstop
      simp only [enumAuxS, hstop, if_true] at h
      have : (fun j => if stop ≤ j then z j else z₀ j) = z₀ := by
        funext j; split_ifs with hj
        · exact hz j (by omega)
        · rfl
      rw [this]; exact h
    have hnonneg : ∀ m, 0 ≤ psumR a w n z stop m := by
      intro m
      exact Finset.sum_nonneg fun i hi => by
        rw [Finset.mem_Ico] at hi
        by_cases hin : i < n
        · exact mul_nonneg (hw i hin) (sq_nonneg _)
        · -- rows beyond `n` vanish
          have : Lrow a n i z = 0 := by
            unfold Lrow; rw [lsum_eq]
            exact Finset.sum_eq_zero fun j hj => by
              rw [Finset.mem_range] at hj; rw [if_neg (by omega)]
          rw [this]; simp
    have hsplit : psumR a w n z stop (k + 1) = psumR a w n z stop k + w k * Lrow a n k z ^ 2 := by
      unfold psumR; rw [Finset.sum_Ico_succ_top (by omega)]
    have hBnn : 0 ≤ B := le_trans (hnonneg _) hB
    simp only [enumAuxS, hstop, if_false, not_lt.mpr hBnn] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hs, hakk⟩, hwk⟩ := hc
    set c := cent a n k z₀
    set s : ℤ := ((isqrt (B.toNat / (w k).toNat) : ℕ) : ℤ)
    have hL := Lrow_split a (by omega : k < n) (fun j hj => hz j (by omega) : ∀ j, k < j → z j = z₀ j)
    set t := z k
    have hwt : w k * (a k k * t + c) ^ 2 ≤ B := by
      rw [← hL]; have := hnonneg k; linarith
    have habs : |a k k * t + c| ≤ s := by
      by_contra hcon; push Not at hcon
      have h1 : s + 1 ≤ |a k k * t + c| := hcon
      have h0 : 0 ≤ s + 1 := by positivity
      have h2 : (s + 1) ^ 2 ≤ (a k k * t + c) ^ 2 := by
        rw [← sq_abs (a k k * t + c)]; exact pow_le_pow_left₀ h0 h1 2
      have := mul_le_mul_of_nonneg_left h2 hwk.le
      linarith
    obtain ⟨hab1, hab2⟩ := abs_le.mp habs
    have hlo : (-s - c) / a k k ≤ t := by
      have := Int.ediv_mul_le (-s - c) hakk.ne'
      by_contra hcon; push Not at hcon
      have : a k k * (t + 1) ≤ a k k * ((-s - c) / a k k) :=
        mul_le_mul_of_nonneg_left (by omega) hakk.le
      nlinarith
    have hhi : t ≤ (s - c) / a k k := by
      have := Int.lt_ediv_add_one_mul_self (s - c) hakk
      by_contra hcon; push Not at hcon
      have : a k k * ((s - c) / a k k + 1) ≤ a k k * t :=
        mul_le_mul_of_nonneg_left (by omega) hakk.le
      nlinarith
    have hrange := allRange_spec h t hlo (by
      have : (((s - c) / a k k - (-s - c) / a k k + 1).toNat : ℤ) =
          (s - c) / a k k - (-s - c) / a k k + 1 := Int.toNat_of_nonneg (by omega)
      rw [this]; omega)
    have key := ih (by omega) (by omega) _ _ hrange z (by
      intro j hj
      rcases eq_or_lt_of_le hj with rfl | hlt
      · simp [t]
      · rw [Function.update_of_ne (by omega)]; exact hz j (by omega)) (by
      rw [hsplit, hL] at hB; linarith)
    have e : (fun j => if stop ≤ j then z j else Function.update z₀ k t j) =
        (fun j => if stop ≤ j then z j else z₀ j) := by
      funext j; split_ifs with hj
      · rfl
      · rw [Function.update_of_ne (by omega)]
    rw [e] at key; exact key

/-- The search stopped at level `stop`, from `z = 0`. -/
def enumS (a : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (n stop : ℕ) (leaf : (ℕ → ℤ) → Bool) (B : ℤ) : Bool :=
  enumAuxS a w n stop leaf n (fun _ => 0) B

theorem enumS_sound {a : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf : (ℕ → ℤ) → Bool}
    {B : ℤ} (hw : ∀ i, i < n → 0 ≤ w i) (hst : stop ≤ n) (h : enumS a w n stop leaf B = true)
    (z : ℕ → ℤ) (hz : ∀ j, n ≤ j → z j = 0) (hB : psum a w n z n ≤ B) :
    leaf (fun j => if stop ≤ j then z j else 0) = true := by
  have hR : psumR a w n z stop n ≤ psum a w n z n := by
    unfold psumR psum
    rw [Finset.range_eq_Ico]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Ico_subset_Ico_left (Nat.zero_le _)
    · intro i hi _
      rw [Finset.mem_Ico] at hi
      exact mul_nonneg (hw i hi.2) (sq_nonneg _)
  exact enumAuxS_sound hw n le_rfl hst _ B h z hz (le_trans hR hB)

end ReflectZphi.Enum
