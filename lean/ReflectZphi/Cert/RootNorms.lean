import ReflectZphi.Lattice.Basic
import ReflectZphi.Ring.Euclid

/-!
# B7: root norms

Every root of `L = (O³, G)` can be rescaled by a unit to a root whose norm `m`
* divides `2 det G` (`root_norm_dvd`, needs `O` a PID),
* lies in the window `ι₂(m) ≤ ι₁(m) < ρ ι₂(m)`, where `ρ = (ι₁ u / ι₂ u)²` for a chosen unit
  `u` with `ρ > 1` (`exists_unit_window`; only that `u` is a unit is used, not that it is
  fundamental).

Rescaling a root by a unit does not change whether it has one sign on a set of vertices
(`oneSign_smul_iff`).

The window and the divisibility bound `m` in an integer box (`window_box`), so all such `m`
lie in a finite list `windowNorms`, computed by the kernel (`mem_windowNorms`).
-/

namespace ReflectZphi.RootNorms

open Matrix QuadraticAlgebra ReflectZphi.Lattice

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-! ### The embeddings -/

section embed

variable (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a)

lemma ι₁_apply (z : O a b) :
    ι₁ hd z = z.re + z.im * ((b + Real.sqrt ((b : ℝ) ^ 2 + 4 * a)) / 2) := by
  simp only [ι₁, emb_apply, root]; push_cast; ring

lemma ι₂_apply (z : O a b) :
    ι₂ hd z = z.re + z.im * ((b - Real.sqrt ((b : ℝ) ^ 2 + 4 * a)) / 2) := by
  simp only [ι₂, emb_apply, root]; push_cast; ring

/-- `ι₂ = ι₁ ∘ σ`. -/
lemma ι₂_eq_ι₁_star (z : O a b) : ι₂ hd z = ι₁ hd (star z) := by
  rw [ι₂_apply, ι₁_apply, re_star, im_star]; push_cast; ring

/-- The norm is the product of the two embeddings. -/
lemma norm_eq_mul (z : O a b) : ((Nm z : ℤ) : ℝ) = ι₁ hd z * ι₂ hd z := by
  rw [ι₁_apply, ι₂_apply, QuadraticAlgebra.norm_def]
  have h := Real.mul_self_sqrt hd
  push_cast
  linear_combination ((z.im : ℝ) ^ 2 / 4) * h

/-- The difference of the embeddings. -/
lemma ι₁_sub_ι₂ (z : O a b) :
    ι₁ hd z - ι₂ hd z = z.im * Real.sqrt ((b : ℝ) ^ 2 + 4 * a) := by
  rw [ι₁_apply, ι₂_apply]; ring

/-- The sum of the embeddings. -/
lemma ι₁_add_ι₂ (z : O a b) : ι₁ hd z + ι₂ hd z = ((2 * z.re + b * z.im : ℤ) : ℝ) := by
  rw [ι₁_apply, ι₂_apply]; push_cast; ring

lemma ι_ne_zero_of_isUnit (ι : O a b →+* ℝ) {u : O a b} (hu : IsUnit u) : ι u ≠ 0 :=
  (hu.map ι).ne_zero

end embed

/-! ### Bilinearity -/

lemma bil_smul_left (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : O a b) (x y : Fin 3 → O a b) :
    bil G (c • x) y = c * bil G x y := by
  simp [bil, smul_dotProduct]

lemma bil_smul_right (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : O a b) (x y : Fin 3 → O a b) :
    bil G x (c • y) = c * bil G x y := by
  simp [bil, mulVec_smul, dotProduct_smul]

/-! ### `m ∣ 2 det G` -/

/-- In a PID, a primitive vector has a unimodular combination. -/
lemma exists_comb_eq_one [IsPrincipalIdealRing (O a b)] {r : Fin 3 → O a b}
    (hr : Primitive r) : ∃ s : Fin 3 → O a b, ∑ k, s k * r k = 1 := by
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range r))).principal
  have hdiv : ∀ k, g ∣ r k := by
    intro k
    have : r k ∈ Ideal.span (Set.range r) := Ideal.subset_span ⟨k, rfl⟩
    rw [hg] at this
    exact Ideal.mem_span_singleton.mp this
  have hu := hr g hdiv
  have htop : Ideal.span (Set.range r) = ⊤ := by
    rw [hg]; exact (Ideal.span_singleton_eq_top).mpr hu
  have h1 : (1 : O a b) ∈ Ideal.span (Set.range r) := by rw [htop]; trivial
  exact (Ideal.mem_span_range_iff_exists_fun).mp h1

/-- `m ∣ c rₖ` for all `k` and `r` primitive give `m ∣ c`. -/
lemma dvd_of_dvd_mul_primitive [IsPrincipalIdealRing (O a b)] {r : Fin 3 → O a b}
    (hr : Primitive r) {m c : O a b} (h : ∀ k, m ∣ c * r k) : m ∣ c := by
  obtain ⟨s, hs⟩ := exists_comb_eq_one hr
  have : c = ∑ k, s k * (c * r k) := by
    calc c = c * ∑ k, s k * r k := by rw [hs, mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k) _

/-- **The norm of a root divides `2 det G`.** -/
theorem root_norm_dvd [IsPrincipalIdealRing (O a b)] {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a}
    {G : Matrix (Fin 3) (Fin 3) (O a b)} {r : Fin 3 → O a b} (hr : IsRoot hd G r) :
    bil G r r ∣ 2 * G.det := by
  apply dvd_of_dvd_mul_primitive hr.primitive
  intro k
  have h := hr.dvd (G.adjugate *ᵥ Pi.single k 1)
  have : bil G r (G.adjugate *ᵥ Pi.single k 1) = G.det * r k := by
    simp only [bil, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, dotProduct_smul,
      dotProduct_single, mul_one, smul_eq_mul]
  rw [this, ← mul_assoc] at h
  exact h

/-! ### Rescaling by a unit -/

theorem isRoot_smul {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a} {G : Matrix (Fin 3) (Fin 3) (O a b)}
    {r : Fin 3 → O a b} (hr : IsRoot hd G r) {u : O a b} (hu : IsUnit u) :
    IsRoot hd G (u • r) := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    apply hr.primitive c
    intro k
    have := hc k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have e : r k = ((v⁻¹ : (O a b)ˣ) : O a b) * ((v : O a b) * r k) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]; exact dvd_mul_of_dvd_right this _
  · have e : bil G ((v : O a b) • r) ((v : O a b) • r) = (v : O a b) * v * bil G r r := by
      rw [bil_smul_left, bil_smul_right]; ring
    rw [e]
    have h1 := ι_ne_zero_of_isUnit (ι₁ hd) v.isUnit
    have h2 := ι_ne_zero_of_isUnit (ι₂ hd) v.isUnit
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul]; exact mul_pos (mul_self_pos.mpr h1) hr.totPos.1
    · rw [map_mul, map_mul]; exact mul_pos (mul_self_pos.mpr h2) hr.totPos.2
  · intro x
    obtain ⟨t, ht⟩ := hr.dvd x
    refine ⟨((v⁻¹ : (O a b)ˣ) : O a b) * t, ?_⟩
    rw [bil_smul_left, bil_smul_left, bil_smul_right]
    have : 2 * ((v : O a b) * bil G r x) = (v : O a b) * (2 * bil G r x) := by ring
    rw [this, ht]
    have hv : (v : O a b) * ((v⁻¹ : (O a b)ˣ) : O a b) = 1 := Units.mul_inv v
    linear_combination (-(v : O a b) * bil G r r * t) * hv

/-- One sign on the vertices `Ps 0, …, Ps (n-1)` at `ι₁`. -/
def OneSign (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ)
    (Ps : ℕ → Fin 3 → O a b) (r : Fin 3 → O a b) : Prop :=
  (∀ i, i < n → ι₁ hd (bil G r (Ps i)) ≤ 0) ∨ (∀ i, i < n → 0 ≤ ι₁ hd (bil G r (Ps i)))

lemma oneSign_smul_iff {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a} {G : Matrix (Fin 3) (Fin 3) (O a b)}
    {n : ℕ} {Ps : ℕ → Fin 3 → O a b} {r : Fin 3 → O a b} {u : O a b} (hu : IsUnit u) :
    OneSign hd G n Ps (u • r) ↔ OneSign hd G n Ps r := by
  have hne := ι_ne_zero_of_isUnit (ι₁ hd) hu
  simp only [OneSign, bil_smul_left, map_mul]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have e1 : ∀ x : ℝ, ι₁ hd u * x ≤ 0 ↔ 0 ≤ x := fun x => by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    have e2 : ∀ x : ℝ, 0 ≤ ι₁ hd u * x ↔ x ≤ 0 := fun x => by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    simp only [e1, e2]; exact or_comm
  · have e1 : ∀ x : ℝ, ι₁ hd u * x ≤ 0 ↔ x ≤ 0 := fun x => by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    have e2 : ∀ x : ℝ, 0 ≤ ι₁ hd u * x ↔ 0 ≤ x := fun x => by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    simp only [e1, e2]

/-! ### The window -/

/-- **Window.** If `u` is a unit with `ι₂(u)² < ι₁(u)²` (so `ρ = (ι₁ u/ι₂ u)² > 1`), every root
has a unit multiple `r'` whose norm `m` satisfies `ι₂ m ≤ ι₁ m < ρ ι₂ m`. -/
theorem exists_unit_window {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a}
    {G : Matrix (Fin 3) (Fin 3) (O a b)} {r : Fin 3 → O a b} (hr : IsRoot hd G r)
    {u : O a b} (hu : IsUnit u) (hρ : ι₂ hd u ^ 2 < ι₁ hd u ^ 2) :
    ∃ v : O a b, IsUnit v ∧
      ι₂ hd (bil G (v • r) (v • r)) ≤ ι₁ hd (bil G (v • r) (v • r)) ∧
      ι₂ hd u ^ 2 * ι₁ hd (bil G (v • r) (v • r)) <
        ι₁ hd u ^ 2 * ι₂ hd (bil G (v • r) (v • r)) := by
  obtain ⟨U, rfl⟩ := hu
  set m := bil G r r
  have hm1 := hr.totPos.1
  have hm2 := hr.totPos.2
  have h1 := ι_ne_zero_of_isUnit (ι₁ hd) U.isUnit
  have h2 := ι_ne_zero_of_isUnit (ι₂ hd) U.isUnit
  set x1 := ι₁ hd (U : O a b)
  set x2 := ι₂ hd (U : O a b)
  have hx2 : 0 < x2 ^ 2 := by positivity
  set ρ := x1 ^ 2 / x2 ^ 2
  have hρ1 : 1 < ρ := by rw [lt_div_iff₀ hx2, one_mul]; exact hρ
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (div_pos hm1 hm2) hρ1
  refine ⟨((U ^ (-k) : (O a b)ˣ) : O a b), (U ^ (-k)).isUnit, ?_⟩
  have hmap : ∀ ι : O a b →+* ℝ, ι ((U ^ (-k) : (O a b)ˣ) : O a b) = (ι U) ^ (-k) := by
    intro ι
    have : ι ((U ^ (-k) : (O a b)ˣ) : O a b) =
        ((Units.map (ι : O a b →* ℝ) (U ^ (-k)) : ℝˣ) : ℝ) := rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have e : bil G (((U ^ (-k) : (O a b)ˣ) : O a b) • r) (((U ^ (-k) : (O a b)ˣ) : O a b) • r) =
      ((U ^ (-k) : (O a b)ˣ) : O a b) * ((U ^ (-k) : (O a b)ˣ) : O a b) * m := by
    rw [bil_smul_left, bil_smul_right]; ring
  rw [e, map_mul, map_mul, map_mul, map_mul, hmap, hmap]
  have sqz : ∀ x : ℝ, x ^ (-k) * x ^ (-k) = (x ^ 2) ^ (-k) := fun x => by
    rw [← mul_zpow, sq]
  rw [sqz, sqz, _root_.zpow_neg, _root_.zpow_neg]
  have hA : 0 < x1 ^ 2 := by positivity
  set A := x1 ^ 2
  set B := x2 ^ 2
  have hP : 0 < A ^ k := zpow_pos hA k
  have hQ : 0 < B ^ k := zpow_pos hx2 k
  rw [div_zpow] at hk1
  rw [zpow_add_one₀ (by positivity), div_zpow] at hk2
  rw [div_le_div_iff₀ hQ hm2] at hk1
  have hk2' : ι₁ hd m * (B ^ k * B) < A ^ k * A * ι₂ hd m := by
    have := hk2
    rw [div_mul_div_comm, div_lt_div_iff₀ hm2 (by positivity)] at this
    linarith
  constructor
  · rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ hQ hP]; linarith
  · rw [inv_mul_eq_div, inv_mul_eq_div, mul_div_assoc', mul_div_assoc',
      div_lt_div_iff₀ hP hQ]
    nlinarith


/-! ### Exact codes -/

/-- A computable consequence of `m ∣ z`: the coordinates of `z σ(m)` are divisible by `N m`. -/
def dvdCode (m z : O a b) : Bool :=
  Nm m != 0 && (z * star m).re % Nm m == 0 && (z * star m).im % Nm m == 0

lemma dvdCode_of_dvd {m z : O a b} (hm : Nm m ≠ 0) (h : m ∣ z) : dvdCode m z = true := by
  obtain ⟨c, rfl⟩ := h
  have e : m * c * star m = c * (algebraMap ℤ (O a b) (Nm m)) := by
    rw [algebraMap_norm_eq_mul_star]; ring
  simp only [dvdCode, e, bne_iff_ne, ne_eq, hm, not_false_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · simp [re_mul]
  · simp [im_mul]

/-! ### The box -/

/-- **Box.** A totally positive divisor `m` of `D ≠ 0` in the window
`ι₂ m ≤ ι₁ m`, `q ι₁ m < p ι₂ m` has `y = m.im ≥ 0`, `s = 2 m.re + b m.im > 0` and
`q d y² < p |N D|`, `q s² < 4 p |N D|` (`d = b² + 4a`). -/
theorem window_box [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {m D : O a b}
    (hD : D ≠ 0) (hdvd : m ∣ D) (h2 : 0 < ι₂ hd0.le m) (hle : ι₂ hd0.le m ≤ ι₁ hd0.le m)
    {p q : ℤ} (hq : 0 < q) (hwin : q * ι₁ hd0.le m < p * ι₂ hd0.le m) :
    0 ≤ m.im ∧ q * (b ^ 2 + 4 * a) * m.im ^ 2 < p * |Nm D| ∧
      0 < 2 * m.re + b * m.im ∧ q * (2 * m.re + b * m.im) ^ 2 < 4 * p * |Nm D| := by
  set n1 := ι₁ hd0.le m
  set n2 := ι₂ hd0.le m
  have h1 : 0 < n1 := lt_of_lt_of_le h2 hle
  have hND : Nm D ≠ 0 := fun h => hD ((nm_eq_zero_iff D).mp h)
  have hNm : Nm m ∣ Nm D := map_dvd _ hdvd
  have hle' : |Nm m| ≤ |Nm D| :=
    Int.le_of_dvd (abs_pos.mpr hND) ((abs_dvd_abs _ _).mpr hNm)
  have hNmR : ((Nm m : ℤ) : ℝ) = n1 * n2 := norm_eq_mul hd0.le m
  have hNpos : 0 < n1 * n2 := mul_pos h1 h2
  have hND' : n1 * n2 ≤ ((|Nm D| : ℤ) : ℝ) := by
    have : ((Nm m : ℤ) : ℝ) ≤ |((Nm m : ℤ) : ℝ)| := le_abs_self _
    have h3 : ((|Nm m| : ℤ) : ℝ) ≤ ((|Nm D| : ℤ) : ℝ) := by exact_mod_cast hle'
    push_cast at h3 ⊢
    linarith
  have hdiff := ι₁_sub_ι₂ hd0.le m
  have hsum := ι₁_add_ι₂ hd0.le m
  have ht : 0 < Real.sqrt ((b : ℝ) ^ 2 + 4 * a) := Real.sqrt_pos.mpr hd0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwin' : q * (n1 * n1) < p * (n1 * n2) := by nlinarith
  have hy : (0 : ℝ) ≤ m.im := by
    by_contra h; push Not at h
    have := mul_neg_of_neg_of_pos h ht
    linarith
  refine ⟨by exact_mod_cast hy, ?_, ?_, ?_⟩
  · have : (q : ℝ) * ((b : ℝ) ^ 2 + 4 * a) * (m.im : ℝ) ^ 2 < p * ((|Nm D| : ℤ) : ℝ) := by
      have e : ((b : ℝ) ^ 2 + 4 * a) * (m.im : ℝ) ^ 2 = (n1 - n2) ^ 2 := by
        rw [hdiff, mul_pow, Real.sq_sqrt hd0.le]; ring
      have hpR : (0 : ℝ) ≤ p := by
        by_contra h; push Not at h; nlinarith
      calc (q : ℝ) * ((b : ℝ) ^ 2 + 4 * a) * (m.im : ℝ) ^ 2 = q * (n1 - n2) ^ 2 := by
            rw [mul_assoc, e]
        _ ≤ q * (n1 * n1) := by
            apply mul_le_mul_of_nonneg_left _ hqR.le; nlinarith
        _ < p * (n1 * n2) := hwin'
        _ ≤ p * ((|Nm D| : ℤ) : ℝ) := mul_le_mul_of_nonneg_left hND' hpR
    exact_mod_cast this
  · have : (0 : ℝ) < ((2 * m.re + b * m.im : ℤ) : ℝ) := by rw [← hsum]; exact add_pos h1 h2
    exact_mod_cast this
  · have hpR : (0 : ℝ) ≤ p := by
      by_contra h; push Not at h; nlinarith
    have : (q : ℝ) * ((2 * m.re + b * m.im : ℤ) : ℝ) ^ 2 < 4 * p * ((|Nm D| : ℤ) : ℝ) := by
      rw [← hsum]
      have hsq : (n1 + n2) ^ 2 ≤ 4 * (n1 * n1) := by nlinarith
      calc (q : ℝ) * (n1 + n2) ^ 2 ≤ 4 * (q * (n1 * n1)) := by
            nlinarith [mul_le_mul_of_nonneg_left hsq hqR.le]
        _ < 4 * (p * (n1 * n2)) := by linarith
        _ ≤ 4 * p * ((|Nm D| : ℤ) : ℝ) := by nlinarith
    exact_mod_cast this

/-- `q ι₁ m < p ι₂ m`, decided exactly (`ι₁` of `p σ(m) − q m`). -/
def winCode (p q : ℤ) (m : O a b) : Bool :=
  posCode (2 * (p * (m.re + b * m.im) - q * m.re) + b * (-(p + q) * m.im)) (-(p + q) * m.im)
    (b ^ 2 + 4 * a)

/-- The candidate norms: all `m = ((s - b y)/2) + y ω` with `y < Y`, `0 < s < S` in the box,
`ι₂ m > 0` (by `posCode`) and `dvdCode m D`. Computed by the kernel. -/
def windowNorms (a b : ℤ) (D : O a b) (p q : ℤ) (Y S : ℕ) : List (O a b) :=
  (List.range Y).flatMap fun (y : ℕ) => (List.range S).filterMap fun (s : ℕ) =>
    let yi : ℤ := y
    let si : ℤ := s
    let m : O a b := ⟨(si - b * yi) / 2, yi⟩
    if (si - b * yi) % 2 == 0 && 0 < si &&
        decide (q * (b ^ 2 + 4 * a) * yi ^ 2 < p * |Nm D|) &&
        decide (q * si ^ 2 < 4 * p * |Nm D|) &&
        posCode si (-yi) (b ^ 2 + 4 * a) &&
        winCode p q m && dvdCode m D
    then some m else none

theorem mem_windowNorms [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {m D : O a b}
    (hD : D ≠ 0) (hdvd : m ∣ D) (h2 : 0 < ι₂ hd0.le m) (hle : ι₂ hd0.le m ≤ ι₁ hd0.le m)
    {p q : ℤ} (hq : 0 < q) (hwin : q * ι₁ hd0.le m < p * ι₂ hd0.le m) {Y S : ℕ}
    (hY : p * |Nm D| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS : 4 * p * |Nm D| ≤ q * (S : ℤ) ^ 2) :
    m ∈ windowNorms a b D p q Y S := by
  obtain ⟨hy, hyb, hs, hsb⟩ := window_box hd0 hD hdvd h2 hle hq hwin
  have hdZ : 0 < b ^ 2 + 4 * a := by exact_mod_cast hd0
  set y := m.im
  set s := 2 * m.re + b * m.im
  have hyY : y < Y := by
    by_contra h; push Not at h
    have : (Y : ℤ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have : q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2 ≤ q * (b ^ 2 + 4 * a) * y ^ 2 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hsS : s < S := by
    by_contra h; push Not at h
    have : (S : ℤ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have : q * (S : ℤ) ^ 2 ≤ q * s ^ 2 := mul_le_mul_of_nonneg_left this hq.le
    linarith
  have hpos : posCode s (-y) (b ^ 2 + 4 * a) = true := by
    have h := (emb_pos_iff hd0 (by norm_num : (-1 : ℤ) * -1 = 1) m).mp h2
    simpa [s, y] using h
  have hND : Nm D ≠ 0 := fun h => hD ((nm_eq_zero_iff D).mp h)
  have hNm : Nm m ≠ 0 := by
    intro h; have := (nm_eq_zero_iff m).mp h; rw [this, map_zero] at h2; exact lt_irrefl _ h2
  have hdc := dvdCode_of_dvd hNm hdvd
  have hwc : winCode p q m = true := by
    have hz : 0 < ι₁ hd0.le ((p : O a b) * star m - (q : O a b) * m) := by
      rw [map_sub, map_mul, map_mul, ← ι₂_eq_ι₁_star, map_intCast, map_intCast]; linarith
    have h := (emb_pos_iff hd0 (by norm_num : (1 : ℤ) * 1 = 1) _).mp hz
    have e1 : 2 * ((p : O a b) * star m - (q : O a b) * m).re +
        b * ((p : O a b) * star m - (q : O a b) * m).im =
        2 * (p * (m.re + b * m.im) - q * m.re) + b * (-(p + q) * m.im) := by
      simp only [re_sub, im_sub, re_mul, im_mul, re_intCast, im_intCast, re_star, im_star,
        Int.cast_id]
      ring
    have e2 : 1 * ((p : O a b) * star m - (q : O a b) * m).im = -(p + q) * m.im := by
      simp only [re_sub, im_sub, re_mul, im_mul, re_intCast, im_intCast, re_star, im_star,
        Int.cast_id]
      ring
    rw [e1, e2] at h; exact h
  unfold windowNorms
  rw [List.mem_flatMap]
  have ey : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
  have es : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs.le
  refine ⟨y.toNat, ?_, ?_⟩
  · apply List.mem_range.mpr
    have h := hyY; rw [← ey] at h; exact_mod_cast h
  rw [List.mem_filterMap]
  refine ⟨s.toNat, ?_, ?_⟩
  · apply List.mem_range.mpr
    have h := hsS; rw [← es] at h; exact_mod_cast h
  have em : (⟨(s - b * y) / 2, y⟩ : O a b) = m := by
    ext
    · show (2 * m.re + b * m.im - b * m.im) / 2 = m.re; omega
    · rfl
  simp only [ey, es, em, hdc, hpos, hyb, hsb, hs, decide_true, Bool.and_true, Bool.true_and,
    beq_iff_eq, hwc]
  have : (s - b * y) % 2 = 0 := by show (2 * m.re + b * m.im - b * m.im) % 2 = 0; omega
  simp [this]

/-- **B7.** Every root has a unit multiple, a root with the same one-sign behaviour, whose
norm is in `windowNorms a b (2 det G) p q Y S`. Hypotheses: `O` a PID domain; a unit `u`
with `ι₂(u)² < ι₁(u)²` and `q ι₁(u)² ≤ p ι₂(u)²` (so `1 < ρ ≤ p/q`); `Y`, `S` large
enough; `det G ≠ 0`. -/
theorem exists_root_in_window [IsDomain (O a b)] [IsPrincipalIdealRing (O a b)]
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS : 4 * p * |Nm (2 * G.det)| ≤ q * (S : ℤ) ^ 2) {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {r : Fin 3 → O a b} (hr : IsRoot hd0.le G r) :
    ∃ r', IsRoot hd0.le G r' ∧ (OneSign hd0.le G n Ps r' ↔ OneSign hd0.le G n Ps r) ∧
      bil G r' r' ∈ windowNorms a b (2 * G.det) p q Y S := by
  obtain ⟨v, hv, hle, hlt⟩ := exists_unit_window hr hu hρ
  have hr' := isRoot_smul hr hv
  refine ⟨v • r, hr', oneSign_smul_iff hv, ?_⟩
  have hu2 : 0 < ι₂ hd0.le u ^ 2 := by
    have := ι_ne_zero_of_isUnit (ι₂ hd0.le) hu; positivity
  have hm2 := hr'.totPos.2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply mem_windowNorms hd0 hG (root_norm_dvd hr') hm2 hle hq _ hY hS
  have : ι₂ hd0.le u ^ 2 * (q * ι₁ hd0.le (bil G (v • r) (v • r))) <
      ι₂ hd0.le u ^ 2 * (p * ι₂ hd0.le (bil G (v • r) (v • r))) := by
    nlinarith
  exact lt_of_mul_lt_mul_left this hu2.le

end ReflectZphi.RootNorms
