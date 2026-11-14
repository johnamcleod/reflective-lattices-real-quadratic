import ReflectZphi.Cert.Crossing
import ReflectZphi.Cert.Enum
import ReflectZphi.Cert.QuadSolve

/-!
# B8 (part 3): every root has one sign on the vertices (`hone`)

For a certified polygon, a root `r` whose mirror crosses it (rescaled by B7 so that its
norm `m` is in `windowNorms`) satisfies `Tr ψ(r) ≤ K`, where
`ψ(x, y) = 2q (x·V)(y·V) + (μ − q V·V)(x·y)` (`psiB`) and `K` bounds
`ι₁((2p − q) m (−V·V) + μ m) + ι₂(q m V·V + μ m)` over the window norms.
`Tr ψ` is an integer quadratic form on the coordinates `z ∈ ℤ⁶` of `r`, and the
certificate writes it (after a unimodular change `U`) as a sum of weighted squares, so
`enum` visits `r`. The leaf check then shows that `r` is not a root or has one sign:
a contradiction, which proves `hone_of_enum`.
-/

namespace ReflectZphi.PolyEnum

open Matrix QuadraticAlgebra ReflectZphi.Lattice ReflectZphi.Bridge ReflectZphi.RootNorms
  ReflectZphi.Crossing ReflectZphi.Enum ReflectZphi.QuadSolve

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-! ### Explicit forms (fast in the kernel) -/

/-- `bil G x y`, written out. -/
def bilE (G : Matrix (Fin 3) (Fin 3) (O a b)) (x y : Fin 3 → O a b) : O a b :=
  x 0 * (G 0 0 * y 0 + G 0 1 * y 1 + G 0 2 * y 2) +
    x 1 * (G 1 0 * y 0 + G 1 1 * y 1 + G 1 2 * y 2) +
    x 2 * (G 2 0 * y 0 + G 2 1 * y 1 + G 2 2 * y 2)

lemma bilE_eq (G : Matrix (Fin 3) (Fin 3) (O a b)) (x y : Fin 3 → O a b) :
    bilE G x y = bil G x y := by
  simp [bilE, bil, dotProduct, mulVec, Fin.sum_univ_three]

/-- The vector of `O³` with integer coordinates `z 0, …, z 5`. -/
def vecOf (z : ℕ → ℤ) : Fin 3 → O a b := ![⟨z 0, z 1⟩, ⟨z 2, z 3⟩, ⟨z 4, z 5⟩]

/-- The coordinates of a vector (zero from index 6 on). -/
def coords (r : Fin 3 → O a b) : ℕ → ℤ
  | 0 => (r 0).re
  | 1 => (r 0).im
  | 2 => (r 1).re
  | 3 => (r 1).im
  | 4 => (r 2).re
  | 5 => (r 2).im
  | _ => 0

lemma vecOf_coords (r : Fin 3 → O a b) : vecOf (coords r) = r := by
  funext k; fin_cases k <;> rfl

lemma coords_ge (r : Fin 3 → O a b) (j : ℕ) (hj : 6 ≤ j) : coords r j = 0 := by
  match j, hj with
  | j + 6, _ => rfl

/-- The `ℤ`-basis `e₀, ωe₀, e₁, ωe₁, e₂, ωe₂`. -/
def basisVec (j : ℕ) : Fin 3 → O a b := vecOf fun i => if i = j then 1 else 0

lemma vecOf_eq_sum (z : ℕ → ℤ) :
    vecOf (a := a) (b := b) z = ∑ j ∈ Finset.range 6, (z j : O a b) • basisVec j := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases k <;>
    · simp only [vecOf, basisVec, Finset.sum_range_succ, Finset.sum_range_zero]
      ext <;> simp

/-! ### The majorant `ψ` and its trace form -/

/-- `ψ(x, y) = 2q (x·V)(y·V) + (μ − q V·V)(x·y)`. -/
def psiB (G : Matrix (Fin 3) (Fin 3) (O a b)) (V : Fin 3 → O a b) (μ : O a b) (q : ℤ)
    (x y : Fin 3 → O a b) : O a b :=
  2 * q * bilE G x V * bilE G y V + (μ - q * bilE G V V) * bilE G x y

lemma bil_add_left (G : Matrix (Fin 3) (Fin 3) (O a b)) (x x' y : Fin 3 → O a b) :
    bil G (x + x') y = bil G x y + bil G x' y := by simp [bil, add_dotProduct]

lemma bil_add_right (G : Matrix (Fin 3) (Fin 3) (O a b)) (x y y' : Fin 3 → O a b) :
    bil G x (y + y') = bil G x y + bil G x y' := by simp [bil, mulVec_add, dotProduct_add]

/-- `psiB` as an `O`-bilinear map. -/
def psiL (G : Matrix (Fin 3) (Fin 3) (O a b)) (V : Fin 3 → O a b) (μ : O a b) (q : ℤ) :
    (Fin 3 → O a b) →ₗ[O a b] (Fin 3 → O a b) →ₗ[O a b] O a b :=
  LinearMap.mk₂ (O a b) (psiB G V μ q)
    (fun x x' y => by simp only [psiB, bilE_eq, bil_add_left, bil_add_right]; ring)
    (fun c x y => by simp only [psiB, bilE_eq, bil_smul_left, bil_smul_right, smul_eq_mul]; ring)
    (fun x y y' => by simp only [psiB, bilE_eq, bil_add_left, bil_add_right]; ring)
    (fun c x y => by simp only [psiB, bilE_eq, bil_smul_left, bil_smul_right, smul_eq_mul]; ring)

/-- The Gram matrix of `Tr ψ` on the `ℤ`-basis. -/
def traceGram (G : Matrix (Fin 3) (Fin 3) (O a b)) (V : Fin 3 → O a b) (μ : O a b) (q : ℤ)
    (j l : ℕ) : ℤ :=
  trace (psiB G V μ q (basisVec j) (basisVec l))

theorem trace_psi_eq (G : Matrix (Fin 3) (Fin 3) (O a b)) (V : Fin 3 → O a b) (μ : O a b)
    (q : ℤ) (z : ℕ → ℤ) :
    trace (psiB G V μ q (vecOf z) (vecOf z)) = qform (traceGram G V μ q) 6 z := by
  have h : psiB G V μ q (vecOf z) (vecOf z) = psiL G V μ q (vecOf z) (vecOf z) := rfl
  have hexp : psiL G V μ q (vecOf z) (vecOf z) = ∑ j ∈ Finset.range 6, ∑ l ∈ Finset.range 6,
      (z j * z l) • psiL G V μ q (basisVec j) (basisVec l) := by
    rw [vecOf_eq_sum, LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul₂, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_smul, zsmul_eq_mul, smul_eq_mul]
    push_cast; ring
  rw [h, hexp, map_sum]
  unfold qform traceGram
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, smul_eq_mul]
  change z j * z l * trace (psiB G V μ q (basisVec j) (basisVec l)) = _
  ring

/-! ### Unimodular change of coordinates -/

/-- `U z` on `[0, 6)`, zero beyond. -/
def mv (U : ℕ → ℕ → ℤ) (z : ℕ → ℤ) : ℕ → ℤ :=
  fun j => if j < 6 then lsum (fun l => U j l * z l) 6 else 0

/-- `U · Uinv = 1` on `[0, 6)²`. -/
def invCheck (U Uinv : ℕ → ℕ → ℤ) : Bool :=
  (List.range 6).all fun j => (List.range 6).all fun l =>
    lsum (fun t => U j t * Uinv t l) 6 == if j = l then 1 else 0

lemma mv_mv {U Uinv : ℕ → ℕ → ℤ} (h : invCheck U Uinv = true) {z : ℕ → ℤ}
    (hz : ∀ j, 6 ≤ j → z j = 0) : mv U (mv Uinv z) = z := by
  simp only [invCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  funext j
  unfold mv
  split_ifs with hj
  · rw [lsum_eq]
    simp_rw [lsum_eq]
    have : ∀ l ∈ Finset.range 6, U j l * (if l < 6 then ∑ t ∈ Finset.range 6, Uinv l t * z t
        else 0) = ∑ t ∈ Finset.range 6, U j l * Uinv l t * z t := by
      intro l hl
      rw [if_pos (Finset.mem_range.mp hl), Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    have h2 : ∀ t ∈ Finset.range 6, ∑ l ∈ Finset.range 6, U j l * Uinv l t * z t =
        (if j = t then 1 else 0) * z t := by
      intro t ht
      rw [← Finset.sum_mul, ← h j hj t (Finset.mem_range.mp ht), lsum_eq]
    rw [Finset.sum_congr rfl h2]
    simp [Finset.mem_range, hj]
  · rw [hz j (by omega)]

/-- The Gram matrix after the change: `(Uᵀ A U) j l`. -/
def gramU (U : ℕ → ℕ → ℤ) (A : ℕ → ℕ → ℤ) (j l : ℕ) : ℤ :=
  lsum (fun s => lsum (fun t => U s j * A s t * U t l) 6) 6

lemma mv_apply (U : ℕ → ℕ → ℤ) (z : ℕ → ℤ) {j : ℕ} (hj : j ∈ Finset.range 6) :
    mv U z j = ∑ l ∈ Finset.range 6, U j l * z l := by
  unfold mv; rw [if_pos (Finset.mem_range.mp hj), lsum_eq]

lemma qform_gramU (U A : ℕ → ℕ → ℤ) (z : ℕ → ℤ) :
    qform (gramU U A) 6 z = qform A 6 (mv U z) := by
  set F : ℕ → ℕ → ℕ → ℕ → ℤ := fun j l s t => U s j * A s t * U t l * z j * z l
  calc qform (gramU U A) 6 z
      = ∑ j ∈ Finset.range 6, ∑ l ∈ Finset.range 6, ∑ s ∈ Finset.range 6,
          ∑ t ∈ Finset.range 6, F j l s t := by
        unfold qform gramU; simp only [lsum_eq, Finset.sum_mul, F]
    _ = ∑ j ∈ Finset.range 6, ∑ s ∈ Finset.range 6, ∑ t ∈ Finset.range 6,
          ∑ l ∈ Finset.range 6, F j l s t := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ s ∈ Finset.range 6, ∑ t ∈ Finset.range 6, ∑ j ∈ Finset.range 6,
          ∑ l ∈ Finset.range 6, F j l s t := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]
    _ = qform A 6 (mv U z) := by
        unfold qform
        refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
        rw [mv_apply U z hs, mv_apply U z ht, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by simp only [F]; ring

/-! ### The leaf check -/

/-- `0 < ι₁ z`, decided exactly. -/
def pos1 (z : O a b) : Bool := posCode (2 * z.re + b * z.im) z.im (b ^ 2 + 4 * a)

lemma pos1_iff (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) (z : O a b) :
    pos1 z = true ↔ 0 < ι₁ hd0.le z := by
  rw [pos1, ι₁, emb_pos_iff hd0 (by norm_num : (1 : ℤ) * 1 = 1), one_mul]

/-- `(r·G)_k = bil G r eₖ`. -/
def gcol (G : Matrix (Fin 3) (Fin 3) (O a b)) (r : Fin 3 → O a b) (k : Fin 3) : O a b :=
  r 0 * G 0 k + r 1 * G 1 k + r 2 * G 2 k

lemma gcol_eq (G : Matrix (Fin 3) (Fin 3) (O a b)) (r : Fin 3 → O a b) (k : Fin 3) :
    gcol G r k = bil G r (Pi.single k 1) := by
  fin_cases k <;> simp [gcol, bil, dotProduct, mulVec, Fin.sum_univ_three, Pi.single_apply]

/-- The leaf: if the norm `m` of `r` is a window norm, then `r` is not a root
(`m ∤ 2 (r·eₖ)` for some `k`) or has one sign on the vertices. -/
def leafCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (r : Fin 3 → O a b) : Bool :=
  let m := bilE G r r
  !(norms.any fun m' => decide (m = m')) ||
    ((List.range n).all fun i => !pos1 (bilE G r (Ps i))) ||
    ((List.range n).all fun i => !pos1 (-bilE G r (Ps i))) ||
    ((List.finRange 3).any fun k => !dvdCode m (2 * gcol G r k))

lemma leafCheck_sound [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
    {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {norms : List (O a b)} {r : Fin 3 → O a b} (h : leafCheck G n Ps norms r = true)
    (hr : IsRoot hd0.le G r) (hm : bil G r r ∈ norms) : OneSign hd0.le G n Ps r := by
  simp only [leafCheck, bilE_eq, Bool.or_eq_true, List.any_eq_false,
    List.all_eq_true, List.mem_range, List.any_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_true_eq] at h
  have hm0 : bil G r r ≠ 0 := fun h0 => by
    have := hr.totPos.1; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have hN : Nm (bil G r r) ≠ 0 := fun h0 => hm0 ((nm_eq_zero_iff _).mp h0)
  rcases h with ((h | h) | h) | h
  · exact absurd rfl (h _ hm)
  · left; intro i hi
    have := h i hi
    rw [← not_lt, ← pos1_iff hd0]; simpa using this
  · right; intro i hi
    have := h i hi
    have h2 : ¬ 0 < ι₁ hd0.le (-bil G r (Ps i)) := by rw [← pos1_iff hd0]; simpa using this
    rw [map_neg] at h2; linarith
  · obtain ⟨k, -, hk⟩ := h
    rw [gcol_eq] at hk
    rw [dvdCode_of_dvd hN (hr.dvd _)] at hk
    exact absurd hk (by simp)

/-! ### `hone` -/

/-- The bound element `X_m` whose `ι₁` bounds `Tr ψ(r)` for a crossing root of norm `m`. -/
def bndElt (G : Matrix (Fin 3) (Fin 3) (O a b)) (V : Fin 3 → O a b) (μ : O a b) (p q : ℤ)
    (m : O a b) : O a b :=
  (2 * p - q) * m * (-bilE G V V) + μ * m + star (q * m * bilE G V V + μ * m)

/-- **The trace bound.** A root `r` of window norm `m` that takes both signs on the
vertices has `∑ wᵢ (Lᵢ z')² ≤ S K` for its coordinates `z' = U⁻¹ z`. -/
theorem cross_psum (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hadm : Admissible hd0.le G) {n : ℕ} {f : Fin 3 → Fin 3 → O a b}
    {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b} (hc : PolyCert hd0.le G n f rs Ps Xs)
    (hvert : ∀ k i, k < n → i < n → ι₁ hd0.le (bil G (rs k) (Ps i)) ≤ 0)
    {V : Fin 3 → O a b} (hVV : ι₁ hd0.le (bil G V V) < 0)
    (hVs : ι₁ hd0.le (bil G V (f 2)) < 0) {pC qC : ℤ} (hqC : 0 < qC)
    (hC : ∀ i, i < n → (qC : ℝ) * ι₁ hd0.le (bil G V (Ps i)) ^ 2 ≤
      pC * (ι₁ hd0.le (bil G V V) * ι₁ hd0.le (bil G (Ps i) (Ps i))))
    {norms : List (O a b)} {μ : O a b} {K : ℤ}
    (hK : ∀ m ∈ norms, ι₁ hd0.le (bndElt G V μ pC qC m) ≤ K)
    {aL : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {S : ℤ} {U Uinv : ℕ → ℕ → ℤ} (hS : 0 < S)
    (hquad : quadCheck aL w 6 (gramU U (traceGram G V μ qC)) S = true)
    (hinv : invCheck U Uinv = true)
    {r' : Fin 3 → O a b} (hr' : IsRoot hd0.le G r') (hmem : bil G r' r' ∈ norms)
    (hns : ¬ OneSign hd0.le G n Ps r') :
    psum aL w 6 (mv Uinv (coords r')) 6 ≤ S * K := by
  have hcross : (∃ i, i < n ∧ 0 < ι₁ hd0.le (bil G r' (Ps i))) ∧
      (∃ j, j < n ∧ ι₁ hd0.le (bil G r' (Ps j)) < 0) := by
    unfold OneSign at hns
    push Not at hns
    obtain ⟨⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩ := hns
    exact ⟨⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
  obtain ⟨⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩ := hcross
  have hqR : (0 : ℝ) < qC := by exact_mod_cast hqC
  have hb1 := crossing_lat hc hvert hVV hVs hqR hC hi hj h1 h2
  have hb2 := cs_ι₂ hadm r' V
  -- the trace bound
  set m := bil G r' r'
  have hm1 := hr'.totPos.1
  have hm2 := hr'.totPos.2
  have hVV2 : 0 ≤ ι₂ hd0.le (bil G V V) := by
    have := cs_ι₂ hadm V V; nlinarith [sq_nonneg (ι₂ hd0.le (bil G V V))]
  have htr : ((trace (psiB G V μ qC r' r') : ℤ) : ℝ) ≤ K := by
    have e := ι₁_add_ι₂ hd0.le (psiB G V μ qC r' r')
    rw [trace_def, ← e]
    have hK' := hK m hmem
    have hX : ι₁ hd0.le (bndElt G V μ pC qC m) =
        (2 * pC - qC) * ι₁ hd0.le m * (-ι₁ hd0.le (bil G V V)) + ι₁ hd0.le μ * ι₁ hd0.le m +
          (qC * ι₂ hd0.le m * ι₂ hd0.le (bil G V V) + ι₂ hd0.le μ * ι₂ hd0.le m) := by
      unfold bndElt
      rw [map_add, map_add, ← ι₂_eq_ι₁_star]
      simp only [bilE_eq, map_add, map_mul, map_sub, map_neg, map_intCast, map_ofNat]
    have hψ : ∀ ι : O a b →+* ℝ, ι (psiB G V μ qC r' r') =
        2 * qC * ι (bil G r' V) ^ 2 + (ι μ - qC * ι (bil G V V)) * ι m := by
      intro ι
      simp only [psiB, bilE_eq, map_add, map_mul, map_sub, map_intCast, map_ofNat, m]
      ring
    rw [hψ, hψ]
    rw [hX] at hK'
    have h2q := mul_le_mul_of_nonneg_left hb2 hqR.le
    push_cast
    linarith
  -- the enumeration visits r'
  set z := coords r'
  set z' := mv Uinv z
  have hzU : mv U z' = z := mv_mv hinv (coords_ge r')
  show psum aL w 6 z' 6 ≤ S * K
  rw [quadCheck_sound hquad, qform_gramU, hzU, ← trace_psi_eq, vecOf_coords]
  have : ((trace (psiB G V μ qC r' r') : ℤ) : ℝ) ≤ (K : ℝ) := htr
  have h' : trace (psiB G V μ qC r' r') ≤ K := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_left h' hS.le

/-- **B8.** The one-sign property of every root, from a certified polygon, a centre `V`
with cosh bound `p/q`, the window data of B7, a bound `K` on `ι₁ (bndElt m)` over the
window norms, and an enumeration certificate `(a, w, S, U, Uinv)` whose search returns
`true`. -/
theorem hone_of_enum [IsDomain (O a b)] [IsPrincipalIdealRing (O a b)]
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hadm : Admissible hd0.le G) {n : ℕ} {f : Fin 3 → Fin 3 → O a b}
    {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b} (hc : PolyCert hd0.le G n f rs Ps Xs)
    (hvert : ∀ k i, k < n → i < n → ι₁ hd0.le (bil G (rs k) (Ps i)) ≤ 0)
    -- the centre
    {V : Fin 3 → O a b} (hVV : ι₁ hd0.le (bil G V V) < 0)
    (hVs : ι₁ hd0.le (bil G V (f 2)) < 0) {pC qC : ℤ} (hqC : 0 < qC)
    (hC : ∀ i, i < n → (qC : ℝ) * ι₁ hd0.le (bil G V (Ps i)) ^ 2 ≤
      pC * (ι₁ hd0.le (bil G V V) * ι₁ hd0.le (bil G (Ps i) (Ps i))))
    -- the window (B7)
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S' : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS' : 4 * p * |Nm (2 * G.det)| ≤ q * (S' : ℤ) ^ 2)
    -- the bound
    {μ : O a b} {K : ℤ}
    (hK : ∀ m ∈ windowNorms a b (2 * G.det) p q Y S',
      ι₁ hd0.le (bndElt G V μ pC qC m) ≤ K)
    -- the enumeration
    {aL : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {S : ℤ} {U Uinv : ℕ → ℕ → ℤ}
    (hw : ∀ i, i < 6 → 0 ≤ w i) (hS : 0 < S)
    (hquad : quadCheck aL w 6 (gramU U (traceGram G V μ qC)) S = true)
    (hinv : invCheck U Uinv = true)
    (henum : enum aL w 6 (fun z => leafCheck G n Ps (windowNorms a b (2 * G.det) p q Y S')
      (vecOf (mv U z))) (S * K) = true) :
    ∀ r, IsRoot hd0.le G r → OneSign hd0.le G n Ps r := by
  intro r hr
  obtain ⟨r', hr', hiff, hmem⟩ := exists_root_in_window hd0 hG hu hρ hq hpq hY hS'
    (n := n) (Ps := Ps) hr
  rw [← hiff]
  by_contra hns
  have hpsum := cross_psum hd0 hadm hc hvert hVV hVs hqC hC hK hS hquad hinv hr' hmem hns
  have hz'0 : ∀ j, 6 ≤ j → mv Uinv (coords r') j = 0 := fun j hj => by
    unfold mv; rw [if_neg (by omega)]
  have hleaf := enum_sound hw henum _ hz'0 hpsum
  rw [mv_mv hinv (coords_ge r'), vecOf_coords] at hleaf
  exact hns (leafCheck_sound hd0 hleaf hr' hmem)

/-- **Reflectivity from a polygon certificate and an enumeration certificate**, assuming
Vinberg's chamber theorem: B1–B8 combined. Every hypothesis other than `hV` is an exact
statement about the data (an equation in `O`, a sign at `ι₁` or `ι₂`, or a Boolean
computed by the kernel). -/
theorem reflective_of_enum (hV : VinbergChamber) [IsDomain (O a b)]
    [IsPrincipalIdealRing (O a b)] (hns : ¬ IsSquare (b ^ 2 + 4 * a))
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hadm : Admissible hd0.le G) {n : ℕ} {f : Fin 3 → Fin 3 → O a b}
    {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b} (hc : PolyCert hd0.le G n f rs Ps Xs)
    (hvert : ∀ k i, k < n → i < n → ι₁ hd0.le (bil G (rs k) (Ps i)) ≤ 0)
    {V : Fin 3 → O a b} (hVV : ι₁ hd0.le (bil G V V) < 0)
    (hVs : ι₁ hd0.le (bil G V (f 2)) < 0) {pC qC : ℤ} (hqC : 0 < qC)
    (hC : ∀ i, i < n → (qC : ℝ) * ι₁ hd0.le (bil G V (Ps i)) ^ 2 ≤
      pC * (ι₁ hd0.le (bil G V V) * ι₁ hd0.le (bil G (Ps i) (Ps i))))
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S' : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS' : 4 * p * |Nm (2 * G.det)| ≤ q * (S' : ℤ) ^ 2)
    {μ : O a b} {K : ℤ}
    (hK : ∀ m ∈ windowNorms a b (2 * G.det) p q Y S',
      ι₁ hd0.le (bndElt G V μ pC qC m) ≤ K)
    {aL : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {S : ℤ} {U Uinv : ℕ → ℕ → ℤ}
    (hw : ∀ i, i < 6 → 0 ≤ w i) (hS : 0 < S)
    (hquad : quadCheck aL w 6 (gramU U (traceGram G V μ qC)) S = true)
    (hinv : invCheck U Uinv = true)
    (henum : enum aL w 6 (fun z => leafCheck G n Ps (windowNorms a b (2 * G.det) p q Y S')
      (vecOf (mv U z))) (S * K) = true) :
    Reflective hd0.le G :=
  reflective_of_cert hV hns hadm hc
    (hone_of_enum hd0 hadm hc hvert hVV hVs hqC hC hG hu hρ hq hpq hY hS' hK hw hS hquad
      hinv henum)


/-! ### Variant: the last `O`-coordinate solved exactly -/

/-- Column `j` of `U` as a vector of `O³`. -/
def colVec (U : ℕ → ℕ → ℤ) (j : ℕ) : Fin 3 → O a b := vecOf fun i => U i j

/-- Column 1 of `U` is `ω` times column 0. -/
def colCheck (U : ℕ → ℕ → ℤ) : Bool :=
  (List.finRange 3).all fun k => decide (colVec (a := a) (b := b) U 1 k = ⟨0, 1⟩ * colVec U 0 k)

lemma vecOf_add (f g : ℕ → ℤ) :
    vecOf (a := a) (b := b) (f + g) = vecOf f + vecOf g := by
  funext k; fin_cases k <;> (ext <;> simp [vecOf])

lemma vecOf_smul (c : ℤ) (f : ℕ → ℤ) :
    vecOf (a := a) (b := b) (c • f) = (c : O a b) • vecOf f := by
  funext k; fin_cases k <;> (ext <;> simp [vecOf])

/-- `U z = U z_f + z₀ u₀ + z₁ ω u₀`, where `z_f` is `z` with the first two coordinates
zeroed and `u₀` is column 0. -/
lemma vecOf_mv_split {U : ℕ → ℕ → ℤ} (hcol : colCheck (a := a) (b := b) U = true)
    (z : ℕ → ℤ) :
    vecOf (a := a) (b := b) (mv U z) =
      vecOf (mv U fun j => if 2 ≤ j then z j else 0) + (⟨z 0, z 1⟩ : O a b) • colVec U 0 := by
  simp only [colCheck, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
    at hcol
  have h1 : vecOf (a := a) (b := b) (mv U z) =
      vecOf (mv U fun j => if 2 ≤ j then z j else 0) + (z 0 : O a b) • colVec U 0 +
        (z 1 : O a b) • colVec U 1 := by
    funext k
    fin_cases k <;> (ext <;> simp [vecOf, mv, lsum, colVec] <;> ring)
  have h2 : colVec (a := a) (b := b) U 1 = (⟨0, 1⟩ : O a b) • colVec U 0 := by
    funext k; exact hcol k
  rw [h1, h2, smul_smul, add_assoc, ← add_smul]
  congr 2
  ext <;> simp

/-- The leaf of the stopped search: for each window norm `m`, solve
`(u₀·u₀) t² + 2 (u₀·r_f) t + (r_f·r_f − m) = 0` and check every solution. -/
def leaf2 (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (U : ℕ → ℕ → ℤ) (zf : ℕ → ℤ) : Bool :=
  let rf : Fin 3 → O a b := vecOf (mv U zf)
  let u0 : Fin 3 → O a b := colVec U 0
  norms.all fun m =>
    let sol := solveQuad (bilE G u0 u0) (bilE G u0 rf) (bilE G rf rf - m)
    sol.1 && sol.2.all fun t => leafCheck G n Ps norms (rf + t • u0)


lemma bil_comm {G : Matrix (Fin 3) (Fin 3) (O a b)} (hG : Gᵀ = G) (x y : Fin 3 → O a b) :
    bil G x y = bil G y x := by
  unfold bil
  rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]

/-- **B8, stopped search.** As `hone_of_enum`, but the search stops two levels early and the
leaf solves for the last `O`-coordinate exactly (`leaf2`); column 1 of `U` must be `ω`
times column 0. -/
theorem hone_of_enum2 [IsDomain (O a b)] [IsPrincipalIdealRing (O a b)]
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hadm : Admissible hd0.le G) {n : ℕ} {f : Fin 3 → Fin 3 → O a b}
    {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b} (hc : PolyCert hd0.le G n f rs Ps Xs)
    (hvert : ∀ k i, k < n → i < n → ι₁ hd0.le (bil G (rs k) (Ps i)) ≤ 0)
    -- the centre
    {V : Fin 3 → O a b} (hVV : ι₁ hd0.le (bil G V V) < 0)
    (hVs : ι₁ hd0.le (bil G V (f 2)) < 0) {pC qC : ℤ} (hqC : 0 < qC)
    (hC : ∀ i, i < n → (qC : ℝ) * ι₁ hd0.le (bil G V (Ps i)) ^ 2 ≤
      pC * (ι₁ hd0.le (bil G V V) * ι₁ hd0.le (bil G (Ps i) (Ps i))))
    -- the window (B7)
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S' : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS' : 4 * p * |Nm (2 * G.det)| ≤ q * (S' : ℤ) ^ 2)
    -- the bound
    {μ : O a b} {K : ℤ}
    (hK : ∀ m ∈ windowNorms a b (2 * G.det) p q Y S',
      ι₁ hd0.le (bndElt G V μ pC qC m) ≤ K)
    -- the enumeration
    {aL : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {S : ℤ} {U Uinv : ℕ → ℕ → ℤ}
    (hw : ∀ i, i < 6 → 0 ≤ w i) (hS : 0 < S)
    (hquad : quadCheck aL w 6 (gramU U (traceGram G V μ qC)) S = true)
    (hinv : invCheck U Uinv = true)
    (hcol : colCheck (a := a) (b := b) U = true)
    (henum : enumS aL w 6 2 (leaf2 G n Ps (windowNorms a b (2 * G.det) p q Y S') U) (S * K)
      = true) :
    ∀ r, IsRoot hd0.le G r → OneSign hd0.le G n Ps r := by
  intro r hr
  obtain ⟨r', hr', hiff, hmem⟩ := exists_root_in_window hd0 hG hu hρ hq hpq hY hS'
    (n := n) (Ps := Ps) hr
  rw [← hiff]
  by_contra hns
  set norms := windowNorms a b (2 * G.det) p q Y S'
  have hpsum := cross_psum hd0 hadm hc hvert hVV hVs hqC hC hK hS hquad hinv hr' hmem hns
  set z' := mv Uinv (coords r')
  have hz'0 : ∀ j, 6 ≤ j → z' j = 0 := fun j hj => by
    show mv Uinv (coords r') j = 0
    unfold mv; rw [if_neg (by omega)]
  have hleaf := enumS_sound hw (by norm_num) henum z' hz'0 hpsum
  set zf : ℕ → ℤ := fun j => if 2 ≤ j then z' j else 0
  set rf : Fin 3 → O a b := vecOf (mv U zf)
  set u0 : Fin 3 → O a b := colVec U 0
  set t : O a b := ⟨z' 0, z' 1⟩
  have hreq : r' = rf + t • u0 := by
    have := vecOf_mv_split hcol z'
    rw [mv_mv hinv (coords_ge r'), vecOf_coords] at this
    exact this
  simp only [leaf2, List.all_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨hok, hall⟩ := hleaf _ hmem
  have hdZ : b ^ 2 + 4 * a ≠ 0 := by
    have : (0 : ℤ) < b ^ 2 + 4 * a := by exact_mod_cast hd0
    omega
  have heq : bilE G u0 u0 * t * t + 2 * bilE G u0 rf * t + (bilE G rf rf - bil G r' r') = 0 := by
    rw [hreq]
    simp only [bilE_eq, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right]
    rw [bil_comm hadm.symm rf u0]
    ring
  have ht := mem_solveQuad hdZ hok heq
  have hl := hall t ht
  rw [← hreq] at hl
  exact hns (leafCheck_sound hd0 hl hr' hmem)

/-- **Reflectivity**, stopped-search form (B1–B8). -/
theorem reflective_of_enum2 (hV : VinbergChamber) (hns : ¬ IsSquare (b ^ 2 + 4 * a)) [IsDomain (O a b)] [IsPrincipalIdealRing (O a b)]
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hadm : Admissible hd0.le G) {n : ℕ} {f : Fin 3 → Fin 3 → O a b}
    {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b} (hc : PolyCert hd0.le G n f rs Ps Xs)
    (hvert : ∀ k i, k < n → i < n → ι₁ hd0.le (bil G (rs k) (Ps i)) ≤ 0)
    -- the centre
    {V : Fin 3 → O a b} (hVV : ι₁ hd0.le (bil G V V) < 0)
    (hVs : ι₁ hd0.le (bil G V (f 2)) < 0) {pC qC : ℤ} (hqC : 0 < qC)
    (hC : ∀ i, i < n → (qC : ℝ) * ι₁ hd0.le (bil G V (Ps i)) ^ 2 ≤
      pC * (ι₁ hd0.le (bil G V V) * ι₁ hd0.le (bil G (Ps i) (Ps i))))
    -- the window (B7)
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S' : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS' : 4 * p * |Nm (2 * G.det)| ≤ q * (S' : ℤ) ^ 2)
    -- the bound
    {μ : O a b} {K : ℤ}
    (hK : ∀ m ∈ windowNorms a b (2 * G.det) p q Y S',
      ι₁ hd0.le (bndElt G V μ pC qC m) ≤ K)
    -- the enumeration
    {aL : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {S : ℤ} {U Uinv : ℕ → ℕ → ℤ}
    (hw : ∀ i, i < 6 → 0 ≤ w i) (hS : 0 < S)
    (hquad : quadCheck aL w 6 (gramU U (traceGram G V μ qC)) S = true)
    (hinv : invCheck U Uinv = true)
    (hcol : colCheck (a := a) (b := b) U = true)
    (henum : enumS aL w 6 2 (leaf2 G n Ps (windowNorms a b (2 * G.det) p q Y S') U) (S * K)
      = true) :
    Reflective hd0.le G :=
  reflective_of_cert hV hns hadm hc
    (hone_of_enum2 hd0 hadm hc hvert hVV hVs hqC hC hG hu hρ hq hpq hY hS' hK hw hS hquad
      hinv hcol henum)

end ReflectZphi.PolyEnum
