import ReflectZphi.Cert.PolyEnum

/-!
# B8′: several centres per polygon (cells along a chain)

The single-centre bound of `crossing_lat` is too weak for long polygons. Here the
crossing point of a mirror is located on a *chain* `B₀, …, B_{N-1}` of future vectors
containing every vertex: if `r` takes both strict signs on the vertices, it changes sign
(`> 0` to `≤ 0`, or back) between two consecutive points `B_j, B_{j+1}` (`exists_switch`),
and `r^⊥` then meets the segment `[B_j, B_{j+1}]` at a future vector. The cosh bound at
the two endpoints, for the centre of the cell that segment belongs to, gives the
crossing bound (`segment_bound`, `segment_lat`), and that cell's enumeration finishes the
argument (`cell_oneSign`).

Soundness does not need the `B_j` to lie on the boundary: any future vectors will do.
Points on the polygon edges are what make the cells small.
-/

namespace ReflectZphi.Cells

open Matrix QuadraticAlgebra ReflectZphi.Minkowski ReflectZphi.Geometry ReflectZphi.Lattice
  ReflectZphi.Transfer ReflectZphi.Bridge ReflectZphi.RootNorms ReflectZphi.Crossing
  ReflectZphi.Enum ReflectZphi.QuadSolve ReflectZphi.PolyEnum

local notation "Nm" => QuadraticAlgebra.norm

/-! ### The bound on a segment, in `J` coordinates -/

/-- If `r^⊥` contains `α A + β B` (`α ≥ 0 < β`, `A, B` future, both within cosh `C` of `v`),
then `(r·v)² ≤ (r·r)(−v·v)(C² − 1)`. -/
theorem segment_bound {A B v : Fin 3 → ℝ} (hA : Future A) (hB : Future B) (hv : Future v)
    {C : ℝ} (hC : 0 ≤ C) (hbA : -mink v A ≤ C * tau v * tau A)
    (hbB : -mink v B ≤ C * tau v * tau B) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (r : Fin 3 → ℝ) (hrx : mink (α • A + β • B) r = 0) :
    mink r v ^ 2 ≤ mink r r * (-mink v v) * (C ^ 2 - 1) := by
  set x := α • A + β • B with hx_def
  have hxf : Future x := by
    rcases eq_or_lt_of_le hα with h0 | hpos
    · rw [hx_def, ← h0, zero_smul, zero_add]; exact future_smul hβ hB
    · exact future_add (future_smul hpos hA) (future_smul hβ hB)
  have hxx : mink x x < 0 := hxf.2
  have hmaj := majorant_bound v hxx hrx
  have hball := ball_convex (Finset.univ : Finset (Fin 2)) ![α, β] ![A, B] v C hC
    (by intro i _; fin_cases i <;> simp [hα, hβ.le])
    (by intro i _; fin_cases i <;> simp [FutureOrZero, hA, hB])
    (by intro i _; fin_cases i <;> simp [hbA, hbB])
  have hsum : ∑ i : Fin 2, (![α, β] : Fin 2 → ℝ) i • (![A, B] : Fin 2 → Fin 3 → ℝ) i = x := by
    simp [Fin.sum_univ_two, hx_def]
  rw [hsum] at hball
  have hvx : 0 < -mink v x := by linarith [mink_neg_of_future hv hxf]
  have htv : tau v ^ 2 = -mink v v := by
    unfold tau; rw [Real.sq_sqrt (by linarith [hv.2])]
  have htx : tau x ^ 2 = -mink x x := by
    unfold tau; rw [Real.sq_sqrt (by linarith)]
  have hsq : mink v x ^ 2 ≤ C ^ 2 * (-mink v v) * (-mink x x) := by
    have h := pow_le_pow_left₀ hvx.le hball 2
    rw [neg_sq, mul_pow, mul_pow, htv, htx] at h
    linarith
  have hrr : 0 ≤ mink r r := perp_nonneg hxx hrx
  have hX : 0 < -mink x x := by linarith
  have key : (-mink x x) * mink r v ^ 2 ≤ (-mink x x) * (mink r r * (-mink v v) * (C ^ 2 - 1)) := by
    calc (-mink x x) * mink r v ^ 2 ≤ mink r r * (mink v x ^ 2 - mink x x * mink v v) := hmaj
      _ ≤ mink r r * (C ^ 2 * (-mink v v) * (-mink x x) - mink x x * mink v v) :=
          mul_le_mul_of_nonneg_left (by linarith) hrr
      _ = (-mink x x) * (mink r r * (-mink v v) * (C ^ 2 - 1)) := by ring
  exact le_of_mul_le_mul_left key hX

/-! ### The bound on a segment, for the lattice -/

variable {a b : ℤ} {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a} {G : Matrix (Fin 3) (Fin 3) (O a b)}
  {n : ℕ} {f : Fin 3 → Fin 3 → O a b} {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b}

/-- The cosh bound `q (V·P)² ≤ p (V·V)(P·P)` in `J` coordinates, with `C = √(p/q)`. -/
lemma cosh_T (hc : PolyCert hd G n f rs Ps Xs) {V P : Fin 3 → O a b}
    (hVV : ι₁ hd (bil G V V) < 0) (hVs : ι₁ hd (bil G V (f 2)) < 0)
    (hPP : ι₁ hd (bil G P P) < 0) (hPs : ι₁ hd (bil G P (f 2)) < 0)
    {pC qC : ℝ} (hq : 0 < qC)
    (hC : qC * ι₁ hd (bil G V P) ^ 2 ≤ pC * (ι₁ hd (bil G V V) * ι₁ hd (bil G P P))) :
    -mink (Tm (hd := hd) (G := G) f *ᵥ realVec hd V) (Tm (hd := hd) (G := G) f *ᵥ realVec hd P)
      ≤ Real.sqrt (pC / qC) * tau (Tm (hd := hd) (G := G) f *ᵥ realVec hd V) *
        tau (Tm (hd := hd) (G := G) f *ᵥ realVec hd P) := by
  set T := Tm (hd := hd) (G := G) f
  have hT : ∀ u w, mink (T *ᵥ realVec hd u) (T *ᵥ realVec hd w) = ι₁ hd (bil G u w) :=
    mink_T hc
  have hv : Future (T *ᵥ realVec hd V) := future_T hc hVV hVs
  have hp : Future (T *ᵥ realVec hd P) := future_T hc hPP hPs
  have hprod : 0 < ι₁ hd (bil G V V) * ι₁ hd (bil G P P) := mul_pos_of_neg_of_neg hVV hPP
  have hpC : 0 ≤ pC := by
    by_contra h'; push Not at h'
    have := mul_neg_of_neg_of_pos h' hprod
    nlinarith [sq_nonneg (ι₁ hd (bil G V P))]
  have hpq : 0 ≤ pC / qC := by positivity
  set C := Real.sqrt (pC / qC)
  have hC2 : C ^ 2 = pC / qC := Real.sq_sqrt hpq
  have htv : tau (T *ᵥ realVec hd V) ^ 2 = -mink (T *ᵥ realVec hd V) (T *ᵥ realVec hd V) := by
    unfold tau; rw [Real.sq_sqrt (by linarith [hv.2])]
  have htp : tau (T *ᵥ realVec hd P) ^ 2 = -mink (T *ᵥ realVec hd P) (T *ᵥ realVec hd P) := by
    unfold tau; rw [Real.sq_sqrt (by linarith [hp.2])]
  have hneg' : 0 < -mink (T *ᵥ realVec hd V) (T *ᵥ realVec hd P) :=
    neg_pos.mpr (mink_neg_of_future hv hp)
  have hrhs : 0 ≤ C * tau (T *ᵥ realVec hd V) * tau (T *ᵥ realVec hd P) := by
    have := tau_nonneg (T *ᵥ realVec hd V); have := tau_nonneg (T *ᵥ realVec hd P)
    positivity
  rw [← pow_le_pow_iff_left₀ hneg'.le hrhs two_ne_zero]
  rw [mul_pow, mul_pow, hC2, htv, htp, neg_sq]
  simp only [hT]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hq]
  nlinarith

/-- **Crossing bound on a segment.** If `r·A > 0 ≥ r·B` for future `A, B` within the cosh
bound `p/q` of the future centre `V`, then `q (r·V)² ≤ (p − q)(r·r)(−V·V)` at `ι₁`. -/
theorem segment_lat (hc : PolyCert hd G n f rs Ps Xs) {A B V : Fin 3 → O a b}
    (hAA : ι₁ hd (bil G A A) < 0) (hAs : ι₁ hd (bil G A (f 2)) < 0)
    (hBB : ι₁ hd (bil G B B) < 0) (hBs : ι₁ hd (bil G B (f 2)) < 0)
    (hVV : ι₁ hd (bil G V V) < 0) (hVs : ι₁ hd (bil G V (f 2)) < 0)
    {pC qC : ℝ} (hq : 0 < qC)
    (hCA : qC * ι₁ hd (bil G V A) ^ 2 ≤ pC * (ι₁ hd (bil G V V) * ι₁ hd (bil G A A)))
    (hCB : qC * ι₁ hd (bil G V B) ^ 2 ≤ pC * (ι₁ hd (bil G V V) * ι₁ hd (bil G B B)))
    {r : Fin 3 → O a b} (hpos : 0 < ι₁ hd (bil G r A)) (hnp : ι₁ hd (bil G r B) ≤ 0) :
    qC * ι₁ hd (bil G r V) ^ 2 ≤ (pC - qC) * ι₁ hd (bil G r r) * (-ι₁ hd (bil G V V)) := by
  set T := Tm (hd := hd) (G := G) f
  have hT : ∀ u w, mink (T *ᵥ realVec hd u) (T *ᵥ realVec hd w) = ι₁ hd (bil G u w) :=
    mink_T hc
  have hfA : Future (T *ᵥ realVec hd A) := future_T hc hAA hAs
  have hfB : Future (T *ᵥ realVec hd B) := future_T hc hBB hBs
  have hv : Future (T *ᵥ realVec hd V) := future_T hc hVV hVs
  have hbA := cosh_T hc hVV hVs hAA hAs hq hCA
  have hbB := cosh_T hc hVV hVs hBB hBs hq hCB
  have hpq : 0 ≤ pC / qC := by
    have hprod : 0 < ι₁ hd (bil G V V) * ι₁ hd (bil G A A) := mul_pos_of_neg_of_neg hVV hAA
    have : 0 ≤ pC := by
      by_contra h'; push Not at h'
      have := mul_neg_of_neg_of_pos h' hprod
      nlinarith [sq_nonneg (ι₁ hd (bil G V A))]
    positivity
  have hC2 : Real.sqrt (pC / qC) ^ 2 = pC / qC := Real.sq_sqrt hpq
  set ρ := T *ᵥ realVec hd r
  have hrx : mink ((-ι₁ hd (bil G r B)) • (T *ᵥ realVec hd A) +
      (ι₁ hd (bil G r A)) • (T *ᵥ realVec hd B)) ρ = 0 := by
    rw [mink_comm, mink_add_left, mink_smul_left, mink_smul_left]
    simp only [ρ, hT]; ring
  have hseg := segment_bound hfA hfB hv (Real.sqrt_nonneg _) hbA hbB (neg_nonneg.mpr hnp)
    hpos ρ hrx
  simp only [ρ, hT, hC2] at hseg
  have : qC * ι₁ hd (bil G r V) ^ 2 ≤
      qC * (ι₁ hd (bil G r r) * -ι₁ hd (bil G V V) * (pC / qC - 1)) :=
    mul_le_mul_of_nonneg_left hseg hq.le
  have e : qC * (ι₁ hd (bil G r r) * -ι₁ hd (bil G V V) * (pC / qC - 1)) =
      (pC - qC) * ι₁ hd (bil G r r) * (-ι₁ hd (bil G V V)) := by
    field_simp
  linarith

/-! ### A sign change along a chain -/

/-- A real sequence with a positive and a negative term among its first `N` changes sign
(`> 0` to `≤ 0` or `≤ 0` to `> 0`) between two consecutive terms. -/
lemma exists_switch {s : ℕ → ℝ} {N i j : ℕ} (hi : i < N) (hj : j < N) (hpi : 0 < s i)
    (hnj : s j < 0) :
    ∃ k, k + 1 < N ∧ ((0 < s k ∧ s (k + 1) ≤ 0) ∨ (s k ≤ 0 ∧ 0 < s (k + 1))) := by
  classical
  rcases lt_or_gt_of_ne (show i ≠ j by rintro rfl; linarith) with hij | hji
  · set k := Nat.findGreatest (fun k => i ≤ k ∧ 0 < s k) j
    have hk : i ≤ k ∧ 0 < s k := Nat.findGreatest_spec (P := fun k => i ≤ k ∧ 0 < s k)
      hij.le ⟨le_rfl, hpi⟩
    have hkj : k ≤ j := Nat.findGreatest_le j
    have hkj' : k < j := lt_of_le_of_ne hkj (by rintro h; rw [h] at hk; linarith [hk.2])
    have hnot := Nat.findGreatest_is_greatest (P := fun k => i ≤ k ∧ 0 < s k)
      (Nat.lt_succ_self k) hkj'
    refine ⟨k, by omega, Or.inl ⟨hk.2, ?_⟩⟩
    by_contra h; push Not at h
    exact hnot ⟨by omega, h⟩
  · set k := Nat.findGreatest (fun k => j ≤ k ∧ s k ≤ 0) i
    have hk : j ≤ k ∧ s k ≤ 0 := Nat.findGreatest_spec (P := fun k => j ≤ k ∧ s k ≤ 0)
      hji.le ⟨le_rfl, hnj.le⟩
    have hki : k ≤ i := Nat.findGreatest_le i
    have hki' : k < i := lt_of_le_of_ne hki (by rintro h; rw [h] at hk; linarith [hk.2])
    have hnot := Nat.findGreatest_is_greatest (P := fun k => j ≤ k ∧ s k ≤ 0)
      (Nat.lt_succ_self k) hki'
    refine ⟨k, by omega, Or.inr ⟨hk.2, ?_⟩⟩
    by_contra h; push Not at h
    exact hnot ⟨by omega, h⟩

/-! ### One cell -/

/-- The data of one cell: a centre `V` with cosh bound `pC/qC`, the majorant parameter `μ`,
its bound `K`, and the enumeration certificate `(aL, w, S, U, Uinv)`. -/
structure CellData (a b : ℤ) where
  V : Fin 3 → O a b
  pC : ℤ
  qC : ℤ
  μ : O a b
  K : ℤ
  aL : ℕ → ℕ → ℤ
  w : ℕ → ℤ
  S : ℤ
  U : ℕ → ℕ → ℤ
  Uinv : ℕ → ℕ → ℤ

/-- **One cell.** A root `r` of window norm `m ∈ norms` satisfying the crossing bound for the
centre of the cell has one sign on the vertices, provided the cell's enumeration succeeds. -/
theorem cell_oneSign [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
    (hadm : Admissible hd0.le G) {n : ℕ} {Ps : ℕ → Fin 3 → O a b} {norms : List (O a b)}
    (c : CellData a b) (hqC : 0 < c.qC)
    (hK : ∀ m ∈ norms, ι₁ hd0.le (bndElt G c.V c.μ c.pC c.qC m) ≤ c.K)
    (hw : ∀ i, i < 6 → 0 ≤ c.w i) (hS : 0 < c.S)
    (hquad : quadCheck c.aL c.w 6 (gramU c.U (traceGram G c.V c.μ c.qC)) c.S = true)
    (hinv : invCheck c.U c.Uinv = true) (hcol : colCheck (a := a) (b := b) c.U = true)
    (henum : enumS c.aL c.w 6 2 (leaf2 G n Ps norms c.U) (c.S * c.K) = true)
    {r : Fin 3 → O a b} (hr : IsRoot hd0.le G r) (hm : bil G r r ∈ norms)
    (hb1 : (c.qC : ℝ) * ι₁ hd0.le (bil G r c.V) ^ 2 ≤
      (c.pC - c.qC) * ι₁ hd0.le (bil G r r) * (-ι₁ hd0.le (bil G c.V c.V))) :
    OneSign hd0.le G n Ps r := by
  by_contra hns
  have hqR : (0 : ℝ) < c.qC := by exact_mod_cast hqC
  have hb2 := cs_ι₂ hadm r c.V
  have hm1 := hr.totPos.1
  have hm2 := hr.totPos.2
  have hVV2 : 0 ≤ ι₂ hd0.le (bil G c.V c.V) := by
    have := cs_ι₂ hadm c.V c.V; nlinarith [sq_nonneg (ι₂ hd0.le (bil G c.V c.V))]
  -- the trace bound
  have htr : ((trace (psiB G c.V c.μ c.qC r r) : ℤ) : ℝ) ≤ c.K := by
    have e := ι₁_add_ι₂ hd0.le (psiB G c.V c.μ c.qC r r)
    rw [trace_def, ← e]
    have hK' := hK _ hm
    have hX : ι₁ hd0.le (bndElt G c.V c.μ c.pC c.qC (bil G r r)) =
        (2 * c.pC - c.qC) * ι₁ hd0.le (bil G r r) * (-ι₁ hd0.le (bil G c.V c.V)) +
          ι₁ hd0.le c.μ * ι₁ hd0.le (bil G r r) +
          (c.qC * ι₂ hd0.le (bil G r r) * ι₂ hd0.le (bil G c.V c.V) +
            ι₂ hd0.le c.μ * ι₂ hd0.le (bil G r r)) := by
      unfold bndElt
      rw [map_add, map_add, ← ι₂_eq_ι₁_star]
      simp only [bilE_eq, map_add, map_mul, map_sub, map_neg, map_intCast, map_ofNat]
    have hψ : ∀ ι : O a b →+* ℝ, ι (psiB G c.V c.μ c.qC r r) =
        2 * c.qC * ι (bil G r c.V) ^ 2 + (ι c.μ - c.qC * ι (bil G c.V c.V)) * ι (bil G r r) := by
      intro ι
      simp only [psiB, bilE_eq, map_add, map_mul, map_sub, map_intCast, map_ofNat]
      ring
    rw [hψ, hψ]
    rw [hX] at hK'
    have h2q := mul_le_mul_of_nonneg_left hb2 hqR.le
    linarith
  have hpsum : psum c.aL c.w 6 (mv c.Uinv (coords r)) 6 ≤ c.S * c.K := by
    have hzU : mv c.U (mv c.Uinv (coords r)) = coords r := mv_mv hinv (coords_ge r)
    rw [quadCheck_sound hquad, qform_gramU, hzU, ← trace_psi_eq, vecOf_coords]
    have h' : trace (psiB G c.V c.μ c.qC r r) ≤ c.K := by exact_mod_cast htr
    exact mul_le_mul_of_nonneg_left h' hS.le
  set z' := mv c.Uinv (coords r)
  have hz'0 : ∀ j, 6 ≤ j → z' j = 0 := fun j hj => by
    show mv c.Uinv (coords r) j = 0
    simp [mv, show ¬ j < 6 by omega]
  have hleaf := enumS_sound hw (by norm_num) henum z' hz'0 hpsum
  set zf : ℕ → ℤ := fun j => if 2 ≤ j then z' j else 0
  set rf : Fin 3 → O a b := vecOf (mv c.U zf)
  set u0 : Fin 3 → O a b := colVec c.U 0
  set t : O a b := ⟨z' 0, z' 1⟩
  have hreq : r = rf + t • u0 := by
    have := vecOf_mv_split hcol z'
    rw [mv_mv hinv (coords_ge r), vecOf_coords] at this
    exact this
  simp only [leaf2, List.all_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨hok, hall⟩ := hleaf _ hm
  have hdZ : b ^ 2 + 4 * a ≠ 0 := by
    have : (0 : ℤ) < b ^ 2 + 4 * a := by exact_mod_cast hd0
    omega
  have heq : bilE G u0 u0 * t * t + 2 * bilE G u0 rf * t + (bilE G rf rf - bil G r r) = 0 := by
    rw [hreq]
    simp only [bilE_eq, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right]
    rw [bil_comm hadm.symm rf u0]
    ring
  have ht := mem_solveQuad hdZ hok heq
  have hl := hall t ht
  rw [← hreq] at hl
  exact hns (leafCheck_sound hd0 hl hr hm)

/-! ### All cells -/

/-- **B8′.** Every root has one sign on the vertices, given:
* a chain `Bs 0, …, Bs (N-1)` of future vectors containing every vertex;
* for each segment `j` (`j + 1 < N`) a cell `seg j < nc` whose centre satisfies the cosh
  bound at both endpoints;
* for each cell its enumeration certificate (`cell_oneSign`);
* the window data of B7 (`exists_root_in_window`), with the window norms equal to `norms`. -/
theorem hone_of_cells [IsDomain (O a b)] [IsPrincipalIdealRing (O a b)]
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) (hadm : Admissible hd0.le G)
    (hc : PolyCert hd0.le G n f rs Ps Xs)
    -- the window (B7)
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S' : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS' : 4 * p * |Nm (2 * G.det)| ≤ q * (S' : ℤ) ^ 2)
    {norms : List (O a b)} (hnorms : windowNorms a b (2 * G.det) p q Y S' = norms)
    -- the chain
    {N : ℕ} {Bs : ℕ → Fin 3 → O a b} {idx : ℕ → ℕ}
    (hidx : ∀ i, i < n → idx i < N ∧ Bs (idx i) = Ps i)
    (hBB : ∀ j, j < N → ι₁ hd0.le (bil G (Bs j) (Bs j)) < 0)
    (hBs : ∀ j, j < N → ι₁ hd0.le (bil G (Bs j) (f 2)) < 0)
    -- the cells
    {nc : ℕ} {cells : ℕ → CellData a b} {seg : ℕ → ℕ}
    (hseg : ∀ j, j + 1 < N → seg j < nc)
    (hCseg : ∀ j, j + 1 < N → ∀ P ∈ [Bs j, Bs (j + 1)],
      ((cells (seg j)).qC : ℝ) * ι₁ hd0.le (bil G (cells (seg j)).V P) ^ 2 ≤
        (cells (seg j)).pC * (ι₁ hd0.le (bil G (cells (seg j)).V (cells (seg j)).V) *
          ι₁ hd0.le (bil G P P)))
    (hVV : ∀ k, k < nc → ι₁ hd0.le (bil G (cells k).V (cells k).V) < 0)
    (hVs : ∀ k, k < nc → ι₁ hd0.le (bil G (cells k).V (f 2)) < 0)
    (hqC : ∀ k, k < nc → 0 < (cells k).qC)
    (hK : ∀ k, k < nc → ∀ m ∈ norms,
      ι₁ hd0.le (bndElt G (cells k).V (cells k).μ (cells k).pC (cells k).qC m) ≤ (cells k).K)
    (hw : ∀ k, k < nc → ∀ i, i < 6 → 0 ≤ (cells k).w i) (hS : ∀ k, k < nc → 0 < (cells k).S)
    (hquad : ∀ k, k < nc → quadCheck (cells k).aL (cells k).w 6
      (gramU (cells k).U (traceGram G (cells k).V (cells k).μ (cells k).qC)) (cells k).S = true)
    (hinv : ∀ k, k < nc → invCheck (cells k).U (cells k).Uinv = true)
    (hcol : ∀ k, k < nc → colCheck (a := a) (b := b) (cells k).U = true)
    (henum : ∀ k, k < nc → enumS (cells k).aL (cells k).w 6 2 (leaf2 G n Ps norms (cells k).U)
      ((cells k).S * (cells k).K) = true) :
    ∀ r, IsRoot hd0.le G r → OneSign hd0.le G n Ps r := by
  intro r hr
  obtain ⟨r', hr', hiff, hmem⟩ := exists_root_in_window hd0 hG hu hρ hq hpq hY hS'
    (n := n) (Ps := Ps) hr
  rw [hnorms] at hmem
  rw [← hiff]
  by_contra hns
  have hns' := hns
  unfold OneSign at hns'
  push Not at hns'
  obtain ⟨⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩ := hns'
  obtain ⟨hi1, hi2⟩ := hidx i hi
  obtain ⟨hj1, hj2⟩ := hidx j hj
  obtain ⟨k, hk, hsw⟩ := exists_switch (s := fun l => ι₁ hd0.le (bil G r' (Bs l))) hi1 hj1
    (show 0 < ι₁ hd0.le (bil G r' (Bs (idx i))) by rw [hi2]; exact h1)
    (show ι₁ hd0.le (bil G r' (Bs (idx j))) < 0 by rw [hj2]; exact h2)
  have hck := hseg k hk
  set c := cells (seg k)
  have hqR : (0 : ℝ) < c.qC := by exact_mod_cast hqC _ hck
  have hC0 := hCseg k hk (Bs k) (by simp)
  have hC1 := hCseg k hk (Bs (k + 1)) (by simp)
  have hb1 : (c.qC : ℝ) * ι₁ hd0.le (bil G r' c.V) ^ 2 ≤
      (c.pC - c.qC) * ι₁ hd0.le (bil G r' r') * (-ι₁ hd0.le (bil G c.V c.V)) := by
    rcases hsw with ⟨hp, hn⟩ | ⟨hn, hp⟩
    · exact segment_lat hc (hBB k (by omega)) (hBs k (by omega)) (hBB (k + 1) hk)
        (hBs (k + 1) hk) (hVV _ hck) (hVs _ hck) hqR hC0 hC1 hp hn
    · exact segment_lat hc (hBB (k + 1) hk) (hBs (k + 1) hk) (hBB k (by omega))
        (hBs k (by omega)) (hVV _ hck) (hVs _ hck) hqR hC1 hC0 hp hn
  exact hns (cell_oneSign hd0 hadm c (hqC _ hck) (hK _ hck) (hw _ hck) (hS _ hck)
    (hquad _ hck) (hinv _ hck) (hcol _ hck) (henum _ hck) hr' hmem hb1)

end ReflectZphi.Cells
