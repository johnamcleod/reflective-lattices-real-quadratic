import ReflectZphi.Cert.Cover
import ReflectZphi.Cert.FastLeaf

/-!
# Per-norm sublattices for the cell searches

A root `r` of norm `m` satisfies `m ∣ 2 (r·x)` for every `x ∈ O³` (`IsRoot.dvd`), so it lies
in the sublattice `L_m = {r : m ∣ 2 (G r)ᵢ}`, of index up to `|Nm m|³`. Searching `L_m` with
the bound of the norm `m` alone (instead of `O³` with the largest bound of all window norms)
makes the cell searches an order of magnitude smaller.

The search coordinates `z` of `r` are given by an integer certificate `(Pz, Qz)`:
`z = Pz·coords r + Qz·coords s` with `s = 2 G r / m` (integral since `r` is a root). The
Boolean `subCheck` checks, on the six `ℤ`-basis vectors `e`, the identity

  `Nm m · U (Pz e) + U (Qz ((m̄ · 2) G e)) = Nm m · e`;

both sides are `ℤ`-linear in `e`, so it holds for all `r`, and since `Nm m · s = (m̄·2) G r`
it gives `U z = r` (`sub_coords`): every root of norm `m` is reached by the search in `z`.
-/

namespace ReflectZphi.Sublat

open Matrix QuadraticAlgebra ReflectZphi.Lattice ReflectZphi.Enum ReflectZphi.QuadSolve
  ReflectZphi.PolyEnum ReflectZphi.Check ReflectZphi.Cells

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-! ### Linearity of the coordinate maps -/

lemma coords_add (x y : Fin 3 → O a b) : coords (x + y) = coords x + coords y := by
  funext j
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [coords]
  | j + 6 => simp [coords]

lemma coords_zero : coords (0 : Fin 3 → O a b) = 0 := by
  funext j
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [coords]
  | j + 6 => simp [coords]

lemma mv_add' (U : ℕ → ℕ → ℤ) (z z' : ℕ → ℤ) : mv U (z + z') = mv U z + mv U z' := by
  funext j
  simp only [mv, Pi.add_apply]
  split_ifs
  · simp only [lsum_eq, mul_add, Finset.sum_add_distrib]
  · simp

lemma mv_zero' (U : ℕ → ℕ → ℤ) : mv U 0 = 0 := by
  funext j; simp [mv, lsum_eq]

lemma vecOf_zero : vecOf (a := a) (b := b) 0 = 0 := by
  funext k; fin_cases k <;> rfl

/-- `x ↦ U (P (coords x))` as an additive map. -/
def lin2 (U P : ℕ → ℕ → ℤ) : (Fin 3 → O a b) →+ (Fin 3 → O a b) where
  toFun x := vecOf (mv U (mv P (coords x)))
  map_zero' := by simp only [coords_zero, mv_zero', vecOf_zero]
  map_add' x y := by simp only [coords_add, mv_add', vecOf_add]

/-- `x ↦ c • (G x)` as an additive map. -/
def linG (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : O a b) : (Fin 3 → O a b) →+ (Fin 3 → O a b) where
  toFun x := c • (G *ᵥ x)
  map_zero' := by simp
  map_add' x y := by simp [mulVec_add, smul_add]

/-- The map checked on the basis: `Φ e = Nm m · U (Pz e) + U (Qz ((m̄·2) G e))`. -/
def phi (G : Matrix (Fin 3) (Fin 3) (O a b)) (m : O a b) (U Pz Qz : ℕ → ℕ → ℤ) :
    (Fin 3 → O a b) →+ (Fin 3 → O a b) :=
  (Nm m) • lin2 U Pz + (lin2 U Qz).comp (linG G (star m * 2))

/-- The sublattice certificate (six vector identities). -/
def subCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (m : O a b) (U Pz Qz : ℕ → ℕ → ℤ) : Bool :=
  (List.range 6).all fun l =>
    let e : Fin 3 → O a b := basisVec l
    vecEq (((Nm m : ℤ) : O a b) • vecOf (mv U (mv Pz (coords e))) +
      vecOf (mv U (mv Qz (coords ((star m * 2) • (G *ᵥ e))))))
      (((Nm m : ℤ) : O a b) • e)

lemma phi_basis {G : Matrix (Fin 3) (Fin 3) (O a b)} {m : O a b} {U Pz Qz : ℕ → ℕ → ℤ}
    (h : subCheck G m U Pz Qz = true) {l : ℕ} (hl : l < 6) :
    phi G m U Pz Qz (basisVec l) = (Nm m) • basisVec l := by
  simp only [subCheck, List.all_eq_true, List.mem_range, vecEq_iff] at h
  have := h l hl
  simp only [phi, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply]
  rw [← Int.cast_smul_eq_zsmul (O a b), ← Int.cast_smul_eq_zsmul (O a b)]
  exact this

lemma phi_all {G : Matrix (Fin 3) (Fin 3) (O a b)} {m : O a b} {U Pz Qz : ℕ → ℕ → ℤ}
    (h : subCheck G m U Pz Qz = true) (r : Fin 3 → O a b) :
    phi G m U Pz Qz r = (Nm m) • r := by
  have hr : r = ∑ j ∈ Finset.range 6, (coords r j) • basisVec (a := a) (b := b) j := by
    conv_lhs => rw [← vecOf_coords r, vecOf_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  rw [hr, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_zsmul, phi_basis h (Finset.mem_range.mp hj), smul_comm]

/-- **The coordinates.** If `m • s = 2 • G r` (`r` a root of norm `m`, `s = 2 G r / m`), then
`z = Pz (coords r) + Qz (coords s)` satisfies `U z = r`. -/
theorem sub_coords [IsDomain (O a b)] {G : Matrix (Fin 3) (Fin 3) (O a b)} {m : O a b}
    {U Pz Qz : ℕ → ℕ → ℤ} (h : subCheck G m U Pz Qz = true) (hm : m ≠ 0)
    {r s : Fin 3 → O a b} (hs : m • s = (2 : O a b) • (G *ᵥ r)) :
    vecOf (mv U (mv Pz (coords r) + mv Qz (coords s))) = r := by
  have hN : Nm m ≠ 0 := fun h0 => hm ((nm_eq_zero_iff m).mp h0)
  have hNs : (Nm m) • s = (star m * 2) • (G *ᵥ r) := by
    have e : ((Nm m : ℤ) : O a b) = star m * m := by
      rw [← eq_intCast (algebraMap ℤ (O a b)), algebraMap_norm_eq_mul_star, mul_comm]
    rw [← Int.cast_smul_eq_zsmul (O a b), e, mul_smul, hs, smul_comm, ← mul_smul, mul_comm]
  have hphi := phi_all h r
  simp only [phi, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] at hphi
  have hlin : lin2 U Qz (linG G (star m * 2) r) = (Nm m) • lin2 U Qz s := by
    rw [← map_zsmul, hNs]; rfl
  rw [hlin, ← smul_add] at hphi
  have hinj : Function.Injective fun x : Fin 3 → O a b => (Nm m) • x := by
    intro x y hxy
    funext k
    have := congrFun hxy k
    simp only [Pi.smul_apply] at this
    rw [← Int.cast_smul_eq_zsmul (O a b), ← Int.cast_smul_eq_zsmul (O a b), smul_eq_mul,
      smul_eq_mul] at this
    exact mul_left_cancel₀ (by exact_mod_cast hN) this
  have := hinj hphi
  simp only [lin2, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [mv_add', vecOf_add]; exact this

/-- The `s` of a root: `2 G r / m` is integral. -/
lemma exists_s {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a} {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hG : Gᵀ = G) {r : Fin 3 → O a b} (hr : IsRoot hd G r) :
    ∃ s : Fin 3 → O a b, bil G r r • s = (2 : O a b) • (G *ᵥ r) := by
  choose s hs using fun k : Fin 3 => hr.dvd (Pi.single k 1)
  refine ⟨s, funext fun k => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hs k, ← gcol_eq]
  congr 1
  have : (G *ᵥ r) k = ∑ j, G k j * r j := rfl
  rw [this, gcol, Fin.sum_univ_three]
  have e : ∀ j, G k j = G j k := fun j => by
    have := congrFun (congrFun hG j) k; simpa using this
  rw [e 0, e 1, e 2]; ring

lemma coords_vecOf {z : ℕ → ℤ} (hz : ∀ j, 6 ≤ j → z j = 0) :
    coords (vecOf (a := a) (b := b) z) = z := by
  funext j
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | j + 6 => exact (hz (j + 6) (by omega)).symm

lemma mv_ge (U : ℕ → ℕ → ℤ) (z : ℕ → ℤ) (j : ℕ) (hj : 6 ≤ j) : mv U z j = 0 := by
  simp [mv, show ¬ j < 6 by omega]

/-! ### One norm of one cell -/

/-- One search of one cell, for a group `ms` of window norms, in a lattice containing every
`L_m` (`m ∈ ms`), with a bound `K` valid for every `m ∈ ms`; `(Pz i, Qz i)` is the
coordinate certificate of the `i`-th norm. -/
structure SubCell (a b : ℤ) where
  ms : List (O a b)
  K : ℤ
  aL : ℕ → ℕ → ℤ
  w : ℕ → ℤ
  S : ℤ
  U : ℕ → ℕ → ℤ
  Pz : ℕ → ℕ → ℕ → ℤ
  Qz : ℕ → ℕ → ℕ → ℤ

open ReflectZphi.Cells ReflectZphi.Bridge ReflectZphi.RootNorms ReflectZphi.Minkowski ReflectZphi.Geometry ReflectZphi.Transfer ReflectZphi.Crossing in
/-- **One search of one cell.** As `Cells.cell_oneSign`, for the roots of the norms `d.ms`,
searched in a lattice containing their `L_m`, with a bound valid for these norms. -/
theorem sub_oneSign [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
    {G : Matrix (Fin 3) (Fin 3) (O a b)}
    (hadm : Admissible hd0.le G) {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    (c : CellData a b) (d : SubCell a b) (hqC : 0 < c.qC)
    (hK : ∀ m ∈ d.ms, ι₁ hd0.le (bndElt G c.V c.μ c.pC c.qC m) ≤ d.K)
    (hw : ∀ i, i < 6 → 0 ≤ d.w i) (hS : 0 < d.S)
    (hquad : quadCheck d.aL d.w 6 (gramU d.U (traceGram G c.V c.μ c.qC)) d.S = true)
    (hsub : ∀ i, i < d.ms.length → subCheck G (d.ms.getD i 0) d.U (d.Pz i) (d.Qz i) = true)
    (hm0 : ∀ m ∈ d.ms, m ≠ 0)
    (hcol : colCheck (a := a) (b := b) d.U = true)
    (henum : enumS d.aL d.w 6 2 (leaf2 G n Ps d.ms d.U) (d.S * d.K) = true)
    {r : Fin 3 → O a b} (hr : IsRoot hd0.le G r) (hm' : bil G r r ∈ d.ms)
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
  have htr : ((trace (psiB G c.V c.μ c.qC r r) : ℤ) : ℝ) ≤ d.K := by
    have e := ι₁_add_ι₂ hd0.le (psiB G c.V c.μ c.qC r r)
    rw [trace_def, ← e]
    have hK' := hK _ hm'
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
  -- the coordinates in L_m
  obtain ⟨s, hs⟩ := exists_s hadm.symm hr
  obtain ⟨i, hi, hgi⟩ : ∃ i, i < d.ms.length ∧ d.ms.getD i 0 = bil G r r := by
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm'
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi, e]⟩
  have hsub' := hsub i hi
  rw [hgi] at hsub'
  set z' : ℕ → ℤ := mv (d.Pz i) (coords r) + mv (d.Qz i) (coords s)
  have hsc : vecOf (mv d.U z') = r := sub_coords hsub' (hm0 _ hm') hs
  have hzU : mv d.U z' = coords r := by
    rw [← coords_vecOf (a := a) (b := b) (mv_ge d.U z'), hsc]
  have hpsum : psum d.aL d.w 6 z' 6 ≤ d.S * d.K := by
    rw [quadCheck_sound hquad, qform_gramU, hzU, ← trace_psi_eq, vecOf_coords]
    have h' : trace (psiB G c.V c.μ c.qC r r) ≤ d.K := by exact_mod_cast htr
    exact mul_le_mul_of_nonneg_left h' hS.le
  have hz'0 : ∀ j, 6 ≤ j → z' j = 0 := fun j hj => by
    simp only [z', Pi.add_apply, mv_ge _ _ j hj, add_zero]
  have hleaf := enumS_sound hw (by norm_num) henum z' hz'0 hpsum
  set zf : ℕ → ℤ := fun j => if 2 ≤ j then z' j else 0
  set rf : Fin 3 → O a b := vecOf (mv d.U zf)
  set u0 : Fin 3 → O a b := colVec d.U 0
  set t : O a b := ⟨z' 0, z' 1⟩
  have hreq : r = rf + t • u0 := by
    rw [← hsc]; exact vecOf_mv_split hcol z'
  simp only [leaf2, List.all_eq_true, Bool.and_eq_true] at hleaf
  obtain ⟨hok, hall⟩ := hleaf _ hm'
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
  exact hns (leafCheck_sound hd0 hl hr hm')

/-! ### The cells and the theorem -/

/-- The cheap conditions of one search of one cell (everything but the search). -/
def subPre (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : CellData a b) (d : SubCell a b) : Bool :=
  (d.ms.all fun m => nonneg1 ((d.K : O a b) - bndElt G c.V c.μ c.pC c.qC m) && decide (m ≠ 0)) &&
  ((List.range 6).all fun i => decide (0 ≤ d.w i)) && decide (0 < d.S) &&
  quadCheck d.aL d.w 6 (gramU d.U (traceGram G c.V c.μ c.qC)) d.S &&
  ((List.range d.ms.length).all fun i => subCheck G (d.ms.getD i 0) d.U (d.Pz i) (d.Qz i)) &&
  colCheck (a := a) (b := b) d.U

/-- The search of one norm of one cell. -/
def subEnum (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (d : SubCell a b) : Bool :=
  enumS d.aL d.w 6 2 (leaf2 G n Ps d.ms d.U) (d.S * d.K)

open ReflectZphi.FastLeaf in
/-- A per-norm search through the fast leaf (`leaf4`, table checked by `ldCheck`). -/
theorem subEnum_fast {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {d : SubCell a b} {ld : LeafData a b} (hld : ldCheck G d.U d.ms ld = true)
    (he : enumS d.aL d.w 6 2 (leaf4 G n Ps d.ms d.U ld) (d.S * d.K) = true) :
    subEnum G n Ps d = true :=
  enumAuxS_mono (fun z hz => leaf3_sound hld z (leaf4_sound z hz)) 6 _ _ he

/-- The centre of a cell: future, and `0 < qC`. -/
def cenCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (f : Fin 3 → Fin 3 → O a b) (c : CellData a b) :
    Bool :=
  neg1 (bilE G c.V c.V) && neg1 (bilE G c.V (f 2)) && decide (0 < c.qC)

/-- Every window norm has a search. -/
def normsCovered (norms : List (O a b)) (ds : List (SubCell a b)) : Bool :=
  norms.all fun m => ds.any fun d => decide (m ∈ d.ms)

open ReflectZphi.Cells ReflectZphi.Bridge ReflectZphi.RootNorms in
/-- What a cell gives: every root of a window norm satisfying the cell's crossing bound has
one sign on the vertices. -/
def CellOK (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ)
    (Ps : ℕ → Fin 3 → O a b) (norms : List (O a b)) (c : CellData a b) : Prop :=
  ∀ r, IsRoot hd0.le G r → bil G r r ∈ norms →
    (c.qC : ℝ) * ι₁ hd0.le (bil G r c.V) ^ 2 ≤
      (c.pC - c.qC) * ι₁ hd0.le (bil G r r) * (-ι₁ hd0.le (bil G c.V c.V)) →
    OneSign hd0.le G n Ps r

/-- **A cell from its per-norm searches.** -/
theorem cellOK_of [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
    {G : Matrix (Fin 3) (Fin 3) (O a b)} (hadm : Admissible hd0.le G) {n : ℕ}
    {Ps : ℕ → Fin 3 → O a b} {norms : List (O a b)} {c : CellData a b} (hqC : 0 < c.qC)
    {ds : List (SubCell a b)} (hcov : normsCovered norms ds = true)
    (hds : ∀ d ∈ ds, subPre G c d = true ∧ subEnum G n Ps d = true) :
    CellOK hd0 G n Ps norms c := by
  intro r hr hm hb1
  simp only [normsCovered, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hcov
  obtain ⟨d, hd, hdm⟩ := hcov _ hm
  obtain ⟨hpre, hen⟩ := hds d hd
  simp only [subPre, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    at hpre
  obtain ⟨⟨⟨⟨⟨hKm, hw⟩, hS⟩, hquad⟩, hsub⟩, hcol⟩ := hpre
  have hK : ∀ m ∈ d.ms, ι₁ hd0.le (bndElt G c.V c.μ c.pC c.qC m) ≤ d.K := fun m hm => by
    have := (nonneg1_iff hd0 _).mp (hKm m hm).1
    rw [map_sub, map_intCast] at this
    linarith
  exact sub_oneSign hd0 hadm c d hqC hK hw hS hquad hsub (fun m hm => (hKm m hm).2) hcol hen
    hr hdm hb1

open ReflectZphi.Cells ReflectZphi.Bridge ReflectZphi.RootNorms ReflectZphi.Minkowski
  ReflectZphi.Geometry ReflectZphi.Transfer ReflectZphi.Crossing in
/-- `Cells.hone_of_cells`, with each cell given by `CellOK`. -/
theorem hone_of_cellsM [IsDomain (O a b)] [IsPrincipalIdealRing (O a b)]
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ}
    {f : Fin 3 → Fin 3 → O a b} {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b}
    (hc : PolyCert hd0.le G n f rs Ps Xs)
    (hG : 2 * G.det ≠ 0) {u : O a b} (hu : IsUnit u)
    (hρ : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2) {p q : ℤ} (hq : 0 < q)
    (hpq : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2) {Y S' : ℕ}
    (hY : p * |Nm (2 * G.det)| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2)
    (hS' : 4 * p * |Nm (2 * G.det)| ≤ q * (S' : ℤ) ^ 2)
    {norms : List (O a b)} (hnorms : windowNorms a b (2 * G.det) p q Y S' = norms)
    {N : ℕ} {Bs : ℕ → Fin 3 → O a b} {idx : ℕ → ℕ}
    (hidx : ∀ i, i < n → idx i < N ∧ Bs (idx i) = Ps i)
    (hBB : ∀ j, j < N → ι₁ hd0.le (bil G (Bs j) (Bs j)) < 0)
    (hBs : ∀ j, j < N → ι₁ hd0.le (bil G (Bs j) (f 2)) < 0)
    {nc : ℕ} {cells : ℕ → CellData a b} {seg : ℕ → ℕ}
    (hseg : ∀ j, j + 1 < N → seg j < nc)
    (hCseg : ∀ j, j + 1 < N → ∀ P ∈ [Bs j, Bs (j + 1)],
      ((cells (seg j)).qC : ℝ) * ι₁ hd0.le (bil G (cells (seg j)).V P) ^ 2 ≤
        (cells (seg j)).pC * (ι₁ hd0.le (bil G (cells (seg j)).V (cells (seg j)).V) *
          ι₁ hd0.le (bil G P P)))
    (hVV : ∀ k, k < nc → ι₁ hd0.le (bil G (cells k).V (cells k).V) < 0)
    (hVs : ∀ k, k < nc → ι₁ hd0.le (bil G (cells k).V (f 2)) < 0)
    (hqC : ∀ k, k < nc → 0 < (cells k).qC)
    (hok : ∀ k, k < nc → CellOK hd0 G n Ps norms (cells k)) :
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
  exact hns (hok _ hck r' hr' hmem hb1)

open ReflectZphi.Bridge ReflectZphi.RootNorms in
/-- **Reflectivity from a checked certificate, per-norm sublattice form.** As
`Check.reflective_of_check`, with each cell given by `cenCheck` and `CellOK` (from `cellOK_of`). -/
theorem reflective_of_checkM (hV : VinbergChamber) [IsDomain (O a b)]
    [IsPrincipalIdealRing (O a b)] (hns : ¬ IsSquare (b ^ 2 + 4 * a))
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ}
    {f : Fin 3 → Fin 3 → O a b} {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b}
    {cf : ℕ → Fin 3 → O a b} (hpoly : polyCheck G n f rs Ps Xs cf = true)
    (hadm : admCheck G f = true)
    {D2 u uinv : O a b} {p q : ℤ} {Y S' : ℕ} (hwin : winCheck G D2 u uinv p q Y S' = true)
    {norms : List (O a b)} (hnorms : windowNorms a b D2 p q Y S' = norms)
    {N : ℕ} {Bs : ℕ → Fin 3 → O a b} {idx : ℕ → ℕ} {nc : ℕ} {cells : ℕ → CellData a b}
    {seg : ℕ → ℕ} (hchain : chainCheck G f n Ps N Bs idx nc cells seg = true)
    (hcen : ∀ k, k < nc → cenCheck G f (cells k) = true)
    (hok : ∀ k, k < nc → CellOK hd0 G n Ps norms (cells k)) :
    Reflective hd0.le G := by
  have hc := polyCheck_sound hd0 hpoly
  have hb : basisCheck G f = true := by
    cases hbc : basisCheck G f
    · simp [polyCheck, hbc] at hpoly
    · rfl
  have ha := admCheck_sound hd0 hb hadm
  -- the window
  simp only [winCheck, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hD0⟩, hu⟩, hρ⟩, hpq⟩, hq⟩, hY⟩, hS'⟩ := hwin
  rw [detE_eq] at hD
  subst hD
  have hρ' : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2 := by
    rw [pos1_iff hd0] at hρ
    simp only [map_sub, map_mul, ← ι₂_eq_ι₁_star] at hρ
    nlinarith
  have hpq' : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2 := by
    rw [nonneg1_iff hd0] at hpq
    simp only [map_sub, map_mul, map_intCast, ← ι₂_eq_ι₁_star] at hpq
    nlinarith
  -- the chain
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, vecEq_iff] at hchain
  obtain ⟨⟨hidx, hB⟩, hsegs⟩ := hchain
  simp only [neg1_iff hd0, bilE_eq] at hB
  have hsg : ∀ j, j + 1 < N → seg j < nc ∧ coshCheck G (cells (seg j)) (Bs j) = true ∧
      coshCheck G (cells (seg j)) (Bs (j + 1)) = true := fun j hj => by
    rcases hsegs j (by omega) with h | h
    · omega
    · exact ⟨h.1.1, h.1.2, h.2⟩
  have hcl : ∀ k, k < nc → _ := fun k hk => by
    have h := hcen k hk
    simp only [cenCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  refine reflective_of_cert hV hns ha hc ?_
  refine hone_of_cellsM hd0 hc (by simpa using hD0) (IsUnit.of_mul_eq_one _ hu) hρ' hq
    hpq' hY hS' hnorms (N := N) (Bs := Bs) (idx := idx) hidx (fun j hj => (hB j hj).1)
    (fun j hj => (hB j hj).2) (nc := nc) (cells := cells) (seg := seg)
    (fun j hj => (hsg j hj).1) ?_ ?_ ?_ ?_ ?_
  · intro j hj P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact coshCheck_sound hd0 (hsg j hj).2.1
    · exact coshCheck_sound hd0 (hsg j hj).2.2
  · intro k hk; rw [← bilE_eq]; exact (neg1_iff hd0 _).mp (hcl k hk).1.1
  · intro k hk; rw [← bilE_eq]; exact (neg1_iff hd0 _).mp (hcl k hk).1.2
  · intro k hk; exact (hcl k hk).2
  · exact hok

end ReflectZphi.Sublat

