import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C087.Base
import ReflectZphi.Data.Cert5.C087.Pchk
import ReflectZphi.Data.Cert5.C087.Pnorms
import ReflectZphi.Data.Cert5.C087.P000
import ReflectZphi.Data.Cert5.C087.P001

namespace ReflectZphi.Data.Cert5.C087

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem hd : (0 : ℝ) < ((1 : ℤ) : ℝ) ^ 2 + 4 * ((1 : ℤ) : ℝ) := by norm_num
theorem adm : Admissible hd.le G := admCheck_sound hd basis_ok adm_ok

theorem coverd0_0 : (coverL d0_0.aL d0_0.w 6 2 6 (fun _ => 0) (d0_0.S * d0_0.K) [] preLd0_0).isSome = true := by decide +kernel
theorem subsd0_0 : ∀ q ∈ preLd0_0, subd0_0 q = true := by
  unfold preLd0_0
  exact sbd0_0_0
theorem en_okd0_0 : subEnum G n Ps d0_0 = true :=
  subEnum_fast ld_okd0_0 (enumS_of_coverL coverd0_0 subsd0_0)
theorem coverd0_1 : (coverL d0_1.aL d0_1.w 6 2 6 (fun _ => 0) (d0_1.S * d0_1.K) [] preLd0_1).isSome = true := by decide +kernel
theorem subsd0_1 : ∀ q ∈ preLd0_1, subd0_1 q = true := by
  unfold preLd0_1
  exact sbd0_1_0
theorem en_okd0_1 : subEnum G n Ps d0_1 = true :=
  subEnum_fast ld_okd0_1 (enumS_of_coverL coverd0_1 subsd0_1)
theorem coverd0_2 : (coverL d0_2.aL d0_2.w 6 2 6 (fun _ => 0) (d0_2.S * d0_2.K) [] preLd0_2).isSome = true := by decide +kernel
theorem subsd0_2 : ∀ q ∈ preLd0_2, subd0_2 q = true := by
  unfold preLd0_2
  exact sbd0_2_0
theorem en_okd0_2 : subEnum G n Ps d0_2 = true :=
  subEnum_fast ld_okd0_2 (enumS_of_coverL coverd0_2 subsd0_2)
theorem coverd0_3 : (coverL d0_3.aL d0_3.w 6 2 6 (fun _ => 0) (d0_3.S * d0_3.K) [] preLd0_3).isSome = true := by decide +kernel
theorem subsd0_3 : ∀ q ∈ preLd0_3, subd0_3 q = true := by
  unfold preLd0_3
  exact sbd0_3_0
theorem en_okd0_3 : subEnum G n Ps d0_3 = true :=
  subEnum_fast ld_okd0_3 (enumS_of_coverL coverd0_3 subsd0_3)
theorem coverd0_4 : (coverL d0_4.aL d0_4.w 6 2 6 (fun _ => 0) (d0_4.S * d0_4.K) [] preLd0_4).isSome = true := by decide +kernel
theorem subsd0_4 : ∀ q ∈ preLd0_4, subd0_4 q = true := by
  unfold preLd0_4
  exact sbd0_4_0
theorem en_okd0_4 : subEnum G n Ps d0_4 = true :=
  subEnum_fast ld_okd0_4 (enumS_of_coverL coverd0_4 subsd0_4)
theorem coverd0_5 : (coverL d0_5.aL d0_5.w 6 2 6 (fun _ => 0) (d0_5.S * d0_5.K) [] preLd0_5).isSome = true := by decide +kernel
theorem subsd0_5 : ∀ q ∈ preLd0_5, subd0_5 q = true := by
  unfold preLd0_5
  exact sbd0_5_0
theorem en_okd0_5 : subEnum G n Ps d0_5 = true :=
  subEnum_fast ld_okd0_5 (enumS_of_coverL coverd0_5 subsd0_5)
theorem coverd0_6 : (coverL d0_6.aL d0_6.w 6 2 6 (fun _ => 0) (d0_6.S * d0_6.K) [] preLd0_6).isSome = true := by decide +kernel
theorem subsd0_6 : ∀ q ∈ preLd0_6, subd0_6 q = true := by
  unfold preLd0_6
  exact sbd0_6_0
theorem en_okd0_6 : subEnum G n Ps d0_6 = true :=
  subEnum_fast ld_okd0_6 (enumS_of_coverL coverd0_6 subsd0_6)
theorem coverd0_7 : (coverL d0_7.aL d0_7.w 6 2 6 (fun _ => 0) (d0_7.S * d0_7.K) [] preLd0_7).isSome = true := by decide +kernel
theorem subsd0_7 : ∀ q ∈ preLd0_7, subd0_7 q = true := by
  unfold preLd0_7
  exact sbd0_7_0
theorem en_okd0_7 : subEnum G n Ps d0_7 = true :=
  subEnum_fast ld_okd0_7 (enumS_of_coverL coverd0_7 subsd0_7)
theorem coverd0_8 : (coverL d0_8.aL d0_8.w 6 2 6 (fun _ => 0) (d0_8.S * d0_8.K) [] preLd0_8).isSome = true := by decide +kernel
theorem subsd0_8 : ∀ q ∈ preLd0_8, subd0_8 q = true := by
  unfold preLd0_8
  exact sbd0_8_0
theorem en_okd0_8 : subEnum G n Ps d0_8 = true :=
  subEnum_fast ld_okd0_8 (enumS_of_coverL coverd0_8 subsd0_8)
theorem coverd0_9 : (coverL d0_9.aL d0_9.w 6 2 6 (fun _ => 0) (d0_9.S * d0_9.K) [] preLd0_9).isSome = true := by decide +kernel
theorem subsd0_9 : ∀ q ∈ preLd0_9, subd0_9 q = true := by
  unfold preLd0_9
  exact sbd0_9_0
theorem en_okd0_9 : subEnum G n Ps d0_9 = true :=
  subEnum_fast ld_okd0_9 (enumS_of_coverL coverd0_9 subsd0_9)
theorem coverd0_10 : (coverL d0_10.aL d0_10.w 6 2 6 (fun _ => 0) (d0_10.S * d0_10.K) [] preLd0_10).isSome = true := by decide +kernel
theorem subsd0_10 : ∀ q ∈ preLd0_10, subd0_10 q = true := by
  unfold preLd0_10
  exact sbd0_10_0
theorem en_okd0_10 : subEnum G n Ps d0_10 = true :=
  subEnum_fast ld_okd0_10 (enumS_of_coverL coverd0_10 subsd0_10)
theorem coverd0_11 : (coverL d0_11.aL d0_11.w 6 2 6 (fun _ => 0) (d0_11.S * d0_11.K) [] preLd0_11).isSome = true := by decide +kernel
theorem subsd0_11 : ∀ q ∈ preLd0_11, subd0_11 q = true := by
  unfold preLd0_11
  exact sbd0_11_0
theorem en_okd0_11 : subEnum G n Ps d0_11 = true :=
  subEnum_fast ld_okd0_11 (enumS_of_coverL coverd0_11 subsd0_11)
theorem cov_ok0 : normsCovered normsL [d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6, d0_7, d0_8, d0_9, d0_10, d0_11] = true := by decide +kernel
theorem cell_ok0 : CellOK hd G n Ps normsL cell0 :=
  cellOK_of hd adm (by decide +kernel) cov_ok0 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd0_0, en_okd0_0⟩
    · exact ⟨pre_okd0_1, en_okd0_1⟩
    · exact ⟨pre_okd0_2, en_okd0_2⟩
    · exact ⟨pre_okd0_3, en_okd0_3⟩
    · exact ⟨pre_okd0_4, en_okd0_4⟩
    · exact ⟨pre_okd0_5, en_okd0_5⟩
    · exact ⟨pre_okd0_6, en_okd0_6⟩
    · exact ⟨pre_okd0_7, en_okd0_7⟩
    · exact ⟨pre_okd0_8, en_okd0_8⟩
    · exact ⟨pre_okd0_9, en_okd0_9⟩
    · exact ⟨pre_okd0_10, en_okd0_10⟩
    · exact ⟨pre_okd0_11, en_okd0_11⟩
  )

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C087
