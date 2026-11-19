import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C088.Base
import ReflectZphi.Data.Cert5.C088.Pchk
import ReflectZphi.Data.Cert5.C088.Pnorms
import ReflectZphi.Data.Cert5.C088.P000
import ReflectZphi.Data.Cert5.C088.P001
import ReflectZphi.Data.Cert5.C088.P002
import ReflectZphi.Data.Cert5.C088.P003
import ReflectZphi.Data.Cert5.C088.P004
import ReflectZphi.Data.Cert5.C088.P005
import ReflectZphi.Data.Cert5.C088.P006
import ReflectZphi.Data.Cert5.C088.P007
import ReflectZphi.Data.Cert5.C088.P008
import ReflectZphi.Data.Cert5.C088.P009
import ReflectZphi.Data.Cert5.C088.P010

namespace ReflectZphi.Data.Cert5.C088

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
theorem coverd0_12 : (coverL d0_12.aL d0_12.w 6 2 6 (fun _ => 0) (d0_12.S * d0_12.K) [] preLd0_12).isSome = true := by decide +kernel
theorem subsd0_12 : ∀ q ∈ preLd0_12, subd0_12 q = true := by
  unfold preLd0_12
  exact sbd0_12_0
theorem en_okd0_12 : subEnum G n Ps d0_12 = true :=
  subEnum_fast ld_okd0_12 (enumS_of_coverL coverd0_12 subsd0_12)
theorem coverd0_13 : (coverL d0_13.aL d0_13.w 6 2 6 (fun _ => 0) (d0_13.S * d0_13.K) [] preLd0_13).isSome = true := by decide +kernel
theorem subsd0_13 : ∀ q ∈ preLd0_13, subd0_13 q = true := by
  unfold preLd0_13
  exact sbd0_13_0
theorem en_okd0_13 : subEnum G n Ps d0_13 = true :=
  subEnum_fast ld_okd0_13 (enumS_of_coverL coverd0_13 subsd0_13)
theorem cov_ok0 : normsCovered normsL [d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6, d0_7, d0_8, d0_9, d0_10, d0_11, d0_12, d0_13] = true := by decide +kernel
theorem cell_ok0 : CellOK hd G n Ps normsL cell0 :=
  cellOK_of hd adm (by decide +kernel) cov_ok0 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd0_12, en_okd0_12⟩
    · exact ⟨pre_okd0_13, en_okd0_13⟩
  )
theorem coverd1_0 : (coverL d1_0.aL d1_0.w 6 2 6 (fun _ => 0) (d1_0.S * d1_0.K) [] preLd1_0).isSome = true := by decide +kernel
theorem subsd1_0 : ∀ q ∈ preLd1_0, subd1_0 q = true := by
  unfold preLd1_0
  exact sbd1_0_0
theorem en_okd1_0 : subEnum G n Ps d1_0 = true :=
  subEnum_fast ld_okd1_0 (enumS_of_coverL coverd1_0 subsd1_0)
theorem coverd1_1 : (coverL d1_1.aL d1_1.w 6 2 6 (fun _ => 0) (d1_1.S * d1_1.K) [] preLd1_1).isSome = true := by decide +kernel
theorem subsd1_1 : ∀ q ∈ preLd1_1, subd1_1 q = true := by
  unfold preLd1_1
  exact sbd1_1_0
theorem en_okd1_1 : subEnum G n Ps d1_1 = true :=
  subEnum_fast ld_okd1_1 (enumS_of_coverL coverd1_1 subsd1_1)
theorem coverd1_2 : (coverL d1_2.aL d1_2.w 6 2 6 (fun _ => 0) (d1_2.S * d1_2.K) [] preLd1_2).isSome = true := by decide +kernel
theorem subsd1_2 : ∀ q ∈ preLd1_2, subd1_2 q = true := by
  unfold preLd1_2
  exact sbd1_2_0
theorem en_okd1_2 : subEnum G n Ps d1_2 = true :=
  subEnum_fast ld_okd1_2 (enumS_of_coverL coverd1_2 subsd1_2)
theorem coverd1_3 : (coverL d1_3.aL d1_3.w 6 2 6 (fun _ => 0) (d1_3.S * d1_3.K) [] preLd1_3).isSome = true := by decide +kernel
theorem subsd1_3 : ∀ q ∈ preLd1_3, subd1_3 q = true := by
  unfold preLd1_3
  exact sbd1_3_0
theorem en_okd1_3 : subEnum G n Ps d1_3 = true :=
  subEnum_fast ld_okd1_3 (enumS_of_coverL coverd1_3 subsd1_3)
theorem coverd1_4 : (coverL d1_4.aL d1_4.w 6 2 6 (fun _ => 0) (d1_4.S * d1_4.K) [] preLd1_4).isSome = true := by decide +kernel
theorem subsd1_4 : ∀ q ∈ preLd1_4, subd1_4 q = true := by
  unfold preLd1_4
  exact sbd1_4_0
theorem en_okd1_4 : subEnum G n Ps d1_4 = true :=
  subEnum_fast ld_okd1_4 (enumS_of_coverL coverd1_4 subsd1_4)
theorem coverd1_5 : (coverL d1_5.aL d1_5.w 6 2 6 (fun _ => 0) (d1_5.S * d1_5.K) [] preLd1_5).isSome = true := by decide +kernel
theorem subsd1_5 : ∀ q ∈ preLd1_5, subd1_5 q = true := by
  unfold preLd1_5
  exact sbd1_5_0
theorem en_okd1_5 : subEnum G n Ps d1_5 = true :=
  subEnum_fast ld_okd1_5 (enumS_of_coverL coverd1_5 subsd1_5)
theorem coverd1_6 : (coverL d1_6.aL d1_6.w 6 2 6 (fun _ => 0) (d1_6.S * d1_6.K) [] preLd1_6).isSome = true := by decide +kernel
theorem subsd1_6 : ∀ q ∈ preLd1_6, subd1_6 q = true := by
  unfold preLd1_6
  exact sbd1_6_0
theorem en_okd1_6 : subEnum G n Ps d1_6 = true :=
  subEnum_fast ld_okd1_6 (enumS_of_coverL coverd1_6 subsd1_6)
theorem coverd1_7 : (coverL d1_7.aL d1_7.w 6 2 6 (fun _ => 0) (d1_7.S * d1_7.K) [] preLd1_7).isSome = true := by decide +kernel
theorem subsd1_7 : ∀ q ∈ preLd1_7, subd1_7 q = true := by
  unfold preLd1_7
  exact sbd1_7_0
theorem en_okd1_7 : subEnum G n Ps d1_7 = true :=
  subEnum_fast ld_okd1_7 (enumS_of_coverL coverd1_7 subsd1_7)
theorem coverd1_8 : (coverL d1_8.aL d1_8.w 6 2 6 (fun _ => 0) (d1_8.S * d1_8.K) [] preLd1_8).isSome = true := by decide +kernel
theorem subsd1_8 : ∀ q ∈ preLd1_8, subd1_8 q = true := by
  unfold preLd1_8
  exact sbd1_8_0
theorem en_okd1_8 : subEnum G n Ps d1_8 = true :=
  subEnum_fast ld_okd1_8 (enumS_of_coverL coverd1_8 subsd1_8)
theorem coverd1_9 : (coverL d1_9.aL d1_9.w 6 2 6 (fun _ => 0) (d1_9.S * d1_9.K) [] preLd1_9).isSome = true := by decide +kernel
theorem subsd1_9 : ∀ q ∈ preLd1_9, subd1_9 q = true := by
  unfold preLd1_9
  exact sbd1_9_0
theorem en_okd1_9 : subEnum G n Ps d1_9 = true :=
  subEnum_fast ld_okd1_9 (enumS_of_coverL coverd1_9 subsd1_9)
theorem coverd1_10 : (coverL d1_10.aL d1_10.w 6 2 6 (fun _ => 0) (d1_10.S * d1_10.K) [] preLd1_10).isSome = true := by decide +kernel
theorem subsd1_10 : ∀ q ∈ preLd1_10, subd1_10 q = true := by
  unfold preLd1_10
  exact sbd1_10_0
theorem en_okd1_10 : subEnum G n Ps d1_10 = true :=
  subEnum_fast ld_okd1_10 (enumS_of_coverL coverd1_10 subsd1_10)
theorem coverd1_11 : (coverL d1_11.aL d1_11.w 6 2 6 (fun _ => 0) (d1_11.S * d1_11.K) [] preLd1_11).isSome = true := by decide +kernel
theorem subsd1_11 : ∀ q ∈ preLd1_11, subd1_11 q = true := by
  unfold preLd1_11
  exact sbd1_11_0
theorem en_okd1_11 : subEnum G n Ps d1_11 = true :=
  subEnum_fast ld_okd1_11 (enumS_of_coverL coverd1_11 subsd1_11)
theorem coverd1_12 : (coverL d1_12.aL d1_12.w 6 2 6 (fun _ => 0) (d1_12.S * d1_12.K) [] preLd1_12).isSome = true := by decide +kernel
theorem subsd1_12 : ∀ q ∈ preLd1_12, subd1_12 q = true := by
  unfold preLd1_12
  exact sbd1_12_0
theorem en_okd1_12 : subEnum G n Ps d1_12 = true :=
  subEnum_fast ld_okd1_12 (enumS_of_coverL coverd1_12 subsd1_12)
theorem coverd1_13 : (coverL d1_13.aL d1_13.w 6 2 6 (fun _ => 0) (d1_13.S * d1_13.K) [] preLd1_13).isSome = true := by decide +kernel
theorem subsd1_13 : ∀ q ∈ preLd1_13, subd1_13 q = true := by
  unfold preLd1_13
  exact sbd1_13_0
theorem en_okd1_13 : subEnum G n Ps d1_13 = true :=
  subEnum_fast ld_okd1_13 (enumS_of_coverL coverd1_13 subsd1_13)
theorem cov_ok1 : normsCovered normsL [d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6, d1_7, d1_8, d1_9, d1_10, d1_11, d1_12, d1_13] = true := by decide +kernel
theorem cell_ok1 : CellOK hd G n Ps normsL cell1 :=
  cellOK_of hd adm (by decide +kernel) cov_ok1 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd1_0, en_okd1_0⟩
    · exact ⟨pre_okd1_1, en_okd1_1⟩
    · exact ⟨pre_okd1_2, en_okd1_2⟩
    · exact ⟨pre_okd1_3, en_okd1_3⟩
    · exact ⟨pre_okd1_4, en_okd1_4⟩
    · exact ⟨pre_okd1_5, en_okd1_5⟩
    · exact ⟨pre_okd1_6, en_okd1_6⟩
    · exact ⟨pre_okd1_7, en_okd1_7⟩
    · exact ⟨pre_okd1_8, en_okd1_8⟩
    · exact ⟨pre_okd1_9, en_okd1_9⟩
    · exact ⟨pre_okd1_10, en_okd1_10⟩
    · exact ⟨pre_okd1_11, en_okd1_11⟩
    · exact ⟨pre_okd1_12, en_okd1_12⟩
    · exact ⟨pre_okd1_13, en_okd1_13⟩
  )
theorem coverd2_0 : (coverL d2_0.aL d2_0.w 6 2 6 (fun _ => 0) (d2_0.S * d2_0.K) [] preLd2_0).isSome = true := by decide +kernel
theorem subsd2_0 : ∀ q ∈ preLd2_0, subd2_0 q = true := by
  unfold preLd2_0
  exact sbd2_0_0
theorem en_okd2_0 : subEnum G n Ps d2_0 = true :=
  subEnum_fast ld_okd2_0 (enumS_of_coverL coverd2_0 subsd2_0)
theorem coverd2_1 : (coverL d2_1.aL d2_1.w 6 2 6 (fun _ => 0) (d2_1.S * d2_1.K) [] preLd2_1).isSome = true := by decide +kernel
theorem subsd2_1 : ∀ q ∈ preLd2_1, subd2_1 q = true := by
  unfold preLd2_1
  exact sbd2_1_0
theorem en_okd2_1 : subEnum G n Ps d2_1 = true :=
  subEnum_fast ld_okd2_1 (enumS_of_coverL coverd2_1 subsd2_1)
theorem coverd2_2 : (coverL d2_2.aL d2_2.w 6 2 6 (fun _ => 0) (d2_2.S * d2_2.K) [] preLd2_2).isSome = true := by decide +kernel
theorem subsd2_2 : ∀ q ∈ preLd2_2, subd2_2 q = true := by
  unfold preLd2_2
  exact sbd2_2_0
theorem en_okd2_2 : subEnum G n Ps d2_2 = true :=
  subEnum_fast ld_okd2_2 (enumS_of_coverL coverd2_2 subsd2_2)
theorem coverd2_3 : (coverL d2_3.aL d2_3.w 6 2 6 (fun _ => 0) (d2_3.S * d2_3.K) [] preLd2_3).isSome = true := by decide +kernel
theorem subsd2_3 : ∀ q ∈ preLd2_3, subd2_3 q = true := by
  unfold preLd2_3
  exact sbd2_3_0
theorem en_okd2_3 : subEnum G n Ps d2_3 = true :=
  subEnum_fast ld_okd2_3 (enumS_of_coverL coverd2_3 subsd2_3)
theorem coverd2_4 : (coverL d2_4.aL d2_4.w 6 2 6 (fun _ => 0) (d2_4.S * d2_4.K) [] preLd2_4).isSome = true := by decide +kernel
theorem subsd2_4 : ∀ q ∈ preLd2_4, subd2_4 q = true := by
  unfold preLd2_4
  exact sbd2_4_0
theorem en_okd2_4 : subEnum G n Ps d2_4 = true :=
  subEnum_fast ld_okd2_4 (enumS_of_coverL coverd2_4 subsd2_4)
theorem coverd2_5 : (coverL d2_5.aL d2_5.w 6 2 6 (fun _ => 0) (d2_5.S * d2_5.K) [] preLd2_5).isSome = true := by decide +kernel
theorem subsd2_5 : ∀ q ∈ preLd2_5, subd2_5 q = true := by
  unfold preLd2_5
  exact sbd2_5_0
theorem en_okd2_5 : subEnum G n Ps d2_5 = true :=
  subEnum_fast ld_okd2_5 (enumS_of_coverL coverd2_5 subsd2_5)
theorem coverd2_6 : (coverL d2_6.aL d2_6.w 6 2 6 (fun _ => 0) (d2_6.S * d2_6.K) [] preLd2_6).isSome = true := by decide +kernel
theorem subsd2_6 : ∀ q ∈ preLd2_6, subd2_6 q = true := by
  unfold preLd2_6
  exact sbd2_6_0
theorem en_okd2_6 : subEnum G n Ps d2_6 = true :=
  subEnum_fast ld_okd2_6 (enumS_of_coverL coverd2_6 subsd2_6)
theorem coverd2_7 : (coverL d2_7.aL d2_7.w 6 2 6 (fun _ => 0) (d2_7.S * d2_7.K) [] preLd2_7).isSome = true := by decide +kernel
theorem subsd2_7 : ∀ q ∈ preLd2_7, subd2_7 q = true := by
  unfold preLd2_7
  exact sbd2_7_0
theorem en_okd2_7 : subEnum G n Ps d2_7 = true :=
  subEnum_fast ld_okd2_7 (enumS_of_coverL coverd2_7 subsd2_7)
theorem coverd2_8 : (coverL d2_8.aL d2_8.w 6 2 6 (fun _ => 0) (d2_8.S * d2_8.K) [] preLd2_8).isSome = true := by decide +kernel
theorem subsd2_8 : ∀ q ∈ preLd2_8, subd2_8 q = true := by
  unfold preLd2_8
  exact sbd2_8_0
theorem en_okd2_8 : subEnum G n Ps d2_8 = true :=
  subEnum_fast ld_okd2_8 (enumS_of_coverL coverd2_8 subsd2_8)
theorem coverd2_9 : (coverL d2_9.aL d2_9.w 6 2 6 (fun _ => 0) (d2_9.S * d2_9.K) [] preLd2_9).isSome = true := by decide +kernel
theorem subsd2_9 : ∀ q ∈ preLd2_9, subd2_9 q = true := by
  unfold preLd2_9
  exact sbd2_9_0
theorem en_okd2_9 : subEnum G n Ps d2_9 = true :=
  subEnum_fast ld_okd2_9 (enumS_of_coverL coverd2_9 subsd2_9)
theorem coverd2_10 : (coverL d2_10.aL d2_10.w 6 2 6 (fun _ => 0) (d2_10.S * d2_10.K) [] preLd2_10).isSome = true := by decide +kernel
theorem subsd2_10 : ∀ q ∈ preLd2_10, subd2_10 q = true := by
  unfold preLd2_10
  exact sbd2_10_0
theorem en_okd2_10 : subEnum G n Ps d2_10 = true :=
  subEnum_fast ld_okd2_10 (enumS_of_coverL coverd2_10 subsd2_10)
theorem coverd2_11 : (coverL d2_11.aL d2_11.w 6 2 6 (fun _ => 0) (d2_11.S * d2_11.K) [] preLd2_11).isSome = true := by decide +kernel
theorem subsd2_11 : ∀ q ∈ preLd2_11, subd2_11 q = true := by
  unfold preLd2_11
  exact sbd2_11_0
theorem en_okd2_11 : subEnum G n Ps d2_11 = true :=
  subEnum_fast ld_okd2_11 (enumS_of_coverL coverd2_11 subsd2_11)
theorem coverd2_12 : (coverL d2_12.aL d2_12.w 6 2 6 (fun _ => 0) (d2_12.S * d2_12.K) [] preLd2_12).isSome = true := by decide +kernel
theorem subsd2_12 : ∀ q ∈ preLd2_12, subd2_12 q = true := by
  unfold preLd2_12
  exact sbd2_12_0
theorem en_okd2_12 : subEnum G n Ps d2_12 = true :=
  subEnum_fast ld_okd2_12 (enumS_of_coverL coverd2_12 subsd2_12)
theorem coverd2_13 : (coverL d2_13.aL d2_13.w 6 2 6 (fun _ => 0) (d2_13.S * d2_13.K) [] preLd2_13).isSome = true := by decide +kernel
theorem subsd2_13 : ∀ q ∈ preLd2_13, subd2_13 q = true := by
  unfold preLd2_13
  exact sbd2_13_0
theorem en_okd2_13 : subEnum G n Ps d2_13 = true :=
  subEnum_fast ld_okd2_13 (enumS_of_coverL coverd2_13 subsd2_13)
theorem cov_ok2 : normsCovered normsL [d2_0, d2_1, d2_2, d2_3, d2_4, d2_5, d2_6, d2_7, d2_8, d2_9, d2_10, d2_11, d2_12, d2_13] = true := by decide +kernel
theorem cell_ok2 : CellOK hd G n Ps normsL cell2 :=
  cellOK_of hd adm (by decide +kernel) cov_ok2 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd2_0, en_okd2_0⟩
    · exact ⟨pre_okd2_1, en_okd2_1⟩
    · exact ⟨pre_okd2_2, en_okd2_2⟩
    · exact ⟨pre_okd2_3, en_okd2_3⟩
    · exact ⟨pre_okd2_4, en_okd2_4⟩
    · exact ⟨pre_okd2_5, en_okd2_5⟩
    · exact ⟨pre_okd2_6, en_okd2_6⟩
    · exact ⟨pre_okd2_7, en_okd2_7⟩
    · exact ⟨pre_okd2_8, en_okd2_8⟩
    · exact ⟨pre_okd2_9, en_okd2_9⟩
    · exact ⟨pre_okd2_10, en_okd2_10⟩
    · exact ⟨pre_okd2_11, en_okd2_11⟩
    · exact ⟨pre_okd2_12, en_okd2_12⟩
    · exact ⟨pre_okd2_13, en_okd2_13⟩
  )
theorem coverd3_0 : (coverL d3_0.aL d3_0.w 6 2 6 (fun _ => 0) (d3_0.S * d3_0.K) [] preLd3_0).isSome = true := by decide +kernel
theorem subsd3_0 : ∀ q ∈ preLd3_0, subd3_0 q = true := by
  unfold preLd3_0
  exact sbd3_0_0
theorem en_okd3_0 : subEnum G n Ps d3_0 = true :=
  subEnum_fast ld_okd3_0 (enumS_of_coverL coverd3_0 subsd3_0)
theorem coverd3_1 : (coverL d3_1.aL d3_1.w 6 2 6 (fun _ => 0) (d3_1.S * d3_1.K) [] preLd3_1).isSome = true := by decide +kernel
theorem subsd3_1 : ∀ q ∈ preLd3_1, subd3_1 q = true := by
  unfold preLd3_1
  exact sbd3_1_0
theorem en_okd3_1 : subEnum G n Ps d3_1 = true :=
  subEnum_fast ld_okd3_1 (enumS_of_coverL coverd3_1 subsd3_1)
theorem coverd3_2 : (coverL d3_2.aL d3_2.w 6 2 6 (fun _ => 0) (d3_2.S * d3_2.K) [] preLd3_2).isSome = true := by decide +kernel
theorem subsd3_2 : ∀ q ∈ preLd3_2, subd3_2 q = true := by
  unfold preLd3_2
  exact sbd3_2_0
theorem en_okd3_2 : subEnum G n Ps d3_2 = true :=
  subEnum_fast ld_okd3_2 (enumS_of_coverL coverd3_2 subsd3_2)
theorem coverd3_3 : (coverL d3_3.aL d3_3.w 6 2 6 (fun _ => 0) (d3_3.S * d3_3.K) [] preLd3_3).isSome = true := by decide +kernel
theorem subsd3_3 : ∀ q ∈ preLd3_3, subd3_3 q = true := by
  unfold preLd3_3
  exact sbd3_3_0
theorem en_okd3_3 : subEnum G n Ps d3_3 = true :=
  subEnum_fast ld_okd3_3 (enumS_of_coverL coverd3_3 subsd3_3)
theorem coverd3_4 : (coverL d3_4.aL d3_4.w 6 2 6 (fun _ => 0) (d3_4.S * d3_4.K) [] preLd3_4).isSome = true := by decide +kernel
theorem subsd3_4 : ∀ q ∈ preLd3_4, subd3_4 q = true := by
  unfold preLd3_4
  exact sbd3_4_0
theorem en_okd3_4 : subEnum G n Ps d3_4 = true :=
  subEnum_fast ld_okd3_4 (enumS_of_coverL coverd3_4 subsd3_4)
theorem coverd3_5 : (coverL d3_5.aL d3_5.w 6 2 6 (fun _ => 0) (d3_5.S * d3_5.K) [] preLd3_5).isSome = true := by decide +kernel
theorem subsd3_5 : ∀ q ∈ preLd3_5, subd3_5 q = true := by
  unfold preLd3_5
  exact sbd3_5_0
theorem en_okd3_5 : subEnum G n Ps d3_5 = true :=
  subEnum_fast ld_okd3_5 (enumS_of_coverL coverd3_5 subsd3_5)
theorem coverd3_6 : (coverL d3_6.aL d3_6.w 6 2 6 (fun _ => 0) (d3_6.S * d3_6.K) [] preLd3_6).isSome = true := by decide +kernel
theorem subsd3_6 : ∀ q ∈ preLd3_6, subd3_6 q = true := by
  unfold preLd3_6
  exact sbd3_6_0
theorem en_okd3_6 : subEnum G n Ps d3_6 = true :=
  subEnum_fast ld_okd3_6 (enumS_of_coverL coverd3_6 subsd3_6)
theorem coverd3_7 : (coverL d3_7.aL d3_7.w 6 2 6 (fun _ => 0) (d3_7.S * d3_7.K) [] preLd3_7).isSome = true := by decide +kernel
theorem subsd3_7 : ∀ q ∈ preLd3_7, subd3_7 q = true := by
  unfold preLd3_7
  exact sbd3_7_0
theorem en_okd3_7 : subEnum G n Ps d3_7 = true :=
  subEnum_fast ld_okd3_7 (enumS_of_coverL coverd3_7 subsd3_7)
theorem coverd3_8 : (coverL d3_8.aL d3_8.w 6 2 6 (fun _ => 0) (d3_8.S * d3_8.K) [] preLd3_8).isSome = true := by decide +kernel
theorem subsd3_8 : ∀ q ∈ preLd3_8, subd3_8 q = true := by
  unfold preLd3_8
  exact sbd3_8_0
theorem en_okd3_8 : subEnum G n Ps d3_8 = true :=
  subEnum_fast ld_okd3_8 (enumS_of_coverL coverd3_8 subsd3_8)
theorem coverd3_9 : (coverL d3_9.aL d3_9.w 6 2 6 (fun _ => 0) (d3_9.S * d3_9.K) [] preLd3_9).isSome = true := by decide +kernel
theorem subsd3_9 : ∀ q ∈ preLd3_9, subd3_9 q = true := by
  unfold preLd3_9
  exact sbd3_9_0
theorem en_okd3_9 : subEnum G n Ps d3_9 = true :=
  subEnum_fast ld_okd3_9 (enumS_of_coverL coverd3_9 subsd3_9)
theorem coverd3_10 : (coverL d3_10.aL d3_10.w 6 2 6 (fun _ => 0) (d3_10.S * d3_10.K) [] preLd3_10).isSome = true := by decide +kernel
theorem subsd3_10 : ∀ q ∈ preLd3_10, subd3_10 q = true := by
  unfold preLd3_10
  exact sbd3_10_0
theorem en_okd3_10 : subEnum G n Ps d3_10 = true :=
  subEnum_fast ld_okd3_10 (enumS_of_coverL coverd3_10 subsd3_10)
theorem coverd3_11 : (coverL d3_11.aL d3_11.w 6 2 6 (fun _ => 0) (d3_11.S * d3_11.K) [] preLd3_11).isSome = true := by decide +kernel
theorem subsd3_11 : ∀ q ∈ preLd3_11, subd3_11 q = true := by
  unfold preLd3_11
  exact sbd3_11_0
theorem en_okd3_11 : subEnum G n Ps d3_11 = true :=
  subEnum_fast ld_okd3_11 (enumS_of_coverL coverd3_11 subsd3_11)
theorem coverd3_12 : (coverL d3_12.aL d3_12.w 6 2 6 (fun _ => 0) (d3_12.S * d3_12.K) [] preLd3_12).isSome = true := by decide +kernel
theorem subsd3_12 : ∀ q ∈ preLd3_12, subd3_12 q = true := by
  unfold preLd3_12
  exact sbd3_12_0
theorem en_okd3_12 : subEnum G n Ps d3_12 = true :=
  subEnum_fast ld_okd3_12 (enumS_of_coverL coverd3_12 subsd3_12)
theorem coverd3_13 : (coverL d3_13.aL d3_13.w 6 2 6 (fun _ => 0) (d3_13.S * d3_13.K) [] preLd3_13).isSome = true := by decide +kernel
theorem subsd3_13 : ∀ q ∈ preLd3_13, subd3_13 q = true := by
  unfold preLd3_13
  exact sbd3_13_0
theorem en_okd3_13 : subEnum G n Ps d3_13 = true :=
  subEnum_fast ld_okd3_13 (enumS_of_coverL coverd3_13 subsd3_13)
theorem cov_ok3 : normsCovered normsL [d3_0, d3_1, d3_2, d3_3, d3_4, d3_5, d3_6, d3_7, d3_8, d3_9, d3_10, d3_11, d3_12, d3_13] = true := by decide +kernel
theorem cell_ok3 : CellOK hd G n Ps normsL cell3 :=
  cellOK_of hd adm (by decide +kernel) cov_ok3 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd3_0, en_okd3_0⟩
    · exact ⟨pre_okd3_1, en_okd3_1⟩
    · exact ⟨pre_okd3_2, en_okd3_2⟩
    · exact ⟨pre_okd3_3, en_okd3_3⟩
    · exact ⟨pre_okd3_4, en_okd3_4⟩
    · exact ⟨pre_okd3_5, en_okd3_5⟩
    · exact ⟨pre_okd3_6, en_okd3_6⟩
    · exact ⟨pre_okd3_7, en_okd3_7⟩
    · exact ⟨pre_okd3_8, en_okd3_8⟩
    · exact ⟨pre_okd3_9, en_okd3_9⟩
    · exact ⟨pre_okd3_10, en_okd3_10⟩
    · exact ⟨pre_okd3_11, en_okd3_11⟩
    · exact ⟨pre_okd3_12, en_okd3_12⟩
    · exact ⟨pre_okd3_13, en_okd3_13⟩
  )
theorem coverd4_0 : (coverL d4_0.aL d4_0.w 6 2 6 (fun _ => 0) (d4_0.S * d4_0.K) [] preLd4_0).isSome = true := by decide +kernel
theorem subsd4_0 : ∀ q ∈ preLd4_0, subd4_0 q = true := by
  unfold preLd4_0
  exact sbd4_0_0
theorem en_okd4_0 : subEnum G n Ps d4_0 = true :=
  subEnum_fast ld_okd4_0 (enumS_of_coverL coverd4_0 subsd4_0)
theorem coverd4_1 : (coverL d4_1.aL d4_1.w 6 2 6 (fun _ => 0) (d4_1.S * d4_1.K) [] preLd4_1).isSome = true := by decide +kernel
theorem subsd4_1 : ∀ q ∈ preLd4_1, subd4_1 q = true := by
  unfold preLd4_1
  exact sbd4_1_0
theorem en_okd4_1 : subEnum G n Ps d4_1 = true :=
  subEnum_fast ld_okd4_1 (enumS_of_coverL coverd4_1 subsd4_1)
theorem coverd4_2 : (coverL d4_2.aL d4_2.w 6 2 6 (fun _ => 0) (d4_2.S * d4_2.K) [] preLd4_2).isSome = true := by decide +kernel
theorem subsd4_2 : ∀ q ∈ preLd4_2, subd4_2 q = true := by
  unfold preLd4_2
  exact sbd4_2_0
theorem en_okd4_2 : subEnum G n Ps d4_2 = true :=
  subEnum_fast ld_okd4_2 (enumS_of_coverL coverd4_2 subsd4_2)
theorem coverd4_3 : (coverL d4_3.aL d4_3.w 6 2 6 (fun _ => 0) (d4_3.S * d4_3.K) [] preLd4_3).isSome = true := by decide +kernel
theorem subsd4_3 : ∀ q ∈ preLd4_3, subd4_3 q = true := by
  unfold preLd4_3
  exact sbd4_3_0
theorem en_okd4_3 : subEnum G n Ps d4_3 = true :=
  subEnum_fast ld_okd4_3 (enumS_of_coverL coverd4_3 subsd4_3)
theorem coverd4_4 : (coverL d4_4.aL d4_4.w 6 2 6 (fun _ => 0) (d4_4.S * d4_4.K) [] preLd4_4).isSome = true := by decide +kernel
theorem subsd4_4 : ∀ q ∈ preLd4_4, subd4_4 q = true := by
  unfold preLd4_4
  exact sbd4_4_0
theorem en_okd4_4 : subEnum G n Ps d4_4 = true :=
  subEnum_fast ld_okd4_4 (enumS_of_coverL coverd4_4 subsd4_4)
theorem coverd4_5 : (coverL d4_5.aL d4_5.w 6 2 6 (fun _ => 0) (d4_5.S * d4_5.K) [] preLd4_5).isSome = true := by decide +kernel
theorem subsd4_5 : ∀ q ∈ preLd4_5, subd4_5 q = true := by
  unfold preLd4_5
  exact sbd4_5_0
theorem en_okd4_5 : subEnum G n Ps d4_5 = true :=
  subEnum_fast ld_okd4_5 (enumS_of_coverL coverd4_5 subsd4_5)
theorem coverd4_6 : (coverL d4_6.aL d4_6.w 6 2 6 (fun _ => 0) (d4_6.S * d4_6.K) [] preLd4_6).isSome = true := by decide +kernel
theorem subsd4_6 : ∀ q ∈ preLd4_6, subd4_6 q = true := by
  unfold preLd4_6
  exact sbd4_6_0
theorem en_okd4_6 : subEnum G n Ps d4_6 = true :=
  subEnum_fast ld_okd4_6 (enumS_of_coverL coverd4_6 subsd4_6)
theorem coverd4_7 : (coverL d4_7.aL d4_7.w 6 2 6 (fun _ => 0) (d4_7.S * d4_7.K) [] preLd4_7).isSome = true := by decide +kernel
theorem subsd4_7 : ∀ q ∈ preLd4_7, subd4_7 q = true := by
  unfold preLd4_7
  exact sbd4_7_0
theorem en_okd4_7 : subEnum G n Ps d4_7 = true :=
  subEnum_fast ld_okd4_7 (enumS_of_coverL coverd4_7 subsd4_7)
theorem coverd4_8 : (coverL d4_8.aL d4_8.w 6 2 6 (fun _ => 0) (d4_8.S * d4_8.K) [] preLd4_8).isSome = true := by decide +kernel
theorem subsd4_8 : ∀ q ∈ preLd4_8, subd4_8 q = true := by
  unfold preLd4_8
  exact sbd4_8_0
theorem en_okd4_8 : subEnum G n Ps d4_8 = true :=
  subEnum_fast ld_okd4_8 (enumS_of_coverL coverd4_8 subsd4_8)
theorem coverd4_9 : (coverL d4_9.aL d4_9.w 6 2 6 (fun _ => 0) (d4_9.S * d4_9.K) [] preLd4_9).isSome = true := by decide +kernel
theorem subsd4_9 : ∀ q ∈ preLd4_9, subd4_9 q = true := by
  unfold preLd4_9
  exact sbd4_9_0
theorem en_okd4_9 : subEnum G n Ps d4_9 = true :=
  subEnum_fast ld_okd4_9 (enumS_of_coverL coverd4_9 subsd4_9)
theorem coverd4_10 : (coverL d4_10.aL d4_10.w 6 2 6 (fun _ => 0) (d4_10.S * d4_10.K) [] preLd4_10).isSome = true := by decide +kernel
theorem subsd4_10 : ∀ q ∈ preLd4_10, subd4_10 q = true := by
  unfold preLd4_10
  exact sbd4_10_0
theorem en_okd4_10 : subEnum G n Ps d4_10 = true :=
  subEnum_fast ld_okd4_10 (enumS_of_coverL coverd4_10 subsd4_10)
theorem coverd4_11 : (coverL d4_11.aL d4_11.w 6 2 6 (fun _ => 0) (d4_11.S * d4_11.K) [] preLd4_11).isSome = true := by decide +kernel
theorem subsd4_11 : ∀ q ∈ preLd4_11, subd4_11 q = true := by
  unfold preLd4_11
  exact sbd4_11_0
theorem en_okd4_11 : subEnum G n Ps d4_11 = true :=
  subEnum_fast ld_okd4_11 (enumS_of_coverL coverd4_11 subsd4_11)
theorem coverd4_12 : (coverL d4_12.aL d4_12.w 6 2 6 (fun _ => 0) (d4_12.S * d4_12.K) [] preLd4_12).isSome = true := by decide +kernel
theorem subsd4_12 : ∀ q ∈ preLd4_12, subd4_12 q = true := by
  unfold preLd4_12
  exact sbd4_12_0
theorem en_okd4_12 : subEnum G n Ps d4_12 = true :=
  subEnum_fast ld_okd4_12 (enumS_of_coverL coverd4_12 subsd4_12)
theorem coverd4_13 : (coverL d4_13.aL d4_13.w 6 2 6 (fun _ => 0) (d4_13.S * d4_13.K) [] preLd4_13).isSome = true := by decide +kernel
theorem subsd4_13 : ∀ q ∈ preLd4_13, subd4_13 q = true := by
  unfold preLd4_13
  exact sbd4_13_0
theorem en_okd4_13 : subEnum G n Ps d4_13 = true :=
  subEnum_fast ld_okd4_13 (enumS_of_coverL coverd4_13 subsd4_13)
theorem cov_ok4 : normsCovered normsL [d4_0, d4_1, d4_2, d4_3, d4_4, d4_5, d4_6, d4_7, d4_8, d4_9, d4_10, d4_11, d4_12, d4_13] = true := by decide +kernel
theorem cell_ok4 : CellOK hd G n Ps normsL cell4 :=
  cellOK_of hd adm (by decide +kernel) cov_ok4 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd4_0, en_okd4_0⟩
    · exact ⟨pre_okd4_1, en_okd4_1⟩
    · exact ⟨pre_okd4_2, en_okd4_2⟩
    · exact ⟨pre_okd4_3, en_okd4_3⟩
    · exact ⟨pre_okd4_4, en_okd4_4⟩
    · exact ⟨pre_okd4_5, en_okd4_5⟩
    · exact ⟨pre_okd4_6, en_okd4_6⟩
    · exact ⟨pre_okd4_7, en_okd4_7⟩
    · exact ⟨pre_okd4_8, en_okd4_8⟩
    · exact ⟨pre_okd4_9, en_okd4_9⟩
    · exact ⟨pre_okd4_10, en_okd4_10⟩
    · exact ⟨pre_okd4_11, en_okd4_11⟩
    · exact ⟨pre_okd4_12, en_okd4_12⟩
    · exact ⟨pre_okd4_13, en_okd4_13⟩
  )
theorem coverd5_0 : (coverL d5_0.aL d5_0.w 6 2 6 (fun _ => 0) (d5_0.S * d5_0.K) [] preLd5_0).isSome = true := by decide +kernel
theorem subsd5_0 : ∀ q ∈ preLd5_0, subd5_0 q = true := by
  unfold preLd5_0
  exact sbd5_0_0
theorem en_okd5_0 : subEnum G n Ps d5_0 = true :=
  subEnum_fast ld_okd5_0 (enumS_of_coverL coverd5_0 subsd5_0)
theorem coverd5_1 : (coverL d5_1.aL d5_1.w 6 2 6 (fun _ => 0) (d5_1.S * d5_1.K) [] preLd5_1).isSome = true := by decide +kernel
theorem subsd5_1 : ∀ q ∈ preLd5_1, subd5_1 q = true := by
  unfold preLd5_1
  exact sbd5_1_0
theorem en_okd5_1 : subEnum G n Ps d5_1 = true :=
  subEnum_fast ld_okd5_1 (enumS_of_coverL coverd5_1 subsd5_1)
theorem coverd5_2 : (coverL d5_2.aL d5_2.w 6 2 6 (fun _ => 0) (d5_2.S * d5_2.K) [] preLd5_2).isSome = true := by decide +kernel
theorem subsd5_2 : ∀ q ∈ preLd5_2, subd5_2 q = true := by
  unfold preLd5_2
  exact sbd5_2_0
theorem en_okd5_2 : subEnum G n Ps d5_2 = true :=
  subEnum_fast ld_okd5_2 (enumS_of_coverL coverd5_2 subsd5_2)
theorem coverd5_3 : (coverL d5_3.aL d5_3.w 6 2 6 (fun _ => 0) (d5_3.S * d5_3.K) [] preLd5_3).isSome = true := by decide +kernel
theorem subsd5_3 : ∀ q ∈ preLd5_3, subd5_3 q = true := by
  unfold preLd5_3
  exact sbd5_3_0
theorem en_okd5_3 : subEnum G n Ps d5_3 = true :=
  subEnum_fast ld_okd5_3 (enumS_of_coverL coverd5_3 subsd5_3)
theorem coverd5_4 : (coverL d5_4.aL d5_4.w 6 2 6 (fun _ => 0) (d5_4.S * d5_4.K) [] preLd5_4).isSome = true := by decide +kernel
theorem subsd5_4 : ∀ q ∈ preLd5_4, subd5_4 q = true := by
  unfold preLd5_4
  exact sbd5_4_0
theorem en_okd5_4 : subEnum G n Ps d5_4 = true :=
  subEnum_fast ld_okd5_4 (enumS_of_coverL coverd5_4 subsd5_4)
theorem coverd5_5 : (coverL d5_5.aL d5_5.w 6 2 6 (fun _ => 0) (d5_5.S * d5_5.K) [] preLd5_5).isSome = true := by decide +kernel
theorem subsd5_5 : ∀ q ∈ preLd5_5, subd5_5 q = true := by
  unfold preLd5_5
  exact sbd5_5_0
theorem en_okd5_5 : subEnum G n Ps d5_5 = true :=
  subEnum_fast ld_okd5_5 (enumS_of_coverL coverd5_5 subsd5_5)
theorem coverd5_6 : (coverL d5_6.aL d5_6.w 6 2 6 (fun _ => 0) (d5_6.S * d5_6.K) [] preLd5_6).isSome = true := by decide +kernel
theorem subsd5_6 : ∀ q ∈ preLd5_6, subd5_6 q = true := by
  unfold preLd5_6
  exact sbd5_6_0
theorem en_okd5_6 : subEnum G n Ps d5_6 = true :=
  subEnum_fast ld_okd5_6 (enumS_of_coverL coverd5_6 subsd5_6)
theorem coverd5_7 : (coverL d5_7.aL d5_7.w 6 2 6 (fun _ => 0) (d5_7.S * d5_7.K) [] preLd5_7).isSome = true := by decide +kernel
theorem subsd5_7 : ∀ q ∈ preLd5_7, subd5_7 q = true := by
  unfold preLd5_7
  exact sbd5_7_0
theorem en_okd5_7 : subEnum G n Ps d5_7 = true :=
  subEnum_fast ld_okd5_7 (enumS_of_coverL coverd5_7 subsd5_7)
theorem coverd5_8 : (coverL d5_8.aL d5_8.w 6 2 6 (fun _ => 0) (d5_8.S * d5_8.K) [] preLd5_8).isSome = true := by decide +kernel
theorem subsd5_8 : ∀ q ∈ preLd5_8, subd5_8 q = true := by
  unfold preLd5_8
  exact sbd5_8_0
theorem en_okd5_8 : subEnum G n Ps d5_8 = true :=
  subEnum_fast ld_okd5_8 (enumS_of_coverL coverd5_8 subsd5_8)
theorem coverd5_9 : (coverL d5_9.aL d5_9.w 6 2 6 (fun _ => 0) (d5_9.S * d5_9.K) [] preLd5_9).isSome = true := by decide +kernel
theorem subsd5_9 : ∀ q ∈ preLd5_9, subd5_9 q = true := by
  unfold preLd5_9
  exact sbd5_9_0
theorem en_okd5_9 : subEnum G n Ps d5_9 = true :=
  subEnum_fast ld_okd5_9 (enumS_of_coverL coverd5_9 subsd5_9)
theorem coverd5_10 : (coverL d5_10.aL d5_10.w 6 2 6 (fun _ => 0) (d5_10.S * d5_10.K) [] preLd5_10).isSome = true := by decide +kernel
theorem subsd5_10 : ∀ q ∈ preLd5_10, subd5_10 q = true := by
  unfold preLd5_10
  exact sbd5_10_0
theorem en_okd5_10 : subEnum G n Ps d5_10 = true :=
  subEnum_fast ld_okd5_10 (enumS_of_coverL coverd5_10 subsd5_10)
theorem coverd5_11 : (coverL d5_11.aL d5_11.w 6 2 6 (fun _ => 0) (d5_11.S * d5_11.K) [] preLd5_11).isSome = true := by decide +kernel
theorem subsd5_11 : ∀ q ∈ preLd5_11, subd5_11 q = true := by
  unfold preLd5_11
  exact sbd5_11_0
theorem en_okd5_11 : subEnum G n Ps d5_11 = true :=
  subEnum_fast ld_okd5_11 (enumS_of_coverL coverd5_11 subsd5_11)
theorem coverd5_12 : (coverL d5_12.aL d5_12.w 6 2 6 (fun _ => 0) (d5_12.S * d5_12.K) [] preLd5_12).isSome = true := by decide +kernel
theorem subsd5_12 : ∀ q ∈ preLd5_12, subd5_12 q = true := by
  unfold preLd5_12
  exact sbd5_12_0
theorem en_okd5_12 : subEnum G n Ps d5_12 = true :=
  subEnum_fast ld_okd5_12 (enumS_of_coverL coverd5_12 subsd5_12)
theorem coverd5_13 : (coverL d5_13.aL d5_13.w 6 2 6 (fun _ => 0) (d5_13.S * d5_13.K) [] preLd5_13).isSome = true := by decide +kernel
theorem subsd5_13 : ∀ q ∈ preLd5_13, subd5_13 q = true := by
  unfold preLd5_13
  exact sbd5_13_0
theorem en_okd5_13 : subEnum G n Ps d5_13 = true :=
  subEnum_fast ld_okd5_13 (enumS_of_coverL coverd5_13 subsd5_13)
theorem cov_ok5 : normsCovered normsL [d5_0, d5_1, d5_2, d5_3, d5_4, d5_5, d5_6, d5_7, d5_8, d5_9, d5_10, d5_11, d5_12, d5_13] = true := by decide +kernel
theorem cell_ok5 : CellOK hd G n Ps normsL cell5 :=
  cellOK_of hd adm (by decide +kernel) cov_ok5 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd5_0, en_okd5_0⟩
    · exact ⟨pre_okd5_1, en_okd5_1⟩
    · exact ⟨pre_okd5_2, en_okd5_2⟩
    · exact ⟨pre_okd5_3, en_okd5_3⟩
    · exact ⟨pre_okd5_4, en_okd5_4⟩
    · exact ⟨pre_okd5_5, en_okd5_5⟩
    · exact ⟨pre_okd5_6, en_okd5_6⟩
    · exact ⟨pre_okd5_7, en_okd5_7⟩
    · exact ⟨pre_okd5_8, en_okd5_8⟩
    · exact ⟨pre_okd5_9, en_okd5_9⟩
    · exact ⟨pre_okd5_10, en_okd5_10⟩
    · exact ⟨pre_okd5_11, en_okd5_11⟩
    · exact ⟨pre_okd5_12, en_okd5_12⟩
    · exact ⟨pre_okd5_13, en_okd5_13⟩
  )
theorem coverd6_0 : (coverL d6_0.aL d6_0.w 6 2 6 (fun _ => 0) (d6_0.S * d6_0.K) [] preLd6_0).isSome = true := by decide +kernel
theorem subsd6_0 : ∀ q ∈ preLd6_0, subd6_0 q = true := by
  unfold preLd6_0
  exact sbd6_0_0
theorem en_okd6_0 : subEnum G n Ps d6_0 = true :=
  subEnum_fast ld_okd6_0 (enumS_of_coverL coverd6_0 subsd6_0)
theorem coverd6_1 : (coverL d6_1.aL d6_1.w 6 2 6 (fun _ => 0) (d6_1.S * d6_1.K) [] preLd6_1).isSome = true := by decide +kernel
theorem subsd6_1 : ∀ q ∈ preLd6_1, subd6_1 q = true := by
  unfold preLd6_1
  exact sbd6_1_0
theorem en_okd6_1 : subEnum G n Ps d6_1 = true :=
  subEnum_fast ld_okd6_1 (enumS_of_coverL coverd6_1 subsd6_1)
theorem coverd6_2 : (coverL d6_2.aL d6_2.w 6 2 6 (fun _ => 0) (d6_2.S * d6_2.K) [] preLd6_2).isSome = true := by decide +kernel
theorem subsd6_2 : ∀ q ∈ preLd6_2, subd6_2 q = true := by
  unfold preLd6_2
  exact sbd6_2_0
theorem en_okd6_2 : subEnum G n Ps d6_2 = true :=
  subEnum_fast ld_okd6_2 (enumS_of_coverL coverd6_2 subsd6_2)
theorem coverd6_3 : (coverL d6_3.aL d6_3.w 6 2 6 (fun _ => 0) (d6_3.S * d6_3.K) [] preLd6_3).isSome = true := by decide +kernel
theorem subsd6_3 : ∀ q ∈ preLd6_3, subd6_3 q = true := by
  unfold preLd6_3
  exact sbd6_3_0
theorem en_okd6_3 : subEnum G n Ps d6_3 = true :=
  subEnum_fast ld_okd6_3 (enumS_of_coverL coverd6_3 subsd6_3)
theorem coverd6_4 : (coverL d6_4.aL d6_4.w 6 2 6 (fun _ => 0) (d6_4.S * d6_4.K) [] preLd6_4).isSome = true := by decide +kernel
theorem subsd6_4 : ∀ q ∈ preLd6_4, subd6_4 q = true := by
  unfold preLd6_4
  exact sbd6_4_0
theorem en_okd6_4 : subEnum G n Ps d6_4 = true :=
  subEnum_fast ld_okd6_4 (enumS_of_coverL coverd6_4 subsd6_4)
theorem coverd6_5 : (coverL d6_5.aL d6_5.w 6 2 6 (fun _ => 0) (d6_5.S * d6_5.K) [] preLd6_5).isSome = true := by decide +kernel
theorem subsd6_5 : ∀ q ∈ preLd6_5, subd6_5 q = true := by
  unfold preLd6_5
  exact sbd6_5_0
theorem en_okd6_5 : subEnum G n Ps d6_5 = true :=
  subEnum_fast ld_okd6_5 (enumS_of_coverL coverd6_5 subsd6_5)
theorem coverd6_6 : (coverL d6_6.aL d6_6.w 6 2 6 (fun _ => 0) (d6_6.S * d6_6.K) [] preLd6_6).isSome = true := by decide +kernel
theorem subsd6_6 : ∀ q ∈ preLd6_6, subd6_6 q = true := by
  unfold preLd6_6
  exact sbd6_6_0
theorem en_okd6_6 : subEnum G n Ps d6_6 = true :=
  subEnum_fast ld_okd6_6 (enumS_of_coverL coverd6_6 subsd6_6)
theorem coverd6_7 : (coverL d6_7.aL d6_7.w 6 2 6 (fun _ => 0) (d6_7.S * d6_7.K) [] preLd6_7).isSome = true := by decide +kernel
theorem subsd6_7 : ∀ q ∈ preLd6_7, subd6_7 q = true := by
  unfold preLd6_7
  exact sbd6_7_0
theorem en_okd6_7 : subEnum G n Ps d6_7 = true :=
  subEnum_fast ld_okd6_7 (enumS_of_coverL coverd6_7 subsd6_7)
theorem coverd6_8 : (coverL d6_8.aL d6_8.w 6 2 6 (fun _ => 0) (d6_8.S * d6_8.K) [] preLd6_8).isSome = true := by decide +kernel
theorem subsd6_8 : ∀ q ∈ preLd6_8, subd6_8 q = true := by
  unfold preLd6_8
  exact sbd6_8_0
theorem en_okd6_8 : subEnum G n Ps d6_8 = true :=
  subEnum_fast ld_okd6_8 (enumS_of_coverL coverd6_8 subsd6_8)
theorem coverd6_9 : (coverL d6_9.aL d6_9.w 6 2 6 (fun _ => 0) (d6_9.S * d6_9.K) [] preLd6_9).isSome = true := by decide +kernel
theorem subsd6_9 : ∀ q ∈ preLd6_9, subd6_9 q = true := by
  unfold preLd6_9
  exact sbd6_9_0
theorem en_okd6_9 : subEnum G n Ps d6_9 = true :=
  subEnum_fast ld_okd6_9 (enumS_of_coverL coverd6_9 subsd6_9)
theorem coverd6_10 : (coverL d6_10.aL d6_10.w 6 2 6 (fun _ => 0) (d6_10.S * d6_10.K) [] preLd6_10).isSome = true := by decide +kernel
theorem subsd6_10 : ∀ q ∈ preLd6_10, subd6_10 q = true := by
  unfold preLd6_10
  exact sbd6_10_0
theorem en_okd6_10 : subEnum G n Ps d6_10 = true :=
  subEnum_fast ld_okd6_10 (enumS_of_coverL coverd6_10 subsd6_10)
theorem coverd6_11 : (coverL d6_11.aL d6_11.w 6 2 6 (fun _ => 0) (d6_11.S * d6_11.K) [] preLd6_11).isSome = true := by decide +kernel
theorem subsd6_11 : ∀ q ∈ preLd6_11, subd6_11 q = true := by
  unfold preLd6_11
  exact sbd6_11_0
theorem en_okd6_11 : subEnum G n Ps d6_11 = true :=
  subEnum_fast ld_okd6_11 (enumS_of_coverL coverd6_11 subsd6_11)
theorem coverd6_12 : (coverL d6_12.aL d6_12.w 6 2 6 (fun _ => 0) (d6_12.S * d6_12.K) [] preLd6_12).isSome = true := by decide +kernel
theorem subsd6_12 : ∀ q ∈ preLd6_12, subd6_12 q = true := by
  unfold preLd6_12
  exact sbd6_12_0
theorem en_okd6_12 : subEnum G n Ps d6_12 = true :=
  subEnum_fast ld_okd6_12 (enumS_of_coverL coverd6_12 subsd6_12)
theorem coverd6_13 : (coverL d6_13.aL d6_13.w 6 2 6 (fun _ => 0) (d6_13.S * d6_13.K) [] preLd6_13).isSome = true := by decide +kernel
theorem subsd6_13 : ∀ q ∈ preLd6_13, subd6_13 q = true := by
  unfold preLd6_13
  exact sbd6_13_0
theorem en_okd6_13 : subEnum G n Ps d6_13 = true :=
  subEnum_fast ld_okd6_13 (enumS_of_coverL coverd6_13 subsd6_13)
theorem cov_ok6 : normsCovered normsL [d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_6, d6_7, d6_8, d6_9, d6_10, d6_11, d6_12, d6_13] = true := by decide +kernel
theorem cell_ok6 : CellOK hd G n Ps normsL cell6 :=
  cellOK_of hd adm (by decide +kernel) cov_ok6 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd6_0, en_okd6_0⟩
    · exact ⟨pre_okd6_1, en_okd6_1⟩
    · exact ⟨pre_okd6_2, en_okd6_2⟩
    · exact ⟨pre_okd6_3, en_okd6_3⟩
    · exact ⟨pre_okd6_4, en_okd6_4⟩
    · exact ⟨pre_okd6_5, en_okd6_5⟩
    · exact ⟨pre_okd6_6, en_okd6_6⟩
    · exact ⟨pre_okd6_7, en_okd6_7⟩
    · exact ⟨pre_okd6_8, en_okd6_8⟩
    · exact ⟨pre_okd6_9, en_okd6_9⟩
    · exact ⟨pre_okd6_10, en_okd6_10⟩
    · exact ⟨pre_okd6_11, en_okd6_11⟩
    · exact ⟨pre_okd6_12, en_okd6_12⟩
    · exact ⟨pre_okd6_13, en_okd6_13⟩
  )

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C088
