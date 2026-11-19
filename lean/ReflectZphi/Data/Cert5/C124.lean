import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C124.Base
import ReflectZphi.Data.Cert5.C124.Pchk
import ReflectZphi.Data.Cert5.C124.Pnorms
import ReflectZphi.Data.Cert5.C124.P000
import ReflectZphi.Data.Cert5.C124.P001
import ReflectZphi.Data.Cert5.C124.P002
import ReflectZphi.Data.Cert5.C124.P003
import ReflectZphi.Data.Cert5.C124.P004
import ReflectZphi.Data.Cert5.C124.P005
import ReflectZphi.Data.Cert5.C124.P006
import ReflectZphi.Data.Cert5.C124.P007
import ReflectZphi.Data.Cert5.C124.P008
import ReflectZphi.Data.Cert5.C124.P009
import ReflectZphi.Data.Cert5.C124.P010
import ReflectZphi.Data.Cert5.C124.P011
import ReflectZphi.Data.Cert5.C124.P012
import ReflectZphi.Data.Cert5.C124.P013
import ReflectZphi.Data.Cert5.C124.P014
import ReflectZphi.Data.Cert5.C124.P015
import ReflectZphi.Data.Cert5.C124.P016
import ReflectZphi.Data.Cert5.C124.P017
import ReflectZphi.Data.Cert5.C124.P018
import ReflectZphi.Data.Cert5.C124.P019
import ReflectZphi.Data.Cert5.C124.P020
import ReflectZphi.Data.Cert5.C124.P021
import ReflectZphi.Data.Cert5.C124.P022
import ReflectZphi.Data.Cert5.C124.P023
import ReflectZphi.Data.Cert5.C124.P024
import ReflectZphi.Data.Cert5.C124.P025
import ReflectZphi.Data.Cert5.C124.P026
import ReflectZphi.Data.Cert5.C124.P027
import ReflectZphi.Data.Cert5.C124.P028
import ReflectZphi.Data.Cert5.C124.P029
import ReflectZphi.Data.Cert5.C124.P030
import ReflectZphi.Data.Cert5.C124.P031
import ReflectZphi.Data.Cert5.C124.P032
import ReflectZphi.Data.Cert5.C124.P033
import ReflectZphi.Data.Cert5.C124.P034
import ReflectZphi.Data.Cert5.C124.P035
import ReflectZphi.Data.Cert5.C124.P036
import ReflectZphi.Data.Cert5.C124.P037
import ReflectZphi.Data.Cert5.C124.P038
import ReflectZphi.Data.Cert5.C124.P039
import ReflectZphi.Data.Cert5.C124.P040
import ReflectZphi.Data.Cert5.C124.P041
import ReflectZphi.Data.Cert5.C124.P042
import ReflectZphi.Data.Cert5.C124.P043
import ReflectZphi.Data.Cert5.C124.P044
import ReflectZphi.Data.Cert5.C124.P045
import ReflectZphi.Data.Cert5.C124.P046
import ReflectZphi.Data.Cert5.C124.P047
import ReflectZphi.Data.Cert5.C124.P048
import ReflectZphi.Data.Cert5.C124.P049
import ReflectZphi.Data.Cert5.C124.P050
import ReflectZphi.Data.Cert5.C124.P051
import ReflectZphi.Data.Cert5.C124.P052
import ReflectZphi.Data.Cert5.C124.P053
import ReflectZphi.Data.Cert5.C124.P054
import ReflectZphi.Data.Cert5.C124.P055
import ReflectZphi.Data.Cert5.C124.P056
import ReflectZphi.Data.Cert5.C124.P057
import ReflectZphi.Data.Cert5.C124.P058
import ReflectZphi.Data.Cert5.C124.P059
import ReflectZphi.Data.Cert5.C124.P060
import ReflectZphi.Data.Cert5.C124.P061
import ReflectZphi.Data.Cert5.C124.P062
import ReflectZphi.Data.Cert5.C124.P063
import ReflectZphi.Data.Cert5.C124.P064

namespace ReflectZphi.Data.Cert5.C124

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
theorem coverd0_14 : (coverL d0_14.aL d0_14.w 6 2 6 (fun _ => 0) (d0_14.S * d0_14.K) [] preLd0_14).isSome = true := by decide +kernel
theorem subsd0_14 : ∀ q ∈ preLd0_14, subd0_14 q = true := by
  unfold preLd0_14
  exact sbd0_14_0
theorem en_okd0_14 : subEnum G n Ps d0_14 = true :=
  subEnum_fast ld_okd0_14 (enumS_of_coverL coverd0_14 subsd0_14)
theorem cov_ok0 : normsCovered normsL [d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6, d0_7, d0_8, d0_9, d0_10, d0_11, d0_12, d0_13, d0_14] = true := by decide +kernel
theorem cell_ok0 : CellOK hd G n Ps normsL cell0 :=
  cellOK_of hd adm (by decide +kernel) cov_ok0 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd0_14, en_okd0_14⟩
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
theorem coverd1_14 : (coverL d1_14.aL d1_14.w 6 2 6 (fun _ => 0) (d1_14.S * d1_14.K) [] preLd1_14).isSome = true := by decide +kernel
theorem subsd1_14 : ∀ q ∈ preLd1_14, subd1_14 q = true := by
  unfold preLd1_14
  exact sbd1_14_0
theorem en_okd1_14 : subEnum G n Ps d1_14 = true :=
  subEnum_fast ld_okd1_14 (enumS_of_coverL coverd1_14 subsd1_14)
theorem cov_ok1 : normsCovered normsL [d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6, d1_7, d1_8, d1_9, d1_10, d1_11, d1_12, d1_13, d1_14] = true := by decide +kernel
theorem cell_ok1 : CellOK hd G n Ps normsL cell1 :=
  cellOK_of hd adm (by decide +kernel) cov_ok1 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd1_14, en_okd1_14⟩
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
theorem coverd2_14 : (coverL d2_14.aL d2_14.w 6 2 6 (fun _ => 0) (d2_14.S * d2_14.K) [] preLd2_14).isSome = true := by decide +kernel
theorem subsd2_14 : ∀ q ∈ preLd2_14, subd2_14 q = true := by
  unfold preLd2_14
  exact sbd2_14_0
theorem en_okd2_14 : subEnum G n Ps d2_14 = true :=
  subEnum_fast ld_okd2_14 (enumS_of_coverL coverd2_14 subsd2_14)
theorem cov_ok2 : normsCovered normsL [d2_0, d2_1, d2_2, d2_3, d2_4, d2_5, d2_6, d2_7, d2_8, d2_9, d2_10, d2_11, d2_12, d2_13, d2_14] = true := by decide +kernel
theorem cell_ok2 : CellOK hd G n Ps normsL cell2 :=
  cellOK_of hd adm (by decide +kernel) cov_ok2 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd2_14, en_okd2_14⟩
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
theorem coverd3_14 : (coverL d3_14.aL d3_14.w 6 2 6 (fun _ => 0) (d3_14.S * d3_14.K) [] preLd3_14).isSome = true := by decide +kernel
theorem subsd3_14 : ∀ q ∈ preLd3_14, subd3_14 q = true := by
  unfold preLd3_14
  exact sbd3_14_0
theorem en_okd3_14 : subEnum G n Ps d3_14 = true :=
  subEnum_fast ld_okd3_14 (enumS_of_coverL coverd3_14 subsd3_14)
theorem cov_ok3 : normsCovered normsL [d3_0, d3_1, d3_2, d3_3, d3_4, d3_5, d3_6, d3_7, d3_8, d3_9, d3_10, d3_11, d3_12, d3_13, d3_14] = true := by decide +kernel
theorem cell_ok3 : CellOK hd G n Ps normsL cell3 :=
  cellOK_of hd adm (by decide +kernel) cov_ok3 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd3_14, en_okd3_14⟩
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
theorem coverd4_14 : (coverL d4_14.aL d4_14.w 6 2 6 (fun _ => 0) (d4_14.S * d4_14.K) [] preLd4_14).isSome = true := by decide +kernel
theorem subsd4_14 : ∀ q ∈ preLd4_14, subd4_14 q = true := by
  unfold preLd4_14
  exact sbd4_14_0
theorem en_okd4_14 : subEnum G n Ps d4_14 = true :=
  subEnum_fast ld_okd4_14 (enumS_of_coverL coverd4_14 subsd4_14)
theorem cov_ok4 : normsCovered normsL [d4_0, d4_1, d4_2, d4_3, d4_4, d4_5, d4_6, d4_7, d4_8, d4_9, d4_10, d4_11, d4_12, d4_13, d4_14] = true := by decide +kernel
theorem cell_ok4 : CellOK hd G n Ps normsL cell4 :=
  cellOK_of hd adm (by decide +kernel) cov_ok4 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd4_14, en_okd4_14⟩
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
  exact List.forall_mem_append.2 ⟨sbd5_7_0, sbd5_7_1⟩
theorem en_okd5_7 : subEnum G n Ps d5_7 = true :=
  subEnum_fast ld_okd5_7 (enumS_of_coverL coverd5_7 subsd5_7)
theorem coverd5_8 : (coverL d5_8.aL d5_8.w 6 2 6 (fun _ => 0) (d5_8.S * d5_8.K) [] preLd5_8).isSome = true := by decide +kernel
theorem subsd5_8 : ∀ q ∈ preLd5_8, subd5_8 q = true := by
  unfold preLd5_8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_8_0, List.forall_mem_append.2 ⟨sbd5_8_1, sbd5_8_2⟩⟩, List.forall_mem_append.2 ⟨sbd5_8_3, List.forall_mem_append.2 ⟨sbd5_8_4, sbd5_8_5⟩⟩⟩
theorem en_okd5_8 : subEnum G n Ps d5_8 = true :=
  subEnum_fast ld_okd5_8 (enumS_of_coverL coverd5_8 subsd5_8)
theorem coverd5_9 : (coverL d5_9.aL d5_9.w 6 2 6 (fun _ => 0) (d5_9.S * d5_9.K) [] preLd5_9).isSome = true := by decide +kernel
theorem subsd5_9 : ∀ q ∈ preLd5_9, subd5_9 q = true := by
  unfold preLd5_9
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_9_0, List.forall_mem_append.2 ⟨sbd5_9_1, sbd5_9_2⟩⟩, List.forall_mem_append.2 ⟨sbd5_9_3, List.forall_mem_append.2 ⟨sbd5_9_4, sbd5_9_5⟩⟩⟩
theorem en_okd5_9 : subEnum G n Ps d5_9 = true :=
  subEnum_fast ld_okd5_9 (enumS_of_coverL coverd5_9 subsd5_9)
theorem coverd5_10 : (coverL d5_10.aL d5_10.w 6 2 6 (fun _ => 0) (d5_10.S * d5_10.K) [] preLd5_10).isSome = true := by decide +kernel
theorem subsd5_10 : ∀ q ∈ preLd5_10, subd5_10 q = true := by
  unfold preLd5_10
  exact List.forall_mem_append.2 ⟨sbd5_10_0, sbd5_10_1⟩
theorem en_okd5_10 : subEnum G n Ps d5_10 = true :=
  subEnum_fast ld_okd5_10 (enumS_of_coverL coverd5_10 subsd5_10)
theorem coverd5_11 : (coverL d5_11.aL d5_11.w 6 2 6 (fun _ => 0) (d5_11.S * d5_11.K) [] preLd5_11).isSome = true := by decide +kernel
theorem subsd5_11 : ∀ q ∈ preLd5_11, subd5_11 q = true := by
  unfold preLd5_11
  exact List.forall_mem_append.2 ⟨sbd5_11_0, sbd5_11_1⟩
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
theorem coverd5_14 : (coverL d5_14.aL d5_14.w 6 2 6 (fun _ => 0) (d5_14.S * d5_14.K) [] preLd5_14).isSome = true := by decide +kernel
theorem subsd5_14 : ∀ q ∈ preLd5_14, subd5_14 q = true := by
  unfold preLd5_14
  exact List.forall_mem_append.2 ⟨sbd5_14_0, List.forall_mem_append.2 ⟨sbd5_14_1, sbd5_14_2⟩⟩
theorem en_okd5_14 : subEnum G n Ps d5_14 = true :=
  subEnum_fast ld_okd5_14 (enumS_of_coverL coverd5_14 subsd5_14)
theorem cov_ok5 : normsCovered normsL [d5_0, d5_1, d5_2, d5_3, d5_4, d5_5, d5_6, d5_7, d5_8, d5_9, d5_10, d5_11, d5_12, d5_13, d5_14] = true := by decide +kernel
theorem cell_ok5 : CellOK hd G n Ps normsL cell5 :=
  cellOK_of hd adm (by decide +kernel) cov_ok5 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd5_14, en_okd5_14⟩
  )
theorem coverd6_0 : (coverL d6_0.aL d6_0.w 6 2 6 (fun _ => 0) (d6_0.S * d6_0.K) [] preLd6_0).isSome = true := by decide +kernel
theorem subsd6_0 : ∀ q ∈ preLd6_0, subd6_0 q = true := by
  unfold preLd6_0
  exact List.forall_mem_append.2 ⟨sbd6_0_0, sbd6_0_1⟩
theorem en_okd6_0 : subEnum G n Ps d6_0 = true :=
  subEnum_fast ld_okd6_0 (enumS_of_coverL coverd6_0 subsd6_0)
theorem coverd6_1 : (coverL d6_1.aL d6_1.w 6 2 6 (fun _ => 0) (d6_1.S * d6_1.K) [] preLd6_1).isSome = true := by decide +kernel
theorem subsd6_1 : ∀ q ∈ preLd6_1, subd6_1 q = true := by
  unfold preLd6_1
  exact List.forall_mem_append.2 ⟨sbd6_1_0, sbd6_1_1⟩
theorem en_okd6_1 : subEnum G n Ps d6_1 = true :=
  subEnum_fast ld_okd6_1 (enumS_of_coverL coverd6_1 subsd6_1)
theorem coverd6_2 : (coverL d6_2.aL d6_2.w 6 2 6 (fun _ => 0) (d6_2.S * d6_2.K) [] preLd6_2).isSome = true := by decide +kernel
theorem subsd6_2 : ∀ q ∈ preLd6_2, subd6_2 q = true := by
  unfold preLd6_2
  exact List.forall_mem_append.2 ⟨sbd6_2_0, sbd6_2_1⟩
theorem en_okd6_2 : subEnum G n Ps d6_2 = true :=
  subEnum_fast ld_okd6_2 (enumS_of_coverL coverd6_2 subsd6_2)
theorem coverd6_3 : (coverL d6_3.aL d6_3.w 6 2 6 (fun _ => 0) (d6_3.S * d6_3.K) [] preLd6_3).isSome = true := by decide +kernel
theorem subsd6_3 : ∀ q ∈ preLd6_3, subd6_3 q = true := by
  unfold preLd6_3
  exact List.forall_mem_append.2 ⟨sbd6_3_0, sbd6_3_1⟩
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
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_6_0, sbd6_6_1⟩, List.forall_mem_append.2 ⟨sbd6_6_2, sbd6_6_3⟩⟩
theorem en_okd6_6 : subEnum G n Ps d6_6 = true :=
  subEnum_fast ld_okd6_6 (enumS_of_coverL coverd6_6 subsd6_6)
theorem coverd6_7 : (coverL d6_7.aL d6_7.w 6 2 6 (fun _ => 0) (d6_7.S * d6_7.K) [] preLd6_7).isSome = true := by decide +kernel
theorem subsd6_7 : ∀ q ∈ preLd6_7, subd6_7 q = true := by
  unfold preLd6_7
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_7_0, sbd6_7_1⟩, List.forall_mem_append.2 ⟨sbd6_7_2, List.forall_mem_append.2 ⟨sbd6_7_3, sbd6_7_4⟩⟩⟩
theorem en_okd6_7 : subEnum G n Ps d6_7 = true :=
  subEnum_fast ld_okd6_7 (enumS_of_coverL coverd6_7 subsd6_7)
theorem coverd6_8 : (coverL d6_8.aL d6_8.w 6 2 6 (fun _ => 0) (d6_8.S * d6_8.K) [] preLd6_8).isSome = true := by decide +kernel
theorem subsd6_8 : ∀ q ∈ preLd6_8, subd6_8 q = true := by
  unfold preLd6_8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_8_0, List.forall_mem_append.2 ⟨sbd6_8_1, sbd6_8_2⟩⟩, List.forall_mem_append.2 ⟨sbd6_8_3, List.forall_mem_append.2 ⟨sbd6_8_4, sbd6_8_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_8_6, List.forall_mem_append.2 ⟨sbd6_8_7, sbd6_8_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_8_9, sbd6_8_10⟩, List.forall_mem_append.2 ⟨sbd6_8_11, sbd6_8_12⟩⟩⟩⟩
theorem en_okd6_8 : subEnum G n Ps d6_8 = true :=
  subEnum_fast ld_okd6_8 (enumS_of_coverL coverd6_8 subsd6_8)
theorem coverd6_9 : (coverL d6_9.aL d6_9.w 6 2 6 (fun _ => 0) (d6_9.S * d6_9.K) [] preLd6_9).isSome = true := by decide +kernel
theorem subsd6_9 : ∀ q ∈ preLd6_9, subd6_9 q = true := by
  unfold preLd6_9
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_9_0, List.forall_mem_append.2 ⟨sbd6_9_1, sbd6_9_2⟩⟩, List.forall_mem_append.2 ⟨sbd6_9_3, List.forall_mem_append.2 ⟨sbd6_9_4, sbd6_9_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_9_6, List.forall_mem_append.2 ⟨sbd6_9_7, sbd6_9_8⟩⟩, List.forall_mem_append.2 ⟨sbd6_9_9, List.forall_mem_append.2 ⟨sbd6_9_10, sbd6_9_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_9_12, List.forall_mem_append.2 ⟨sbd6_9_13, sbd6_9_14⟩⟩, List.forall_mem_append.2 ⟨sbd6_9_15, List.forall_mem_append.2 ⟨sbd6_9_16, sbd6_9_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_9_18, List.forall_mem_append.2 ⟨sbd6_9_19, sbd6_9_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_9_21, sbd6_9_22⟩, List.forall_mem_append.2 ⟨sbd6_9_23, sbd6_9_24⟩⟩⟩⟩⟩
theorem en_okd6_9 : subEnum G n Ps d6_9 = true :=
  subEnum_fast ld_okd6_9 (enumS_of_coverL coverd6_9 subsd6_9)
theorem coverd6_10 : (coverL d6_10.aL d6_10.w 6 2 6 (fun _ => 0) (d6_10.S * d6_10.K) [] preLd6_10).isSome = true := by decide +kernel
theorem subsd6_10 : ∀ q ∈ preLd6_10, subd6_10 q = true := by
  unfold preLd6_10
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_10_0, List.forall_mem_append.2 ⟨sbd6_10_1, sbd6_10_2⟩⟩, List.forall_mem_append.2 ⟨sbd6_10_3, List.forall_mem_append.2 ⟨sbd6_10_4, sbd6_10_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_10_6, List.forall_mem_append.2 ⟨sbd6_10_7, sbd6_10_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_10_9, sbd6_10_10⟩, List.forall_mem_append.2 ⟨sbd6_10_11, sbd6_10_12⟩⟩⟩⟩
theorem en_okd6_10 : subEnum G n Ps d6_10 = true :=
  subEnum_fast ld_okd6_10 (enumS_of_coverL coverd6_10 subsd6_10)
theorem coverd6_11 : (coverL d6_11.aL d6_11.w 6 2 6 (fun _ => 0) (d6_11.S * d6_11.K) [] preLd6_11).isSome = true := by decide +kernel
theorem subsd6_11 : ∀ q ∈ preLd6_11, subd6_11 q = true := by
  unfold preLd6_11
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_11_0, sbd6_11_1⟩, List.forall_mem_append.2 ⟨sbd6_11_2, List.forall_mem_append.2 ⟨sbd6_11_3, sbd6_11_4⟩⟩⟩
theorem en_okd6_11 : subEnum G n Ps d6_11 = true :=
  subEnum_fast ld_okd6_11 (enumS_of_coverL coverd6_11 subsd6_11)
theorem coverd6_12 : (coverL d6_12.aL d6_12.w 6 2 6 (fun _ => 0) (d6_12.S * d6_12.K) [] preLd6_12).isSome = true := by decide +kernel
theorem subsd6_12 : ∀ q ∈ preLd6_12, subd6_12 q = true := by
  unfold preLd6_12
  exact List.forall_mem_append.2 ⟨sbd6_12_0, List.forall_mem_append.2 ⟨sbd6_12_1, sbd6_12_2⟩⟩
theorem en_okd6_12 : subEnum G n Ps d6_12 = true :=
  subEnum_fast ld_okd6_12 (enumS_of_coverL coverd6_12 subsd6_12)
theorem coverd6_13 : (coverL d6_13.aL d6_13.w 6 2 6 (fun _ => 0) (d6_13.S * d6_13.K) [] preLd6_13).isSome = true := by decide +kernel
theorem subsd6_13 : ∀ q ∈ preLd6_13, subd6_13 q = true := by
  unfold preLd6_13
  exact List.forall_mem_append.2 ⟨sbd6_13_0, sbd6_13_1⟩
theorem en_okd6_13 : subEnum G n Ps d6_13 = true :=
  subEnum_fast ld_okd6_13 (enumS_of_coverL coverd6_13 subsd6_13)
theorem coverd6_14 : (coverL d6_14.aL d6_14.w 6 2 6 (fun _ => 0) (d6_14.S * d6_14.K) [] preLd6_14).isSome = true := by decide +kernel
theorem subsd6_14 : ∀ q ∈ preLd6_14, subd6_14 q = true := by
  unfold preLd6_14
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_0, sbd6_14_1⟩, List.forall_mem_append.2 ⟨sbd6_14_2, sbd6_14_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_4, sbd6_14_5⟩, List.forall_mem_append.2 ⟨sbd6_14_6, sbd6_14_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_8, sbd6_14_9⟩, List.forall_mem_append.2 ⟨sbd6_14_10, sbd6_14_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_12, sbd6_14_13⟩, List.forall_mem_append.2 ⟨sbd6_14_14, sbd6_14_15⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_16, sbd6_14_17⟩, List.forall_mem_append.2 ⟨sbd6_14_18, sbd6_14_19⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_20, sbd6_14_21⟩, List.forall_mem_append.2 ⟨sbd6_14_22, sbd6_14_23⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_24, sbd6_14_25⟩, List.forall_mem_append.2 ⟨sbd6_14_26, sbd6_14_27⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_14_28, sbd6_14_29⟩, List.forall_mem_append.2 ⟨sbd6_14_30, List.forall_mem_append.2 ⟨sbd6_14_31, sbd6_14_32⟩⟩⟩⟩⟩⟩
theorem en_okd6_14 : subEnum G n Ps d6_14 = true :=
  subEnum_fast ld_okd6_14 (enumS_of_coverL coverd6_14 subsd6_14)
theorem cov_ok6 : normsCovered normsL [d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_6, d6_7, d6_8, d6_9, d6_10, d6_11, d6_12, d6_13, d6_14] = true := by decide +kernel
theorem cell_ok6 : CellOK hd G n Ps normsL cell6 :=
  cellOK_of hd adm (by decide +kernel) cov_ok6 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨pre_okd6_14, en_okd6_14⟩
  )
theorem coverd7_0 : (coverL d7_0.aL d7_0.w 6 2 6 (fun _ => 0) (d7_0.S * d7_0.K) [] preLd7_0).isSome = true := by decide +kernel
theorem subsd7_0 : ∀ q ∈ preLd7_0, subd7_0 q = true := by
  unfold preLd7_0
  exact sbd7_0_0
theorem en_okd7_0 : subEnum G n Ps d7_0 = true :=
  subEnum_fast ld_okd7_0 (enumS_of_coverL coverd7_0 subsd7_0)
theorem coverd7_1 : (coverL d7_1.aL d7_1.w 6 2 6 (fun _ => 0) (d7_1.S * d7_1.K) [] preLd7_1).isSome = true := by decide +kernel
theorem subsd7_1 : ∀ q ∈ preLd7_1, subd7_1 q = true := by
  unfold preLd7_1
  exact List.forall_mem_append.2 ⟨sbd7_1_0, sbd7_1_1⟩
theorem en_okd7_1 : subEnum G n Ps d7_1 = true :=
  subEnum_fast ld_okd7_1 (enumS_of_coverL coverd7_1 subsd7_1)
theorem coverd7_2 : (coverL d7_2.aL d7_2.w 6 2 6 (fun _ => 0) (d7_2.S * d7_2.K) [] preLd7_2).isSome = true := by decide +kernel
theorem subsd7_2 : ∀ q ∈ preLd7_2, subd7_2 q = true := by
  unfold preLd7_2
  exact sbd7_2_0
theorem en_okd7_2 : subEnum G n Ps d7_2 = true :=
  subEnum_fast ld_okd7_2 (enumS_of_coverL coverd7_2 subsd7_2)
theorem coverd7_3 : (coverL d7_3.aL d7_3.w 6 2 6 (fun _ => 0) (d7_3.S * d7_3.K) [] preLd7_3).isSome = true := by decide +kernel
theorem subsd7_3 : ∀ q ∈ preLd7_3, subd7_3 q = true := by
  unfold preLd7_3
  exact sbd7_3_0
theorem en_okd7_3 : subEnum G n Ps d7_3 = true :=
  subEnum_fast ld_okd7_3 (enumS_of_coverL coverd7_3 subsd7_3)
theorem coverd7_4 : (coverL d7_4.aL d7_4.w 6 2 6 (fun _ => 0) (d7_4.S * d7_4.K) [] preLd7_4).isSome = true := by decide +kernel
theorem subsd7_4 : ∀ q ∈ preLd7_4, subd7_4 q = true := by
  unfold preLd7_4
  exact sbd7_4_0
theorem en_okd7_4 : subEnum G n Ps d7_4 = true :=
  subEnum_fast ld_okd7_4 (enumS_of_coverL coverd7_4 subsd7_4)
theorem coverd7_5 : (coverL d7_5.aL d7_5.w 6 2 6 (fun _ => 0) (d7_5.S * d7_5.K) [] preLd7_5).isSome = true := by decide +kernel
theorem subsd7_5 : ∀ q ∈ preLd7_5, subd7_5 q = true := by
  unfold preLd7_5
  exact sbd7_5_0
theorem en_okd7_5 : subEnum G n Ps d7_5 = true :=
  subEnum_fast ld_okd7_5 (enumS_of_coverL coverd7_5 subsd7_5)
theorem coverd7_6 : (coverL d7_6.aL d7_6.w 6 2 6 (fun _ => 0) (d7_6.S * d7_6.K) [] preLd7_6).isSome = true := by decide +kernel
theorem subsd7_6 : ∀ q ∈ preLd7_6, subd7_6 q = true := by
  unfold preLd7_6
  exact List.forall_mem_append.2 ⟨sbd7_6_0, List.forall_mem_append.2 ⟨sbd7_6_1, sbd7_6_2⟩⟩
theorem en_okd7_6 : subEnum G n Ps d7_6 = true :=
  subEnum_fast ld_okd7_6 (enumS_of_coverL coverd7_6 subsd7_6)
theorem coverd7_7 : (coverL d7_7.aL d7_7.w 6 2 6 (fun _ => 0) (d7_7.S * d7_7.K) [] preLd7_7).isSome = true := by decide +kernel
theorem subsd7_7 : ∀ q ∈ preLd7_7, subd7_7 q = true := by
  unfold preLd7_7
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_7_0, sbd7_7_1⟩, List.forall_mem_append.2 ⟨sbd7_7_2, sbd7_7_3⟩⟩
theorem en_okd7_7 : subEnum G n Ps d7_7 = true :=
  subEnum_fast ld_okd7_7 (enumS_of_coverL coverd7_7 subsd7_7)
theorem coverd7_8 : (coverL d7_8.aL d7_8.w 6 2 6 (fun _ => 0) (d7_8.S * d7_8.K) [] preLd7_8).isSome = true := by decide +kernel
theorem subsd7_8 : ∀ q ∈ preLd7_8, subd7_8 q = true := by
  unfold preLd7_8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_8_0, sbd7_8_1⟩, List.forall_mem_append.2 ⟨sbd7_8_2, sbd7_8_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_8_4, sbd7_8_5⟩, List.forall_mem_append.2 ⟨sbd7_8_6, sbd7_8_7⟩⟩⟩
theorem en_okd7_8 : subEnum G n Ps d7_8 = true :=
  subEnum_fast ld_okd7_8 (enumS_of_coverL coverd7_8 subsd7_8)
theorem coverd7_9 : (coverL d7_9.aL d7_9.w 6 2 6 (fun _ => 0) (d7_9.S * d7_9.K) [] preLd7_9).isSome = true := by decide +kernel
theorem subsd7_9 : ∀ q ∈ preLd7_9, subd7_9 q = true := by
  unfold preLd7_9
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_9_0, sbd7_9_1⟩, List.forall_mem_append.2 ⟨sbd7_9_2, List.forall_mem_append.2 ⟨sbd7_9_3, sbd7_9_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_9_5, List.forall_mem_append.2 ⟨sbd7_9_6, sbd7_9_7⟩⟩, List.forall_mem_append.2 ⟨sbd7_9_8, List.forall_mem_append.2 ⟨sbd7_9_9, sbd7_9_10⟩⟩⟩⟩
theorem en_okd7_9 : subEnum G n Ps d7_9 = true :=
  subEnum_fast ld_okd7_9 (enumS_of_coverL coverd7_9 subsd7_9)
theorem coverd7_10 : (coverL d7_10.aL d7_10.w 6 2 6 (fun _ => 0) (d7_10.S * d7_10.K) [] preLd7_10).isSome = true := by decide +kernel
theorem subsd7_10 : ∀ q ∈ preLd7_10, subd7_10 q = true := by
  unfold preLd7_10
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_10_0, sbd7_10_1⟩, List.forall_mem_append.2 ⟨sbd7_10_2, List.forall_mem_append.2 ⟨sbd7_10_3, sbd7_10_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_10_5, sbd7_10_6⟩, List.forall_mem_append.2 ⟨sbd7_10_7, List.forall_mem_append.2 ⟨sbd7_10_8, sbd7_10_9⟩⟩⟩⟩
theorem en_okd7_10 : subEnum G n Ps d7_10 = true :=
  subEnum_fast ld_okd7_10 (enumS_of_coverL coverd7_10 subsd7_10)
theorem coverd7_11 : (coverL d7_11.aL d7_11.w 6 2 6 (fun _ => 0) (d7_11.S * d7_11.K) [] preLd7_11).isSome = true := by decide +kernel
theorem subsd7_11 : ∀ q ∈ preLd7_11, subd7_11 q = true := by
  unfold preLd7_11
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_11_0, sbd7_11_1⟩, List.forall_mem_append.2 ⟨sbd7_11_2, sbd7_11_3⟩⟩
theorem en_okd7_11 : subEnum G n Ps d7_11 = true :=
  subEnum_fast ld_okd7_11 (enumS_of_coverL coverd7_11 subsd7_11)
theorem coverd7_12 : (coverL d7_12.aL d7_12.w 6 2 6 (fun _ => 0) (d7_12.S * d7_12.K) [] preLd7_12).isSome = true := by decide +kernel
theorem subsd7_12 : ∀ q ∈ preLd7_12, subd7_12 q = true := by
  unfold preLd7_12
  exact List.forall_mem_append.2 ⟨sbd7_12_0, sbd7_12_1⟩
theorem en_okd7_12 : subEnum G n Ps d7_12 = true :=
  subEnum_fast ld_okd7_12 (enumS_of_coverL coverd7_12 subsd7_12)
theorem coverd7_13 : (coverL d7_13.aL d7_13.w 6 2 6 (fun _ => 0) (d7_13.S * d7_13.K) [] preLd7_13).isSome = true := by decide +kernel
theorem subsd7_13 : ∀ q ∈ preLd7_13, subd7_13 q = true := by
  unfold preLd7_13
  exact List.forall_mem_append.2 ⟨sbd7_13_0, sbd7_13_1⟩
theorem en_okd7_13 : subEnum G n Ps d7_13 = true :=
  subEnum_fast ld_okd7_13 (enumS_of_coverL coverd7_13 subsd7_13)
theorem coverd7_14 : (coverL d7_14.aL d7_14.w 6 2 6 (fun _ => 0) (d7_14.S * d7_14.K) [] preLd7_14).isSome = true := by decide +kernel
theorem subsd7_14 : ∀ q ∈ preLd7_14, subd7_14 q = true := by
  unfold preLd7_14
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_14_0, List.forall_mem_append.2 ⟨sbd7_14_1, sbd7_14_2⟩⟩, List.forall_mem_append.2 ⟨sbd7_14_3, List.forall_mem_append.2 ⟨sbd7_14_4, sbd7_14_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_14_6, List.forall_mem_append.2 ⟨sbd7_14_7, sbd7_14_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_14_9, sbd7_14_10⟩, List.forall_mem_append.2 ⟨sbd7_14_11, sbd7_14_12⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_14_13, List.forall_mem_append.2 ⟨sbd7_14_14, sbd7_14_15⟩⟩, List.forall_mem_append.2 ⟨sbd7_14_16, List.forall_mem_append.2 ⟨sbd7_14_17, sbd7_14_18⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_14_19, List.forall_mem_append.2 ⟨sbd7_14_20, sbd7_14_21⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_14_22, sbd7_14_23⟩, List.forall_mem_append.2 ⟨sbd7_14_24, sbd7_14_25⟩⟩⟩⟩⟩
theorem en_okd7_14 : subEnum G n Ps d7_14 = true :=
  subEnum_fast ld_okd7_14 (enumS_of_coverL coverd7_14 subsd7_14)
theorem cov_ok7 : normsCovered normsL [d7_0, d7_1, d7_2, d7_3, d7_4, d7_5, d7_6, d7_7, d7_8, d7_9, d7_10, d7_11, d7_12, d7_13, d7_14] = true := by decide +kernel
theorem cell_ok7 : CellOK hd G n Ps normsL cell7 :=
  cellOK_of hd adm (by decide +kernel) cov_ok7 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd7_0, en_okd7_0⟩
    · exact ⟨pre_okd7_1, en_okd7_1⟩
    · exact ⟨pre_okd7_2, en_okd7_2⟩
    · exact ⟨pre_okd7_3, en_okd7_3⟩
    · exact ⟨pre_okd7_4, en_okd7_4⟩
    · exact ⟨pre_okd7_5, en_okd7_5⟩
    · exact ⟨pre_okd7_6, en_okd7_6⟩
    · exact ⟨pre_okd7_7, en_okd7_7⟩
    · exact ⟨pre_okd7_8, en_okd7_8⟩
    · exact ⟨pre_okd7_9, en_okd7_9⟩
    · exact ⟨pre_okd7_10, en_okd7_10⟩
    · exact ⟨pre_okd7_11, en_okd7_11⟩
    · exact ⟨pre_okd7_12, en_okd7_12⟩
    · exact ⟨pre_okd7_13, en_okd7_13⟩
    · exact ⟨pre_okd7_14, en_okd7_14⟩
  )
theorem coverd8_0 : (coverL d8_0.aL d8_0.w 6 2 6 (fun _ => 0) (d8_0.S * d8_0.K) [] preLd8_0).isSome = true := by decide +kernel
theorem subsd8_0 : ∀ q ∈ preLd8_0, subd8_0 q = true := by
  unfold preLd8_0
  exact sbd8_0_0
theorem en_okd8_0 : subEnum G n Ps d8_0 = true :=
  subEnum_fast ld_okd8_0 (enumS_of_coverL coverd8_0 subsd8_0)
theorem coverd8_1 : (coverL d8_1.aL d8_1.w 6 2 6 (fun _ => 0) (d8_1.S * d8_1.K) [] preLd8_1).isSome = true := by decide +kernel
theorem subsd8_1 : ∀ q ∈ preLd8_1, subd8_1 q = true := by
  unfold preLd8_1
  exact sbd8_1_0
theorem en_okd8_1 : subEnum G n Ps d8_1 = true :=
  subEnum_fast ld_okd8_1 (enumS_of_coverL coverd8_1 subsd8_1)
theorem coverd8_2 : (coverL d8_2.aL d8_2.w 6 2 6 (fun _ => 0) (d8_2.S * d8_2.K) [] preLd8_2).isSome = true := by decide +kernel
theorem subsd8_2 : ∀ q ∈ preLd8_2, subd8_2 q = true := by
  unfold preLd8_2
  exact sbd8_2_0
theorem en_okd8_2 : subEnum G n Ps d8_2 = true :=
  subEnum_fast ld_okd8_2 (enumS_of_coverL coverd8_2 subsd8_2)
theorem coverd8_3 : (coverL d8_3.aL d8_3.w 6 2 6 (fun _ => 0) (d8_3.S * d8_3.K) [] preLd8_3).isSome = true := by decide +kernel
theorem subsd8_3 : ∀ q ∈ preLd8_3, subd8_3 q = true := by
  unfold preLd8_3
  exact sbd8_3_0
theorem en_okd8_3 : subEnum G n Ps d8_3 = true :=
  subEnum_fast ld_okd8_3 (enumS_of_coverL coverd8_3 subsd8_3)
theorem coverd8_4 : (coverL d8_4.aL d8_4.w 6 2 6 (fun _ => 0) (d8_4.S * d8_4.K) [] preLd8_4).isSome = true := by decide +kernel
theorem subsd8_4 : ∀ q ∈ preLd8_4, subd8_4 q = true := by
  unfold preLd8_4
  exact sbd8_4_0
theorem en_okd8_4 : subEnum G n Ps d8_4 = true :=
  subEnum_fast ld_okd8_4 (enumS_of_coverL coverd8_4 subsd8_4)
theorem coverd8_5 : (coverL d8_5.aL d8_5.w 6 2 6 (fun _ => 0) (d8_5.S * d8_5.K) [] preLd8_5).isSome = true := by decide +kernel
theorem subsd8_5 : ∀ q ∈ preLd8_5, subd8_5 q = true := by
  unfold preLd8_5
  exact sbd8_5_0
theorem en_okd8_5 : subEnum G n Ps d8_5 = true :=
  subEnum_fast ld_okd8_5 (enumS_of_coverL coverd8_5 subsd8_5)
theorem coverd8_6 : (coverL d8_6.aL d8_6.w 6 2 6 (fun _ => 0) (d8_6.S * d8_6.K) [] preLd8_6).isSome = true := by decide +kernel
theorem subsd8_6 : ∀ q ∈ preLd8_6, subd8_6 q = true := by
  unfold preLd8_6
  exact List.forall_mem_append.2 ⟨sbd8_6_0, List.forall_mem_append.2 ⟨sbd8_6_1, sbd8_6_2⟩⟩
theorem en_okd8_6 : subEnum G n Ps d8_6 = true :=
  subEnum_fast ld_okd8_6 (enumS_of_coverL coverd8_6 subsd8_6)
theorem coverd8_7 : (coverL d8_7.aL d8_7.w 6 2 6 (fun _ => 0) (d8_7.S * d8_7.K) [] preLd8_7).isSome = true := by decide +kernel
theorem subsd8_7 : ∀ q ∈ preLd8_7, subd8_7 q = true := by
  unfold preLd8_7
  exact List.forall_mem_append.2 ⟨sbd8_7_0, List.forall_mem_append.2 ⟨sbd8_7_1, sbd8_7_2⟩⟩
theorem en_okd8_7 : subEnum G n Ps d8_7 = true :=
  subEnum_fast ld_okd8_7 (enumS_of_coverL coverd8_7 subsd8_7)
theorem coverd8_8 : (coverL d8_8.aL d8_8.w 6 2 6 (fun _ => 0) (d8_8.S * d8_8.K) [] preLd8_8).isSome = true := by decide +kernel
theorem subsd8_8 : ∀ q ∈ preLd8_8, subd8_8 q = true := by
  unfold preLd8_8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_8_0, sbd8_8_1⟩, List.forall_mem_append.2 ⟨sbd8_8_2, sbd8_8_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_8_4, sbd8_8_5⟩, List.forall_mem_append.2 ⟨sbd8_8_6, List.forall_mem_append.2 ⟨sbd8_8_7, sbd8_8_8⟩⟩⟩⟩
theorem en_okd8_8 : subEnum G n Ps d8_8 = true :=
  subEnum_fast ld_okd8_8 (enumS_of_coverL coverd8_8 subsd8_8)
theorem coverd8_9 : (coverL d8_9.aL d8_9.w 6 2 6 (fun _ => 0) (d8_9.S * d8_9.K) [] preLd8_9).isSome = true := by decide +kernel
theorem subsd8_9 : ∀ q ∈ preLd8_9, subd8_9 q = true := by
  unfold preLd8_9
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_9_0, sbd8_9_1⟩, List.forall_mem_append.2 ⟨sbd8_9_2, sbd8_9_3⟩⟩
theorem en_okd8_9 : subEnum G n Ps d8_9 = true :=
  subEnum_fast ld_okd8_9 (enumS_of_coverL coverd8_9 subsd8_9)
theorem coverd8_10 : (coverL d8_10.aL d8_10.w 6 2 6 (fun _ => 0) (d8_10.S * d8_10.K) [] preLd8_10).isSome = true := by decide +kernel
theorem subsd8_10 : ∀ q ∈ preLd8_10, subd8_10 q = true := by
  unfold preLd8_10
  exact List.forall_mem_append.2 ⟨sbd8_10_0, sbd8_10_1⟩
theorem en_okd8_10 : subEnum G n Ps d8_10 = true :=
  subEnum_fast ld_okd8_10 (enumS_of_coverL coverd8_10 subsd8_10)
theorem coverd8_11 : (coverL d8_11.aL d8_11.w 6 2 6 (fun _ => 0) (d8_11.S * d8_11.K) [] preLd8_11).isSome = true := by decide +kernel
theorem subsd8_11 : ∀ q ∈ preLd8_11, subd8_11 q = true := by
  unfold preLd8_11
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_11_0, sbd8_11_1⟩, List.forall_mem_append.2 ⟨sbd8_11_2, sbd8_11_3⟩⟩
theorem en_okd8_11 : subEnum G n Ps d8_11 = true :=
  subEnum_fast ld_okd8_11 (enumS_of_coverL coverd8_11 subsd8_11)
theorem coverd8_12 : (coverL d8_12.aL d8_12.w 6 2 6 (fun _ => 0) (d8_12.S * d8_12.K) [] preLd8_12).isSome = true := by decide +kernel
theorem subsd8_12 : ∀ q ∈ preLd8_12, subd8_12 q = true := by
  unfold preLd8_12
  exact sbd8_12_0
theorem en_okd8_12 : subEnum G n Ps d8_12 = true :=
  subEnum_fast ld_okd8_12 (enumS_of_coverL coverd8_12 subsd8_12)
theorem coverd8_13 : (coverL d8_13.aL d8_13.w 6 2 6 (fun _ => 0) (d8_13.S * d8_13.K) [] preLd8_13).isSome = true := by decide +kernel
theorem subsd8_13 : ∀ q ∈ preLd8_13, subd8_13 q = true := by
  unfold preLd8_13
  exact List.forall_mem_append.2 ⟨sbd8_13_0, sbd8_13_1⟩
theorem en_okd8_13 : subEnum G n Ps d8_13 = true :=
  subEnum_fast ld_okd8_13 (enumS_of_coverL coverd8_13 subsd8_13)
theorem coverd8_14 : (coverL d8_14.aL d8_14.w 6 2 6 (fun _ => 0) (d8_14.S * d8_14.K) [] preLd8_14).isSome = true := by decide +kernel
theorem subsd8_14 : ∀ q ∈ preLd8_14, subd8_14 q = true := by
  unfold preLd8_14
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_14_0, List.forall_mem_append.2 ⟨sbd8_14_1, sbd8_14_2⟩⟩, List.forall_mem_append.2 ⟨sbd8_14_3, List.forall_mem_append.2 ⟨sbd8_14_4, sbd8_14_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_14_6, List.forall_mem_append.2 ⟨sbd8_14_7, sbd8_14_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_14_9, sbd8_14_10⟩, List.forall_mem_append.2 ⟨sbd8_14_11, sbd8_14_12⟩⟩⟩⟩
theorem en_okd8_14 : subEnum G n Ps d8_14 = true :=
  subEnum_fast ld_okd8_14 (enumS_of_coverL coverd8_14 subsd8_14)
theorem cov_ok8 : normsCovered normsL [d8_0, d8_1, d8_2, d8_3, d8_4, d8_5, d8_6, d8_7, d8_8, d8_9, d8_10, d8_11, d8_12, d8_13, d8_14] = true := by decide +kernel
theorem cell_ok8 : CellOK hd G n Ps normsL cell8 :=
  cellOK_of hd adm (by decide +kernel) cov_ok8 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd8_0, en_okd8_0⟩
    · exact ⟨pre_okd8_1, en_okd8_1⟩
    · exact ⟨pre_okd8_2, en_okd8_2⟩
    · exact ⟨pre_okd8_3, en_okd8_3⟩
    · exact ⟨pre_okd8_4, en_okd8_4⟩
    · exact ⟨pre_okd8_5, en_okd8_5⟩
    · exact ⟨pre_okd8_6, en_okd8_6⟩
    · exact ⟨pre_okd8_7, en_okd8_7⟩
    · exact ⟨pre_okd8_8, en_okd8_8⟩
    · exact ⟨pre_okd8_9, en_okd8_9⟩
    · exact ⟨pre_okd8_10, en_okd8_10⟩
    · exact ⟨pre_okd8_11, en_okd8_11⟩
    · exact ⟨pre_okd8_12, en_okd8_12⟩
    · exact ⟨pre_okd8_13, en_okd8_13⟩
    · exact ⟨pre_okd8_14, en_okd8_14⟩
  )
theorem coverd9_0 : (coverL d9_0.aL d9_0.w 6 2 6 (fun _ => 0) (d9_0.S * d9_0.K) [] preLd9_0).isSome = true := by decide +kernel
theorem subsd9_0 : ∀ q ∈ preLd9_0, subd9_0 q = true := by
  unfold preLd9_0
  exact sbd9_0_0
theorem en_okd9_0 : subEnum G n Ps d9_0 = true :=
  subEnum_fast ld_okd9_0 (enumS_of_coverL coverd9_0 subsd9_0)
theorem coverd9_1 : (coverL d9_1.aL d9_1.w 6 2 6 (fun _ => 0) (d9_1.S * d9_1.K) [] preLd9_1).isSome = true := by decide +kernel
theorem subsd9_1 : ∀ q ∈ preLd9_1, subd9_1 q = true := by
  unfold preLd9_1
  exact sbd9_1_0
theorem en_okd9_1 : subEnum G n Ps d9_1 = true :=
  subEnum_fast ld_okd9_1 (enumS_of_coverL coverd9_1 subsd9_1)
theorem coverd9_2 : (coverL d9_2.aL d9_2.w 6 2 6 (fun _ => 0) (d9_2.S * d9_2.K) [] preLd9_2).isSome = true := by decide +kernel
theorem subsd9_2 : ∀ q ∈ preLd9_2, subd9_2 q = true := by
  unfold preLd9_2
  exact sbd9_2_0
theorem en_okd9_2 : subEnum G n Ps d9_2 = true :=
  subEnum_fast ld_okd9_2 (enumS_of_coverL coverd9_2 subsd9_2)
theorem coverd9_3 : (coverL d9_3.aL d9_3.w 6 2 6 (fun _ => 0) (d9_3.S * d9_3.K) [] preLd9_3).isSome = true := by decide +kernel
theorem subsd9_3 : ∀ q ∈ preLd9_3, subd9_3 q = true := by
  unfold preLd9_3
  exact sbd9_3_0
theorem en_okd9_3 : subEnum G n Ps d9_3 = true :=
  subEnum_fast ld_okd9_3 (enumS_of_coverL coverd9_3 subsd9_3)
theorem coverd9_4 : (coverL d9_4.aL d9_4.w 6 2 6 (fun _ => 0) (d9_4.S * d9_4.K) [] preLd9_4).isSome = true := by decide +kernel
theorem subsd9_4 : ∀ q ∈ preLd9_4, subd9_4 q = true := by
  unfold preLd9_4
  exact sbd9_4_0
theorem en_okd9_4 : subEnum G n Ps d9_4 = true :=
  subEnum_fast ld_okd9_4 (enumS_of_coverL coverd9_4 subsd9_4)
theorem coverd9_5 : (coverL d9_5.aL d9_5.w 6 2 6 (fun _ => 0) (d9_5.S * d9_5.K) [] preLd9_5).isSome = true := by decide +kernel
theorem subsd9_5 : ∀ q ∈ preLd9_5, subd9_5 q = true := by
  unfold preLd9_5
  exact sbd9_5_0
theorem en_okd9_5 : subEnum G n Ps d9_5 = true :=
  subEnum_fast ld_okd9_5 (enumS_of_coverL coverd9_5 subsd9_5)
theorem coverd9_6 : (coverL d9_6.aL d9_6.w 6 2 6 (fun _ => 0) (d9_6.S * d9_6.K) [] preLd9_6).isSome = true := by decide +kernel
theorem subsd9_6 : ∀ q ∈ preLd9_6, subd9_6 q = true := by
  unfold preLd9_6
  exact List.forall_mem_append.2 ⟨sbd9_6_0, sbd9_6_1⟩
theorem en_okd9_6 : subEnum G n Ps d9_6 = true :=
  subEnum_fast ld_okd9_6 (enumS_of_coverL coverd9_6 subsd9_6)
theorem coverd9_7 : (coverL d9_7.aL d9_7.w 6 2 6 (fun _ => 0) (d9_7.S * d9_7.K) [] preLd9_7).isSome = true := by decide +kernel
theorem subsd9_7 : ∀ q ∈ preLd9_7, subd9_7 q = true := by
  unfold preLd9_7
  exact List.forall_mem_append.2 ⟨sbd9_7_0, sbd9_7_1⟩
theorem en_okd9_7 : subEnum G n Ps d9_7 = true :=
  subEnum_fast ld_okd9_7 (enumS_of_coverL coverd9_7 subsd9_7)
theorem coverd9_8 : (coverL d9_8.aL d9_8.w 6 2 6 (fun _ => 0) (d9_8.S * d9_8.K) [] preLd9_8).isSome = true := by decide +kernel
theorem subsd9_8 : ∀ q ∈ preLd9_8, subd9_8 q = true := by
  unfold preLd9_8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_8_0, List.forall_mem_append.2 ⟨sbd9_8_1, sbd9_8_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_8_3, sbd9_8_4⟩, List.forall_mem_append.2 ⟨sbd9_8_5, sbd9_8_6⟩⟩⟩
theorem en_okd9_8 : subEnum G n Ps d9_8 = true :=
  subEnum_fast ld_okd9_8 (enumS_of_coverL coverd9_8 subsd9_8)
theorem coverd9_9 : (coverL d9_9.aL d9_9.w 6 2 6 (fun _ => 0) (d9_9.S * d9_9.K) [] preLd9_9).isSome = true := by decide +kernel
theorem subsd9_9 : ∀ q ∈ preLd9_9, subd9_9 q = true := by
  unfold preLd9_9
  exact List.forall_mem_append.2 ⟨sbd9_9_0, List.forall_mem_append.2 ⟨sbd9_9_1, sbd9_9_2⟩⟩
theorem en_okd9_9 : subEnum G n Ps d9_9 = true :=
  subEnum_fast ld_okd9_9 (enumS_of_coverL coverd9_9 subsd9_9)
theorem coverd9_10 : (coverL d9_10.aL d9_10.w 6 2 6 (fun _ => 0) (d9_10.S * d9_10.K) [] preLd9_10).isSome = true := by decide +kernel
theorem subsd9_10 : ∀ q ∈ preLd9_10, subd9_10 q = true := by
  unfold preLd9_10
  exact List.forall_mem_append.2 ⟨sbd9_10_0, sbd9_10_1⟩
theorem en_okd9_10 : subEnum G n Ps d9_10 = true :=
  subEnum_fast ld_okd9_10 (enumS_of_coverL coverd9_10 subsd9_10)
theorem coverd9_11 : (coverL d9_11.aL d9_11.w 6 2 6 (fun _ => 0) (d9_11.S * d9_11.K) [] preLd9_11).isSome = true := by decide +kernel
theorem subsd9_11 : ∀ q ∈ preLd9_11, subd9_11 q = true := by
  unfold preLd9_11
  exact List.forall_mem_append.2 ⟨sbd9_11_0, sbd9_11_1⟩
theorem en_okd9_11 : subEnum G n Ps d9_11 = true :=
  subEnum_fast ld_okd9_11 (enumS_of_coverL coverd9_11 subsd9_11)
theorem coverd9_12 : (coverL d9_12.aL d9_12.w 6 2 6 (fun _ => 0) (d9_12.S * d9_12.K) [] preLd9_12).isSome = true := by decide +kernel
theorem subsd9_12 : ∀ q ∈ preLd9_12, subd9_12 q = true := by
  unfold preLd9_12
  exact sbd9_12_0
theorem en_okd9_12 : subEnum G n Ps d9_12 = true :=
  subEnum_fast ld_okd9_12 (enumS_of_coverL coverd9_12 subsd9_12)
theorem coverd9_13 : (coverL d9_13.aL d9_13.w 6 2 6 (fun _ => 0) (d9_13.S * d9_13.K) [] preLd9_13).isSome = true := by decide +kernel
theorem subsd9_13 : ∀ q ∈ preLd9_13, subd9_13 q = true := by
  unfold preLd9_13
  exact sbd9_13_0
theorem en_okd9_13 : subEnum G n Ps d9_13 = true :=
  subEnum_fast ld_okd9_13 (enumS_of_coverL coverd9_13 subsd9_13)
theorem coverd9_14 : (coverL d9_14.aL d9_14.w 6 2 6 (fun _ => 0) (d9_14.S * d9_14.K) [] preLd9_14).isSome = true := by decide +kernel
theorem subsd9_14 : ∀ q ∈ preLd9_14, subd9_14 q = true := by
  unfold preLd9_14
  exact List.forall_mem_append.2 ⟨sbd9_14_0, List.forall_mem_append.2 ⟨sbd9_14_1, sbd9_14_2⟩⟩
theorem en_okd9_14 : subEnum G n Ps d9_14 = true :=
  subEnum_fast ld_okd9_14 (enumS_of_coverL coverd9_14 subsd9_14)
theorem cov_ok9 : normsCovered normsL [d9_0, d9_1, d9_2, d9_3, d9_4, d9_5, d9_6, d9_7, d9_8, d9_9, d9_10, d9_11, d9_12, d9_13, d9_14] = true := by decide +kernel
theorem cell_ok9 : CellOK hd G n Ps normsL cell9 :=
  cellOK_of hd adm (by decide +kernel) cov_ok9 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd9_0, en_okd9_0⟩
    · exact ⟨pre_okd9_1, en_okd9_1⟩
    · exact ⟨pre_okd9_2, en_okd9_2⟩
    · exact ⟨pre_okd9_3, en_okd9_3⟩
    · exact ⟨pre_okd9_4, en_okd9_4⟩
    · exact ⟨pre_okd9_5, en_okd9_5⟩
    · exact ⟨pre_okd9_6, en_okd9_6⟩
    · exact ⟨pre_okd9_7, en_okd9_7⟩
    · exact ⟨pre_okd9_8, en_okd9_8⟩
    · exact ⟨pre_okd9_9, en_okd9_9⟩
    · exact ⟨pre_okd9_10, en_okd9_10⟩
    · exact ⟨pre_okd9_11, en_okd9_11⟩
    · exact ⟨pre_okd9_12, en_okd9_12⟩
    · exact ⟨pre_okd9_13, en_okd9_13⟩
    · exact ⟨pre_okd9_14, en_okd9_14⟩
  )
theorem coverd10_0 : (coverL d10_0.aL d10_0.w 6 2 6 (fun _ => 0) (d10_0.S * d10_0.K) [] preLd10_0).isSome = true := by decide +kernel
theorem subsd10_0 : ∀ q ∈ preLd10_0, subd10_0 q = true := by
  unfold preLd10_0
  exact sbd10_0_0
theorem en_okd10_0 : subEnum G n Ps d10_0 = true :=
  subEnum_fast ld_okd10_0 (enumS_of_coverL coverd10_0 subsd10_0)
theorem coverd10_1 : (coverL d10_1.aL d10_1.w 6 2 6 (fun _ => 0) (d10_1.S * d10_1.K) [] preLd10_1).isSome = true := by decide +kernel
theorem subsd10_1 : ∀ q ∈ preLd10_1, subd10_1 q = true := by
  unfold preLd10_1
  exact sbd10_1_0
theorem en_okd10_1 : subEnum G n Ps d10_1 = true :=
  subEnum_fast ld_okd10_1 (enumS_of_coverL coverd10_1 subsd10_1)
theorem coverd10_2 : (coverL d10_2.aL d10_2.w 6 2 6 (fun _ => 0) (d10_2.S * d10_2.K) [] preLd10_2).isSome = true := by decide +kernel
theorem subsd10_2 : ∀ q ∈ preLd10_2, subd10_2 q = true := by
  unfold preLd10_2
  exact sbd10_2_0
theorem en_okd10_2 : subEnum G n Ps d10_2 = true :=
  subEnum_fast ld_okd10_2 (enumS_of_coverL coverd10_2 subsd10_2)
theorem coverd10_3 : (coverL d10_3.aL d10_3.w 6 2 6 (fun _ => 0) (d10_3.S * d10_3.K) [] preLd10_3).isSome = true := by decide +kernel
theorem subsd10_3 : ∀ q ∈ preLd10_3, subd10_3 q = true := by
  unfold preLd10_3
  exact sbd10_3_0
theorem en_okd10_3 : subEnum G n Ps d10_3 = true :=
  subEnum_fast ld_okd10_3 (enumS_of_coverL coverd10_3 subsd10_3)
theorem coverd10_4 : (coverL d10_4.aL d10_4.w 6 2 6 (fun _ => 0) (d10_4.S * d10_4.K) [] preLd10_4).isSome = true := by decide +kernel
theorem subsd10_4 : ∀ q ∈ preLd10_4, subd10_4 q = true := by
  unfold preLd10_4
  exact sbd10_4_0
theorem en_okd10_4 : subEnum G n Ps d10_4 = true :=
  subEnum_fast ld_okd10_4 (enumS_of_coverL coverd10_4 subsd10_4)
theorem coverd10_5 : (coverL d10_5.aL d10_5.w 6 2 6 (fun _ => 0) (d10_5.S * d10_5.K) [] preLd10_5).isSome = true := by decide +kernel
theorem subsd10_5 : ∀ q ∈ preLd10_5, subd10_5 q = true := by
  unfold preLd10_5
  exact sbd10_5_0
theorem en_okd10_5 : subEnum G n Ps d10_5 = true :=
  subEnum_fast ld_okd10_5 (enumS_of_coverL coverd10_5 subsd10_5)
theorem coverd10_6 : (coverL d10_6.aL d10_6.w 6 2 6 (fun _ => 0) (d10_6.S * d10_6.K) [] preLd10_6).isSome = true := by decide +kernel
theorem subsd10_6 : ∀ q ∈ preLd10_6, subd10_6 q = true := by
  unfold preLd10_6
  exact sbd10_6_0
theorem en_okd10_6 : subEnum G n Ps d10_6 = true :=
  subEnum_fast ld_okd10_6 (enumS_of_coverL coverd10_6 subsd10_6)
theorem coverd10_7 : (coverL d10_7.aL d10_7.w 6 2 6 (fun _ => 0) (d10_7.S * d10_7.K) [] preLd10_7).isSome = true := by decide +kernel
theorem subsd10_7 : ∀ q ∈ preLd10_7, subd10_7 q = true := by
  unfold preLd10_7
  exact sbd10_7_0
theorem en_okd10_7 : subEnum G n Ps d10_7 = true :=
  subEnum_fast ld_okd10_7 (enumS_of_coverL coverd10_7 subsd10_7)
theorem coverd10_8 : (coverL d10_8.aL d10_8.w 6 2 6 (fun _ => 0) (d10_8.S * d10_8.K) [] preLd10_8).isSome = true := by decide +kernel
theorem subsd10_8 : ∀ q ∈ preLd10_8, subd10_8 q = true := by
  unfold preLd10_8
  exact List.forall_mem_append.2 ⟨sbd10_8_0, List.forall_mem_append.2 ⟨sbd10_8_1, sbd10_8_2⟩⟩
theorem en_okd10_8 : subEnum G n Ps d10_8 = true :=
  subEnum_fast ld_okd10_8 (enumS_of_coverL coverd10_8 subsd10_8)
theorem coverd10_9 : (coverL d10_9.aL d10_9.w 6 2 6 (fun _ => 0) (d10_9.S * d10_9.K) [] preLd10_9).isSome = true := by decide +kernel
theorem subsd10_9 : ∀ q ∈ preLd10_9, subd10_9 q = true := by
  unfold preLd10_9
  exact sbd10_9_0
theorem en_okd10_9 : subEnum G n Ps d10_9 = true :=
  subEnum_fast ld_okd10_9 (enumS_of_coverL coverd10_9 subsd10_9)
theorem coverd10_10 : (coverL d10_10.aL d10_10.w 6 2 6 (fun _ => 0) (d10_10.S * d10_10.K) [] preLd10_10).isSome = true := by decide +kernel
theorem subsd10_10 : ∀ q ∈ preLd10_10, subd10_10 q = true := by
  unfold preLd10_10
  exact sbd10_10_0
theorem en_okd10_10 : subEnum G n Ps d10_10 = true :=
  subEnum_fast ld_okd10_10 (enumS_of_coverL coverd10_10 subsd10_10)
theorem coverd10_11 : (coverL d10_11.aL d10_11.w 6 2 6 (fun _ => 0) (d10_11.S * d10_11.K) [] preLd10_11).isSome = true := by decide +kernel
theorem subsd10_11 : ∀ q ∈ preLd10_11, subd10_11 q = true := by
  unfold preLd10_11
  exact sbd10_11_0
theorem en_okd10_11 : subEnum G n Ps d10_11 = true :=
  subEnum_fast ld_okd10_11 (enumS_of_coverL coverd10_11 subsd10_11)
theorem coverd10_12 : (coverL d10_12.aL d10_12.w 6 2 6 (fun _ => 0) (d10_12.S * d10_12.K) [] preLd10_12).isSome = true := by decide +kernel
theorem subsd10_12 : ∀ q ∈ preLd10_12, subd10_12 q = true := by
  unfold preLd10_12
  exact sbd10_12_0
theorem en_okd10_12 : subEnum G n Ps d10_12 = true :=
  subEnum_fast ld_okd10_12 (enumS_of_coverL coverd10_12 subsd10_12)
theorem coverd10_13 : (coverL d10_13.aL d10_13.w 6 2 6 (fun _ => 0) (d10_13.S * d10_13.K) [] preLd10_13).isSome = true := by decide +kernel
theorem subsd10_13 : ∀ q ∈ preLd10_13, subd10_13 q = true := by
  unfold preLd10_13
  exact sbd10_13_0
theorem en_okd10_13 : subEnum G n Ps d10_13 = true :=
  subEnum_fast ld_okd10_13 (enumS_of_coverL coverd10_13 subsd10_13)
theorem coverd10_14 : (coverL d10_14.aL d10_14.w 6 2 6 (fun _ => 0) (d10_14.S * d10_14.K) [] preLd10_14).isSome = true := by decide +kernel
theorem subsd10_14 : ∀ q ∈ preLd10_14, subd10_14 q = true := by
  unfold preLd10_14
  exact List.forall_mem_append.2 ⟨sbd10_14_0, sbd10_14_1⟩
theorem en_okd10_14 : subEnum G n Ps d10_14 = true :=
  subEnum_fast ld_okd10_14 (enumS_of_coverL coverd10_14 subsd10_14)
theorem cov_ok10 : normsCovered normsL [d10_0, d10_1, d10_2, d10_3, d10_4, d10_5, d10_6, d10_7, d10_8, d10_9, d10_10, d10_11, d10_12, d10_13, d10_14] = true := by decide +kernel
theorem cell_ok10 : CellOK hd G n Ps normsL cell10 :=
  cellOK_of hd adm (by decide +kernel) cov_ok10 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd10_0, en_okd10_0⟩
    · exact ⟨pre_okd10_1, en_okd10_1⟩
    · exact ⟨pre_okd10_2, en_okd10_2⟩
    · exact ⟨pre_okd10_3, en_okd10_3⟩
    · exact ⟨pre_okd10_4, en_okd10_4⟩
    · exact ⟨pre_okd10_5, en_okd10_5⟩
    · exact ⟨pre_okd10_6, en_okd10_6⟩
    · exact ⟨pre_okd10_7, en_okd10_7⟩
    · exact ⟨pre_okd10_8, en_okd10_8⟩
    · exact ⟨pre_okd10_9, en_okd10_9⟩
    · exact ⟨pre_okd10_10, en_okd10_10⟩
    · exact ⟨pre_okd10_11, en_okd10_11⟩
    · exact ⟨pre_okd10_12, en_okd10_12⟩
    · exact ⟨pre_okd10_13, en_okd10_13⟩
    · exact ⟨pre_okd10_14, en_okd10_14⟩
  )
theorem coverd11_0 : (coverL d11_0.aL d11_0.w 6 2 6 (fun _ => 0) (d11_0.S * d11_0.K) [] preLd11_0).isSome = true := by decide +kernel
theorem subsd11_0 : ∀ q ∈ preLd11_0, subd11_0 q = true := by
  unfold preLd11_0
  exact sbd11_0_0
theorem en_okd11_0 : subEnum G n Ps d11_0 = true :=
  subEnum_fast ld_okd11_0 (enumS_of_coverL coverd11_0 subsd11_0)
theorem coverd11_1 : (coverL d11_1.aL d11_1.w 6 2 6 (fun _ => 0) (d11_1.S * d11_1.K) [] preLd11_1).isSome = true := by decide +kernel
theorem subsd11_1 : ∀ q ∈ preLd11_1, subd11_1 q = true := by
  unfold preLd11_1
  exact sbd11_1_0
theorem en_okd11_1 : subEnum G n Ps d11_1 = true :=
  subEnum_fast ld_okd11_1 (enumS_of_coverL coverd11_1 subsd11_1)
theorem coverd11_2 : (coverL d11_2.aL d11_2.w 6 2 6 (fun _ => 0) (d11_2.S * d11_2.K) [] preLd11_2).isSome = true := by decide +kernel
theorem subsd11_2 : ∀ q ∈ preLd11_2, subd11_2 q = true := by
  unfold preLd11_2
  exact sbd11_2_0
theorem en_okd11_2 : subEnum G n Ps d11_2 = true :=
  subEnum_fast ld_okd11_2 (enumS_of_coverL coverd11_2 subsd11_2)
theorem coverd11_3 : (coverL d11_3.aL d11_3.w 6 2 6 (fun _ => 0) (d11_3.S * d11_3.K) [] preLd11_3).isSome = true := by decide +kernel
theorem subsd11_3 : ∀ q ∈ preLd11_3, subd11_3 q = true := by
  unfold preLd11_3
  exact sbd11_3_0
theorem en_okd11_3 : subEnum G n Ps d11_3 = true :=
  subEnum_fast ld_okd11_3 (enumS_of_coverL coverd11_3 subsd11_3)
theorem coverd11_4 : (coverL d11_4.aL d11_4.w 6 2 6 (fun _ => 0) (d11_4.S * d11_4.K) [] preLd11_4).isSome = true := by decide +kernel
theorem subsd11_4 : ∀ q ∈ preLd11_4, subd11_4 q = true := by
  unfold preLd11_4
  exact sbd11_4_0
theorem en_okd11_4 : subEnum G n Ps d11_4 = true :=
  subEnum_fast ld_okd11_4 (enumS_of_coverL coverd11_4 subsd11_4)
theorem coverd11_5 : (coverL d11_5.aL d11_5.w 6 2 6 (fun _ => 0) (d11_5.S * d11_5.K) [] preLd11_5).isSome = true := by decide +kernel
theorem subsd11_5 : ∀ q ∈ preLd11_5, subd11_5 q = true := by
  unfold preLd11_5
  exact sbd11_5_0
theorem en_okd11_5 : subEnum G n Ps d11_5 = true :=
  subEnum_fast ld_okd11_5 (enumS_of_coverL coverd11_5 subsd11_5)
theorem coverd11_6 : (coverL d11_6.aL d11_6.w 6 2 6 (fun _ => 0) (d11_6.S * d11_6.K) [] preLd11_6).isSome = true := by decide +kernel
theorem subsd11_6 : ∀ q ∈ preLd11_6, subd11_6 q = true := by
  unfold preLd11_6
  exact sbd11_6_0
theorem en_okd11_6 : subEnum G n Ps d11_6 = true :=
  subEnum_fast ld_okd11_6 (enumS_of_coverL coverd11_6 subsd11_6)
theorem coverd11_7 : (coverL d11_7.aL d11_7.w 6 2 6 (fun _ => 0) (d11_7.S * d11_7.K) [] preLd11_7).isSome = true := by decide +kernel
theorem subsd11_7 : ∀ q ∈ preLd11_7, subd11_7 q = true := by
  unfold preLd11_7
  exact sbd11_7_0
theorem en_okd11_7 : subEnum G n Ps d11_7 = true :=
  subEnum_fast ld_okd11_7 (enumS_of_coverL coverd11_7 subsd11_7)
theorem coverd11_8 : (coverL d11_8.aL d11_8.w 6 2 6 (fun _ => 0) (d11_8.S * d11_8.K) [] preLd11_8).isSome = true := by decide +kernel
theorem subsd11_8 : ∀ q ∈ preLd11_8, subd11_8 q = true := by
  unfold preLd11_8
  exact sbd11_8_0
theorem en_okd11_8 : subEnum G n Ps d11_8 = true :=
  subEnum_fast ld_okd11_8 (enumS_of_coverL coverd11_8 subsd11_8)
theorem coverd11_9 : (coverL d11_9.aL d11_9.w 6 2 6 (fun _ => 0) (d11_9.S * d11_9.K) [] preLd11_9).isSome = true := by decide +kernel
theorem subsd11_9 : ∀ q ∈ preLd11_9, subd11_9 q = true := by
  unfold preLd11_9
  exact sbd11_9_0
theorem en_okd11_9 : subEnum G n Ps d11_9 = true :=
  subEnum_fast ld_okd11_9 (enumS_of_coverL coverd11_9 subsd11_9)
theorem coverd11_10 : (coverL d11_10.aL d11_10.w 6 2 6 (fun _ => 0) (d11_10.S * d11_10.K) [] preLd11_10).isSome = true := by decide +kernel
theorem subsd11_10 : ∀ q ∈ preLd11_10, subd11_10 q = true := by
  unfold preLd11_10
  exact sbd11_10_0
theorem en_okd11_10 : subEnum G n Ps d11_10 = true :=
  subEnum_fast ld_okd11_10 (enumS_of_coverL coverd11_10 subsd11_10)
theorem coverd11_11 : (coverL d11_11.aL d11_11.w 6 2 6 (fun _ => 0) (d11_11.S * d11_11.K) [] preLd11_11).isSome = true := by decide +kernel
theorem subsd11_11 : ∀ q ∈ preLd11_11, subd11_11 q = true := by
  unfold preLd11_11
  exact sbd11_11_0
theorem en_okd11_11 : subEnum G n Ps d11_11 = true :=
  subEnum_fast ld_okd11_11 (enumS_of_coverL coverd11_11 subsd11_11)
theorem coverd11_12 : (coverL d11_12.aL d11_12.w 6 2 6 (fun _ => 0) (d11_12.S * d11_12.K) [] preLd11_12).isSome = true := by decide +kernel
theorem subsd11_12 : ∀ q ∈ preLd11_12, subd11_12 q = true := by
  unfold preLd11_12
  exact sbd11_12_0
theorem en_okd11_12 : subEnum G n Ps d11_12 = true :=
  subEnum_fast ld_okd11_12 (enumS_of_coverL coverd11_12 subsd11_12)
theorem coverd11_13 : (coverL d11_13.aL d11_13.w 6 2 6 (fun _ => 0) (d11_13.S * d11_13.K) [] preLd11_13).isSome = true := by decide +kernel
theorem subsd11_13 : ∀ q ∈ preLd11_13, subd11_13 q = true := by
  unfold preLd11_13
  exact sbd11_13_0
theorem en_okd11_13 : subEnum G n Ps d11_13 = true :=
  subEnum_fast ld_okd11_13 (enumS_of_coverL coverd11_13 subsd11_13)
theorem coverd11_14 : (coverL d11_14.aL d11_14.w 6 2 6 (fun _ => 0) (d11_14.S * d11_14.K) [] preLd11_14).isSome = true := by decide +kernel
theorem subsd11_14 : ∀ q ∈ preLd11_14, subd11_14 q = true := by
  unfold preLd11_14
  exact sbd11_14_0
theorem en_okd11_14 : subEnum G n Ps d11_14 = true :=
  subEnum_fast ld_okd11_14 (enumS_of_coverL coverd11_14 subsd11_14)
theorem cov_ok11 : normsCovered normsL [d11_0, d11_1, d11_2, d11_3, d11_4, d11_5, d11_6, d11_7, d11_8, d11_9, d11_10, d11_11, d11_12, d11_13, d11_14] = true := by decide +kernel
theorem cell_ok11 : CellOK hd G n Ps normsL cell11 :=
  cellOK_of hd adm (by decide +kernel) cov_ok11 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd11_0, en_okd11_0⟩
    · exact ⟨pre_okd11_1, en_okd11_1⟩
    · exact ⟨pre_okd11_2, en_okd11_2⟩
    · exact ⟨pre_okd11_3, en_okd11_3⟩
    · exact ⟨pre_okd11_4, en_okd11_4⟩
    · exact ⟨pre_okd11_5, en_okd11_5⟩
    · exact ⟨pre_okd11_6, en_okd11_6⟩
    · exact ⟨pre_okd11_7, en_okd11_7⟩
    · exact ⟨pre_okd11_8, en_okd11_8⟩
    · exact ⟨pre_okd11_9, en_okd11_9⟩
    · exact ⟨pre_okd11_10, en_okd11_10⟩
    · exact ⟨pre_okd11_11, en_okd11_11⟩
    · exact ⟨pre_okd11_12, en_okd11_12⟩
    · exact ⟨pre_okd11_13, en_okd11_13⟩
    · exact ⟨pre_okd11_14, en_okd11_14⟩
  )
theorem coverd12_0 : (coverL d12_0.aL d12_0.w 6 2 6 (fun _ => 0) (d12_0.S * d12_0.K) [] preLd12_0).isSome = true := by decide +kernel
theorem subsd12_0 : ∀ q ∈ preLd12_0, subd12_0 q = true := by
  unfold preLd12_0
  exact sbd12_0_0
theorem en_okd12_0 : subEnum G n Ps d12_0 = true :=
  subEnum_fast ld_okd12_0 (enumS_of_coverL coverd12_0 subsd12_0)
theorem coverd12_1 : (coverL d12_1.aL d12_1.w 6 2 6 (fun _ => 0) (d12_1.S * d12_1.K) [] preLd12_1).isSome = true := by decide +kernel
theorem subsd12_1 : ∀ q ∈ preLd12_1, subd12_1 q = true := by
  unfold preLd12_1
  exact sbd12_1_0
theorem en_okd12_1 : subEnum G n Ps d12_1 = true :=
  subEnum_fast ld_okd12_1 (enumS_of_coverL coverd12_1 subsd12_1)
theorem coverd12_2 : (coverL d12_2.aL d12_2.w 6 2 6 (fun _ => 0) (d12_2.S * d12_2.K) [] preLd12_2).isSome = true := by decide +kernel
theorem subsd12_2 : ∀ q ∈ preLd12_2, subd12_2 q = true := by
  unfold preLd12_2
  exact sbd12_2_0
theorem en_okd12_2 : subEnum G n Ps d12_2 = true :=
  subEnum_fast ld_okd12_2 (enumS_of_coverL coverd12_2 subsd12_2)
theorem coverd12_3 : (coverL d12_3.aL d12_3.w 6 2 6 (fun _ => 0) (d12_3.S * d12_3.K) [] preLd12_3).isSome = true := by decide +kernel
theorem subsd12_3 : ∀ q ∈ preLd12_3, subd12_3 q = true := by
  unfold preLd12_3
  exact sbd12_3_0
theorem en_okd12_3 : subEnum G n Ps d12_3 = true :=
  subEnum_fast ld_okd12_3 (enumS_of_coverL coverd12_3 subsd12_3)
theorem coverd12_4 : (coverL d12_4.aL d12_4.w 6 2 6 (fun _ => 0) (d12_4.S * d12_4.K) [] preLd12_4).isSome = true := by decide +kernel
theorem subsd12_4 : ∀ q ∈ preLd12_4, subd12_4 q = true := by
  unfold preLd12_4
  exact sbd12_4_0
theorem en_okd12_4 : subEnum G n Ps d12_4 = true :=
  subEnum_fast ld_okd12_4 (enumS_of_coverL coverd12_4 subsd12_4)
theorem coverd12_5 : (coverL d12_5.aL d12_5.w 6 2 6 (fun _ => 0) (d12_5.S * d12_5.K) [] preLd12_5).isSome = true := by decide +kernel
theorem subsd12_5 : ∀ q ∈ preLd12_5, subd12_5 q = true := by
  unfold preLd12_5
  exact sbd12_5_0
theorem en_okd12_5 : subEnum G n Ps d12_5 = true :=
  subEnum_fast ld_okd12_5 (enumS_of_coverL coverd12_5 subsd12_5)
theorem coverd12_6 : (coverL d12_6.aL d12_6.w 6 2 6 (fun _ => 0) (d12_6.S * d12_6.K) [] preLd12_6).isSome = true := by decide +kernel
theorem subsd12_6 : ∀ q ∈ preLd12_6, subd12_6 q = true := by
  unfold preLd12_6
  exact sbd12_6_0
theorem en_okd12_6 : subEnum G n Ps d12_6 = true :=
  subEnum_fast ld_okd12_6 (enumS_of_coverL coverd12_6 subsd12_6)
theorem coverd12_7 : (coverL d12_7.aL d12_7.w 6 2 6 (fun _ => 0) (d12_7.S * d12_7.K) [] preLd12_7).isSome = true := by decide +kernel
theorem subsd12_7 : ∀ q ∈ preLd12_7, subd12_7 q = true := by
  unfold preLd12_7
  exact sbd12_7_0
theorem en_okd12_7 : subEnum G n Ps d12_7 = true :=
  subEnum_fast ld_okd12_7 (enumS_of_coverL coverd12_7 subsd12_7)
theorem coverd12_8 : (coverL d12_8.aL d12_8.w 6 2 6 (fun _ => 0) (d12_8.S * d12_8.K) [] preLd12_8).isSome = true := by decide +kernel
theorem subsd12_8 : ∀ q ∈ preLd12_8, subd12_8 q = true := by
  unfold preLd12_8
  exact sbd12_8_0
theorem en_okd12_8 : subEnum G n Ps d12_8 = true :=
  subEnum_fast ld_okd12_8 (enumS_of_coverL coverd12_8 subsd12_8)
theorem coverd12_9 : (coverL d12_9.aL d12_9.w 6 2 6 (fun _ => 0) (d12_9.S * d12_9.K) [] preLd12_9).isSome = true := by decide +kernel
theorem subsd12_9 : ∀ q ∈ preLd12_9, subd12_9 q = true := by
  unfold preLd12_9
  exact sbd12_9_0
theorem en_okd12_9 : subEnum G n Ps d12_9 = true :=
  subEnum_fast ld_okd12_9 (enumS_of_coverL coverd12_9 subsd12_9)
theorem coverd12_10 : (coverL d12_10.aL d12_10.w 6 2 6 (fun _ => 0) (d12_10.S * d12_10.K) [] preLd12_10).isSome = true := by decide +kernel
theorem subsd12_10 : ∀ q ∈ preLd12_10, subd12_10 q = true := by
  unfold preLd12_10
  exact sbd12_10_0
theorem en_okd12_10 : subEnum G n Ps d12_10 = true :=
  subEnum_fast ld_okd12_10 (enumS_of_coverL coverd12_10 subsd12_10)
theorem coverd12_11 : (coverL d12_11.aL d12_11.w 6 2 6 (fun _ => 0) (d12_11.S * d12_11.K) [] preLd12_11).isSome = true := by decide +kernel
theorem subsd12_11 : ∀ q ∈ preLd12_11, subd12_11 q = true := by
  unfold preLd12_11
  exact sbd12_11_0
theorem en_okd12_11 : subEnum G n Ps d12_11 = true :=
  subEnum_fast ld_okd12_11 (enumS_of_coverL coverd12_11 subsd12_11)
theorem coverd12_12 : (coverL d12_12.aL d12_12.w 6 2 6 (fun _ => 0) (d12_12.S * d12_12.K) [] preLd12_12).isSome = true := by decide +kernel
theorem subsd12_12 : ∀ q ∈ preLd12_12, subd12_12 q = true := by
  unfold preLd12_12
  exact sbd12_12_0
theorem en_okd12_12 : subEnum G n Ps d12_12 = true :=
  subEnum_fast ld_okd12_12 (enumS_of_coverL coverd12_12 subsd12_12)
theorem coverd12_13 : (coverL d12_13.aL d12_13.w 6 2 6 (fun _ => 0) (d12_13.S * d12_13.K) [] preLd12_13).isSome = true := by decide +kernel
theorem subsd12_13 : ∀ q ∈ preLd12_13, subd12_13 q = true := by
  unfold preLd12_13
  exact sbd12_13_0
theorem en_okd12_13 : subEnum G n Ps d12_13 = true :=
  subEnum_fast ld_okd12_13 (enumS_of_coverL coverd12_13 subsd12_13)
theorem coverd12_14 : (coverL d12_14.aL d12_14.w 6 2 6 (fun _ => 0) (d12_14.S * d12_14.K) [] preLd12_14).isSome = true := by decide +kernel
theorem subsd12_14 : ∀ q ∈ preLd12_14, subd12_14 q = true := by
  unfold preLd12_14
  exact sbd12_14_0
theorem en_okd12_14 : subEnum G n Ps d12_14 = true :=
  subEnum_fast ld_okd12_14 (enumS_of_coverL coverd12_14 subsd12_14)
theorem cov_ok12 : normsCovered normsL [d12_0, d12_1, d12_2, d12_3, d12_4, d12_5, d12_6, d12_7, d12_8, d12_9, d12_10, d12_11, d12_12, d12_13, d12_14] = true := by decide +kernel
theorem cell_ok12 : CellOK hd G n Ps normsL cell12 :=
  cellOK_of hd adm (by decide +kernel) cov_ok12 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd12_0, en_okd12_0⟩
    · exact ⟨pre_okd12_1, en_okd12_1⟩
    · exact ⟨pre_okd12_2, en_okd12_2⟩
    · exact ⟨pre_okd12_3, en_okd12_3⟩
    · exact ⟨pre_okd12_4, en_okd12_4⟩
    · exact ⟨pre_okd12_5, en_okd12_5⟩
    · exact ⟨pre_okd12_6, en_okd12_6⟩
    · exact ⟨pre_okd12_7, en_okd12_7⟩
    · exact ⟨pre_okd12_8, en_okd12_8⟩
    · exact ⟨pre_okd12_9, en_okd12_9⟩
    · exact ⟨pre_okd12_10, en_okd12_10⟩
    · exact ⟨pre_okd12_11, en_okd12_11⟩
    · exact ⟨pre_okd12_12, en_okd12_12⟩
    · exact ⟨pre_okd12_13, en_okd12_13⟩
    · exact ⟨pre_okd12_14, en_okd12_14⟩
  )
theorem coverd13_0 : (coverL d13_0.aL d13_0.w 6 2 6 (fun _ => 0) (d13_0.S * d13_0.K) [] preLd13_0).isSome = true := by decide +kernel
theorem subsd13_0 : ∀ q ∈ preLd13_0, subd13_0 q = true := by
  unfold preLd13_0
  exact sbd13_0_0
theorem en_okd13_0 : subEnum G n Ps d13_0 = true :=
  subEnum_fast ld_okd13_0 (enumS_of_coverL coverd13_0 subsd13_0)
theorem coverd13_1 : (coverL d13_1.aL d13_1.w 6 2 6 (fun _ => 0) (d13_1.S * d13_1.K) [] preLd13_1).isSome = true := by decide +kernel
theorem subsd13_1 : ∀ q ∈ preLd13_1, subd13_1 q = true := by
  unfold preLd13_1
  exact sbd13_1_0
theorem en_okd13_1 : subEnum G n Ps d13_1 = true :=
  subEnum_fast ld_okd13_1 (enumS_of_coverL coverd13_1 subsd13_1)
theorem coverd13_2 : (coverL d13_2.aL d13_2.w 6 2 6 (fun _ => 0) (d13_2.S * d13_2.K) [] preLd13_2).isSome = true := by decide +kernel
theorem subsd13_2 : ∀ q ∈ preLd13_2, subd13_2 q = true := by
  unfold preLd13_2
  exact sbd13_2_0
theorem en_okd13_2 : subEnum G n Ps d13_2 = true :=
  subEnum_fast ld_okd13_2 (enumS_of_coverL coverd13_2 subsd13_2)
theorem coverd13_3 : (coverL d13_3.aL d13_3.w 6 2 6 (fun _ => 0) (d13_3.S * d13_3.K) [] preLd13_3).isSome = true := by decide +kernel
theorem subsd13_3 : ∀ q ∈ preLd13_3, subd13_3 q = true := by
  unfold preLd13_3
  exact sbd13_3_0
theorem en_okd13_3 : subEnum G n Ps d13_3 = true :=
  subEnum_fast ld_okd13_3 (enumS_of_coverL coverd13_3 subsd13_3)
theorem coverd13_4 : (coverL d13_4.aL d13_4.w 6 2 6 (fun _ => 0) (d13_4.S * d13_4.K) [] preLd13_4).isSome = true := by decide +kernel
theorem subsd13_4 : ∀ q ∈ preLd13_4, subd13_4 q = true := by
  unfold preLd13_4
  exact sbd13_4_0
theorem en_okd13_4 : subEnum G n Ps d13_4 = true :=
  subEnum_fast ld_okd13_4 (enumS_of_coverL coverd13_4 subsd13_4)
theorem coverd13_5 : (coverL d13_5.aL d13_5.w 6 2 6 (fun _ => 0) (d13_5.S * d13_5.K) [] preLd13_5).isSome = true := by decide +kernel
theorem subsd13_5 : ∀ q ∈ preLd13_5, subd13_5 q = true := by
  unfold preLd13_5
  exact sbd13_5_0
theorem en_okd13_5 : subEnum G n Ps d13_5 = true :=
  subEnum_fast ld_okd13_5 (enumS_of_coverL coverd13_5 subsd13_5)
theorem coverd13_6 : (coverL d13_6.aL d13_6.w 6 2 6 (fun _ => 0) (d13_6.S * d13_6.K) [] preLd13_6).isSome = true := by decide +kernel
theorem subsd13_6 : ∀ q ∈ preLd13_6, subd13_6 q = true := by
  unfold preLd13_6
  exact sbd13_6_0
theorem en_okd13_6 : subEnum G n Ps d13_6 = true :=
  subEnum_fast ld_okd13_6 (enumS_of_coverL coverd13_6 subsd13_6)
theorem coverd13_7 : (coverL d13_7.aL d13_7.w 6 2 6 (fun _ => 0) (d13_7.S * d13_7.K) [] preLd13_7).isSome = true := by decide +kernel
theorem subsd13_7 : ∀ q ∈ preLd13_7, subd13_7 q = true := by
  unfold preLd13_7
  exact sbd13_7_0
theorem en_okd13_7 : subEnum G n Ps d13_7 = true :=
  subEnum_fast ld_okd13_7 (enumS_of_coverL coverd13_7 subsd13_7)
theorem coverd13_8 : (coverL d13_8.aL d13_8.w 6 2 6 (fun _ => 0) (d13_8.S * d13_8.K) [] preLd13_8).isSome = true := by decide +kernel
theorem subsd13_8 : ∀ q ∈ preLd13_8, subd13_8 q = true := by
  unfold preLd13_8
  exact sbd13_8_0
theorem en_okd13_8 : subEnum G n Ps d13_8 = true :=
  subEnum_fast ld_okd13_8 (enumS_of_coverL coverd13_8 subsd13_8)
theorem coverd13_9 : (coverL d13_9.aL d13_9.w 6 2 6 (fun _ => 0) (d13_9.S * d13_9.K) [] preLd13_9).isSome = true := by decide +kernel
theorem subsd13_9 : ∀ q ∈ preLd13_9, subd13_9 q = true := by
  unfold preLd13_9
  exact sbd13_9_0
theorem en_okd13_9 : subEnum G n Ps d13_9 = true :=
  subEnum_fast ld_okd13_9 (enumS_of_coverL coverd13_9 subsd13_9)
theorem coverd13_10 : (coverL d13_10.aL d13_10.w 6 2 6 (fun _ => 0) (d13_10.S * d13_10.K) [] preLd13_10).isSome = true := by decide +kernel
theorem subsd13_10 : ∀ q ∈ preLd13_10, subd13_10 q = true := by
  unfold preLd13_10
  exact sbd13_10_0
theorem en_okd13_10 : subEnum G n Ps d13_10 = true :=
  subEnum_fast ld_okd13_10 (enumS_of_coverL coverd13_10 subsd13_10)
theorem coverd13_11 : (coverL d13_11.aL d13_11.w 6 2 6 (fun _ => 0) (d13_11.S * d13_11.K) [] preLd13_11).isSome = true := by decide +kernel
theorem subsd13_11 : ∀ q ∈ preLd13_11, subd13_11 q = true := by
  unfold preLd13_11
  exact sbd13_11_0
theorem en_okd13_11 : subEnum G n Ps d13_11 = true :=
  subEnum_fast ld_okd13_11 (enumS_of_coverL coverd13_11 subsd13_11)
theorem coverd13_12 : (coverL d13_12.aL d13_12.w 6 2 6 (fun _ => 0) (d13_12.S * d13_12.K) [] preLd13_12).isSome = true := by decide +kernel
theorem subsd13_12 : ∀ q ∈ preLd13_12, subd13_12 q = true := by
  unfold preLd13_12
  exact sbd13_12_0
theorem en_okd13_12 : subEnum G n Ps d13_12 = true :=
  subEnum_fast ld_okd13_12 (enumS_of_coverL coverd13_12 subsd13_12)
theorem coverd13_13 : (coverL d13_13.aL d13_13.w 6 2 6 (fun _ => 0) (d13_13.S * d13_13.K) [] preLd13_13).isSome = true := by decide +kernel
theorem subsd13_13 : ∀ q ∈ preLd13_13, subd13_13 q = true := by
  unfold preLd13_13
  exact sbd13_13_0
theorem en_okd13_13 : subEnum G n Ps d13_13 = true :=
  subEnum_fast ld_okd13_13 (enumS_of_coverL coverd13_13 subsd13_13)
theorem coverd13_14 : (coverL d13_14.aL d13_14.w 6 2 6 (fun _ => 0) (d13_14.S * d13_14.K) [] preLd13_14).isSome = true := by decide +kernel
theorem subsd13_14 : ∀ q ∈ preLd13_14, subd13_14 q = true := by
  unfold preLd13_14
  exact List.forall_mem_append.2 ⟨sbd13_14_0, sbd13_14_1⟩
theorem en_okd13_14 : subEnum G n Ps d13_14 = true :=
  subEnum_fast ld_okd13_14 (enumS_of_coverL coverd13_14 subsd13_14)
theorem cov_ok13 : normsCovered normsL [d13_0, d13_1, d13_2, d13_3, d13_4, d13_5, d13_6, d13_7, d13_8, d13_9, d13_10, d13_11, d13_12, d13_13, d13_14] = true := by decide +kernel
theorem cell_ok13 : CellOK hd G n Ps normsL cell13 :=
  cellOK_of hd adm (by decide +kernel) cov_ok13 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd13_0, en_okd13_0⟩
    · exact ⟨pre_okd13_1, en_okd13_1⟩
    · exact ⟨pre_okd13_2, en_okd13_2⟩
    · exact ⟨pre_okd13_3, en_okd13_3⟩
    · exact ⟨pre_okd13_4, en_okd13_4⟩
    · exact ⟨pre_okd13_5, en_okd13_5⟩
    · exact ⟨pre_okd13_6, en_okd13_6⟩
    · exact ⟨pre_okd13_7, en_okd13_7⟩
    · exact ⟨pre_okd13_8, en_okd13_8⟩
    · exact ⟨pre_okd13_9, en_okd13_9⟩
    · exact ⟨pre_okd13_10, en_okd13_10⟩
    · exact ⟨pre_okd13_11, en_okd13_11⟩
    · exact ⟨pre_okd13_12, en_okd13_12⟩
    · exact ⟨pre_okd13_13, en_okd13_13⟩
    · exact ⟨pre_okd13_14, en_okd13_14⟩
  )

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8, cell_ok9, cell_ok10, cell_ok11, cell_ok12, cell_ok13]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C124
