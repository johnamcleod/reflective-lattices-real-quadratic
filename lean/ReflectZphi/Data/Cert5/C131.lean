import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C131.Base
import ReflectZphi.Data.Cert5.C131.Pchk
import ReflectZphi.Data.Cert5.C131.Pnorms
import ReflectZphi.Data.Cert5.C131.P000
import ReflectZphi.Data.Cert5.C131.P001
import ReflectZphi.Data.Cert5.C131.P002
import ReflectZphi.Data.Cert5.C131.P003
import ReflectZphi.Data.Cert5.C131.P004
import ReflectZphi.Data.Cert5.C131.P005
import ReflectZphi.Data.Cert5.C131.P006
import ReflectZphi.Data.Cert5.C131.P007
import ReflectZphi.Data.Cert5.C131.P008
import ReflectZphi.Data.Cert5.C131.P009
import ReflectZphi.Data.Cert5.C131.P010
import ReflectZphi.Data.Cert5.C131.P011
import ReflectZphi.Data.Cert5.C131.P012
import ReflectZphi.Data.Cert5.C131.P013
import ReflectZphi.Data.Cert5.C131.P014
import ReflectZphi.Data.Cert5.C131.P015
import ReflectZphi.Data.Cert5.C131.P016
import ReflectZphi.Data.Cert5.C131.P017
import ReflectZphi.Data.Cert5.C131.P018
import ReflectZphi.Data.Cert5.C131.P019
import ReflectZphi.Data.Cert5.C131.P020
import ReflectZphi.Data.Cert5.C131.P021
import ReflectZphi.Data.Cert5.C131.P022
import ReflectZphi.Data.Cert5.C131.P023
import ReflectZphi.Data.Cert5.C131.P024
import ReflectZphi.Data.Cert5.C131.P025
import ReflectZphi.Data.Cert5.C131.P026
import ReflectZphi.Data.Cert5.C131.P027
import ReflectZphi.Data.Cert5.C131.P028
import ReflectZphi.Data.Cert5.C131.P029
import ReflectZphi.Data.Cert5.C131.P030
import ReflectZphi.Data.Cert5.C131.P031
import ReflectZphi.Data.Cert5.C131.P032
import ReflectZphi.Data.Cert5.C131.P033
import ReflectZphi.Data.Cert5.C131.P034
import ReflectZphi.Data.Cert5.C131.P035
import ReflectZphi.Data.Cert5.C131.P036

namespace ReflectZphi.Data.Cert5.C131

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
theorem cov_ok0 : normsCovered normsL [d0_0, d0_1] = true := by decide +kernel
theorem cell_ok0 : CellOK hd G n Ps normsL cell0 :=
  cellOK_of hd adm (by decide +kernel) cov_ok0 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd0_0, en_okd0_0⟩
    · exact ⟨pre_okd0_1, en_okd0_1⟩
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
theorem cov_ok1 : normsCovered normsL [d1_0, d1_1] = true := by decide +kernel
theorem cell_ok1 : CellOK hd G n Ps normsL cell1 :=
  cellOK_of hd adm (by decide +kernel) cov_ok1 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd1_0, en_okd1_0⟩
    · exact ⟨pre_okd1_1, en_okd1_1⟩
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
theorem cov_ok2 : normsCovered normsL [d2_0, d2_1] = true := by decide +kernel
theorem cell_ok2 : CellOK hd G n Ps normsL cell2 :=
  cellOK_of hd adm (by decide +kernel) cov_ok2 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd2_0, en_okd2_0⟩
    · exact ⟨pre_okd2_1, en_okd2_1⟩
  )
theorem coverd3_0 : (coverL d3_0.aL d3_0.w 6 2 6 (fun _ => 0) (d3_0.S * d3_0.K) [] preLd3_0).isSome = true := by decide +kernel
theorem subsd3_0 : ∀ q ∈ preLd3_0, subd3_0 q = true := by
  unfold preLd3_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd3_0_0, List.forall_mem_append.2 ⟨sbd3_0_1, sbd3_0_2⟩⟩, List.forall_mem_append.2 ⟨sbd3_0_3, List.forall_mem_append.2 ⟨sbd3_0_4, sbd3_0_5⟩⟩⟩
theorem en_okd3_0 : subEnum G n Ps d3_0 = true :=
  subEnum_fast ld_okd3_0 (enumS_of_coverL coverd3_0 subsd3_0)
theorem coverd3_1 : (coverL d3_1.aL d3_1.w 6 2 6 (fun _ => 0) (d3_1.S * d3_1.K) [] preLd3_1).isSome = true := by decide +kernel
theorem subsd3_1 : ∀ q ∈ preLd3_1, subd3_1 q = true := by
  unfold preLd3_1
  exact sbd3_1_0
theorem en_okd3_1 : subEnum G n Ps d3_1 = true :=
  subEnum_fast ld_okd3_1 (enumS_of_coverL coverd3_1 subsd3_1)
theorem cov_ok3 : normsCovered normsL [d3_0, d3_1] = true := by decide +kernel
theorem cell_ok3 : CellOK hd G n Ps normsL cell3 :=
  cellOK_of hd adm (by decide +kernel) cov_ok3 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd3_0, en_okd3_0⟩
    · exact ⟨pre_okd3_1, en_okd3_1⟩
  )
theorem coverd4_0 : (coverL d4_0.aL d4_0.w 6 2 6 (fun _ => 0) (d4_0.S * d4_0.K) [] preLd4_0).isSome = true := by decide +kernel
theorem subsd4_0 : ∀ q ∈ preLd4_0, subd4_0 q = true := by
  unfold preLd4_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd4_0_0, sbd4_0_1⟩, List.forall_mem_append.2 ⟨sbd4_0_2, sbd4_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd4_0_4, sbd4_0_5⟩, List.forall_mem_append.2 ⟨sbd4_0_6, sbd4_0_7⟩⟩⟩
theorem en_okd4_0 : subEnum G n Ps d4_0 = true :=
  subEnum_fast ld_okd4_0 (enumS_of_coverL coverd4_0 subsd4_0)
theorem coverd4_1 : (coverL d4_1.aL d4_1.w 6 2 6 (fun _ => 0) (d4_1.S * d4_1.K) [] preLd4_1).isSome = true := by decide +kernel
theorem subsd4_1 : ∀ q ∈ preLd4_1, subd4_1 q = true := by
  unfold preLd4_1
  exact sbd4_1_0
theorem en_okd4_1 : subEnum G n Ps d4_1 = true :=
  subEnum_fast ld_okd4_1 (enumS_of_coverL coverd4_1 subsd4_1)
theorem cov_ok4 : normsCovered normsL [d4_0, d4_1] = true := by decide +kernel
theorem cell_ok4 : CellOK hd G n Ps normsL cell4 :=
  cellOK_of hd adm (by decide +kernel) cov_ok4 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd4_0, en_okd4_0⟩
    · exact ⟨pre_okd4_1, en_okd4_1⟩
  )
theorem coverd5_0 : (coverL d5_0.aL d5_0.w 6 2 6 (fun _ => 0) (d5_0.S * d5_0.K) [] preLd5_0).isSome = true := by decide +kernel
theorem subsd5_0 : ∀ q ∈ preLd5_0, subd5_0 q = true := by
  unfold preLd5_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_0_0, sbd5_0_1⟩, List.forall_mem_append.2 ⟨sbd5_0_2, List.forall_mem_append.2 ⟨sbd5_0_3, sbd5_0_4⟩⟩⟩
theorem en_okd5_0 : subEnum G n Ps d5_0 = true :=
  subEnum_fast ld_okd5_0 (enumS_of_coverL coverd5_0 subsd5_0)
theorem coverd5_1 : (coverL d5_1.aL d5_1.w 6 2 6 (fun _ => 0) (d5_1.S * d5_1.K) [] preLd5_1).isSome = true := by decide +kernel
theorem subsd5_1 : ∀ q ∈ preLd5_1, subd5_1 q = true := by
  unfold preLd5_1
  exact sbd5_1_0
theorem en_okd5_1 : subEnum G n Ps d5_1 = true :=
  subEnum_fast ld_okd5_1 (enumS_of_coverL coverd5_1 subsd5_1)
theorem cov_ok5 : normsCovered normsL [d5_0, d5_1] = true := by decide +kernel
theorem cell_ok5 : CellOK hd G n Ps normsL cell5 :=
  cellOK_of hd adm (by decide +kernel) cov_ok5 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd5_0, en_okd5_0⟩
    · exact ⟨pre_okd5_1, en_okd5_1⟩
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
  exact sbd6_1_0
theorem en_okd6_1 : subEnum G n Ps d6_1 = true :=
  subEnum_fast ld_okd6_1 (enumS_of_coverL coverd6_1 subsd6_1)
theorem cov_ok6 : normsCovered normsL [d6_0, d6_1] = true := by decide +kernel
theorem cell_ok6 : CellOK hd G n Ps normsL cell6 :=
  cellOK_of hd adm (by decide +kernel) cov_ok6 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd6_0, en_okd6_0⟩
    · exact ⟨pre_okd6_1, en_okd6_1⟩
  )
theorem coverd7_0 : (coverL d7_0.aL d7_0.w 6 2 6 (fun _ => 0) (d7_0.S * d7_0.K) [] preLd7_0).isSome = true := by decide +kernel
theorem subsd7_0 : ∀ q ∈ preLd7_0, subd7_0 q = true := by
  unfold preLd7_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_0_0, sbd7_0_1⟩, List.forall_mem_append.2 ⟨sbd7_0_2, List.forall_mem_append.2 ⟨sbd7_0_3, sbd7_0_4⟩⟩⟩
theorem en_okd7_0 : subEnum G n Ps d7_0 = true :=
  subEnum_fast ld_okd7_0 (enumS_of_coverL coverd7_0 subsd7_0)
theorem coverd7_1 : (coverL d7_1.aL d7_1.w 6 2 6 (fun _ => 0) (d7_1.S * d7_1.K) [] preLd7_1).isSome = true := by decide +kernel
theorem subsd7_1 : ∀ q ∈ preLd7_1, subd7_1 q = true := by
  unfold preLd7_1
  exact sbd7_1_0
theorem en_okd7_1 : subEnum G n Ps d7_1 = true :=
  subEnum_fast ld_okd7_1 (enumS_of_coverL coverd7_1 subsd7_1)
theorem cov_ok7 : normsCovered normsL [d7_0, d7_1] = true := by decide +kernel
theorem cell_ok7 : CellOK hd G n Ps normsL cell7 :=
  cellOK_of hd adm (by decide +kernel) cov_ok7 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd7_0, en_okd7_0⟩
    · exact ⟨pre_okd7_1, en_okd7_1⟩
  )
theorem coverd8_0 : (coverL d8_0.aL d8_0.w 6 2 6 (fun _ => 0) (d8_0.S * d8_0.K) [] preLd8_0).isSome = true := by decide +kernel
theorem subsd8_0 : ∀ q ∈ preLd8_0, subd8_0 q = true := by
  unfold preLd8_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_0_0, List.forall_mem_append.2 ⟨sbd8_0_1, sbd8_0_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_0_3, sbd8_0_4⟩, List.forall_mem_append.2 ⟨sbd8_0_5, sbd8_0_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_0_7, List.forall_mem_append.2 ⟨sbd8_0_8, sbd8_0_9⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_0_10, sbd8_0_11⟩, List.forall_mem_append.2 ⟨sbd8_0_12, sbd8_0_13⟩⟩⟩⟩
theorem en_okd8_0 : subEnum G n Ps d8_0 = true :=
  subEnum_fast ld_okd8_0 (enumS_of_coverL coverd8_0 subsd8_0)
theorem coverd8_1 : (coverL d8_1.aL d8_1.w 6 2 6 (fun _ => 0) (d8_1.S * d8_1.K) [] preLd8_1).isSome = true := by decide +kernel
theorem subsd8_1 : ∀ q ∈ preLd8_1, subd8_1 q = true := by
  unfold preLd8_1
  exact List.forall_mem_append.2 ⟨sbd8_1_0, List.forall_mem_append.2 ⟨sbd8_1_1, sbd8_1_2⟩⟩
theorem en_okd8_1 : subEnum G n Ps d8_1 = true :=
  subEnum_fast ld_okd8_1 (enumS_of_coverL coverd8_1 subsd8_1)
theorem cov_ok8 : normsCovered normsL [d8_0, d8_1] = true := by decide +kernel
theorem cell_ok8 : CellOK hd G n Ps normsL cell8 :=
  cellOK_of hd adm (by decide +kernel) cov_ok8 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd8_0, en_okd8_0⟩
    · exact ⟨pre_okd8_1, en_okd8_1⟩
  )
theorem coverd9_0 : (coverL d9_0.aL d9_0.w 6 2 6 (fun _ => 0) (d9_0.S * d9_0.K) [] preLd9_0).isSome = true := by decide +kernel
theorem subsd9_0 : ∀ q ∈ preLd9_0, subd9_0 q = true := by
  unfold preLd9_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_0, sbd9_0_1⟩, List.forall_mem_append.2 ⟨sbd9_0_2, sbd9_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_4, sbd9_0_5⟩, List.forall_mem_append.2 ⟨sbd9_0_6, List.forall_mem_append.2 ⟨sbd9_0_7, sbd9_0_8⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_9, sbd9_0_10⟩, List.forall_mem_append.2 ⟨sbd9_0_11, sbd9_0_12⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_13, sbd9_0_14⟩, List.forall_mem_append.2 ⟨sbd9_0_15, List.forall_mem_append.2 ⟨sbd9_0_16, sbd9_0_17⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_18, sbd9_0_19⟩, List.forall_mem_append.2 ⟨sbd9_0_20, sbd9_0_21⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_22, sbd9_0_23⟩, List.forall_mem_append.2 ⟨sbd9_0_24, List.forall_mem_append.2 ⟨sbd9_0_25, sbd9_0_26⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_27, sbd9_0_28⟩, List.forall_mem_append.2 ⟨sbd9_0_29, List.forall_mem_append.2 ⟨sbd9_0_30, sbd9_0_31⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_0_32, sbd9_0_33⟩, List.forall_mem_append.2 ⟨sbd9_0_34, List.forall_mem_append.2 ⟨sbd9_0_35, sbd9_0_36⟩⟩⟩⟩⟩⟩
theorem en_okd9_0 : subEnum G n Ps d9_0 = true :=
  subEnum_fast ld_okd9_0 (enumS_of_coverL coverd9_0 subsd9_0)
theorem coverd9_1 : (coverL d9_1.aL d9_1.w 6 2 6 (fun _ => 0) (d9_1.S * d9_1.K) [] preLd9_1).isSome = true := by decide +kernel
theorem subsd9_1 : ∀ q ∈ preLd9_1, subd9_1 q = true := by
  unfold preLd9_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_0, sbd9_1_1⟩, List.forall_mem_append.2 ⟨sbd9_1_2, sbd9_1_3⟩⟩
theorem en_okd9_1 : subEnum G n Ps d9_1 = true :=
  subEnum_fast ld_okd9_1 (enumS_of_coverL coverd9_1 subsd9_1)
theorem cov_ok9 : normsCovered normsL [d9_0, d9_1] = true := by decide +kernel
theorem cell_ok9 : CellOK hd G n Ps normsL cell9 :=
  cellOK_of hd adm (by decide +kernel) cov_ok9 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd9_0, en_okd9_0⟩
    · exact ⟨pre_okd9_1, en_okd9_1⟩
  )
theorem coverd10_0 : (coverL d10_0.aL d10_0.w 6 2 6 (fun _ => 0) (d10_0.S * d10_0.K) [] preLd10_0).isSome = true := by decide +kernel
theorem subsd10_0 : ∀ q ∈ preLd10_0, subd10_0 q = true := by
  unfold preLd10_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_0, List.forall_mem_append.2 ⟨sbd10_0_1, sbd10_0_2⟩⟩, List.forall_mem_append.2 ⟨sbd10_0_3, List.forall_mem_append.2 ⟨sbd10_0_4, sbd10_0_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_6, List.forall_mem_append.2 ⟨sbd10_0_7, sbd10_0_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_9, sbd10_0_10⟩, List.forall_mem_append.2 ⟨sbd10_0_11, sbd10_0_12⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_13, List.forall_mem_append.2 ⟨sbd10_0_14, sbd10_0_15⟩⟩, List.forall_mem_append.2 ⟨sbd10_0_16, List.forall_mem_append.2 ⟨sbd10_0_17, sbd10_0_18⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_19, List.forall_mem_append.2 ⟨sbd10_0_20, sbd10_0_21⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_22, sbd10_0_23⟩, List.forall_mem_append.2 ⟨sbd10_0_24, sbd10_0_25⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_26, List.forall_mem_append.2 ⟨sbd10_0_27, sbd10_0_28⟩⟩, List.forall_mem_append.2 ⟨sbd10_0_29, List.forall_mem_append.2 ⟨sbd10_0_30, sbd10_0_31⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_32, List.forall_mem_append.2 ⟨sbd10_0_33, sbd10_0_34⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_35, sbd10_0_36⟩, List.forall_mem_append.2 ⟨sbd10_0_37, sbd10_0_38⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_39, List.forall_mem_append.2 ⟨sbd10_0_40, sbd10_0_41⟩⟩, List.forall_mem_append.2 ⟨sbd10_0_42, List.forall_mem_append.2 ⟨sbd10_0_43, sbd10_0_44⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_45, List.forall_mem_append.2 ⟨sbd10_0_46, sbd10_0_47⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_0_48, sbd10_0_49⟩, List.forall_mem_append.2 ⟨sbd10_0_50, sbd10_0_51⟩⟩⟩⟩⟩⟩
theorem en_okd10_0 : subEnum G n Ps d10_0 = true :=
  subEnum_fast ld_okd10_0 (enumS_of_coverL coverd10_0 subsd10_0)
theorem coverd10_1 : (coverL d10_1.aL d10_1.w 6 2 6 (fun _ => 0) (d10_1.S * d10_1.K) [] preLd10_1).isSome = true := by decide +kernel
theorem subsd10_1 : ∀ q ∈ preLd10_1, subd10_1 q = true := by
  unfold preLd10_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_0, List.forall_mem_append.2 ⟨sbd10_1_1, sbd10_1_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_3, sbd10_1_4⟩, List.forall_mem_append.2 ⟨sbd10_1_5, sbd10_1_6⟩⟩⟩
theorem en_okd10_1 : subEnum G n Ps d10_1 = true :=
  subEnum_fast ld_okd10_1 (enumS_of_coverL coverd10_1 subsd10_1)
theorem cov_ok10 : normsCovered normsL [d10_0, d10_1] = true := by decide +kernel
theorem cell_ok10 : CellOK hd G n Ps normsL cell10 :=
  cellOK_of hd adm (by decide +kernel) cov_ok10 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd10_0, en_okd10_0⟩
    · exact ⟨pre_okd10_1, en_okd10_1⟩
  )
theorem coverd11_0 : (coverL d11_0.aL d11_0.w 6 2 6 (fun _ => 0) (d11_0.S * d11_0.K) [] preLd11_0).isSome = true := by decide +kernel
theorem subsd11_0 : ∀ q ∈ preLd11_0, subd11_0 q = true := by
  unfold preLd11_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_0, sbd11_0_1⟩, List.forall_mem_append.2 ⟨sbd11_0_2, sbd11_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_4, sbd11_0_5⟩, List.forall_mem_append.2 ⟨sbd11_0_6, sbd11_0_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_8, sbd11_0_9⟩, List.forall_mem_append.2 ⟨sbd11_0_10, sbd11_0_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_12, sbd11_0_13⟩, List.forall_mem_append.2 ⟨sbd11_0_14, List.forall_mem_append.2 ⟨sbd11_0_15, sbd11_0_16⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_17, sbd11_0_18⟩, List.forall_mem_append.2 ⟨sbd11_0_19, sbd11_0_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_21, sbd11_0_22⟩, List.forall_mem_append.2 ⟨sbd11_0_23, sbd11_0_24⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_25, sbd11_0_26⟩, List.forall_mem_append.2 ⟨sbd11_0_27, sbd11_0_28⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_29, sbd11_0_30⟩, List.forall_mem_append.2 ⟨sbd11_0_31, List.forall_mem_append.2 ⟨sbd11_0_32, sbd11_0_33⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_34, sbd11_0_35⟩, List.forall_mem_append.2 ⟨sbd11_0_36, sbd11_0_37⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_38, sbd11_0_39⟩, List.forall_mem_append.2 ⟨sbd11_0_40, sbd11_0_41⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_42, sbd11_0_43⟩, List.forall_mem_append.2 ⟨sbd11_0_44, sbd11_0_45⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_46, sbd11_0_47⟩, List.forall_mem_append.2 ⟨sbd11_0_48, List.forall_mem_append.2 ⟨sbd11_0_49, sbd11_0_50⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_51, sbd11_0_52⟩, List.forall_mem_append.2 ⟨sbd11_0_53, sbd11_0_54⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_55, sbd11_0_56⟩, List.forall_mem_append.2 ⟨sbd11_0_57, List.forall_mem_append.2 ⟨sbd11_0_58, sbd11_0_59⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_60, sbd11_0_61⟩, List.forall_mem_append.2 ⟨sbd11_0_62, sbd11_0_63⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_0_64, sbd11_0_65⟩, List.forall_mem_append.2 ⟨sbd11_0_66, List.forall_mem_append.2 ⟨sbd11_0_67, sbd11_0_68⟩⟩⟩⟩⟩⟩⟩
theorem en_okd11_0 : subEnum G n Ps d11_0 = true :=
  subEnum_fast ld_okd11_0 (enumS_of_coverL coverd11_0 subsd11_0)
theorem coverd11_1 : (coverL d11_1.aL d11_1.w 6 2 6 (fun _ => 0) (d11_1.S * d11_1.K) [] preLd11_1).isSome = true := by decide +kernel
theorem subsd11_1 : ∀ q ∈ preLd11_1, subd11_1 q = true := by
  unfold preLd11_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_0, sbd11_1_1⟩, List.forall_mem_append.2 ⟨sbd11_1_2, List.forall_mem_append.2 ⟨sbd11_1_3, sbd11_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_5, List.forall_mem_append.2 ⟨sbd11_1_6, sbd11_1_7⟩⟩, List.forall_mem_append.2 ⟨sbd11_1_8, List.forall_mem_append.2 ⟨sbd11_1_9, sbd11_1_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_11, sbd11_1_12⟩, List.forall_mem_append.2 ⟨sbd11_1_13, List.forall_mem_append.2 ⟨sbd11_1_14, sbd11_1_15⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_16, List.forall_mem_append.2 ⟨sbd11_1_17, sbd11_1_18⟩⟩, List.forall_mem_append.2 ⟨sbd11_1_19, List.forall_mem_append.2 ⟨sbd11_1_20, sbd11_1_21⟩⟩⟩⟩⟩
theorem en_okd11_1 : subEnum G n Ps d11_1 = true :=
  subEnum_fast ld_okd11_1 (enumS_of_coverL coverd11_1 subsd11_1)
theorem cov_ok11 : normsCovered normsL [d11_0, d11_1] = true := by decide +kernel
theorem cell_ok11 : CellOK hd G n Ps normsL cell11 :=
  cellOK_of hd adm (by decide +kernel) cov_ok11 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd11_0, en_okd11_0⟩
    · exact ⟨pre_okd11_1, en_okd11_1⟩
  )
theorem coverd12_0 : (coverL d12_0.aL d12_0.w 6 2 6 (fun _ => 0) (d12_0.S * d12_0.K) [] preLd12_0).isSome = true := by decide +kernel
theorem subsd12_0 : ∀ q ∈ preLd12_0, subd12_0 q = true := by
  unfold preLd12_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_0, sbd12_0_1⟩, List.forall_mem_append.2 ⟨sbd12_0_2, List.forall_mem_append.2 ⟨sbd12_0_3, sbd12_0_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_5, sbd12_0_6⟩, List.forall_mem_append.2 ⟨sbd12_0_7, List.forall_mem_append.2 ⟨sbd12_0_8, sbd12_0_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_10, sbd12_0_11⟩, List.forall_mem_append.2 ⟨sbd12_0_12, List.forall_mem_append.2 ⟨sbd12_0_13, sbd12_0_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_15, List.forall_mem_append.2 ⟨sbd12_0_16, sbd12_0_17⟩⟩, List.forall_mem_append.2 ⟨sbd12_0_18, List.forall_mem_append.2 ⟨sbd12_0_19, sbd12_0_20⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_21, sbd12_0_22⟩, List.forall_mem_append.2 ⟨sbd12_0_23, List.forall_mem_append.2 ⟨sbd12_0_24, sbd12_0_25⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_26, List.forall_mem_append.2 ⟨sbd12_0_27, sbd12_0_28⟩⟩, List.forall_mem_append.2 ⟨sbd12_0_29, List.forall_mem_append.2 ⟨sbd12_0_30, sbd12_0_31⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_32, sbd12_0_33⟩, List.forall_mem_append.2 ⟨sbd12_0_34, List.forall_mem_append.2 ⟨sbd12_0_35, sbd12_0_36⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_0_37, List.forall_mem_append.2 ⟨sbd12_0_38, sbd12_0_39⟩⟩, List.forall_mem_append.2 ⟨sbd12_0_40, List.forall_mem_append.2 ⟨sbd12_0_41, sbd12_0_42⟩⟩⟩⟩⟩⟩
theorem en_okd12_0 : subEnum G n Ps d12_0 = true :=
  subEnum_fast ld_okd12_0 (enumS_of_coverL coverd12_0 subsd12_0)
theorem coverd12_1 : (coverL d12_1.aL d12_1.w 6 2 6 (fun _ => 0) (d12_1.S * d12_1.K) [] preLd12_1).isSome = true := by decide +kernel
theorem subsd12_1 : ∀ q ∈ preLd12_1, subd12_1 q = true := by
  unfold preLd12_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_1_0, List.forall_mem_append.2 ⟨sbd12_1_1, sbd12_1_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_1_3, sbd12_1_4⟩, List.forall_mem_append.2 ⟨sbd12_1_5, sbd12_1_6⟩⟩⟩
theorem en_okd12_1 : subEnum G n Ps d12_1 = true :=
  subEnum_fast ld_okd12_1 (enumS_of_coverL coverd12_1 subsd12_1)
theorem cov_ok12 : normsCovered normsL [d12_0, d12_1] = true := by decide +kernel
theorem cell_ok12 : CellOK hd G n Ps normsL cell12 :=
  cellOK_of hd adm (by decide +kernel) cov_ok12 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd12_0, en_okd12_0⟩
    · exact ⟨pre_okd12_1, en_okd12_1⟩
  )
theorem coverd13_0 : (coverL d13_0.aL d13_0.w 6 2 6 (fun _ => 0) (d13_0.S * d13_0.K) [] preLd13_0).isSome = true := by decide +kernel
theorem subsd13_0 : ∀ q ∈ preLd13_0, subd13_0 q = true := by
  unfold preLd13_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_0_0, List.forall_mem_append.2 ⟨sbd13_0_1, sbd13_0_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_0_3, sbd13_0_4⟩, List.forall_mem_append.2 ⟨sbd13_0_5, sbd13_0_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_0_7, List.forall_mem_append.2 ⟨sbd13_0_8, sbd13_0_9⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_0_10, sbd13_0_11⟩, List.forall_mem_append.2 ⟨sbd13_0_12, sbd13_0_13⟩⟩⟩⟩
theorem en_okd13_0 : subEnum G n Ps d13_0 = true :=
  subEnum_fast ld_okd13_0 (enumS_of_coverL coverd13_0 subsd13_0)
theorem coverd13_1 : (coverL d13_1.aL d13_1.w 6 2 6 (fun _ => 0) (d13_1.S * d13_1.K) [] preLd13_1).isSome = true := by decide +kernel
theorem subsd13_1 : ∀ q ∈ preLd13_1, subd13_1 q = true := by
  unfold preLd13_1
  exact List.forall_mem_append.2 ⟨sbd13_1_0, List.forall_mem_append.2 ⟨sbd13_1_1, sbd13_1_2⟩⟩
theorem en_okd13_1 : subEnum G n Ps d13_1 = true :=
  subEnum_fast ld_okd13_1 (enumS_of_coverL coverd13_1 subsd13_1)
theorem cov_ok13 : normsCovered normsL [d13_0, d13_1] = true := by decide +kernel
theorem cell_ok13 : CellOK hd G n Ps normsL cell13 :=
  cellOK_of hd adm (by decide +kernel) cov_ok13 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd13_0, en_okd13_0⟩
    · exact ⟨pre_okd13_1, en_okd13_1⟩
  )
theorem coverd14_0 : (coverL d14_0.aL d14_0.w 6 2 6 (fun _ => 0) (d14_0.S * d14_0.K) [] preLd14_0).isSome = true := by decide +kernel
theorem subsd14_0 : ∀ q ∈ preLd14_0, subd14_0 q = true := by
  unfold preLd14_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_0_0, sbd14_0_1⟩, List.forall_mem_append.2 ⟨sbd14_0_2, sbd14_0_3⟩⟩
theorem en_okd14_0 : subEnum G n Ps d14_0 = true :=
  subEnum_fast ld_okd14_0 (enumS_of_coverL coverd14_0 subsd14_0)
theorem coverd14_1 : (coverL d14_1.aL d14_1.w 6 2 6 (fun _ => 0) (d14_1.S * d14_1.K) [] preLd14_1).isSome = true := by decide +kernel
theorem subsd14_1 : ∀ q ∈ preLd14_1, subd14_1 q = true := by
  unfold preLd14_1
  exact List.forall_mem_append.2 ⟨sbd14_1_0, sbd14_1_1⟩
theorem en_okd14_1 : subEnum G n Ps d14_1 = true :=
  subEnum_fast ld_okd14_1 (enumS_of_coverL coverd14_1 subsd14_1)
theorem cov_ok14 : normsCovered normsL [d14_0, d14_1] = true := by decide +kernel
theorem cell_ok14 : CellOK hd G n Ps normsL cell14 :=
  cellOK_of hd adm (by decide +kernel) cov_ok14 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd14_0, en_okd14_0⟩
    · exact ⟨pre_okd14_1, en_okd14_1⟩
  )
theorem coverd15_0 : (coverL d15_0.aL d15_0.w 6 2 6 (fun _ => 0) (d15_0.S * d15_0.K) [] preLd15_0).isSome = true := by decide +kernel
theorem subsd15_0 : ∀ q ∈ preLd15_0, subd15_0 q = true := by
  unfold preLd15_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_0_0, List.forall_mem_append.2 ⟨sbd15_0_1, sbd15_0_2⟩⟩, List.forall_mem_append.2 ⟨sbd15_0_3, List.forall_mem_append.2 ⟨sbd15_0_4, sbd15_0_5⟩⟩⟩
theorem en_okd15_0 : subEnum G n Ps d15_0 = true :=
  subEnum_fast ld_okd15_0 (enumS_of_coverL coverd15_0 subsd15_0)
theorem coverd15_1 : (coverL d15_1.aL d15_1.w 6 2 6 (fun _ => 0) (d15_1.S * d15_1.K) [] preLd15_1).isSome = true := by decide +kernel
theorem subsd15_1 : ∀ q ∈ preLd15_1, subd15_1 q = true := by
  unfold preLd15_1
  exact List.forall_mem_append.2 ⟨sbd15_1_0, sbd15_1_1⟩
theorem en_okd15_1 : subEnum G n Ps d15_1 = true :=
  subEnum_fast ld_okd15_1 (enumS_of_coverL coverd15_1 subsd15_1)
theorem cov_ok15 : normsCovered normsL [d15_0, d15_1] = true := by decide +kernel
theorem cell_ok15 : CellOK hd G n Ps normsL cell15 :=
  cellOK_of hd adm (by decide +kernel) cov_ok15 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd15_0, en_okd15_0⟩
    · exact ⟨pre_okd15_1, en_okd15_1⟩
  )
theorem coverd16_0 : (coverL d16_0.aL d16_0.w 6 2 6 (fun _ => 0) (d16_0.S * d16_0.K) [] preLd16_0).isSome = true := by decide +kernel
theorem subsd16_0 : ∀ q ∈ preLd16_0, subd16_0 q = true := by
  unfold preLd16_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_0_0, List.forall_mem_append.2 ⟨sbd16_0_1, sbd16_0_2⟩⟩, List.forall_mem_append.2 ⟨sbd16_0_3, List.forall_mem_append.2 ⟨sbd16_0_4, sbd16_0_5⟩⟩⟩
theorem en_okd16_0 : subEnum G n Ps d16_0 = true :=
  subEnum_fast ld_okd16_0 (enumS_of_coverL coverd16_0 subsd16_0)
theorem coverd16_1 : (coverL d16_1.aL d16_1.w 6 2 6 (fun _ => 0) (d16_1.S * d16_1.K) [] preLd16_1).isSome = true := by decide +kernel
theorem subsd16_1 : ∀ q ∈ preLd16_1, subd16_1 q = true := by
  unfold preLd16_1
  exact List.forall_mem_append.2 ⟨sbd16_1_0, sbd16_1_1⟩
theorem en_okd16_1 : subEnum G n Ps d16_1 = true :=
  subEnum_fast ld_okd16_1 (enumS_of_coverL coverd16_1 subsd16_1)
theorem cov_ok16 : normsCovered normsL [d16_0, d16_1] = true := by decide +kernel
theorem cell_ok16 : CellOK hd G n Ps normsL cell16 :=
  cellOK_of hd adm (by decide +kernel) cov_ok16 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd16_0, en_okd16_0⟩
    · exact ⟨pre_okd16_1, en_okd16_1⟩
  )
theorem coverd17_0 : (coverL d17_0.aL d17_0.w 6 2 6 (fun _ => 0) (d17_0.S * d17_0.K) [] preLd17_0).isSome = true := by decide +kernel
theorem subsd17_0 : ∀ q ∈ preLd17_0, subd17_0 q = true := by
  unfold preLd17_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_0_0, sbd17_0_1⟩, List.forall_mem_append.2 ⟨sbd17_0_2, sbd17_0_3⟩⟩
theorem en_okd17_0 : subEnum G n Ps d17_0 = true :=
  subEnum_fast ld_okd17_0 (enumS_of_coverL coverd17_0 subsd17_0)
theorem coverd17_1 : (coverL d17_1.aL d17_1.w 6 2 6 (fun _ => 0) (d17_1.S * d17_1.K) [] preLd17_1).isSome = true := by decide +kernel
theorem subsd17_1 : ∀ q ∈ preLd17_1, subd17_1 q = true := by
  unfold preLd17_1
  exact sbd17_1_0
theorem en_okd17_1 : subEnum G n Ps d17_1 = true :=
  subEnum_fast ld_okd17_1 (enumS_of_coverL coverd17_1 subsd17_1)
theorem cov_ok17 : normsCovered normsL [d17_0, d17_1] = true := by decide +kernel
theorem cell_ok17 : CellOK hd G n Ps normsL cell17 :=
  cellOK_of hd adm (by decide +kernel) cov_ok17 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd17_0, en_okd17_0⟩
    · exact ⟨pre_okd17_1, en_okd17_1⟩
  )
theorem coverd18_0 : (coverL d18_0.aL d18_0.w 6 2 6 (fun _ => 0) (d18_0.S * d18_0.K) [] preLd18_0).isSome = true := by decide +kernel
theorem subsd18_0 : ∀ q ∈ preLd18_0, subd18_0 q = true := by
  unfold preLd18_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_0_0, sbd18_0_1⟩, List.forall_mem_append.2 ⟨sbd18_0_2, sbd18_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_0_4, sbd18_0_5⟩, List.forall_mem_append.2 ⟨sbd18_0_6, sbd18_0_7⟩⟩⟩
theorem en_okd18_0 : subEnum G n Ps d18_0 = true :=
  subEnum_fast ld_okd18_0 (enumS_of_coverL coverd18_0 subsd18_0)
theorem coverd18_1 : (coverL d18_1.aL d18_1.w 6 2 6 (fun _ => 0) (d18_1.S * d18_1.K) [] preLd18_1).isSome = true := by decide +kernel
theorem subsd18_1 : ∀ q ∈ preLd18_1, subd18_1 q = true := by
  unfold preLd18_1
  exact sbd18_1_0
theorem en_okd18_1 : subEnum G n Ps d18_1 = true :=
  subEnum_fast ld_okd18_1 (enumS_of_coverL coverd18_1 subsd18_1)
theorem cov_ok18 : normsCovered normsL [d18_0, d18_1] = true := by decide +kernel
theorem cell_ok18 : CellOK hd G n Ps normsL cell18 :=
  cellOK_of hd adm (by decide +kernel) cov_ok18 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd18_0, en_okd18_0⟩
    · exact ⟨pre_okd18_1, en_okd18_1⟩
  )
theorem coverd19_0 : (coverL d19_0.aL d19_0.w 6 2 6 (fun _ => 0) (d19_0.S * d19_0.K) [] preLd19_0).isSome = true := by decide +kernel
theorem subsd19_0 : ∀ q ∈ preLd19_0, subd19_0 q = true := by
  unfold preLd19_0
  exact List.forall_mem_append.2 ⟨sbd19_0_0, sbd19_0_1⟩
theorem en_okd19_0 : subEnum G n Ps d19_0 = true :=
  subEnum_fast ld_okd19_0 (enumS_of_coverL coverd19_0 subsd19_0)
theorem coverd19_1 : (coverL d19_1.aL d19_1.w 6 2 6 (fun _ => 0) (d19_1.S * d19_1.K) [] preLd19_1).isSome = true := by decide +kernel
theorem subsd19_1 : ∀ q ∈ preLd19_1, subd19_1 q = true := by
  unfold preLd19_1
  exact sbd19_1_0
theorem en_okd19_1 : subEnum G n Ps d19_1 = true :=
  subEnum_fast ld_okd19_1 (enumS_of_coverL coverd19_1 subsd19_1)
theorem cov_ok19 : normsCovered normsL [d19_0, d19_1] = true := by decide +kernel
theorem cell_ok19 : CellOK hd G n Ps normsL cell19 :=
  cellOK_of hd adm (by decide +kernel) cov_ok19 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd19_0, en_okd19_0⟩
    · exact ⟨pre_okd19_1, en_okd19_1⟩
  )
theorem coverd20_0 : (coverL d20_0.aL d20_0.w 6 2 6 (fun _ => 0) (d20_0.S * d20_0.K) [] preLd20_0).isSome = true := by decide +kernel
theorem subsd20_0 : ∀ q ∈ preLd20_0, subd20_0 q = true := by
  unfold preLd20_0
  exact sbd20_0_0
theorem en_okd20_0 : subEnum G n Ps d20_0 = true :=
  subEnum_fast ld_okd20_0 (enumS_of_coverL coverd20_0 subsd20_0)
theorem coverd20_1 : (coverL d20_1.aL d20_1.w 6 2 6 (fun _ => 0) (d20_1.S * d20_1.K) [] preLd20_1).isSome = true := by decide +kernel
theorem subsd20_1 : ∀ q ∈ preLd20_1, subd20_1 q = true := by
  unfold preLd20_1
  exact sbd20_1_0
theorem en_okd20_1 : subEnum G n Ps d20_1 = true :=
  subEnum_fast ld_okd20_1 (enumS_of_coverL coverd20_1 subsd20_1)
theorem cov_ok20 : normsCovered normsL [d20_0, d20_1] = true := by decide +kernel
theorem cell_ok20 : CellOK hd G n Ps normsL cell20 :=
  cellOK_of hd adm (by decide +kernel) cov_ok20 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd20_0, en_okd20_0⟩
    · exact ⟨pre_okd20_1, en_okd20_1⟩
  )
theorem coverd21_0 : (coverL d21_0.aL d21_0.w 6 2 6 (fun _ => 0) (d21_0.S * d21_0.K) [] preLd21_0).isSome = true := by decide +kernel
theorem subsd21_0 : ∀ q ∈ preLd21_0, subd21_0 q = true := by
  unfold preLd21_0
  exact sbd21_0_0
theorem en_okd21_0 : subEnum G n Ps d21_0 = true :=
  subEnum_fast ld_okd21_0 (enumS_of_coverL coverd21_0 subsd21_0)
theorem coverd21_1 : (coverL d21_1.aL d21_1.w 6 2 6 (fun _ => 0) (d21_1.S * d21_1.K) [] preLd21_1).isSome = true := by decide +kernel
theorem subsd21_1 : ∀ q ∈ preLd21_1, subd21_1 q = true := by
  unfold preLd21_1
  exact sbd21_1_0
theorem en_okd21_1 : subEnum G n Ps d21_1 = true :=
  subEnum_fast ld_okd21_1 (enumS_of_coverL coverd21_1 subsd21_1)
theorem cov_ok21 : normsCovered normsL [d21_0, d21_1] = true := by decide +kernel
theorem cell_ok21 : CellOK hd G n Ps normsL cell21 :=
  cellOK_of hd adm (by decide +kernel) cov_ok21 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨pre_okd21_0, en_okd21_0⟩
    · exact ⟨pre_okd21_1, en_okd21_1⟩
  )

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8, cell_ok9, cell_ok10, cell_ok11, cell_ok12, cell_ok13, cell_ok14, cell_ok15, cell_ok16, cell_ok17, cell_ok18, cell_ok19, cell_ok20, cell_ok21]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C131
