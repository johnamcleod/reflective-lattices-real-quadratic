import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C116.Base
import ReflectZphi.Data.Cert5.C116.Pchk
import ReflectZphi.Data.Cert5.C116.Pnorms
import ReflectZphi.Data.Cert5.C116.P000
import ReflectZphi.Data.Cert5.C116.P001
import ReflectZphi.Data.Cert5.C116.P002
import ReflectZphi.Data.Cert5.C116.P003
import ReflectZphi.Data.Cert5.C116.P004
import ReflectZphi.Data.Cert5.C116.P005
import ReflectZphi.Data.Cert5.C116.P006
import ReflectZphi.Data.Cert5.C116.P007
import ReflectZphi.Data.Cert5.C116.P008
import ReflectZphi.Data.Cert5.C116.P009
import ReflectZphi.Data.Cert5.C116.P010
import ReflectZphi.Data.Cert5.C116.P011
import ReflectZphi.Data.Cert5.C116.P012
import ReflectZphi.Data.Cert5.C116.P013
import ReflectZphi.Data.Cert5.C116.P014
import ReflectZphi.Data.Cert5.C116.P015
import ReflectZphi.Data.Cert5.C116.P016
import ReflectZphi.Data.Cert5.C116.P017
import ReflectZphi.Data.Cert5.C116.P018
import ReflectZphi.Data.Cert5.C116.P019
import ReflectZphi.Data.Cert5.C116.P020
import ReflectZphi.Data.Cert5.C116.P021
import ReflectZphi.Data.Cert5.C116.P022
import ReflectZphi.Data.Cert5.C116.P023
import ReflectZphi.Data.Cert5.C116.P024
import ReflectZphi.Data.Cert5.C116.P025
import ReflectZphi.Data.Cert5.C116.P026
import ReflectZphi.Data.Cert5.C116.P027
import ReflectZphi.Data.Cert5.C116.P028
import ReflectZphi.Data.Cert5.C116.P029
import ReflectZphi.Data.Cert5.C116.P030
import ReflectZphi.Data.Cert5.C116.P031
import ReflectZphi.Data.Cert5.C116.P032
import ReflectZphi.Data.Cert5.C116.P033
import ReflectZphi.Data.Cert5.C116.P034
import ReflectZphi.Data.Cert5.C116.P035
import ReflectZphi.Data.Cert5.C116.P036
import ReflectZphi.Data.Cert5.C116.P037
import ReflectZphi.Data.Cert5.C116.P038
import ReflectZphi.Data.Cert5.C116.P039
import ReflectZphi.Data.Cert5.C116.P040
import ReflectZphi.Data.Cert5.C116.P041
import ReflectZphi.Data.Cert5.C116.P042
import ReflectZphi.Data.Cert5.C116.P043
import ReflectZphi.Data.Cert5.C116.P044
import ReflectZphi.Data.Cert5.C116.P045
import ReflectZphi.Data.Cert5.C116.P046
import ReflectZphi.Data.Cert5.C116.P047
import ReflectZphi.Data.Cert5.C116.P048
import ReflectZphi.Data.Cert5.C116.P049
import ReflectZphi.Data.Cert5.C116.P050
import ReflectZphi.Data.Cert5.C116.P051
import ReflectZphi.Data.Cert5.C116.P052
import ReflectZphi.Data.Cert5.C116.P053
import ReflectZphi.Data.Cert5.C116.P054
import ReflectZphi.Data.Cert5.C116.P055
import ReflectZphi.Data.Cert5.C116.P056
import ReflectZphi.Data.Cert5.C116.P057
import ReflectZphi.Data.Cert5.C116.P058

namespace ReflectZphi.Data.Cert5.C116

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
  exact List.forall_mem_append.2 ⟨sbd2_1_0, sbd2_1_1⟩
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
  exact sbd3_0_0
theorem en_okd3_0 : subEnum G n Ps d3_0 = true :=
  subEnum_fast ld_okd3_0 (enumS_of_coverL coverd3_0 subsd3_0)
theorem coverd3_1 : (coverL d3_1.aL d3_1.w 6 2 6 (fun _ => 0) (d3_1.S * d3_1.K) [] preLd3_1).isSome = true := by decide +kernel
theorem subsd3_1 : ∀ q ∈ preLd3_1, subd3_1 q = true := by
  unfold preLd3_1
  exact List.forall_mem_append.2 ⟨sbd3_1_0, List.forall_mem_append.2 ⟨sbd3_1_1, sbd3_1_2⟩⟩
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
  exact sbd4_0_0
theorem en_okd4_0 : subEnum G n Ps d4_0 = true :=
  subEnum_fast ld_okd4_0 (enumS_of_coverL coverd4_0 subsd4_0)
theorem coverd4_1 : (coverL d4_1.aL d4_1.w 6 2 6 (fun _ => 0) (d4_1.S * d4_1.K) [] preLd4_1).isSome = true := by decide +kernel
theorem subsd4_1 : ∀ q ∈ preLd4_1, subd4_1 q = true := by
  unfold preLd4_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd4_1_0, sbd4_1_1⟩, List.forall_mem_append.2 ⟨sbd4_1_2, sbd4_1_3⟩⟩
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
  exact sbd5_0_0
theorem en_okd5_0 : subEnum G n Ps d5_0 = true :=
  subEnum_fast ld_okd5_0 (enumS_of_coverL coverd5_0 subsd5_0)
theorem coverd5_1 : (coverL d5_1.aL d5_1.w 6 2 6 (fun _ => 0) (d5_1.S * d5_1.K) [] preLd5_1).isSome = true := by decide +kernel
theorem subsd5_1 : ∀ q ∈ preLd5_1, subd5_1 q = true := by
  unfold preLd5_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_1_0, sbd5_1_1⟩, List.forall_mem_append.2 ⟨sbd5_1_2, List.forall_mem_append.2 ⟨sbd5_1_3, sbd5_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_1_5, List.forall_mem_append.2 ⟨sbd5_1_6, sbd5_1_7⟩⟩, List.forall_mem_append.2 ⟨sbd5_1_8, List.forall_mem_append.2 ⟨sbd5_1_9, sbd5_1_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_1_11, List.forall_mem_append.2 ⟨sbd5_1_12, sbd5_1_13⟩⟩, List.forall_mem_append.2 ⟨sbd5_1_14, List.forall_mem_append.2 ⟨sbd5_1_15, sbd5_1_16⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd5_1_17, List.forall_mem_append.2 ⟨sbd5_1_18, sbd5_1_19⟩⟩, List.forall_mem_append.2 ⟨sbd5_1_20, List.forall_mem_append.2 ⟨sbd5_1_21, sbd5_1_22⟩⟩⟩⟩⟩
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
  exact sbd6_0_0
theorem en_okd6_0 : subEnum G n Ps d6_0 = true :=
  subEnum_fast ld_okd6_0 (enumS_of_coverL coverd6_0 subsd6_0)
theorem coverd6_1 : (coverL d6_1.aL d6_1.w 6 2 6 (fun _ => 0) (d6_1.S * d6_1.K) [] preLd6_1).isSome = true := by decide +kernel
theorem subsd6_1 : ∀ q ∈ preLd6_1, subd6_1 q = true := by
  unfold preLd6_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_0, List.forall_mem_append.2 ⟨sbd6_1_1, sbd6_1_2⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_3, List.forall_mem_append.2 ⟨sbd6_1_4, sbd6_1_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_6, List.forall_mem_append.2 ⟨sbd6_1_7, sbd6_1_8⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_9, List.forall_mem_append.2 ⟨sbd6_1_10, sbd6_1_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_12, List.forall_mem_append.2 ⟨sbd6_1_13, sbd6_1_14⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_15, List.forall_mem_append.2 ⟨sbd6_1_16, sbd6_1_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_18, List.forall_mem_append.2 ⟨sbd6_1_19, sbd6_1_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_21, sbd6_1_22⟩, List.forall_mem_append.2 ⟨sbd6_1_23, sbd6_1_24⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_25, List.forall_mem_append.2 ⟨sbd6_1_26, sbd6_1_27⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_28, List.forall_mem_append.2 ⟨sbd6_1_29, sbd6_1_30⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_31, List.forall_mem_append.2 ⟨sbd6_1_32, sbd6_1_33⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_34, List.forall_mem_append.2 ⟨sbd6_1_35, sbd6_1_36⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_37, List.forall_mem_append.2 ⟨sbd6_1_38, sbd6_1_39⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_40, List.forall_mem_append.2 ⟨sbd6_1_41, sbd6_1_42⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_43, List.forall_mem_append.2 ⟨sbd6_1_44, sbd6_1_45⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_46, sbd6_1_47⟩, List.forall_mem_append.2 ⟨sbd6_1_48, sbd6_1_49⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_50, List.forall_mem_append.2 ⟨sbd6_1_51, sbd6_1_52⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_53, List.forall_mem_append.2 ⟨sbd6_1_54, sbd6_1_55⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_56, List.forall_mem_append.2 ⟨sbd6_1_57, sbd6_1_58⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_59, List.forall_mem_append.2 ⟨sbd6_1_60, sbd6_1_61⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_62, List.forall_mem_append.2 ⟨sbd6_1_63, sbd6_1_64⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_65, List.forall_mem_append.2 ⟨sbd6_1_66, sbd6_1_67⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_68, List.forall_mem_append.2 ⟨sbd6_1_69, sbd6_1_70⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_71, sbd6_1_72⟩, List.forall_mem_append.2 ⟨sbd6_1_73, sbd6_1_74⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_75, List.forall_mem_append.2 ⟨sbd6_1_76, sbd6_1_77⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_78, List.forall_mem_append.2 ⟨sbd6_1_79, sbd6_1_80⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_81, List.forall_mem_append.2 ⟨sbd6_1_82, sbd6_1_83⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_84, List.forall_mem_append.2 ⟨sbd6_1_85, sbd6_1_86⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_87, List.forall_mem_append.2 ⟨sbd6_1_88, sbd6_1_89⟩⟩, List.forall_mem_append.2 ⟨sbd6_1_90, List.forall_mem_append.2 ⟨sbd6_1_91, sbd6_1_92⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_93, List.forall_mem_append.2 ⟨sbd6_1_94, sbd6_1_95⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd6_1_96, sbd6_1_97⟩, List.forall_mem_append.2 ⟨sbd6_1_98, sbd6_1_99⟩⟩⟩⟩⟩⟩⟩
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
  exact List.forall_mem_append.2 ⟨sbd7_0_0, List.forall_mem_append.2 ⟨sbd7_0_1, sbd7_0_2⟩⟩
theorem en_okd7_0 : subEnum G n Ps d7_0 = true :=
  subEnum_fast ld_okd7_0 (enumS_of_coverL coverd7_0 subsd7_0)
theorem coverd7_1 : (coverL d7_1.aL d7_1.w 6 2 6 (fun _ => 0) (d7_1.S * d7_1.K) [] preLd7_1).isSome = true := by decide +kernel
theorem subsd7_1 : ∀ q ∈ preLd7_1, subd7_1 q = true := by
  unfold preLd7_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_0, sbd7_1_1⟩, List.forall_mem_append.2 ⟨sbd7_1_2, sbd7_1_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_4, sbd7_1_5⟩, List.forall_mem_append.2 ⟨sbd7_1_6, List.forall_mem_append.2 ⟨sbd7_1_7, sbd7_1_8⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_9, sbd7_1_10⟩, List.forall_mem_append.2 ⟨sbd7_1_11, List.forall_mem_append.2 ⟨sbd7_1_12, sbd7_1_13⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_14, sbd7_1_15⟩, List.forall_mem_append.2 ⟨sbd7_1_16, List.forall_mem_append.2 ⟨sbd7_1_17, sbd7_1_18⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_19, sbd7_1_20⟩, List.forall_mem_append.2 ⟨sbd7_1_21, sbd7_1_22⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_23, sbd7_1_24⟩, List.forall_mem_append.2 ⟨sbd7_1_25, List.forall_mem_append.2 ⟨sbd7_1_26, sbd7_1_27⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_28, sbd7_1_29⟩, List.forall_mem_append.2 ⟨sbd7_1_30, List.forall_mem_append.2 ⟨sbd7_1_31, sbd7_1_32⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_33, sbd7_1_34⟩, List.forall_mem_append.2 ⟨sbd7_1_35, List.forall_mem_append.2 ⟨sbd7_1_36, sbd7_1_37⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_38, sbd7_1_39⟩, List.forall_mem_append.2 ⟨sbd7_1_40, sbd7_1_41⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_42, sbd7_1_43⟩, List.forall_mem_append.2 ⟨sbd7_1_44, List.forall_mem_append.2 ⟨sbd7_1_45, sbd7_1_46⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_47, sbd7_1_48⟩, List.forall_mem_append.2 ⟨sbd7_1_49, List.forall_mem_append.2 ⟨sbd7_1_50, sbd7_1_51⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_52, sbd7_1_53⟩, List.forall_mem_append.2 ⟨sbd7_1_54, List.forall_mem_append.2 ⟨sbd7_1_55, sbd7_1_56⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_57, sbd7_1_58⟩, List.forall_mem_append.2 ⟨sbd7_1_59, List.forall_mem_append.2 ⟨sbd7_1_60, sbd7_1_61⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_62, sbd7_1_63⟩, List.forall_mem_append.2 ⟨sbd7_1_64, List.forall_mem_append.2 ⟨sbd7_1_65, sbd7_1_66⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_67, sbd7_1_68⟩, List.forall_mem_append.2 ⟨sbd7_1_69, List.forall_mem_append.2 ⟨sbd7_1_70, sbd7_1_71⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_72, sbd7_1_73⟩, List.forall_mem_append.2 ⟨sbd7_1_74, List.forall_mem_append.2 ⟨sbd7_1_75, sbd7_1_76⟩⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_77, sbd7_1_78⟩, List.forall_mem_append.2 ⟨sbd7_1_79, sbd7_1_80⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_81, sbd7_1_82⟩, List.forall_mem_append.2 ⟨sbd7_1_83, List.forall_mem_append.2 ⟨sbd7_1_84, sbd7_1_85⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_86, sbd7_1_87⟩, List.forall_mem_append.2 ⟨sbd7_1_88, List.forall_mem_append.2 ⟨sbd7_1_89, sbd7_1_90⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_91, sbd7_1_92⟩, List.forall_mem_append.2 ⟨sbd7_1_93, List.forall_mem_append.2 ⟨sbd7_1_94, sbd7_1_95⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_96, sbd7_1_97⟩, List.forall_mem_append.2 ⟨sbd7_1_98, sbd7_1_99⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_100, sbd7_1_101⟩, List.forall_mem_append.2 ⟨sbd7_1_102, List.forall_mem_append.2 ⟨sbd7_1_103, sbd7_1_104⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_105, sbd7_1_106⟩, List.forall_mem_append.2 ⟨sbd7_1_107, List.forall_mem_append.2 ⟨sbd7_1_108, sbd7_1_109⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_110, sbd7_1_111⟩, List.forall_mem_append.2 ⟨sbd7_1_112, List.forall_mem_append.2 ⟨sbd7_1_113, sbd7_1_114⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_115, sbd7_1_116⟩, List.forall_mem_append.2 ⟨sbd7_1_117, sbd7_1_118⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_119, sbd7_1_120⟩, List.forall_mem_append.2 ⟨sbd7_1_121, List.forall_mem_append.2 ⟨sbd7_1_122, sbd7_1_123⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_124, sbd7_1_125⟩, List.forall_mem_append.2 ⟨sbd7_1_126, List.forall_mem_append.2 ⟨sbd7_1_127, sbd7_1_128⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_129, sbd7_1_130⟩, List.forall_mem_append.2 ⟨sbd7_1_131, List.forall_mem_append.2 ⟨sbd7_1_132, sbd7_1_133⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_134, sbd7_1_135⟩, List.forall_mem_append.2 ⟨sbd7_1_136, List.forall_mem_append.2 ⟨sbd7_1_137, sbd7_1_138⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_139, sbd7_1_140⟩, List.forall_mem_append.2 ⟨sbd7_1_141, List.forall_mem_append.2 ⟨sbd7_1_142, sbd7_1_143⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_144, sbd7_1_145⟩, List.forall_mem_append.2 ⟨sbd7_1_146, List.forall_mem_append.2 ⟨sbd7_1_147, sbd7_1_148⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd7_1_149, sbd7_1_150⟩, List.forall_mem_append.2 ⟨sbd7_1_151, List.forall_mem_append.2 ⟨sbd7_1_152, sbd7_1_153⟩⟩⟩⟩⟩⟩⟩⟩
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
  exact List.forall_mem_append.2 ⟨sbd8_0_0, List.forall_mem_append.2 ⟨sbd8_0_1, sbd8_0_2⟩⟩
theorem en_okd8_0 : subEnum G n Ps d8_0 = true :=
  subEnum_fast ld_okd8_0 (enumS_of_coverL coverd8_0 subsd8_0)
theorem coverd8_1 : (coverL d8_1.aL d8_1.w 6 2 6 (fun _ => 0) (d8_1.S * d8_1.K) [] preLd8_1).isSome = true := by decide +kernel
theorem subsd8_1 : ∀ q ∈ preLd8_1, subd8_1 q = true := by
  unfold preLd8_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_0, sbd8_1_1⟩, List.forall_mem_append.2 ⟨sbd8_1_2, sbd8_1_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_4, sbd8_1_5⟩, List.forall_mem_append.2 ⟨sbd8_1_6, sbd8_1_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_8, sbd8_1_9⟩, List.forall_mem_append.2 ⟨sbd8_1_10, sbd8_1_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_12, sbd8_1_13⟩, List.forall_mem_append.2 ⟨sbd8_1_14, List.forall_mem_append.2 ⟨sbd8_1_15, sbd8_1_16⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_17, sbd8_1_18⟩, List.forall_mem_append.2 ⟨sbd8_1_19, sbd8_1_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_21, sbd8_1_22⟩, List.forall_mem_append.2 ⟨sbd8_1_23, sbd8_1_24⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_25, sbd8_1_26⟩, List.forall_mem_append.2 ⟨sbd8_1_27, sbd8_1_28⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_29, sbd8_1_30⟩, List.forall_mem_append.2 ⟨sbd8_1_31, List.forall_mem_append.2 ⟨sbd8_1_32, sbd8_1_33⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_34, sbd8_1_35⟩, List.forall_mem_append.2 ⟨sbd8_1_36, sbd8_1_37⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_38, sbd8_1_39⟩, List.forall_mem_append.2 ⟨sbd8_1_40, sbd8_1_41⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_42, sbd8_1_43⟩, List.forall_mem_append.2 ⟨sbd8_1_44, sbd8_1_45⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_46, sbd8_1_47⟩, List.forall_mem_append.2 ⟨sbd8_1_48, List.forall_mem_append.2 ⟨sbd8_1_49, sbd8_1_50⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_51, sbd8_1_52⟩, List.forall_mem_append.2 ⟨sbd8_1_53, sbd8_1_54⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_55, sbd8_1_56⟩, List.forall_mem_append.2 ⟨sbd8_1_57, List.forall_mem_append.2 ⟨sbd8_1_58, sbd8_1_59⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_60, sbd8_1_61⟩, List.forall_mem_append.2 ⟨sbd8_1_62, sbd8_1_63⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_64, sbd8_1_65⟩, List.forall_mem_append.2 ⟨sbd8_1_66, List.forall_mem_append.2 ⟨sbd8_1_67, sbd8_1_68⟩⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_69, sbd8_1_70⟩, List.forall_mem_append.2 ⟨sbd8_1_71, sbd8_1_72⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_73, sbd8_1_74⟩, List.forall_mem_append.2 ⟨sbd8_1_75, sbd8_1_76⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_77, sbd8_1_78⟩, List.forall_mem_append.2 ⟨sbd8_1_79, sbd8_1_80⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_81, sbd8_1_82⟩, List.forall_mem_append.2 ⟨sbd8_1_83, List.forall_mem_append.2 ⟨sbd8_1_84, sbd8_1_85⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_86, sbd8_1_87⟩, List.forall_mem_append.2 ⟨sbd8_1_88, sbd8_1_89⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_90, sbd8_1_91⟩, List.forall_mem_append.2 ⟨sbd8_1_92, List.forall_mem_append.2 ⟨sbd8_1_93, sbd8_1_94⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_95, sbd8_1_96⟩, List.forall_mem_append.2 ⟨sbd8_1_97, sbd8_1_98⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_99, sbd8_1_100⟩, List.forall_mem_append.2 ⟨sbd8_1_101, List.forall_mem_append.2 ⟨sbd8_1_102, sbd8_1_103⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_104, sbd8_1_105⟩, List.forall_mem_append.2 ⟨sbd8_1_106, sbd8_1_107⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_108, sbd8_1_109⟩, List.forall_mem_append.2 ⟨sbd8_1_110, sbd8_1_111⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_112, sbd8_1_113⟩, List.forall_mem_append.2 ⟨sbd8_1_114, sbd8_1_115⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_116, sbd8_1_117⟩, List.forall_mem_append.2 ⟨sbd8_1_118, List.forall_mem_append.2 ⟨sbd8_1_119, sbd8_1_120⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_121, sbd8_1_122⟩, List.forall_mem_append.2 ⟨sbd8_1_123, sbd8_1_124⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_125, sbd8_1_126⟩, List.forall_mem_append.2 ⟨sbd8_1_127, List.forall_mem_append.2 ⟨sbd8_1_128, sbd8_1_129⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_130, sbd8_1_131⟩, List.forall_mem_append.2 ⟨sbd8_1_132, sbd8_1_133⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd8_1_134, sbd8_1_135⟩, List.forall_mem_append.2 ⟨sbd8_1_136, List.forall_mem_append.2 ⟨sbd8_1_137, sbd8_1_138⟩⟩⟩⟩⟩⟩⟩⟩
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
  exact List.forall_mem_append.2 ⟨sbd9_0_0, List.forall_mem_append.2 ⟨sbd9_0_1, sbd9_0_2⟩⟩
theorem en_okd9_0 : subEnum G n Ps d9_0 = true :=
  subEnum_fast ld_okd9_0 (enumS_of_coverL coverd9_0 subsd9_0)
theorem coverd9_1 : (coverL d9_1.aL d9_1.w 6 2 6 (fun _ => 0) (d9_1.S * d9_1.K) [] preLd9_1).isSome = true := by decide +kernel
theorem subsd9_1 : ∀ q ∈ preLd9_1, subd9_1 q = true := by
  unfold preLd9_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_0, sbd9_1_1⟩, List.forall_mem_append.2 ⟨sbd9_1_2, List.forall_mem_append.2 ⟨sbd9_1_3, sbd9_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_5, sbd9_1_6⟩, List.forall_mem_append.2 ⟨sbd9_1_7, List.forall_mem_append.2 ⟨sbd9_1_8, sbd9_1_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_10, sbd9_1_11⟩, List.forall_mem_append.2 ⟨sbd9_1_12, List.forall_mem_append.2 ⟨sbd9_1_13, sbd9_1_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_15, sbd9_1_16⟩, List.forall_mem_append.2 ⟨sbd9_1_17, List.forall_mem_append.2 ⟨sbd9_1_18, sbd9_1_19⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_20, sbd9_1_21⟩, List.forall_mem_append.2 ⟨sbd9_1_22, List.forall_mem_append.2 ⟨sbd9_1_23, sbd9_1_24⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_25, sbd9_1_26⟩, List.forall_mem_append.2 ⟨sbd9_1_27, List.forall_mem_append.2 ⟨sbd9_1_28, sbd9_1_29⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_30, sbd9_1_31⟩, List.forall_mem_append.2 ⟨sbd9_1_32, List.forall_mem_append.2 ⟨sbd9_1_33, sbd9_1_34⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_35, sbd9_1_36⟩, List.forall_mem_append.2 ⟨sbd9_1_37, List.forall_mem_append.2 ⟨sbd9_1_38, sbd9_1_39⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_40, sbd9_1_41⟩, List.forall_mem_append.2 ⟨sbd9_1_42, List.forall_mem_append.2 ⟨sbd9_1_43, sbd9_1_44⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_45, sbd9_1_46⟩, List.forall_mem_append.2 ⟨sbd9_1_47, List.forall_mem_append.2 ⟨sbd9_1_48, sbd9_1_49⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_50, sbd9_1_51⟩, List.forall_mem_append.2 ⟨sbd9_1_52, List.forall_mem_append.2 ⟨sbd9_1_53, sbd9_1_54⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_55, sbd9_1_56⟩, List.forall_mem_append.2 ⟨sbd9_1_57, List.forall_mem_append.2 ⟨sbd9_1_58, sbd9_1_59⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_60, sbd9_1_61⟩, List.forall_mem_append.2 ⟨sbd9_1_62, List.forall_mem_append.2 ⟨sbd9_1_63, sbd9_1_64⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_65, sbd9_1_66⟩, List.forall_mem_append.2 ⟨sbd9_1_67, List.forall_mem_append.2 ⟨sbd9_1_68, sbd9_1_69⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_70, sbd9_1_71⟩, List.forall_mem_append.2 ⟨sbd9_1_72, List.forall_mem_append.2 ⟨sbd9_1_73, sbd9_1_74⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_75, sbd9_1_76⟩, List.forall_mem_append.2 ⟨sbd9_1_77, List.forall_mem_append.2 ⟨sbd9_1_78, sbd9_1_79⟩⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_80, sbd9_1_81⟩, List.forall_mem_append.2 ⟨sbd9_1_82, List.forall_mem_append.2 ⟨sbd9_1_83, sbd9_1_84⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_85, sbd9_1_86⟩, List.forall_mem_append.2 ⟨sbd9_1_87, List.forall_mem_append.2 ⟨sbd9_1_88, sbd9_1_89⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_90, sbd9_1_91⟩, List.forall_mem_append.2 ⟨sbd9_1_92, List.forall_mem_append.2 ⟨sbd9_1_93, sbd9_1_94⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_95, sbd9_1_96⟩, List.forall_mem_append.2 ⟨sbd9_1_97, List.forall_mem_append.2 ⟨sbd9_1_98, sbd9_1_99⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_100, sbd9_1_101⟩, List.forall_mem_append.2 ⟨sbd9_1_102, List.forall_mem_append.2 ⟨sbd9_1_103, sbd9_1_104⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_105, sbd9_1_106⟩, List.forall_mem_append.2 ⟨sbd9_1_107, List.forall_mem_append.2 ⟨sbd9_1_108, sbd9_1_109⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_110, sbd9_1_111⟩, List.forall_mem_append.2 ⟨sbd9_1_112, List.forall_mem_append.2 ⟨sbd9_1_113, sbd9_1_114⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_115, sbd9_1_116⟩, List.forall_mem_append.2 ⟨sbd9_1_117, List.forall_mem_append.2 ⟨sbd9_1_118, sbd9_1_119⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_120, sbd9_1_121⟩, List.forall_mem_append.2 ⟨sbd9_1_122, List.forall_mem_append.2 ⟨sbd9_1_123, sbd9_1_124⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_125, sbd9_1_126⟩, List.forall_mem_append.2 ⟨sbd9_1_127, List.forall_mem_append.2 ⟨sbd9_1_128, sbd9_1_129⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_130, sbd9_1_131⟩, List.forall_mem_append.2 ⟨sbd9_1_132, List.forall_mem_append.2 ⟨sbd9_1_133, sbd9_1_134⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_135, sbd9_1_136⟩, List.forall_mem_append.2 ⟨sbd9_1_137, List.forall_mem_append.2 ⟨sbd9_1_138, sbd9_1_139⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_140, sbd9_1_141⟩, List.forall_mem_append.2 ⟨sbd9_1_142, List.forall_mem_append.2 ⟨sbd9_1_143, sbd9_1_144⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_145, sbd9_1_146⟩, List.forall_mem_append.2 ⟨sbd9_1_147, List.forall_mem_append.2 ⟨sbd9_1_148, sbd9_1_149⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_150, sbd9_1_151⟩, List.forall_mem_append.2 ⟨sbd9_1_152, List.forall_mem_append.2 ⟨sbd9_1_153, sbd9_1_154⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd9_1_155, List.forall_mem_append.2 ⟨sbd9_1_156, sbd9_1_157⟩⟩, List.forall_mem_append.2 ⟨sbd9_1_158, List.forall_mem_append.2 ⟨sbd9_1_159, sbd9_1_160⟩⟩⟩⟩⟩⟩⟩⟩
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
  exact sbd10_0_0
theorem en_okd10_0 : subEnum G n Ps d10_0 = true :=
  subEnum_fast ld_okd10_0 (enumS_of_coverL coverd10_0 subsd10_0)
theorem coverd10_1 : (coverL d10_1.aL d10_1.w 6 2 6 (fun _ => 0) (d10_1.S * d10_1.K) [] preLd10_1).isSome = true := by decide +kernel
theorem subsd10_1 : ∀ q ∈ preLd10_1, subd10_1 q = true := by
  unfold preLd10_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_0, sbd10_1_1⟩, List.forall_mem_append.2 ⟨sbd10_1_2, List.forall_mem_append.2 ⟨sbd10_1_3, sbd10_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_5, List.forall_mem_append.2 ⟨sbd10_1_6, sbd10_1_7⟩⟩, List.forall_mem_append.2 ⟨sbd10_1_8, List.forall_mem_append.2 ⟨sbd10_1_9, sbd10_1_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_11, sbd10_1_12⟩, List.forall_mem_append.2 ⟨sbd10_1_13, List.forall_mem_append.2 ⟨sbd10_1_14, sbd10_1_15⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_16, List.forall_mem_append.2 ⟨sbd10_1_17, sbd10_1_18⟩⟩, List.forall_mem_append.2 ⟨sbd10_1_19, List.forall_mem_append.2 ⟨sbd10_1_20, sbd10_1_21⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_22, sbd10_1_23⟩, List.forall_mem_append.2 ⟨sbd10_1_24, List.forall_mem_append.2 ⟨sbd10_1_25, sbd10_1_26⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_27, List.forall_mem_append.2 ⟨sbd10_1_28, sbd10_1_29⟩⟩, List.forall_mem_append.2 ⟨sbd10_1_30, List.forall_mem_append.2 ⟨sbd10_1_31, sbd10_1_32⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_33, sbd10_1_34⟩, List.forall_mem_append.2 ⟨sbd10_1_35, List.forall_mem_append.2 ⟨sbd10_1_36, sbd10_1_37⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd10_1_38, List.forall_mem_append.2 ⟨sbd10_1_39, sbd10_1_40⟩⟩, List.forall_mem_append.2 ⟨sbd10_1_41, List.forall_mem_append.2 ⟨sbd10_1_42, sbd10_1_43⟩⟩⟩⟩⟩⟩
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
  exact sbd11_0_0
theorem en_okd11_0 : subEnum G n Ps d11_0 = true :=
  subEnum_fast ld_okd11_0 (enumS_of_coverL coverd11_0 subsd11_0)
theorem coverd11_1 : (coverL d11_1.aL d11_1.w 6 2 6 (fun _ => 0) (d11_1.S * d11_1.K) [] preLd11_1).isSome = true := by decide +kernel
theorem subsd11_1 : ∀ q ∈ preLd11_1, subd11_1 q = true := by
  unfold preLd11_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_0, List.forall_mem_append.2 ⟨sbd11_1_1, sbd11_1_2⟩⟩, List.forall_mem_append.2 ⟨sbd11_1_3, List.forall_mem_append.2 ⟨sbd11_1_4, sbd11_1_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_6, List.forall_mem_append.2 ⟨sbd11_1_7, sbd11_1_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_9, sbd11_1_10⟩, List.forall_mem_append.2 ⟨sbd11_1_11, sbd11_1_12⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_13, List.forall_mem_append.2 ⟨sbd11_1_14, sbd11_1_15⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_16, sbd11_1_17⟩, List.forall_mem_append.2 ⟨sbd11_1_18, sbd11_1_19⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_20, List.forall_mem_append.2 ⟨sbd11_1_21, sbd11_1_22⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd11_1_23, sbd11_1_24⟩, List.forall_mem_append.2 ⟨sbd11_1_25, sbd11_1_26⟩⟩⟩⟩⟩
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
  exact sbd12_0_0
theorem en_okd12_0 : subEnum G n Ps d12_0 = true :=
  subEnum_fast ld_okd12_0 (enumS_of_coverL coverd12_0 subsd12_0)
theorem coverd12_1 : (coverL d12_1.aL d12_1.w 6 2 6 (fun _ => 0) (d12_1.S * d12_1.K) [] preLd12_1).isSome = true := by decide +kernel
theorem subsd12_1 : ∀ q ∈ preLd12_1, subd12_1 q = true := by
  unfold preLd12_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_1_0, sbd12_1_1⟩, List.forall_mem_append.2 ⟨sbd12_1_2, sbd12_1_3⟩⟩
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
  exact sbd13_0_0
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
  exact sbd14_0_0
theorem en_okd14_0 : subEnum G n Ps d14_0 = true :=
  subEnum_fast ld_okd14_0 (enumS_of_coverL coverd14_0 subsd14_0)
theorem coverd14_1 : (coverL d14_1.aL d14_1.w 6 2 6 (fun _ => 0) (d14_1.S * d14_1.K) [] preLd14_1).isSome = true := by decide +kernel
theorem subsd14_1 : ∀ q ∈ preLd14_1, subd14_1 q = true := by
  unfold preLd14_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_1_0, sbd14_1_1⟩, List.forall_mem_append.2 ⟨sbd14_1_2, sbd14_1_3⟩⟩
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
  exact sbd15_0_0
theorem en_okd15_0 : subEnum G n Ps d15_0 = true :=
  subEnum_fast ld_okd15_0 (enumS_of_coverL coverd15_0 subsd15_0)
theorem coverd15_1 : (coverL d15_1.aL d15_1.w 6 2 6 (fun _ => 0) (d15_1.S * d15_1.K) [] preLd15_1).isSome = true := by decide +kernel
theorem subsd15_1 : ∀ q ∈ preLd15_1, subd15_1 q = true := by
  unfold preLd15_1
  exact sbd15_1_0
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
  exact sbd16_0_0
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

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8, cell_ok9, cell_ok10, cell_ok11, cell_ok12, cell_ok13, cell_ok14, cell_ok15, cell_ok16]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C116
