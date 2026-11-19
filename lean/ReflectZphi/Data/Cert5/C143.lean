import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C143.Base
import ReflectZphi.Data.Cert5.C143.Pchk
import ReflectZphi.Data.Cert5.C143.Pnorms
import ReflectZphi.Data.Cert5.C143.P000
import ReflectZphi.Data.Cert5.C143.P001
import ReflectZphi.Data.Cert5.C143.P002
import ReflectZphi.Data.Cert5.C143.P003
import ReflectZphi.Data.Cert5.C143.P004
import ReflectZphi.Data.Cert5.C143.P005
import ReflectZphi.Data.Cert5.C143.P006
import ReflectZphi.Data.Cert5.C143.P007
import ReflectZphi.Data.Cert5.C143.P008
import ReflectZphi.Data.Cert5.C143.P009
import ReflectZphi.Data.Cert5.C143.P010
import ReflectZphi.Data.Cert5.C143.P011
import ReflectZphi.Data.Cert5.C143.P012
import ReflectZphi.Data.Cert5.C143.P013
import ReflectZphi.Data.Cert5.C143.P014
import ReflectZphi.Data.Cert5.C143.P015
import ReflectZphi.Data.Cert5.C143.P016
import ReflectZphi.Data.Cert5.C143.P017
import ReflectZphi.Data.Cert5.C143.P018
import ReflectZphi.Data.Cert5.C143.P019
import ReflectZphi.Data.Cert5.C143.P020
import ReflectZphi.Data.Cert5.C143.P021
import ReflectZphi.Data.Cert5.C143.P022
import ReflectZphi.Data.Cert5.C143.P023
import ReflectZphi.Data.Cert5.C143.P024
import ReflectZphi.Data.Cert5.C143.P025
import ReflectZphi.Data.Cert5.C143.P026
import ReflectZphi.Data.Cert5.C143.P027
import ReflectZphi.Data.Cert5.C143.P028
import ReflectZphi.Data.Cert5.C143.P029
import ReflectZphi.Data.Cert5.C143.P030
import ReflectZphi.Data.Cert5.C143.P031
import ReflectZphi.Data.Cert5.C143.P032
import ReflectZphi.Data.Cert5.C143.P033
import ReflectZphi.Data.Cert5.C143.P034
import ReflectZphi.Data.Cert5.C143.P035
import ReflectZphi.Data.Cert5.C143.P036
import ReflectZphi.Data.Cert5.C143.P037
import ReflectZphi.Data.Cert5.C143.P038
import ReflectZphi.Data.Cert5.C143.P039
import ReflectZphi.Data.Cert5.C143.P040
import ReflectZphi.Data.Cert5.C143.P041
import ReflectZphi.Data.Cert5.C143.P042
import ReflectZphi.Data.Cert5.C143.P043
import ReflectZphi.Data.Cert5.C143.P044
import ReflectZphi.Data.Cert5.C143.P045
import ReflectZphi.Data.Cert5.C143.P046
import ReflectZphi.Data.Cert5.C143.P047
import ReflectZphi.Data.Cert5.C143.P048
import ReflectZphi.Data.Cert5.C143.P049
import ReflectZphi.Data.Cert5.C143.P050
import ReflectZphi.Data.Cert5.C143.P051
import ReflectZphi.Data.Cert5.C143.P052
import ReflectZphi.Data.Cert5.C143.P053
import ReflectZphi.Data.Cert5.C143.P054
import ReflectZphi.Data.Cert5.C143.P055
import ReflectZphi.Data.Cert5.C143.P056
import ReflectZphi.Data.Cert5.C143.P057
import ReflectZphi.Data.Cert5.C143.P058
import ReflectZphi.Data.Cert5.C143.P059
import ReflectZphi.Data.Cert5.C143.P060
import ReflectZphi.Data.Cert5.C143.P061
import ReflectZphi.Data.Cert5.C143.P062
import ReflectZphi.Data.Cert5.C143.P063
import ReflectZphi.Data.Cert5.C143.P064
import ReflectZphi.Data.Cert5.C143.P065
import ReflectZphi.Data.Cert5.C143.P066
import ReflectZphi.Data.Cert5.C143.P067
import ReflectZphi.Data.Cert5.C143.P068
import ReflectZphi.Data.Cert5.C143.P069
import ReflectZphi.Data.Cert5.C143.P070
import ReflectZphi.Data.Cert5.C143.P071
import ReflectZphi.Data.Cert5.C143.P072
import ReflectZphi.Data.Cert5.C143.P073
import ReflectZphi.Data.Cert5.C143.P074
import ReflectZphi.Data.Cert5.C143.P075
import ReflectZphi.Data.Cert5.C143.P076
import ReflectZphi.Data.Cert5.C143.P077
import ReflectZphi.Data.Cert5.C143.P078
import ReflectZphi.Data.Cert5.C143.P079
import ReflectZphi.Data.Cert5.C143.P080
import ReflectZphi.Data.Cert5.C143.P081
import ReflectZphi.Data.Cert5.C143.P082
import ReflectZphi.Data.Cert5.C143.P083
import ReflectZphi.Data.Cert5.C143.P084
import ReflectZphi.Data.Cert5.C143.P085
import ReflectZphi.Data.Cert5.C143.P086
import ReflectZphi.Data.Cert5.C143.P087
import ReflectZphi.Data.Cert5.C143.P088
import ReflectZphi.Data.Cert5.C143.P089

namespace ReflectZphi.Data.Cert5.C143

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
theorem cov_ok0 : normsCovered normsL [d0_0, d0_1, d0_2, d0_3] = true := by decide +kernel
theorem cell_ok0 : CellOK hd G n Ps normsL cell0 :=
  cellOK_of hd adm (by decide +kernel) cov_ok0 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd0_0, en_okd0_0⟩
    · exact ⟨pre_okd0_1, en_okd0_1⟩
    · exact ⟨pre_okd0_2, en_okd0_2⟩
    · exact ⟨pre_okd0_3, en_okd0_3⟩
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
theorem cov_ok1 : normsCovered normsL [d1_0, d1_1, d1_2, d1_3] = true := by decide +kernel
theorem cell_ok1 : CellOK hd G n Ps normsL cell1 :=
  cellOK_of hd adm (by decide +kernel) cov_ok1 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd1_0, en_okd1_0⟩
    · exact ⟨pre_okd1_1, en_okd1_1⟩
    · exact ⟨pre_okd1_2, en_okd1_2⟩
    · exact ⟨pre_okd1_3, en_okd1_3⟩
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
theorem cov_ok2 : normsCovered normsL [d2_0, d2_1, d2_2, d2_3] = true := by decide +kernel
theorem cell_ok2 : CellOK hd G n Ps normsL cell2 :=
  cellOK_of hd adm (by decide +kernel) cov_ok2 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd2_0, en_okd2_0⟩
    · exact ⟨pre_okd2_1, en_okd2_1⟩
    · exact ⟨pre_okd2_2, en_okd2_2⟩
    · exact ⟨pre_okd2_3, en_okd2_3⟩
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
theorem cov_ok3 : normsCovered normsL [d3_0, d3_1, d3_2, d3_3] = true := by decide +kernel
theorem cell_ok3 : CellOK hd G n Ps normsL cell3 :=
  cellOK_of hd adm (by decide +kernel) cov_ok3 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd3_0, en_okd3_0⟩
    · exact ⟨pre_okd3_1, en_okd3_1⟩
    · exact ⟨pre_okd3_2, en_okd3_2⟩
    · exact ⟨pre_okd3_3, en_okd3_3⟩
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
theorem cov_ok4 : normsCovered normsL [d4_0, d4_1, d4_2, d4_3] = true := by decide +kernel
theorem cell_ok4 : CellOK hd G n Ps normsL cell4 :=
  cellOK_of hd adm (by decide +kernel) cov_ok4 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd4_0, en_okd4_0⟩
    · exact ⟨pre_okd4_1, en_okd4_1⟩
    · exact ⟨pre_okd4_2, en_okd4_2⟩
    · exact ⟨pre_okd4_3, en_okd4_3⟩
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
theorem cov_ok5 : normsCovered normsL [d5_0, d5_1, d5_2, d5_3] = true := by decide +kernel
theorem cell_ok5 : CellOK hd G n Ps normsL cell5 :=
  cellOK_of hd adm (by decide +kernel) cov_ok5 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd5_0, en_okd5_0⟩
    · exact ⟨pre_okd5_1, en_okd5_1⟩
    · exact ⟨pre_okd5_2, en_okd5_2⟩
    · exact ⟨pre_okd5_3, en_okd5_3⟩
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
theorem cov_ok6 : normsCovered normsL [d6_0, d6_1, d6_2, d6_3] = true := by decide +kernel
theorem cell_ok6 : CellOK hd G n Ps normsL cell6 :=
  cellOK_of hd adm (by decide +kernel) cov_ok6 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd6_0, en_okd6_0⟩
    · exact ⟨pre_okd6_1, en_okd6_1⟩
    · exact ⟨pre_okd6_2, en_okd6_2⟩
    · exact ⟨pre_okd6_3, en_okd6_3⟩
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
  exact sbd7_1_0
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
theorem cov_ok7 : normsCovered normsL [d7_0, d7_1, d7_2, d7_3] = true := by decide +kernel
theorem cell_ok7 : CellOK hd G n Ps normsL cell7 :=
  cellOK_of hd adm (by decide +kernel) cov_ok7 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd7_0, en_okd7_0⟩
    · exact ⟨pre_okd7_1, en_okd7_1⟩
    · exact ⟨pre_okd7_2, en_okd7_2⟩
    · exact ⟨pre_okd7_3, en_okd7_3⟩
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
theorem cov_ok8 : normsCovered normsL [d8_0, d8_1, d8_2, d8_3] = true := by decide +kernel
theorem cell_ok8 : CellOK hd G n Ps normsL cell8 :=
  cellOK_of hd adm (by decide +kernel) cov_ok8 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd8_0, en_okd8_0⟩
    · exact ⟨pre_okd8_1, en_okd8_1⟩
    · exact ⟨pre_okd8_2, en_okd8_2⟩
    · exact ⟨pre_okd8_3, en_okd8_3⟩
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
  exact List.forall_mem_append.2 ⟨sbd9_1_0, sbd9_1_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd9_3_0, sbd9_3_1⟩
theorem en_okd9_3 : subEnum G n Ps d9_3 = true :=
  subEnum_fast ld_okd9_3 (enumS_of_coverL coverd9_3 subsd9_3)
theorem cov_ok9 : normsCovered normsL [d9_0, d9_1, d9_2, d9_3] = true := by decide +kernel
theorem cell_ok9 : CellOK hd G n Ps normsL cell9 :=
  cellOK_of hd adm (by decide +kernel) cov_ok9 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd9_0, en_okd9_0⟩
    · exact ⟨pre_okd9_1, en_okd9_1⟩
    · exact ⟨pre_okd9_2, en_okd9_2⟩
    · exact ⟨pre_okd9_3, en_okd9_3⟩
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
  exact List.forall_mem_append.2 ⟨sbd10_1_0, List.forall_mem_append.2 ⟨sbd10_1_1, sbd10_1_2⟩⟩
theorem en_okd10_1 : subEnum G n Ps d10_1 = true :=
  subEnum_fast ld_okd10_1 (enumS_of_coverL coverd10_1 subsd10_1)
theorem coverd10_2 : (coverL d10_2.aL d10_2.w 6 2 6 (fun _ => 0) (d10_2.S * d10_2.K) [] preLd10_2).isSome = true := by decide +kernel
theorem subsd10_2 : ∀ q ∈ preLd10_2, subd10_2 q = true := by
  unfold preLd10_2
  exact List.forall_mem_append.2 ⟨sbd10_2_0, sbd10_2_1⟩
theorem en_okd10_2 : subEnum G n Ps d10_2 = true :=
  subEnum_fast ld_okd10_2 (enumS_of_coverL coverd10_2 subsd10_2)
theorem coverd10_3 : (coverL d10_3.aL d10_3.w 6 2 6 (fun _ => 0) (d10_3.S * d10_3.K) [] preLd10_3).isSome = true := by decide +kernel
theorem subsd10_3 : ∀ q ∈ preLd10_3, subd10_3 q = true := by
  unfold preLd10_3
  exact List.forall_mem_append.2 ⟨sbd10_3_0, sbd10_3_1⟩
theorem en_okd10_3 : subEnum G n Ps d10_3 = true :=
  subEnum_fast ld_okd10_3 (enumS_of_coverL coverd10_3 subsd10_3)
theorem cov_ok10 : normsCovered normsL [d10_0, d10_1, d10_2, d10_3] = true := by decide +kernel
theorem cell_ok10 : CellOK hd G n Ps normsL cell10 :=
  cellOK_of hd adm (by decide +kernel) cov_ok10 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd10_0, en_okd10_0⟩
    · exact ⟨pre_okd10_1, en_okd10_1⟩
    · exact ⟨pre_okd10_2, en_okd10_2⟩
    · exact ⟨pre_okd10_3, en_okd10_3⟩
  )
theorem coverd11_0 : (coverL d11_0.aL d11_0.w 6 2 6 (fun _ => 0) (d11_0.S * d11_0.K) [] preLd11_0).isSome = true := by decide +kernel
theorem subsd11_0 : ∀ q ∈ preLd11_0, subd11_0 q = true := by
  unfold preLd11_0
  exact List.forall_mem_append.2 ⟨sbd11_0_0, sbd11_0_1⟩
theorem en_okd11_0 : subEnum G n Ps d11_0 = true :=
  subEnum_fast ld_okd11_0 (enumS_of_coverL coverd11_0 subsd11_0)
theorem coverd11_1 : (coverL d11_1.aL d11_1.w 6 2 6 (fun _ => 0) (d11_1.S * d11_1.K) [] preLd11_1).isSome = true := by decide +kernel
theorem subsd11_1 : ∀ q ∈ preLd11_1, subd11_1 q = true := by
  unfold preLd11_1
  exact List.forall_mem_append.2 ⟨sbd11_1_0, sbd11_1_1⟩
theorem en_okd11_1 : subEnum G n Ps d11_1 = true :=
  subEnum_fast ld_okd11_1 (enumS_of_coverL coverd11_1 subsd11_1)
theorem coverd11_2 : (coverL d11_2.aL d11_2.w 6 2 6 (fun _ => 0) (d11_2.S * d11_2.K) [] preLd11_2).isSome = true := by decide +kernel
theorem subsd11_2 : ∀ q ∈ preLd11_2, subd11_2 q = true := by
  unfold preLd11_2
  exact List.forall_mem_append.2 ⟨sbd11_2_0, sbd11_2_1⟩
theorem en_okd11_2 : subEnum G n Ps d11_2 = true :=
  subEnum_fast ld_okd11_2 (enumS_of_coverL coverd11_2 subsd11_2)
theorem coverd11_3 : (coverL d11_3.aL d11_3.w 6 2 6 (fun _ => 0) (d11_3.S * d11_3.K) [] preLd11_3).isSome = true := by decide +kernel
theorem subsd11_3 : ∀ q ∈ preLd11_3, subd11_3 q = true := by
  unfold preLd11_3
  exact List.forall_mem_append.2 ⟨sbd11_3_0, sbd11_3_1⟩
theorem en_okd11_3 : subEnum G n Ps d11_3 = true :=
  subEnum_fast ld_okd11_3 (enumS_of_coverL coverd11_3 subsd11_3)
theorem cov_ok11 : normsCovered normsL [d11_0, d11_1, d11_2, d11_3] = true := by decide +kernel
theorem cell_ok11 : CellOK hd G n Ps normsL cell11 :=
  cellOK_of hd adm (by decide +kernel) cov_ok11 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd11_0, en_okd11_0⟩
    · exact ⟨pre_okd11_1, en_okd11_1⟩
    · exact ⟨pre_okd11_2, en_okd11_2⟩
    · exact ⟨pre_okd11_3, en_okd11_3⟩
  )
theorem coverd12_0 : (coverL d12_0.aL d12_0.w 6 2 6 (fun _ => 0) (d12_0.S * d12_0.K) [] preLd12_0).isSome = true := by decide +kernel
theorem subsd12_0 : ∀ q ∈ preLd12_0, subd12_0 q = true := by
  unfold preLd12_0
  exact List.forall_mem_append.2 ⟨sbd12_0_0, List.forall_mem_append.2 ⟨sbd12_0_1, sbd12_0_2⟩⟩
theorem en_okd12_0 : subEnum G n Ps d12_0 = true :=
  subEnum_fast ld_okd12_0 (enumS_of_coverL coverd12_0 subsd12_0)
theorem coverd12_1 : (coverL d12_1.aL d12_1.w 6 2 6 (fun _ => 0) (d12_1.S * d12_1.K) [] preLd12_1).isSome = true := by decide +kernel
theorem subsd12_1 : ∀ q ∈ preLd12_1, subd12_1 q = true := by
  unfold preLd12_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_1_0, sbd12_1_1⟩, List.forall_mem_append.2 ⟨sbd12_1_2, List.forall_mem_append.2 ⟨sbd12_1_3, sbd12_1_4⟩⟩⟩
theorem en_okd12_1 : subEnum G n Ps d12_1 = true :=
  subEnum_fast ld_okd12_1 (enumS_of_coverL coverd12_1 subsd12_1)
theorem coverd12_2 : (coverL d12_2.aL d12_2.w 6 2 6 (fun _ => 0) (d12_2.S * d12_2.K) [] preLd12_2).isSome = true := by decide +kernel
theorem subsd12_2 : ∀ q ∈ preLd12_2, subd12_2 q = true := by
  unfold preLd12_2
  exact List.forall_mem_append.2 ⟨sbd12_2_0, List.forall_mem_append.2 ⟨sbd12_2_1, sbd12_2_2⟩⟩
theorem en_okd12_2 : subEnum G n Ps d12_2 = true :=
  subEnum_fast ld_okd12_2 (enumS_of_coverL coverd12_2 subsd12_2)
theorem coverd12_3 : (coverL d12_3.aL d12_3.w 6 2 6 (fun _ => 0) (d12_3.S * d12_3.K) [] preLd12_3).isSome = true := by decide +kernel
theorem subsd12_3 : ∀ q ∈ preLd12_3, subd12_3 q = true := by
  unfold preLd12_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_3_0, List.forall_mem_append.2 ⟨sbd12_3_1, sbd12_3_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_3_3, sbd12_3_4⟩, List.forall_mem_append.2 ⟨sbd12_3_5, sbd12_3_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_3_7, List.forall_mem_append.2 ⟨sbd12_3_8, sbd12_3_9⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd12_3_10, sbd12_3_11⟩, List.forall_mem_append.2 ⟨sbd12_3_12, sbd12_3_13⟩⟩⟩⟩
theorem en_okd12_3 : subEnum G n Ps d12_3 = true :=
  subEnum_fast ld_okd12_3 (enumS_of_coverL coverd12_3 subsd12_3)
theorem cov_ok12 : normsCovered normsL [d12_0, d12_1, d12_2, d12_3] = true := by decide +kernel
theorem cell_ok12 : CellOK hd G n Ps normsL cell12 :=
  cellOK_of hd adm (by decide +kernel) cov_ok12 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd12_0, en_okd12_0⟩
    · exact ⟨pre_okd12_1, en_okd12_1⟩
    · exact ⟨pre_okd12_2, en_okd12_2⟩
    · exact ⟨pre_okd12_3, en_okd12_3⟩
  )
theorem coverd13_0 : (coverL d13_0.aL d13_0.w 6 2 6 (fun _ => 0) (d13_0.S * d13_0.K) [] preLd13_0).isSome = true := by decide +kernel
theorem subsd13_0 : ∀ q ∈ preLd13_0, subd13_0 q = true := by
  unfold preLd13_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_0_0, sbd13_0_1⟩, List.forall_mem_append.2 ⟨sbd13_0_2, sbd13_0_3⟩⟩
theorem en_okd13_0 : subEnum G n Ps d13_0 = true :=
  subEnum_fast ld_okd13_0 (enumS_of_coverL coverd13_0 subsd13_0)
theorem coverd13_1 : (coverL d13_1.aL d13_1.w 6 2 6 (fun _ => 0) (d13_1.S * d13_1.K) [] preLd13_1).isSome = true := by decide +kernel
theorem subsd13_1 : ∀ q ∈ preLd13_1, subd13_1 q = true := by
  unfold preLd13_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_1_0, sbd13_1_1⟩, List.forall_mem_append.2 ⟨sbd13_1_2, List.forall_mem_append.2 ⟨sbd13_1_3, sbd13_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_1_5, sbd13_1_6⟩, List.forall_mem_append.2 ⟨sbd13_1_7, List.forall_mem_append.2 ⟨sbd13_1_8, sbd13_1_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_1_10, sbd13_1_11⟩, List.forall_mem_append.2 ⟨sbd13_1_12, List.forall_mem_append.2 ⟨sbd13_1_13, sbd13_1_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_1_15, sbd13_1_16⟩, List.forall_mem_append.2 ⟨sbd13_1_17, List.forall_mem_append.2 ⟨sbd13_1_18, sbd13_1_19⟩⟩⟩⟩⟩
theorem en_okd13_1 : subEnum G n Ps d13_1 = true :=
  subEnum_fast ld_okd13_1 (enumS_of_coverL coverd13_1 subsd13_1)
theorem coverd13_2 : (coverL d13_2.aL d13_2.w 6 2 6 (fun _ => 0) (d13_2.S * d13_2.K) [] preLd13_2).isSome = true := by decide +kernel
theorem subsd13_2 : ∀ q ∈ preLd13_2, subd13_2 q = true := by
  unfold preLd13_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_2_0, sbd13_2_1⟩, List.forall_mem_append.2 ⟨sbd13_2_2, List.forall_mem_append.2 ⟨sbd13_2_3, sbd13_2_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_2_5, sbd13_2_6⟩, List.forall_mem_append.2 ⟨sbd13_2_7, List.forall_mem_append.2 ⟨sbd13_2_8, sbd13_2_9⟩⟩⟩⟩
theorem en_okd13_2 : subEnum G n Ps d13_2 = true :=
  subEnum_fast ld_okd13_2 (enumS_of_coverL coverd13_2 subsd13_2)
theorem coverd13_3 : (coverL d13_3.aL d13_3.w 6 2 6 (fun _ => 0) (d13_3.S * d13_3.K) [] preLd13_3).isSome = true := by decide +kernel
theorem subsd13_3 : ∀ q ∈ preLd13_3, subd13_3 q = true := by
  unfold preLd13_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_3_0, sbd13_3_1⟩, List.forall_mem_append.2 ⟨sbd13_3_2, sbd13_3_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_3_4, sbd13_3_5⟩, List.forall_mem_append.2 ⟨sbd13_3_6, sbd13_3_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_3_8, sbd13_3_9⟩, List.forall_mem_append.2 ⟨sbd13_3_10, sbd13_3_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd13_3_12, sbd13_3_13⟩, List.forall_mem_append.2 ⟨sbd13_3_14, List.forall_mem_append.2 ⟨sbd13_3_15, sbd13_3_16⟩⟩⟩⟩⟩
theorem en_okd13_3 : subEnum G n Ps d13_3 = true :=
  subEnum_fast ld_okd13_3 (enumS_of_coverL coverd13_3 subsd13_3)
theorem cov_ok13 : normsCovered normsL [d13_0, d13_1, d13_2, d13_3] = true := by decide +kernel
theorem cell_ok13 : CellOK hd G n Ps normsL cell13 :=
  cellOK_of hd adm (by decide +kernel) cov_ok13 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd13_0, en_okd13_0⟩
    · exact ⟨pre_okd13_1, en_okd13_1⟩
    · exact ⟨pre_okd13_2, en_okd13_2⟩
    · exact ⟨pre_okd13_3, en_okd13_3⟩
  )
theorem coverd14_0 : (coverL d14_0.aL d14_0.w 6 2 6 (fun _ => 0) (d14_0.S * d14_0.K) [] preLd14_0).isSome = true := by decide +kernel
theorem subsd14_0 : ∀ q ∈ preLd14_0, subd14_0 q = true := by
  unfold preLd14_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_0_0, sbd14_0_1⟩, List.forall_mem_append.2 ⟨sbd14_0_2, List.forall_mem_append.2 ⟨sbd14_0_3, sbd14_0_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_0_5, sbd14_0_6⟩, List.forall_mem_append.2 ⟨sbd14_0_7, List.forall_mem_append.2 ⟨sbd14_0_8, sbd14_0_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_0_10, sbd14_0_11⟩, List.forall_mem_append.2 ⟨sbd14_0_12, List.forall_mem_append.2 ⟨sbd14_0_13, sbd14_0_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_0_15, List.forall_mem_append.2 ⟨sbd14_0_16, sbd14_0_17⟩⟩, List.forall_mem_append.2 ⟨sbd14_0_18, List.forall_mem_append.2 ⟨sbd14_0_19, sbd14_0_20⟩⟩⟩⟩⟩
theorem en_okd14_0 : subEnum G n Ps d14_0 = true :=
  subEnum_fast ld_okd14_0 (enumS_of_coverL coverd14_0 subsd14_0)
theorem coverd14_1 : (coverL d14_1.aL d14_1.w 6 2 6 (fun _ => 0) (d14_1.S * d14_1.K) [] preLd14_1).isSome = true := by decide +kernel
theorem subsd14_1 : ∀ q ∈ preLd14_1, subd14_1 q = true := by
  unfold preLd14_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_1_0, sbd14_1_1⟩, List.forall_mem_append.2 ⟨sbd14_1_2, List.forall_mem_append.2 ⟨sbd14_1_3, sbd14_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_1_5, List.forall_mem_append.2 ⟨sbd14_1_6, sbd14_1_7⟩⟩, List.forall_mem_append.2 ⟨sbd14_1_8, List.forall_mem_append.2 ⟨sbd14_1_9, sbd14_1_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_1_11, List.forall_mem_append.2 ⟨sbd14_1_12, sbd14_1_13⟩⟩, List.forall_mem_append.2 ⟨sbd14_1_14, List.forall_mem_append.2 ⟨sbd14_1_15, sbd14_1_16⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_1_17, List.forall_mem_append.2 ⟨sbd14_1_18, sbd14_1_19⟩⟩, List.forall_mem_append.2 ⟨sbd14_1_20, List.forall_mem_append.2 ⟨sbd14_1_21, sbd14_1_22⟩⟩⟩⟩⟩
theorem en_okd14_1 : subEnum G n Ps d14_1 = true :=
  subEnum_fast ld_okd14_1 (enumS_of_coverL coverd14_1 subsd14_1)
theorem coverd14_2 : (coverL d14_2.aL d14_2.w 6 2 6 (fun _ => 0) (d14_2.S * d14_2.K) [] preLd14_2).isSome = true := by decide +kernel
theorem subsd14_2 : ∀ q ∈ preLd14_2, subd14_2 q = true := by
  unfold preLd14_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_2_0, List.forall_mem_append.2 ⟨sbd14_2_1, sbd14_2_2⟩⟩, List.forall_mem_append.2 ⟨sbd14_2_3, List.forall_mem_append.2 ⟨sbd14_2_4, sbd14_2_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_2_6, List.forall_mem_append.2 ⟨sbd14_2_7, sbd14_2_8⟩⟩, List.forall_mem_append.2 ⟨sbd14_2_9, List.forall_mem_append.2 ⟨sbd14_2_10, sbd14_2_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_2_12, List.forall_mem_append.2 ⟨sbd14_2_13, sbd14_2_14⟩⟩, List.forall_mem_append.2 ⟨sbd14_2_15, List.forall_mem_append.2 ⟨sbd14_2_16, sbd14_2_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_2_18, List.forall_mem_append.2 ⟨sbd14_2_19, sbd14_2_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_2_21, sbd14_2_22⟩, List.forall_mem_append.2 ⟨sbd14_2_23, sbd14_2_24⟩⟩⟩⟩⟩
theorem en_okd14_2 : subEnum G n Ps d14_2 = true :=
  subEnum_fast ld_okd14_2 (enumS_of_coverL coverd14_2 subsd14_2)
theorem coverd14_3 : (coverL d14_3.aL d14_3.w 6 2 6 (fun _ => 0) (d14_3.S * d14_3.K) [] preLd14_3).isSome = true := by decide +kernel
theorem subsd14_3 : ∀ q ∈ preLd14_3, subd14_3 q = true := by
  unfold preLd14_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_0, sbd14_3_1⟩, List.forall_mem_append.2 ⟨sbd14_3_2, sbd14_3_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_4, sbd14_3_5⟩, List.forall_mem_append.2 ⟨sbd14_3_6, sbd14_3_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_8, sbd14_3_9⟩, List.forall_mem_append.2 ⟨sbd14_3_10, sbd14_3_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_12, sbd14_3_13⟩, List.forall_mem_append.2 ⟨sbd14_3_14, List.forall_mem_append.2 ⟨sbd14_3_15, sbd14_3_16⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_17, sbd14_3_18⟩, List.forall_mem_append.2 ⟨sbd14_3_19, sbd14_3_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_21, sbd14_3_22⟩, List.forall_mem_append.2 ⟨sbd14_3_23, List.forall_mem_append.2 ⟨sbd14_3_24, sbd14_3_25⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_26, sbd14_3_27⟩, List.forall_mem_append.2 ⟨sbd14_3_28, sbd14_3_29⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd14_3_30, sbd14_3_31⟩, List.forall_mem_append.2 ⟨sbd14_3_32, List.forall_mem_append.2 ⟨sbd14_3_33, sbd14_3_34⟩⟩⟩⟩⟩⟩
theorem en_okd14_3 : subEnum G n Ps d14_3 = true :=
  subEnum_fast ld_okd14_3 (enumS_of_coverL coverd14_3 subsd14_3)
theorem cov_ok14 : normsCovered normsL [d14_0, d14_1, d14_2, d14_3] = true := by decide +kernel
theorem cell_ok14 : CellOK hd G n Ps normsL cell14 :=
  cellOK_of hd adm (by decide +kernel) cov_ok14 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd14_0, en_okd14_0⟩
    · exact ⟨pre_okd14_1, en_okd14_1⟩
    · exact ⟨pre_okd14_2, en_okd14_2⟩
    · exact ⟨pre_okd14_3, en_okd14_3⟩
  )
theorem coverd15_0 : (coverL d15_0.aL d15_0.w 6 2 6 (fun _ => 0) (d15_0.S * d15_0.K) [] preLd15_0).isSome = true := by decide +kernel
theorem subsd15_0 : ∀ q ∈ preLd15_0, subd15_0 q = true := by
  unfold preLd15_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_0_0, List.forall_mem_append.2 ⟨sbd15_0_1, sbd15_0_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_0_3, sbd15_0_4⟩, List.forall_mem_append.2 ⟨sbd15_0_5, sbd15_0_6⟩⟩⟩
theorem en_okd15_0 : subEnum G n Ps d15_0 = true :=
  subEnum_fast ld_okd15_0 (enumS_of_coverL coverd15_0 subsd15_0)
theorem coverd15_1 : (coverL d15_1.aL d15_1.w 6 2 6 (fun _ => 0) (d15_1.S * d15_1.K) [] preLd15_1).isSome = true := by decide +kernel
theorem subsd15_1 : ∀ q ∈ preLd15_1, subd15_1 q = true := by
  unfold preLd15_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_1_0, List.forall_mem_append.2 ⟨sbd15_1_1, sbd15_1_2⟩⟩, List.forall_mem_append.2 ⟨sbd15_1_3, List.forall_mem_append.2 ⟨sbd15_1_4, sbd15_1_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_1_6, List.forall_mem_append.2 ⟨sbd15_1_7, sbd15_1_8⟩⟩, List.forall_mem_append.2 ⟨sbd15_1_9, List.forall_mem_append.2 ⟨sbd15_1_10, sbd15_1_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_1_12, List.forall_mem_append.2 ⟨sbd15_1_13, sbd15_1_14⟩⟩, List.forall_mem_append.2 ⟨sbd15_1_15, List.forall_mem_append.2 ⟨sbd15_1_16, sbd15_1_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_1_18, List.forall_mem_append.2 ⟨sbd15_1_19, sbd15_1_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_1_21, sbd15_1_22⟩, List.forall_mem_append.2 ⟨sbd15_1_23, sbd15_1_24⟩⟩⟩⟩⟩
theorem en_okd15_1 : subEnum G n Ps d15_1 = true :=
  subEnum_fast ld_okd15_1 (enumS_of_coverL coverd15_1 subsd15_1)
theorem coverd15_2 : (coverL d15_2.aL d15_2.w 6 2 6 (fun _ => 0) (d15_2.S * d15_2.K) [] preLd15_2).isSome = true := by decide +kernel
theorem subsd15_2 : ∀ q ∈ preLd15_2, subd15_2 q = true := by
  unfold preLd15_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_2_0, sbd15_2_1⟩, List.forall_mem_append.2 ⟨sbd15_2_2, List.forall_mem_append.2 ⟨sbd15_2_3, sbd15_2_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_2_5, sbd15_2_6⟩, List.forall_mem_append.2 ⟨sbd15_2_7, List.forall_mem_append.2 ⟨sbd15_2_8, sbd15_2_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_2_10, sbd15_2_11⟩, List.forall_mem_append.2 ⟨sbd15_2_12, List.forall_mem_append.2 ⟨sbd15_2_13, sbd15_2_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_2_15, List.forall_mem_append.2 ⟨sbd15_2_16, sbd15_2_17⟩⟩, List.forall_mem_append.2 ⟨sbd15_2_18, List.forall_mem_append.2 ⟨sbd15_2_19, sbd15_2_20⟩⟩⟩⟩⟩
theorem en_okd15_2 : subEnum G n Ps d15_2 = true :=
  subEnum_fast ld_okd15_2 (enumS_of_coverL coverd15_2 subsd15_2)
theorem coverd15_3 : (coverL d15_3.aL d15_3.w 6 2 6 (fun _ => 0) (d15_3.S * d15_3.K) [] preLd15_3).isSome = true := by decide +kernel
theorem subsd15_3 : ∀ q ∈ preLd15_3, subd15_3 q = true := by
  unfold preLd15_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_3_0, List.forall_mem_append.2 ⟨sbd15_3_1, sbd15_3_2⟩⟩, List.forall_mem_append.2 ⟨sbd15_3_3, List.forall_mem_append.2 ⟨sbd15_3_4, sbd15_3_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_3_6, List.forall_mem_append.2 ⟨sbd15_3_7, sbd15_3_8⟩⟩, List.forall_mem_append.2 ⟨sbd15_3_9, List.forall_mem_append.2 ⟨sbd15_3_10, sbd15_3_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_3_12, List.forall_mem_append.2 ⟨sbd15_3_13, sbd15_3_14⟩⟩, List.forall_mem_append.2 ⟨sbd15_3_15, List.forall_mem_append.2 ⟨sbd15_3_16, sbd15_3_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_3_18, List.forall_mem_append.2 ⟨sbd15_3_19, sbd15_3_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd15_3_21, sbd15_3_22⟩, List.forall_mem_append.2 ⟨sbd15_3_23, sbd15_3_24⟩⟩⟩⟩⟩
theorem en_okd15_3 : subEnum G n Ps d15_3 = true :=
  subEnum_fast ld_okd15_3 (enumS_of_coverL coverd15_3 subsd15_3)
theorem cov_ok15 : normsCovered normsL [d15_0, d15_1, d15_2, d15_3] = true := by decide +kernel
theorem cell_ok15 : CellOK hd G n Ps normsL cell15 :=
  cellOK_of hd adm (by decide +kernel) cov_ok15 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd15_0, en_okd15_0⟩
    · exact ⟨pre_okd15_1, en_okd15_1⟩
    · exact ⟨pre_okd15_2, en_okd15_2⟩
    · exact ⟨pre_okd15_3, en_okd15_3⟩
  )
theorem coverd16_0 : (coverL d16_0.aL d16_0.w 6 2 6 (fun _ => 0) (d16_0.S * d16_0.K) [] preLd16_0).isSome = true := by decide +kernel
theorem subsd16_0 : ∀ q ∈ preLd16_0, subd16_0 q = true := by
  unfold preLd16_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_0_0, sbd16_0_1⟩, List.forall_mem_append.2 ⟨sbd16_0_2, sbd16_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_0_4, sbd16_0_5⟩, List.forall_mem_append.2 ⟨sbd16_0_6, sbd16_0_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_0_8, sbd16_0_9⟩, List.forall_mem_append.2 ⟨sbd16_0_10, sbd16_0_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_0_12, sbd16_0_13⟩, List.forall_mem_append.2 ⟨sbd16_0_14, List.forall_mem_append.2 ⟨sbd16_0_15, sbd16_0_16⟩⟩⟩⟩⟩
theorem en_okd16_0 : subEnum G n Ps d16_0 = true :=
  subEnum_fast ld_okd16_0 (enumS_of_coverL coverd16_0 subsd16_0)
theorem coverd16_1 : (coverL d16_1.aL d16_1.w 6 2 6 (fun _ => 0) (d16_1.S * d16_1.K) [] preLd16_1).isSome = true := by decide +kernel
theorem subsd16_1 : ∀ q ∈ preLd16_1, subd16_1 q = true := by
  unfold preLd16_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_1_0, List.forall_mem_append.2 ⟨sbd16_1_1, sbd16_1_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_1_3, sbd16_1_4⟩, List.forall_mem_append.2 ⟨sbd16_1_5, sbd16_1_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_1_7, List.forall_mem_append.2 ⟨sbd16_1_8, sbd16_1_9⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_1_10, sbd16_1_11⟩, List.forall_mem_append.2 ⟨sbd16_1_12, sbd16_1_13⟩⟩⟩⟩
theorem en_okd16_1 : subEnum G n Ps d16_1 = true :=
  subEnum_fast ld_okd16_1 (enumS_of_coverL coverd16_1 subsd16_1)
theorem coverd16_2 : (coverL d16_2.aL d16_2.w 6 2 6 (fun _ => 0) (d16_2.S * d16_2.K) [] preLd16_2).isSome = true := by decide +kernel
theorem subsd16_2 : ∀ q ∈ preLd16_2, subd16_2 q = true := by
  unfold preLd16_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_2_0, sbd16_2_1⟩, List.forall_mem_append.2 ⟨sbd16_2_2, List.forall_mem_append.2 ⟨sbd16_2_3, sbd16_2_4⟩⟩⟩
theorem en_okd16_2 : subEnum G n Ps d16_2 = true :=
  subEnum_fast ld_okd16_2 (enumS_of_coverL coverd16_2 subsd16_2)
theorem coverd16_3 : (coverL d16_3.aL d16_3.w 6 2 6 (fun _ => 0) (d16_3.S * d16_3.K) [] preLd16_3).isSome = true := by decide +kernel
theorem subsd16_3 : ∀ q ∈ preLd16_3, subd16_3 q = true := by
  unfold preLd16_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_3_0, sbd16_3_1⟩, List.forall_mem_append.2 ⟨sbd16_3_2, List.forall_mem_append.2 ⟨sbd16_3_3, sbd16_3_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_3_5, List.forall_mem_append.2 ⟨sbd16_3_6, sbd16_3_7⟩⟩, List.forall_mem_append.2 ⟨sbd16_3_8, List.forall_mem_append.2 ⟨sbd16_3_9, sbd16_3_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_3_11, List.forall_mem_append.2 ⟨sbd16_3_12, sbd16_3_13⟩⟩, List.forall_mem_append.2 ⟨sbd16_3_14, List.forall_mem_append.2 ⟨sbd16_3_15, sbd16_3_16⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd16_3_17, List.forall_mem_append.2 ⟨sbd16_3_18, sbd16_3_19⟩⟩, List.forall_mem_append.2 ⟨sbd16_3_20, List.forall_mem_append.2 ⟨sbd16_3_21, sbd16_3_22⟩⟩⟩⟩⟩
theorem en_okd16_3 : subEnum G n Ps d16_3 = true :=
  subEnum_fast ld_okd16_3 (enumS_of_coverL coverd16_3 subsd16_3)
theorem cov_ok16 : normsCovered normsL [d16_0, d16_1, d16_2, d16_3] = true := by decide +kernel
theorem cell_ok16 : CellOK hd G n Ps normsL cell16 :=
  cellOK_of hd adm (by decide +kernel) cov_ok16 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd16_0, en_okd16_0⟩
    · exact ⟨pre_okd16_1, en_okd16_1⟩
    · exact ⟨pre_okd16_2, en_okd16_2⟩
    · exact ⟨pre_okd16_3, en_okd16_3⟩
  )
theorem coverd17_0 : (coverL d17_0.aL d17_0.w 6 2 6 (fun _ => 0) (d17_0.S * d17_0.K) [] preLd17_0).isSome = true := by decide +kernel
theorem subsd17_0 : ∀ q ∈ preLd17_0, subd17_0 q = true := by
  unfold preLd17_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_0_0, sbd17_0_1⟩, List.forall_mem_append.2 ⟨sbd17_0_2, List.forall_mem_append.2 ⟨sbd17_0_3, sbd17_0_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_0_5, sbd17_0_6⟩, List.forall_mem_append.2 ⟨sbd17_0_7, List.forall_mem_append.2 ⟨sbd17_0_8, sbd17_0_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_0_10, sbd17_0_11⟩, List.forall_mem_append.2 ⟨sbd17_0_12, List.forall_mem_append.2 ⟨sbd17_0_13, sbd17_0_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_0_15, List.forall_mem_append.2 ⟨sbd17_0_16, sbd17_0_17⟩⟩, List.forall_mem_append.2 ⟨sbd17_0_18, List.forall_mem_append.2 ⟨sbd17_0_19, sbd17_0_20⟩⟩⟩⟩⟩
theorem en_okd17_0 : subEnum G n Ps d17_0 = true :=
  subEnum_fast ld_okd17_0 (enumS_of_coverL coverd17_0 subsd17_0)
theorem coverd17_1 : (coverL d17_1.aL d17_1.w 6 2 6 (fun _ => 0) (d17_1.S * d17_1.K) [] preLd17_1).isSome = true := by decide +kernel
theorem subsd17_1 : ∀ q ∈ preLd17_1, subd17_1 q = true := by
  unfold preLd17_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_0, sbd17_1_1⟩, List.forall_mem_append.2 ⟨sbd17_1_2, sbd17_1_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_4, sbd17_1_5⟩, List.forall_mem_append.2 ⟨sbd17_1_6, List.forall_mem_append.2 ⟨sbd17_1_7, sbd17_1_8⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_9, sbd17_1_10⟩, List.forall_mem_append.2 ⟨sbd17_1_11, List.forall_mem_append.2 ⟨sbd17_1_12, sbd17_1_13⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_14, sbd17_1_15⟩, List.forall_mem_append.2 ⟨sbd17_1_16, List.forall_mem_append.2 ⟨sbd17_1_17, sbd17_1_18⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_19, sbd17_1_20⟩, List.forall_mem_append.2 ⟨sbd17_1_21, List.forall_mem_append.2 ⟨sbd17_1_22, sbd17_1_23⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_24, sbd17_1_25⟩, List.forall_mem_append.2 ⟨sbd17_1_26, List.forall_mem_append.2 ⟨sbd17_1_27, sbd17_1_28⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_29, sbd17_1_30⟩, List.forall_mem_append.2 ⟨sbd17_1_31, List.forall_mem_append.2 ⟨sbd17_1_32, sbd17_1_33⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_1_34, sbd17_1_35⟩, List.forall_mem_append.2 ⟨sbd17_1_36, List.forall_mem_append.2 ⟨sbd17_1_37, sbd17_1_38⟩⟩⟩⟩⟩⟩
theorem en_okd17_1 : subEnum G n Ps d17_1 = true :=
  subEnum_fast ld_okd17_1 (enumS_of_coverL coverd17_1 subsd17_1)
theorem coverd17_2 : (coverL d17_2.aL d17_2.w 6 2 6 (fun _ => 0) (d17_2.S * d17_2.K) [] preLd17_2).isSome = true := by decide +kernel
theorem subsd17_2 : ∀ q ∈ preLd17_2, subd17_2 q = true := by
  unfold preLd17_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_0, List.forall_mem_append.2 ⟨sbd17_2_1, sbd17_2_2⟩⟩, List.forall_mem_append.2 ⟨sbd17_2_3, List.forall_mem_append.2 ⟨sbd17_2_4, sbd17_2_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_6, List.forall_mem_append.2 ⟨sbd17_2_7, sbd17_2_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_9, sbd17_2_10⟩, List.forall_mem_append.2 ⟨sbd17_2_11, sbd17_2_12⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_13, List.forall_mem_append.2 ⟨sbd17_2_14, sbd17_2_15⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_16, sbd17_2_17⟩, List.forall_mem_append.2 ⟨sbd17_2_18, sbd17_2_19⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_20, List.forall_mem_append.2 ⟨sbd17_2_21, sbd17_2_22⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_2_23, sbd17_2_24⟩, List.forall_mem_append.2 ⟨sbd17_2_25, sbd17_2_26⟩⟩⟩⟩⟩
theorem en_okd17_2 : subEnum G n Ps d17_2 = true :=
  subEnum_fast ld_okd17_2 (enumS_of_coverL coverd17_2 subsd17_2)
theorem coverd17_3 : (coverL d17_3.aL d17_3.w 6 2 6 (fun _ => 0) (d17_3.S * d17_3.K) [] preLd17_3).isSome = true := by decide +kernel
theorem subsd17_3 : ∀ q ∈ preLd17_3, subd17_3 q = true := by
  unfold preLd17_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_0, sbd17_3_1⟩, List.forall_mem_append.2 ⟨sbd17_3_2, sbd17_3_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_4, sbd17_3_5⟩, List.forall_mem_append.2 ⟨sbd17_3_6, List.forall_mem_append.2 ⟨sbd17_3_7, sbd17_3_8⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_9, sbd17_3_10⟩, List.forall_mem_append.2 ⟨sbd17_3_11, List.forall_mem_append.2 ⟨sbd17_3_12, sbd17_3_13⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_14, sbd17_3_15⟩, List.forall_mem_append.2 ⟨sbd17_3_16, List.forall_mem_append.2 ⟨sbd17_3_17, sbd17_3_18⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_19, sbd17_3_20⟩, List.forall_mem_append.2 ⟨sbd17_3_21, List.forall_mem_append.2 ⟨sbd17_3_22, sbd17_3_23⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_24, sbd17_3_25⟩, List.forall_mem_append.2 ⟨sbd17_3_26, List.forall_mem_append.2 ⟨sbd17_3_27, sbd17_3_28⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_29, sbd17_3_30⟩, List.forall_mem_append.2 ⟨sbd17_3_31, List.forall_mem_append.2 ⟨sbd17_3_32, sbd17_3_33⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd17_3_34, sbd17_3_35⟩, List.forall_mem_append.2 ⟨sbd17_3_36, List.forall_mem_append.2 ⟨sbd17_3_37, sbd17_3_38⟩⟩⟩⟩⟩⟩
theorem en_okd17_3 : subEnum G n Ps d17_3 = true :=
  subEnum_fast ld_okd17_3 (enumS_of_coverL coverd17_3 subsd17_3)
theorem cov_ok17 : normsCovered normsL [d17_0, d17_1, d17_2, d17_3] = true := by decide +kernel
theorem cell_ok17 : CellOK hd G n Ps normsL cell17 :=
  cellOK_of hd adm (by decide +kernel) cov_ok17 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd17_0, en_okd17_0⟩
    · exact ⟨pre_okd17_1, en_okd17_1⟩
    · exact ⟨pre_okd17_2, en_okd17_2⟩
    · exact ⟨pre_okd17_3, en_okd17_3⟩
  )
theorem coverd18_0 : (coverL d18_0.aL d18_0.w 6 2 6 (fun _ => 0) (d18_0.S * d18_0.K) [] preLd18_0).isSome = true := by decide +kernel
theorem subsd18_0 : ∀ q ∈ preLd18_0, subd18_0 q = true := by
  unfold preLd18_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_0_0, sbd18_0_1⟩, List.forall_mem_append.2 ⟨sbd18_0_2, sbd18_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_0_4, sbd18_0_5⟩, List.forall_mem_append.2 ⟨sbd18_0_6, List.forall_mem_append.2 ⟨sbd18_0_7, sbd18_0_8⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_0_9, sbd18_0_10⟩, List.forall_mem_append.2 ⟨sbd18_0_11, List.forall_mem_append.2 ⟨sbd18_0_12, sbd18_0_13⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_0_14, sbd18_0_15⟩, List.forall_mem_append.2 ⟨sbd18_0_16, List.forall_mem_append.2 ⟨sbd18_0_17, sbd18_0_18⟩⟩⟩⟩⟩
theorem en_okd18_0 : subEnum G n Ps d18_0 = true :=
  subEnum_fast ld_okd18_0 (enumS_of_coverL coverd18_0 subsd18_0)
theorem coverd18_1 : (coverL d18_1.aL d18_1.w 6 2 6 (fun _ => 0) (d18_1.S * d18_1.K) [] preLd18_1).isSome = true := by decide +kernel
theorem subsd18_1 : ∀ q ∈ preLd18_1, subd18_1 q = true := by
  unfold preLd18_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_0, List.forall_mem_append.2 ⟨sbd18_1_1, sbd18_1_2⟩⟩, List.forall_mem_append.2 ⟨sbd18_1_3, List.forall_mem_append.2 ⟨sbd18_1_4, sbd18_1_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_6, List.forall_mem_append.2 ⟨sbd18_1_7, sbd18_1_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_9, sbd18_1_10⟩, List.forall_mem_append.2 ⟨sbd18_1_11, sbd18_1_12⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_13, List.forall_mem_append.2 ⟨sbd18_1_14, sbd18_1_15⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_16, sbd18_1_17⟩, List.forall_mem_append.2 ⟨sbd18_1_18, sbd18_1_19⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_20, List.forall_mem_append.2 ⟨sbd18_1_21, sbd18_1_22⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_1_23, sbd18_1_24⟩, List.forall_mem_append.2 ⟨sbd18_1_25, sbd18_1_26⟩⟩⟩⟩⟩
theorem en_okd18_1 : subEnum G n Ps d18_1 = true :=
  subEnum_fast ld_okd18_1 (enumS_of_coverL coverd18_1 subsd18_1)
theorem coverd18_2 : (coverL d18_2.aL d18_2.w 6 2 6 (fun _ => 0) (d18_2.S * d18_2.K) [] preLd18_2).isSome = true := by decide +kernel
theorem subsd18_2 : ∀ q ∈ preLd18_2, subd18_2 q = true := by
  unfold preLd18_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_2_0, sbd18_2_1⟩, List.forall_mem_append.2 ⟨sbd18_2_2, sbd18_2_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_2_4, sbd18_2_5⟩, List.forall_mem_append.2 ⟨sbd18_2_6, sbd18_2_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_2_8, sbd18_2_9⟩, List.forall_mem_append.2 ⟨sbd18_2_10, sbd18_2_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_2_12, sbd18_2_13⟩, List.forall_mem_append.2 ⟨sbd18_2_14, List.forall_mem_append.2 ⟨sbd18_2_15, sbd18_2_16⟩⟩⟩⟩⟩
theorem en_okd18_2 : subEnum G n Ps d18_2 = true :=
  subEnum_fast ld_okd18_2 (enumS_of_coverL coverd18_2 subsd18_2)
theorem coverd18_3 : (coverL d18_3.aL d18_3.w 6 2 6 (fun _ => 0) (d18_3.S * d18_3.K) [] preLd18_3).isSome = true := by decide +kernel
theorem subsd18_3 : ∀ q ∈ preLd18_3, subd18_3 q = true := by
  unfold preLd18_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_3_0, sbd18_3_1⟩, List.forall_mem_append.2 ⟨sbd18_3_2, sbd18_3_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_3_4, sbd18_3_5⟩, List.forall_mem_append.2 ⟨sbd18_3_6, sbd18_3_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_3_8, sbd18_3_9⟩, List.forall_mem_append.2 ⟨sbd18_3_10, sbd18_3_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd18_3_12, sbd18_3_13⟩, List.forall_mem_append.2 ⟨sbd18_3_14, List.forall_mem_append.2 ⟨sbd18_3_15, sbd18_3_16⟩⟩⟩⟩⟩
theorem en_okd18_3 : subEnum G n Ps d18_3 = true :=
  subEnum_fast ld_okd18_3 (enumS_of_coverL coverd18_3 subsd18_3)
theorem cov_ok18 : normsCovered normsL [d18_0, d18_1, d18_2, d18_3] = true := by decide +kernel
theorem cell_ok18 : CellOK hd G n Ps normsL cell18 :=
  cellOK_of hd adm (by decide +kernel) cov_ok18 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd18_0, en_okd18_0⟩
    · exact ⟨pre_okd18_1, en_okd18_1⟩
    · exact ⟨pre_okd18_2, en_okd18_2⟩
    · exact ⟨pre_okd18_3, en_okd18_3⟩
  )
theorem coverd19_0 : (coverL d19_0.aL d19_0.w 6 2 6 (fun _ => 0) (d19_0.S * d19_0.K) [] preLd19_0).isSome = true := by decide +kernel
theorem subsd19_0 : ∀ q ∈ preLd19_0, subd19_0 q = true := by
  unfold preLd19_0
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_0, sbd19_0_1⟩, List.forall_mem_append.2 ⟨sbd19_0_2, sbd19_0_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_4, sbd19_0_5⟩, List.forall_mem_append.2 ⟨sbd19_0_6, sbd19_0_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_8, sbd19_0_9⟩, List.forall_mem_append.2 ⟨sbd19_0_10, sbd19_0_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_12, sbd19_0_13⟩, List.forall_mem_append.2 ⟨sbd19_0_14, List.forall_mem_append.2 ⟨sbd19_0_15, sbd19_0_16⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_17, sbd19_0_18⟩, List.forall_mem_append.2 ⟨sbd19_0_19, sbd19_0_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_21, sbd19_0_22⟩, List.forall_mem_append.2 ⟨sbd19_0_23, sbd19_0_24⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_25, sbd19_0_26⟩, List.forall_mem_append.2 ⟨sbd19_0_27, sbd19_0_28⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_0_29, sbd19_0_30⟩, List.forall_mem_append.2 ⟨sbd19_0_31, List.forall_mem_append.2 ⟨sbd19_0_32, sbd19_0_33⟩⟩⟩⟩⟩⟩
theorem en_okd19_0 : subEnum G n Ps d19_0 = true :=
  subEnum_fast ld_okd19_0 (enumS_of_coverL coverd19_0 subsd19_0)
theorem coverd19_1 : (coverL d19_1.aL d19_1.w 6 2 6 (fun _ => 0) (d19_1.S * d19_1.K) [] preLd19_1).isSome = true := by decide +kernel
theorem subsd19_1 : ∀ q ∈ preLd19_1, subd19_1 q = true := by
  unfold preLd19_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_0, sbd19_1_1⟩, List.forall_mem_append.2 ⟨sbd19_1_2, List.forall_mem_append.2 ⟨sbd19_1_3, sbd19_1_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_5, List.forall_mem_append.2 ⟨sbd19_1_6, sbd19_1_7⟩⟩, List.forall_mem_append.2 ⟨sbd19_1_8, List.forall_mem_append.2 ⟨sbd19_1_9, sbd19_1_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_11, sbd19_1_12⟩, List.forall_mem_append.2 ⟨sbd19_1_13, List.forall_mem_append.2 ⟨sbd19_1_14, sbd19_1_15⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_16, List.forall_mem_append.2 ⟨sbd19_1_17, sbd19_1_18⟩⟩, List.forall_mem_append.2 ⟨sbd19_1_19, List.forall_mem_append.2 ⟨sbd19_1_20, sbd19_1_21⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_22, sbd19_1_23⟩, List.forall_mem_append.2 ⟨sbd19_1_24, List.forall_mem_append.2 ⟨sbd19_1_25, sbd19_1_26⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_27, List.forall_mem_append.2 ⟨sbd19_1_28, sbd19_1_29⟩⟩, List.forall_mem_append.2 ⟨sbd19_1_30, List.forall_mem_append.2 ⟨sbd19_1_31, sbd19_1_32⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_33, sbd19_1_34⟩, List.forall_mem_append.2 ⟨sbd19_1_35, List.forall_mem_append.2 ⟨sbd19_1_36, sbd19_1_37⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_1_38, List.forall_mem_append.2 ⟨sbd19_1_39, sbd19_1_40⟩⟩, List.forall_mem_append.2 ⟨sbd19_1_41, List.forall_mem_append.2 ⟨sbd19_1_42, sbd19_1_43⟩⟩⟩⟩⟩⟩
theorem en_okd19_1 : subEnum G n Ps d19_1 = true :=
  subEnum_fast ld_okd19_1 (enumS_of_coverL coverd19_1 subsd19_1)
theorem coverd19_2 : (coverL d19_2.aL d19_2.w 6 2 6 (fun _ => 0) (d19_2.S * d19_2.K) [] preLd19_2).isSome = true := by decide +kernel
theorem subsd19_2 : ∀ q ∈ preLd19_2, subd19_2 q = true := by
  unfold preLd19_2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_0, sbd19_2_1⟩, List.forall_mem_append.2 ⟨sbd19_2_2, sbd19_2_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_4, sbd19_2_5⟩, List.forall_mem_append.2 ⟨sbd19_2_6, sbd19_2_7⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_8, sbd19_2_9⟩, List.forall_mem_append.2 ⟨sbd19_2_10, sbd19_2_11⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_12, sbd19_2_13⟩, List.forall_mem_append.2 ⟨sbd19_2_14, List.forall_mem_append.2 ⟨sbd19_2_15, sbd19_2_16⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_17, sbd19_2_18⟩, List.forall_mem_append.2 ⟨sbd19_2_19, sbd19_2_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_21, sbd19_2_22⟩, List.forall_mem_append.2 ⟨sbd19_2_23, sbd19_2_24⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_25, sbd19_2_26⟩, List.forall_mem_append.2 ⟨sbd19_2_27, sbd19_2_28⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_2_29, sbd19_2_30⟩, List.forall_mem_append.2 ⟨sbd19_2_31, List.forall_mem_append.2 ⟨sbd19_2_32, sbd19_2_33⟩⟩⟩⟩⟩⟩
theorem en_okd19_2 : subEnum G n Ps d19_2 = true :=
  subEnum_fast ld_okd19_2 (enumS_of_coverL coverd19_2 subsd19_2)
theorem coverd19_3 : (coverL d19_3.aL d19_3.w 6 2 6 (fun _ => 0) (d19_3.S * d19_3.K) [] preLd19_3).isSome = true := by decide +kernel
theorem subsd19_3 : ∀ q ∈ preLd19_3, subd19_3 q = true := by
  unfold preLd19_3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_0, List.forall_mem_append.2 ⟨sbd19_3_1, sbd19_3_2⟩⟩, List.forall_mem_append.2 ⟨sbd19_3_3, List.forall_mem_append.2 ⟨sbd19_3_4, sbd19_3_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_6, List.forall_mem_append.2 ⟨sbd19_3_7, sbd19_3_8⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_9, sbd19_3_10⟩, List.forall_mem_append.2 ⟨sbd19_3_11, sbd19_3_12⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_13, List.forall_mem_append.2 ⟨sbd19_3_14, sbd19_3_15⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_16, sbd19_3_17⟩, List.forall_mem_append.2 ⟨sbd19_3_18, sbd19_3_19⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_20, List.forall_mem_append.2 ⟨sbd19_3_21, sbd19_3_22⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_23, sbd19_3_24⟩, List.forall_mem_append.2 ⟨sbd19_3_25, sbd19_3_26⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_27, List.forall_mem_append.2 ⟨sbd19_3_28, sbd19_3_29⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_30, sbd19_3_31⟩, List.forall_mem_append.2 ⟨sbd19_3_32, sbd19_3_33⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_34, List.forall_mem_append.2 ⟨sbd19_3_35, sbd19_3_36⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_37, sbd19_3_38⟩, List.forall_mem_append.2 ⟨sbd19_3_39, sbd19_3_40⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_41, List.forall_mem_append.2 ⟨sbd19_3_42, sbd19_3_43⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_44, sbd19_3_45⟩, List.forall_mem_append.2 ⟨sbd19_3_46, sbd19_3_47⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_48, List.forall_mem_append.2 ⟨sbd19_3_49, sbd19_3_50⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd19_3_51, sbd19_3_52⟩, List.forall_mem_append.2 ⟨sbd19_3_53, sbd19_3_54⟩⟩⟩⟩⟩⟩
theorem en_okd19_3 : subEnum G n Ps d19_3 = true :=
  subEnum_fast ld_okd19_3 (enumS_of_coverL coverd19_3 subsd19_3)
theorem cov_ok19 : normsCovered normsL [d19_0, d19_1, d19_2, d19_3] = true := by decide +kernel
theorem cell_ok19 : CellOK hd G n Ps normsL cell19 :=
  cellOK_of hd adm (by decide +kernel) cov_ok19 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd19_0, en_okd19_0⟩
    · exact ⟨pre_okd19_1, en_okd19_1⟩
    · exact ⟨pre_okd19_2, en_okd19_2⟩
    · exact ⟨pre_okd19_3, en_okd19_3⟩
  )
theorem coverd20_0 : (coverL d20_0.aL d20_0.w 6 2 6 (fun _ => 0) (d20_0.S * d20_0.K) [] preLd20_0).isSome = true := by decide +kernel
theorem subsd20_0 : ∀ q ∈ preLd20_0, subd20_0 q = true := by
  unfold preLd20_0
  exact List.forall_mem_append.2 ⟨sbd20_0_0, List.forall_mem_append.2 ⟨sbd20_0_1, sbd20_0_2⟩⟩
theorem en_okd20_0 : subEnum G n Ps d20_0 = true :=
  subEnum_fast ld_okd20_0 (enumS_of_coverL coverd20_0 subsd20_0)
theorem coverd20_1 : (coverL d20_1.aL d20_1.w 6 2 6 (fun _ => 0) (d20_1.S * d20_1.K) [] preLd20_1).isSome = true := by decide +kernel
theorem subsd20_1 : ∀ q ∈ preLd20_1, subd20_1 q = true := by
  unfold preLd20_1
  exact List.forall_mem_append.2 ⟨sbd20_1_0, List.forall_mem_append.2 ⟨sbd20_1_1, sbd20_1_2⟩⟩
theorem en_okd20_1 : subEnum G n Ps d20_1 = true :=
  subEnum_fast ld_okd20_1 (enumS_of_coverL coverd20_1 subsd20_1)
theorem coverd20_2 : (coverL d20_2.aL d20_2.w 6 2 6 (fun _ => 0) (d20_2.S * d20_2.K) [] preLd20_2).isSome = true := by decide +kernel
theorem subsd20_2 : ∀ q ∈ preLd20_2, subd20_2 q = true := by
  unfold preLd20_2
  exact List.forall_mem_append.2 ⟨sbd20_2_0, List.forall_mem_append.2 ⟨sbd20_2_1, sbd20_2_2⟩⟩
theorem en_okd20_2 : subEnum G n Ps d20_2 = true :=
  subEnum_fast ld_okd20_2 (enumS_of_coverL coverd20_2 subsd20_2)
theorem coverd20_3 : (coverL d20_3.aL d20_3.w 6 2 6 (fun _ => 0) (d20_3.S * d20_3.K) [] preLd20_3).isSome = true := by decide +kernel
theorem subsd20_3 : ∀ q ∈ preLd20_3, subd20_3 q = true := by
  unfold preLd20_3
  exact List.forall_mem_append.2 ⟨sbd20_3_0, List.forall_mem_append.2 ⟨sbd20_3_1, sbd20_3_2⟩⟩
theorem en_okd20_3 : subEnum G n Ps d20_3 = true :=
  subEnum_fast ld_okd20_3 (enumS_of_coverL coverd20_3 subsd20_3)
theorem cov_ok20 : normsCovered normsL [d20_0, d20_1, d20_2, d20_3] = true := by decide +kernel
theorem cell_ok20 : CellOK hd G n Ps normsL cell20 :=
  cellOK_of hd adm (by decide +kernel) cov_ok20 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd20_0, en_okd20_0⟩
    · exact ⟨pre_okd20_1, en_okd20_1⟩
    · exact ⟨pre_okd20_2, en_okd20_2⟩
    · exact ⟨pre_okd20_3, en_okd20_3⟩
  )
theorem coverd21_0 : (coverL d21_0.aL d21_0.w 6 2 6 (fun _ => 0) (d21_0.S * d21_0.K) [] preLd21_0).isSome = true := by decide +kernel
theorem subsd21_0 : ∀ q ∈ preLd21_0, subd21_0 q = true := by
  unfold preLd21_0
  exact List.forall_mem_append.2 ⟨sbd21_0_0, sbd21_0_1⟩
theorem en_okd21_0 : subEnum G n Ps d21_0 = true :=
  subEnum_fast ld_okd21_0 (enumS_of_coverL coverd21_0 subsd21_0)
theorem coverd21_1 : (coverL d21_1.aL d21_1.w 6 2 6 (fun _ => 0) (d21_1.S * d21_1.K) [] preLd21_1).isSome = true := by decide +kernel
theorem subsd21_1 : ∀ q ∈ preLd21_1, subd21_1 q = true := by
  unfold preLd21_1
  exact List.forall_mem_append.2 ⟨sbd21_1_0, sbd21_1_1⟩
theorem en_okd21_1 : subEnum G n Ps d21_1 = true :=
  subEnum_fast ld_okd21_1 (enumS_of_coverL coverd21_1 subsd21_1)
theorem coverd21_2 : (coverL d21_2.aL d21_2.w 6 2 6 (fun _ => 0) (d21_2.S * d21_2.K) [] preLd21_2).isSome = true := by decide +kernel
theorem subsd21_2 : ∀ q ∈ preLd21_2, subd21_2 q = true := by
  unfold preLd21_2
  exact List.forall_mem_append.2 ⟨sbd21_2_0, sbd21_2_1⟩
theorem en_okd21_2 : subEnum G n Ps d21_2 = true :=
  subEnum_fast ld_okd21_2 (enumS_of_coverL coverd21_2 subsd21_2)
theorem coverd21_3 : (coverL d21_3.aL d21_3.w 6 2 6 (fun _ => 0) (d21_3.S * d21_3.K) [] preLd21_3).isSome = true := by decide +kernel
theorem subsd21_3 : ∀ q ∈ preLd21_3, subd21_3 q = true := by
  unfold preLd21_3
  exact List.forall_mem_append.2 ⟨sbd21_3_0, sbd21_3_1⟩
theorem en_okd21_3 : subEnum G n Ps d21_3 = true :=
  subEnum_fast ld_okd21_3 (enumS_of_coverL coverd21_3 subsd21_3)
theorem cov_ok21 : normsCovered normsL [d21_0, d21_1, d21_2, d21_3] = true := by decide +kernel
theorem cell_ok21 : CellOK hd G n Ps normsL cell21 :=
  cellOK_of hd adm (by decide +kernel) cov_ok21 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd21_0, en_okd21_0⟩
    · exact ⟨pre_okd21_1, en_okd21_1⟩
    · exact ⟨pre_okd21_2, en_okd21_2⟩
    · exact ⟨pre_okd21_3, en_okd21_3⟩
  )
theorem coverd22_0 : (coverL d22_0.aL d22_0.w 6 2 6 (fun _ => 0) (d22_0.S * d22_0.K) [] preLd22_0).isSome = true := by decide +kernel
theorem subsd22_0 : ∀ q ∈ preLd22_0, subd22_0 q = true := by
  unfold preLd22_0
  exact List.forall_mem_append.2 ⟨sbd22_0_0, sbd22_0_1⟩
theorem en_okd22_0 : subEnum G n Ps d22_0 = true :=
  subEnum_fast ld_okd22_0 (enumS_of_coverL coverd22_0 subsd22_0)
theorem coverd22_1 : (coverL d22_1.aL d22_1.w 6 2 6 (fun _ => 0) (d22_1.S * d22_1.K) [] preLd22_1).isSome = true := by decide +kernel
theorem subsd22_1 : ∀ q ∈ preLd22_1, subd22_1 q = true := by
  unfold preLd22_1
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sbd22_1_0, sbd22_1_1⟩, List.forall_mem_append.2 ⟨sbd22_1_2, List.forall_mem_append.2 ⟨sbd22_1_3, sbd22_1_4⟩⟩⟩
theorem en_okd22_1 : subEnum G n Ps d22_1 = true :=
  subEnum_fast ld_okd22_1 (enumS_of_coverL coverd22_1 subsd22_1)
theorem coverd22_2 : (coverL d22_2.aL d22_2.w 6 2 6 (fun _ => 0) (d22_2.S * d22_2.K) [] preLd22_2).isSome = true := by decide +kernel
theorem subsd22_2 : ∀ q ∈ preLd22_2, subd22_2 q = true := by
  unfold preLd22_2
  exact sbd22_2_0
theorem en_okd22_2 : subEnum G n Ps d22_2 = true :=
  subEnum_fast ld_okd22_2 (enumS_of_coverL coverd22_2 subsd22_2)
theorem coverd22_3 : (coverL d22_3.aL d22_3.w 6 2 6 (fun _ => 0) (d22_3.S * d22_3.K) [] preLd22_3).isSome = true := by decide +kernel
theorem subsd22_3 : ∀ q ∈ preLd22_3, subd22_3 q = true := by
  unfold preLd22_3
  exact List.forall_mem_append.2 ⟨sbd22_3_0, sbd22_3_1⟩
theorem en_okd22_3 : subEnum G n Ps d22_3 = true :=
  subEnum_fast ld_okd22_3 (enumS_of_coverL coverd22_3 subsd22_3)
theorem cov_ok22 : normsCovered normsL [d22_0, d22_1, d22_2, d22_3] = true := by decide +kernel
theorem cell_ok22 : CellOK hd G n Ps normsL cell22 :=
  cellOK_of hd adm (by decide +kernel) cov_ok22 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd22_0, en_okd22_0⟩
    · exact ⟨pre_okd22_1, en_okd22_1⟩
    · exact ⟨pre_okd22_2, en_okd22_2⟩
    · exact ⟨pre_okd22_3, en_okd22_3⟩
  )
theorem coverd23_0 : (coverL d23_0.aL d23_0.w 6 2 6 (fun _ => 0) (d23_0.S * d23_0.K) [] preLd23_0).isSome = true := by decide +kernel
theorem subsd23_0 : ∀ q ∈ preLd23_0, subd23_0 q = true := by
  unfold preLd23_0
  exact sbd23_0_0
theorem en_okd23_0 : subEnum G n Ps d23_0 = true :=
  subEnum_fast ld_okd23_0 (enumS_of_coverL coverd23_0 subsd23_0)
theorem coverd23_1 : (coverL d23_1.aL d23_1.w 6 2 6 (fun _ => 0) (d23_1.S * d23_1.K) [] preLd23_1).isSome = true := by decide +kernel
theorem subsd23_1 : ∀ q ∈ preLd23_1, subd23_1 q = true := by
  unfold preLd23_1
  exact sbd23_1_0
theorem en_okd23_1 : subEnum G n Ps d23_1 = true :=
  subEnum_fast ld_okd23_1 (enumS_of_coverL coverd23_1 subsd23_1)
theorem coverd23_2 : (coverL d23_2.aL d23_2.w 6 2 6 (fun _ => 0) (d23_2.S * d23_2.K) [] preLd23_2).isSome = true := by decide +kernel
theorem subsd23_2 : ∀ q ∈ preLd23_2, subd23_2 q = true := by
  unfold preLd23_2
  exact sbd23_2_0
theorem en_okd23_2 : subEnum G n Ps d23_2 = true :=
  subEnum_fast ld_okd23_2 (enumS_of_coverL coverd23_2 subsd23_2)
theorem coverd23_3 : (coverL d23_3.aL d23_3.w 6 2 6 (fun _ => 0) (d23_3.S * d23_3.K) [] preLd23_3).isSome = true := by decide +kernel
theorem subsd23_3 : ∀ q ∈ preLd23_3, subd23_3 q = true := by
  unfold preLd23_3
  exact sbd23_3_0
theorem en_okd23_3 : subEnum G n Ps d23_3 = true :=
  subEnum_fast ld_okd23_3 (enumS_of_coverL coverd23_3 subsd23_3)
theorem cov_ok23 : normsCovered normsL [d23_0, d23_1, d23_2, d23_3] = true := by decide +kernel
theorem cell_ok23 : CellOK hd G n Ps normsL cell23 :=
  cellOK_of hd adm (by decide +kernel) cov_ok23 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd23_0, en_okd23_0⟩
    · exact ⟨pre_okd23_1, en_okd23_1⟩
    · exact ⟨pre_okd23_2, en_okd23_2⟩
    · exact ⟨pre_okd23_3, en_okd23_3⟩
  )
theorem coverd24_0 : (coverL d24_0.aL d24_0.w 6 2 6 (fun _ => 0) (d24_0.S * d24_0.K) [] preLd24_0).isSome = true := by decide +kernel
theorem subsd24_0 : ∀ q ∈ preLd24_0, subd24_0 q = true := by
  unfold preLd24_0
  exact sbd24_0_0
theorem en_okd24_0 : subEnum G n Ps d24_0 = true :=
  subEnum_fast ld_okd24_0 (enumS_of_coverL coverd24_0 subsd24_0)
theorem coverd24_1 : (coverL d24_1.aL d24_1.w 6 2 6 (fun _ => 0) (d24_1.S * d24_1.K) [] preLd24_1).isSome = true := by decide +kernel
theorem subsd24_1 : ∀ q ∈ preLd24_1, subd24_1 q = true := by
  unfold preLd24_1
  exact sbd24_1_0
theorem en_okd24_1 : subEnum G n Ps d24_1 = true :=
  subEnum_fast ld_okd24_1 (enumS_of_coverL coverd24_1 subsd24_1)
theorem coverd24_2 : (coverL d24_2.aL d24_2.w 6 2 6 (fun _ => 0) (d24_2.S * d24_2.K) [] preLd24_2).isSome = true := by decide +kernel
theorem subsd24_2 : ∀ q ∈ preLd24_2, subd24_2 q = true := by
  unfold preLd24_2
  exact sbd24_2_0
theorem en_okd24_2 : subEnum G n Ps d24_2 = true :=
  subEnum_fast ld_okd24_2 (enumS_of_coverL coverd24_2 subsd24_2)
theorem coverd24_3 : (coverL d24_3.aL d24_3.w 6 2 6 (fun _ => 0) (d24_3.S * d24_3.K) [] preLd24_3).isSome = true := by decide +kernel
theorem subsd24_3 : ∀ q ∈ preLd24_3, subd24_3 q = true := by
  unfold preLd24_3
  exact sbd24_3_0
theorem en_okd24_3 : subEnum G n Ps d24_3 = true :=
  subEnum_fast ld_okd24_3 (enumS_of_coverL coverd24_3 subsd24_3)
theorem cov_ok24 : normsCovered normsL [d24_0, d24_1, d24_2, d24_3] = true := by decide +kernel
theorem cell_ok24 : CellOK hd G n Ps normsL cell24 :=
  cellOK_of hd adm (by decide +kernel) cov_ok24 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd24_0, en_okd24_0⟩
    · exact ⟨pre_okd24_1, en_okd24_1⟩
    · exact ⟨pre_okd24_2, en_okd24_2⟩
    · exact ⟨pre_okd24_3, en_okd24_3⟩
  )
theorem coverd25_0 : (coverL d25_0.aL d25_0.w 6 2 6 (fun _ => 0) (d25_0.S * d25_0.K) [] preLd25_0).isSome = true := by decide +kernel
theorem subsd25_0 : ∀ q ∈ preLd25_0, subd25_0 q = true := by
  unfold preLd25_0
  exact sbd25_0_0
theorem en_okd25_0 : subEnum G n Ps d25_0 = true :=
  subEnum_fast ld_okd25_0 (enumS_of_coverL coverd25_0 subsd25_0)
theorem coverd25_1 : (coverL d25_1.aL d25_1.w 6 2 6 (fun _ => 0) (d25_1.S * d25_1.K) [] preLd25_1).isSome = true := by decide +kernel
theorem subsd25_1 : ∀ q ∈ preLd25_1, subd25_1 q = true := by
  unfold preLd25_1
  exact sbd25_1_0
theorem en_okd25_1 : subEnum G n Ps d25_1 = true :=
  subEnum_fast ld_okd25_1 (enumS_of_coverL coverd25_1 subsd25_1)
theorem coverd25_2 : (coverL d25_2.aL d25_2.w 6 2 6 (fun _ => 0) (d25_2.S * d25_2.K) [] preLd25_2).isSome = true := by decide +kernel
theorem subsd25_2 : ∀ q ∈ preLd25_2, subd25_2 q = true := by
  unfold preLd25_2
  exact sbd25_2_0
theorem en_okd25_2 : subEnum G n Ps d25_2 = true :=
  subEnum_fast ld_okd25_2 (enumS_of_coverL coverd25_2 subsd25_2)
theorem coverd25_3 : (coverL d25_3.aL d25_3.w 6 2 6 (fun _ => 0) (d25_3.S * d25_3.K) [] preLd25_3).isSome = true := by decide +kernel
theorem subsd25_3 : ∀ q ∈ preLd25_3, subd25_3 q = true := by
  unfold preLd25_3
  exact sbd25_3_0
theorem en_okd25_3 : subEnum G n Ps d25_3 = true :=
  subEnum_fast ld_okd25_3 (enumS_of_coverL coverd25_3 subsd25_3)
theorem cov_ok25 : normsCovered normsL [d25_0, d25_1, d25_2, d25_3] = true := by decide +kernel
theorem cell_ok25 : CellOK hd G n Ps normsL cell25 :=
  cellOK_of hd adm (by decide +kernel) cov_ok25 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd25_0, en_okd25_0⟩
    · exact ⟨pre_okd25_1, en_okd25_1⟩
    · exact ⟨pre_okd25_2, en_okd25_2⟩
    · exact ⟨pre_okd25_3, en_okd25_3⟩
  )
theorem coverd26_0 : (coverL d26_0.aL d26_0.w 6 2 6 (fun _ => 0) (d26_0.S * d26_0.K) [] preLd26_0).isSome = true := by decide +kernel
theorem subsd26_0 : ∀ q ∈ preLd26_0, subd26_0 q = true := by
  unfold preLd26_0
  exact sbd26_0_0
theorem en_okd26_0 : subEnum G n Ps d26_0 = true :=
  subEnum_fast ld_okd26_0 (enumS_of_coverL coverd26_0 subsd26_0)
theorem coverd26_1 : (coverL d26_1.aL d26_1.w 6 2 6 (fun _ => 0) (d26_1.S * d26_1.K) [] preLd26_1).isSome = true := by decide +kernel
theorem subsd26_1 : ∀ q ∈ preLd26_1, subd26_1 q = true := by
  unfold preLd26_1
  exact List.forall_mem_append.2 ⟨sbd26_1_0, sbd26_1_1⟩
theorem en_okd26_1 : subEnum G n Ps d26_1 = true :=
  subEnum_fast ld_okd26_1 (enumS_of_coverL coverd26_1 subsd26_1)
theorem coverd26_2 : (coverL d26_2.aL d26_2.w 6 2 6 (fun _ => 0) (d26_2.S * d26_2.K) [] preLd26_2).isSome = true := by decide +kernel
theorem subsd26_2 : ∀ q ∈ preLd26_2, subd26_2 q = true := by
  unfold preLd26_2
  exact sbd26_2_0
theorem en_okd26_2 : subEnum G n Ps d26_2 = true :=
  subEnum_fast ld_okd26_2 (enumS_of_coverL coverd26_2 subsd26_2)
theorem coverd26_3 : (coverL d26_3.aL d26_3.w 6 2 6 (fun _ => 0) (d26_3.S * d26_3.K) [] preLd26_3).isSome = true := by decide +kernel
theorem subsd26_3 : ∀ q ∈ preLd26_3, subd26_3 q = true := by
  unfold preLd26_3
  exact sbd26_3_0
theorem en_okd26_3 : subEnum G n Ps d26_3 = true :=
  subEnum_fast ld_okd26_3 (enumS_of_coverL coverd26_3 subsd26_3)
theorem cov_ok26 : normsCovered normsL [d26_0, d26_1, d26_2, d26_3] = true := by decide +kernel
theorem cell_ok26 : CellOK hd G n Ps normsL cell26 :=
  cellOK_of hd adm (by decide +kernel) cov_ok26 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd26_0, en_okd26_0⟩
    · exact ⟨pre_okd26_1, en_okd26_1⟩
    · exact ⟨pre_okd26_2, en_okd26_2⟩
    · exact ⟨pre_okd26_3, en_okd26_3⟩
  )
theorem coverd27_0 : (coverL d27_0.aL d27_0.w 6 2 6 (fun _ => 0) (d27_0.S * d27_0.K) [] preLd27_0).isSome = true := by decide +kernel
theorem subsd27_0 : ∀ q ∈ preLd27_0, subd27_0 q = true := by
  unfold preLd27_0
  exact sbd27_0_0
theorem en_okd27_0 : subEnum G n Ps d27_0 = true :=
  subEnum_fast ld_okd27_0 (enumS_of_coverL coverd27_0 subsd27_0)
theorem coverd27_1 : (coverL d27_1.aL d27_1.w 6 2 6 (fun _ => 0) (d27_1.S * d27_1.K) [] preLd27_1).isSome = true := by decide +kernel
theorem subsd27_1 : ∀ q ∈ preLd27_1, subd27_1 q = true := by
  unfold preLd27_1
  exact sbd27_1_0
theorem en_okd27_1 : subEnum G n Ps d27_1 = true :=
  subEnum_fast ld_okd27_1 (enumS_of_coverL coverd27_1 subsd27_1)
theorem coverd27_2 : (coverL d27_2.aL d27_2.w 6 2 6 (fun _ => 0) (d27_2.S * d27_2.K) [] preLd27_2).isSome = true := by decide +kernel
theorem subsd27_2 : ∀ q ∈ preLd27_2, subd27_2 q = true := by
  unfold preLd27_2
  exact sbd27_2_0
theorem en_okd27_2 : subEnum G n Ps d27_2 = true :=
  subEnum_fast ld_okd27_2 (enumS_of_coverL coverd27_2 subsd27_2)
theorem coverd27_3 : (coverL d27_3.aL d27_3.w 6 2 6 (fun _ => 0) (d27_3.S * d27_3.K) [] preLd27_3).isSome = true := by decide +kernel
theorem subsd27_3 : ∀ q ∈ preLd27_3, subd27_3 q = true := by
  unfold preLd27_3
  exact sbd27_3_0
theorem en_okd27_3 : subEnum G n Ps d27_3 = true :=
  subEnum_fast ld_okd27_3 (enumS_of_coverL coverd27_3 subsd27_3)
theorem cov_ok27 : normsCovered normsL [d27_0, d27_1, d27_2, d27_3] = true := by decide +kernel
theorem cell_ok27 : CellOK hd G n Ps normsL cell27 :=
  cellOK_of hd adm (by decide +kernel) cov_ok27 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd27_0, en_okd27_0⟩
    · exact ⟨pre_okd27_1, en_okd27_1⟩
    · exact ⟨pre_okd27_2, en_okd27_2⟩
    · exact ⟨pre_okd27_3, en_okd27_3⟩
  )
theorem coverd28_0 : (coverL d28_0.aL d28_0.w 6 2 6 (fun _ => 0) (d28_0.S * d28_0.K) [] preLd28_0).isSome = true := by decide +kernel
theorem subsd28_0 : ∀ q ∈ preLd28_0, subd28_0 q = true := by
  unfold preLd28_0
  exact sbd28_0_0
theorem en_okd28_0 : subEnum G n Ps d28_0 = true :=
  subEnum_fast ld_okd28_0 (enumS_of_coverL coverd28_0 subsd28_0)
theorem coverd28_1 : (coverL d28_1.aL d28_1.w 6 2 6 (fun _ => 0) (d28_1.S * d28_1.K) [] preLd28_1).isSome = true := by decide +kernel
theorem subsd28_1 : ∀ q ∈ preLd28_1, subd28_1 q = true := by
  unfold preLd28_1
  exact sbd28_1_0
theorem en_okd28_1 : subEnum G n Ps d28_1 = true :=
  subEnum_fast ld_okd28_1 (enumS_of_coverL coverd28_1 subsd28_1)
theorem coverd28_2 : (coverL d28_2.aL d28_2.w 6 2 6 (fun _ => 0) (d28_2.S * d28_2.K) [] preLd28_2).isSome = true := by decide +kernel
theorem subsd28_2 : ∀ q ∈ preLd28_2, subd28_2 q = true := by
  unfold preLd28_2
  exact sbd28_2_0
theorem en_okd28_2 : subEnum G n Ps d28_2 = true :=
  subEnum_fast ld_okd28_2 (enumS_of_coverL coverd28_2 subsd28_2)
theorem coverd28_3 : (coverL d28_3.aL d28_3.w 6 2 6 (fun _ => 0) (d28_3.S * d28_3.K) [] preLd28_3).isSome = true := by decide +kernel
theorem subsd28_3 : ∀ q ∈ preLd28_3, subd28_3 q = true := by
  unfold preLd28_3
  exact sbd28_3_0
theorem en_okd28_3 : subEnum G n Ps d28_3 = true :=
  subEnum_fast ld_okd28_3 (enumS_of_coverL coverd28_3 subsd28_3)
theorem cov_ok28 : normsCovered normsL [d28_0, d28_1, d28_2, d28_3] = true := by decide +kernel
theorem cell_ok28 : CellOK hd G n Ps normsL cell28 :=
  cellOK_of hd adm (by decide +kernel) cov_ok28 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd28_0, en_okd28_0⟩
    · exact ⟨pre_okd28_1, en_okd28_1⟩
    · exact ⟨pre_okd28_2, en_okd28_2⟩
    · exact ⟨pre_okd28_3, en_okd28_3⟩
  )
theorem coverd29_0 : (coverL d29_0.aL d29_0.w 6 2 6 (fun _ => 0) (d29_0.S * d29_0.K) [] preLd29_0).isSome = true := by decide +kernel
theorem subsd29_0 : ∀ q ∈ preLd29_0, subd29_0 q = true := by
  unfold preLd29_0
  exact sbd29_0_0
theorem en_okd29_0 : subEnum G n Ps d29_0 = true :=
  subEnum_fast ld_okd29_0 (enumS_of_coverL coverd29_0 subsd29_0)
theorem coverd29_1 : (coverL d29_1.aL d29_1.w 6 2 6 (fun _ => 0) (d29_1.S * d29_1.K) [] preLd29_1).isSome = true := by decide +kernel
theorem subsd29_1 : ∀ q ∈ preLd29_1, subd29_1 q = true := by
  unfold preLd29_1
  exact sbd29_1_0
theorem en_okd29_1 : subEnum G n Ps d29_1 = true :=
  subEnum_fast ld_okd29_1 (enumS_of_coverL coverd29_1 subsd29_1)
theorem coverd29_2 : (coverL d29_2.aL d29_2.w 6 2 6 (fun _ => 0) (d29_2.S * d29_2.K) [] preLd29_2).isSome = true := by decide +kernel
theorem subsd29_2 : ∀ q ∈ preLd29_2, subd29_2 q = true := by
  unfold preLd29_2
  exact sbd29_2_0
theorem en_okd29_2 : subEnum G n Ps d29_2 = true :=
  subEnum_fast ld_okd29_2 (enumS_of_coverL coverd29_2 subsd29_2)
theorem coverd29_3 : (coverL d29_3.aL d29_3.w 6 2 6 (fun _ => 0) (d29_3.S * d29_3.K) [] preLd29_3).isSome = true := by decide +kernel
theorem subsd29_3 : ∀ q ∈ preLd29_3, subd29_3 q = true := by
  unfold preLd29_3
  exact sbd29_3_0
theorem en_okd29_3 : subEnum G n Ps d29_3 = true :=
  subEnum_fast ld_okd29_3 (enumS_of_coverL coverd29_3 subsd29_3)
theorem cov_ok29 : normsCovered normsL [d29_0, d29_1, d29_2, d29_3] = true := by decide +kernel
theorem cell_ok29 : CellOK hd G n Ps normsL cell29 :=
  cellOK_of hd adm (by decide +kernel) cov_ok29 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd29_0, en_okd29_0⟩
    · exact ⟨pre_okd29_1, en_okd29_1⟩
    · exact ⟨pre_okd29_2, en_okd29_2⟩
    · exact ⟨pre_okd29_3, en_okd29_3⟩
  )
theorem coverd30_0 : (coverL d30_0.aL d30_0.w 6 2 6 (fun _ => 0) (d30_0.S * d30_0.K) [] preLd30_0).isSome = true := by decide +kernel
theorem subsd30_0 : ∀ q ∈ preLd30_0, subd30_0 q = true := by
  unfold preLd30_0
  exact sbd30_0_0
theorem en_okd30_0 : subEnum G n Ps d30_0 = true :=
  subEnum_fast ld_okd30_0 (enumS_of_coverL coverd30_0 subsd30_0)
theorem coverd30_1 : (coverL d30_1.aL d30_1.w 6 2 6 (fun _ => 0) (d30_1.S * d30_1.K) [] preLd30_1).isSome = true := by decide +kernel
theorem subsd30_1 : ∀ q ∈ preLd30_1, subd30_1 q = true := by
  unfold preLd30_1
  exact sbd30_1_0
theorem en_okd30_1 : subEnum G n Ps d30_1 = true :=
  subEnum_fast ld_okd30_1 (enumS_of_coverL coverd30_1 subsd30_1)
theorem coverd30_2 : (coverL d30_2.aL d30_2.w 6 2 6 (fun _ => 0) (d30_2.S * d30_2.K) [] preLd30_2).isSome = true := by decide +kernel
theorem subsd30_2 : ∀ q ∈ preLd30_2, subd30_2 q = true := by
  unfold preLd30_2
  exact sbd30_2_0
theorem en_okd30_2 : subEnum G n Ps d30_2 = true :=
  subEnum_fast ld_okd30_2 (enumS_of_coverL coverd30_2 subsd30_2)
theorem coverd30_3 : (coverL d30_3.aL d30_3.w 6 2 6 (fun _ => 0) (d30_3.S * d30_3.K) [] preLd30_3).isSome = true := by decide +kernel
theorem subsd30_3 : ∀ q ∈ preLd30_3, subd30_3 q = true := by
  unfold preLd30_3
  exact sbd30_3_0
theorem en_okd30_3 : subEnum G n Ps d30_3 = true :=
  subEnum_fast ld_okd30_3 (enumS_of_coverL coverd30_3 subsd30_3)
theorem cov_ok30 : normsCovered normsL [d30_0, d30_1, d30_2, d30_3] = true := by decide +kernel
theorem cell_ok30 : CellOK hd G n Ps normsL cell30 :=
  cellOK_of hd adm (by decide +kernel) cov_ok30 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd30_0, en_okd30_0⟩
    · exact ⟨pre_okd30_1, en_okd30_1⟩
    · exact ⟨pre_okd30_2, en_okd30_2⟩
    · exact ⟨pre_okd30_3, en_okd30_3⟩
  )
theorem coverd31_0 : (coverL d31_0.aL d31_0.w 6 2 6 (fun _ => 0) (d31_0.S * d31_0.K) [] preLd31_0).isSome = true := by decide +kernel
theorem subsd31_0 : ∀ q ∈ preLd31_0, subd31_0 q = true := by
  unfold preLd31_0
  exact sbd31_0_0
theorem en_okd31_0 : subEnum G n Ps d31_0 = true :=
  subEnum_fast ld_okd31_0 (enumS_of_coverL coverd31_0 subsd31_0)
theorem coverd31_1 : (coverL d31_1.aL d31_1.w 6 2 6 (fun _ => 0) (d31_1.S * d31_1.K) [] preLd31_1).isSome = true := by decide +kernel
theorem subsd31_1 : ∀ q ∈ preLd31_1, subd31_1 q = true := by
  unfold preLd31_1
  exact sbd31_1_0
theorem en_okd31_1 : subEnum G n Ps d31_1 = true :=
  subEnum_fast ld_okd31_1 (enumS_of_coverL coverd31_1 subsd31_1)
theorem coverd31_2 : (coverL d31_2.aL d31_2.w 6 2 6 (fun _ => 0) (d31_2.S * d31_2.K) [] preLd31_2).isSome = true := by decide +kernel
theorem subsd31_2 : ∀ q ∈ preLd31_2, subd31_2 q = true := by
  unfold preLd31_2
  exact sbd31_2_0
theorem en_okd31_2 : subEnum G n Ps d31_2 = true :=
  subEnum_fast ld_okd31_2 (enumS_of_coverL coverd31_2 subsd31_2)
theorem coverd31_3 : (coverL d31_3.aL d31_3.w 6 2 6 (fun _ => 0) (d31_3.S * d31_3.K) [] preLd31_3).isSome = true := by decide +kernel
theorem subsd31_3 : ∀ q ∈ preLd31_3, subd31_3 q = true := by
  unfold preLd31_3
  exact sbd31_3_0
theorem en_okd31_3 : subEnum G n Ps d31_3 = true :=
  subEnum_fast ld_okd31_3 (enumS_of_coverL coverd31_3 subsd31_3)
theorem cov_ok31 : normsCovered normsL [d31_0, d31_1, d31_2, d31_3] = true := by decide +kernel
theorem cell_ok31 : CellOK hd G n Ps normsL cell31 :=
  cellOK_of hd adm (by decide +kernel) cov_ok31 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd31_0, en_okd31_0⟩
    · exact ⟨pre_okd31_1, en_okd31_1⟩
    · exact ⟨pre_okd31_2, en_okd31_2⟩
    · exact ⟨pre_okd31_3, en_okd31_3⟩
  )
theorem coverd32_0 : (coverL d32_0.aL d32_0.w 6 2 6 (fun _ => 0) (d32_0.S * d32_0.K) [] preLd32_0).isSome = true := by decide +kernel
theorem subsd32_0 : ∀ q ∈ preLd32_0, subd32_0 q = true := by
  unfold preLd32_0
  exact sbd32_0_0
theorem en_okd32_0 : subEnum G n Ps d32_0 = true :=
  subEnum_fast ld_okd32_0 (enumS_of_coverL coverd32_0 subsd32_0)
theorem coverd32_1 : (coverL d32_1.aL d32_1.w 6 2 6 (fun _ => 0) (d32_1.S * d32_1.K) [] preLd32_1).isSome = true := by decide +kernel
theorem subsd32_1 : ∀ q ∈ preLd32_1, subd32_1 q = true := by
  unfold preLd32_1
  exact sbd32_1_0
theorem en_okd32_1 : subEnum G n Ps d32_1 = true :=
  subEnum_fast ld_okd32_1 (enumS_of_coverL coverd32_1 subsd32_1)
theorem coverd32_2 : (coverL d32_2.aL d32_2.w 6 2 6 (fun _ => 0) (d32_2.S * d32_2.K) [] preLd32_2).isSome = true := by decide +kernel
theorem subsd32_2 : ∀ q ∈ preLd32_2, subd32_2 q = true := by
  unfold preLd32_2
  exact sbd32_2_0
theorem en_okd32_2 : subEnum G n Ps d32_2 = true :=
  subEnum_fast ld_okd32_2 (enumS_of_coverL coverd32_2 subsd32_2)
theorem coverd32_3 : (coverL d32_3.aL d32_3.w 6 2 6 (fun _ => 0) (d32_3.S * d32_3.K) [] preLd32_3).isSome = true := by decide +kernel
theorem subsd32_3 : ∀ q ∈ preLd32_3, subd32_3 q = true := by
  unfold preLd32_3
  exact sbd32_3_0
theorem en_okd32_3 : subEnum G n Ps d32_3 = true :=
  subEnum_fast ld_okd32_3 (enumS_of_coverL coverd32_3 subsd32_3)
theorem cov_ok32 : normsCovered normsL [d32_0, d32_1, d32_2, d32_3] = true := by decide +kernel
theorem cell_ok32 : CellOK hd G n Ps normsL cell32 :=
  cellOK_of hd adm (by decide +kernel) cov_ok32 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨pre_okd32_0, en_okd32_0⟩
    · exact ⟨pre_okd32_1, en_okd32_1⟩
    · exact ⟨pre_okd32_2, en_okd32_2⟩
    · exact ⟨pre_okd32_3, en_okd32_3⟩
  )

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8, cell_ok9, cell_ok10, cell_ok11, cell_ok12, cell_ok13, cell_ok14, cell_ok15, cell_ok16, cell_ok17, cell_ok18, cell_ok19, cell_ok20, cell_ok21, cell_ok22, cell_ok23, cell_ok24, cell_ok25, cell_ok26, cell_ok27, cell_ok28, cell_ok29, cell_ok30, cell_ok31, cell_ok32]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C143
