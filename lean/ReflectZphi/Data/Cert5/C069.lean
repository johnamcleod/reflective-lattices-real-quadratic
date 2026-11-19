import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C069.Base
import ReflectZphi.Data.Cert5.C069.Pchk
import ReflectZphi.Data.Cert5.C069.P000
import ReflectZphi.Data.Cert5.C069.P001
import ReflectZphi.Data.Cert5.C069.P002
import ReflectZphi.Data.Cert5.C069.P003
import ReflectZphi.Data.Cert5.C069.P004

namespace ReflectZphi.Data.Cert5.C069

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
theorem cov_ok0 : normsCovered normsL [d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6, d0_7] = true := by decide +kernel
theorem cell_ok0 : CellOK hd G n Ps normsL cell0 :=
  cellOK_of hd adm (by decide +kernel) cov_ok0 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd0_0, en_okd0_0⟩
    · exact ⟨pre_okd0_1, en_okd0_1⟩
    · exact ⟨pre_okd0_2, en_okd0_2⟩
    · exact ⟨pre_okd0_3, en_okd0_3⟩
    · exact ⟨pre_okd0_4, en_okd0_4⟩
    · exact ⟨pre_okd0_5, en_okd0_5⟩
    · exact ⟨pre_okd0_6, en_okd0_6⟩
    · exact ⟨pre_okd0_7, en_okd0_7⟩
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
theorem cov_ok1 : normsCovered normsL [d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6, d1_7] = true := by decide +kernel
theorem cell_ok1 : CellOK hd G n Ps normsL cell1 :=
  cellOK_of hd adm (by decide +kernel) cov_ok1 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd1_0, en_okd1_0⟩
    · exact ⟨pre_okd1_1, en_okd1_1⟩
    · exact ⟨pre_okd1_2, en_okd1_2⟩
    · exact ⟨pre_okd1_3, en_okd1_3⟩
    · exact ⟨pre_okd1_4, en_okd1_4⟩
    · exact ⟨pre_okd1_5, en_okd1_5⟩
    · exact ⟨pre_okd1_6, en_okd1_6⟩
    · exact ⟨pre_okd1_7, en_okd1_7⟩
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
theorem cov_ok2 : normsCovered normsL [d2_0, d2_1, d2_2, d2_3, d2_4, d2_5, d2_6, d2_7] = true := by decide +kernel
theorem cell_ok2 : CellOK hd G n Ps normsL cell2 :=
  cellOK_of hd adm (by decide +kernel) cov_ok2 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd2_0, en_okd2_0⟩
    · exact ⟨pre_okd2_1, en_okd2_1⟩
    · exact ⟨pre_okd2_2, en_okd2_2⟩
    · exact ⟨pre_okd2_3, en_okd2_3⟩
    · exact ⟨pre_okd2_4, en_okd2_4⟩
    · exact ⟨pre_okd2_5, en_okd2_5⟩
    · exact ⟨pre_okd2_6, en_okd2_6⟩
    · exact ⟨pre_okd2_7, en_okd2_7⟩
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
theorem cov_ok3 : normsCovered normsL [d3_0, d3_1, d3_2, d3_3, d3_4, d3_5, d3_6, d3_7] = true := by decide +kernel
theorem cell_ok3 : CellOK hd G n Ps normsL cell3 :=
  cellOK_of hd adm (by decide +kernel) cov_ok3 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd3_0, en_okd3_0⟩
    · exact ⟨pre_okd3_1, en_okd3_1⟩
    · exact ⟨pre_okd3_2, en_okd3_2⟩
    · exact ⟨pre_okd3_3, en_okd3_3⟩
    · exact ⟨pre_okd3_4, en_okd3_4⟩
    · exact ⟨pre_okd3_5, en_okd3_5⟩
    · exact ⟨pre_okd3_6, en_okd3_6⟩
    · exact ⟨pre_okd3_7, en_okd3_7⟩
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
theorem cov_ok4 : normsCovered normsL [d4_0, d4_1, d4_2, d4_3, d4_4, d4_5, d4_6, d4_7] = true := by decide +kernel
theorem cell_ok4 : CellOK hd G n Ps normsL cell4 :=
  cellOK_of hd adm (by decide +kernel) cov_ok4 (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pre_okd4_0, en_okd4_0⟩
    · exact ⟨pre_okd4_1, en_okd4_1⟩
    · exact ⟨pre_okd4_2, en_okd4_2⟩
    · exact ⟨pre_okd4_3, en_okd4_3⟩
    · exact ⟨pre_okd4_4, en_okd4_4⟩
    · exact ⟨pre_okd4_5, en_okd4_5⟩
    · exact ⟨pre_okd4_6, en_okd4_6⟩
    · exact ⟨pre_okd4_7, en_okd4_7⟩
  )

theorem cen_ok : ∀ k, k < nc → cenCheck G f (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k <;> decide +kernel
theorem cells_ok : ∀ k, k < nc → CellOK hd G n Ps normsL (cells k) := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4]

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_checkM hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cen_ok cells_ok

end ReflectZphi.Data.Cert5.C069
