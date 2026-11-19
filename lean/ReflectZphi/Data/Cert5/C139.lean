import ReflectZphi.Cert.Sublat
import ReflectZphi.Data.Cert5.C139.Base
import ReflectZphi.Data.Cert5.C139.Pchk
import ReflectZphi.Data.Cert5.C139.P000
import ReflectZphi.Data.Cert5.C139.P001
import ReflectZphi.Data.Cert5.C139.P002
import ReflectZphi.Data.Cert5.C139.P003
import ReflectZphi.Data.Cert5.C139.P004
import ReflectZphi.Data.Cert5.C139.P005
import ReflectZphi.Data.Cert5.C139.P006
import ReflectZphi.Data.Cert5.C139.P007
import ReflectZphi.Data.Cert5.C139.P008
import ReflectZphi.Data.Cert5.C139.P009
import ReflectZphi.Data.Cert5.C139.P010
import ReflectZphi.Data.Cert5.C139.P011
import ReflectZphi.Data.Cert5.C139.P012
import ReflectZphi.Data.Cert5.C139.P013
import ReflectZphi.Data.Cert5.C139.P014

namespace ReflectZphi.Data.Cert5.C139

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
  exact List.forall_mem_append.2 ⟨sbd1_1_0, sbd1_1_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd2_1_0, sbd2_1_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd2_3_0, sbd2_3_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd4_3_0, sbd4_3_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd5_1_0, sbd5_1_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd6_1_0, sbd6_1_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd6_3_0, sbd6_3_1⟩
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
  exact List.forall_mem_append.2 ⟨sbd10_3_0, List.forall_mem_append.2 ⟨sbd10_3_1, sbd10_3_2⟩⟩
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
  exact sbd11_0_0
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
  exact sbd11_2_0
theorem en_okd11_2 : subEnum G n Ps d11_2 = true :=
  subEnum_fast ld_okd11_2 (enumS_of_coverL coverd11_2 subsd11_2)
theorem coverd11_3 : (coverL d11_3.aL d11_3.w 6 2 6 (fun _ => 0) (d11_3.S * d11_3.K) [] preLd11_3).isSome = true := by decide +kernel
theorem subsd11_3 : ∀ q ∈ preLd11_3, subd11_3 q = true := by
  unfold preLd11_3
  exact sbd11_3_0
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
  exact sbd12_0_0
theorem en_okd12_0 : subEnum G n Ps d12_0 = true :=
  subEnum_fast ld_okd12_0 (enumS_of_coverL coverd12_0 subsd12_0)
theorem coverd12_1 : (coverL d12_1.aL d12_1.w 6 2 6 (fun _ => 0) (d12_1.S * d12_1.K) [] preLd12_1).isSome = true := by decide +kernel
theorem subsd12_1 : ∀ q ∈ preLd12_1, subd12_1 q = true := by
  unfold preLd12_1
  exact List.forall_mem_append.2 ⟨sbd12_1_0, sbd12_1_1⟩
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
  exact sbd14_0_0
theorem en_okd14_0 : subEnum G n Ps d14_0 = true :=
  subEnum_fast ld_okd14_0 (enumS_of_coverL coverd14_0 subsd14_0)
theorem coverd14_1 : (coverL d14_1.aL d14_1.w 6 2 6 (fun _ => 0) (d14_1.S * d14_1.K) [] preLd14_1).isSome = true := by decide +kernel
theorem subsd14_1 : ∀ q ∈ preLd14_1, subd14_1 q = true := by
  unfold preLd14_1
  exact sbd14_1_0
theorem en_okd14_1 : subEnum G n Ps d14_1 = true :=
  subEnum_fast ld_okd14_1 (enumS_of_coverL coverd14_1 subsd14_1)
theorem coverd14_2 : (coverL d14_2.aL d14_2.w 6 2 6 (fun _ => 0) (d14_2.S * d14_2.K) [] preLd14_2).isSome = true := by decide +kernel
theorem subsd14_2 : ∀ q ∈ preLd14_2, subd14_2 q = true := by
  unfold preLd14_2
  exact sbd14_2_0
theorem en_okd14_2 : subEnum G n Ps d14_2 = true :=
  subEnum_fast ld_okd14_2 (enumS_of_coverL coverd14_2 subsd14_2)
theorem coverd14_3 : (coverL d14_3.aL d14_3.w 6 2 6 (fun _ => 0) (d14_3.S * d14_3.K) [] preLd14_3).isSome = true := by decide +kernel
theorem subsd14_3 : ∀ q ∈ preLd14_3, subd14_3 q = true := by
  unfold preLd14_3
  exact sbd14_3_0
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
  exact sbd15_0_0
theorem en_okd15_0 : subEnum G n Ps d15_0 = true :=
  subEnum_fast ld_okd15_0 (enumS_of_coverL coverd15_0 subsd15_0)
theorem coverd15_1 : (coverL d15_1.aL d15_1.w 6 2 6 (fun _ => 0) (d15_1.S * d15_1.K) [] preLd15_1).isSome = true := by decide +kernel
theorem subsd15_1 : ∀ q ∈ preLd15_1, subd15_1 q = true := by
  unfold preLd15_1
  exact sbd15_1_0
theorem en_okd15_1 : subEnum G n Ps d15_1 = true :=
  subEnum_fast ld_okd15_1 (enumS_of_coverL coverd15_1 subsd15_1)
theorem coverd15_2 : (coverL d15_2.aL d15_2.w 6 2 6 (fun _ => 0) (d15_2.S * d15_2.K) [] preLd15_2).isSome = true := by decide +kernel
theorem subsd15_2 : ∀ q ∈ preLd15_2, subd15_2 q = true := by
  unfold preLd15_2
  exact sbd15_2_0
theorem en_okd15_2 : subEnum G n Ps d15_2 = true :=
  subEnum_fast ld_okd15_2 (enumS_of_coverL coverd15_2 subsd15_2)
theorem coverd15_3 : (coverL d15_3.aL d15_3.w 6 2 6 (fun _ => 0) (d15_3.S * d15_3.K) [] preLd15_3).isSome = true := by decide +kernel
theorem subsd15_3 : ∀ q ∈ preLd15_3, subd15_3 q = true := by
  unfold preLd15_3
  exact sbd15_3_0
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
  exact sbd16_0_0
theorem en_okd16_0 : subEnum G n Ps d16_0 = true :=
  subEnum_fast ld_okd16_0 (enumS_of_coverL coverd16_0 subsd16_0)
theorem coverd16_1 : (coverL d16_1.aL d16_1.w 6 2 6 (fun _ => 0) (d16_1.S * d16_1.K) [] preLd16_1).isSome = true := by decide +kernel
theorem subsd16_1 : ∀ q ∈ preLd16_1, subd16_1 q = true := by
  unfold preLd16_1
  exact List.forall_mem_append.2 ⟨sbd16_1_0, sbd16_1_1⟩
theorem en_okd16_1 : subEnum G n Ps d16_1 = true :=
  subEnum_fast ld_okd16_1 (enumS_of_coverL coverd16_1 subsd16_1)
theorem coverd16_2 : (coverL d16_2.aL d16_2.w 6 2 6 (fun _ => 0) (d16_2.S * d16_2.K) [] preLd16_2).isSome = true := by decide +kernel
theorem subsd16_2 : ∀ q ∈ preLd16_2, subd16_2 q = true := by
  unfold preLd16_2
  exact sbd16_2_0
theorem en_okd16_2 : subEnum G n Ps d16_2 = true :=
  subEnum_fast ld_okd16_2 (enumS_of_coverL coverd16_2 subsd16_2)
theorem coverd16_3 : (coverL d16_3.aL d16_3.w 6 2 6 (fun _ => 0) (d16_3.S * d16_3.K) [] preLd16_3).isSome = true := by decide +kernel
theorem subsd16_3 : ∀ q ∈ preLd16_3, subd16_3 q = true := by
  unfold preLd16_3
  exact List.forall_mem_append.2 ⟨sbd16_3_0, sbd16_3_1⟩
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

end ReflectZphi.Data.Cert5.C139
