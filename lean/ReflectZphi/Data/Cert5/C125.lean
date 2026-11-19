import ReflectZphi.Cert.Cover
import ReflectZphi.Data.Cert5.C125.Base
import ReflectZphi.Data.Cert5.C125.P000
import ReflectZphi.Data.Cert5.C125.P001
import ReflectZphi.Data.Cert5.C125.P002
import ReflectZphi.Data.Cert5.C125.P003
import ReflectZphi.Data.Cert5.C125.P004
import ReflectZphi.Data.Cert5.C125.P005
import ReflectZphi.Data.Cert5.C125.P006
import ReflectZphi.Data.Cert5.C125.P007
import ReflectZphi.Data.Cert5.C125.P008
import ReflectZphi.Data.Cert5.C125.P009
import ReflectZphi.Data.Cert5.C125.P010
import ReflectZphi.Data.Cert5.C125.P011
import ReflectZphi.Data.Cert5.C125.P012
import ReflectZphi.Data.Cert5.C125.P013
import ReflectZphi.Data.Cert5.C125.P014
import ReflectZphi.Data.Cert5.C125.P015
import ReflectZphi.Data.Cert5.C125.P016
import ReflectZphi.Data.Cert5.C125.P017
import ReflectZphi.Data.Cert5.C125.P018

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem cover0 : (coverL cell0.aL cell0.w 6 2 6 (fun _ => 0) (cell0.S * cell0.K) [] preL0).isSome = true := by decide +kernel
theorem subs0 : ∀ q ∈ preL0, sub0 q = true := by
  unfold preL0
  exact sb0_0
theorem cell_ok0 : cellCheck G f n Ps normsL cell0 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok0 (enumS_of_coverL cover0 subs0)
theorem cover1 : (coverL cell1.aL cell1.w 6 2 6 (fun _ => 0) (cell1.S * cell1.K) [] preL1).isSome = true := by decide +kernel
theorem subs1 : ∀ q ∈ preL1, sub1 q = true := by
  unfold preL1
  exact List.forall_mem_append.2 ⟨sb1_0, List.forall_mem_append.2 ⟨sb1_1, List.forall_mem_append.2 ⟨sb1_2, List.forall_mem_append.2 ⟨sb1_3, List.forall_mem_append.2 ⟨sb1_4, sb1_5⟩⟩⟩⟩⟩
theorem cell_ok1 : cellCheck G f n Ps normsL cell1 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok1 (enumS_of_coverL cover1 subs1)
theorem cover2 : (coverL cell2.aL cell2.w 6 2 6 (fun _ => 0) (cell2.S * cell2.K) [] preL2).isSome = true := by decide +kernel
theorem subs2 : ∀ q ∈ preL2, sub2 q = true := by
  unfold preL2
  exact List.forall_mem_append.2 ⟨sb2_0, List.forall_mem_append.2 ⟨sb2_1, sb2_2⟩⟩
theorem cell_ok2 : cellCheck G f n Ps normsL cell2 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok2 (enumS_of_coverL cover2 subs2)
theorem cover3 : (coverL cell3.aL cell3.w 6 2 6 (fun _ => 0) (cell3.S * cell3.K) [] preL3).isSome = true := by decide +kernel
theorem subs3 : ∀ q ∈ preL3, sub3 q = true := by
  unfold preL3
  exact List.forall_mem_append.2 ⟨sb3_0, List.forall_mem_append.2 ⟨sb3_1, List.forall_mem_append.2 ⟨sb3_2, List.forall_mem_append.2 ⟨sb3_3, List.forall_mem_append.2 ⟨sb3_4, List.forall_mem_append.2 ⟨sb3_5, List.forall_mem_append.2 ⟨sb3_6, List.forall_mem_append.2 ⟨sb3_7, List.forall_mem_append.2 ⟨sb3_8, List.forall_mem_append.2 ⟨sb3_9, List.forall_mem_append.2 ⟨sb3_10, List.forall_mem_append.2 ⟨sb3_11, List.forall_mem_append.2 ⟨sb3_12, List.forall_mem_append.2 ⟨sb3_13, List.forall_mem_append.2 ⟨sb3_14, List.forall_mem_append.2 ⟨sb3_15, List.forall_mem_append.2 ⟨sb3_16, List.forall_mem_append.2 ⟨sb3_17, List.forall_mem_append.2 ⟨sb3_18, List.forall_mem_append.2 ⟨sb3_19, sb3_20⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok3 : cellCheck G f n Ps normsL cell3 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok3 (enumS_of_coverL cover3 subs3)
theorem cover4 : (coverL cell4.aL cell4.w 6 2 6 (fun _ => 0) (cell4.S * cell4.K) [] preL4).isSome = true := by decide +kernel
theorem subs4 : ∀ q ∈ preL4, sub4 q = true := by
  unfold preL4
  exact List.forall_mem_append.2 ⟨sb4_0, List.forall_mem_append.2 ⟨sb4_1, List.forall_mem_append.2 ⟨sb4_2, List.forall_mem_append.2 ⟨sb4_3, sb4_4⟩⟩⟩⟩
theorem cell_ok4 : cellCheck G f n Ps normsL cell4 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok4 (enumS_of_coverL cover4 subs4)
theorem cover5 : (coverL cell5.aL cell5.w 6 2 6 (fun _ => 0) (cell5.S * cell5.K) [] preL5).isSome = true := by decide +kernel
theorem subs5 : ∀ q ∈ preL5, sub5 q = true := by
  unfold preL5
  exact List.forall_mem_append.2 ⟨sb5_0, List.forall_mem_append.2 ⟨sb5_1, List.forall_mem_append.2 ⟨sb5_2, List.forall_mem_append.2 ⟨sb5_3, List.forall_mem_append.2 ⟨sb5_4, List.forall_mem_append.2 ⟨sb5_5, List.forall_mem_append.2 ⟨sb5_6, List.forall_mem_append.2 ⟨sb5_7, List.forall_mem_append.2 ⟨sb5_8, List.forall_mem_append.2 ⟨sb5_9, List.forall_mem_append.2 ⟨sb5_10, List.forall_mem_append.2 ⟨sb5_11, List.forall_mem_append.2 ⟨sb5_12, List.forall_mem_append.2 ⟨sb5_13, List.forall_mem_append.2 ⟨sb5_14, List.forall_mem_append.2 ⟨sb5_15, List.forall_mem_append.2 ⟨sb5_16, List.forall_mem_append.2 ⟨sb5_17, List.forall_mem_append.2 ⟨sb5_18, List.forall_mem_append.2 ⟨sb5_19, List.forall_mem_append.2 ⟨sb5_20, List.forall_mem_append.2 ⟨sb5_21, List.forall_mem_append.2 ⟨sb5_22, List.forall_mem_append.2 ⟨sb5_23, List.forall_mem_append.2 ⟨sb5_24, List.forall_mem_append.2 ⟨sb5_25, List.forall_mem_append.2 ⟨sb5_26, List.forall_mem_append.2 ⟨sb5_27, sb5_28⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok5 : cellCheck G f n Ps normsL cell5 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok5 (enumS_of_coverL cover5 subs5)
theorem cover6 : (coverL cell6.aL cell6.w 6 2 6 (fun _ => 0) (cell6.S * cell6.K) [] preL6).isSome = true := by decide +kernel
theorem subs6 : ∀ q ∈ preL6, sub6 q = true := by
  unfold preL6
  exact List.forall_mem_append.2 ⟨sb6_0, List.forall_mem_append.2 ⟨sb6_1, List.forall_mem_append.2 ⟨sb6_2, List.forall_mem_append.2 ⟨sb6_3, List.forall_mem_append.2 ⟨sb6_4, sb6_5⟩⟩⟩⟩⟩
theorem cell_ok6 : cellCheck G f n Ps normsL cell6 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok6 (enumS_of_coverL cover6 subs6)
theorem cover7 : (coverL cell7.aL cell7.w 6 2 6 (fun _ => 0) (cell7.S * cell7.K) [] preL7).isSome = true := by decide +kernel
theorem subs7 : ∀ q ∈ preL7, sub7 q = true := by
  unfold preL7
  exact List.forall_mem_append.2 ⟨sb7_0, List.forall_mem_append.2 ⟨sb7_1, List.forall_mem_append.2 ⟨sb7_2, List.forall_mem_append.2 ⟨sb7_3, List.forall_mem_append.2 ⟨sb7_4, List.forall_mem_append.2 ⟨sb7_5, List.forall_mem_append.2 ⟨sb7_6, List.forall_mem_append.2 ⟨sb7_7, List.forall_mem_append.2 ⟨sb7_8, List.forall_mem_append.2 ⟨sb7_9, List.forall_mem_append.2 ⟨sb7_10, List.forall_mem_append.2 ⟨sb7_11, List.forall_mem_append.2 ⟨sb7_12, List.forall_mem_append.2 ⟨sb7_13, List.forall_mem_append.2 ⟨sb7_14, List.forall_mem_append.2 ⟨sb7_15, List.forall_mem_append.2 ⟨sb7_16, List.forall_mem_append.2 ⟨sb7_17, List.forall_mem_append.2 ⟨sb7_18, List.forall_mem_append.2 ⟨sb7_19, List.forall_mem_append.2 ⟨sb7_20, List.forall_mem_append.2 ⟨sb7_21, List.forall_mem_append.2 ⟨sb7_22, List.forall_mem_append.2 ⟨sb7_23, List.forall_mem_append.2 ⟨sb7_24, List.forall_mem_append.2 ⟨sb7_25, List.forall_mem_append.2 ⟨sb7_26, List.forall_mem_append.2 ⟨sb7_27, List.forall_mem_append.2 ⟨sb7_28, List.forall_mem_append.2 ⟨sb7_29, List.forall_mem_append.2 ⟨sb7_30, List.forall_mem_append.2 ⟨sb7_31, List.forall_mem_append.2 ⟨sb7_32, List.forall_mem_append.2 ⟨sb7_33, List.forall_mem_append.2 ⟨sb7_34, List.forall_mem_append.2 ⟨sb7_35, List.forall_mem_append.2 ⟨sb7_36, sb7_37⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok7 : cellCheck G f n Ps normsL cell7 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok7 (enumS_of_coverL cover7 subs7)
theorem cover8 : (coverL cell8.aL cell8.w 6 2 6 (fun _ => 0) (cell8.S * cell8.K) [] preL8).isSome = true := by decide +kernel
theorem subs8 : ∀ q ∈ preL8, sub8 q = true := by
  unfold preL8
  exact List.forall_mem_append.2 ⟨sb8_0, List.forall_mem_append.2 ⟨sb8_1, List.forall_mem_append.2 ⟨sb8_2, List.forall_mem_append.2 ⟨sb8_3, List.forall_mem_append.2 ⟨sb8_4, List.forall_mem_append.2 ⟨sb8_5, List.forall_mem_append.2 ⟨sb8_6, List.forall_mem_append.2 ⟨sb8_7, List.forall_mem_append.2 ⟨sb8_8, List.forall_mem_append.2 ⟨sb8_9, List.forall_mem_append.2 ⟨sb8_10, List.forall_mem_append.2 ⟨sb8_11, List.forall_mem_append.2 ⟨sb8_12, List.forall_mem_append.2 ⟨sb8_13, List.forall_mem_append.2 ⟨sb8_14, List.forall_mem_append.2 ⟨sb8_15, List.forall_mem_append.2 ⟨sb8_16, sb8_17⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok8 : cellCheck G f n Ps normsL cell8 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok8 (enumS_of_coverL cover8 subs8)
theorem cover9 : (coverL cell9.aL cell9.w 6 2 6 (fun _ => 0) (cell9.S * cell9.K) [] preL9).isSome = true := by decide +kernel
theorem subs9 : ∀ q ∈ preL9, sub9 q = true := by
  unfold preL9
  exact List.forall_mem_append.2 ⟨sb9_0, List.forall_mem_append.2 ⟨sb9_1, List.forall_mem_append.2 ⟨sb9_2, List.forall_mem_append.2 ⟨sb9_3, List.forall_mem_append.2 ⟨sb9_4, List.forall_mem_append.2 ⟨sb9_5, List.forall_mem_append.2 ⟨sb9_6, List.forall_mem_append.2 ⟨sb9_7, List.forall_mem_append.2 ⟨sb9_8, List.forall_mem_append.2 ⟨sb9_9, List.forall_mem_append.2 ⟨sb9_10, List.forall_mem_append.2 ⟨sb9_11, List.forall_mem_append.2 ⟨sb9_12, List.forall_mem_append.2 ⟨sb9_13, List.forall_mem_append.2 ⟨sb9_14, List.forall_mem_append.2 ⟨sb9_15, List.forall_mem_append.2 ⟨sb9_16, List.forall_mem_append.2 ⟨sb9_17, List.forall_mem_append.2 ⟨sb9_18, List.forall_mem_append.2 ⟨sb9_19, List.forall_mem_append.2 ⟨sb9_20, List.forall_mem_append.2 ⟨sb9_21, List.forall_mem_append.2 ⟨sb9_22, List.forall_mem_append.2 ⟨sb9_23, List.forall_mem_append.2 ⟨sb9_24, List.forall_mem_append.2 ⟨sb9_25, List.forall_mem_append.2 ⟨sb9_26, List.forall_mem_append.2 ⟨sb9_27, List.forall_mem_append.2 ⟨sb9_28, List.forall_mem_append.2 ⟨sb9_29, List.forall_mem_append.2 ⟨sb9_30, List.forall_mem_append.2 ⟨sb9_31, List.forall_mem_append.2 ⟨sb9_32, List.forall_mem_append.2 ⟨sb9_33, List.forall_mem_append.2 ⟨sb9_34, sb9_35⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok9 : cellCheck G f n Ps normsL cell9 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok9 (enumS_of_coverL cover9 subs9)
theorem cover10 : (coverL cell10.aL cell10.w 6 2 6 (fun _ => 0) (cell10.S * cell10.K) [] preL10).isSome = true := by decide +kernel
theorem subs10 : ∀ q ∈ preL10, sub10 q = true := by
  unfold preL10
  exact List.forall_mem_append.2 ⟨sb10_0, List.forall_mem_append.2 ⟨sb10_1, List.forall_mem_append.2 ⟨sb10_2, List.forall_mem_append.2 ⟨sb10_3, List.forall_mem_append.2 ⟨sb10_4, List.forall_mem_append.2 ⟨sb10_5, List.forall_mem_append.2 ⟨sb10_6, List.forall_mem_append.2 ⟨sb10_7, List.forall_mem_append.2 ⟨sb10_8, List.forall_mem_append.2 ⟨sb10_9, List.forall_mem_append.2 ⟨sb10_10, List.forall_mem_append.2 ⟨sb10_11, List.forall_mem_append.2 ⟨sb10_12, List.forall_mem_append.2 ⟨sb10_13, List.forall_mem_append.2 ⟨sb10_14, sb10_15⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok10 : cellCheck G f n Ps normsL cell10 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok10 (enumS_of_coverL cover10 subs10)
theorem cover11 : (coverL cell11.aL cell11.w 6 2 6 (fun _ => 0) (cell11.S * cell11.K) [] preL11).isSome = true := by decide +kernel
theorem subs11 : ∀ q ∈ preL11, sub11 q = true := by
  unfold preL11
  exact List.forall_mem_append.2 ⟨sb11_0, List.forall_mem_append.2 ⟨sb11_1, sb11_2⟩⟩
theorem cell_ok11 : cellCheck G f n Ps normsL cell11 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok11 (enumS_of_coverL cover11 subs11)
theorem cover12 : (coverL cell12.aL cell12.w 6 2 6 (fun _ => 0) (cell12.S * cell12.K) [] preL12).isSome = true := by decide +kernel
theorem subs12 : ∀ q ∈ preL12, sub12 q = true := by
  unfold preL12
  exact List.forall_mem_append.2 ⟨sb12_0, sb12_1⟩
theorem cell_ok12 : cellCheck G f n Ps normsL cell12 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok12 (enumS_of_coverL cover12 subs12)
theorem cells_ok : ∀ k, k < nc → cellCheck G f n Ps normsL (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8, cell_ok9, cell_ok10, cell_ok11, cell_ok12]

theorem hd : (0 : ℝ) < ((1 : ℤ) : ℝ) ^ 2 + 4 * ((1 : ℤ) : ℝ) := by norm_num

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_check hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cells_ok

end ReflectZphi.Data.Cert5.C125
