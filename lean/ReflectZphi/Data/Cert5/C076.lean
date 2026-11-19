import ReflectZphi.Cert.Cover
import ReflectZphi.Data.Cert5.C076.Base
import ReflectZphi.Data.Cert5.C076.P000
import ReflectZphi.Data.Cert5.C076.P001
import ReflectZphi.Data.Cert5.C076.P002
import ReflectZphi.Data.Cert5.C076.P003
import ReflectZphi.Data.Cert5.C076.P004
import ReflectZphi.Data.Cert5.C076.P005
import ReflectZphi.Data.Cert5.C076.P006
import ReflectZphi.Data.Cert5.C076.P007

namespace ReflectZphi.Data.Cert5.C076
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem cover0 : (coverL cell0.aL cell0.w 6 2 6 (fun _ => 0) (cell0.S * cell0.K) [] preL0).isSome = true := by decide +kernel
theorem subs0 : ∀ q ∈ preL0, sub0 q = true := by
  unfold preL0
  exact List.forall_mem_append.2 ⟨sb0_0, List.forall_mem_append.2 ⟨sb0_1, List.forall_mem_append.2 ⟨sb0_2, sb0_3⟩⟩⟩
theorem cell_ok0 : cellCheck G f n Ps normsL cell0 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok0 (enumS_of_coverL cover0 subs0)
theorem cover1 : (coverL cell1.aL cell1.w 6 2 6 (fun _ => 0) (cell1.S * cell1.K) [] preL1).isSome = true := by decide +kernel
theorem subs1 : ∀ q ∈ preL1, sub1 q = true := by
  unfold preL1
  exact List.forall_mem_append.2 ⟨sb1_0, List.forall_mem_append.2 ⟨sb1_1, sb1_2⟩⟩
theorem cell_ok1 : cellCheck G f n Ps normsL cell1 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok1 (enumS_of_coverL cover1 subs1)
theorem cover2 : (coverL cell2.aL cell2.w 6 2 6 (fun _ => 0) (cell2.S * cell2.K) [] preL2).isSome = true := by decide +kernel
theorem subs2 : ∀ q ∈ preL2, sub2 q = true := by
  unfold preL2
  exact List.forall_mem_append.2 ⟨sb2_0, sb2_1⟩
theorem cell_ok2 : cellCheck G f n Ps normsL cell2 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok2 (enumS_of_coverL cover2 subs2)
theorem cover3 : (coverL cell3.aL cell3.w 6 2 6 (fun _ => 0) (cell3.S * cell3.K) [] preL3).isSome = true := by decide +kernel
theorem subs3 : ∀ q ∈ preL3, sub3 q = true := by
  unfold preL3
  exact List.forall_mem_append.2 ⟨sb3_0, sb3_1⟩
theorem cell_ok3 : cellCheck G f n Ps normsL cell3 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok3 (enumS_of_coverL cover3 subs3)
theorem cover4 : (coverL cell4.aL cell4.w 6 2 6 (fun _ => 0) (cell4.S * cell4.K) [] preL4).isSome = true := by decide +kernel
theorem subs4 : ∀ q ∈ preL4, sub4 q = true := by
  unfold preL4
  exact List.forall_mem_append.2 ⟨sb4_0, List.forall_mem_append.2 ⟨sb4_1, sb4_2⟩⟩
theorem cell_ok4 : cellCheck G f n Ps normsL cell4 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok4 (enumS_of_coverL cover4 subs4)
theorem cover5 : (coverL cell5.aL cell5.w 6 2 6 (fun _ => 0) (cell5.S * cell5.K) [] preL5).isSome = true := by decide +kernel
theorem subs5 : ∀ q ∈ preL5, sub5 q = true := by
  unfold preL5
  exact List.forall_mem_append.2 ⟨sb5_0, List.forall_mem_append.2 ⟨sb5_1, sb5_2⟩⟩
theorem cell_ok5 : cellCheck G f n Ps normsL cell5 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok5 (enumS_of_coverL cover5 subs5)
theorem cover6 : (coverL cell6.aL cell6.w 6 2 6 (fun _ => 0) (cell6.S * cell6.K) [] preL6).isSome = true := by decide +kernel
theorem subs6 : ∀ q ∈ preL6, sub6 q = true := by
  unfold preL6
  exact List.forall_mem_append.2 ⟨sb6_0, List.forall_mem_append.2 ⟨sb6_1, List.forall_mem_append.2 ⟨sb6_2, List.forall_mem_append.2 ⟨sb6_3, List.forall_mem_append.2 ⟨sb6_4, List.forall_mem_append.2 ⟨sb6_5, List.forall_mem_append.2 ⟨sb6_6, List.forall_mem_append.2 ⟨sb6_7, sb6_8⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok6 : cellCheck G f n Ps normsL cell6 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok6 (enumS_of_coverL cover6 subs6)
theorem cover7 : (coverL cell7.aL cell7.w 6 2 6 (fun _ => 0) (cell7.S * cell7.K) [] preL7).isSome = true := by decide +kernel
theorem subs7 : ∀ q ∈ preL7, sub7 q = true := by
  unfold preL7
  exact List.forall_mem_append.2 ⟨sb7_0, List.forall_mem_append.2 ⟨sb7_1, List.forall_mem_append.2 ⟨sb7_2, List.forall_mem_append.2 ⟨sb7_3, List.forall_mem_append.2 ⟨sb7_4, List.forall_mem_append.2 ⟨sb7_5, List.forall_mem_append.2 ⟨sb7_6, List.forall_mem_append.2 ⟨sb7_7, List.forall_mem_append.2 ⟨sb7_8, List.forall_mem_append.2 ⟨sb7_9, sb7_10⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok7 : cellCheck G f n Ps normsL cell7 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok7 (enumS_of_coverL cover7 subs7)
theorem cover8 : (coverL cell8.aL cell8.w 6 2 6 (fun _ => 0) (cell8.S * cell8.K) [] preL8).isSome = true := by decide +kernel
theorem subs8 : ∀ q ∈ preL8, sub8 q = true := by
  unfold preL8
  exact List.forall_mem_append.2 ⟨sb8_0, List.forall_mem_append.2 ⟨sb8_1, List.forall_mem_append.2 ⟨sb8_2, List.forall_mem_append.2 ⟨sb8_3, List.forall_mem_append.2 ⟨sb8_4, List.forall_mem_append.2 ⟨sb8_5, List.forall_mem_append.2 ⟨sb8_6, List.forall_mem_append.2 ⟨sb8_7, List.forall_mem_append.2 ⟨sb8_8, List.forall_mem_append.2 ⟨sb8_9, List.forall_mem_append.2 ⟨sb8_10, sb8_11⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok8 : cellCheck G f n Ps normsL cell8 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok8 (enumS_of_coverL cover8 subs8)
theorem cells_ok : ∀ k, k < nc → cellCheck G f n Ps normsL (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8]

theorem hd : (0 : ℝ) < ((1 : ℤ) : ℝ) ^ 2 + 4 * ((1 : ℤ) : ℝ) := by norm_num

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_check hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cells_ok

end ReflectZphi.Data.Cert5.C076
