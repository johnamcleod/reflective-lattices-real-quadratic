import ReflectZphi.Cert.Cover
import ReflectZphi.Data.Cert5.C079.Base
import ReflectZphi.Data.Cert5.C079.P000
import ReflectZphi.Data.Cert5.C079.P001
import ReflectZphi.Data.Cert5.C079.P002
import ReflectZphi.Data.Cert5.C079.P003
import ReflectZphi.Data.Cert5.C079.P004
import ReflectZphi.Data.Cert5.C079.P005
import ReflectZphi.Data.Cert5.C079.P006
import ReflectZphi.Data.Cert5.C079.P007
import ReflectZphi.Data.Cert5.C079.P008
import ReflectZphi.Data.Cert5.C079.P009
import ReflectZphi.Data.Cert5.C079.P010
import ReflectZphi.Data.Cert5.C079.P011
import ReflectZphi.Data.Cert5.C079.P012
import ReflectZphi.Data.Cert5.C079.P013
import ReflectZphi.Data.Cert5.C079.P014
import ReflectZphi.Data.Cert5.C079.P015
import ReflectZphi.Data.Cert5.C079.P016
import ReflectZphi.Data.Cert5.C079.P017
import ReflectZphi.Data.Cert5.C079.P018
import ReflectZphi.Data.Cert5.C079.P019
import ReflectZphi.Data.Cert5.C079.P020

namespace ReflectZphi.Data.Cert5.C079
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
  exact sb1_0
theorem cell_ok1 : cellCheck G f n Ps normsL cell1 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok1 (enumS_of_coverL cover1 subs1)
theorem cover2 : (coverL cell2.aL cell2.w 6 2 6 (fun _ => 0) (cell2.S * cell2.K) [] preL2).isSome = true := by decide +kernel
theorem subs2 : ∀ q ∈ preL2, sub2 q = true := by
  unfold preL2
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb2_0, List.forall_mem_append.2 ⟨sb2_1, sb2_2⟩⟩, List.forall_mem_append.2 ⟨sb2_3, List.forall_mem_append.2 ⟨sb2_4, sb2_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb2_6, List.forall_mem_append.2 ⟨sb2_7, sb2_8⟩⟩, List.forall_mem_append.2 ⟨sb2_9, List.forall_mem_append.2 ⟨sb2_10, sb2_11⟩⟩⟩⟩
theorem cell_ok2 : cellCheck G f n Ps normsL cell2 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok2 (enumS_of_coverL cover2 subs2)
theorem cover3 : (coverL cell3.aL cell3.w 6 2 6 (fun _ => 0) (cell3.S * cell3.K) [] preL3).isSome = true := by decide +kernel
theorem subs3 : ∀ q ∈ preL3, sub3 q = true := by
  unfold preL3
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb3_0, sb3_1⟩, List.forall_mem_append.2 ⟨sb3_2, List.forall_mem_append.2 ⟨sb3_3, sb3_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb3_5, List.forall_mem_append.2 ⟨sb3_6, sb3_7⟩⟩, List.forall_mem_append.2 ⟨sb3_8, List.forall_mem_append.2 ⟨sb3_9, sb3_10⟩⟩⟩⟩
theorem cell_ok3 : cellCheck G f n Ps normsL cell3 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok3 (enumS_of_coverL cover3 subs3)
theorem cover4 : (coverL cell4.aL cell4.w 6 2 6 (fun _ => 0) (cell4.S * cell4.K) [] preL4).isSome = true := by decide +kernel
theorem subs4 : ∀ q ∈ preL4, sub4 q = true := by
  unfold preL4
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_0, List.forall_mem_append.2 ⟨sb4_1, sb4_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_3, sb4_4⟩, List.forall_mem_append.2 ⟨sb4_5, sb4_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_7, sb4_8⟩, List.forall_mem_append.2 ⟨sb4_9, sb4_10⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_11, sb4_12⟩, List.forall_mem_append.2 ⟨sb4_13, sb4_14⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_15, sb4_16⟩, List.forall_mem_append.2 ⟨sb4_17, sb4_18⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_19, sb4_20⟩, List.forall_mem_append.2 ⟨sb4_21, sb4_22⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_23, sb4_24⟩, List.forall_mem_append.2 ⟨sb4_25, sb4_26⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_27, sb4_28⟩, List.forall_mem_append.2 ⟨sb4_29, sb4_30⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_31, List.forall_mem_append.2 ⟨sb4_32, sb4_33⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_34, sb4_35⟩, List.forall_mem_append.2 ⟨sb4_36, sb4_37⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_38, sb4_39⟩, List.forall_mem_append.2 ⟨sb4_40, sb4_41⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_42, sb4_43⟩, List.forall_mem_append.2 ⟨sb4_44, sb4_45⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_46, sb4_47⟩, List.forall_mem_append.2 ⟨sb4_48, sb4_49⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_50, sb4_51⟩, List.forall_mem_append.2 ⟨sb4_52, sb4_53⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_54, sb4_55⟩, List.forall_mem_append.2 ⟨sb4_56, sb4_57⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb4_58, sb4_59⟩, List.forall_mem_append.2 ⟨sb4_60, sb4_61⟩⟩⟩⟩⟩⟩
theorem cell_ok4 : cellCheck G f n Ps normsL cell4 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok4 (enumS_of_coverL cover4 subs4)
theorem cover5 : (coverL cell5.aL cell5.w 6 2 6 (fun _ => 0) (cell5.S * cell5.K) [] preL5).isSome = true := by decide +kernel
theorem subs5 : ∀ q ∈ preL5, sub5 q = true := by
  unfold preL5
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_0, List.forall_mem_append.2 ⟨sb5_1, sb5_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_3, sb5_4⟩, List.forall_mem_append.2 ⟨sb5_5, sb5_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_7, List.forall_mem_append.2 ⟨sb5_8, sb5_9⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_10, sb5_11⟩, List.forall_mem_append.2 ⟨sb5_12, sb5_13⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_14, List.forall_mem_append.2 ⟨sb5_15, sb5_16⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_17, sb5_18⟩, List.forall_mem_append.2 ⟨sb5_19, sb5_20⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_21, sb5_22⟩, List.forall_mem_append.2 ⟨sb5_23, sb5_24⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_25, sb5_26⟩, List.forall_mem_append.2 ⟨sb5_27, sb5_28⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_29, List.forall_mem_append.2 ⟨sb5_30, sb5_31⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_32, sb5_33⟩, List.forall_mem_append.2 ⟨sb5_34, sb5_35⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_36, sb5_37⟩, List.forall_mem_append.2 ⟨sb5_38, sb5_39⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_40, sb5_41⟩, List.forall_mem_append.2 ⟨sb5_42, sb5_43⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_44, List.forall_mem_append.2 ⟨sb5_45, sb5_46⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_47, sb5_48⟩, List.forall_mem_append.2 ⟨sb5_49, sb5_50⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_51, sb5_52⟩, List.forall_mem_append.2 ⟨sb5_53, sb5_54⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb5_55, sb5_56⟩, List.forall_mem_append.2 ⟨sb5_57, sb5_58⟩⟩⟩⟩⟩⟩
theorem cell_ok5 : cellCheck G f n Ps normsL cell5 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok5 (enumS_of_coverL cover5 subs5)
theorem cover6 : (coverL cell6.aL cell6.w 6 2 6 (fun _ => 0) (cell6.S * cell6.K) [] preL6).isSome = true := by decide +kernel
theorem subs6 : ∀ q ∈ preL6, sub6 q = true := by
  unfold preL6
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_0, sb6_1⟩, List.forall_mem_append.2 ⟨sb6_2, sb6_3⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_4, sb6_5⟩, List.forall_mem_append.2 ⟨sb6_6, List.forall_mem_append.2 ⟨sb6_7, sb6_8⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_9, sb6_10⟩, List.forall_mem_append.2 ⟨sb6_11, List.forall_mem_append.2 ⟨sb6_12, sb6_13⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_14, sb6_15⟩, List.forall_mem_append.2 ⟨sb6_16, List.forall_mem_append.2 ⟨sb6_17, sb6_18⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_19, sb6_20⟩, List.forall_mem_append.2 ⟨sb6_21, sb6_22⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_23, sb6_24⟩, List.forall_mem_append.2 ⟨sb6_25, List.forall_mem_append.2 ⟨sb6_26, sb6_27⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_28, sb6_29⟩, List.forall_mem_append.2 ⟨sb6_30, List.forall_mem_append.2 ⟨sb6_31, sb6_32⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_33, sb6_34⟩, List.forall_mem_append.2 ⟨sb6_35, List.forall_mem_append.2 ⟨sb6_36, sb6_37⟩⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_38, sb6_39⟩, List.forall_mem_append.2 ⟨sb6_40, sb6_41⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_42, sb6_43⟩, List.forall_mem_append.2 ⟨sb6_44, List.forall_mem_append.2 ⟨sb6_45, sb6_46⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_47, sb6_48⟩, List.forall_mem_append.2 ⟨sb6_49, List.forall_mem_append.2 ⟨sb6_50, sb6_51⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_52, sb6_53⟩, List.forall_mem_append.2 ⟨sb6_54, List.forall_mem_append.2 ⟨sb6_55, sb6_56⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_57, sb6_58⟩, List.forall_mem_append.2 ⟨sb6_59, sb6_60⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_61, sb6_62⟩, List.forall_mem_append.2 ⟨sb6_63, List.forall_mem_append.2 ⟨sb6_64, sb6_65⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_66, sb6_67⟩, List.forall_mem_append.2 ⟨sb6_68, List.forall_mem_append.2 ⟨sb6_69, sb6_70⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_71, sb6_72⟩, List.forall_mem_append.2 ⟨sb6_73, List.forall_mem_append.2 ⟨sb6_74, sb6_75⟩⟩⟩⟩⟩⟩⟩
theorem cell_ok6 : cellCheck G f n Ps normsL cell6 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok6 (enumS_of_coverL cover6 subs6)
theorem cover7 : (coverL cell7.aL cell7.w 6 2 6 (fun _ => 0) (cell7.S * cell7.K) [] preL7).isSome = true := by decide +kernel
theorem subs7 : ∀ q ∈ preL7, sub7 q = true := by
  unfold preL7
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_0, List.forall_mem_append.2 ⟨sb7_1, sb7_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_3, sb7_4⟩, List.forall_mem_append.2 ⟨sb7_5, sb7_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_7, List.forall_mem_append.2 ⟨sb7_8, sb7_9⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_10, sb7_11⟩, List.forall_mem_append.2 ⟨sb7_12, sb7_13⟩⟩⟩⟩
theorem cell_ok7 : cellCheck G f n Ps normsL cell7 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok7 (enumS_of_coverL cover7 subs7)
theorem cover8 : (coverL cell8.aL cell8.w 6 2 6 (fun _ => 0) (cell8.S * cell8.K) [] preL8).isSome = true := by decide +kernel
theorem subs8 : ∀ q ∈ preL8, sub8 q = true := by
  unfold preL8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_0, sb8_1⟩, List.forall_mem_append.2 ⟨sb8_2, sb8_3⟩⟩
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

end ReflectZphi.Data.Cert5.C079
