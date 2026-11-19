import ReflectZphi.Cert.Cover
import ReflectZphi.Data.Cert5.C080.Base
import ReflectZphi.Data.Cert5.C080.P000
import ReflectZphi.Data.Cert5.C080.P001
import ReflectZphi.Data.Cert5.C080.P002
import ReflectZphi.Data.Cert5.C080.P003
import ReflectZphi.Data.Cert5.C080.P004
import ReflectZphi.Data.Cert5.C080.P005
import ReflectZphi.Data.Cert5.C080.P006
import ReflectZphi.Data.Cert5.C080.P007
import ReflectZphi.Data.Cert5.C080.P008
import ReflectZphi.Data.Cert5.C080.P009
import ReflectZphi.Data.Cert5.C080.P010
import ReflectZphi.Data.Cert5.C080.P011
import ReflectZphi.Data.Cert5.C080.P012
import ReflectZphi.Data.Cert5.C080.P013
import ReflectZphi.Data.Cert5.C080.P014
import ReflectZphi.Data.Cert5.C080.P015
import ReflectZphi.Data.Cert5.C080.P016
import ReflectZphi.Data.Cert5.C080.P017
import ReflectZphi.Data.Cert5.C080.P018
import ReflectZphi.Data.Cert5.C080.P019
import ReflectZphi.Data.Cert5.C080.P020
import ReflectZphi.Data.Cert5.C080.P021

namespace ReflectZphi.Data.Cert5.C080
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
  exact List.forall_mem_append.2 ⟨sb1_0, sb1_1⟩
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
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb3_0, List.forall_mem_append.2 ⟨sb3_1, sb3_2⟩⟩, List.forall_mem_append.2 ⟨sb3_3, List.forall_mem_append.2 ⟨sb3_4, sb3_5⟩⟩⟩
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
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_0, List.forall_mem_append.2 ⟨sb6_1, sb6_2⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_3, sb6_4⟩, List.forall_mem_append.2 ⟨sb6_5, sb6_6⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_7, sb6_8⟩, List.forall_mem_append.2 ⟨sb6_9, sb6_10⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_11, sb6_12⟩, List.forall_mem_append.2 ⟨sb6_13, sb6_14⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_15, List.forall_mem_append.2 ⟨sb6_16, sb6_17⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_18, sb6_19⟩, List.forall_mem_append.2 ⟨sb6_20, sb6_21⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_22, sb6_23⟩, List.forall_mem_append.2 ⟨sb6_24, sb6_25⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_26, sb6_27⟩, List.forall_mem_append.2 ⟨sb6_28, sb6_29⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_30, List.forall_mem_append.2 ⟨sb6_31, sb6_32⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_33, sb6_34⟩, List.forall_mem_append.2 ⟨sb6_35, sb6_36⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_37, sb6_38⟩, List.forall_mem_append.2 ⟨sb6_39, sb6_40⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_41, sb6_42⟩, List.forall_mem_append.2 ⟨sb6_43, sb6_44⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_45, sb6_46⟩, List.forall_mem_append.2 ⟨sb6_47, sb6_48⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_49, sb6_50⟩, List.forall_mem_append.2 ⟨sb6_51, sb6_52⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_53, sb6_54⟩, List.forall_mem_append.2 ⟨sb6_55, sb6_56⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb6_57, sb6_58⟩, List.forall_mem_append.2 ⟨sb6_59, sb6_60⟩⟩⟩⟩⟩⟩
theorem cell_ok6 : cellCheck G f n Ps normsL cell6 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok6 (enumS_of_coverL cover6 subs6)
theorem cover7 : (coverL cell7.aL cell7.w 6 2 6 (fun _ => 0) (cell7.S * cell7.K) [] preL7).isSome = true := by decide +kernel
theorem subs7 : ∀ q ∈ preL7, sub7 q = true := by
  unfold preL7
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_0, List.forall_mem_append.2 ⟨sb7_1, sb7_2⟩⟩, List.forall_mem_append.2 ⟨sb7_3, List.forall_mem_append.2 ⟨sb7_4, sb7_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_6, List.forall_mem_append.2 ⟨sb7_7, sb7_8⟩⟩, List.forall_mem_append.2 ⟨sb7_9, List.forall_mem_append.2 ⟨sb7_10, sb7_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_12, List.forall_mem_append.2 ⟨sb7_13, sb7_14⟩⟩, List.forall_mem_append.2 ⟨sb7_15, List.forall_mem_append.2 ⟨sb7_16, sb7_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_18, List.forall_mem_append.2 ⟨sb7_19, sb7_20⟩⟩, List.forall_mem_append.2 ⟨sb7_21, List.forall_mem_append.2 ⟨sb7_22, sb7_23⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_24, List.forall_mem_append.2 ⟨sb7_25, sb7_26⟩⟩, List.forall_mem_append.2 ⟨sb7_27, List.forall_mem_append.2 ⟨sb7_28, sb7_29⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_30, List.forall_mem_append.2 ⟨sb7_31, sb7_32⟩⟩, List.forall_mem_append.2 ⟨sb7_33, List.forall_mem_append.2 ⟨sb7_34, sb7_35⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_36, List.forall_mem_append.2 ⟨sb7_37, sb7_38⟩⟩, List.forall_mem_append.2 ⟨sb7_39, List.forall_mem_append.2 ⟨sb7_40, sb7_41⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb7_42, List.forall_mem_append.2 ⟨sb7_43, sb7_44⟩⟩, List.forall_mem_append.2 ⟨sb7_45, List.forall_mem_append.2 ⟨sb7_46, sb7_47⟩⟩⟩⟩⟩⟩
theorem cell_ok7 : cellCheck G f n Ps normsL cell7 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok7 (enumS_of_coverL cover7 subs7)
theorem cover8 : (coverL cell8.aL cell8.w 6 2 6 (fun _ => 0) (cell8.S * cell8.K) [] preL8).isSome = true := by decide +kernel
theorem subs8 : ∀ q ∈ preL8, sub8 q = true := by
  unfold preL8
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_0, sb8_1⟩, List.forall_mem_append.2 ⟨sb8_2, List.forall_mem_append.2 ⟨sb8_3, sb8_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_5, sb8_6⟩, List.forall_mem_append.2 ⟨sb8_7, List.forall_mem_append.2 ⟨sb8_8, sb8_9⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_10, sb8_11⟩, List.forall_mem_append.2 ⟨sb8_12, List.forall_mem_append.2 ⟨sb8_13, sb8_14⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_15, List.forall_mem_append.2 ⟨sb8_16, sb8_17⟩⟩, List.forall_mem_append.2 ⟨sb8_18, List.forall_mem_append.2 ⟨sb8_19, sb8_20⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_21, sb8_22⟩, List.forall_mem_append.2 ⟨sb8_23, List.forall_mem_append.2 ⟨sb8_24, sb8_25⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_26, List.forall_mem_append.2 ⟨sb8_27, sb8_28⟩⟩, List.forall_mem_append.2 ⟨sb8_29, List.forall_mem_append.2 ⟨sb8_30, sb8_31⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_32, sb8_33⟩, List.forall_mem_append.2 ⟨sb8_34, List.forall_mem_append.2 ⟨sb8_35, sb8_36⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb8_37, List.forall_mem_append.2 ⟨sb8_38, sb8_39⟩⟩, List.forall_mem_append.2 ⟨sb8_40, List.forall_mem_append.2 ⟨sb8_41, sb8_42⟩⟩⟩⟩⟩⟩
theorem cell_ok8 : cellCheck G f n Ps normsL cell8 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok8 (enumS_of_coverL cover8 subs8)
theorem cover9 : (coverL cell9.aL cell9.w 6 2 6 (fun _ => 0) (cell9.S * cell9.K) [] preL9).isSome = true := by decide +kernel
theorem subs9 : ∀ q ∈ preL9, sub9 q = true := by
  unfold preL9
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_0, List.forall_mem_append.2 ⟨sb9_1, sb9_2⟩⟩, List.forall_mem_append.2 ⟨sb9_3, List.forall_mem_append.2 ⟨sb9_4, sb9_5⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_6, List.forall_mem_append.2 ⟨sb9_7, sb9_8⟩⟩, List.forall_mem_append.2 ⟨sb9_9, List.forall_mem_append.2 ⟨sb9_10, sb9_11⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_12, List.forall_mem_append.2 ⟨sb9_13, sb9_14⟩⟩, List.forall_mem_append.2 ⟨sb9_15, List.forall_mem_append.2 ⟨sb9_16, sb9_17⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_18, List.forall_mem_append.2 ⟨sb9_19, sb9_20⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_21, sb9_22⟩, List.forall_mem_append.2 ⟨sb9_23, sb9_24⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_25, List.forall_mem_append.2 ⟨sb9_26, sb9_27⟩⟩, List.forall_mem_append.2 ⟨sb9_28, List.forall_mem_append.2 ⟨sb9_29, sb9_30⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_31, List.forall_mem_append.2 ⟨sb9_32, sb9_33⟩⟩, List.forall_mem_append.2 ⟨sb9_34, List.forall_mem_append.2 ⟨sb9_35, sb9_36⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_37, List.forall_mem_append.2 ⟨sb9_38, sb9_39⟩⟩, List.forall_mem_append.2 ⟨sb9_40, List.forall_mem_append.2 ⟨sb9_41, sb9_42⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_43, List.forall_mem_append.2 ⟨sb9_44, sb9_45⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb9_46, sb9_47⟩, List.forall_mem_append.2 ⟨sb9_48, sb9_49⟩⟩⟩⟩⟩⟩
theorem cell_ok9 : cellCheck G f n Ps normsL cell9 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok9 (enumS_of_coverL cover9 subs9)
theorem cover10 : (coverL cell10.aL cell10.w 6 2 6 (fun _ => 0) (cell10.S * cell10.K) [] preL10).isSome = true := by decide +kernel
theorem subs10 : ∀ q ∈ preL10, sub10 q = true := by
  unfold preL10
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_0, sb10_1⟩, List.forall_mem_append.2 ⟨sb10_2, List.forall_mem_append.2 ⟨sb10_3, sb10_4⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_5, List.forall_mem_append.2 ⟨sb10_6, sb10_7⟩⟩, List.forall_mem_append.2 ⟨sb10_8, List.forall_mem_append.2 ⟨sb10_9, sb10_10⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_11, sb10_12⟩, List.forall_mem_append.2 ⟨sb10_13, List.forall_mem_append.2 ⟨sb10_14, sb10_15⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_16, List.forall_mem_append.2 ⟨sb10_17, sb10_18⟩⟩, List.forall_mem_append.2 ⟨sb10_19, List.forall_mem_append.2 ⟨sb10_20, sb10_21⟩⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_22, sb10_23⟩, List.forall_mem_append.2 ⟨sb10_24, List.forall_mem_append.2 ⟨sb10_25, sb10_26⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_27, List.forall_mem_append.2 ⟨sb10_28, sb10_29⟩⟩, List.forall_mem_append.2 ⟨sb10_30, List.forall_mem_append.2 ⟨sb10_31, sb10_32⟩⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_33, List.forall_mem_append.2 ⟨sb10_34, sb10_35⟩⟩, List.forall_mem_append.2 ⟨sb10_36, List.forall_mem_append.2 ⟨sb10_37, sb10_38⟩⟩⟩, List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨sb10_39, List.forall_mem_append.2 ⟨sb10_40, sb10_41⟩⟩, List.forall_mem_append.2 ⟨sb10_42, List.forall_mem_append.2 ⟨sb10_43, sb10_44⟩⟩⟩⟩⟩⟩
theorem cell_ok10 : cellCheck G f n Ps normsL cell10 = true :=
  cellCheck_fast4 (by decide +kernel) ld_ok10 (enumS_of_coverL cover10 subs10)
theorem cells_ok : ∀ k, k < nc → cellCheck G f n Ps normsL (cells k) = true := by
  intro k hk
  simp only [nc] at hk
  interval_cases k
  exacts [cell_ok0, cell_ok1, cell_ok2, cell_ok3, cell_ok4, cell_ok5, cell_ok6, cell_ok7, cell_ok8, cell_ok9, cell_ok10]

theorem hd : (0 : ℝ) < ((1 : ℤ) : ℝ) ^ 2 + 4 * ((1 : ℤ) : ℝ) := by norm_num

/-- The lattice is reflective (assuming Vinberg's chamber theorem). -/
theorem reflective (hV : VinbergChamber) : Reflective hd.le G := by
  haveI : IsPrincipalIdealRing OK := isPrincipalIdealRing (by norm_num)
  exact reflective_of_check hV (by
      have h := (inferInstance : Fact (¬ IsSquare (QuadraticAlgebra.discr (1 : ℤ) 1))).out
      rwa [QuadraticAlgebra.discr_def] at h) hd poly_ok adm_ok win_ok norms_eq chain_ok
    cells_ok

end ReflectZphi.Data.Cert5.C080
