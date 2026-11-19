import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_4_32 : subd12_4 [0, -3] = true := by decide +kernel
theorem subd12_4_33 : subd12_4 [0, -2] = true := by decide +kernel
theorem subd12_4_34 : subd12_4 [0, -1] = true := by decide +kernel
theorem subd12_4_35 : subd12_4 [0, 0] = true := by decide +kernel
theorem subd12_4_36 : subd12_4 [0, 1] = true := by decide +kernel
theorem subd12_4_37 : subd12_4 [0, 2] = true := by decide +kernel
theorem subd12_4_38 : subd12_4 [0, 3] = true := by decide +kernel
theorem subd12_4_39 : subd12_4 [0, 4] = true := by decide +kernel
theorem subd12_4_40 : subd12_4 [1, -5] = true := by decide +kernel
theorem subd12_4_41 : subd12_4 [1, -4] = true := by decide +kernel
theorem subd12_4_42 : subd12_4 [1, -3] = true := by decide +kernel
theorem subd12_4_43 : subd12_4 [1, -2] = true := by decide +kernel
theorem subd12_4_44 : subd12_4 [1, -1] = true := by decide +kernel
theorem subd12_4_45 : subd12_4 [1, 0] = true := by decide +kernel
theorem subd12_4_46 : subd12_4 [1, 1] = true := by decide +kernel
theorem subd12_4_47 : subd12_4 [1, 2] = true := by decide +kernel
theorem subd12_4_48 : subd12_4 [1, 3] = true := by decide +kernel
theorem subd12_4_49 : subd12_4 [1, 4] = true := by decide +kernel
theorem subd12_4_50 : subd12_4 [2, -5] = true := by decide +kernel
theorem subd12_4_51 : subd12_4 [2, -4] = true := by decide +kernel
theorem subd12_4_52 : subd12_4 [2, -3] = true := by decide +kernel
theorem subd12_4_53 : subd12_4 [2, -2] = true := by decide +kernel
theorem subd12_4_54 : subd12_4 [2, -1] = true := by decide +kernel
theorem subd12_4_55 : subd12_4 [2, 0] = true := by decide +kernel
theorem subd12_4_56 : subd12_4 [2, 1] = true := by decide +kernel
theorem subd12_4_57 : subd12_4 [2, 2] = true := by decide +kernel
theorem subd12_4_58 : subd12_4 [2, 3] = true := by decide +kernel
theorem subd12_4_59 : subd12_4 [2, 4] = true := by decide +kernel
theorem subd12_4_60 : subd12_4 [3, -4] = true := by decide +kernel
theorem subd12_4_61 : subd12_4 [3, -3] = true := by decide +kernel
theorem subd12_4_62 : subd12_4 [3, -2] = true := by decide +kernel
theorem subd12_4_63 : subd12_4 [3, -1] = true := by decide +kernel
theorem sbd12_4_1 : ∀ q ∈ blkd12_4_1, subd12_4 q = true := by
  unfold blkd12_4_1
  exact List.forall_mem_cons.2 ⟨subd12_4_32, List.forall_mem_cons.2 ⟨subd12_4_33, List.forall_mem_cons.2 ⟨subd12_4_34, List.forall_mem_cons.2 ⟨subd12_4_35, List.forall_mem_cons.2 ⟨subd12_4_36, List.forall_mem_cons.2 ⟨subd12_4_37, List.forall_mem_cons.2 ⟨subd12_4_38, List.forall_mem_cons.2 ⟨subd12_4_39, List.forall_mem_cons.2 ⟨subd12_4_40, List.forall_mem_cons.2 ⟨subd12_4_41, List.forall_mem_cons.2 ⟨subd12_4_42, List.forall_mem_cons.2 ⟨subd12_4_43, List.forall_mem_cons.2 ⟨subd12_4_44, List.forall_mem_cons.2 ⟨subd12_4_45, List.forall_mem_cons.2 ⟨subd12_4_46, List.forall_mem_cons.2 ⟨subd12_4_47, List.forall_mem_cons.2 ⟨subd12_4_48, List.forall_mem_cons.2 ⟨subd12_4_49, List.forall_mem_cons.2 ⟨subd12_4_50, List.forall_mem_cons.2 ⟨subd12_4_51, List.forall_mem_cons.2 ⟨subd12_4_52, List.forall_mem_cons.2 ⟨subd12_4_53, List.forall_mem_cons.2 ⟨subd12_4_54, List.forall_mem_cons.2 ⟨subd12_4_55, List.forall_mem_cons.2 ⟨subd12_4_56, List.forall_mem_cons.2 ⟨subd12_4_57, List.forall_mem_cons.2 ⟨subd12_4_58, List.forall_mem_cons.2 ⟨subd12_4_59, List.forall_mem_cons.2 ⟨subd12_4_60, List.forall_mem_cons.2 ⟨subd12_4_61, List.forall_mem_cons.2 ⟨subd12_4_62, List.forall_mem_cons.2 ⟨subd12_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_4_64 : subd12_4 [3, 0] = true := by decide +kernel
theorem subd12_4_65 : subd12_4 [3, 1] = true := by decide +kernel
theorem subd12_4_66 : subd12_4 [3, 2] = true := by decide +kernel
theorem subd12_4_67 : subd12_4 [3, 3] = true := by decide +kernel
theorem subd12_4_68 : subd12_4 [3, 4] = true := by decide +kernel
theorem subd12_4_69 : subd12_4 [4] = true := by decide +kernel
theorem sbd12_4_2 : ∀ q ∈ blkd12_4_2, subd12_4 q = true := by
  unfold blkd12_4_2
  exact List.forall_mem_cons.2 ⟨subd12_4_64, List.forall_mem_cons.2 ⟨subd12_4_65, List.forall_mem_cons.2 ⟨subd12_4_66, List.forall_mem_cons.2 ⟨subd12_4_67, List.forall_mem_cons.2 ⟨subd12_4_68, List.forall_mem_cons.2 ⟨subd12_4_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd12_5 : ldCheck G d12_5.U d12_5.ms ldd12_5 = true := by decide +kernel
theorem pre_okd12_5 : subPre G cell12 d12_5 = true := by decide +kernel
theorem subd12_5_0 : subd12_5 [-2] = true := by decide +kernel
theorem subd12_5_1 : subd12_5 [-1] = true := by decide +kernel
theorem subd12_5_2 : subd12_5 [0, -3] = true := by decide +kernel
theorem subd12_5_3 : subd12_5 [0, -2] = true := by decide +kernel
theorem subd12_5_4 : subd12_5 [0, -1] = true := by decide +kernel
theorem subd12_5_5 : subd12_5 [0, 0] = true := by decide +kernel
theorem subd12_5_6 : subd12_5 [0, 1] = true := by decide +kernel
theorem subd12_5_7 : subd12_5 [0, 2] = true := by decide +kernel
theorem subd12_5_8 : subd12_5 [1] = true := by decide +kernel
theorem subd12_5_9 : subd12_5 [2] = true := by decide +kernel
theorem sbd12_5_0 : ∀ q ∈ blkd12_5_0, subd12_5 q = true := by
  unfold blkd12_5_0
  exact List.forall_mem_cons.2 ⟨subd12_5_0, List.forall_mem_cons.2 ⟨subd12_5_1, List.forall_mem_cons.2 ⟨subd12_5_2, List.forall_mem_cons.2 ⟨subd12_5_3, List.forall_mem_cons.2 ⟨subd12_5_4, List.forall_mem_cons.2 ⟨subd12_5_5, List.forall_mem_cons.2 ⟨subd12_5_6, List.forall_mem_cons.2 ⟨subd12_5_7, List.forall_mem_cons.2 ⟨subd12_5_8, List.forall_mem_cons.2 ⟨subd12_5_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-1] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [0] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [1] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_nil _⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-2] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-1] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [0] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [1] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [2] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C140
