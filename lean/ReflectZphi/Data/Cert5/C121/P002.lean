import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd2_2_32 : subd2_2 [-1, 4] = true := by decide +kernel
theorem subd2_2_33 : subd2_2 [-1, 5] = true := by decide +kernel
theorem subd2_2_34 : subd2_2 [0, -6] = true := by decide +kernel
theorem subd2_2_35 : subd2_2 [0, -5] = true := by decide +kernel
theorem subd2_2_36 : subd2_2 [0, -4] = true := by decide +kernel
theorem subd2_2_37 : subd2_2 [0, -3] = true := by decide +kernel
theorem subd2_2_38 : subd2_2 [0, -2] = true := by decide +kernel
theorem subd2_2_39 : subd2_2 [0, -1] = true := by decide +kernel
theorem subd2_2_40 : subd2_2 [0, 0] = true := by decide +kernel
theorem subd2_2_41 : subd2_2 [0, 1] = true := by decide +kernel
theorem subd2_2_42 : subd2_2 [0, 2] = true := by decide +kernel
theorem subd2_2_43 : subd2_2 [0, 3] = true := by decide +kernel
theorem subd2_2_44 : subd2_2 [0, 4] = true := by decide +kernel
theorem subd2_2_45 : subd2_2 [0, 5] = true := by decide +kernel
theorem subd2_2_46 : subd2_2 [1, -6] = true := by decide +kernel
theorem subd2_2_47 : subd2_2 [1, -5] = true := by decide +kernel
theorem subd2_2_48 : subd2_2 [1, -4] = true := by decide +kernel
theorem subd2_2_49 : subd2_2 [1, -3] = true := by decide +kernel
theorem subd2_2_50 : subd2_2 [1, -2] = true := by decide +kernel
theorem subd2_2_51 : subd2_2 [1, -1] = true := by decide +kernel
theorem subd2_2_52 : subd2_2 [1, 0] = true := by decide +kernel
theorem subd2_2_53 : subd2_2 [1, 1] = true := by decide +kernel
theorem subd2_2_54 : subd2_2 [1, 2] = true := by decide +kernel
theorem subd2_2_55 : subd2_2 [1, 3] = true := by decide +kernel
theorem subd2_2_56 : subd2_2 [1, 4] = true := by decide +kernel
theorem subd2_2_57 : subd2_2 [1, 5] = true := by decide +kernel
theorem subd2_2_58 : subd2_2 [2, -6] = true := by decide +kernel
theorem subd2_2_59 : subd2_2 [2, -5] = true := by decide +kernel
theorem subd2_2_60 : subd2_2 [2, -4] = true := by decide +kernel
theorem subd2_2_61 : subd2_2 [2, -3] = true := by decide +kernel
theorem subd2_2_62 : subd2_2 [2, -2] = true := by decide +kernel
theorem subd2_2_63 : subd2_2 [2, -1] = true := by decide +kernel
theorem sbd2_2_1 : ∀ q ∈ blkd2_2_1, subd2_2 q = true := by
  unfold blkd2_2_1
  exact List.forall_mem_cons.2 ⟨subd2_2_32, List.forall_mem_cons.2 ⟨subd2_2_33, List.forall_mem_cons.2 ⟨subd2_2_34, List.forall_mem_cons.2 ⟨subd2_2_35, List.forall_mem_cons.2 ⟨subd2_2_36, List.forall_mem_cons.2 ⟨subd2_2_37, List.forall_mem_cons.2 ⟨subd2_2_38, List.forall_mem_cons.2 ⟨subd2_2_39, List.forall_mem_cons.2 ⟨subd2_2_40, List.forall_mem_cons.2 ⟨subd2_2_41, List.forall_mem_cons.2 ⟨subd2_2_42, List.forall_mem_cons.2 ⟨subd2_2_43, List.forall_mem_cons.2 ⟨subd2_2_44, List.forall_mem_cons.2 ⟨subd2_2_45, List.forall_mem_cons.2 ⟨subd2_2_46, List.forall_mem_cons.2 ⟨subd2_2_47, List.forall_mem_cons.2 ⟨subd2_2_48, List.forall_mem_cons.2 ⟨subd2_2_49, List.forall_mem_cons.2 ⟨subd2_2_50, List.forall_mem_cons.2 ⟨subd2_2_51, List.forall_mem_cons.2 ⟨subd2_2_52, List.forall_mem_cons.2 ⟨subd2_2_53, List.forall_mem_cons.2 ⟨subd2_2_54, List.forall_mem_cons.2 ⟨subd2_2_55, List.forall_mem_cons.2 ⟨subd2_2_56, List.forall_mem_cons.2 ⟨subd2_2_57, List.forall_mem_cons.2 ⟨subd2_2_58, List.forall_mem_cons.2 ⟨subd2_2_59, List.forall_mem_cons.2 ⟨subd2_2_60, List.forall_mem_cons.2 ⟨subd2_2_61, List.forall_mem_cons.2 ⟨subd2_2_62, List.forall_mem_cons.2 ⟨subd2_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_2_64 : subd2_2 [2, 0] = true := by decide +kernel
theorem subd2_2_65 : subd2_2 [2, 1] = true := by decide +kernel
theorem subd2_2_66 : subd2_2 [2, 2] = true := by decide +kernel
theorem subd2_2_67 : subd2_2 [2, 3] = true := by decide +kernel
theorem subd2_2_68 : subd2_2 [2, 4] = true := by decide +kernel
theorem subd2_2_69 : subd2_2 [3, -6] = true := by decide +kernel
theorem subd2_2_70 : subd2_2 [3, -5] = true := by decide +kernel
theorem subd2_2_71 : subd2_2 [3, -4] = true := by decide +kernel
theorem subd2_2_72 : subd2_2 [3, -3] = true := by decide +kernel
theorem subd2_2_73 : subd2_2 [3, -2] = true := by decide +kernel
theorem subd2_2_74 : subd2_2 [3, -1] = true := by decide +kernel
theorem subd2_2_75 : subd2_2 [3, 0] = true := by decide +kernel
theorem subd2_2_76 : subd2_2 [3, 1] = true := by decide +kernel
theorem subd2_2_77 : subd2_2 [3, 2] = true := by decide +kernel
theorem subd2_2_78 : subd2_2 [3, 3] = true := by decide +kernel
theorem subd2_2_79 : subd2_2 [4] = true := by decide +kernel
theorem sbd2_2_2 : ∀ q ∈ blkd2_2_2, subd2_2 q = true := by
  unfold blkd2_2_2
  exact List.forall_mem_cons.2 ⟨subd2_2_64, List.forall_mem_cons.2 ⟨subd2_2_65, List.forall_mem_cons.2 ⟨subd2_2_66, List.forall_mem_cons.2 ⟨subd2_2_67, List.forall_mem_cons.2 ⟨subd2_2_68, List.forall_mem_cons.2 ⟨subd2_2_69, List.forall_mem_cons.2 ⟨subd2_2_70, List.forall_mem_cons.2 ⟨subd2_2_71, List.forall_mem_cons.2 ⟨subd2_2_72, List.forall_mem_cons.2 ⟨subd2_2_73, List.forall_mem_cons.2 ⟨subd2_2_74, List.forall_mem_cons.2 ⟨subd2_2_75, List.forall_mem_cons.2 ⟨subd2_2_76, List.forall_mem_cons.2 ⟨subd2_2_77, List.forall_mem_cons.2 ⟨subd2_2_78, List.forall_mem_cons.2 ⟨subd2_2_79, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [-2] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [-1] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [0, -3] = true := by decide +kernel
theorem subd2_3_3 : subd2_3 [0, -2] = true := by decide +kernel
theorem subd2_3_4 : subd2_3 [0, -1] = true := by decide +kernel
theorem subd2_3_5 : subd2_3 [0, 0] = true := by decide +kernel
theorem subd2_3_6 : subd2_3 [0, 1] = true := by decide +kernel
theorem subd2_3_7 : subd2_3 [0, 2] = true := by decide +kernel
theorem subd2_3_8 : subd2_3 [1] = true := by decide +kernel
theorem subd2_3_9 : subd2_3 [2] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_cons.2 ⟨subd2_3_3, List.forall_mem_cons.2 ⟨subd2_3_4, List.forall_mem_cons.2 ⟨subd2_3_5, List.forall_mem_cons.2 ⟨subd2_3_6, List.forall_mem_cons.2 ⟨subd2_3_7, List.forall_mem_cons.2 ⟨subd2_3_8, List.forall_mem_cons.2 ⟨subd2_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_nil _⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1, -3] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_18 : subd3_1 [1, 2] = true := by decide +kernel
theorem subd3_1_19 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_cons.2 ⟨subd3_1_18, List.forall_mem_cons.2 ⟨subd3_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C121
