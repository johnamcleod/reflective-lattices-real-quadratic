import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_7_32 : subd3_7 [-1, -4] = true := by decide +kernel
theorem subd3_7_33 : subd3_7 [-1, -3] = true := by decide +kernel
theorem subd3_7_34 : subd3_7 [-1, -2] = true := by decide +kernel
theorem subd3_7_35 : subd3_7 [-1, -1] = true := by decide +kernel
theorem subd3_7_36 : subd3_7 [-1, 0] = true := by decide +kernel
theorem subd3_7_37 : subd3_7 [-1, 1] = true := by decide +kernel
theorem subd3_7_38 : subd3_7 [-1, 2] = true := by decide +kernel
theorem subd3_7_39 : subd3_7 [-1, 3] = true := by decide +kernel
theorem subd3_7_40 : subd3_7 [-1, 4] = true := by decide +kernel
theorem subd3_7_41 : subd3_7 [-1, 5] = true := by decide +kernel
theorem subd3_7_42 : subd3_7 [0, -6] = true := by decide +kernel
theorem subd3_7_43 : subd3_7 [0, -5] = true := by decide +kernel
theorem subd3_7_44 : subd3_7 [0, -4] = true := by decide +kernel
theorem subd3_7_45 : subd3_7 [0, -3] = true := by decide +kernel
theorem subd3_7_46 : subd3_7 [0, -2] = true := by decide +kernel
theorem subd3_7_47 : subd3_7 [0, -1] = true := by decide +kernel
theorem subd3_7_48 : subd3_7 [0, 0] = true := by decide +kernel
theorem subd3_7_49 : subd3_7 [0, 1] = true := by decide +kernel
theorem subd3_7_50 : subd3_7 [0, 2] = true := by decide +kernel
theorem subd3_7_51 : subd3_7 [0, 3] = true := by decide +kernel
theorem subd3_7_52 : subd3_7 [0, 4] = true := by decide +kernel
theorem subd3_7_53 : subd3_7 [0, 5] = true := by decide +kernel
theorem subd3_7_54 : subd3_7 [1, -6] = true := by decide +kernel
theorem subd3_7_55 : subd3_7 [1, -5] = true := by decide +kernel
theorem subd3_7_56 : subd3_7 [1, -4] = true := by decide +kernel
theorem subd3_7_57 : subd3_7 [1, -3] = true := by decide +kernel
theorem subd3_7_58 : subd3_7 [1, -2] = true := by decide +kernel
theorem subd3_7_59 : subd3_7 [1, -1] = true := by decide +kernel
theorem subd3_7_60 : subd3_7 [1, 0] = true := by decide +kernel
theorem subd3_7_61 : subd3_7 [1, 1] = true := by decide +kernel
theorem subd3_7_62 : subd3_7 [1, 2] = true := by decide +kernel
theorem subd3_7_63 : subd3_7 [1, 3] = true := by decide +kernel
theorem sbd3_7_1 : ∀ q ∈ blkd3_7_1, subd3_7 q = true := by
  unfold blkd3_7_1
  exact List.forall_mem_cons.2 ⟨subd3_7_32, List.forall_mem_cons.2 ⟨subd3_7_33, List.forall_mem_cons.2 ⟨subd3_7_34, List.forall_mem_cons.2 ⟨subd3_7_35, List.forall_mem_cons.2 ⟨subd3_7_36, List.forall_mem_cons.2 ⟨subd3_7_37, List.forall_mem_cons.2 ⟨subd3_7_38, List.forall_mem_cons.2 ⟨subd3_7_39, List.forall_mem_cons.2 ⟨subd3_7_40, List.forall_mem_cons.2 ⟨subd3_7_41, List.forall_mem_cons.2 ⟨subd3_7_42, List.forall_mem_cons.2 ⟨subd3_7_43, List.forall_mem_cons.2 ⟨subd3_7_44, List.forall_mem_cons.2 ⟨subd3_7_45, List.forall_mem_cons.2 ⟨subd3_7_46, List.forall_mem_cons.2 ⟨subd3_7_47, List.forall_mem_cons.2 ⟨subd3_7_48, List.forall_mem_cons.2 ⟨subd3_7_49, List.forall_mem_cons.2 ⟨subd3_7_50, List.forall_mem_cons.2 ⟨subd3_7_51, List.forall_mem_cons.2 ⟨subd3_7_52, List.forall_mem_cons.2 ⟨subd3_7_53, List.forall_mem_cons.2 ⟨subd3_7_54, List.forall_mem_cons.2 ⟨subd3_7_55, List.forall_mem_cons.2 ⟨subd3_7_56, List.forall_mem_cons.2 ⟨subd3_7_57, List.forall_mem_cons.2 ⟨subd3_7_58, List.forall_mem_cons.2 ⟨subd3_7_59, List.forall_mem_cons.2 ⟨subd3_7_60, List.forall_mem_cons.2 ⟨subd3_7_61, List.forall_mem_cons.2 ⟨subd3_7_62, List.forall_mem_cons.2 ⟨subd3_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_7_64 : subd3_7 [1, 4] = true := by decide +kernel
theorem subd3_7_65 : subd3_7 [1, 5] = true := by decide +kernel
theorem subd3_7_66 : subd3_7 [2, -5] = true := by decide +kernel
theorem subd3_7_67 : subd3_7 [2, -4] = true := by decide +kernel
theorem subd3_7_68 : subd3_7 [2, -3] = true := by decide +kernel
theorem subd3_7_69 : subd3_7 [2, -2] = true := by decide +kernel
theorem subd3_7_70 : subd3_7 [2, -1] = true := by decide +kernel
theorem subd3_7_71 : subd3_7 [2, 0] = true := by decide +kernel
theorem subd3_7_72 : subd3_7 [2, 1] = true := by decide +kernel
theorem subd3_7_73 : subd3_7 [2, 2] = true := by decide +kernel
theorem subd3_7_74 : subd3_7 [2, 3] = true := by decide +kernel
theorem subd3_7_75 : subd3_7 [2, 4] = true := by decide +kernel
theorem subd3_7_76 : subd3_7 [2, 5] = true := by decide +kernel
theorem subd3_7_77 : subd3_7 [3, -4] = true := by decide +kernel
theorem subd3_7_78 : subd3_7 [3, -3] = true := by decide +kernel
theorem subd3_7_79 : subd3_7 [3, -2] = true := by decide +kernel
theorem subd3_7_80 : subd3_7 [3, -1] = true := by decide +kernel
theorem subd3_7_81 : subd3_7 [3, 0] = true := by decide +kernel
theorem subd3_7_82 : subd3_7 [3, 1] = true := by decide +kernel
theorem subd3_7_83 : subd3_7 [3, 2] = true := by decide +kernel
theorem subd3_7_84 : subd3_7 [3, 3] = true := by decide +kernel
theorem subd3_7_85 : subd3_7 [3, 4] = true := by decide +kernel
theorem subd3_7_86 : subd3_7 [3, 5] = true := by decide +kernel
theorem subd3_7_87 : subd3_7 [4, -3] = true := by decide +kernel
theorem subd3_7_88 : subd3_7 [4, -2] = true := by decide +kernel
theorem subd3_7_89 : subd3_7 [4, -1] = true := by decide +kernel
theorem subd3_7_90 : subd3_7 [4, 0] = true := by decide +kernel
theorem subd3_7_91 : subd3_7 [4, 1] = true := by decide +kernel
theorem subd3_7_92 : subd3_7 [4, 2] = true := by decide +kernel
theorem subd3_7_93 : subd3_7 [4, 3] = true := by decide +kernel
theorem subd3_7_94 : subd3_7 [4, 4] = true := by decide +kernel
theorem subd3_7_95 : subd3_7 [5] = true := by decide +kernel
theorem sbd3_7_2 : ∀ q ∈ blkd3_7_2, subd3_7 q = true := by
  unfold blkd3_7_2
  exact List.forall_mem_cons.2 ⟨subd3_7_64, List.forall_mem_cons.2 ⟨subd3_7_65, List.forall_mem_cons.2 ⟨subd3_7_66, List.forall_mem_cons.2 ⟨subd3_7_67, List.forall_mem_cons.2 ⟨subd3_7_68, List.forall_mem_cons.2 ⟨subd3_7_69, List.forall_mem_cons.2 ⟨subd3_7_70, List.forall_mem_cons.2 ⟨subd3_7_71, List.forall_mem_cons.2 ⟨subd3_7_72, List.forall_mem_cons.2 ⟨subd3_7_73, List.forall_mem_cons.2 ⟨subd3_7_74, List.forall_mem_cons.2 ⟨subd3_7_75, List.forall_mem_cons.2 ⟨subd3_7_76, List.forall_mem_cons.2 ⟨subd3_7_77, List.forall_mem_cons.2 ⟨subd3_7_78, List.forall_mem_cons.2 ⟨subd3_7_79, List.forall_mem_cons.2 ⟨subd3_7_80, List.forall_mem_cons.2 ⟨subd3_7_81, List.forall_mem_cons.2 ⟨subd3_7_82, List.forall_mem_cons.2 ⟨subd3_7_83, List.forall_mem_cons.2 ⟨subd3_7_84, List.forall_mem_cons.2 ⟨subd3_7_85, List.forall_mem_cons.2 ⟨subd3_7_86, List.forall_mem_cons.2 ⟨subd3_7_87, List.forall_mem_cons.2 ⟨subd3_7_88, List.forall_mem_cons.2 ⟨subd3_7_89, List.forall_mem_cons.2 ⟨subd3_7_90, List.forall_mem_cons.2 ⟨subd3_7_91, List.forall_mem_cons.2 ⟨subd3_7_92, List.forall_mem_cons.2 ⟨subd3_7_93, List.forall_mem_cons.2 ⟨subd3_7_94, List.forall_mem_cons.2 ⟨subd3_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [1, 1] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
