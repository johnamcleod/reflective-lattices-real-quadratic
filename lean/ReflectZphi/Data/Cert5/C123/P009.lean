import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_6_64 : subd4_6 [1, -4] = true := by decide +kernel
theorem subd4_6_65 : subd4_6 [1, -3] = true := by decide +kernel
theorem subd4_6_66 : subd4_6 [1, -2] = true := by decide +kernel
theorem subd4_6_67 : subd4_6 [1, -1] = true := by decide +kernel
theorem subd4_6_68 : subd4_6 [1, 0] = true := by decide +kernel
theorem subd4_6_69 : subd4_6 [1, 1] = true := by decide +kernel
theorem subd4_6_70 : subd4_6 [1, 2] = true := by decide +kernel
theorem subd4_6_71 : subd4_6 [1, 3] = true := by decide +kernel
theorem subd4_6_72 : subd4_6 [1, 4] = true := by decide +kernel
theorem subd4_6_73 : subd4_6 [1, 5] = true := by decide +kernel
theorem subd4_6_74 : subd4_6 [2, -7] = true := by decide +kernel
theorem subd4_6_75 : subd4_6 [2, -6] = true := by decide +kernel
theorem subd4_6_76 : subd4_6 [2, -5] = true := by decide +kernel
theorem subd4_6_77 : subd4_6 [2, -4] = true := by decide +kernel
theorem subd4_6_78 : subd4_6 [2, -3] = true := by decide +kernel
theorem subd4_6_79 : subd4_6 [2, -2] = true := by decide +kernel
theorem subd4_6_80 : subd4_6 [2, -1] = true := by decide +kernel
theorem subd4_6_81 : subd4_6 [2, 0] = true := by decide +kernel
theorem subd4_6_82 : subd4_6 [2, 1] = true := by decide +kernel
theorem subd4_6_83 : subd4_6 [2, 2] = true := by decide +kernel
theorem subd4_6_84 : subd4_6 [2, 3] = true := by decide +kernel
theorem subd4_6_85 : subd4_6 [2, 4] = true := by decide +kernel
theorem subd4_6_86 : subd4_6 [2, 5] = true := by decide +kernel
theorem subd4_6_87 : subd4_6 [3, -6] = true := by decide +kernel
theorem subd4_6_88 : subd4_6 [3, -5] = true := by decide +kernel
theorem subd4_6_89 : subd4_6 [3, -4] = true := by decide +kernel
theorem subd4_6_90 : subd4_6 [3, -3] = true := by decide +kernel
theorem subd4_6_91 : subd4_6 [3, -2] = true := by decide +kernel
theorem subd4_6_92 : subd4_6 [3, -1] = true := by decide +kernel
theorem subd4_6_93 : subd4_6 [3, 0] = true := by decide +kernel
theorem subd4_6_94 : subd4_6 [3, 1] = true := by decide +kernel
theorem subd4_6_95 : subd4_6 [3, 2] = true := by decide +kernel
theorem sbd4_6_2 : ∀ q ∈ blkd4_6_2, subd4_6 q = true := by
  unfold blkd4_6_2
  exact List.forall_mem_cons.2 ⟨subd4_6_64, List.forall_mem_cons.2 ⟨subd4_6_65, List.forall_mem_cons.2 ⟨subd4_6_66, List.forall_mem_cons.2 ⟨subd4_6_67, List.forall_mem_cons.2 ⟨subd4_6_68, List.forall_mem_cons.2 ⟨subd4_6_69, List.forall_mem_cons.2 ⟨subd4_6_70, List.forall_mem_cons.2 ⟨subd4_6_71, List.forall_mem_cons.2 ⟨subd4_6_72, List.forall_mem_cons.2 ⟨subd4_6_73, List.forall_mem_cons.2 ⟨subd4_6_74, List.forall_mem_cons.2 ⟨subd4_6_75, List.forall_mem_cons.2 ⟨subd4_6_76, List.forall_mem_cons.2 ⟨subd4_6_77, List.forall_mem_cons.2 ⟨subd4_6_78, List.forall_mem_cons.2 ⟨subd4_6_79, List.forall_mem_cons.2 ⟨subd4_6_80, List.forall_mem_cons.2 ⟨subd4_6_81, List.forall_mem_cons.2 ⟨subd4_6_82, List.forall_mem_cons.2 ⟨subd4_6_83, List.forall_mem_cons.2 ⟨subd4_6_84, List.forall_mem_cons.2 ⟨subd4_6_85, List.forall_mem_cons.2 ⟨subd4_6_86, List.forall_mem_cons.2 ⟨subd4_6_87, List.forall_mem_cons.2 ⟨subd4_6_88, List.forall_mem_cons.2 ⟨subd4_6_89, List.forall_mem_cons.2 ⟨subd4_6_90, List.forall_mem_cons.2 ⟨subd4_6_91, List.forall_mem_cons.2 ⟨subd4_6_92, List.forall_mem_cons.2 ⟨subd4_6_93, List.forall_mem_cons.2 ⟨subd4_6_94, List.forall_mem_cons.2 ⟨subd4_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_96 : subd4_6 [3, 3] = true := by decide +kernel
theorem subd4_6_97 : subd4_6 [3, 4] = true := by decide +kernel
theorem subd4_6_98 : subd4_6 [4, -6] = true := by decide +kernel
theorem subd4_6_99 : subd4_6 [4, -5] = true := by decide +kernel
theorem subd4_6_100 : subd4_6 [4, -4] = true := by decide +kernel
theorem subd4_6_101 : subd4_6 [4, -3] = true := by decide +kernel
theorem subd4_6_102 : subd4_6 [4, -2] = true := by decide +kernel
theorem subd4_6_103 : subd4_6 [4, -1] = true := by decide +kernel
theorem subd4_6_104 : subd4_6 [4, 0] = true := by decide +kernel
theorem subd4_6_105 : subd4_6 [4, 1] = true := by decide +kernel
theorem subd4_6_106 : subd4_6 [4, 2] = true := by decide +kernel
theorem subd4_6_107 : subd4_6 [5] = true := by decide +kernel
theorem sbd4_6_3 : ∀ q ∈ blkd4_6_3, subd4_6 q = true := by
  unfold blkd4_6_3
  exact List.forall_mem_cons.2 ⟨subd4_6_96, List.forall_mem_cons.2 ⟨subd4_6_97, List.forall_mem_cons.2 ⟨subd4_6_98, List.forall_mem_cons.2 ⟨subd4_6_99, List.forall_mem_cons.2 ⟨subd4_6_100, List.forall_mem_cons.2 ⟨subd4_6_101, List.forall_mem_cons.2 ⟨subd4_6_102, List.forall_mem_cons.2 ⟨subd4_6_103, List.forall_mem_cons.2 ⟨subd4_6_104, List.forall_mem_cons.2 ⟨subd4_6_105, List.forall_mem_cons.2 ⟨subd4_6_106, List.forall_mem_cons.2 ⟨subd4_6_107, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-1] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [0] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [2] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-2] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-1, 0] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [0, 0] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [1, 0] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [2] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-2] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [0] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [2] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
