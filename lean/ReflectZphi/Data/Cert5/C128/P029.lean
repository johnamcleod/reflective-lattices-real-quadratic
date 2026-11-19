import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_7_64 : subd5_7 [0, 2] = true := by decide +kernel
theorem subd5_7_65 : subd5_7 [0, 3] = true := by decide +kernel
theorem subd5_7_66 : subd5_7 [0, 4] = true := by decide +kernel
theorem subd5_7_67 : subd5_7 [0, 5] = true := by decide +kernel
theorem subd5_7_68 : subd5_7 [1, -7] = true := by decide +kernel
theorem subd5_7_69 : subd5_7 [1, -6] = true := by decide +kernel
theorem subd5_7_70 : subd5_7 [1, -5] = true := by decide +kernel
theorem subd5_7_71 : subd5_7 [1, -4] = true := by decide +kernel
theorem subd5_7_72 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_73 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_74 : subd5_7 [1, -1] = true := by decide +kernel
theorem subd5_7_75 : subd5_7 [1, 0] = true := by decide +kernel
theorem subd5_7_76 : subd5_7 [1, 1] = true := by decide +kernel
theorem subd5_7_77 : subd5_7 [1, 2] = true := by decide +kernel
theorem subd5_7_78 : subd5_7 [1, 3] = true := by decide +kernel
theorem subd5_7_79 : subd5_7 [1, 4] = true := by decide +kernel
theorem subd5_7_80 : subd5_7 [1, 5] = true := by decide +kernel
theorem subd5_7_81 : subd5_7 [2, -7] = true := by decide +kernel
theorem subd5_7_82 : subd5_7 [2, -6] = true := by decide +kernel
theorem subd5_7_83 : subd5_7 [2, -5] = true := by decide +kernel
theorem subd5_7_84 : subd5_7 [2, -4] = true := by decide +kernel
theorem subd5_7_85 : subd5_7 [2, -3] = true := by decide +kernel
theorem subd5_7_86 : subd5_7 [2, -2] = true := by decide +kernel
theorem subd5_7_87 : subd5_7 [2, -1] = true := by decide +kernel
theorem subd5_7_88 : subd5_7 [2, 0] = true := by decide +kernel
theorem subd5_7_89 : subd5_7 [2, 1] = true := by decide +kernel
theorem subd5_7_90 : subd5_7 [2, 2] = true := by decide +kernel
theorem subd5_7_91 : subd5_7 [2, 3] = true := by decide +kernel
theorem subd5_7_92 : subd5_7 [2, 4] = true := by decide +kernel
theorem subd5_7_93 : subd5_7 [2, 5] = true := by decide +kernel
theorem subd5_7_94 : subd5_7 [3, -6] = true := by decide +kernel
theorem subd5_7_95 : subd5_7 [3, -5] = true := by decide +kernel
theorem sbd5_7_2 : ∀ q ∈ blkd5_7_2, subd5_7 q = true := by
  unfold blkd5_7_2
  exact List.forall_mem_cons.2 ⟨subd5_7_64, List.forall_mem_cons.2 ⟨subd5_7_65, List.forall_mem_cons.2 ⟨subd5_7_66, List.forall_mem_cons.2 ⟨subd5_7_67, List.forall_mem_cons.2 ⟨subd5_7_68, List.forall_mem_cons.2 ⟨subd5_7_69, List.forall_mem_cons.2 ⟨subd5_7_70, List.forall_mem_cons.2 ⟨subd5_7_71, List.forall_mem_cons.2 ⟨subd5_7_72, List.forall_mem_cons.2 ⟨subd5_7_73, List.forall_mem_cons.2 ⟨subd5_7_74, List.forall_mem_cons.2 ⟨subd5_7_75, List.forall_mem_cons.2 ⟨subd5_7_76, List.forall_mem_cons.2 ⟨subd5_7_77, List.forall_mem_cons.2 ⟨subd5_7_78, List.forall_mem_cons.2 ⟨subd5_7_79, List.forall_mem_cons.2 ⟨subd5_7_80, List.forall_mem_cons.2 ⟨subd5_7_81, List.forall_mem_cons.2 ⟨subd5_7_82, List.forall_mem_cons.2 ⟨subd5_7_83, List.forall_mem_cons.2 ⟨subd5_7_84, List.forall_mem_cons.2 ⟨subd5_7_85, List.forall_mem_cons.2 ⟨subd5_7_86, List.forall_mem_cons.2 ⟨subd5_7_87, List.forall_mem_cons.2 ⟨subd5_7_88, List.forall_mem_cons.2 ⟨subd5_7_89, List.forall_mem_cons.2 ⟨subd5_7_90, List.forall_mem_cons.2 ⟨subd5_7_91, List.forall_mem_cons.2 ⟨subd5_7_92, List.forall_mem_cons.2 ⟨subd5_7_93, List.forall_mem_cons.2 ⟨subd5_7_94, List.forall_mem_cons.2 ⟨subd5_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_96 : subd5_7 [3, -4] = true := by decide +kernel
theorem subd5_7_97 : subd5_7 [3, -3] = true := by decide +kernel
theorem subd5_7_98 : subd5_7 [3, -2] = true := by decide +kernel
theorem subd5_7_99 : subd5_7 [3, -1] = true := by decide +kernel
theorem subd5_7_100 : subd5_7 [3, 0] = true := by decide +kernel
theorem subd5_7_101 : subd5_7 [3, 1] = true := by decide +kernel
theorem subd5_7_102 : subd5_7 [3, 2] = true := by decide +kernel
theorem subd5_7_103 : subd5_7 [3, 3] = true := by decide +kernel
theorem subd5_7_104 : subd5_7 [3, 4] = true := by decide +kernel
theorem subd5_7_105 : subd5_7 [4, -6] = true := by decide +kernel
theorem subd5_7_106 : subd5_7 [4, -5] = true := by decide +kernel
theorem subd5_7_107 : subd5_7 [4, -4] = true := by decide +kernel
theorem subd5_7_108 : subd5_7 [4, -3] = true := by decide +kernel
theorem subd5_7_109 : subd5_7 [4, -2] = true := by decide +kernel
theorem subd5_7_110 : subd5_7 [4, -1] = true := by decide +kernel
theorem subd5_7_111 : subd5_7 [4, 0] = true := by decide +kernel
theorem subd5_7_112 : subd5_7 [4, 1] = true := by decide +kernel
theorem subd5_7_113 : subd5_7 [4, 2] = true := by decide +kernel
theorem subd5_7_114 : subd5_7 [4, 3] = true := by decide +kernel
theorem subd5_7_115 : subd5_7 [5, -5] = true := by decide +kernel
theorem subd5_7_116 : subd5_7 [5, -4] = true := by decide +kernel
theorem subd5_7_117 : subd5_7 [5, -3] = true := by decide +kernel
theorem subd5_7_118 : subd5_7 [5, -2] = true := by decide +kernel
theorem subd5_7_119 : subd5_7 [5, -1] = true := by decide +kernel
theorem subd5_7_120 : subd5_7 [5, 0] = true := by decide +kernel
theorem subd5_7_121 : subd5_7 [5, 1] = true := by decide +kernel
theorem subd5_7_122 : subd5_7 [5, 2] = true := by decide +kernel
theorem subd5_7_123 : subd5_7 [6] = true := by decide +kernel
theorem sbd5_7_3 : ∀ q ∈ blkd5_7_3, subd5_7 q = true := by
  unfold blkd5_7_3
  exact List.forall_mem_cons.2 ⟨subd5_7_96, List.forall_mem_cons.2 ⟨subd5_7_97, List.forall_mem_cons.2 ⟨subd5_7_98, List.forall_mem_cons.2 ⟨subd5_7_99, List.forall_mem_cons.2 ⟨subd5_7_100, List.forall_mem_cons.2 ⟨subd5_7_101, List.forall_mem_cons.2 ⟨subd5_7_102, List.forall_mem_cons.2 ⟨subd5_7_103, List.forall_mem_cons.2 ⟨subd5_7_104, List.forall_mem_cons.2 ⟨subd5_7_105, List.forall_mem_cons.2 ⟨subd5_7_106, List.forall_mem_cons.2 ⟨subd5_7_107, List.forall_mem_cons.2 ⟨subd5_7_108, List.forall_mem_cons.2 ⟨subd5_7_109, List.forall_mem_cons.2 ⟨subd5_7_110, List.forall_mem_cons.2 ⟨subd5_7_111, List.forall_mem_cons.2 ⟨subd5_7_112, List.forall_mem_cons.2 ⟨subd5_7_113, List.forall_mem_cons.2 ⟨subd5_7_114, List.forall_mem_cons.2 ⟨subd5_7_115, List.forall_mem_cons.2 ⟨subd5_7_116, List.forall_mem_cons.2 ⟨subd5_7_117, List.forall_mem_cons.2 ⟨subd5_7_118, List.forall_mem_cons.2 ⟨subd5_7_119, List.forall_mem_cons.2 ⟨subd5_7_120, List.forall_mem_cons.2 ⟨subd5_7_121, List.forall_mem_cons.2 ⟨subd5_7_122, List.forall_mem_cons.2 ⟨subd5_7_123, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [2] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [3] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
