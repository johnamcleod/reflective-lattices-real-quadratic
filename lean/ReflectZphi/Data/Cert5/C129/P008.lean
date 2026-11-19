import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_64 : subd6_1 [0, 4] = true := by decide +kernel
theorem subd6_1_65 : subd6_1 [0, 5] = true := by decide +kernel
theorem subd6_1_66 : subd6_1 [1, -7] = true := by decide +kernel
theorem subd6_1_67 : subd6_1 [1, -6] = true := by decide +kernel
theorem subd6_1_68 : subd6_1 [1, -5] = true := by decide +kernel
theorem subd6_1_69 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_70 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_71 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_72 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_73 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_74 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_75 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_76 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_77 : subd6_1 [1, 4] = true := by decide +kernel
theorem subd6_1_78 : subd6_1 [1, 5] = true := by decide +kernel
theorem subd6_1_79 : subd6_1 [2, -7] = true := by decide +kernel
theorem subd6_1_80 : subd6_1 [2, -6] = true := by decide +kernel
theorem subd6_1_81 : subd6_1 [2, -5] = true := by decide +kernel
theorem subd6_1_82 : subd6_1 [2, -4] = true := by decide +kernel
theorem subd6_1_83 : subd6_1 [2, -3] = true := by decide +kernel
theorem subd6_1_84 : subd6_1 [2, -2] = true := by decide +kernel
theorem subd6_1_85 : subd6_1 [2, -1] = true := by decide +kernel
theorem subd6_1_86 : subd6_1 [2, 0] = true := by decide +kernel
theorem subd6_1_87 : subd6_1 [2, 1] = true := by decide +kernel
theorem subd6_1_88 : subd6_1 [2, 2] = true := by decide +kernel
theorem subd6_1_89 : subd6_1 [2, 3] = true := by decide +kernel
theorem subd6_1_90 : subd6_1 [2, 4] = true := by decide +kernel
theorem subd6_1_91 : subd6_1 [3, -7] = true := by decide +kernel
theorem subd6_1_92 : subd6_1 [3, -6] = true := by decide +kernel
theorem subd6_1_93 : subd6_1 [3, -5] = true := by decide +kernel
theorem subd6_1_94 : subd6_1 [3, -4] = true := by decide +kernel
theorem subd6_1_95 : subd6_1 [3, -3] = true := by decide +kernel
theorem sbd6_1_2 : ∀ q ∈ blkd6_1_2, subd6_1 q = true := by
  unfold blkd6_1_2
  exact List.forall_mem_cons.2 ⟨subd6_1_64, List.forall_mem_cons.2 ⟨subd6_1_65, List.forall_mem_cons.2 ⟨subd6_1_66, List.forall_mem_cons.2 ⟨subd6_1_67, List.forall_mem_cons.2 ⟨subd6_1_68, List.forall_mem_cons.2 ⟨subd6_1_69, List.forall_mem_cons.2 ⟨subd6_1_70, List.forall_mem_cons.2 ⟨subd6_1_71, List.forall_mem_cons.2 ⟨subd6_1_72, List.forall_mem_cons.2 ⟨subd6_1_73, List.forall_mem_cons.2 ⟨subd6_1_74, List.forall_mem_cons.2 ⟨subd6_1_75, List.forall_mem_cons.2 ⟨subd6_1_76, List.forall_mem_cons.2 ⟨subd6_1_77, List.forall_mem_cons.2 ⟨subd6_1_78, List.forall_mem_cons.2 ⟨subd6_1_79, List.forall_mem_cons.2 ⟨subd6_1_80, List.forall_mem_cons.2 ⟨subd6_1_81, List.forall_mem_cons.2 ⟨subd6_1_82, List.forall_mem_cons.2 ⟨subd6_1_83, List.forall_mem_cons.2 ⟨subd6_1_84, List.forall_mem_cons.2 ⟨subd6_1_85, List.forall_mem_cons.2 ⟨subd6_1_86, List.forall_mem_cons.2 ⟨subd6_1_87, List.forall_mem_cons.2 ⟨subd6_1_88, List.forall_mem_cons.2 ⟨subd6_1_89, List.forall_mem_cons.2 ⟨subd6_1_90, List.forall_mem_cons.2 ⟨subd6_1_91, List.forall_mem_cons.2 ⟨subd6_1_92, List.forall_mem_cons.2 ⟨subd6_1_93, List.forall_mem_cons.2 ⟨subd6_1_94, List.forall_mem_cons.2 ⟨subd6_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_96 : subd6_1 [3, -2] = true := by decide +kernel
theorem subd6_1_97 : subd6_1 [3, -1] = true := by decide +kernel
theorem subd6_1_98 : subd6_1 [3, 0] = true := by decide +kernel
theorem subd6_1_99 : subd6_1 [3, 1] = true := by decide +kernel
theorem subd6_1_100 : subd6_1 [3, 2] = true := by decide +kernel
theorem subd6_1_101 : subd6_1 [3, 3] = true := by decide +kernel
theorem subd6_1_102 : subd6_1 [4, -6] = true := by decide +kernel
theorem subd6_1_103 : subd6_1 [4, -5] = true := by decide +kernel
theorem subd6_1_104 : subd6_1 [4, -4] = true := by decide +kernel
theorem subd6_1_105 : subd6_1 [4, -3] = true := by decide +kernel
theorem subd6_1_106 : subd6_1 [4, -2] = true := by decide +kernel
theorem subd6_1_107 : subd6_1 [4, -1] = true := by decide +kernel
theorem subd6_1_108 : subd6_1 [4, 0] = true := by decide +kernel
theorem subd6_1_109 : subd6_1 [4, 1] = true := by decide +kernel
theorem subd6_1_110 : subd6_1 [4, 2] = true := by decide +kernel
theorem subd6_1_111 : subd6_1 [5, -6] = true := by decide +kernel
theorem subd6_1_112 : subd6_1 [5, -5] = true := by decide +kernel
theorem subd6_1_113 : subd6_1 [5, -4] = true := by decide +kernel
theorem subd6_1_114 : subd6_1 [5, -3] = true := by decide +kernel
theorem subd6_1_115 : subd6_1 [5, -2] = true := by decide +kernel
theorem subd6_1_116 : subd6_1 [5, -1] = true := by decide +kernel
theorem subd6_1_117 : subd6_1 [5, 0] = true := by decide +kernel
theorem subd6_1_118 : subd6_1 [5, 1] = true := by decide +kernel
theorem subd6_1_119 : subd6_1 [6] = true := by decide +kernel
theorem sbd6_1_3 : ∀ q ∈ blkd6_1_3, subd6_1 q = true := by
  unfold blkd6_1_3
  exact List.forall_mem_cons.2 ⟨subd6_1_96, List.forall_mem_cons.2 ⟨subd6_1_97, List.forall_mem_cons.2 ⟨subd6_1_98, List.forall_mem_cons.2 ⟨subd6_1_99, List.forall_mem_cons.2 ⟨subd6_1_100, List.forall_mem_cons.2 ⟨subd6_1_101, List.forall_mem_cons.2 ⟨subd6_1_102, List.forall_mem_cons.2 ⟨subd6_1_103, List.forall_mem_cons.2 ⟨subd6_1_104, List.forall_mem_cons.2 ⟨subd6_1_105, List.forall_mem_cons.2 ⟨subd6_1_106, List.forall_mem_cons.2 ⟨subd6_1_107, List.forall_mem_cons.2 ⟨subd6_1_108, List.forall_mem_cons.2 ⟨subd6_1_109, List.forall_mem_cons.2 ⟨subd6_1_110, List.forall_mem_cons.2 ⟨subd6_1_111, List.forall_mem_cons.2 ⟨subd6_1_112, List.forall_mem_cons.2 ⟨subd6_1_113, List.forall_mem_cons.2 ⟨subd6_1_114, List.forall_mem_cons.2 ⟨subd6_1_115, List.forall_mem_cons.2 ⟨subd6_1_116, List.forall_mem_cons.2 ⟨subd6_1_117, List.forall_mem_cons.2 ⟨subd6_1_118, List.forall_mem_cons.2 ⟨subd6_1_119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-5, -4] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-5, -3] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-5, -2] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-5, -1] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-5, 0] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-5, 1] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-5, 2] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-5, 3] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-4, -6] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-4, -5] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [-4, -4] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [-4, -3] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [-4, -2] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [-4, -1] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [-4, 0] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [-4, 1] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [-4, 2] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [-4, 3] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [-4, 4] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [-3, -7] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [-3, -6] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [-3, -5] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [-3, -4] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [-3, -3] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [-3, -2] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [-3, -1] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [-3, 0] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [-3, 1] = true := by decide +kernel
theorem subd6_2_28 : subd6_2 [-3, 2] = true := by decide +kernel
theorem subd6_2_29 : subd6_2 [-3, 3] = true := by decide +kernel
theorem subd6_2_30 : subd6_2 [-3, 4] = true := by decide +kernel
theorem subd6_2_31 : subd6_2 [-3, 5] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_cons.2 ⟨subd6_2_28, List.forall_mem_cons.2 ⟨subd6_2_29, List.forall_mem_cons.2 ⟨subd6_2_30, List.forall_mem_cons.2 ⟨subd6_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
