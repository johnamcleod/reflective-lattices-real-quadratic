import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_7_96 : subd7_7 [2, -2] = true := by decide +kernel
theorem subd7_7_97 : subd7_7 [2, -1] = true := by decide +kernel
theorem subd7_7_98 : subd7_7 [2, 0] = true := by decide +kernel
theorem subd7_7_99 : subd7_7 [2, 1] = true := by decide +kernel
theorem subd7_7_100 : subd7_7 [2, 2] = true := by decide +kernel
theorem subd7_7_101 : subd7_7 [2, 3] = true := by decide +kernel
theorem subd7_7_102 : subd7_7 [2, 4] = true := by decide +kernel
theorem subd7_7_103 : subd7_7 [2, 5] = true := by decide +kernel
theorem subd7_7_104 : subd7_7 [2, 6] = true := by decide +kernel
theorem subd7_7_105 : subd7_7 [3, -7] = true := by decide +kernel
theorem subd7_7_106 : subd7_7 [3, -6] = true := by decide +kernel
theorem subd7_7_107 : subd7_7 [3, -5] = true := by decide +kernel
theorem subd7_7_108 : subd7_7 [3, -4] = true := by decide +kernel
theorem subd7_7_109 : subd7_7 [3, -3] = true := by decide +kernel
theorem subd7_7_110 : subd7_7 [3, -2] = true := by decide +kernel
theorem subd7_7_111 : subd7_7 [3, -1] = true := by decide +kernel
theorem subd7_7_112 : subd7_7 [3, 0] = true := by decide +kernel
theorem subd7_7_113 : subd7_7 [3, 1] = true := by decide +kernel
theorem subd7_7_114 : subd7_7 [3, 2] = true := by decide +kernel
theorem subd7_7_115 : subd7_7 [3, 3] = true := by decide +kernel
theorem subd7_7_116 : subd7_7 [3, 4] = true := by decide +kernel
theorem subd7_7_117 : subd7_7 [3, 5] = true := by decide +kernel
theorem subd7_7_118 : subd7_7 [4, -6] = true := by decide +kernel
theorem subd7_7_119 : subd7_7 [4, -5] = true := by decide +kernel
theorem subd7_7_120 : subd7_7 [4, -4] = true := by decide +kernel
theorem subd7_7_121 : subd7_7 [4, -3] = true := by decide +kernel
theorem subd7_7_122 : subd7_7 [4, -2] = true := by decide +kernel
theorem subd7_7_123 : subd7_7 [4, -1] = true := by decide +kernel
theorem subd7_7_124 : subd7_7 [4, 0] = true := by decide +kernel
theorem subd7_7_125 : subd7_7 [4, 1] = true := by decide +kernel
theorem subd7_7_126 : subd7_7 [4, 2] = true := by decide +kernel
theorem subd7_7_127 : subd7_7 [4, 3] = true := by decide +kernel
theorem sbd7_7_3 : ∀ q ∈ blkd7_7_3, subd7_7 q = true := by
  unfold blkd7_7_3
  exact List.forall_mem_cons.2 ⟨subd7_7_96, List.forall_mem_cons.2 ⟨subd7_7_97, List.forall_mem_cons.2 ⟨subd7_7_98, List.forall_mem_cons.2 ⟨subd7_7_99, List.forall_mem_cons.2 ⟨subd7_7_100, List.forall_mem_cons.2 ⟨subd7_7_101, List.forall_mem_cons.2 ⟨subd7_7_102, List.forall_mem_cons.2 ⟨subd7_7_103, List.forall_mem_cons.2 ⟨subd7_7_104, List.forall_mem_cons.2 ⟨subd7_7_105, List.forall_mem_cons.2 ⟨subd7_7_106, List.forall_mem_cons.2 ⟨subd7_7_107, List.forall_mem_cons.2 ⟨subd7_7_108, List.forall_mem_cons.2 ⟨subd7_7_109, List.forall_mem_cons.2 ⟨subd7_7_110, List.forall_mem_cons.2 ⟨subd7_7_111, List.forall_mem_cons.2 ⟨subd7_7_112, List.forall_mem_cons.2 ⟨subd7_7_113, List.forall_mem_cons.2 ⟨subd7_7_114, List.forall_mem_cons.2 ⟨subd7_7_115, List.forall_mem_cons.2 ⟨subd7_7_116, List.forall_mem_cons.2 ⟨subd7_7_117, List.forall_mem_cons.2 ⟨subd7_7_118, List.forall_mem_cons.2 ⟨subd7_7_119, List.forall_mem_cons.2 ⟨subd7_7_120, List.forall_mem_cons.2 ⟨subd7_7_121, List.forall_mem_cons.2 ⟨subd7_7_122, List.forall_mem_cons.2 ⟨subd7_7_123, List.forall_mem_cons.2 ⟨subd7_7_124, List.forall_mem_cons.2 ⟨subd7_7_125, List.forall_mem_cons.2 ⟨subd7_7_126, List.forall_mem_cons.2 ⟨subd7_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_128 : subd7_7 [4, 4] = true := by decide +kernel
theorem subd7_7_129 : subd7_7 [4, 5] = true := by decide +kernel
theorem subd7_7_130 : subd7_7 [5, -5] = true := by decide +kernel
theorem subd7_7_131 : subd7_7 [5, -4] = true := by decide +kernel
theorem subd7_7_132 : subd7_7 [5, -3] = true := by decide +kernel
theorem subd7_7_133 : subd7_7 [5, -2] = true := by decide +kernel
theorem subd7_7_134 : subd7_7 [5, -1] = true := by decide +kernel
theorem subd7_7_135 : subd7_7 [5, 0] = true := by decide +kernel
theorem subd7_7_136 : subd7_7 [5, 1] = true := by decide +kernel
theorem subd7_7_137 : subd7_7 [5, 2] = true := by decide +kernel
theorem subd7_7_138 : subd7_7 [5, 3] = true := by decide +kernel
theorem subd7_7_139 : subd7_7 [6] = true := by decide +kernel
theorem sbd7_7_4 : ∀ q ∈ blkd7_7_4, subd7_7 q = true := by
  unfold blkd7_7_4
  exact List.forall_mem_cons.2 ⟨subd7_7_128, List.forall_mem_cons.2 ⟨subd7_7_129, List.forall_mem_cons.2 ⟨subd7_7_130, List.forall_mem_cons.2 ⟨subd7_7_131, List.forall_mem_cons.2 ⟨subd7_7_132, List.forall_mem_cons.2 ⟨subd7_7_133, List.forall_mem_cons.2 ⟨subd7_7_134, List.forall_mem_cons.2 ⟨subd7_7_135, List.forall_mem_cons.2 ⟨subd7_7_136, List.forall_mem_cons.2 ⟨subd7_7_137, List.forall_mem_cons.2 ⟨subd7_7_138, List.forall_mem_cons.2 ⟨subd7_7_139, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1, -4] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [1, 3] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-6, -2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-6, -1] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-6, 0] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-6, 1] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-6, 2] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-6, 3] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-6, 4] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-5, -4] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-5, -3] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-5, -2] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-5, -1] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-5, 0] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-5, 1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-5, 2] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-5, 3] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-5, 4] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-5, 5] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [-4, -5] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [-4, -4] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [-4, -3] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [-4, -2] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [-4, -1] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [-4, 0] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [-4, 1] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [-4, 2] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [-4, 3] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [-4, 4] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [-4, 5] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [-4, 6] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [-3, -5] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [-3, -4] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [-3, -3] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
