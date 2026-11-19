import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_6_96 : subd6_6 [1, -3] = true := by decide +kernel
theorem subd6_6_97 : subd6_6 [1, -2] = true := by decide +kernel
theorem subd6_6_98 : subd6_6 [1, -1] = true := by decide +kernel
theorem subd6_6_99 : subd6_6 [1, 0, -7] = true := by decide +kernel
theorem subd6_6_100 : subd6_6 [1, 0, -6] = true := by decide +kernel
theorem subd6_6_101 : subd6_6 [1, 0, -5] = true := by decide +kernel
theorem subd6_6_102 : subd6_6 [1, 0, -4] = true := by decide +kernel
theorem subd6_6_103 : subd6_6 [1, 0, -3] = true := by decide +kernel
theorem subd6_6_104 : subd6_6 [1, 0, -2] = true := by decide +kernel
theorem subd6_6_105 : subd6_6 [1, 0, -1] = true := by decide +kernel
theorem subd6_6_106 : subd6_6 [1, 0, 0] = true := by decide +kernel
theorem subd6_6_107 : subd6_6 [1, 0, 1] = true := by decide +kernel
theorem subd6_6_108 : subd6_6 [1, 0, 2] = true := by decide +kernel
theorem subd6_6_109 : subd6_6 [1, 0, 3] = true := by decide +kernel
theorem subd6_6_110 : subd6_6 [1, 0, 4] = true := by decide +kernel
theorem subd6_6_111 : subd6_6 [1, 0, 5] = true := by decide +kernel
theorem subd6_6_112 : subd6_6 [1, 0, 6] = true := by decide +kernel
theorem subd6_6_113 : subd6_6 [1, 1] = true := by decide +kernel
theorem subd6_6_114 : subd6_6 [1, 2] = true := by decide +kernel
theorem subd6_6_115 : subd6_6 [1, 3] = true := by decide +kernel
theorem subd6_6_116 : subd6_6 [1, 4] = true := by decide +kernel
theorem subd6_6_117 : subd6_6 [1, 5] = true := by decide +kernel
theorem subd6_6_118 : subd6_6 [2, -6] = true := by decide +kernel
theorem subd6_6_119 : subd6_6 [2, -5] = true := by decide +kernel
theorem subd6_6_120 : subd6_6 [2, -4] = true := by decide +kernel
theorem subd6_6_121 : subd6_6 [2, -3] = true := by decide +kernel
theorem subd6_6_122 : subd6_6 [2, -2] = true := by decide +kernel
theorem subd6_6_123 : subd6_6 [2, -1] = true := by decide +kernel
theorem subd6_6_124 : subd6_6 [2, 0] = true := by decide +kernel
theorem subd6_6_125 : subd6_6 [2, 1] = true := by decide +kernel
theorem subd6_6_126 : subd6_6 [2, 2] = true := by decide +kernel
theorem subd6_6_127 : subd6_6 [2, 3] = true := by decide +kernel
theorem sbd6_6_3 : ∀ q ∈ blkd6_6_3, subd6_6 q = true := by
  unfold blkd6_6_3
  exact List.forall_mem_cons.2 ⟨subd6_6_96, List.forall_mem_cons.2 ⟨subd6_6_97, List.forall_mem_cons.2 ⟨subd6_6_98, List.forall_mem_cons.2 ⟨subd6_6_99, List.forall_mem_cons.2 ⟨subd6_6_100, List.forall_mem_cons.2 ⟨subd6_6_101, List.forall_mem_cons.2 ⟨subd6_6_102, List.forall_mem_cons.2 ⟨subd6_6_103, List.forall_mem_cons.2 ⟨subd6_6_104, List.forall_mem_cons.2 ⟨subd6_6_105, List.forall_mem_cons.2 ⟨subd6_6_106, List.forall_mem_cons.2 ⟨subd6_6_107, List.forall_mem_cons.2 ⟨subd6_6_108, List.forall_mem_cons.2 ⟨subd6_6_109, List.forall_mem_cons.2 ⟨subd6_6_110, List.forall_mem_cons.2 ⟨subd6_6_111, List.forall_mem_cons.2 ⟨subd6_6_112, List.forall_mem_cons.2 ⟨subd6_6_113, List.forall_mem_cons.2 ⟨subd6_6_114, List.forall_mem_cons.2 ⟨subd6_6_115, List.forall_mem_cons.2 ⟨subd6_6_116, List.forall_mem_cons.2 ⟨subd6_6_117, List.forall_mem_cons.2 ⟨subd6_6_118, List.forall_mem_cons.2 ⟨subd6_6_119, List.forall_mem_cons.2 ⟨subd6_6_120, List.forall_mem_cons.2 ⟨subd6_6_121, List.forall_mem_cons.2 ⟨subd6_6_122, List.forall_mem_cons.2 ⟨subd6_6_123, List.forall_mem_cons.2 ⟨subd6_6_124, List.forall_mem_cons.2 ⟨subd6_6_125, List.forall_mem_cons.2 ⟨subd6_6_126, List.forall_mem_cons.2 ⟨subd6_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_128 : subd6_6 [2, 4] = true := by decide +kernel
theorem subd6_6_129 : subd6_6 [2, 5] = true := by decide +kernel
theorem subd6_6_130 : subd6_6 [3, -5] = true := by decide +kernel
theorem subd6_6_131 : subd6_6 [3, -4] = true := by decide +kernel
theorem subd6_6_132 : subd6_6 [3, -3] = true := by decide +kernel
theorem subd6_6_133 : subd6_6 [3, -2] = true := by decide +kernel
theorem subd6_6_134 : subd6_6 [3, -1] = true := by decide +kernel
theorem subd6_6_135 : subd6_6 [3, 0] = true := by decide +kernel
theorem subd6_6_136 : subd6_6 [3, 1] = true := by decide +kernel
theorem subd6_6_137 : subd6_6 [3, 2] = true := by decide +kernel
theorem subd6_6_138 : subd6_6 [3, 3] = true := by decide +kernel
theorem subd6_6_139 : subd6_6 [3, 4] = true := by decide +kernel
theorem subd6_6_140 : subd6_6 [3, 5] = true := by decide +kernel
theorem subd6_6_141 : subd6_6 [4, -4] = true := by decide +kernel
theorem subd6_6_142 : subd6_6 [4, -3] = true := by decide +kernel
theorem subd6_6_143 : subd6_6 [4, -2] = true := by decide +kernel
theorem subd6_6_144 : subd6_6 [4, -1] = true := by decide +kernel
theorem subd6_6_145 : subd6_6 [4, 0] = true := by decide +kernel
theorem subd6_6_146 : subd6_6 [4, 1] = true := by decide +kernel
theorem subd6_6_147 : subd6_6 [4, 2] = true := by decide +kernel
theorem subd6_6_148 : subd6_6 [4, 3] = true := by decide +kernel
theorem subd6_6_149 : subd6_6 [4, 4] = true := by decide +kernel
theorem subd6_6_150 : subd6_6 [4, 5] = true := by decide +kernel
theorem subd6_6_151 : subd6_6 [5, -4] = true := by decide +kernel
theorem subd6_6_152 : subd6_6 [5, -3] = true := by decide +kernel
theorem subd6_6_153 : subd6_6 [5, -2] = true := by decide +kernel
theorem subd6_6_154 : subd6_6 [5, -1] = true := by decide +kernel
theorem subd6_6_155 : subd6_6 [5, 0] = true := by decide +kernel
theorem subd6_6_156 : subd6_6 [5, 1] = true := by decide +kernel
theorem subd6_6_157 : subd6_6 [5, 2] = true := by decide +kernel
theorem subd6_6_158 : subd6_6 [5, 3] = true := by decide +kernel
theorem subd6_6_159 : subd6_6 [5, 4] = true := by decide +kernel
theorem sbd6_6_4 : ∀ q ∈ blkd6_6_4, subd6_6 q = true := by
  unfold blkd6_6_4
  exact List.forall_mem_cons.2 ⟨subd6_6_128, List.forall_mem_cons.2 ⟨subd6_6_129, List.forall_mem_cons.2 ⟨subd6_6_130, List.forall_mem_cons.2 ⟨subd6_6_131, List.forall_mem_cons.2 ⟨subd6_6_132, List.forall_mem_cons.2 ⟨subd6_6_133, List.forall_mem_cons.2 ⟨subd6_6_134, List.forall_mem_cons.2 ⟨subd6_6_135, List.forall_mem_cons.2 ⟨subd6_6_136, List.forall_mem_cons.2 ⟨subd6_6_137, List.forall_mem_cons.2 ⟨subd6_6_138, List.forall_mem_cons.2 ⟨subd6_6_139, List.forall_mem_cons.2 ⟨subd6_6_140, List.forall_mem_cons.2 ⟨subd6_6_141, List.forall_mem_cons.2 ⟨subd6_6_142, List.forall_mem_cons.2 ⟨subd6_6_143, List.forall_mem_cons.2 ⟨subd6_6_144, List.forall_mem_cons.2 ⟨subd6_6_145, List.forall_mem_cons.2 ⟨subd6_6_146, List.forall_mem_cons.2 ⟨subd6_6_147, List.forall_mem_cons.2 ⟨subd6_6_148, List.forall_mem_cons.2 ⟨subd6_6_149, List.forall_mem_cons.2 ⟨subd6_6_150, List.forall_mem_cons.2 ⟨subd6_6_151, List.forall_mem_cons.2 ⟨subd6_6_152, List.forall_mem_cons.2 ⟨subd6_6_153, List.forall_mem_cons.2 ⟨subd6_6_154, List.forall_mem_cons.2 ⟨subd6_6_155, List.forall_mem_cons.2 ⟨subd6_6_156, List.forall_mem_cons.2 ⟨subd6_6_157, List.forall_mem_cons.2 ⟨subd6_6_158, List.forall_mem_cons.2 ⟨subd6_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_160 : subd6_6 [6] = true := by decide +kernel
theorem sbd6_6_5 : ∀ q ∈ blkd6_6_5, subd6_6 q = true := by
  unfold blkd6_6_5
  exact List.forall_mem_cons.2 ⟨subd6_6_160, List.forall_mem_nil _⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [-6] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [-5, -4] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [-5, -3] = true := by decide +kernel
theorem subd6_7_3 : subd6_7 [-5, -2] = true := by decide +kernel
theorem subd6_7_4 : subd6_7 [-5, -1] = true := by decide +kernel
theorem subd6_7_5 : subd6_7 [-5, 0] = true := by decide +kernel
theorem subd6_7_6 : subd6_7 [-5, 1] = true := by decide +kernel
theorem subd6_7_7 : subd6_7 [-5, 2] = true := by decide +kernel
theorem subd6_7_8 : subd6_7 [-5, 3] = true := by decide +kernel
theorem subd6_7_9 : subd6_7 [-5, 4] = true := by decide +kernel
theorem subd6_7_10 : subd6_7 [-4, -5] = true := by decide +kernel
theorem subd6_7_11 : subd6_7 [-4, -4] = true := by decide +kernel
theorem subd6_7_12 : subd6_7 [-4, -3] = true := by decide +kernel
theorem subd6_7_13 : subd6_7 [-4, -2] = true := by decide +kernel
theorem subd6_7_14 : subd6_7 [-4, -1] = true := by decide +kernel
theorem subd6_7_15 : subd6_7 [-4, 0] = true := by decide +kernel
theorem subd6_7_16 : subd6_7 [-4, 1] = true := by decide +kernel
theorem subd6_7_17 : subd6_7 [-4, 2] = true := by decide +kernel
theorem subd6_7_18 : subd6_7 [-4, 3] = true := by decide +kernel
theorem subd6_7_19 : subd6_7 [-4, 4] = true := by decide +kernel
theorem subd6_7_20 : subd6_7 [-4, 5] = true := by decide +kernel
theorem subd6_7_21 : subd6_7 [-3, -6] = true := by decide +kernel
theorem subd6_7_22 : subd6_7 [-3, -5] = true := by decide +kernel
theorem subd6_7_23 : subd6_7 [-3, -4] = true := by decide +kernel
theorem subd6_7_24 : subd6_7 [-3, -3] = true := by decide +kernel
theorem subd6_7_25 : subd6_7 [-3, -2] = true := by decide +kernel
theorem subd6_7_26 : subd6_7 [-3, -1] = true := by decide +kernel
theorem subd6_7_27 : subd6_7 [-3, 0] = true := by decide +kernel
theorem subd6_7_28 : subd6_7 [-3, 1] = true := by decide +kernel
theorem subd6_7_29 : subd6_7 [-3, 2] = true := by decide +kernel
theorem subd6_7_30 : subd6_7 [-3, 3] = true := by decide +kernel
theorem subd6_7_31 : subd6_7 [-3, 4] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_cons.2 ⟨subd6_7_3, List.forall_mem_cons.2 ⟨subd6_7_4, List.forall_mem_cons.2 ⟨subd6_7_5, List.forall_mem_cons.2 ⟨subd6_7_6, List.forall_mem_cons.2 ⟨subd6_7_7, List.forall_mem_cons.2 ⟨subd6_7_8, List.forall_mem_cons.2 ⟨subd6_7_9, List.forall_mem_cons.2 ⟨subd6_7_10, List.forall_mem_cons.2 ⟨subd6_7_11, List.forall_mem_cons.2 ⟨subd6_7_12, List.forall_mem_cons.2 ⟨subd6_7_13, List.forall_mem_cons.2 ⟨subd6_7_14, List.forall_mem_cons.2 ⟨subd6_7_15, List.forall_mem_cons.2 ⟨subd6_7_16, List.forall_mem_cons.2 ⟨subd6_7_17, List.forall_mem_cons.2 ⟨subd6_7_18, List.forall_mem_cons.2 ⟨subd6_7_19, List.forall_mem_cons.2 ⟨subd6_7_20, List.forall_mem_cons.2 ⟨subd6_7_21, List.forall_mem_cons.2 ⟨subd6_7_22, List.forall_mem_cons.2 ⟨subd6_7_23, List.forall_mem_cons.2 ⟨subd6_7_24, List.forall_mem_cons.2 ⟨subd6_7_25, List.forall_mem_cons.2 ⟨subd6_7_26, List.forall_mem_cons.2 ⟨subd6_7_27, List.forall_mem_cons.2 ⟨subd6_7_28, List.forall_mem_cons.2 ⟨subd6_7_29, List.forall_mem_cons.2 ⟨subd6_7_30, List.forall_mem_cons.2 ⟨subd6_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
