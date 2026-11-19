import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_96 : subd6_2 [0, 0, 7] = true := by decide +kernel
theorem subd6_2_97 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_98 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_99 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_100 : subd6_2 [0, 4] = true := by decide +kernel
theorem subd6_2_101 : subd6_2 [0, 5] = true := by decide +kernel
theorem subd6_2_102 : subd6_2 [0, 6] = true := by decide +kernel
theorem subd6_2_103 : subd6_2 [1, -7] = true := by decide +kernel
theorem subd6_2_104 : subd6_2 [1, -6] = true := by decide +kernel
theorem subd6_2_105 : subd6_2 [1, -5] = true := by decide +kernel
theorem subd6_2_106 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_107 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_108 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_109 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_110 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_111 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_112 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_113 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_114 : subd6_2 [1, 4] = true := by decide +kernel
theorem subd6_2_115 : subd6_2 [1, 5] = true := by decide +kernel
theorem subd6_2_116 : subd6_2 [1, 6] = true := by decide +kernel
theorem subd6_2_117 : subd6_2 [1, 7] = true := by decide +kernel
theorem subd6_2_118 : subd6_2 [2, -6] = true := by decide +kernel
theorem subd6_2_119 : subd6_2 [2, -5] = true := by decide +kernel
theorem subd6_2_120 : subd6_2 [2, -4] = true := by decide +kernel
theorem subd6_2_121 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_122 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_123 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_124 : subd6_2 [2, 0] = true := by decide +kernel
theorem subd6_2_125 : subd6_2 [2, 1] = true := by decide +kernel
theorem subd6_2_126 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_127 : subd6_2 [2, 3] = true := by decide +kernel
theorem sbd6_2_3 : ∀ q ∈ blkd6_2_3, subd6_2 q = true := by
  unfold blkd6_2_3
  exact List.forall_mem_cons.2 ⟨subd6_2_96, List.forall_mem_cons.2 ⟨subd6_2_97, List.forall_mem_cons.2 ⟨subd6_2_98, List.forall_mem_cons.2 ⟨subd6_2_99, List.forall_mem_cons.2 ⟨subd6_2_100, List.forall_mem_cons.2 ⟨subd6_2_101, List.forall_mem_cons.2 ⟨subd6_2_102, List.forall_mem_cons.2 ⟨subd6_2_103, List.forall_mem_cons.2 ⟨subd6_2_104, List.forall_mem_cons.2 ⟨subd6_2_105, List.forall_mem_cons.2 ⟨subd6_2_106, List.forall_mem_cons.2 ⟨subd6_2_107, List.forall_mem_cons.2 ⟨subd6_2_108, List.forall_mem_cons.2 ⟨subd6_2_109, List.forall_mem_cons.2 ⟨subd6_2_110, List.forall_mem_cons.2 ⟨subd6_2_111, List.forall_mem_cons.2 ⟨subd6_2_112, List.forall_mem_cons.2 ⟨subd6_2_113, List.forall_mem_cons.2 ⟨subd6_2_114, List.forall_mem_cons.2 ⟨subd6_2_115, List.forall_mem_cons.2 ⟨subd6_2_116, List.forall_mem_cons.2 ⟨subd6_2_117, List.forall_mem_cons.2 ⟨subd6_2_118, List.forall_mem_cons.2 ⟨subd6_2_119, List.forall_mem_cons.2 ⟨subd6_2_120, List.forall_mem_cons.2 ⟨subd6_2_121, List.forall_mem_cons.2 ⟨subd6_2_122, List.forall_mem_cons.2 ⟨subd6_2_123, List.forall_mem_cons.2 ⟨subd6_2_124, List.forall_mem_cons.2 ⟨subd6_2_125, List.forall_mem_cons.2 ⟨subd6_2_126, List.forall_mem_cons.2 ⟨subd6_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_128 : subd6_2 [2, 4] = true := by decide +kernel
theorem subd6_2_129 : subd6_2 [2, 5] = true := by decide +kernel
theorem subd6_2_130 : subd6_2 [2, 6] = true := by decide +kernel
theorem subd6_2_131 : subd6_2 [2, 7] = true := by decide +kernel
theorem subd6_2_132 : subd6_2 [3, -6] = true := by decide +kernel
theorem subd6_2_133 : subd6_2 [3, -5] = true := by decide +kernel
theorem subd6_2_134 : subd6_2 [3, -4] = true := by decide +kernel
theorem subd6_2_135 : subd6_2 [3, -3] = true := by decide +kernel
theorem subd6_2_136 : subd6_2 [3, -2] = true := by decide +kernel
theorem subd6_2_137 : subd6_2 [3, -1] = true := by decide +kernel
theorem subd6_2_138 : subd6_2 [3, 0] = true := by decide +kernel
theorem subd6_2_139 : subd6_2 [3, 1] = true := by decide +kernel
theorem subd6_2_140 : subd6_2 [3, 2] = true := by decide +kernel
theorem subd6_2_141 : subd6_2 [3, 3] = true := by decide +kernel
theorem subd6_2_142 : subd6_2 [3, 4] = true := by decide +kernel
theorem subd6_2_143 : subd6_2 [3, 5] = true := by decide +kernel
theorem subd6_2_144 : subd6_2 [3, 6] = true := by decide +kernel
theorem subd6_2_145 : subd6_2 [3, 7] = true := by decide +kernel
theorem subd6_2_146 : subd6_2 [4, -5] = true := by decide +kernel
theorem subd6_2_147 : subd6_2 [4, -4] = true := by decide +kernel
theorem subd6_2_148 : subd6_2 [4, -3] = true := by decide +kernel
theorem subd6_2_149 : subd6_2 [4, -2] = true := by decide +kernel
theorem subd6_2_150 : subd6_2 [4, -1] = true := by decide +kernel
theorem subd6_2_151 : subd6_2 [4, 0] = true := by decide +kernel
theorem subd6_2_152 : subd6_2 [4, 1] = true := by decide +kernel
theorem subd6_2_153 : subd6_2 [4, 2] = true := by decide +kernel
theorem subd6_2_154 : subd6_2 [4, 3] = true := by decide +kernel
theorem subd6_2_155 : subd6_2 [4, 4] = true := by decide +kernel
theorem subd6_2_156 : subd6_2 [4, 5] = true := by decide +kernel
theorem subd6_2_157 : subd6_2 [4, 6] = true := by decide +kernel
theorem subd6_2_158 : subd6_2 [5, -4] = true := by decide +kernel
theorem subd6_2_159 : subd6_2 [5, -3] = true := by decide +kernel
theorem sbd6_2_4 : ∀ q ∈ blkd6_2_4, subd6_2 q = true := by
  unfold blkd6_2_4
  exact List.forall_mem_cons.2 ⟨subd6_2_128, List.forall_mem_cons.2 ⟨subd6_2_129, List.forall_mem_cons.2 ⟨subd6_2_130, List.forall_mem_cons.2 ⟨subd6_2_131, List.forall_mem_cons.2 ⟨subd6_2_132, List.forall_mem_cons.2 ⟨subd6_2_133, List.forall_mem_cons.2 ⟨subd6_2_134, List.forall_mem_cons.2 ⟨subd6_2_135, List.forall_mem_cons.2 ⟨subd6_2_136, List.forall_mem_cons.2 ⟨subd6_2_137, List.forall_mem_cons.2 ⟨subd6_2_138, List.forall_mem_cons.2 ⟨subd6_2_139, List.forall_mem_cons.2 ⟨subd6_2_140, List.forall_mem_cons.2 ⟨subd6_2_141, List.forall_mem_cons.2 ⟨subd6_2_142, List.forall_mem_cons.2 ⟨subd6_2_143, List.forall_mem_cons.2 ⟨subd6_2_144, List.forall_mem_cons.2 ⟨subd6_2_145, List.forall_mem_cons.2 ⟨subd6_2_146, List.forall_mem_cons.2 ⟨subd6_2_147, List.forall_mem_cons.2 ⟨subd6_2_148, List.forall_mem_cons.2 ⟨subd6_2_149, List.forall_mem_cons.2 ⟨subd6_2_150, List.forall_mem_cons.2 ⟨subd6_2_151, List.forall_mem_cons.2 ⟨subd6_2_152, List.forall_mem_cons.2 ⟨subd6_2_153, List.forall_mem_cons.2 ⟨subd6_2_154, List.forall_mem_cons.2 ⟨subd6_2_155, List.forall_mem_cons.2 ⟨subd6_2_156, List.forall_mem_cons.2 ⟨subd6_2_157, List.forall_mem_cons.2 ⟨subd6_2_158, List.forall_mem_cons.2 ⟨subd6_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_160 : subd6_2 [5, -2] = true := by decide +kernel
theorem subd6_2_161 : subd6_2 [5, -1] = true := by decide +kernel
theorem subd6_2_162 : subd6_2 [5, 0] = true := by decide +kernel
theorem subd6_2_163 : subd6_2 [5, 1] = true := by decide +kernel
theorem subd6_2_164 : subd6_2 [5, 2] = true := by decide +kernel
theorem subd6_2_165 : subd6_2 [5, 3] = true := by decide +kernel
theorem subd6_2_166 : subd6_2 [5, 4] = true := by decide +kernel
theorem subd6_2_167 : subd6_2 [5, 5] = true := by decide +kernel
theorem subd6_2_168 : subd6_2 [5, 6] = true := by decide +kernel
theorem subd6_2_169 : subd6_2 [6, -2] = true := by decide +kernel
theorem subd6_2_170 : subd6_2 [6, -1] = true := by decide +kernel
theorem subd6_2_171 : subd6_2 [6, 0] = true := by decide +kernel
theorem subd6_2_172 : subd6_2 [6, 1] = true := by decide +kernel
theorem subd6_2_173 : subd6_2 [6, 2] = true := by decide +kernel
theorem subd6_2_174 : subd6_2 [6, 3] = true := by decide +kernel
theorem subd6_2_175 : subd6_2 [6, 4] = true := by decide +kernel
theorem subd6_2_176 : subd6_2 [6, 5] = true := by decide +kernel
theorem sbd6_2_5 : ∀ q ∈ blkd6_2_5, subd6_2 q = true := by
  unfold blkd6_2_5
  exact List.forall_mem_cons.2 ⟨subd6_2_160, List.forall_mem_cons.2 ⟨subd6_2_161, List.forall_mem_cons.2 ⟨subd6_2_162, List.forall_mem_cons.2 ⟨subd6_2_163, List.forall_mem_cons.2 ⟨subd6_2_164, List.forall_mem_cons.2 ⟨subd6_2_165, List.forall_mem_cons.2 ⟨subd6_2_166, List.forall_mem_cons.2 ⟨subd6_2_167, List.forall_mem_cons.2 ⟨subd6_2_168, List.forall_mem_cons.2 ⟨subd6_2_169, List.forall_mem_cons.2 ⟨subd6_2_170, List.forall_mem_cons.2 ⟨subd6_2_171, List.forall_mem_cons.2 ⟨subd6_2_172, List.forall_mem_cons.2 ⟨subd6_2_173, List.forall_mem_cons.2 ⟨subd6_2_174, List.forall_mem_cons.2 ⟨subd6_2_175, List.forall_mem_cons.2 ⟨subd6_2_176, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C121
