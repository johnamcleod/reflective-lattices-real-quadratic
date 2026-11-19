import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_5_96 : subd9_5 [0, -1] = true := by decide +kernel
theorem subd9_5_97 : subd9_5 [0, 0] = true := by decide +kernel
theorem subd9_5_98 : subd9_5 [0, 1] = true := by decide +kernel
theorem subd9_5_99 : subd9_5 [0, 2] = true := by decide +kernel
theorem subd9_5_100 : subd9_5 [0, 3] = true := by decide +kernel
theorem subd9_5_101 : subd9_5 [0, 4] = true := by decide +kernel
theorem subd9_5_102 : subd9_5 [0, 5] = true := by decide +kernel
theorem subd9_5_103 : subd9_5 [0, 6] = true := by decide +kernel
theorem subd9_5_104 : subd9_5 [0, 7] = true := by decide +kernel
theorem subd9_5_105 : subd9_5 [1, -7] = true := by decide +kernel
theorem subd9_5_106 : subd9_5 [1, -6] = true := by decide +kernel
theorem subd9_5_107 : subd9_5 [1, -5] = true := by decide +kernel
theorem subd9_5_108 : subd9_5 [1, -4] = true := by decide +kernel
theorem subd9_5_109 : subd9_5 [1, -3] = true := by decide +kernel
theorem subd9_5_110 : subd9_5 [1, -2] = true := by decide +kernel
theorem subd9_5_111 : subd9_5 [1, -1] = true := by decide +kernel
theorem subd9_5_112 : subd9_5 [1, 0] = true := by decide +kernel
theorem subd9_5_113 : subd9_5 [1, 1] = true := by decide +kernel
theorem subd9_5_114 : subd9_5 [1, 2] = true := by decide +kernel
theorem subd9_5_115 : subd9_5 [1, 3] = true := by decide +kernel
theorem subd9_5_116 : subd9_5 [1, 4] = true := by decide +kernel
theorem subd9_5_117 : subd9_5 [1, 5] = true := by decide +kernel
theorem subd9_5_118 : subd9_5 [1, 6] = true := by decide +kernel
theorem subd9_5_119 : subd9_5 [1, 7] = true := by decide +kernel
theorem subd9_5_120 : subd9_5 [2, -7] = true := by decide +kernel
theorem subd9_5_121 : subd9_5 [2, -6] = true := by decide +kernel
theorem subd9_5_122 : subd9_5 [2, -5] = true := by decide +kernel
theorem subd9_5_123 : subd9_5 [2, -4] = true := by decide +kernel
theorem subd9_5_124 : subd9_5 [2, -3] = true := by decide +kernel
theorem subd9_5_125 : subd9_5 [2, -2] = true := by decide +kernel
theorem subd9_5_126 : subd9_5 [2, -1] = true := by decide +kernel
theorem subd9_5_127 : subd9_5 [2, 0] = true := by decide +kernel
theorem sbd9_5_3 : ∀ q ∈ blkd9_5_3, subd9_5 q = true := by
  unfold blkd9_5_3
  exact List.forall_mem_cons.2 ⟨subd9_5_96, List.forall_mem_cons.2 ⟨subd9_5_97, List.forall_mem_cons.2 ⟨subd9_5_98, List.forall_mem_cons.2 ⟨subd9_5_99, List.forall_mem_cons.2 ⟨subd9_5_100, List.forall_mem_cons.2 ⟨subd9_5_101, List.forall_mem_cons.2 ⟨subd9_5_102, List.forall_mem_cons.2 ⟨subd9_5_103, List.forall_mem_cons.2 ⟨subd9_5_104, List.forall_mem_cons.2 ⟨subd9_5_105, List.forall_mem_cons.2 ⟨subd9_5_106, List.forall_mem_cons.2 ⟨subd9_5_107, List.forall_mem_cons.2 ⟨subd9_5_108, List.forall_mem_cons.2 ⟨subd9_5_109, List.forall_mem_cons.2 ⟨subd9_5_110, List.forall_mem_cons.2 ⟨subd9_5_111, List.forall_mem_cons.2 ⟨subd9_5_112, List.forall_mem_cons.2 ⟨subd9_5_113, List.forall_mem_cons.2 ⟨subd9_5_114, List.forall_mem_cons.2 ⟨subd9_5_115, List.forall_mem_cons.2 ⟨subd9_5_116, List.forall_mem_cons.2 ⟨subd9_5_117, List.forall_mem_cons.2 ⟨subd9_5_118, List.forall_mem_cons.2 ⟨subd9_5_119, List.forall_mem_cons.2 ⟨subd9_5_120, List.forall_mem_cons.2 ⟨subd9_5_121, List.forall_mem_cons.2 ⟨subd9_5_122, List.forall_mem_cons.2 ⟨subd9_5_123, List.forall_mem_cons.2 ⟨subd9_5_124, List.forall_mem_cons.2 ⟨subd9_5_125, List.forall_mem_cons.2 ⟨subd9_5_126, List.forall_mem_cons.2 ⟨subd9_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_128 : subd9_5 [2, 1] = true := by decide +kernel
theorem subd9_5_129 : subd9_5 [2, 2] = true := by decide +kernel
theorem subd9_5_130 : subd9_5 [2, 3] = true := by decide +kernel
theorem subd9_5_131 : subd9_5 [2, 4] = true := by decide +kernel
theorem subd9_5_132 : subd9_5 [2, 5] = true := by decide +kernel
theorem subd9_5_133 : subd9_5 [2, 6] = true := by decide +kernel
theorem subd9_5_134 : subd9_5 [2, 7] = true := by decide +kernel
theorem subd9_5_135 : subd9_5 [3, -7] = true := by decide +kernel
theorem subd9_5_136 : subd9_5 [3, -6] = true := by decide +kernel
theorem subd9_5_137 : subd9_5 [3, -5] = true := by decide +kernel
theorem subd9_5_138 : subd9_5 [3, -4] = true := by decide +kernel
theorem subd9_5_139 : subd9_5 [3, -3] = true := by decide +kernel
theorem subd9_5_140 : subd9_5 [3, -2] = true := by decide +kernel
theorem subd9_5_141 : subd9_5 [3, -1] = true := by decide +kernel
theorem subd9_5_142 : subd9_5 [3, 0] = true := by decide +kernel
theorem subd9_5_143 : subd9_5 [3, 1] = true := by decide +kernel
theorem subd9_5_144 : subd9_5 [3, 2] = true := by decide +kernel
theorem subd9_5_145 : subd9_5 [3, 3] = true := by decide +kernel
theorem subd9_5_146 : subd9_5 [3, 4] = true := by decide +kernel
theorem subd9_5_147 : subd9_5 [3, 5] = true := by decide +kernel
theorem subd9_5_148 : subd9_5 [3, 6] = true := by decide +kernel
theorem subd9_5_149 : subd9_5 [3, 7] = true := by decide +kernel
theorem subd9_5_150 : subd9_5 [4, -6] = true := by decide +kernel
theorem subd9_5_151 : subd9_5 [4, -5] = true := by decide +kernel
theorem subd9_5_152 : subd9_5 [4, -4] = true := by decide +kernel
theorem subd9_5_153 : subd9_5 [4, -3] = true := by decide +kernel
theorem subd9_5_154 : subd9_5 [4, -2] = true := by decide +kernel
theorem subd9_5_155 : subd9_5 [4, -1] = true := by decide +kernel
theorem subd9_5_156 : subd9_5 [4, 0] = true := by decide +kernel
theorem subd9_5_157 : subd9_5 [4, 1] = true := by decide +kernel
theorem subd9_5_158 : subd9_5 [4, 2] = true := by decide +kernel
theorem subd9_5_159 : subd9_5 [4, 3] = true := by decide +kernel
theorem sbd9_5_4 : ∀ q ∈ blkd9_5_4, subd9_5 q = true := by
  unfold blkd9_5_4
  exact List.forall_mem_cons.2 ⟨subd9_5_128, List.forall_mem_cons.2 ⟨subd9_5_129, List.forall_mem_cons.2 ⟨subd9_5_130, List.forall_mem_cons.2 ⟨subd9_5_131, List.forall_mem_cons.2 ⟨subd9_5_132, List.forall_mem_cons.2 ⟨subd9_5_133, List.forall_mem_cons.2 ⟨subd9_5_134, List.forall_mem_cons.2 ⟨subd9_5_135, List.forall_mem_cons.2 ⟨subd9_5_136, List.forall_mem_cons.2 ⟨subd9_5_137, List.forall_mem_cons.2 ⟨subd9_5_138, List.forall_mem_cons.2 ⟨subd9_5_139, List.forall_mem_cons.2 ⟨subd9_5_140, List.forall_mem_cons.2 ⟨subd9_5_141, List.forall_mem_cons.2 ⟨subd9_5_142, List.forall_mem_cons.2 ⟨subd9_5_143, List.forall_mem_cons.2 ⟨subd9_5_144, List.forall_mem_cons.2 ⟨subd9_5_145, List.forall_mem_cons.2 ⟨subd9_5_146, List.forall_mem_cons.2 ⟨subd9_5_147, List.forall_mem_cons.2 ⟨subd9_5_148, List.forall_mem_cons.2 ⟨subd9_5_149, List.forall_mem_cons.2 ⟨subd9_5_150, List.forall_mem_cons.2 ⟨subd9_5_151, List.forall_mem_cons.2 ⟨subd9_5_152, List.forall_mem_cons.2 ⟨subd9_5_153, List.forall_mem_cons.2 ⟨subd9_5_154, List.forall_mem_cons.2 ⟨subd9_5_155, List.forall_mem_cons.2 ⟨subd9_5_156, List.forall_mem_cons.2 ⟨subd9_5_157, List.forall_mem_cons.2 ⟨subd9_5_158, List.forall_mem_cons.2 ⟨subd9_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_160 : subd9_5 [4, 4] = true := by decide +kernel
theorem subd9_5_161 : subd9_5 [4, 5] = true := by decide +kernel
theorem subd9_5_162 : subd9_5 [4, 6] = true := by decide +kernel
theorem subd9_5_163 : subd9_5 [5, -5] = true := by decide +kernel
theorem subd9_5_164 : subd9_5 [5, -4] = true := by decide +kernel
theorem subd9_5_165 : subd9_5 [5, -3] = true := by decide +kernel
theorem subd9_5_166 : subd9_5 [5, -2] = true := by decide +kernel
theorem subd9_5_167 : subd9_5 [5, -1] = true := by decide +kernel
theorem subd9_5_168 : subd9_5 [5, 0] = true := by decide +kernel
theorem subd9_5_169 : subd9_5 [5, 1] = true := by decide +kernel
theorem subd9_5_170 : subd9_5 [5, 2] = true := by decide +kernel
theorem subd9_5_171 : subd9_5 [5, 3] = true := by decide +kernel
theorem subd9_5_172 : subd9_5 [5, 4] = true := by decide +kernel
theorem subd9_5_173 : subd9_5 [5, 5] = true := by decide +kernel
theorem subd9_5_174 : subd9_5 [5, 6] = true := by decide +kernel
theorem subd9_5_175 : subd9_5 [6, -4] = true := by decide +kernel
theorem subd9_5_176 : subd9_5 [6, -3] = true := by decide +kernel
theorem subd9_5_177 : subd9_5 [6, -2] = true := by decide +kernel
theorem subd9_5_178 : subd9_5 [6, -1] = true := by decide +kernel
theorem subd9_5_179 : subd9_5 [6, 0] = true := by decide +kernel
theorem subd9_5_180 : subd9_5 [6, 1] = true := by decide +kernel
theorem subd9_5_181 : subd9_5 [6, 2] = true := by decide +kernel
theorem subd9_5_182 : subd9_5 [6, 3] = true := by decide +kernel
theorem subd9_5_183 : subd9_5 [6, 4] = true := by decide +kernel
theorem subd9_5_184 : subd9_5 [6, 5] = true := by decide +kernel
theorem subd9_5_185 : subd9_5 [7, -3] = true := by decide +kernel
theorem subd9_5_186 : subd9_5 [7, -2] = true := by decide +kernel
theorem subd9_5_187 : subd9_5 [7, -1] = true := by decide +kernel
theorem subd9_5_188 : subd9_5 [7, 0] = true := by decide +kernel
theorem subd9_5_189 : subd9_5 [7, 1] = true := by decide +kernel
theorem subd9_5_190 : subd9_5 [7, 2] = true := by decide +kernel
theorem subd9_5_191 : subd9_5 [7, 3] = true := by decide +kernel
theorem sbd9_5_5 : ∀ q ∈ blkd9_5_5, subd9_5 q = true := by
  unfold blkd9_5_5
  exact List.forall_mem_cons.2 ⟨subd9_5_160, List.forall_mem_cons.2 ⟨subd9_5_161, List.forall_mem_cons.2 ⟨subd9_5_162, List.forall_mem_cons.2 ⟨subd9_5_163, List.forall_mem_cons.2 ⟨subd9_5_164, List.forall_mem_cons.2 ⟨subd9_5_165, List.forall_mem_cons.2 ⟨subd9_5_166, List.forall_mem_cons.2 ⟨subd9_5_167, List.forall_mem_cons.2 ⟨subd9_5_168, List.forall_mem_cons.2 ⟨subd9_5_169, List.forall_mem_cons.2 ⟨subd9_5_170, List.forall_mem_cons.2 ⟨subd9_5_171, List.forall_mem_cons.2 ⟨subd9_5_172, List.forall_mem_cons.2 ⟨subd9_5_173, List.forall_mem_cons.2 ⟨subd9_5_174, List.forall_mem_cons.2 ⟨subd9_5_175, List.forall_mem_cons.2 ⟨subd9_5_176, List.forall_mem_cons.2 ⟨subd9_5_177, List.forall_mem_cons.2 ⟨subd9_5_178, List.forall_mem_cons.2 ⟨subd9_5_179, List.forall_mem_cons.2 ⟨subd9_5_180, List.forall_mem_cons.2 ⟨subd9_5_181, List.forall_mem_cons.2 ⟨subd9_5_182, List.forall_mem_cons.2 ⟨subd9_5_183, List.forall_mem_cons.2 ⟨subd9_5_184, List.forall_mem_cons.2 ⟨subd9_5_185, List.forall_mem_cons.2 ⟨subd9_5_186, List.forall_mem_cons.2 ⟨subd9_5_187, List.forall_mem_cons.2 ⟨subd9_5_188, List.forall_mem_cons.2 ⟨subd9_5_189, List.forall_mem_cons.2 ⟨subd9_5_190, List.forall_mem_cons.2 ⟨subd9_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_192 : subd9_5 [7, 4] = true := by decide +kernel
theorem subd9_5_193 : subd9_5 [8] = true := by decide +kernel
theorem sbd9_5_6 : ∀ q ∈ blkd9_5_6, subd9_5 q = true := by
  unfold blkd9_5_6
  exact List.forall_mem_cons.2 ⟨subd9_5_192, List.forall_mem_cons.2 ⟨subd9_5_193, List.forall_mem_nil _⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
