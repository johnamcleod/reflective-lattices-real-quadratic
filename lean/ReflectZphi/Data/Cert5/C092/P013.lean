import ReflectZphi.Data.Cert5.C092.Base

namespace ReflectZphi.Data.Cert5.C092
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_96 : sub9 [0, 0, 6] = true := by decide +kernel
theorem sub9_97 : sub9 [0, 1] = true := by decide +kernel
theorem sub9_98 : sub9 [0, 2] = true := by decide +kernel
theorem sub9_99 : sub9 [0, 3] = true := by decide +kernel
theorem sub9_100 : sub9 [0, 4] = true := by decide +kernel
theorem sub9_101 : sub9 [0, 5] = true := by decide +kernel
theorem sub9_102 : sub9 [0, 6] = true := by decide +kernel
theorem sub9_103 : sub9 [0, 7] = true := by decide +kernel
theorem sub9_104 : sub9 [1, -7] = true := by decide +kernel
theorem sub9_105 : sub9 [1, -6] = true := by decide +kernel
theorem sub9_106 : sub9 [1, -5] = true := by decide +kernel
theorem sub9_107 : sub9 [1, -4] = true := by decide +kernel
theorem sub9_108 : sub9 [1, -3] = true := by decide +kernel
theorem sub9_109 : sub9 [1, -2] = true := by decide +kernel
theorem sub9_110 : sub9 [1, -1] = true := by decide +kernel
theorem sub9_111 : sub9 [1, 0] = true := by decide +kernel
theorem sub9_112 : sub9 [1, 1] = true := by decide +kernel
theorem sub9_113 : sub9 [1, 2] = true := by decide +kernel
theorem sub9_114 : sub9 [1, 3] = true := by decide +kernel
theorem sub9_115 : sub9 [1, 4] = true := by decide +kernel
theorem sub9_116 : sub9 [1, 5] = true := by decide +kernel
theorem sub9_117 : sub9 [1, 6] = true := by decide +kernel
theorem sub9_118 : sub9 [1, 7] = true := by decide +kernel
theorem sub9_119 : sub9 [2, -7] = true := by decide +kernel
theorem sub9_120 : sub9 [2, -6] = true := by decide +kernel
theorem sub9_121 : sub9 [2, -5] = true := by decide +kernel
theorem sub9_122 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_123 : sub9 [2, -3] = true := by decide +kernel
theorem sub9_124 : sub9 [2, -2] = true := by decide +kernel
theorem sub9_125 : sub9 [2, -1] = true := by decide +kernel
theorem sub9_126 : sub9 [2, 0] = true := by decide +kernel
theorem sub9_127 : sub9 [2, 1] = true := by decide +kernel
theorem sb9_3 : ∀ q ∈ blk9_3, sub9 q = true := by
  unfold blk9_3
  exact List.forall_mem_cons.2 ⟨sub9_96, List.forall_mem_cons.2 ⟨sub9_97, List.forall_mem_cons.2 ⟨sub9_98, List.forall_mem_cons.2 ⟨sub9_99, List.forall_mem_cons.2 ⟨sub9_100, List.forall_mem_cons.2 ⟨sub9_101, List.forall_mem_cons.2 ⟨sub9_102, List.forall_mem_cons.2 ⟨sub9_103, List.forall_mem_cons.2 ⟨sub9_104, List.forall_mem_cons.2 ⟨sub9_105, List.forall_mem_cons.2 ⟨sub9_106, List.forall_mem_cons.2 ⟨sub9_107, List.forall_mem_cons.2 ⟨sub9_108, List.forall_mem_cons.2 ⟨sub9_109, List.forall_mem_cons.2 ⟨sub9_110, List.forall_mem_cons.2 ⟨sub9_111, List.forall_mem_cons.2 ⟨sub9_112, List.forall_mem_cons.2 ⟨sub9_113, List.forall_mem_cons.2 ⟨sub9_114, List.forall_mem_cons.2 ⟨sub9_115, List.forall_mem_cons.2 ⟨sub9_116, List.forall_mem_cons.2 ⟨sub9_117, List.forall_mem_cons.2 ⟨sub9_118, List.forall_mem_cons.2 ⟨sub9_119, List.forall_mem_cons.2 ⟨sub9_120, List.forall_mem_cons.2 ⟨sub9_121, List.forall_mem_cons.2 ⟨sub9_122, List.forall_mem_cons.2 ⟨sub9_123, List.forall_mem_cons.2 ⟨sub9_124, List.forall_mem_cons.2 ⟨sub9_125, List.forall_mem_cons.2 ⟨sub9_126, List.forall_mem_cons.2 ⟨sub9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_128 : sub9 [2, 2] = true := by decide +kernel
theorem sub9_129 : sub9 [2, 3] = true := by decide +kernel
theorem sub9_130 : sub9 [2, 4] = true := by decide +kernel
theorem sub9_131 : sub9 [2, 5] = true := by decide +kernel
theorem sub9_132 : sub9 [2, 6] = true := by decide +kernel
theorem sub9_133 : sub9 [2, 7] = true := by decide +kernel
theorem sub9_134 : sub9 [3, -6] = true := by decide +kernel
theorem sub9_135 : sub9 [3, -5] = true := by decide +kernel
theorem sub9_136 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_137 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_138 : sub9 [3, -2] = true := by decide +kernel
theorem sub9_139 : sub9 [3, -1] = true := by decide +kernel
theorem sub9_140 : sub9 [3, 0] = true := by decide +kernel
theorem sub9_141 : sub9 [3, 1] = true := by decide +kernel
theorem sub9_142 : sub9 [3, 2] = true := by decide +kernel
theorem sub9_143 : sub9 [3, 3] = true := by decide +kernel
theorem sub9_144 : sub9 [3, 4] = true := by decide +kernel
theorem sub9_145 : sub9 [3, 5] = true := by decide +kernel
theorem sub9_146 : sub9 [3, 6] = true := by decide +kernel
theorem sub9_147 : sub9 [3, 7] = true := by decide +kernel
theorem sub9_148 : sub9 [4, -5] = true := by decide +kernel
theorem sub9_149 : sub9 [4, -4] = true := by decide +kernel
theorem sub9_150 : sub9 [4, -3] = true := by decide +kernel
theorem sub9_151 : sub9 [4, -2] = true := by decide +kernel
theorem sub9_152 : sub9 [4, -1] = true := by decide +kernel
theorem sub9_153 : sub9 [4, 0] = true := by decide +kernel
theorem sub9_154 : sub9 [4, 1] = true := by decide +kernel
theorem sub9_155 : sub9 [4, 2] = true := by decide +kernel
theorem sub9_156 : sub9 [4, 3] = true := by decide +kernel
theorem sub9_157 : sub9 [4, 4] = true := by decide +kernel
theorem sub9_158 : sub9 [4, 5] = true := by decide +kernel
theorem sub9_159 : sub9 [4, 6] = true := by decide +kernel
theorem sb9_4 : ∀ q ∈ blk9_4, sub9 q = true := by
  unfold blk9_4
  exact List.forall_mem_cons.2 ⟨sub9_128, List.forall_mem_cons.2 ⟨sub9_129, List.forall_mem_cons.2 ⟨sub9_130, List.forall_mem_cons.2 ⟨sub9_131, List.forall_mem_cons.2 ⟨sub9_132, List.forall_mem_cons.2 ⟨sub9_133, List.forall_mem_cons.2 ⟨sub9_134, List.forall_mem_cons.2 ⟨sub9_135, List.forall_mem_cons.2 ⟨sub9_136, List.forall_mem_cons.2 ⟨sub9_137, List.forall_mem_cons.2 ⟨sub9_138, List.forall_mem_cons.2 ⟨sub9_139, List.forall_mem_cons.2 ⟨sub9_140, List.forall_mem_cons.2 ⟨sub9_141, List.forall_mem_cons.2 ⟨sub9_142, List.forall_mem_cons.2 ⟨sub9_143, List.forall_mem_cons.2 ⟨sub9_144, List.forall_mem_cons.2 ⟨sub9_145, List.forall_mem_cons.2 ⟨sub9_146, List.forall_mem_cons.2 ⟨sub9_147, List.forall_mem_cons.2 ⟨sub9_148, List.forall_mem_cons.2 ⟨sub9_149, List.forall_mem_cons.2 ⟨sub9_150, List.forall_mem_cons.2 ⟨sub9_151, List.forall_mem_cons.2 ⟨sub9_152, List.forall_mem_cons.2 ⟨sub9_153, List.forall_mem_cons.2 ⟨sub9_154, List.forall_mem_cons.2 ⟨sub9_155, List.forall_mem_cons.2 ⟨sub9_156, List.forall_mem_cons.2 ⟨sub9_157, List.forall_mem_cons.2 ⟨sub9_158, List.forall_mem_cons.2 ⟨sub9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_160 : sub9 [5, -4] = true := by decide +kernel
theorem sub9_161 : sub9 [5, -3] = true := by decide +kernel
theorem sub9_162 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_163 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_164 : sub9 [5, 0] = true := by decide +kernel
theorem sub9_165 : sub9 [5, 1] = true := by decide +kernel
theorem sub9_166 : sub9 [5, 2] = true := by decide +kernel
theorem sub9_167 : sub9 [5, 3] = true := by decide +kernel
theorem sub9_168 : sub9 [5, 4] = true := by decide +kernel
theorem sub9_169 : sub9 [5, 5] = true := by decide +kernel
theorem sub9_170 : sub9 [5, 6] = true := by decide +kernel
theorem sub9_171 : sub9 [6, -2] = true := by decide +kernel
theorem sub9_172 : sub9 [6, -1] = true := by decide +kernel
theorem sub9_173 : sub9 [6, 0] = true := by decide +kernel
theorem sub9_174 : sub9 [6, 1] = true := by decide +kernel
theorem sub9_175 : sub9 [6, 2] = true := by decide +kernel
theorem sub9_176 : sub9 [6, 3] = true := by decide +kernel
theorem sub9_177 : sub9 [6, 4] = true := by decide +kernel
theorem sub9_178 : sub9 [6, 5] = true := by decide +kernel
theorem sb9_5 : ∀ q ∈ blk9_5, sub9 q = true := by
  unfold blk9_5
  exact List.forall_mem_cons.2 ⟨sub9_160, List.forall_mem_cons.2 ⟨sub9_161, List.forall_mem_cons.2 ⟨sub9_162, List.forall_mem_cons.2 ⟨sub9_163, List.forall_mem_cons.2 ⟨sub9_164, List.forall_mem_cons.2 ⟨sub9_165, List.forall_mem_cons.2 ⟨sub9_166, List.forall_mem_cons.2 ⟨sub9_167, List.forall_mem_cons.2 ⟨sub9_168, List.forall_mem_cons.2 ⟨sub9_169, List.forall_mem_cons.2 ⟨sub9_170, List.forall_mem_cons.2 ⟨sub9_171, List.forall_mem_cons.2 ⟨sub9_172, List.forall_mem_cons.2 ⟨sub9_173, List.forall_mem_cons.2 ⟨sub9_174, List.forall_mem_cons.2 ⟨sub9_175, List.forall_mem_cons.2 ⟨sub9_176, List.forall_mem_cons.2 ⟨sub9_177, List.forall_mem_cons.2 ⟨sub9_178, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C092
