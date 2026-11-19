import ReflectZphi.Data.Cert5.C027.Base

namespace ReflectZphi.Data.Cert5.C027
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_128 : sub5 [2, -7] = true := by decide +kernel
theorem sub5_129 : sub5 [2, -6] = true := by decide +kernel
theorem sub5_130 : sub5 [2, -5] = true := by decide +kernel
theorem sub5_131 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_132 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_133 : sub5 [2, -2] = true := by decide +kernel
theorem sub5_134 : sub5 [2, -1] = true := by decide +kernel
theorem sub5_135 : sub5 [2, 0] = true := by decide +kernel
theorem sub5_136 : sub5 [2, 1] = true := by decide +kernel
theorem sub5_137 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_138 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_139 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_140 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_141 : sub5 [3, -7] = true := by decide +kernel
theorem sub5_142 : sub5 [3, -6] = true := by decide +kernel
theorem sub5_143 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_144 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_145 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_146 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_147 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_148 : sub5 [3, 0] = true := by decide +kernel
theorem sub5_149 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_150 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_151 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_152 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_153 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_154 : sub5 [4, -7] = true := by decide +kernel
theorem sub5_155 : sub5 [4, -6] = true := by decide +kernel
theorem sub5_156 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_157 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_158 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_159 : sub5 [4, -2] = true := by decide +kernel
theorem sb5_4 : ∀ q ∈ blk5_4, sub5 q = true := by
  unfold blk5_4
  exact List.forall_mem_cons.2 ⟨sub5_128, List.forall_mem_cons.2 ⟨sub5_129, List.forall_mem_cons.2 ⟨sub5_130, List.forall_mem_cons.2 ⟨sub5_131, List.forall_mem_cons.2 ⟨sub5_132, List.forall_mem_cons.2 ⟨sub5_133, List.forall_mem_cons.2 ⟨sub5_134, List.forall_mem_cons.2 ⟨sub5_135, List.forall_mem_cons.2 ⟨sub5_136, List.forall_mem_cons.2 ⟨sub5_137, List.forall_mem_cons.2 ⟨sub5_138, List.forall_mem_cons.2 ⟨sub5_139, List.forall_mem_cons.2 ⟨sub5_140, List.forall_mem_cons.2 ⟨sub5_141, List.forall_mem_cons.2 ⟨sub5_142, List.forall_mem_cons.2 ⟨sub5_143, List.forall_mem_cons.2 ⟨sub5_144, List.forall_mem_cons.2 ⟨sub5_145, List.forall_mem_cons.2 ⟨sub5_146, List.forall_mem_cons.2 ⟨sub5_147, List.forall_mem_cons.2 ⟨sub5_148, List.forall_mem_cons.2 ⟨sub5_149, List.forall_mem_cons.2 ⟨sub5_150, List.forall_mem_cons.2 ⟨sub5_151, List.forall_mem_cons.2 ⟨sub5_152, List.forall_mem_cons.2 ⟨sub5_153, List.forall_mem_cons.2 ⟨sub5_154, List.forall_mem_cons.2 ⟨sub5_155, List.forall_mem_cons.2 ⟨sub5_156, List.forall_mem_cons.2 ⟨sub5_157, List.forall_mem_cons.2 ⟨sub5_158, List.forall_mem_cons.2 ⟨sub5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_160 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_161 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_162 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_163 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_164 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_165 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_166 : sub5 [5, -6] = true := by decide +kernel
theorem sub5_167 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_168 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_169 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_170 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_171 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_172 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_173 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_174 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_175 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_176 : sub5 [5, 4] = true := by decide +kernel
theorem sub5_177 : sub5 [6, -5] = true := by decide +kernel
theorem sub5_178 : sub5 [6, -4] = true := by decide +kernel
theorem sub5_179 : sub5 [6, -3] = true := by decide +kernel
theorem sub5_180 : sub5 [6, -2] = true := by decide +kernel
theorem sub5_181 : sub5 [6, -1] = true := by decide +kernel
theorem sub5_182 : sub5 [6, 0] = true := by decide +kernel
theorem sub5_183 : sub5 [6, 1] = true := by decide +kernel
theorem sub5_184 : sub5 [6, 2] = true := by decide +kernel
theorem sub5_185 : sub5 [7] = true := by decide +kernel
theorem sb5_5 : ∀ q ∈ blk5_5, sub5 q = true := by
  unfold blk5_5
  exact List.forall_mem_cons.2 ⟨sub5_160, List.forall_mem_cons.2 ⟨sub5_161, List.forall_mem_cons.2 ⟨sub5_162, List.forall_mem_cons.2 ⟨sub5_163, List.forall_mem_cons.2 ⟨sub5_164, List.forall_mem_cons.2 ⟨sub5_165, List.forall_mem_cons.2 ⟨sub5_166, List.forall_mem_cons.2 ⟨sub5_167, List.forall_mem_cons.2 ⟨sub5_168, List.forall_mem_cons.2 ⟨sub5_169, List.forall_mem_cons.2 ⟨sub5_170, List.forall_mem_cons.2 ⟨sub5_171, List.forall_mem_cons.2 ⟨sub5_172, List.forall_mem_cons.2 ⟨sub5_173, List.forall_mem_cons.2 ⟨sub5_174, List.forall_mem_cons.2 ⟨sub5_175, List.forall_mem_cons.2 ⟨sub5_176, List.forall_mem_cons.2 ⟨sub5_177, List.forall_mem_cons.2 ⟨sub5_178, List.forall_mem_cons.2 ⟨sub5_179, List.forall_mem_cons.2 ⟨sub5_180, List.forall_mem_cons.2 ⟨sub5_181, List.forall_mem_cons.2 ⟨sub5_182, List.forall_mem_cons.2 ⟨sub5_183, List.forall_mem_cons.2 ⟨sub5_184, List.forall_mem_cons.2 ⟨sub5_185, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C027
