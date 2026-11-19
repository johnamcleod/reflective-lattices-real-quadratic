import ReflectZphi.Data.Cert5.C073.Base

namespace ReflectZphi.Data.Cert5.C073
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_96 : sub3 [0, 1] = true := by decide +kernel
theorem sub3_97 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_98 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_99 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_100 : sub3 [0, 5] = true := by decide +kernel
theorem sub3_101 : sub3 [0, 6] = true := by decide +kernel
theorem sub3_102 : sub3 [1, -7] = true := by decide +kernel
theorem sub3_103 : sub3 [1, -6] = true := by decide +kernel
theorem sub3_104 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_105 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_106 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_107 : sub3 [1, -2] = true := by decide +kernel
theorem sub3_108 : sub3 [1, -1] = true := by decide +kernel
theorem sub3_109 : sub3 [1, 0] = true := by decide +kernel
theorem sub3_110 : sub3 [1, 1] = true := by decide +kernel
theorem sub3_111 : sub3 [1, 2] = true := by decide +kernel
theorem sub3_112 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_113 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_114 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_115 : sub3 [1, 6] = true := by decide +kernel
theorem sub3_116 : sub3 [2, -7] = true := by decide +kernel
theorem sub3_117 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_118 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_119 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_120 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_121 : sub3 [2, -2] = true := by decide +kernel
theorem sub3_122 : sub3 [2, -1] = true := by decide +kernel
theorem sub3_123 : sub3 [2, 0] = true := by decide +kernel
theorem sub3_124 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_125 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_126 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_127 : sub3 [2, 4] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_128 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_129 : sub3 [2, 6] = true := by decide +kernel
theorem sub3_130 : sub3 [3, -7] = true := by decide +kernel
theorem sub3_131 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_132 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_133 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_134 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_135 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_136 : sub3 [3, -1] = true := by decide +kernel
theorem sub3_137 : sub3 [3, 0] = true := by decide +kernel
theorem sub3_138 : sub3 [3, 1] = true := by decide +kernel
theorem sub3_139 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_140 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_141 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_142 : sub3 [3, 5] = true := by decide +kernel
theorem sub3_143 : sub3 [3, 6] = true := by decide +kernel
theorem sub3_144 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_145 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_146 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_147 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_148 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_149 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_150 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_151 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_152 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_153 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_154 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_155 : sub3 [4, 5] = true := by decide +kernel
theorem sub3_156 : sub3 [5, -6] = true := by decide +kernel
theorem sub3_157 : sub3 [5, -5] = true := by decide +kernel
theorem sub3_158 : sub3 [5, -4] = true := by decide +kernel
theorem sub3_159 : sub3 [5, -3] = true := by decide +kernel
theorem sb3_4 : ∀ q ∈ blk3_4, sub3 q = true := by
  unfold blk3_4
  exact List.forall_mem_cons.2 ⟨sub3_128, List.forall_mem_cons.2 ⟨sub3_129, List.forall_mem_cons.2 ⟨sub3_130, List.forall_mem_cons.2 ⟨sub3_131, List.forall_mem_cons.2 ⟨sub3_132, List.forall_mem_cons.2 ⟨sub3_133, List.forall_mem_cons.2 ⟨sub3_134, List.forall_mem_cons.2 ⟨sub3_135, List.forall_mem_cons.2 ⟨sub3_136, List.forall_mem_cons.2 ⟨sub3_137, List.forall_mem_cons.2 ⟨sub3_138, List.forall_mem_cons.2 ⟨sub3_139, List.forall_mem_cons.2 ⟨sub3_140, List.forall_mem_cons.2 ⟨sub3_141, List.forall_mem_cons.2 ⟨sub3_142, List.forall_mem_cons.2 ⟨sub3_143, List.forall_mem_cons.2 ⟨sub3_144, List.forall_mem_cons.2 ⟨sub3_145, List.forall_mem_cons.2 ⟨sub3_146, List.forall_mem_cons.2 ⟨sub3_147, List.forall_mem_cons.2 ⟨sub3_148, List.forall_mem_cons.2 ⟨sub3_149, List.forall_mem_cons.2 ⟨sub3_150, List.forall_mem_cons.2 ⟨sub3_151, List.forall_mem_cons.2 ⟨sub3_152, List.forall_mem_cons.2 ⟨sub3_153, List.forall_mem_cons.2 ⟨sub3_154, List.forall_mem_cons.2 ⟨sub3_155, List.forall_mem_cons.2 ⟨sub3_156, List.forall_mem_cons.2 ⟨sub3_157, List.forall_mem_cons.2 ⟨sub3_158, List.forall_mem_cons.2 ⟨sub3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_160 : sub3 [5, -2] = true := by decide +kernel
theorem sub3_161 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_162 : sub3 [5, 0] = true := by decide +kernel
theorem sub3_163 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_164 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_165 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_166 : sub3 [5, 4] = true := by decide +kernel
theorem sub3_167 : sub3 [6, -5] = true := by decide +kernel
theorem sub3_168 : sub3 [6, -4] = true := by decide +kernel
theorem sub3_169 : sub3 [6, -3] = true := by decide +kernel
theorem sub3_170 : sub3 [6, -2] = true := by decide +kernel
theorem sub3_171 : sub3 [6, -1] = true := by decide +kernel
theorem sub3_172 : sub3 [6, 0] = true := by decide +kernel
theorem sub3_173 : sub3 [6, 1] = true := by decide +kernel
theorem sub3_174 : sub3 [6, 2] = true := by decide +kernel
theorem sub3_175 : sub3 [6, 3] = true := by decide +kernel
theorem sub3_176 : sub3 [7] = true := by decide +kernel
theorem sb3_5 : ∀ q ∈ blk3_5, sub3 q = true := by
  unfold blk3_5
  exact List.forall_mem_cons.2 ⟨sub3_160, List.forall_mem_cons.2 ⟨sub3_161, List.forall_mem_cons.2 ⟨sub3_162, List.forall_mem_cons.2 ⟨sub3_163, List.forall_mem_cons.2 ⟨sub3_164, List.forall_mem_cons.2 ⟨sub3_165, List.forall_mem_cons.2 ⟨sub3_166, List.forall_mem_cons.2 ⟨sub3_167, List.forall_mem_cons.2 ⟨sub3_168, List.forall_mem_cons.2 ⟨sub3_169, List.forall_mem_cons.2 ⟨sub3_170, List.forall_mem_cons.2 ⟨sub3_171, List.forall_mem_cons.2 ⟨sub3_172, List.forall_mem_cons.2 ⟨sub3_173, List.forall_mem_cons.2 ⟨sub3_174, List.forall_mem_cons.2 ⟨sub3_175, List.forall_mem_cons.2 ⟨sub3_176, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C073
