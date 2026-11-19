import ReflectZphi.Data.Cert5.C067.Base

namespace ReflectZphi.Data.Cert5.C067
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_96 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_97 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_98 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_99 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_100 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_101 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_102 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_103 : sub4 [1, 1] = true := by decide +kernel
theorem sub4_104 : sub4 [1, 2] = true := by decide +kernel
theorem sub4_105 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_106 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_107 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_108 : sub4 [1, 6] = true := by decide +kernel
theorem sub4_109 : sub4 [1, 7] = true := by decide +kernel
theorem sub4_110 : sub4 [2, -7] = true := by decide +kernel
theorem sub4_111 : sub4 [2, -6] = true := by decide +kernel
theorem sub4_112 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_113 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_114 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_115 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_116 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_117 : sub4 [2, 0] = true := by decide +kernel
theorem sub4_118 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_119 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_120 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_121 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_122 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_123 : sub4 [2, 6] = true := by decide +kernel
theorem sub4_124 : sub4 [2, 7] = true := by decide +kernel
theorem sub4_125 : sub4 [3, -6] = true := by decide +kernel
theorem sub4_126 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_127 : sub4 [3, -4] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_128 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_129 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_130 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_131 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_132 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_133 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_134 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_135 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_136 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_137 : sub4 [3, 6] = true := by decide +kernel
theorem sub4_138 : sub4 [3, 7] = true := by decide +kernel
theorem sub4_139 : sub4 [4, -5] = true := by decide +kernel
theorem sub4_140 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_141 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_142 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_143 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_144 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_145 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_146 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_147 : sub4 [4, 3] = true := by decide +kernel
theorem sub4_148 : sub4 [4, 4] = true := by decide +kernel
theorem sub4_149 : sub4 [4, 5] = true := by decide +kernel
theorem sub4_150 : sub4 [4, 6] = true := by decide +kernel
theorem sub4_151 : sub4 [4, 7] = true := by decide +kernel
theorem sub4_152 : sub4 [5, -4] = true := by decide +kernel
theorem sub4_153 : sub4 [5, -3] = true := by decide +kernel
theorem sub4_154 : sub4 [5, -2] = true := by decide +kernel
theorem sub4_155 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_156 : sub4 [5, 0] = true := by decide +kernel
theorem sub4_157 : sub4 [5, 1] = true := by decide +kernel
theorem sub4_158 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_159 : sub4 [5, 3] = true := by decide +kernel
theorem sb4_4 : ∀ q ∈ blk4_4, sub4 q = true := by
  unfold blk4_4
  exact List.forall_mem_cons.2 ⟨sub4_128, List.forall_mem_cons.2 ⟨sub4_129, List.forall_mem_cons.2 ⟨sub4_130, List.forall_mem_cons.2 ⟨sub4_131, List.forall_mem_cons.2 ⟨sub4_132, List.forall_mem_cons.2 ⟨sub4_133, List.forall_mem_cons.2 ⟨sub4_134, List.forall_mem_cons.2 ⟨sub4_135, List.forall_mem_cons.2 ⟨sub4_136, List.forall_mem_cons.2 ⟨sub4_137, List.forall_mem_cons.2 ⟨sub4_138, List.forall_mem_cons.2 ⟨sub4_139, List.forall_mem_cons.2 ⟨sub4_140, List.forall_mem_cons.2 ⟨sub4_141, List.forall_mem_cons.2 ⟨sub4_142, List.forall_mem_cons.2 ⟨sub4_143, List.forall_mem_cons.2 ⟨sub4_144, List.forall_mem_cons.2 ⟨sub4_145, List.forall_mem_cons.2 ⟨sub4_146, List.forall_mem_cons.2 ⟨sub4_147, List.forall_mem_cons.2 ⟨sub4_148, List.forall_mem_cons.2 ⟨sub4_149, List.forall_mem_cons.2 ⟨sub4_150, List.forall_mem_cons.2 ⟨sub4_151, List.forall_mem_cons.2 ⟨sub4_152, List.forall_mem_cons.2 ⟨sub4_153, List.forall_mem_cons.2 ⟨sub4_154, List.forall_mem_cons.2 ⟨sub4_155, List.forall_mem_cons.2 ⟨sub4_156, List.forall_mem_cons.2 ⟨sub4_157, List.forall_mem_cons.2 ⟨sub4_158, List.forall_mem_cons.2 ⟨sub4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_160 : sub4 [5, 4] = true := by decide +kernel
theorem sub4_161 : sub4 [5, 5] = true := by decide +kernel
theorem sub4_162 : sub4 [5, 6] = true := by decide +kernel
theorem sub4_163 : sub4 [5, 7] = true := by decide +kernel
theorem sub4_164 : sub4 [6, -2] = true := by decide +kernel
theorem sub4_165 : sub4 [6, -1] = true := by decide +kernel
theorem sub4_166 : sub4 [6, 0] = true := by decide +kernel
theorem sub4_167 : sub4 [6, 1] = true := by decide +kernel
theorem sub4_168 : sub4 [6, 2] = true := by decide +kernel
theorem sub4_169 : sub4 [6, 3] = true := by decide +kernel
theorem sub4_170 : sub4 [6, 4] = true := by decide +kernel
theorem sub4_171 : sub4 [6, 5] = true := by decide +kernel
theorem sub4_172 : sub4 [6, 6] = true := by decide +kernel
theorem sub4_173 : sub4 [7] = true := by decide +kernel
theorem sb4_5 : ∀ q ∈ blk4_5, sub4 q = true := by
  unfold blk4_5
  exact List.forall_mem_cons.2 ⟨sub4_160, List.forall_mem_cons.2 ⟨sub4_161, List.forall_mem_cons.2 ⟨sub4_162, List.forall_mem_cons.2 ⟨sub4_163, List.forall_mem_cons.2 ⟨sub4_164, List.forall_mem_cons.2 ⟨sub4_165, List.forall_mem_cons.2 ⟨sub4_166, List.forall_mem_cons.2 ⟨sub4_167, List.forall_mem_cons.2 ⟨sub4_168, List.forall_mem_cons.2 ⟨sub4_169, List.forall_mem_cons.2 ⟨sub4_170, List.forall_mem_cons.2 ⟨sub4_171, List.forall_mem_cons.2 ⟨sub4_172, List.forall_mem_cons.2 ⟨sub4_173, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C067
