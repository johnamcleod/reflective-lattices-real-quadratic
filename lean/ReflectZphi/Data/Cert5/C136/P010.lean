import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_64 : subd7_3 [-1, 2] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [-1, 3] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [-1, 4] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [0, -5] = true := by decide +kernel
theorem subd7_3_68 : subd7_3 [0, -4] = true := by decide +kernel
theorem subd7_3_69 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_70 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_71 : subd7_3 [0, -1, -7] = true := by decide +kernel
theorem subd7_3_72 : subd7_3 [0, -1, -6] = true := by decide +kernel
theorem subd7_3_73 : subd7_3 [0, -1, -5] = true := by decide +kernel
theorem subd7_3_74 : subd7_3 [0, -1, -4] = true := by decide +kernel
theorem subd7_3_75 : subd7_3 [0, -1, -3] = true := by decide +kernel
theorem subd7_3_76 : subd7_3 [0, -1, -2] = true := by decide +kernel
theorem subd7_3_77 : subd7_3 [0, -1, -1] = true := by decide +kernel
theorem subd7_3_78 : subd7_3 [0, -1, 0] = true := by decide +kernel
theorem subd7_3_79 : subd7_3 [0, -1, 1] = true := by decide +kernel
theorem subd7_3_80 : subd7_3 [0, -1, 2] = true := by decide +kernel
theorem subd7_3_81 : subd7_3 [0, -1, 3] = true := by decide +kernel
theorem subd7_3_82 : subd7_3 [0, -1, 4] = true := by decide +kernel
theorem subd7_3_83 : subd7_3 [0, -1, 5] = true := by decide +kernel
theorem subd7_3_84 : subd7_3 [0, -1, 6] = true := by decide +kernel
theorem subd7_3_85 : subd7_3 [0, 0, -7] = true := by decide +kernel
theorem subd7_3_86 : subd7_3 [0, 0, -6] = true := by decide +kernel
theorem subd7_3_87 : subd7_3 [0, 0, -5] = true := by decide +kernel
theorem subd7_3_88 : subd7_3 [0, 0, -4] = true := by decide +kernel
theorem subd7_3_89 : subd7_3 [0, 0, -3] = true := by decide +kernel
theorem subd7_3_90 : subd7_3 [0, 0, -2] = true := by decide +kernel
theorem subd7_3_91 : subd7_3 [0, 0, -1] = true := by decide +kernel
theorem subd7_3_92 : subd7_3 [0, 0, 0] = true := by decide +kernel
theorem subd7_3_93 : subd7_3 [0, 0, 1] = true := by decide +kernel
theorem subd7_3_94 : subd7_3 [0, 0, 2] = true := by decide +kernel
theorem subd7_3_95 : subd7_3 [0, 0, 3] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_cons.2 ⟨subd7_3_68, List.forall_mem_cons.2 ⟨subd7_3_69, List.forall_mem_cons.2 ⟨subd7_3_70, List.forall_mem_cons.2 ⟨subd7_3_71, List.forall_mem_cons.2 ⟨subd7_3_72, List.forall_mem_cons.2 ⟨subd7_3_73, List.forall_mem_cons.2 ⟨subd7_3_74, List.forall_mem_cons.2 ⟨subd7_3_75, List.forall_mem_cons.2 ⟨subd7_3_76, List.forall_mem_cons.2 ⟨subd7_3_77, List.forall_mem_cons.2 ⟨subd7_3_78, List.forall_mem_cons.2 ⟨subd7_3_79, List.forall_mem_cons.2 ⟨subd7_3_80, List.forall_mem_cons.2 ⟨subd7_3_81, List.forall_mem_cons.2 ⟨subd7_3_82, List.forall_mem_cons.2 ⟨subd7_3_83, List.forall_mem_cons.2 ⟨subd7_3_84, List.forall_mem_cons.2 ⟨subd7_3_85, List.forall_mem_cons.2 ⟨subd7_3_86, List.forall_mem_cons.2 ⟨subd7_3_87, List.forall_mem_cons.2 ⟨subd7_3_88, List.forall_mem_cons.2 ⟨subd7_3_89, List.forall_mem_cons.2 ⟨subd7_3_90, List.forall_mem_cons.2 ⟨subd7_3_91, List.forall_mem_cons.2 ⟨subd7_3_92, List.forall_mem_cons.2 ⟨subd7_3_93, List.forall_mem_cons.2 ⟨subd7_3_94, List.forall_mem_cons.2 ⟨subd7_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_96 : subd7_3 [0, 0, 4] = true := by decide +kernel
theorem subd7_3_97 : subd7_3 [0, 0, 5] = true := by decide +kernel
theorem subd7_3_98 : subd7_3 [0, 0, 6] = true := by decide +kernel
theorem subd7_3_99 : subd7_3 [0, 1, -7] = true := by decide +kernel
theorem subd7_3_100 : subd7_3 [0, 1, -6] = true := by decide +kernel
theorem subd7_3_101 : subd7_3 [0, 1, -5] = true := by decide +kernel
theorem subd7_3_102 : subd7_3 [0, 1, -4] = true := by decide +kernel
theorem subd7_3_103 : subd7_3 [0, 1, -3] = true := by decide +kernel
theorem subd7_3_104 : subd7_3 [0, 1, -2] = true := by decide +kernel
theorem subd7_3_105 : subd7_3 [0, 1, -1] = true := by decide +kernel
theorem subd7_3_106 : subd7_3 [0, 1, 0] = true := by decide +kernel
theorem subd7_3_107 : subd7_3 [0, 1, 1] = true := by decide +kernel
theorem subd7_3_108 : subd7_3 [0, 1, 2] = true := by decide +kernel
theorem subd7_3_109 : subd7_3 [0, 1, 3] = true := by decide +kernel
theorem subd7_3_110 : subd7_3 [0, 1, 4] = true := by decide +kernel
theorem subd7_3_111 : subd7_3 [0, 1, 5] = true := by decide +kernel
theorem subd7_3_112 : subd7_3 [0, 1, 6] = true := by decide +kernel
theorem subd7_3_113 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_114 : subd7_3 [0, 3] = true := by decide +kernel
theorem subd7_3_115 : subd7_3 [0, 4] = true := by decide +kernel
theorem subd7_3_116 : subd7_3 [1, -5] = true := by decide +kernel
theorem subd7_3_117 : subd7_3 [1, -4] = true := by decide +kernel
theorem subd7_3_118 : subd7_3 [1, -3] = true := by decide +kernel
theorem subd7_3_119 : subd7_3 [1, -2] = true := by decide +kernel
theorem subd7_3_120 : subd7_3 [1, -1, -7] = true := by decide +kernel
theorem subd7_3_121 : subd7_3 [1, -1, -6] = true := by decide +kernel
theorem subd7_3_122 : subd7_3 [1, -1, -5] = true := by decide +kernel
theorem subd7_3_123 : subd7_3 [1, -1, -4] = true := by decide +kernel
theorem subd7_3_124 : subd7_3 [1, -1, -3] = true := by decide +kernel
theorem subd7_3_125 : subd7_3 [1, -1, -2] = true := by decide +kernel
theorem subd7_3_126 : subd7_3 [1, -1, -1] = true := by decide +kernel
theorem subd7_3_127 : subd7_3 [1, -1, 0] = true := by decide +kernel
theorem sbd7_3_3 : ∀ q ∈ blkd7_3_3, subd7_3 q = true := by
  unfold blkd7_3_3
  exact List.forall_mem_cons.2 ⟨subd7_3_96, List.forall_mem_cons.2 ⟨subd7_3_97, List.forall_mem_cons.2 ⟨subd7_3_98, List.forall_mem_cons.2 ⟨subd7_3_99, List.forall_mem_cons.2 ⟨subd7_3_100, List.forall_mem_cons.2 ⟨subd7_3_101, List.forall_mem_cons.2 ⟨subd7_3_102, List.forall_mem_cons.2 ⟨subd7_3_103, List.forall_mem_cons.2 ⟨subd7_3_104, List.forall_mem_cons.2 ⟨subd7_3_105, List.forall_mem_cons.2 ⟨subd7_3_106, List.forall_mem_cons.2 ⟨subd7_3_107, List.forall_mem_cons.2 ⟨subd7_3_108, List.forall_mem_cons.2 ⟨subd7_3_109, List.forall_mem_cons.2 ⟨subd7_3_110, List.forall_mem_cons.2 ⟨subd7_3_111, List.forall_mem_cons.2 ⟨subd7_3_112, List.forall_mem_cons.2 ⟨subd7_3_113, List.forall_mem_cons.2 ⟨subd7_3_114, List.forall_mem_cons.2 ⟨subd7_3_115, List.forall_mem_cons.2 ⟨subd7_3_116, List.forall_mem_cons.2 ⟨subd7_3_117, List.forall_mem_cons.2 ⟨subd7_3_118, List.forall_mem_cons.2 ⟨subd7_3_119, List.forall_mem_cons.2 ⟨subd7_3_120, List.forall_mem_cons.2 ⟨subd7_3_121, List.forall_mem_cons.2 ⟨subd7_3_122, List.forall_mem_cons.2 ⟨subd7_3_123, List.forall_mem_cons.2 ⟨subd7_3_124, List.forall_mem_cons.2 ⟨subd7_3_125, List.forall_mem_cons.2 ⟨subd7_3_126, List.forall_mem_cons.2 ⟨subd7_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_128 : subd7_3 [1, -1, 1] = true := by decide +kernel
theorem subd7_3_129 : subd7_3 [1, -1, 2] = true := by decide +kernel
theorem subd7_3_130 : subd7_3 [1, -1, 3] = true := by decide +kernel
theorem subd7_3_131 : subd7_3 [1, -1, 4] = true := by decide +kernel
theorem subd7_3_132 : subd7_3 [1, -1, 5] = true := by decide +kernel
theorem subd7_3_133 : subd7_3 [1, -1, 6] = true := by decide +kernel
theorem subd7_3_134 : subd7_3 [1, 0, -7] = true := by decide +kernel
theorem subd7_3_135 : subd7_3 [1, 0, -6] = true := by decide +kernel
theorem subd7_3_136 : subd7_3 [1, 0, -5] = true := by decide +kernel
theorem subd7_3_137 : subd7_3 [1, 0, -4] = true := by decide +kernel
theorem subd7_3_138 : subd7_3 [1, 0, -3] = true := by decide +kernel
theorem subd7_3_139 : subd7_3 [1, 0, -2] = true := by decide +kernel
theorem subd7_3_140 : subd7_3 [1, 0, -1] = true := by decide +kernel
theorem subd7_3_141 : subd7_3 [1, 0, 0] = true := by decide +kernel
theorem subd7_3_142 : subd7_3 [1, 0, 1] = true := by decide +kernel
theorem subd7_3_143 : subd7_3 [1, 0, 2] = true := by decide +kernel
theorem subd7_3_144 : subd7_3 [1, 0, 3] = true := by decide +kernel
theorem subd7_3_145 : subd7_3 [1, 0, 4] = true := by decide +kernel
theorem subd7_3_146 : subd7_3 [1, 0, 5] = true := by decide +kernel
theorem subd7_3_147 : subd7_3 [1, 0, 6] = true := by decide +kernel
theorem subd7_3_148 : subd7_3 [1, 1, -8] = true := by decide +kernel
theorem subd7_3_149 : subd7_3 [1, 1, -7] = true := by decide +kernel
theorem subd7_3_150 : subd7_3 [1, 1, -6] = true := by decide +kernel
theorem subd7_3_151 : subd7_3 [1, 1, -5] = true := by decide +kernel
theorem subd7_3_152 : subd7_3 [1, 1, -4] = true := by decide +kernel
theorem subd7_3_153 : subd7_3 [1, 1, -3] = true := by decide +kernel
theorem subd7_3_154 : subd7_3 [1, 1, -2] = true := by decide +kernel
theorem subd7_3_155 : subd7_3 [1, 1, -1] = true := by decide +kernel
theorem subd7_3_156 : subd7_3 [1, 1, 0] = true := by decide +kernel
theorem subd7_3_157 : subd7_3 [1, 1, 1] = true := by decide +kernel
theorem subd7_3_158 : subd7_3 [1, 1, 2] = true := by decide +kernel
theorem subd7_3_159 : subd7_3 [1, 1, 3] = true := by decide +kernel
theorem sbd7_3_4 : ∀ q ∈ blkd7_3_4, subd7_3 q = true := by
  unfold blkd7_3_4
  exact List.forall_mem_cons.2 ⟨subd7_3_128, List.forall_mem_cons.2 ⟨subd7_3_129, List.forall_mem_cons.2 ⟨subd7_3_130, List.forall_mem_cons.2 ⟨subd7_3_131, List.forall_mem_cons.2 ⟨subd7_3_132, List.forall_mem_cons.2 ⟨subd7_3_133, List.forall_mem_cons.2 ⟨subd7_3_134, List.forall_mem_cons.2 ⟨subd7_3_135, List.forall_mem_cons.2 ⟨subd7_3_136, List.forall_mem_cons.2 ⟨subd7_3_137, List.forall_mem_cons.2 ⟨subd7_3_138, List.forall_mem_cons.2 ⟨subd7_3_139, List.forall_mem_cons.2 ⟨subd7_3_140, List.forall_mem_cons.2 ⟨subd7_3_141, List.forall_mem_cons.2 ⟨subd7_3_142, List.forall_mem_cons.2 ⟨subd7_3_143, List.forall_mem_cons.2 ⟨subd7_3_144, List.forall_mem_cons.2 ⟨subd7_3_145, List.forall_mem_cons.2 ⟨subd7_3_146, List.forall_mem_cons.2 ⟨subd7_3_147, List.forall_mem_cons.2 ⟨subd7_3_148, List.forall_mem_cons.2 ⟨subd7_3_149, List.forall_mem_cons.2 ⟨subd7_3_150, List.forall_mem_cons.2 ⟨subd7_3_151, List.forall_mem_cons.2 ⟨subd7_3_152, List.forall_mem_cons.2 ⟨subd7_3_153, List.forall_mem_cons.2 ⟨subd7_3_154, List.forall_mem_cons.2 ⟨subd7_3_155, List.forall_mem_cons.2 ⟨subd7_3_156, List.forall_mem_cons.2 ⟨subd7_3_157, List.forall_mem_cons.2 ⟨subd7_3_158, List.forall_mem_cons.2 ⟨subd7_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_160 : subd7_3 [1, 1, 4] = true := by decide +kernel
theorem subd7_3_161 : subd7_3 [1, 1, 5] = true := by decide +kernel
theorem subd7_3_162 : subd7_3 [1, 2] = true := by decide +kernel
theorem subd7_3_163 : subd7_3 [1, 3] = true := by decide +kernel
theorem subd7_3_164 : subd7_3 [1, 4] = true := by decide +kernel
theorem subd7_3_165 : subd7_3 [2, -4] = true := by decide +kernel
theorem subd7_3_166 : subd7_3 [2, -3] = true := by decide +kernel
theorem subd7_3_167 : subd7_3 [2, -2] = true := by decide +kernel
theorem subd7_3_168 : subd7_3 [2, -1] = true := by decide +kernel
theorem subd7_3_169 : subd7_3 [2, 0] = true := by decide +kernel
theorem subd7_3_170 : subd7_3 [2, 1] = true := by decide +kernel
theorem subd7_3_171 : subd7_3 [2, 2] = true := by decide +kernel
theorem subd7_3_172 : subd7_3 [2, 3] = true := by decide +kernel
theorem subd7_3_173 : subd7_3 [2, 4] = true := by decide +kernel
theorem subd7_3_174 : subd7_3 [3, -4] = true := by decide +kernel
theorem subd7_3_175 : subd7_3 [3, -3] = true := by decide +kernel
theorem subd7_3_176 : subd7_3 [3, -2] = true := by decide +kernel
theorem subd7_3_177 : subd7_3 [3, -1] = true := by decide +kernel
theorem subd7_3_178 : subd7_3 [3, 0] = true := by decide +kernel
theorem subd7_3_179 : subd7_3 [3, 1] = true := by decide +kernel
theorem subd7_3_180 : subd7_3 [3, 2] = true := by decide +kernel
theorem subd7_3_181 : subd7_3 [3, 3] = true := by decide +kernel
theorem subd7_3_182 : subd7_3 [4] = true := by decide +kernel
theorem sbd7_3_5 : ∀ q ∈ blkd7_3_5, subd7_3 q = true := by
  unfold blkd7_3_5
  exact List.forall_mem_cons.2 ⟨subd7_3_160, List.forall_mem_cons.2 ⟨subd7_3_161, List.forall_mem_cons.2 ⟨subd7_3_162, List.forall_mem_cons.2 ⟨subd7_3_163, List.forall_mem_cons.2 ⟨subd7_3_164, List.forall_mem_cons.2 ⟨subd7_3_165, List.forall_mem_cons.2 ⟨subd7_3_166, List.forall_mem_cons.2 ⟨subd7_3_167, List.forall_mem_cons.2 ⟨subd7_3_168, List.forall_mem_cons.2 ⟨subd7_3_169, List.forall_mem_cons.2 ⟨subd7_3_170, List.forall_mem_cons.2 ⟨subd7_3_171, List.forall_mem_cons.2 ⟨subd7_3_172, List.forall_mem_cons.2 ⟨subd7_3_173, List.forall_mem_cons.2 ⟨subd7_3_174, List.forall_mem_cons.2 ⟨subd7_3_175, List.forall_mem_cons.2 ⟨subd7_3_176, List.forall_mem_cons.2 ⟨subd7_3_177, List.forall_mem_cons.2 ⟨subd7_3_178, List.forall_mem_cons.2 ⟨subd7_3_179, List.forall_mem_cons.2 ⟨subd7_3_180, List.forall_mem_cons.2 ⟨subd7_3_181, List.forall_mem_cons.2 ⟨subd7_3_182, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [1] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C136
