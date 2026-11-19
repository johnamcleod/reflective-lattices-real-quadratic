import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_6_64 : subd8_6 [-1, 1, 0] = true := by decide +kernel
theorem subd8_6_65 : subd8_6 [-1, 1, 1] = true := by decide +kernel
theorem subd8_6_66 : subd8_6 [-1, 1, 2] = true := by decide +kernel
theorem subd8_6_67 : subd8_6 [-1, 1, 3] = true := by decide +kernel
theorem subd8_6_68 : subd8_6 [-1, 1, 4] = true := by decide +kernel
theorem subd8_6_69 : subd8_6 [-1, 1, 5] = true := by decide +kernel
theorem subd8_6_70 : subd8_6 [-1, 1, 6] = true := by decide +kernel
theorem subd8_6_71 : subd8_6 [-1, 2] = true := by decide +kernel
theorem subd8_6_72 : subd8_6 [-1, 3] = true := by decide +kernel
theorem subd8_6_73 : subd8_6 [-1, 4] = true := by decide +kernel
theorem subd8_6_74 : subd8_6 [-1, 5] = true := by decide +kernel
theorem subd8_6_75 : subd8_6 [-1, 6] = true := by decide +kernel
theorem subd8_6_76 : subd8_6 [-1, 7] = true := by decide +kernel
theorem subd8_6_77 : subd8_6 [0, -7] = true := by decide +kernel
theorem subd8_6_78 : subd8_6 [0, -6] = true := by decide +kernel
theorem subd8_6_79 : subd8_6 [0, -5] = true := by decide +kernel
theorem subd8_6_80 : subd8_6 [0, -4] = true := by decide +kernel
theorem subd8_6_81 : subd8_6 [0, -3] = true := by decide +kernel
theorem subd8_6_82 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_83 : subd8_6 [0, -1] = true := by decide +kernel
theorem subd8_6_84 : subd8_6 [0, 0, -7] = true := by decide +kernel
theorem subd8_6_85 : subd8_6 [0, 0, -6] = true := by decide +kernel
theorem subd8_6_86 : subd8_6 [0, 0, -5] = true := by decide +kernel
theorem subd8_6_87 : subd8_6 [0, 0, -4] = true := by decide +kernel
theorem subd8_6_88 : subd8_6 [0, 0, -3] = true := by decide +kernel
theorem subd8_6_89 : subd8_6 [0, 0, -2] = true := by decide +kernel
theorem subd8_6_90 : subd8_6 [0, 0, -1] = true := by decide +kernel
theorem subd8_6_91 : subd8_6 [0, 0, 0] = true := by decide +kernel
theorem subd8_6_92 : subd8_6 [0, 0, 1] = true := by decide +kernel
theorem subd8_6_93 : subd8_6 [0, 0, 2] = true := by decide +kernel
theorem subd8_6_94 : subd8_6 [0, 0, 3] = true := by decide +kernel
theorem subd8_6_95 : subd8_6 [0, 0, 4] = true := by decide +kernel
theorem sbd8_6_2 : ∀ q ∈ blkd8_6_2, subd8_6 q = true := by
  unfold blkd8_6_2
  exact List.forall_mem_cons.2 ⟨subd8_6_64, List.forall_mem_cons.2 ⟨subd8_6_65, List.forall_mem_cons.2 ⟨subd8_6_66, List.forall_mem_cons.2 ⟨subd8_6_67, List.forall_mem_cons.2 ⟨subd8_6_68, List.forall_mem_cons.2 ⟨subd8_6_69, List.forall_mem_cons.2 ⟨subd8_6_70, List.forall_mem_cons.2 ⟨subd8_6_71, List.forall_mem_cons.2 ⟨subd8_6_72, List.forall_mem_cons.2 ⟨subd8_6_73, List.forall_mem_cons.2 ⟨subd8_6_74, List.forall_mem_cons.2 ⟨subd8_6_75, List.forall_mem_cons.2 ⟨subd8_6_76, List.forall_mem_cons.2 ⟨subd8_6_77, List.forall_mem_cons.2 ⟨subd8_6_78, List.forall_mem_cons.2 ⟨subd8_6_79, List.forall_mem_cons.2 ⟨subd8_6_80, List.forall_mem_cons.2 ⟨subd8_6_81, List.forall_mem_cons.2 ⟨subd8_6_82, List.forall_mem_cons.2 ⟨subd8_6_83, List.forall_mem_cons.2 ⟨subd8_6_84, List.forall_mem_cons.2 ⟨subd8_6_85, List.forall_mem_cons.2 ⟨subd8_6_86, List.forall_mem_cons.2 ⟨subd8_6_87, List.forall_mem_cons.2 ⟨subd8_6_88, List.forall_mem_cons.2 ⟨subd8_6_89, List.forall_mem_cons.2 ⟨subd8_6_90, List.forall_mem_cons.2 ⟨subd8_6_91, List.forall_mem_cons.2 ⟨subd8_6_92, List.forall_mem_cons.2 ⟨subd8_6_93, List.forall_mem_cons.2 ⟨subd8_6_94, List.forall_mem_cons.2 ⟨subd8_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_96 : subd8_6 [0, 0, 5] = true := by decide +kernel
theorem subd8_6_97 : subd8_6 [0, 0, 6] = true := by decide +kernel
theorem subd8_6_98 : subd8_6 [0, 1] = true := by decide +kernel
theorem subd8_6_99 : subd8_6 [0, 2] = true := by decide +kernel
theorem subd8_6_100 : subd8_6 [0, 3] = true := by decide +kernel
theorem subd8_6_101 : subd8_6 [0, 4] = true := by decide +kernel
theorem subd8_6_102 : subd8_6 [0, 5] = true := by decide +kernel
theorem subd8_6_103 : subd8_6 [0, 6] = true := by decide +kernel
theorem subd8_6_104 : subd8_6 [1, -8] = true := by decide +kernel
theorem subd8_6_105 : subd8_6 [1, -7] = true := by decide +kernel
theorem subd8_6_106 : subd8_6 [1, -6] = true := by decide +kernel
theorem subd8_6_107 : subd8_6 [1, -5] = true := by decide +kernel
theorem subd8_6_108 : subd8_6 [1, -4] = true := by decide +kernel
theorem subd8_6_109 : subd8_6 [1, -3] = true := by decide +kernel
theorem subd8_6_110 : subd8_6 [1, -2] = true := by decide +kernel
theorem subd8_6_111 : subd8_6 [1, -1, -7] = true := by decide +kernel
theorem subd8_6_112 : subd8_6 [1, -1, -6] = true := by decide +kernel
theorem subd8_6_113 : subd8_6 [1, -1, -5] = true := by decide +kernel
theorem subd8_6_114 : subd8_6 [1, -1, -4] = true := by decide +kernel
theorem subd8_6_115 : subd8_6 [1, -1, -3] = true := by decide +kernel
theorem subd8_6_116 : subd8_6 [1, -1, -2] = true := by decide +kernel
theorem subd8_6_117 : subd8_6 [1, -1, -1] = true := by decide +kernel
theorem subd8_6_118 : subd8_6 [1, -1, 0] = true := by decide +kernel
theorem subd8_6_119 : subd8_6 [1, -1, 1] = true := by decide +kernel
theorem subd8_6_120 : subd8_6 [1, -1, 2] = true := by decide +kernel
theorem subd8_6_121 : subd8_6 [1, -1, 3] = true := by decide +kernel
theorem subd8_6_122 : subd8_6 [1, -1, 4] = true := by decide +kernel
theorem subd8_6_123 : subd8_6 [1, -1, 5] = true := by decide +kernel
theorem subd8_6_124 : subd8_6 [1, -1, 6] = true := by decide +kernel
theorem subd8_6_125 : subd8_6 [1, 0] = true := by decide +kernel
theorem subd8_6_126 : subd8_6 [1, 1] = true := by decide +kernel
theorem subd8_6_127 : subd8_6 [1, 2] = true := by decide +kernel
theorem sbd8_6_3 : ∀ q ∈ blkd8_6_3, subd8_6 q = true := by
  unfold blkd8_6_3
  exact List.forall_mem_cons.2 ⟨subd8_6_96, List.forall_mem_cons.2 ⟨subd8_6_97, List.forall_mem_cons.2 ⟨subd8_6_98, List.forall_mem_cons.2 ⟨subd8_6_99, List.forall_mem_cons.2 ⟨subd8_6_100, List.forall_mem_cons.2 ⟨subd8_6_101, List.forall_mem_cons.2 ⟨subd8_6_102, List.forall_mem_cons.2 ⟨subd8_6_103, List.forall_mem_cons.2 ⟨subd8_6_104, List.forall_mem_cons.2 ⟨subd8_6_105, List.forall_mem_cons.2 ⟨subd8_6_106, List.forall_mem_cons.2 ⟨subd8_6_107, List.forall_mem_cons.2 ⟨subd8_6_108, List.forall_mem_cons.2 ⟨subd8_6_109, List.forall_mem_cons.2 ⟨subd8_6_110, List.forall_mem_cons.2 ⟨subd8_6_111, List.forall_mem_cons.2 ⟨subd8_6_112, List.forall_mem_cons.2 ⟨subd8_6_113, List.forall_mem_cons.2 ⟨subd8_6_114, List.forall_mem_cons.2 ⟨subd8_6_115, List.forall_mem_cons.2 ⟨subd8_6_116, List.forall_mem_cons.2 ⟨subd8_6_117, List.forall_mem_cons.2 ⟨subd8_6_118, List.forall_mem_cons.2 ⟨subd8_6_119, List.forall_mem_cons.2 ⟨subd8_6_120, List.forall_mem_cons.2 ⟨subd8_6_121, List.forall_mem_cons.2 ⟨subd8_6_122, List.forall_mem_cons.2 ⟨subd8_6_123, List.forall_mem_cons.2 ⟨subd8_6_124, List.forall_mem_cons.2 ⟨subd8_6_125, List.forall_mem_cons.2 ⟨subd8_6_126, List.forall_mem_cons.2 ⟨subd8_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_128 : subd8_6 [1, 3] = true := by decide +kernel
theorem subd8_6_129 : subd8_6 [1, 4] = true := by decide +kernel
theorem subd8_6_130 : subd8_6 [1, 5] = true := by decide +kernel
theorem subd8_6_131 : subd8_6 [1, 6] = true := by decide +kernel
theorem subd8_6_132 : subd8_6 [2, -8] = true := by decide +kernel
theorem subd8_6_133 : subd8_6 [2, -7] = true := by decide +kernel
theorem subd8_6_134 : subd8_6 [2, -6] = true := by decide +kernel
theorem subd8_6_135 : subd8_6 [2, -5] = true := by decide +kernel
theorem subd8_6_136 : subd8_6 [2, -4] = true := by decide +kernel
theorem subd8_6_137 : subd8_6 [2, -3] = true := by decide +kernel
theorem subd8_6_138 : subd8_6 [2, -2] = true := by decide +kernel
theorem subd8_6_139 : subd8_6 [2, -1] = true := by decide +kernel
theorem subd8_6_140 : subd8_6 [2, 0] = true := by decide +kernel
theorem subd8_6_141 : subd8_6 [2, 1] = true := by decide +kernel
theorem subd8_6_142 : subd8_6 [2, 2] = true := by decide +kernel
theorem subd8_6_143 : subd8_6 [2, 3] = true := by decide +kernel
theorem subd8_6_144 : subd8_6 [2, 4] = true := by decide +kernel
theorem subd8_6_145 : subd8_6 [2, 5] = true := by decide +kernel
theorem subd8_6_146 : subd8_6 [3, -7] = true := by decide +kernel
theorem subd8_6_147 : subd8_6 [3, -6] = true := by decide +kernel
theorem subd8_6_148 : subd8_6 [3, -5] = true := by decide +kernel
theorem subd8_6_149 : subd8_6 [3, -4] = true := by decide +kernel
theorem subd8_6_150 : subd8_6 [3, -3] = true := by decide +kernel
theorem subd8_6_151 : subd8_6 [3, -2] = true := by decide +kernel
theorem subd8_6_152 : subd8_6 [3, -1] = true := by decide +kernel
theorem subd8_6_153 : subd8_6 [3, 0] = true := by decide +kernel
theorem subd8_6_154 : subd8_6 [3, 1] = true := by decide +kernel
theorem subd8_6_155 : subd8_6 [3, 2] = true := by decide +kernel
theorem subd8_6_156 : subd8_6 [3, 3] = true := by decide +kernel
theorem subd8_6_157 : subd8_6 [3, 4] = true := by decide +kernel
theorem subd8_6_158 : subd8_6 [3, 5] = true := by decide +kernel
theorem subd8_6_159 : subd8_6 [4, -7] = true := by decide +kernel
theorem sbd8_6_4 : ∀ q ∈ blkd8_6_4, subd8_6 q = true := by
  unfold blkd8_6_4
  exact List.forall_mem_cons.2 ⟨subd8_6_128, List.forall_mem_cons.2 ⟨subd8_6_129, List.forall_mem_cons.2 ⟨subd8_6_130, List.forall_mem_cons.2 ⟨subd8_6_131, List.forall_mem_cons.2 ⟨subd8_6_132, List.forall_mem_cons.2 ⟨subd8_6_133, List.forall_mem_cons.2 ⟨subd8_6_134, List.forall_mem_cons.2 ⟨subd8_6_135, List.forall_mem_cons.2 ⟨subd8_6_136, List.forall_mem_cons.2 ⟨subd8_6_137, List.forall_mem_cons.2 ⟨subd8_6_138, List.forall_mem_cons.2 ⟨subd8_6_139, List.forall_mem_cons.2 ⟨subd8_6_140, List.forall_mem_cons.2 ⟨subd8_6_141, List.forall_mem_cons.2 ⟨subd8_6_142, List.forall_mem_cons.2 ⟨subd8_6_143, List.forall_mem_cons.2 ⟨subd8_6_144, List.forall_mem_cons.2 ⟨subd8_6_145, List.forall_mem_cons.2 ⟨subd8_6_146, List.forall_mem_cons.2 ⟨subd8_6_147, List.forall_mem_cons.2 ⟨subd8_6_148, List.forall_mem_cons.2 ⟨subd8_6_149, List.forall_mem_cons.2 ⟨subd8_6_150, List.forall_mem_cons.2 ⟨subd8_6_151, List.forall_mem_cons.2 ⟨subd8_6_152, List.forall_mem_cons.2 ⟨subd8_6_153, List.forall_mem_cons.2 ⟨subd8_6_154, List.forall_mem_cons.2 ⟨subd8_6_155, List.forall_mem_cons.2 ⟨subd8_6_156, List.forall_mem_cons.2 ⟨subd8_6_157, List.forall_mem_cons.2 ⟨subd8_6_158, List.forall_mem_cons.2 ⟨subd8_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_160 : subd8_6 [4, -6] = true := by decide +kernel
theorem subd8_6_161 : subd8_6 [4, -5] = true := by decide +kernel
theorem subd8_6_162 : subd8_6 [4, -4] = true := by decide +kernel
theorem subd8_6_163 : subd8_6 [4, -3] = true := by decide +kernel
theorem subd8_6_164 : subd8_6 [4, -2] = true := by decide +kernel
theorem subd8_6_165 : subd8_6 [4, -1] = true := by decide +kernel
theorem subd8_6_166 : subd8_6 [4, 0] = true := by decide +kernel
theorem subd8_6_167 : subd8_6 [4, 1] = true := by decide +kernel
theorem subd8_6_168 : subd8_6 [4, 2] = true := by decide +kernel
theorem subd8_6_169 : subd8_6 [4, 3] = true := by decide +kernel
theorem subd8_6_170 : subd8_6 [4, 4] = true := by decide +kernel
theorem subd8_6_171 : subd8_6 [5, -6] = true := by decide +kernel
theorem subd8_6_172 : subd8_6 [5, -5] = true := by decide +kernel
theorem subd8_6_173 : subd8_6 [5, -4] = true := by decide +kernel
theorem subd8_6_174 : subd8_6 [5, -3] = true := by decide +kernel
theorem subd8_6_175 : subd8_6 [5, -2] = true := by decide +kernel
theorem subd8_6_176 : subd8_6 [5, -1] = true := by decide +kernel
theorem subd8_6_177 : subd8_6 [5, 0] = true := by decide +kernel
theorem subd8_6_178 : subd8_6 [5, 1] = true := by decide +kernel
theorem subd8_6_179 : subd8_6 [5, 2] = true := by decide +kernel
theorem subd8_6_180 : subd8_6 [6] = true := by decide +kernel
theorem sbd8_6_5 : ∀ q ∈ blkd8_6_5, subd8_6 q = true := by
  unfold blkd8_6_5
  exact List.forall_mem_cons.2 ⟨subd8_6_160, List.forall_mem_cons.2 ⟨subd8_6_161, List.forall_mem_cons.2 ⟨subd8_6_162, List.forall_mem_cons.2 ⟨subd8_6_163, List.forall_mem_cons.2 ⟨subd8_6_164, List.forall_mem_cons.2 ⟨subd8_6_165, List.forall_mem_cons.2 ⟨subd8_6_166, List.forall_mem_cons.2 ⟨subd8_6_167, List.forall_mem_cons.2 ⟨subd8_6_168, List.forall_mem_cons.2 ⟨subd8_6_169, List.forall_mem_cons.2 ⟨subd8_6_170, List.forall_mem_cons.2 ⟨subd8_6_171, List.forall_mem_cons.2 ⟨subd8_6_172, List.forall_mem_cons.2 ⟨subd8_6_173, List.forall_mem_cons.2 ⟨subd8_6_174, List.forall_mem_cons.2 ⟨subd8_6_175, List.forall_mem_cons.2 ⟨subd8_6_176, List.forall_mem_cons.2 ⟨subd8_6_177, List.forall_mem_cons.2 ⟨subd8_6_178, List.forall_mem_cons.2 ⟨subd8_6_179, List.forall_mem_cons.2 ⟨subd8_6_180, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
