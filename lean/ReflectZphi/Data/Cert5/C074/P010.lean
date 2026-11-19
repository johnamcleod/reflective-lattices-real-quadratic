import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_32 : sub9 [-5, -2, -9] = true := by decide +kernel
theorem sub9_33 : sub9 [-5, -2, -8] = true := by decide +kernel
theorem sub9_34 : sub9 [-5, -2, -7] = true := by decide +kernel
theorem sub9_35 : sub9 [-5, -2, -6] = true := by decide +kernel
theorem sub9_36 : sub9 [-5, -2, -5] = true := by decide +kernel
theorem sub9_37 : sub9 [-5, -2, -4] = true := by decide +kernel
theorem sub9_38 : sub9 [-5, -2, -3] = true := by decide +kernel
theorem sub9_39 : sub9 [-5, -2, -2] = true := by decide +kernel
theorem sub9_40 : sub9 [-5, -2, -1] = true := by decide +kernel
theorem sub9_41 : sub9 [-5, -2, 0] = true := by decide +kernel
theorem sub9_42 : sub9 [-5, -2, 1] = true := by decide +kernel
theorem sub9_43 : sub9 [-5, -2, 2] = true := by decide +kernel
theorem sub9_44 : sub9 [-5, -2, 3] = true := by decide +kernel
theorem sub9_45 : sub9 [-5, -2, 4] = true := by decide +kernel
theorem sub9_46 : sub9 [-5, -2, 5] = true := by decide +kernel
theorem sub9_47 : sub9 [-5, -1, -9] = true := by decide +kernel
theorem sub9_48 : sub9 [-5, -1, -8] = true := by decide +kernel
theorem sub9_49 : sub9 [-5, -1, -7] = true := by decide +kernel
theorem sub9_50 : sub9 [-5, -1, -6] = true := by decide +kernel
theorem sub9_51 : sub9 [-5, -1, -5] = true := by decide +kernel
theorem sub9_52 : sub9 [-5, -1, -4] = true := by decide +kernel
theorem sub9_53 : sub9 [-5, -1, -3] = true := by decide +kernel
theorem sub9_54 : sub9 [-5, -1, -2] = true := by decide +kernel
theorem sub9_55 : sub9 [-5, -1, -1] = true := by decide +kernel
theorem sub9_56 : sub9 [-5, -1, 0] = true := by decide +kernel
theorem sub9_57 : sub9 [-5, -1, 1] = true := by decide +kernel
theorem sub9_58 : sub9 [-5, -1, 2] = true := by decide +kernel
theorem sub9_59 : sub9 [-5, -1, 3] = true := by decide +kernel
theorem sub9_60 : sub9 [-5, -1, 4] = true := by decide +kernel
theorem sub9_61 : sub9 [-5, -1, 5] = true := by decide +kernel
theorem sub9_62 : sub9 [-5, 0, -9] = true := by decide +kernel
theorem sub9_63 : sub9 [-5, 0, -8] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_64 : sub9 [-5, 0, -7] = true := by decide +kernel
theorem sub9_65 : sub9 [-5, 0, -6] = true := by decide +kernel
theorem sub9_66 : sub9 [-5, 0, -5] = true := by decide +kernel
theorem sub9_67 : sub9 [-5, 0, -4] = true := by decide +kernel
theorem sub9_68 : sub9 [-5, 0, -3] = true := by decide +kernel
theorem sub9_69 : sub9 [-5, 0, -2] = true := by decide +kernel
theorem sub9_70 : sub9 [-5, 0, -1] = true := by decide +kernel
theorem sub9_71 : sub9 [-5, 0, 0] = true := by decide +kernel
theorem sub9_72 : sub9 [-5, 0, 1] = true := by decide +kernel
theorem sub9_73 : sub9 [-5, 0, 2] = true := by decide +kernel
theorem sub9_74 : sub9 [-5, 0, 3] = true := by decide +kernel
theorem sub9_75 : sub9 [-5, 0, 4] = true := by decide +kernel
theorem sub9_76 : sub9 [-5, 0, 5] = true := by decide +kernel
theorem sub9_77 : sub9 [-5, 1] = true := by decide +kernel
theorem sub9_78 : sub9 [-5, 2] = true := by decide +kernel
theorem sub9_79 : sub9 [-5, 3] = true := by decide +kernel
theorem sub9_80 : sub9 [-4, -9] = true := by decide +kernel
theorem sub9_81 : sub9 [-4, -8] = true := by decide +kernel
theorem sub9_82 : sub9 [-4, -7] = true := by decide +kernel
theorem sub9_83 : sub9 [-4, -6] = true := by decide +kernel
theorem sub9_84 : sub9 [-4, -5, -11] = true := by decide +kernel
theorem sub9_85 : sub9 [-4, -5, -10] = true := by decide +kernel
theorem sub9_86 : sub9 [-4, -5, -9] = true := by decide +kernel
theorem sub9_87 : sub9 [-4, -5, -8] = true := by decide +kernel
theorem sub9_88 : sub9 [-4, -5, -7] = true := by decide +kernel
theorem sub9_89 : sub9 [-4, -5, -6] = true := by decide +kernel
theorem sub9_90 : sub9 [-4, -5, -5] = true := by decide +kernel
theorem sub9_91 : sub9 [-4, -5, -4] = true := by decide +kernel
theorem sub9_92 : sub9 [-4, -5, -3] = true := by decide +kernel
theorem sub9_93 : sub9 [-4, -5, -2] = true := by decide +kernel
theorem sub9_94 : sub9 [-4, -5, -1] = true := by decide +kernel
theorem sub9_95 : sub9 [-4, -5, 0] = true := by decide +kernel
theorem sb9_2 : ∀ q ∈ blk9_2, sub9 q = true := by
  unfold blk9_2
  exact List.forall_mem_cons.2 ⟨sub9_64, List.forall_mem_cons.2 ⟨sub9_65, List.forall_mem_cons.2 ⟨sub9_66, List.forall_mem_cons.2 ⟨sub9_67, List.forall_mem_cons.2 ⟨sub9_68, List.forall_mem_cons.2 ⟨sub9_69, List.forall_mem_cons.2 ⟨sub9_70, List.forall_mem_cons.2 ⟨sub9_71, List.forall_mem_cons.2 ⟨sub9_72, List.forall_mem_cons.2 ⟨sub9_73, List.forall_mem_cons.2 ⟨sub9_74, List.forall_mem_cons.2 ⟨sub9_75, List.forall_mem_cons.2 ⟨sub9_76, List.forall_mem_cons.2 ⟨sub9_77, List.forall_mem_cons.2 ⟨sub9_78, List.forall_mem_cons.2 ⟨sub9_79, List.forall_mem_cons.2 ⟨sub9_80, List.forall_mem_cons.2 ⟨sub9_81, List.forall_mem_cons.2 ⟨sub9_82, List.forall_mem_cons.2 ⟨sub9_83, List.forall_mem_cons.2 ⟨sub9_84, List.forall_mem_cons.2 ⟨sub9_85, List.forall_mem_cons.2 ⟨sub9_86, List.forall_mem_cons.2 ⟨sub9_87, List.forall_mem_cons.2 ⟨sub9_88, List.forall_mem_cons.2 ⟨sub9_89, List.forall_mem_cons.2 ⟨sub9_90, List.forall_mem_cons.2 ⟨sub9_91, List.forall_mem_cons.2 ⟨sub9_92, List.forall_mem_cons.2 ⟨sub9_93, List.forall_mem_cons.2 ⟨sub9_94, List.forall_mem_cons.2 ⟨sub9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_96 : sub9 [-4, -5, 1] = true := by decide +kernel
theorem sub9_97 : sub9 [-4, -5, 2] = true := by decide +kernel
theorem sub9_98 : sub9 [-4, -5, 3] = true := by decide +kernel
theorem sub9_99 : sub9 [-4, -4, -11] = true := by decide +kernel
theorem sub9_100 : sub9 [-4, -4, -10] = true := by decide +kernel
theorem sub9_101 : sub9 [-4, -4, -9] = true := by decide +kernel
theorem sub9_102 : sub9 [-4, -4, -8] = true := by decide +kernel
theorem sub9_103 : sub9 [-4, -4, -7] = true := by decide +kernel
theorem sub9_104 : sub9 [-4, -4, -6] = true := by decide +kernel
theorem sub9_105 : sub9 [-4, -4, -5] = true := by decide +kernel
theorem sub9_106 : sub9 [-4, -4, -4] = true := by decide +kernel
theorem sub9_107 : sub9 [-4, -4, -3] = true := by decide +kernel
theorem sub9_108 : sub9 [-4, -4, -2] = true := by decide +kernel
theorem sub9_109 : sub9 [-4, -4, -1] = true := by decide +kernel
theorem sub9_110 : sub9 [-4, -4, 0] = true := by decide +kernel
theorem sub9_111 : sub9 [-4, -4, 1] = true := by decide +kernel
theorem sub9_112 : sub9 [-4, -4, 2] = true := by decide +kernel
theorem sub9_113 : sub9 [-4, -4, 3] = true := by decide +kernel
theorem sub9_114 : sub9 [-4, -4, 4] = true := by decide +kernel
theorem sub9_115 : sub9 [-4, -3, -11] = true := by decide +kernel
theorem sub9_116 : sub9 [-4, -3, -10] = true := by decide +kernel
theorem sub9_117 : sub9 [-4, -3, -9] = true := by decide +kernel
theorem sub9_118 : sub9 [-4, -3, -8] = true := by decide +kernel
theorem sub9_119 : sub9 [-4, -3, -7] = true := by decide +kernel
theorem sub9_120 : sub9 [-4, -3, -6] = true := by decide +kernel
theorem sub9_121 : sub9 [-4, -3, -5] = true := by decide +kernel
theorem sub9_122 : sub9 [-4, -3, -4] = true := by decide +kernel
theorem sub9_123 : sub9 [-4, -3, -3] = true := by decide +kernel
theorem sub9_124 : sub9 [-4, -3, -2] = true := by decide +kernel
theorem sub9_125 : sub9 [-4, -3, -1] = true := by decide +kernel
theorem sub9_126 : sub9 [-4, -3, 0] = true := by decide +kernel
theorem sub9_127 : sub9 [-4, -3, 1] = true := by decide +kernel
theorem sb9_3 : ∀ q ∈ blk9_3, sub9 q = true := by
  unfold blk9_3
  exact List.forall_mem_cons.2 ⟨sub9_96, List.forall_mem_cons.2 ⟨sub9_97, List.forall_mem_cons.2 ⟨sub9_98, List.forall_mem_cons.2 ⟨sub9_99, List.forall_mem_cons.2 ⟨sub9_100, List.forall_mem_cons.2 ⟨sub9_101, List.forall_mem_cons.2 ⟨sub9_102, List.forall_mem_cons.2 ⟨sub9_103, List.forall_mem_cons.2 ⟨sub9_104, List.forall_mem_cons.2 ⟨sub9_105, List.forall_mem_cons.2 ⟨sub9_106, List.forall_mem_cons.2 ⟨sub9_107, List.forall_mem_cons.2 ⟨sub9_108, List.forall_mem_cons.2 ⟨sub9_109, List.forall_mem_cons.2 ⟨sub9_110, List.forall_mem_cons.2 ⟨sub9_111, List.forall_mem_cons.2 ⟨sub9_112, List.forall_mem_cons.2 ⟨sub9_113, List.forall_mem_cons.2 ⟨sub9_114, List.forall_mem_cons.2 ⟨sub9_115, List.forall_mem_cons.2 ⟨sub9_116, List.forall_mem_cons.2 ⟨sub9_117, List.forall_mem_cons.2 ⟨sub9_118, List.forall_mem_cons.2 ⟨sub9_119, List.forall_mem_cons.2 ⟨sub9_120, List.forall_mem_cons.2 ⟨sub9_121, List.forall_mem_cons.2 ⟨sub9_122, List.forall_mem_cons.2 ⟨sub9_123, List.forall_mem_cons.2 ⟨sub9_124, List.forall_mem_cons.2 ⟨sub9_125, List.forall_mem_cons.2 ⟨sub9_126, List.forall_mem_cons.2 ⟨sub9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_128 : sub9 [-4, -3, 2] = true := by decide +kernel
theorem sub9_129 : sub9 [-4, -3, 3] = true := by decide +kernel
theorem sub9_130 : sub9 [-4, -3, 4] = true := by decide +kernel
theorem sub9_131 : sub9 [-4, -3, 5] = true := by decide +kernel
theorem sub9_132 : sub9 [-4, -2, -11] = true := by decide +kernel
theorem sub9_133 : sub9 [-4, -2, -10] = true := by decide +kernel
theorem sub9_134 : sub9 [-4, -2, -9] = true := by decide +kernel
theorem sub9_135 : sub9 [-4, -2, -8] = true := by decide +kernel
theorem sub9_136 : sub9 [-4, -2, -7] = true := by decide +kernel
theorem sub9_137 : sub9 [-4, -2, -6] = true := by decide +kernel
theorem sub9_138 : sub9 [-4, -2, -5] = true := by decide +kernel
theorem sub9_139 : sub9 [-4, -2, -4] = true := by decide +kernel
theorem sub9_140 : sub9 [-4, -2, -3] = true := by decide +kernel
theorem sub9_141 : sub9 [-4, -2, -2] = true := by decide +kernel
theorem sub9_142 : sub9 [-4, -2, -1] = true := by decide +kernel
theorem sub9_143 : sub9 [-4, -2, 0] = true := by decide +kernel
theorem sub9_144 : sub9 [-4, -2, 1] = true := by decide +kernel
theorem sub9_145 : sub9 [-4, -2, 2] = true := by decide +kernel
theorem sub9_146 : sub9 [-4, -2, 3] = true := by decide +kernel
theorem sub9_147 : sub9 [-4, -2, 4] = true := by decide +kernel
theorem sub9_148 : sub9 [-4, -2, 5] = true := by decide +kernel
theorem sub9_149 : sub9 [-4, -2, 6] = true := by decide +kernel
theorem sub9_150 : sub9 [-4, -1, -10] = true := by decide +kernel
theorem sub9_151 : sub9 [-4, -1, -9] = true := by decide +kernel
theorem sub9_152 : sub9 [-4, -1, -8] = true := by decide +kernel
theorem sub9_153 : sub9 [-4, -1, -7] = true := by decide +kernel
theorem sub9_154 : sub9 [-4, -1, -6] = true := by decide +kernel
theorem sub9_155 : sub9 [-4, -1, -5] = true := by decide +kernel
theorem sub9_156 : sub9 [-4, -1, -4] = true := by decide +kernel
theorem sub9_157 : sub9 [-4, -1, -3] = true := by decide +kernel
theorem sub9_158 : sub9 [-4, -1, -2] = true := by decide +kernel
theorem sub9_159 : sub9 [-4, -1, -1] = true := by decide +kernel
theorem sb9_4 : ∀ q ∈ blk9_4, sub9 q = true := by
  unfold blk9_4
  exact List.forall_mem_cons.2 ⟨sub9_128, List.forall_mem_cons.2 ⟨sub9_129, List.forall_mem_cons.2 ⟨sub9_130, List.forall_mem_cons.2 ⟨sub9_131, List.forall_mem_cons.2 ⟨sub9_132, List.forall_mem_cons.2 ⟨sub9_133, List.forall_mem_cons.2 ⟨sub9_134, List.forall_mem_cons.2 ⟨sub9_135, List.forall_mem_cons.2 ⟨sub9_136, List.forall_mem_cons.2 ⟨sub9_137, List.forall_mem_cons.2 ⟨sub9_138, List.forall_mem_cons.2 ⟨sub9_139, List.forall_mem_cons.2 ⟨sub9_140, List.forall_mem_cons.2 ⟨sub9_141, List.forall_mem_cons.2 ⟨sub9_142, List.forall_mem_cons.2 ⟨sub9_143, List.forall_mem_cons.2 ⟨sub9_144, List.forall_mem_cons.2 ⟨sub9_145, List.forall_mem_cons.2 ⟨sub9_146, List.forall_mem_cons.2 ⟨sub9_147, List.forall_mem_cons.2 ⟨sub9_148, List.forall_mem_cons.2 ⟨sub9_149, List.forall_mem_cons.2 ⟨sub9_150, List.forall_mem_cons.2 ⟨sub9_151, List.forall_mem_cons.2 ⟨sub9_152, List.forall_mem_cons.2 ⟨sub9_153, List.forall_mem_cons.2 ⟨sub9_154, List.forall_mem_cons.2 ⟨sub9_155, List.forall_mem_cons.2 ⟨sub9_156, List.forall_mem_cons.2 ⟨sub9_157, List.forall_mem_cons.2 ⟨sub9_158, List.forall_mem_cons.2 ⟨sub9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_160 : sub9 [-4, -1, 0] = true := by decide +kernel
theorem sub9_161 : sub9 [-4, -1, 1] = true := by decide +kernel
theorem sub9_162 : sub9 [-4, -1, 2] = true := by decide +kernel
theorem sub9_163 : sub9 [-4, -1, 3] = true := by decide +kernel
theorem sub9_164 : sub9 [-4, -1, 4] = true := by decide +kernel
theorem sub9_165 : sub9 [-4, -1, 5] = true := by decide +kernel
theorem sub9_166 : sub9 [-4, -1, 6] = true := by decide +kernel
theorem sub9_167 : sub9 [-4, 0, -10] = true := by decide +kernel
theorem sub9_168 : sub9 [-4, 0, -9] = true := by decide +kernel
theorem sub9_169 : sub9 [-4, 0, -8] = true := by decide +kernel
theorem sub9_170 : sub9 [-4, 0, -7] = true := by decide +kernel
theorem sub9_171 : sub9 [-4, 0, -6] = true := by decide +kernel
theorem sub9_172 : sub9 [-4, 0, -5] = true := by decide +kernel
theorem sub9_173 : sub9 [-4, 0, -4] = true := by decide +kernel
theorem sub9_174 : sub9 [-4, 0, -3] = true := by decide +kernel
theorem sub9_175 : sub9 [-4, 0, -2] = true := by decide +kernel
theorem sub9_176 : sub9 [-4, 0, -1] = true := by decide +kernel
theorem sub9_177 : sub9 [-4, 0, 0] = true := by decide +kernel
theorem sub9_178 : sub9 [-4, 0, 1] = true := by decide +kernel
theorem sub9_179 : sub9 [-4, 0, 2] = true := by decide +kernel
theorem sub9_180 : sub9 [-4, 0, 3] = true := by decide +kernel
theorem sub9_181 : sub9 [-4, 0, 4] = true := by decide +kernel
theorem sub9_182 : sub9 [-4, 0, 5] = true := by decide +kernel
theorem sub9_183 : sub9 [-4, 0, 6] = true := by decide +kernel
theorem sub9_184 : sub9 [-4, 0, 7] = true := by decide +kernel
theorem sub9_185 : sub9 [-4, 1, -9] = true := by decide +kernel
theorem sub9_186 : sub9 [-4, 1, -8] = true := by decide +kernel
theorem sub9_187 : sub9 [-4, 1, -7] = true := by decide +kernel
theorem sub9_188 : sub9 [-4, 1, -6] = true := by decide +kernel
theorem sub9_189 : sub9 [-4, 1, -5] = true := by decide +kernel
theorem sub9_190 : sub9 [-4, 1, -4] = true := by decide +kernel
theorem sub9_191 : sub9 [-4, 1, -3] = true := by decide +kernel
theorem sb9_5 : ∀ q ∈ blk9_5, sub9 q = true := by
  unfold blk9_5
  exact List.forall_mem_cons.2 ⟨sub9_160, List.forall_mem_cons.2 ⟨sub9_161, List.forall_mem_cons.2 ⟨sub9_162, List.forall_mem_cons.2 ⟨sub9_163, List.forall_mem_cons.2 ⟨sub9_164, List.forall_mem_cons.2 ⟨sub9_165, List.forall_mem_cons.2 ⟨sub9_166, List.forall_mem_cons.2 ⟨sub9_167, List.forall_mem_cons.2 ⟨sub9_168, List.forall_mem_cons.2 ⟨sub9_169, List.forall_mem_cons.2 ⟨sub9_170, List.forall_mem_cons.2 ⟨sub9_171, List.forall_mem_cons.2 ⟨sub9_172, List.forall_mem_cons.2 ⟨sub9_173, List.forall_mem_cons.2 ⟨sub9_174, List.forall_mem_cons.2 ⟨sub9_175, List.forall_mem_cons.2 ⟨sub9_176, List.forall_mem_cons.2 ⟨sub9_177, List.forall_mem_cons.2 ⟨sub9_178, List.forall_mem_cons.2 ⟨sub9_179, List.forall_mem_cons.2 ⟨sub9_180, List.forall_mem_cons.2 ⟨sub9_181, List.forall_mem_cons.2 ⟨sub9_182, List.forall_mem_cons.2 ⟨sub9_183, List.forall_mem_cons.2 ⟨sub9_184, List.forall_mem_cons.2 ⟨sub9_185, List.forall_mem_cons.2 ⟨sub9_186, List.forall_mem_cons.2 ⟨sub9_187, List.forall_mem_cons.2 ⟨sub9_188, List.forall_mem_cons.2 ⟨sub9_189, List.forall_mem_cons.2 ⟨sub9_190, List.forall_mem_cons.2 ⟨sub9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_192 : sub9 [-4, 1, -2] = true := by decide +kernel
theorem sub9_193 : sub9 [-4, 1, -1] = true := by decide +kernel
theorem sub9_194 : sub9 [-4, 1, 0] = true := by decide +kernel
theorem sub9_195 : sub9 [-4, 1, 1] = true := by decide +kernel
theorem sub9_196 : sub9 [-4, 1, 2] = true := by decide +kernel
theorem sub9_197 : sub9 [-4, 1, 3] = true := by decide +kernel
theorem sub9_198 : sub9 [-4, 1, 4] = true := by decide +kernel
theorem sub9_199 : sub9 [-4, 1, 5] = true := by decide +kernel
theorem sub9_200 : sub9 [-4, 1, 6] = true := by decide +kernel
theorem sub9_201 : sub9 [-4, 1, 7] = true := by decide +kernel
theorem sub9_202 : sub9 [-4, 2, -8] = true := by decide +kernel
theorem sub9_203 : sub9 [-4, 2, -7] = true := by decide +kernel
theorem sub9_204 : sub9 [-4, 2, -6] = true := by decide +kernel
theorem sub9_205 : sub9 [-4, 2, -5] = true := by decide +kernel
theorem sub9_206 : sub9 [-4, 2, -4] = true := by decide +kernel
theorem sub9_207 : sub9 [-4, 2, -3] = true := by decide +kernel
theorem sub9_208 : sub9 [-4, 2, -2] = true := by decide +kernel
theorem sub9_209 : sub9 [-4, 2, -1] = true := by decide +kernel
theorem sub9_210 : sub9 [-4, 2, 0] = true := by decide +kernel
theorem sub9_211 : sub9 [-4, 2, 1] = true := by decide +kernel
theorem sub9_212 : sub9 [-4, 2, 2] = true := by decide +kernel
theorem sub9_213 : sub9 [-4, 2, 3] = true := by decide +kernel
theorem sub9_214 : sub9 [-4, 2, 4] = true := by decide +kernel
theorem sub9_215 : sub9 [-4, 2, 5] = true := by decide +kernel
theorem sub9_216 : sub9 [-4, 2, 6] = true := by decide +kernel
theorem sub9_217 : sub9 [-4, 2, 7] = true := by decide +kernel
theorem sub9_218 : sub9 [-4, 3] = true := by decide +kernel
theorem sub9_219 : sub9 [-4, 4] = true := by decide +kernel
theorem sub9_220 : sub9 [-4, 5] = true := by decide +kernel
theorem sub9_221 : sub9 [-3, -9] = true := by decide +kernel
theorem sub9_222 : sub9 [-3, -8] = true := by decide +kernel
theorem sub9_223 : sub9 [-3, -7] = true := by decide +kernel
theorem sb9_6 : ∀ q ∈ blk9_6, sub9 q = true := by
  unfold blk9_6
  exact List.forall_mem_cons.2 ⟨sub9_192, List.forall_mem_cons.2 ⟨sub9_193, List.forall_mem_cons.2 ⟨sub9_194, List.forall_mem_cons.2 ⟨sub9_195, List.forall_mem_cons.2 ⟨sub9_196, List.forall_mem_cons.2 ⟨sub9_197, List.forall_mem_cons.2 ⟨sub9_198, List.forall_mem_cons.2 ⟨sub9_199, List.forall_mem_cons.2 ⟨sub9_200, List.forall_mem_cons.2 ⟨sub9_201, List.forall_mem_cons.2 ⟨sub9_202, List.forall_mem_cons.2 ⟨sub9_203, List.forall_mem_cons.2 ⟨sub9_204, List.forall_mem_cons.2 ⟨sub9_205, List.forall_mem_cons.2 ⟨sub9_206, List.forall_mem_cons.2 ⟨sub9_207, List.forall_mem_cons.2 ⟨sub9_208, List.forall_mem_cons.2 ⟨sub9_209, List.forall_mem_cons.2 ⟨sub9_210, List.forall_mem_cons.2 ⟨sub9_211, List.forall_mem_cons.2 ⟨sub9_212, List.forall_mem_cons.2 ⟨sub9_213, List.forall_mem_cons.2 ⟨sub9_214, List.forall_mem_cons.2 ⟨sub9_215, List.forall_mem_cons.2 ⟨sub9_216, List.forall_mem_cons.2 ⟨sub9_217, List.forall_mem_cons.2 ⟨sub9_218, List.forall_mem_cons.2 ⟨sub9_219, List.forall_mem_cons.2 ⟨sub9_220, List.forall_mem_cons.2 ⟨sub9_221, List.forall_mem_cons.2 ⟨sub9_222, List.forall_mem_cons.2 ⟨sub9_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_224 : sub9 [-3, -6] = true := by decide +kernel
theorem sub9_225 : sub9 [-3, -5, -11] = true := by decide +kernel
theorem sub9_226 : sub9 [-3, -5, -10] = true := by decide +kernel
theorem sub9_227 : sub9 [-3, -5, -9] = true := by decide +kernel
theorem sub9_228 : sub9 [-3, -5, -8] = true := by decide +kernel
theorem sub9_229 : sub9 [-3, -5, -7] = true := by decide +kernel
theorem sub9_230 : sub9 [-3, -5, -6] = true := by decide +kernel
theorem sub9_231 : sub9 [-3, -5, -5] = true := by decide +kernel
theorem sub9_232 : sub9 [-3, -5, -4] = true := by decide +kernel
theorem sub9_233 : sub9 [-3, -5, -3] = true := by decide +kernel
theorem sub9_234 : sub9 [-3, -5, -2] = true := by decide +kernel
theorem sub9_235 : sub9 [-3, -5, -1] = true := by decide +kernel
theorem sub9_236 : sub9 [-3, -5, 0] = true := by decide +kernel
theorem sub9_237 : sub9 [-3, -5, 1] = true := by decide +kernel
theorem sub9_238 : sub9 [-3, -5, 2] = true := by decide +kernel
theorem sub9_239 : sub9 [-3, -5, 3] = true := by decide +kernel
theorem sub9_240 : sub9 [-3, -5, 4] = true := by decide +kernel
theorem sub9_241 : sub9 [-3, -4, -11] = true := by decide +kernel
theorem sub9_242 : sub9 [-3, -4, -10] = true := by decide +kernel
theorem sub9_243 : sub9 [-3, -4, -9] = true := by decide +kernel
theorem sub9_244 : sub9 [-3, -4, -8] = true := by decide +kernel
theorem sub9_245 : sub9 [-3, -4, -7] = true := by decide +kernel
theorem sub9_246 : sub9 [-3, -4, -6] = true := by decide +kernel
theorem sub9_247 : sub9 [-3, -4, -5] = true := by decide +kernel
theorem sub9_248 : sub9 [-3, -4, -4] = true := by decide +kernel
theorem sub9_249 : sub9 [-3, -4, -3] = true := by decide +kernel
theorem sub9_250 : sub9 [-3, -4, -2] = true := by decide +kernel
theorem sub9_251 : sub9 [-3, -4, -1] = true := by decide +kernel
theorem sub9_252 : sub9 [-3, -4, 0] = true := by decide +kernel
theorem sub9_253 : sub9 [-3, -4, 1] = true := by decide +kernel
theorem sub9_254 : sub9 [-3, -4, 2] = true := by decide +kernel
theorem sub9_255 : sub9 [-3, -4, 3] = true := by decide +kernel
theorem sb9_7 : ∀ q ∈ blk9_7, sub9 q = true := by
  unfold blk9_7
  exact List.forall_mem_cons.2 ⟨sub9_224, List.forall_mem_cons.2 ⟨sub9_225, List.forall_mem_cons.2 ⟨sub9_226, List.forall_mem_cons.2 ⟨sub9_227, List.forall_mem_cons.2 ⟨sub9_228, List.forall_mem_cons.2 ⟨sub9_229, List.forall_mem_cons.2 ⟨sub9_230, List.forall_mem_cons.2 ⟨sub9_231, List.forall_mem_cons.2 ⟨sub9_232, List.forall_mem_cons.2 ⟨sub9_233, List.forall_mem_cons.2 ⟨sub9_234, List.forall_mem_cons.2 ⟨sub9_235, List.forall_mem_cons.2 ⟨sub9_236, List.forall_mem_cons.2 ⟨sub9_237, List.forall_mem_cons.2 ⟨sub9_238, List.forall_mem_cons.2 ⟨sub9_239, List.forall_mem_cons.2 ⟨sub9_240, List.forall_mem_cons.2 ⟨sub9_241, List.forall_mem_cons.2 ⟨sub9_242, List.forall_mem_cons.2 ⟨sub9_243, List.forall_mem_cons.2 ⟨sub9_244, List.forall_mem_cons.2 ⟨sub9_245, List.forall_mem_cons.2 ⟨sub9_246, List.forall_mem_cons.2 ⟨sub9_247, List.forall_mem_cons.2 ⟨sub9_248, List.forall_mem_cons.2 ⟨sub9_249, List.forall_mem_cons.2 ⟨sub9_250, List.forall_mem_cons.2 ⟨sub9_251, List.forall_mem_cons.2 ⟨sub9_252, List.forall_mem_cons.2 ⟨sub9_253, List.forall_mem_cons.2 ⟨sub9_254, List.forall_mem_cons.2 ⟨sub9_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_256 : sub9 [-3, -4, 4] = true := by decide +kernel
theorem sub9_257 : sub9 [-3, -4, 5] = true := by decide +kernel
theorem sub9_258 : sub9 [-3, -3, -11] = true := by decide +kernel
theorem sub9_259 : sub9 [-3, -3, -10] = true := by decide +kernel
theorem sub9_260 : sub9 [-3, -3, -9] = true := by decide +kernel
theorem sub9_261 : sub9 [-3, -3, -8] = true := by decide +kernel
theorem sub9_262 : sub9 [-3, -3, -7] = true := by decide +kernel
theorem sub9_263 : sub9 [-3, -3, -6] = true := by decide +kernel
theorem sub9_264 : sub9 [-3, -3, -5] = true := by decide +kernel
theorem sub9_265 : sub9 [-3, -3, -4] = true := by decide +kernel
theorem sub9_266 : sub9 [-3, -3, -3] = true := by decide +kernel
theorem sub9_267 : sub9 [-3, -3, -2] = true := by decide +kernel
theorem sub9_268 : sub9 [-3, -3, -1] = true := by decide +kernel
theorem sub9_269 : sub9 [-3, -3, 0] = true := by decide +kernel
theorem sub9_270 : sub9 [-3, -3, 1] = true := by decide +kernel
theorem sub9_271 : sub9 [-3, -3, 2] = true := by decide +kernel
theorem sub9_272 : sub9 [-3, -3, 3] = true := by decide +kernel
theorem sub9_273 : sub9 [-3, -3, 4] = true := by decide +kernel
theorem sub9_274 : sub9 [-3, -3, 5] = true := by decide +kernel
theorem sub9_275 : sub9 [-3, -3, 6] = true := by decide +kernel
theorem sub9_276 : sub9 [-3, -2, -11] = true := by decide +kernel
theorem sub9_277 : sub9 [-3, -2, -10] = true := by decide +kernel
theorem sub9_278 : sub9 [-3, -2, -9] = true := by decide +kernel
theorem sub9_279 : sub9 [-3, -2, -8] = true := by decide +kernel
theorem sub9_280 : sub9 [-3, -2, -7] = true := by decide +kernel
theorem sub9_281 : sub9 [-3, -2, -6] = true := by decide +kernel
theorem sub9_282 : sub9 [-3, -2, -5] = true := by decide +kernel
theorem sub9_283 : sub9 [-3, -2, -4] = true := by decide +kernel
theorem sub9_284 : sub9 [-3, -2, -3] = true := by decide +kernel
theorem sub9_285 : sub9 [-3, -2, -2] = true := by decide +kernel
theorem sub9_286 : sub9 [-3, -2, -1] = true := by decide +kernel
theorem sub9_287 : sub9 [-3, -2, 0] = true := by decide +kernel
theorem sb9_8 : ∀ q ∈ blk9_8, sub9 q = true := by
  unfold blk9_8
  exact List.forall_mem_cons.2 ⟨sub9_256, List.forall_mem_cons.2 ⟨sub9_257, List.forall_mem_cons.2 ⟨sub9_258, List.forall_mem_cons.2 ⟨sub9_259, List.forall_mem_cons.2 ⟨sub9_260, List.forall_mem_cons.2 ⟨sub9_261, List.forall_mem_cons.2 ⟨sub9_262, List.forall_mem_cons.2 ⟨sub9_263, List.forall_mem_cons.2 ⟨sub9_264, List.forall_mem_cons.2 ⟨sub9_265, List.forall_mem_cons.2 ⟨sub9_266, List.forall_mem_cons.2 ⟨sub9_267, List.forall_mem_cons.2 ⟨sub9_268, List.forall_mem_cons.2 ⟨sub9_269, List.forall_mem_cons.2 ⟨sub9_270, List.forall_mem_cons.2 ⟨sub9_271, List.forall_mem_cons.2 ⟨sub9_272, List.forall_mem_cons.2 ⟨sub9_273, List.forall_mem_cons.2 ⟨sub9_274, List.forall_mem_cons.2 ⟨sub9_275, List.forall_mem_cons.2 ⟨sub9_276, List.forall_mem_cons.2 ⟨sub9_277, List.forall_mem_cons.2 ⟨sub9_278, List.forall_mem_cons.2 ⟨sub9_279, List.forall_mem_cons.2 ⟨sub9_280, List.forall_mem_cons.2 ⟨sub9_281, List.forall_mem_cons.2 ⟨sub9_282, List.forall_mem_cons.2 ⟨sub9_283, List.forall_mem_cons.2 ⟨sub9_284, List.forall_mem_cons.2 ⟨sub9_285, List.forall_mem_cons.2 ⟨sub9_286, List.forall_mem_cons.2 ⟨sub9_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_288 : sub9 [-3, -2, 1] = true := by decide +kernel
theorem sub9_289 : sub9 [-3, -2, 2] = true := by decide +kernel
theorem sub9_290 : sub9 [-3, -2, 3] = true := by decide +kernel
theorem sub9_291 : sub9 [-3, -2, 4] = true := by decide +kernel
theorem sub9_292 : sub9 [-3, -2, 5] = true := by decide +kernel
theorem sub9_293 : sub9 [-3, -2, 6] = true := by decide +kernel
theorem sub9_294 : sub9 [-3, -2, 7] = true := by decide +kernel
theorem sub9_295 : sub9 [-3, -1, -11] = true := by decide +kernel
theorem sub9_296 : sub9 [-3, -1, -10] = true := by decide +kernel
theorem sub9_297 : sub9 [-3, -1, -9] = true := by decide +kernel
theorem sub9_298 : sub9 [-3, -1, -8] = true := by decide +kernel
theorem sub9_299 : sub9 [-3, -1, -7] = true := by decide +kernel
theorem sub9_300 : sub9 [-3, -1, -6] = true := by decide +kernel
theorem sub9_301 : sub9 [-3, -1, -5] = true := by decide +kernel
theorem sub9_302 : sub9 [-3, -1, -4] = true := by decide +kernel
theorem sub9_303 : sub9 [-3, -1, -3] = true := by decide +kernel
theorem sub9_304 : sub9 [-3, -1, -2] = true := by decide +kernel
theorem sub9_305 : sub9 [-3, -1, -1] = true := by decide +kernel
theorem sub9_306 : sub9 [-3, -1, 0] = true := by decide +kernel
theorem sub9_307 : sub9 [-3, -1, 1] = true := by decide +kernel
theorem sub9_308 : sub9 [-3, -1, 2] = true := by decide +kernel
theorem sub9_309 : sub9 [-3, -1, 3] = true := by decide +kernel
theorem sub9_310 : sub9 [-3, -1, 4] = true := by decide +kernel
theorem sub9_311 : sub9 [-3, -1, 5] = true := by decide +kernel
theorem sub9_312 : sub9 [-3, -1, 6] = true := by decide +kernel
theorem sub9_313 : sub9 [-3, -1, 7] = true := by decide +kernel
theorem sub9_314 : sub9 [-3, 0, -10] = true := by decide +kernel
theorem sub9_315 : sub9 [-3, 0, -9] = true := by decide +kernel
theorem sub9_316 : sub9 [-3, 0, -8] = true := by decide +kernel
theorem sub9_317 : sub9 [-3, 0, -7] = true := by decide +kernel
theorem sub9_318 : sub9 [-3, 0, -6] = true := by decide +kernel
theorem sub9_319 : sub9 [-3, 0, -5] = true := by decide +kernel
theorem sb9_9 : ∀ q ∈ blk9_9, sub9 q = true := by
  unfold blk9_9
  exact List.forall_mem_cons.2 ⟨sub9_288, List.forall_mem_cons.2 ⟨sub9_289, List.forall_mem_cons.2 ⟨sub9_290, List.forall_mem_cons.2 ⟨sub9_291, List.forall_mem_cons.2 ⟨sub9_292, List.forall_mem_cons.2 ⟨sub9_293, List.forall_mem_cons.2 ⟨sub9_294, List.forall_mem_cons.2 ⟨sub9_295, List.forall_mem_cons.2 ⟨sub9_296, List.forall_mem_cons.2 ⟨sub9_297, List.forall_mem_cons.2 ⟨sub9_298, List.forall_mem_cons.2 ⟨sub9_299, List.forall_mem_cons.2 ⟨sub9_300, List.forall_mem_cons.2 ⟨sub9_301, List.forall_mem_cons.2 ⟨sub9_302, List.forall_mem_cons.2 ⟨sub9_303, List.forall_mem_cons.2 ⟨sub9_304, List.forall_mem_cons.2 ⟨sub9_305, List.forall_mem_cons.2 ⟨sub9_306, List.forall_mem_cons.2 ⟨sub9_307, List.forall_mem_cons.2 ⟨sub9_308, List.forall_mem_cons.2 ⟨sub9_309, List.forall_mem_cons.2 ⟨sub9_310, List.forall_mem_cons.2 ⟨sub9_311, List.forall_mem_cons.2 ⟨sub9_312, List.forall_mem_cons.2 ⟨sub9_313, List.forall_mem_cons.2 ⟨sub9_314, List.forall_mem_cons.2 ⟨sub9_315, List.forall_mem_cons.2 ⟨sub9_316, List.forall_mem_cons.2 ⟨sub9_317, List.forall_mem_cons.2 ⟨sub9_318, List.forall_mem_cons.2 ⟨sub9_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_320 : sub9 [-3, 0, -4] = true := by decide +kernel
theorem sub9_321 : sub9 [-3, 0, -3] = true := by decide +kernel
theorem sub9_322 : sub9 [-3, 0, -2] = true := by decide +kernel
theorem sub9_323 : sub9 [-3, 0, -1] = true := by decide +kernel
theorem sub9_324 : sub9 [-3, 0, 0] = true := by decide +kernel
theorem sub9_325 : sub9 [-3, 0, 1] = true := by decide +kernel
theorem sub9_326 : sub9 [-3, 0, 2] = true := by decide +kernel
theorem sub9_327 : sub9 [-3, 0, 3] = true := by decide +kernel
theorem sub9_328 : sub9 [-3, 0, 4] = true := by decide +kernel
theorem sub9_329 : sub9 [-3, 0, 5] = true := by decide +kernel
theorem sub9_330 : sub9 [-3, 0, 6] = true := by decide +kernel
theorem sub9_331 : sub9 [-3, 0, 7] = true := by decide +kernel
theorem sub9_332 : sub9 [-3, 0, 8] = true := by decide +kernel
theorem sub9_333 : sub9 [-3, 1, -10] = true := by decide +kernel
theorem sub9_334 : sub9 [-3, 1, -9] = true := by decide +kernel
theorem sub9_335 : sub9 [-3, 1, -8] = true := by decide +kernel
theorem sub9_336 : sub9 [-3, 1, -7] = true := by decide +kernel
theorem sub9_337 : sub9 [-3, 1, -6] = true := by decide +kernel
theorem sub9_338 : sub9 [-3, 1, -5] = true := by decide +kernel
theorem sub9_339 : sub9 [-3, 1, -4] = true := by decide +kernel
theorem sub9_340 : sub9 [-3, 1, -3] = true := by decide +kernel
theorem sub9_341 : sub9 [-3, 1, -2] = true := by decide +kernel
theorem sub9_342 : sub9 [-3, 1, -1] = true := by decide +kernel
theorem sub9_343 : sub9 [-3, 1, 0] = true := by decide +kernel
theorem sub9_344 : sub9 [-3, 1, 1] = true := by decide +kernel
theorem sub9_345 : sub9 [-3, 1, 2] = true := by decide +kernel
theorem sub9_346 : sub9 [-3, 1, 3] = true := by decide +kernel
theorem sub9_347 : sub9 [-3, 1, 4] = true := by decide +kernel
theorem sub9_348 : sub9 [-3, 1, 5] = true := by decide +kernel
theorem sub9_349 : sub9 [-3, 1, 6] = true := by decide +kernel
theorem sub9_350 : sub9 [-3, 1, 7] = true := by decide +kernel
theorem sub9_351 : sub9 [-3, 1, 8] = true := by decide +kernel
theorem sb9_10 : ∀ q ∈ blk9_10, sub9 q = true := by
  unfold blk9_10
  exact List.forall_mem_cons.2 ⟨sub9_320, List.forall_mem_cons.2 ⟨sub9_321, List.forall_mem_cons.2 ⟨sub9_322, List.forall_mem_cons.2 ⟨sub9_323, List.forall_mem_cons.2 ⟨sub9_324, List.forall_mem_cons.2 ⟨sub9_325, List.forall_mem_cons.2 ⟨sub9_326, List.forall_mem_cons.2 ⟨sub9_327, List.forall_mem_cons.2 ⟨sub9_328, List.forall_mem_cons.2 ⟨sub9_329, List.forall_mem_cons.2 ⟨sub9_330, List.forall_mem_cons.2 ⟨sub9_331, List.forall_mem_cons.2 ⟨sub9_332, List.forall_mem_cons.2 ⟨sub9_333, List.forall_mem_cons.2 ⟨sub9_334, List.forall_mem_cons.2 ⟨sub9_335, List.forall_mem_cons.2 ⟨sub9_336, List.forall_mem_cons.2 ⟨sub9_337, List.forall_mem_cons.2 ⟨sub9_338, List.forall_mem_cons.2 ⟨sub9_339, List.forall_mem_cons.2 ⟨sub9_340, List.forall_mem_cons.2 ⟨sub9_341, List.forall_mem_cons.2 ⟨sub9_342, List.forall_mem_cons.2 ⟨sub9_343, List.forall_mem_cons.2 ⟨sub9_344, List.forall_mem_cons.2 ⟨sub9_345, List.forall_mem_cons.2 ⟨sub9_346, List.forall_mem_cons.2 ⟨sub9_347, List.forall_mem_cons.2 ⟨sub9_348, List.forall_mem_cons.2 ⟨sub9_349, List.forall_mem_cons.2 ⟨sub9_350, List.forall_mem_cons.2 ⟨sub9_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_352 : sub9 [-3, 2, -9] = true := by decide +kernel
theorem sub9_353 : sub9 [-3, 2, -8] = true := by decide +kernel
theorem sub9_354 : sub9 [-3, 2, -7] = true := by decide +kernel
theorem sub9_355 : sub9 [-3, 2, -6] = true := by decide +kernel
theorem sub9_356 : sub9 [-3, 2, -5] = true := by decide +kernel
theorem sub9_357 : sub9 [-3, 2, -4] = true := by decide +kernel
theorem sub9_358 : sub9 [-3, 2, -3] = true := by decide +kernel
theorem sub9_359 : sub9 [-3, 2, -2] = true := by decide +kernel
theorem sub9_360 : sub9 [-3, 2, -1] = true := by decide +kernel
theorem sub9_361 : sub9 [-3, 2, 0] = true := by decide +kernel
theorem sub9_362 : sub9 [-3, 2, 1] = true := by decide +kernel
theorem sub9_363 : sub9 [-3, 2, 2] = true := by decide +kernel
theorem sub9_364 : sub9 [-3, 2, 3] = true := by decide +kernel
theorem sub9_365 : sub9 [-3, 2, 4] = true := by decide +kernel
theorem sub9_366 : sub9 [-3, 2, 5] = true := by decide +kernel
theorem sub9_367 : sub9 [-3, 2, 6] = true := by decide +kernel
theorem sub9_368 : sub9 [-3, 2, 7] = true := by decide +kernel
theorem sub9_369 : sub9 [-3, 2, 8] = true := by decide +kernel
theorem sub9_370 : sub9 [-3, 3, -7] = true := by decide +kernel
theorem sub9_371 : sub9 [-3, 3, -6] = true := by decide +kernel
theorem sub9_372 : sub9 [-3, 3, -5] = true := by decide +kernel
theorem sub9_373 : sub9 [-3, 3, -4] = true := by decide +kernel
theorem sub9_374 : sub9 [-3, 3, -3] = true := by decide +kernel
theorem sub9_375 : sub9 [-3, 3, -2] = true := by decide +kernel
theorem sub9_376 : sub9 [-3, 3, -1] = true := by decide +kernel
theorem sub9_377 : sub9 [-3, 3, 0] = true := by decide +kernel
theorem sub9_378 : sub9 [-3, 3, 1] = true := by decide +kernel
theorem sub9_379 : sub9 [-3, 3, 2] = true := by decide +kernel
theorem sub9_380 : sub9 [-3, 3, 3] = true := by decide +kernel
theorem sub9_381 : sub9 [-3, 3, 4] = true := by decide +kernel
theorem sub9_382 : sub9 [-3, 3, 5] = true := by decide +kernel
theorem sub9_383 : sub9 [-3, 3, 6] = true := by decide +kernel
theorem sb9_11 : ∀ q ∈ blk9_11, sub9 q = true := by
  unfold blk9_11
  exact List.forall_mem_cons.2 ⟨sub9_352, List.forall_mem_cons.2 ⟨sub9_353, List.forall_mem_cons.2 ⟨sub9_354, List.forall_mem_cons.2 ⟨sub9_355, List.forall_mem_cons.2 ⟨sub9_356, List.forall_mem_cons.2 ⟨sub9_357, List.forall_mem_cons.2 ⟨sub9_358, List.forall_mem_cons.2 ⟨sub9_359, List.forall_mem_cons.2 ⟨sub9_360, List.forall_mem_cons.2 ⟨sub9_361, List.forall_mem_cons.2 ⟨sub9_362, List.forall_mem_cons.2 ⟨sub9_363, List.forall_mem_cons.2 ⟨sub9_364, List.forall_mem_cons.2 ⟨sub9_365, List.forall_mem_cons.2 ⟨sub9_366, List.forall_mem_cons.2 ⟨sub9_367, List.forall_mem_cons.2 ⟨sub9_368, List.forall_mem_cons.2 ⟨sub9_369, List.forall_mem_cons.2 ⟨sub9_370, List.forall_mem_cons.2 ⟨sub9_371, List.forall_mem_cons.2 ⟨sub9_372, List.forall_mem_cons.2 ⟨sub9_373, List.forall_mem_cons.2 ⟨sub9_374, List.forall_mem_cons.2 ⟨sub9_375, List.forall_mem_cons.2 ⟨sub9_376, List.forall_mem_cons.2 ⟨sub9_377, List.forall_mem_cons.2 ⟨sub9_378, List.forall_mem_cons.2 ⟨sub9_379, List.forall_mem_cons.2 ⟨sub9_380, List.forall_mem_cons.2 ⟨sub9_381, List.forall_mem_cons.2 ⟨sub9_382, List.forall_mem_cons.2 ⟨sub9_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_384 : sub9 [-3, 3, 7] = true := by decide +kernel
theorem sub9_385 : sub9 [-3, 3, 8] = true := by decide +kernel
theorem sub9_386 : sub9 [-3, 4] = true := by decide +kernel
theorem sub9_387 : sub9 [-3, 5] = true := by decide +kernel
theorem sub9_388 : sub9 [-3, 6] = true := by decide +kernel
theorem sub9_389 : sub9 [-2, -9] = true := by decide +kernel
theorem sub9_390 : sub9 [-2, -8] = true := by decide +kernel
theorem sub9_391 : sub9 [-2, -7] = true := by decide +kernel
theorem sub9_392 : sub9 [-2, -6, -11] = true := by decide +kernel
theorem sub9_393 : sub9 [-2, -6, -10] = true := by decide +kernel
theorem sub9_394 : sub9 [-2, -6, -9] = true := by decide +kernel
theorem sub9_395 : sub9 [-2, -6, -8] = true := by decide +kernel
theorem sub9_396 : sub9 [-2, -6, -7] = true := by decide +kernel
theorem sub9_397 : sub9 [-2, -6, -6] = true := by decide +kernel
theorem sub9_398 : sub9 [-2, -6, -5] = true := by decide +kernel
theorem sub9_399 : sub9 [-2, -6, -4] = true := by decide +kernel
theorem sub9_400 : sub9 [-2, -6, -3] = true := by decide +kernel
theorem sub9_401 : sub9 [-2, -6, -2] = true := by decide +kernel
theorem sub9_402 : sub9 [-2, -6, -1] = true := by decide +kernel
theorem sub9_403 : sub9 [-2, -6, 0] = true := by decide +kernel
theorem sub9_404 : sub9 [-2, -6, 1] = true := by decide +kernel
theorem sub9_405 : sub9 [-2, -6, 2] = true := by decide +kernel
theorem sub9_406 : sub9 [-2, -6, 3] = true := by decide +kernel
theorem sub9_407 : sub9 [-2, -5, -11] = true := by decide +kernel
theorem sub9_408 : sub9 [-2, -5, -10] = true := by decide +kernel
theorem sub9_409 : sub9 [-2, -5, -9] = true := by decide +kernel
theorem sub9_410 : sub9 [-2, -5, -8] = true := by decide +kernel
theorem sub9_411 : sub9 [-2, -5, -7] = true := by decide +kernel
theorem sub9_412 : sub9 [-2, -5, -6] = true := by decide +kernel
theorem sub9_413 : sub9 [-2, -5, -5] = true := by decide +kernel
theorem sub9_414 : sub9 [-2, -5, -4] = true := by decide +kernel
theorem sub9_415 : sub9 [-2, -5, -3] = true := by decide +kernel
theorem sb9_12 : ∀ q ∈ blk9_12, sub9 q = true := by
  unfold blk9_12
  exact List.forall_mem_cons.2 ⟨sub9_384, List.forall_mem_cons.2 ⟨sub9_385, List.forall_mem_cons.2 ⟨sub9_386, List.forall_mem_cons.2 ⟨sub9_387, List.forall_mem_cons.2 ⟨sub9_388, List.forall_mem_cons.2 ⟨sub9_389, List.forall_mem_cons.2 ⟨sub9_390, List.forall_mem_cons.2 ⟨sub9_391, List.forall_mem_cons.2 ⟨sub9_392, List.forall_mem_cons.2 ⟨sub9_393, List.forall_mem_cons.2 ⟨sub9_394, List.forall_mem_cons.2 ⟨sub9_395, List.forall_mem_cons.2 ⟨sub9_396, List.forall_mem_cons.2 ⟨sub9_397, List.forall_mem_cons.2 ⟨sub9_398, List.forall_mem_cons.2 ⟨sub9_399, List.forall_mem_cons.2 ⟨sub9_400, List.forall_mem_cons.2 ⟨sub9_401, List.forall_mem_cons.2 ⟨sub9_402, List.forall_mem_cons.2 ⟨sub9_403, List.forall_mem_cons.2 ⟨sub9_404, List.forall_mem_cons.2 ⟨sub9_405, List.forall_mem_cons.2 ⟨sub9_406, List.forall_mem_cons.2 ⟨sub9_407, List.forall_mem_cons.2 ⟨sub9_408, List.forall_mem_cons.2 ⟨sub9_409, List.forall_mem_cons.2 ⟨sub9_410, List.forall_mem_cons.2 ⟨sub9_411, List.forall_mem_cons.2 ⟨sub9_412, List.forall_mem_cons.2 ⟨sub9_413, List.forall_mem_cons.2 ⟨sub9_414, List.forall_mem_cons.2 ⟨sub9_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_416 : sub9 [-2, -5, -2] = true := by decide +kernel
theorem sub9_417 : sub9 [-2, -5, -1] = true := by decide +kernel
theorem sub9_418 : sub9 [-2, -5, 0] = true := by decide +kernel
theorem sub9_419 : sub9 [-2, -5, 1] = true := by decide +kernel
theorem sub9_420 : sub9 [-2, -5, 2] = true := by decide +kernel
theorem sub9_421 : sub9 [-2, -5, 3] = true := by decide +kernel
theorem sub9_422 : sub9 [-2, -5, 4] = true := by decide +kernel
theorem sub9_423 : sub9 [-2, -5, 5] = true := by decide +kernel
theorem sub9_424 : sub9 [-2, -4, -12] = true := by decide +kernel
theorem sub9_425 : sub9 [-2, -4, -11] = true := by decide +kernel
theorem sub9_426 : sub9 [-2, -4, -10] = true := by decide +kernel
theorem sub9_427 : sub9 [-2, -4, -9] = true := by decide +kernel
theorem sub9_428 : sub9 [-2, -4, -8] = true := by decide +kernel
theorem sub9_429 : sub9 [-2, -4, -7] = true := by decide +kernel
theorem sub9_430 : sub9 [-2, -4, -6] = true := by decide +kernel
theorem sub9_431 : sub9 [-2, -4, -5] = true := by decide +kernel
theorem sub9_432 : sub9 [-2, -4, -4] = true := by decide +kernel
theorem sub9_433 : sub9 [-2, -4, -3] = true := by decide +kernel
theorem sub9_434 : sub9 [-2, -4, -2] = true := by decide +kernel
theorem sub9_435 : sub9 [-2, -4, -1] = true := by decide +kernel
theorem sub9_436 : sub9 [-2, -4, 0] = true := by decide +kernel
theorem sub9_437 : sub9 [-2, -4, 1] = true := by decide +kernel
theorem sub9_438 : sub9 [-2, -4, 2] = true := by decide +kernel
theorem sub9_439 : sub9 [-2, -4, 3] = true := by decide +kernel
theorem sub9_440 : sub9 [-2, -4, 4] = true := by decide +kernel
theorem sub9_441 : sub9 [-2, -4, 5] = true := by decide +kernel
theorem sub9_442 : sub9 [-2, -4, 6] = true := by decide +kernel
theorem sub9_443 : sub9 [-2, -3, -12] = true := by decide +kernel
theorem sub9_444 : sub9 [-2, -3, -11] = true := by decide +kernel
theorem sub9_445 : sub9 [-2, -3, -10] = true := by decide +kernel
theorem sub9_446 : sub9 [-2, -3, -9] = true := by decide +kernel
theorem sub9_447 : sub9 [-2, -3, -8] = true := by decide +kernel
theorem sb9_13 : ∀ q ∈ blk9_13, sub9 q = true := by
  unfold blk9_13
  exact List.forall_mem_cons.2 ⟨sub9_416, List.forall_mem_cons.2 ⟨sub9_417, List.forall_mem_cons.2 ⟨sub9_418, List.forall_mem_cons.2 ⟨sub9_419, List.forall_mem_cons.2 ⟨sub9_420, List.forall_mem_cons.2 ⟨sub9_421, List.forall_mem_cons.2 ⟨sub9_422, List.forall_mem_cons.2 ⟨sub9_423, List.forall_mem_cons.2 ⟨sub9_424, List.forall_mem_cons.2 ⟨sub9_425, List.forall_mem_cons.2 ⟨sub9_426, List.forall_mem_cons.2 ⟨sub9_427, List.forall_mem_cons.2 ⟨sub9_428, List.forall_mem_cons.2 ⟨sub9_429, List.forall_mem_cons.2 ⟨sub9_430, List.forall_mem_cons.2 ⟨sub9_431, List.forall_mem_cons.2 ⟨sub9_432, List.forall_mem_cons.2 ⟨sub9_433, List.forall_mem_cons.2 ⟨sub9_434, List.forall_mem_cons.2 ⟨sub9_435, List.forall_mem_cons.2 ⟨sub9_436, List.forall_mem_cons.2 ⟨sub9_437, List.forall_mem_cons.2 ⟨sub9_438, List.forall_mem_cons.2 ⟨sub9_439, List.forall_mem_cons.2 ⟨sub9_440, List.forall_mem_cons.2 ⟨sub9_441, List.forall_mem_cons.2 ⟨sub9_442, List.forall_mem_cons.2 ⟨sub9_443, List.forall_mem_cons.2 ⟨sub9_444, List.forall_mem_cons.2 ⟨sub9_445, List.forall_mem_cons.2 ⟨sub9_446, List.forall_mem_cons.2 ⟨sub9_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_448 : sub9 [-2, -3, -7] = true := by decide +kernel
theorem sub9_449 : sub9 [-2, -3, -6] = true := by decide +kernel
theorem sub9_450 : sub9 [-2, -3, -5] = true := by decide +kernel
theorem sub9_451 : sub9 [-2, -3, -4] = true := by decide +kernel
theorem sub9_452 : sub9 [-2, -3, -3] = true := by decide +kernel
theorem sub9_453 : sub9 [-2, -3, -2] = true := by decide +kernel
theorem sub9_454 : sub9 [-2, -3, -1] = true := by decide +kernel
theorem sub9_455 : sub9 [-2, -3, 0] = true := by decide +kernel
theorem sub9_456 : sub9 [-2, -3, 1] = true := by decide +kernel
theorem sub9_457 : sub9 [-2, -3, 2] = true := by decide +kernel
theorem sub9_458 : sub9 [-2, -3, 3] = true := by decide +kernel
theorem sub9_459 : sub9 [-2, -3, 4] = true := by decide +kernel
theorem sub9_460 : sub9 [-2, -3, 5] = true := by decide +kernel
theorem sub9_461 : sub9 [-2, -3, 6] = true := by decide +kernel
theorem sub9_462 : sub9 [-2, -3, 7] = true := by decide +kernel
theorem sub9_463 : sub9 [-2, -2, -11] = true := by decide +kernel
theorem sub9_464 : sub9 [-2, -2, -10] = true := by decide +kernel
theorem sub9_465 : sub9 [-2, -2, -9] = true := by decide +kernel
theorem sub9_466 : sub9 [-2, -2, -8] = true := by decide +kernel
theorem sub9_467 : sub9 [-2, -2, -7] = true := by decide +kernel
theorem sub9_468 : sub9 [-2, -2, -6] = true := by decide +kernel
theorem sub9_469 : sub9 [-2, -2, -5] = true := by decide +kernel
theorem sub9_470 : sub9 [-2, -2, -4] = true := by decide +kernel
theorem sub9_471 : sub9 [-2, -2, -3] = true := by decide +kernel
theorem sub9_472 : sub9 [-2, -2, -2] = true := by decide +kernel
theorem sub9_473 : sub9 [-2, -2, -1] = true := by decide +kernel
theorem sub9_474 : sub9 [-2, -2, 0] = true := by decide +kernel
theorem sub9_475 : sub9 [-2, -2, 1] = true := by decide +kernel
theorem sub9_476 : sub9 [-2, -2, 2] = true := by decide +kernel
theorem sub9_477 : sub9 [-2, -2, 3] = true := by decide +kernel
theorem sub9_478 : sub9 [-2, -2, 4] = true := by decide +kernel
theorem sub9_479 : sub9 [-2, -2, 5] = true := by decide +kernel
theorem sb9_14 : ∀ q ∈ blk9_14, sub9 q = true := by
  unfold blk9_14
  exact List.forall_mem_cons.2 ⟨sub9_448, List.forall_mem_cons.2 ⟨sub9_449, List.forall_mem_cons.2 ⟨sub9_450, List.forall_mem_cons.2 ⟨sub9_451, List.forall_mem_cons.2 ⟨sub9_452, List.forall_mem_cons.2 ⟨sub9_453, List.forall_mem_cons.2 ⟨sub9_454, List.forall_mem_cons.2 ⟨sub9_455, List.forall_mem_cons.2 ⟨sub9_456, List.forall_mem_cons.2 ⟨sub9_457, List.forall_mem_cons.2 ⟨sub9_458, List.forall_mem_cons.2 ⟨sub9_459, List.forall_mem_cons.2 ⟨sub9_460, List.forall_mem_cons.2 ⟨sub9_461, List.forall_mem_cons.2 ⟨sub9_462, List.forall_mem_cons.2 ⟨sub9_463, List.forall_mem_cons.2 ⟨sub9_464, List.forall_mem_cons.2 ⟨sub9_465, List.forall_mem_cons.2 ⟨sub9_466, List.forall_mem_cons.2 ⟨sub9_467, List.forall_mem_cons.2 ⟨sub9_468, List.forall_mem_cons.2 ⟨sub9_469, List.forall_mem_cons.2 ⟨sub9_470, List.forall_mem_cons.2 ⟨sub9_471, List.forall_mem_cons.2 ⟨sub9_472, List.forall_mem_cons.2 ⟨sub9_473, List.forall_mem_cons.2 ⟨sub9_474, List.forall_mem_cons.2 ⟨sub9_475, List.forall_mem_cons.2 ⟨sub9_476, List.forall_mem_cons.2 ⟨sub9_477, List.forall_mem_cons.2 ⟨sub9_478, List.forall_mem_cons.2 ⟨sub9_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_480 : sub9 [-2, -2, 6] = true := by decide +kernel
theorem sub9_481 : sub9 [-2, -2, 7] = true := by decide +kernel
theorem sub9_482 : sub9 [-2, -2, 8] = true := by decide +kernel
theorem sub9_483 : sub9 [-2, -1, -11] = true := by decide +kernel
theorem sub9_484 : sub9 [-2, -1, -10] = true := by decide +kernel
theorem sub9_485 : sub9 [-2, -1, -9] = true := by decide +kernel
theorem sub9_486 : sub9 [-2, -1, -8] = true := by decide +kernel
theorem sub9_487 : sub9 [-2, -1, -7] = true := by decide +kernel
theorem sub9_488 : sub9 [-2, -1, -6] = true := by decide +kernel
theorem sub9_489 : sub9 [-2, -1, -5] = true := by decide +kernel
theorem sub9_490 : sub9 [-2, -1, -4] = true := by decide +kernel
theorem sub9_491 : sub9 [-2, -1, -3] = true := by decide +kernel
theorem sub9_492 : sub9 [-2, -1, -2] = true := by decide +kernel
theorem sub9_493 : sub9 [-2, -1, -1] = true := by decide +kernel
theorem sub9_494 : sub9 [-2, -1, 0] = true := by decide +kernel
theorem sub9_495 : sub9 [-2, -1, 1] = true := by decide +kernel
theorem sub9_496 : sub9 [-2, -1, 2] = true := by decide +kernel
theorem sub9_497 : sub9 [-2, -1, 3] = true := by decide +kernel
theorem sub9_498 : sub9 [-2, -1, 4] = true := by decide +kernel
theorem sub9_499 : sub9 [-2, -1, 5] = true := by decide +kernel
theorem sub9_500 : sub9 [-2, -1, 6] = true := by decide +kernel
theorem sub9_501 : sub9 [-2, -1, 7] = true := by decide +kernel
theorem sub9_502 : sub9 [-2, -1, 8] = true := by decide +kernel
theorem sub9_503 : sub9 [-2, 0, -11] = true := by decide +kernel
theorem sub9_504 : sub9 [-2, 0, -10] = true := by decide +kernel
theorem sub9_505 : sub9 [-2, 0, -9] = true := by decide +kernel
theorem sub9_506 : sub9 [-2, 0, -8] = true := by decide +kernel
theorem sub9_507 : sub9 [-2, 0, -7] = true := by decide +kernel
theorem sub9_508 : sub9 [-2, 0, -6] = true := by decide +kernel
theorem sub9_509 : sub9 [-2, 0, -5] = true := by decide +kernel
theorem sub9_510 : sub9 [-2, 0, -4] = true := by decide +kernel
theorem sub9_511 : sub9 [-2, 0, -3] = true := by decide +kernel
theorem sb9_15 : ∀ q ∈ blk9_15, sub9 q = true := by
  unfold blk9_15
  exact List.forall_mem_cons.2 ⟨sub9_480, List.forall_mem_cons.2 ⟨sub9_481, List.forall_mem_cons.2 ⟨sub9_482, List.forall_mem_cons.2 ⟨sub9_483, List.forall_mem_cons.2 ⟨sub9_484, List.forall_mem_cons.2 ⟨sub9_485, List.forall_mem_cons.2 ⟨sub9_486, List.forall_mem_cons.2 ⟨sub9_487, List.forall_mem_cons.2 ⟨sub9_488, List.forall_mem_cons.2 ⟨sub9_489, List.forall_mem_cons.2 ⟨sub9_490, List.forall_mem_cons.2 ⟨sub9_491, List.forall_mem_cons.2 ⟨sub9_492, List.forall_mem_cons.2 ⟨sub9_493, List.forall_mem_cons.2 ⟨sub9_494, List.forall_mem_cons.2 ⟨sub9_495, List.forall_mem_cons.2 ⟨sub9_496, List.forall_mem_cons.2 ⟨sub9_497, List.forall_mem_cons.2 ⟨sub9_498, List.forall_mem_cons.2 ⟨sub9_499, List.forall_mem_cons.2 ⟨sub9_500, List.forall_mem_cons.2 ⟨sub9_501, List.forall_mem_cons.2 ⟨sub9_502, List.forall_mem_cons.2 ⟨sub9_503, List.forall_mem_cons.2 ⟨sub9_504, List.forall_mem_cons.2 ⟨sub9_505, List.forall_mem_cons.2 ⟨sub9_506, List.forall_mem_cons.2 ⟨sub9_507, List.forall_mem_cons.2 ⟨sub9_508, List.forall_mem_cons.2 ⟨sub9_509, List.forall_mem_cons.2 ⟨sub9_510, List.forall_mem_cons.2 ⟨sub9_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_512 : sub9 [-2, 0, -2] = true := by decide +kernel
theorem sub9_513 : sub9 [-2, 0, -1] = true := by decide +kernel
theorem sub9_514 : sub9 [-2, 0, 0] = true := by decide +kernel
theorem sub9_515 : sub9 [-2, 0, 1] = true := by decide +kernel
theorem sub9_516 : sub9 [-2, 0, 2] = true := by decide +kernel
theorem sub9_517 : sub9 [-2, 0, 3] = true := by decide +kernel
theorem sub9_518 : sub9 [-2, 0, 4] = true := by decide +kernel
theorem sub9_519 : sub9 [-2, 0, 5] = true := by decide +kernel
theorem sub9_520 : sub9 [-2, 0, 6] = true := by decide +kernel
theorem sub9_521 : sub9 [-2, 0, 7] = true := by decide +kernel
theorem sub9_522 : sub9 [-2, 0, 8] = true := by decide +kernel
theorem sub9_523 : sub9 [-2, 0, 9] = true := by decide +kernel
theorem sub9_524 : sub9 [-2, 1, -10] = true := by decide +kernel
theorem sub9_525 : sub9 [-2, 1, -9] = true := by decide +kernel
theorem sub9_526 : sub9 [-2, 1, -8] = true := by decide +kernel
theorem sub9_527 : sub9 [-2, 1, -7] = true := by decide +kernel
theorem sub9_528 : sub9 [-2, 1, -6] = true := by decide +kernel
theorem sub9_529 : sub9 [-2, 1, -5] = true := by decide +kernel
theorem sub9_530 : sub9 [-2, 1, -4] = true := by decide +kernel
theorem sub9_531 : sub9 [-2, 1, -3] = true := by decide +kernel
theorem sub9_532 : sub9 [-2, 1, -2] = true := by decide +kernel
theorem sub9_533 : sub9 [-2, 1, -1] = true := by decide +kernel
theorem sub9_534 : sub9 [-2, 1, 0] = true := by decide +kernel
theorem sub9_535 : sub9 [-2, 1, 1] = true := by decide +kernel
theorem sub9_536 : sub9 [-2, 1, 2] = true := by decide +kernel
theorem sub9_537 : sub9 [-2, 1, 3] = true := by decide +kernel
theorem sub9_538 : sub9 [-2, 1, 4] = true := by decide +kernel
theorem sub9_539 : sub9 [-2, 1, 5] = true := by decide +kernel
theorem sub9_540 : sub9 [-2, 1, 6] = true := by decide +kernel
theorem sub9_541 : sub9 [-2, 1, 7] = true := by decide +kernel
theorem sub9_542 : sub9 [-2, 1, 8] = true := by decide +kernel
theorem sub9_543 : sub9 [-2, 1, 9] = true := by decide +kernel
theorem sb9_16 : ∀ q ∈ blk9_16, sub9 q = true := by
  unfold blk9_16
  exact List.forall_mem_cons.2 ⟨sub9_512, List.forall_mem_cons.2 ⟨sub9_513, List.forall_mem_cons.2 ⟨sub9_514, List.forall_mem_cons.2 ⟨sub9_515, List.forall_mem_cons.2 ⟨sub9_516, List.forall_mem_cons.2 ⟨sub9_517, List.forall_mem_cons.2 ⟨sub9_518, List.forall_mem_cons.2 ⟨sub9_519, List.forall_mem_cons.2 ⟨sub9_520, List.forall_mem_cons.2 ⟨sub9_521, List.forall_mem_cons.2 ⟨sub9_522, List.forall_mem_cons.2 ⟨sub9_523, List.forall_mem_cons.2 ⟨sub9_524, List.forall_mem_cons.2 ⟨sub9_525, List.forall_mem_cons.2 ⟨sub9_526, List.forall_mem_cons.2 ⟨sub9_527, List.forall_mem_cons.2 ⟨sub9_528, List.forall_mem_cons.2 ⟨sub9_529, List.forall_mem_cons.2 ⟨sub9_530, List.forall_mem_cons.2 ⟨sub9_531, List.forall_mem_cons.2 ⟨sub9_532, List.forall_mem_cons.2 ⟨sub9_533, List.forall_mem_cons.2 ⟨sub9_534, List.forall_mem_cons.2 ⟨sub9_535, List.forall_mem_cons.2 ⟨sub9_536, List.forall_mem_cons.2 ⟨sub9_537, List.forall_mem_cons.2 ⟨sub9_538, List.forall_mem_cons.2 ⟨sub9_539, List.forall_mem_cons.2 ⟨sub9_540, List.forall_mem_cons.2 ⟨sub9_541, List.forall_mem_cons.2 ⟨sub9_542, List.forall_mem_cons.2 ⟨sub9_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
