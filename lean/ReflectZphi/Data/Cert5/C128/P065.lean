import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_32 : subd9_3 [-3, 2] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [-3, 3] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [-3, 4] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [-3, 5] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [-2, -8] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [-2, -7] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [-2, -6] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [-2, -5] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [-2, -4] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [-2, 3] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [-2, 4] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [-2, 5] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [-2, 6] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [-1, -8] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [-1, -7] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [-1, -6] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [-1, -5] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [-1, 0, -7] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [-1, 0, -6] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [-1, 0, -5] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [-1, 0, -4] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [-1, 0, -3] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_64 : subd9_3 [-1, 0, -2] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [-1, 0, -1] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [-1, 0, 0] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [-1, 0, 1] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [-1, 0, 2] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [-1, 0, 3] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [-1, 0, 4] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [-1, 0, 5] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [-1, 0, 6] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [-1, 1, -7] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [-1, 1, -6] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [-1, 1, -5] = true := by decide +kernel
theorem subd9_3_76 : subd9_3 [-1, 1, -4] = true := by decide +kernel
theorem subd9_3_77 : subd9_3 [-1, 1, -3] = true := by decide +kernel
theorem subd9_3_78 : subd9_3 [-1, 1, -2] = true := by decide +kernel
theorem subd9_3_79 : subd9_3 [-1, 1, -1] = true := by decide +kernel
theorem subd9_3_80 : subd9_3 [-1, 1, 0] = true := by decide +kernel
theorem subd9_3_81 : subd9_3 [-1, 1, 1] = true := by decide +kernel
theorem subd9_3_82 : subd9_3 [-1, 1, 2] = true := by decide +kernel
theorem subd9_3_83 : subd9_3 [-1, 1, 3] = true := by decide +kernel
theorem subd9_3_84 : subd9_3 [-1, 1, 4] = true := by decide +kernel
theorem subd9_3_85 : subd9_3 [-1, 1, 5] = true := by decide +kernel
theorem subd9_3_86 : subd9_3 [-1, 1, 6] = true := by decide +kernel
theorem subd9_3_87 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_88 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_89 : subd9_3 [-1, 4] = true := by decide +kernel
theorem subd9_3_90 : subd9_3 [-1, 5] = true := by decide +kernel
theorem subd9_3_91 : subd9_3 [-1, 6] = true := by decide +kernel
theorem subd9_3_92 : subd9_3 [-1, 7] = true := by decide +kernel
theorem subd9_3_93 : subd9_3 [0, -8] = true := by decide +kernel
theorem subd9_3_94 : subd9_3 [0, -7] = true := by decide +kernel
theorem subd9_3_95 : subd9_3 [0, -6] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_cons.2 ⟨subd9_3_76, List.forall_mem_cons.2 ⟨subd9_3_77, List.forall_mem_cons.2 ⟨subd9_3_78, List.forall_mem_cons.2 ⟨subd9_3_79, List.forall_mem_cons.2 ⟨subd9_3_80, List.forall_mem_cons.2 ⟨subd9_3_81, List.forall_mem_cons.2 ⟨subd9_3_82, List.forall_mem_cons.2 ⟨subd9_3_83, List.forall_mem_cons.2 ⟨subd9_3_84, List.forall_mem_cons.2 ⟨subd9_3_85, List.forall_mem_cons.2 ⟨subd9_3_86, List.forall_mem_cons.2 ⟨subd9_3_87, List.forall_mem_cons.2 ⟨subd9_3_88, List.forall_mem_cons.2 ⟨subd9_3_89, List.forall_mem_cons.2 ⟨subd9_3_90, List.forall_mem_cons.2 ⟨subd9_3_91, List.forall_mem_cons.2 ⟨subd9_3_92, List.forall_mem_cons.2 ⟨subd9_3_93, List.forall_mem_cons.2 ⟨subd9_3_94, List.forall_mem_cons.2 ⟨subd9_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_96 : subd9_3 [0, -5] = true := by decide +kernel
theorem subd9_3_97 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_98 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_99 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_100 : subd9_3 [0, -1, -7] = true := by decide +kernel
theorem subd9_3_101 : subd9_3 [0, -1, -6] = true := by decide +kernel
theorem subd9_3_102 : subd9_3 [0, -1, -5] = true := by decide +kernel
theorem subd9_3_103 : subd9_3 [0, -1, -4] = true := by decide +kernel
theorem subd9_3_104 : subd9_3 [0, -1, -3] = true := by decide +kernel
theorem subd9_3_105 : subd9_3 [0, -1, -2] = true := by decide +kernel
theorem subd9_3_106 : subd9_3 [0, -1, -1] = true := by decide +kernel
theorem subd9_3_107 : subd9_3 [0, -1, 0] = true := by decide +kernel
theorem subd9_3_108 : subd9_3 [0, -1, 1] = true := by decide +kernel
theorem subd9_3_109 : subd9_3 [0, -1, 2] = true := by decide +kernel
theorem subd9_3_110 : subd9_3 [0, -1, 3] = true := by decide +kernel
theorem subd9_3_111 : subd9_3 [0, -1, 4] = true := by decide +kernel
theorem subd9_3_112 : subd9_3 [0, -1, 5] = true := by decide +kernel
theorem subd9_3_113 : subd9_3 [0, -1, 6] = true := by decide +kernel
theorem subd9_3_114 : subd9_3 [0, 0, -7] = true := by decide +kernel
theorem subd9_3_115 : subd9_3 [0, 0, -6] = true := by decide +kernel
theorem subd9_3_116 : subd9_3 [0, 0, -5] = true := by decide +kernel
theorem subd9_3_117 : subd9_3 [0, 0, -4] = true := by decide +kernel
theorem subd9_3_118 : subd9_3 [0, 0, -3] = true := by decide +kernel
theorem subd9_3_119 : subd9_3 [0, 0, -2] = true := by decide +kernel
theorem subd9_3_120 : subd9_3 [0, 0, -1] = true := by decide +kernel
theorem subd9_3_121 : subd9_3 [0, 0, 0] = true := by decide +kernel
theorem subd9_3_122 : subd9_3 [0, 0, 1] = true := by decide +kernel
theorem subd9_3_123 : subd9_3 [0, 0, 2] = true := by decide +kernel
theorem subd9_3_124 : subd9_3 [0, 0, 3] = true := by decide +kernel
theorem subd9_3_125 : subd9_3 [0, 0, 4] = true := by decide +kernel
theorem subd9_3_126 : subd9_3 [0, 0, 5] = true := by decide +kernel
theorem subd9_3_127 : subd9_3 [0, 0, 6] = true := by decide +kernel
theorem sbd9_3_3 : ∀ q ∈ blkd9_3_3, subd9_3 q = true := by
  unfold blkd9_3_3
  exact List.forall_mem_cons.2 ⟨subd9_3_96, List.forall_mem_cons.2 ⟨subd9_3_97, List.forall_mem_cons.2 ⟨subd9_3_98, List.forall_mem_cons.2 ⟨subd9_3_99, List.forall_mem_cons.2 ⟨subd9_3_100, List.forall_mem_cons.2 ⟨subd9_3_101, List.forall_mem_cons.2 ⟨subd9_3_102, List.forall_mem_cons.2 ⟨subd9_3_103, List.forall_mem_cons.2 ⟨subd9_3_104, List.forall_mem_cons.2 ⟨subd9_3_105, List.forall_mem_cons.2 ⟨subd9_3_106, List.forall_mem_cons.2 ⟨subd9_3_107, List.forall_mem_cons.2 ⟨subd9_3_108, List.forall_mem_cons.2 ⟨subd9_3_109, List.forall_mem_cons.2 ⟨subd9_3_110, List.forall_mem_cons.2 ⟨subd9_3_111, List.forall_mem_cons.2 ⟨subd9_3_112, List.forall_mem_cons.2 ⟨subd9_3_113, List.forall_mem_cons.2 ⟨subd9_3_114, List.forall_mem_cons.2 ⟨subd9_3_115, List.forall_mem_cons.2 ⟨subd9_3_116, List.forall_mem_cons.2 ⟨subd9_3_117, List.forall_mem_cons.2 ⟨subd9_3_118, List.forall_mem_cons.2 ⟨subd9_3_119, List.forall_mem_cons.2 ⟨subd9_3_120, List.forall_mem_cons.2 ⟨subd9_3_121, List.forall_mem_cons.2 ⟨subd9_3_122, List.forall_mem_cons.2 ⟨subd9_3_123, List.forall_mem_cons.2 ⟨subd9_3_124, List.forall_mem_cons.2 ⟨subd9_3_125, List.forall_mem_cons.2 ⟨subd9_3_126, List.forall_mem_cons.2 ⟨subd9_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_128 : subd9_3 [0, 1, -7] = true := by decide +kernel
theorem subd9_3_129 : subd9_3 [0, 1, -6] = true := by decide +kernel
theorem subd9_3_130 : subd9_3 [0, 1, -5] = true := by decide +kernel
theorem subd9_3_131 : subd9_3 [0, 1, -4] = true := by decide +kernel
theorem subd9_3_132 : subd9_3 [0, 1, -3] = true := by decide +kernel
theorem subd9_3_133 : subd9_3 [0, 1, -2] = true := by decide +kernel
theorem subd9_3_134 : subd9_3 [0, 1, -1] = true := by decide +kernel
theorem subd9_3_135 : subd9_3 [0, 1, 0] = true := by decide +kernel
theorem subd9_3_136 : subd9_3 [0, 1, 1] = true := by decide +kernel
theorem subd9_3_137 : subd9_3 [0, 1, 2] = true := by decide +kernel
theorem subd9_3_138 : subd9_3 [0, 1, 3] = true := by decide +kernel
theorem subd9_3_139 : subd9_3 [0, 1, 4] = true := by decide +kernel
theorem subd9_3_140 : subd9_3 [0, 1, 5] = true := by decide +kernel
theorem subd9_3_141 : subd9_3 [0, 1, 6] = true := by decide +kernel
theorem subd9_3_142 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_143 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_144 : subd9_3 [0, 4] = true := by decide +kernel
theorem subd9_3_145 : subd9_3 [0, 5] = true := by decide +kernel
theorem subd9_3_146 : subd9_3 [0, 6] = true := by decide +kernel
theorem subd9_3_147 : subd9_3 [0, 7] = true := by decide +kernel
theorem subd9_3_148 : subd9_3 [1, -8] = true := by decide +kernel
theorem subd9_3_149 : subd9_3 [1, -7] = true := by decide +kernel
theorem subd9_3_150 : subd9_3 [1, -6] = true := by decide +kernel
theorem subd9_3_151 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_152 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_153 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_154 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_155 : subd9_3 [1, -1, -7] = true := by decide +kernel
theorem subd9_3_156 : subd9_3 [1, -1, -6] = true := by decide +kernel
theorem subd9_3_157 : subd9_3 [1, -1, -5] = true := by decide +kernel
theorem subd9_3_158 : subd9_3 [1, -1, -4] = true := by decide +kernel
theorem subd9_3_159 : subd9_3 [1, -1, -3] = true := by decide +kernel
theorem sbd9_3_4 : ∀ q ∈ blkd9_3_4, subd9_3 q = true := by
  unfold blkd9_3_4
  exact List.forall_mem_cons.2 ⟨subd9_3_128, List.forall_mem_cons.2 ⟨subd9_3_129, List.forall_mem_cons.2 ⟨subd9_3_130, List.forall_mem_cons.2 ⟨subd9_3_131, List.forall_mem_cons.2 ⟨subd9_3_132, List.forall_mem_cons.2 ⟨subd9_3_133, List.forall_mem_cons.2 ⟨subd9_3_134, List.forall_mem_cons.2 ⟨subd9_3_135, List.forall_mem_cons.2 ⟨subd9_3_136, List.forall_mem_cons.2 ⟨subd9_3_137, List.forall_mem_cons.2 ⟨subd9_3_138, List.forall_mem_cons.2 ⟨subd9_3_139, List.forall_mem_cons.2 ⟨subd9_3_140, List.forall_mem_cons.2 ⟨subd9_3_141, List.forall_mem_cons.2 ⟨subd9_3_142, List.forall_mem_cons.2 ⟨subd9_3_143, List.forall_mem_cons.2 ⟨subd9_3_144, List.forall_mem_cons.2 ⟨subd9_3_145, List.forall_mem_cons.2 ⟨subd9_3_146, List.forall_mem_cons.2 ⟨subd9_3_147, List.forall_mem_cons.2 ⟨subd9_3_148, List.forall_mem_cons.2 ⟨subd9_3_149, List.forall_mem_cons.2 ⟨subd9_3_150, List.forall_mem_cons.2 ⟨subd9_3_151, List.forall_mem_cons.2 ⟨subd9_3_152, List.forall_mem_cons.2 ⟨subd9_3_153, List.forall_mem_cons.2 ⟨subd9_3_154, List.forall_mem_cons.2 ⟨subd9_3_155, List.forall_mem_cons.2 ⟨subd9_3_156, List.forall_mem_cons.2 ⟨subd9_3_157, List.forall_mem_cons.2 ⟨subd9_3_158, List.forall_mem_cons.2 ⟨subd9_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_160 : subd9_3 [1, -1, -2] = true := by decide +kernel
theorem subd9_3_161 : subd9_3 [1, -1, -1] = true := by decide +kernel
theorem subd9_3_162 : subd9_3 [1, -1, 0] = true := by decide +kernel
theorem subd9_3_163 : subd9_3 [1, -1, 1] = true := by decide +kernel
theorem subd9_3_164 : subd9_3 [1, -1, 2] = true := by decide +kernel
theorem subd9_3_165 : subd9_3 [1, -1, 3] = true := by decide +kernel
theorem subd9_3_166 : subd9_3 [1, -1, 4] = true := by decide +kernel
theorem subd9_3_167 : subd9_3 [1, -1, 5] = true := by decide +kernel
theorem subd9_3_168 : subd9_3 [1, -1, 6] = true := by decide +kernel
theorem subd9_3_169 : subd9_3 [1, 0, -7] = true := by decide +kernel
theorem subd9_3_170 : subd9_3 [1, 0, -6] = true := by decide +kernel
theorem subd9_3_171 : subd9_3 [1, 0, -5] = true := by decide +kernel
theorem subd9_3_172 : subd9_3 [1, 0, -4] = true := by decide +kernel
theorem subd9_3_173 : subd9_3 [1, 0, -3] = true := by decide +kernel
theorem subd9_3_174 : subd9_3 [1, 0, -2] = true := by decide +kernel
theorem subd9_3_175 : subd9_3 [1, 0, -1] = true := by decide +kernel
theorem subd9_3_176 : subd9_3 [1, 0, 0] = true := by decide +kernel
theorem subd9_3_177 : subd9_3 [1, 0, 1] = true := by decide +kernel
theorem subd9_3_178 : subd9_3 [1, 0, 2] = true := by decide +kernel
theorem subd9_3_179 : subd9_3 [1, 0, 3] = true := by decide +kernel
theorem subd9_3_180 : subd9_3 [1, 0, 4] = true := by decide +kernel
theorem subd9_3_181 : subd9_3 [1, 0, 5] = true := by decide +kernel
theorem subd9_3_182 : subd9_3 [1, 0, 6] = true := by decide +kernel
theorem subd9_3_183 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_184 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_185 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_186 : subd9_3 [1, 4] = true := by decide +kernel
theorem subd9_3_187 : subd9_3 [1, 5] = true := by decide +kernel
theorem subd9_3_188 : subd9_3 [1, 6] = true := by decide +kernel
theorem subd9_3_189 : subd9_3 [1, 7] = true := by decide +kernel
theorem subd9_3_190 : subd9_3 [2, -7] = true := by decide +kernel
theorem subd9_3_191 : subd9_3 [2, -6] = true := by decide +kernel
theorem sbd9_3_5 : ∀ q ∈ blkd9_3_5, subd9_3 q = true := by
  unfold blkd9_3_5
  exact List.forall_mem_cons.2 ⟨subd9_3_160, List.forall_mem_cons.2 ⟨subd9_3_161, List.forall_mem_cons.2 ⟨subd9_3_162, List.forall_mem_cons.2 ⟨subd9_3_163, List.forall_mem_cons.2 ⟨subd9_3_164, List.forall_mem_cons.2 ⟨subd9_3_165, List.forall_mem_cons.2 ⟨subd9_3_166, List.forall_mem_cons.2 ⟨subd9_3_167, List.forall_mem_cons.2 ⟨subd9_3_168, List.forall_mem_cons.2 ⟨subd9_3_169, List.forall_mem_cons.2 ⟨subd9_3_170, List.forall_mem_cons.2 ⟨subd9_3_171, List.forall_mem_cons.2 ⟨subd9_3_172, List.forall_mem_cons.2 ⟨subd9_3_173, List.forall_mem_cons.2 ⟨subd9_3_174, List.forall_mem_cons.2 ⟨subd9_3_175, List.forall_mem_cons.2 ⟨subd9_3_176, List.forall_mem_cons.2 ⟨subd9_3_177, List.forall_mem_cons.2 ⟨subd9_3_178, List.forall_mem_cons.2 ⟨subd9_3_179, List.forall_mem_cons.2 ⟨subd9_3_180, List.forall_mem_cons.2 ⟨subd9_3_181, List.forall_mem_cons.2 ⟨subd9_3_182, List.forall_mem_cons.2 ⟨subd9_3_183, List.forall_mem_cons.2 ⟨subd9_3_184, List.forall_mem_cons.2 ⟨subd9_3_185, List.forall_mem_cons.2 ⟨subd9_3_186, List.forall_mem_cons.2 ⟨subd9_3_187, List.forall_mem_cons.2 ⟨subd9_3_188, List.forall_mem_cons.2 ⟨subd9_3_189, List.forall_mem_cons.2 ⟨subd9_3_190, List.forall_mem_cons.2 ⟨subd9_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
