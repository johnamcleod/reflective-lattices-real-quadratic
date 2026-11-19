import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_32 : subd8_1 [-9, 2, -1] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [-9, 2, 0] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [-9, 2, 1] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [-9, 2, 2] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [-9, 2, 3] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [-9, 2, 4] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [-9, 2, 5] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [-9, 2, 6] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [-9, 2, 7] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [-9, 3] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [-9, 4] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [-9, 5] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [-9, 6] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [-9, 7] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [-9, 8] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [-8, -6] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [-8, -5] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [-8, -4] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [-8, -3] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [-8, -2, -7] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [-8, -2, -6] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [-8, -2, -5] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [-8, -2, -4] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [-8, -2, -3] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [-8, -2, -2] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [-8, -2, -1] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [-8, -2, 0] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [-8, -2, 1] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [-8, -2, 2] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [-8, -2, 3] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [-8, -2, 4] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [-8, -2, 5] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [-8, -2, 6] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [-8, -1, -8] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [-8, -1, -7] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [-8, -1, -6] = true := by decide +kernel
theorem subd8_1_68 : subd8_1 [-8, -1, -5] = true := by decide +kernel
theorem subd8_1_69 : subd8_1 [-8, -1, -4] = true := by decide +kernel
theorem subd8_1_70 : subd8_1 [-8, -1, -3] = true := by decide +kernel
theorem subd8_1_71 : subd8_1 [-8, -1, -2] = true := by decide +kernel
theorem subd8_1_72 : subd8_1 [-8, -1, -1] = true := by decide +kernel
theorem subd8_1_73 : subd8_1 [-8, -1, 0] = true := by decide +kernel
theorem subd8_1_74 : subd8_1 [-8, -1, 1] = true := by decide +kernel
theorem subd8_1_75 : subd8_1 [-8, -1, 2] = true := by decide +kernel
theorem subd8_1_76 : subd8_1 [-8, -1, 3] = true := by decide +kernel
theorem subd8_1_77 : subd8_1 [-8, -1, 4] = true := by decide +kernel
theorem subd8_1_78 : subd8_1 [-8, -1, 5] = true := by decide +kernel
theorem subd8_1_79 : subd8_1 [-8, -1, 6] = true := by decide +kernel
theorem subd8_1_80 : subd8_1 [-8, -1, 7] = true := by decide +kernel
theorem subd8_1_81 : subd8_1 [-8, 0, -8] = true := by decide +kernel
theorem subd8_1_82 : subd8_1 [-8, 0, -7] = true := by decide +kernel
theorem subd8_1_83 : subd8_1 [-8, 0, -6] = true := by decide +kernel
theorem subd8_1_84 : subd8_1 [-8, 0, -5] = true := by decide +kernel
theorem subd8_1_85 : subd8_1 [-8, 0, -4] = true := by decide +kernel
theorem subd8_1_86 : subd8_1 [-8, 0, -3] = true := by decide +kernel
theorem subd8_1_87 : subd8_1 [-8, 0, -2] = true := by decide +kernel
theorem subd8_1_88 : subd8_1 [-8, 0, -1] = true := by decide +kernel
theorem subd8_1_89 : subd8_1 [-8, 0, 0] = true := by decide +kernel
theorem subd8_1_90 : subd8_1 [-8, 0, 1] = true := by decide +kernel
theorem subd8_1_91 : subd8_1 [-8, 0, 2] = true := by decide +kernel
theorem subd8_1_92 : subd8_1 [-8, 0, 3] = true := by decide +kernel
theorem subd8_1_93 : subd8_1 [-8, 0, 4] = true := by decide +kernel
theorem subd8_1_94 : subd8_1 [-8, 0, 5] = true := by decide +kernel
theorem subd8_1_95 : subd8_1 [-8, 0, 6] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_cons.2 ⟨subd8_1_68, List.forall_mem_cons.2 ⟨subd8_1_69, List.forall_mem_cons.2 ⟨subd8_1_70, List.forall_mem_cons.2 ⟨subd8_1_71, List.forall_mem_cons.2 ⟨subd8_1_72, List.forall_mem_cons.2 ⟨subd8_1_73, List.forall_mem_cons.2 ⟨subd8_1_74, List.forall_mem_cons.2 ⟨subd8_1_75, List.forall_mem_cons.2 ⟨subd8_1_76, List.forall_mem_cons.2 ⟨subd8_1_77, List.forall_mem_cons.2 ⟨subd8_1_78, List.forall_mem_cons.2 ⟨subd8_1_79, List.forall_mem_cons.2 ⟨subd8_1_80, List.forall_mem_cons.2 ⟨subd8_1_81, List.forall_mem_cons.2 ⟨subd8_1_82, List.forall_mem_cons.2 ⟨subd8_1_83, List.forall_mem_cons.2 ⟨subd8_1_84, List.forall_mem_cons.2 ⟨subd8_1_85, List.forall_mem_cons.2 ⟨subd8_1_86, List.forall_mem_cons.2 ⟨subd8_1_87, List.forall_mem_cons.2 ⟨subd8_1_88, List.forall_mem_cons.2 ⟨subd8_1_89, List.forall_mem_cons.2 ⟨subd8_1_90, List.forall_mem_cons.2 ⟨subd8_1_91, List.forall_mem_cons.2 ⟨subd8_1_92, List.forall_mem_cons.2 ⟨subd8_1_93, List.forall_mem_cons.2 ⟨subd8_1_94, List.forall_mem_cons.2 ⟨subd8_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_96 : subd8_1 [-8, 0, 7] = true := by decide +kernel
theorem subd8_1_97 : subd8_1 [-8, 1, -7] = true := by decide +kernel
theorem subd8_1_98 : subd8_1 [-8, 1, -6] = true := by decide +kernel
theorem subd8_1_99 : subd8_1 [-8, 1, -5] = true := by decide +kernel
theorem subd8_1_100 : subd8_1 [-8, 1, -4] = true := by decide +kernel
theorem subd8_1_101 : subd8_1 [-8, 1, -3] = true := by decide +kernel
theorem subd8_1_102 : subd8_1 [-8, 1, -2] = true := by decide +kernel
theorem subd8_1_103 : subd8_1 [-8, 1, -1] = true := by decide +kernel
theorem subd8_1_104 : subd8_1 [-8, 1, 0] = true := by decide +kernel
theorem subd8_1_105 : subd8_1 [-8, 1, 1] = true := by decide +kernel
theorem subd8_1_106 : subd8_1 [-8, 1, 2] = true := by decide +kernel
theorem subd8_1_107 : subd8_1 [-8, 1, 3] = true := by decide +kernel
theorem subd8_1_108 : subd8_1 [-8, 1, 4] = true := by decide +kernel
theorem subd8_1_109 : subd8_1 [-8, 1, 5] = true := by decide +kernel
theorem subd8_1_110 : subd8_1 [-8, 1, 6] = true := by decide +kernel
theorem subd8_1_111 : subd8_1 [-8, 1, 7] = true := by decide +kernel
theorem subd8_1_112 : subd8_1 [-8, 1, 8] = true := by decide +kernel
theorem subd8_1_113 : subd8_1 [-8, 2, -7] = true := by decide +kernel
theorem subd8_1_114 : subd8_1 [-8, 2, -6] = true := by decide +kernel
theorem subd8_1_115 : subd8_1 [-8, 2, -5] = true := by decide +kernel
theorem subd8_1_116 : subd8_1 [-8, 2, -4] = true := by decide +kernel
theorem subd8_1_117 : subd8_1 [-8, 2, -3] = true := by decide +kernel
theorem subd8_1_118 : subd8_1 [-8, 2, -2] = true := by decide +kernel
theorem subd8_1_119 : subd8_1 [-8, 2, -1] = true := by decide +kernel
theorem subd8_1_120 : subd8_1 [-8, 2, 0] = true := by decide +kernel
theorem subd8_1_121 : subd8_1 [-8, 2, 1] = true := by decide +kernel
theorem subd8_1_122 : subd8_1 [-8, 2, 2] = true := by decide +kernel
theorem subd8_1_123 : subd8_1 [-8, 2, 3] = true := by decide +kernel
theorem subd8_1_124 : subd8_1 [-8, 2, 4] = true := by decide +kernel
theorem subd8_1_125 : subd8_1 [-8, 2, 5] = true := by decide +kernel
theorem subd8_1_126 : subd8_1 [-8, 2, 6] = true := by decide +kernel
theorem subd8_1_127 : subd8_1 [-8, 2, 7] = true := by decide +kernel
theorem sbd8_1_3 : ∀ q ∈ blkd8_1_3, subd8_1 q = true := by
  unfold blkd8_1_3
  exact List.forall_mem_cons.2 ⟨subd8_1_96, List.forall_mem_cons.2 ⟨subd8_1_97, List.forall_mem_cons.2 ⟨subd8_1_98, List.forall_mem_cons.2 ⟨subd8_1_99, List.forall_mem_cons.2 ⟨subd8_1_100, List.forall_mem_cons.2 ⟨subd8_1_101, List.forall_mem_cons.2 ⟨subd8_1_102, List.forall_mem_cons.2 ⟨subd8_1_103, List.forall_mem_cons.2 ⟨subd8_1_104, List.forall_mem_cons.2 ⟨subd8_1_105, List.forall_mem_cons.2 ⟨subd8_1_106, List.forall_mem_cons.2 ⟨subd8_1_107, List.forall_mem_cons.2 ⟨subd8_1_108, List.forall_mem_cons.2 ⟨subd8_1_109, List.forall_mem_cons.2 ⟨subd8_1_110, List.forall_mem_cons.2 ⟨subd8_1_111, List.forall_mem_cons.2 ⟨subd8_1_112, List.forall_mem_cons.2 ⟨subd8_1_113, List.forall_mem_cons.2 ⟨subd8_1_114, List.forall_mem_cons.2 ⟨subd8_1_115, List.forall_mem_cons.2 ⟨subd8_1_116, List.forall_mem_cons.2 ⟨subd8_1_117, List.forall_mem_cons.2 ⟨subd8_1_118, List.forall_mem_cons.2 ⟨subd8_1_119, List.forall_mem_cons.2 ⟨subd8_1_120, List.forall_mem_cons.2 ⟨subd8_1_121, List.forall_mem_cons.2 ⟨subd8_1_122, List.forall_mem_cons.2 ⟨subd8_1_123, List.forall_mem_cons.2 ⟨subd8_1_124, List.forall_mem_cons.2 ⟨subd8_1_125, List.forall_mem_cons.2 ⟨subd8_1_126, List.forall_mem_cons.2 ⟨subd8_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_128 : subd8_1 [-8, 2, 8] = true := by decide +kernel
theorem subd8_1_129 : subd8_1 [-8, 3, -7] = true := by decide +kernel
theorem subd8_1_130 : subd8_1 [-8, 3, -6] = true := by decide +kernel
theorem subd8_1_131 : subd8_1 [-8, 3, -5] = true := by decide +kernel
theorem subd8_1_132 : subd8_1 [-8, 3, -4] = true := by decide +kernel
theorem subd8_1_133 : subd8_1 [-8, 3, -3] = true := by decide +kernel
theorem subd8_1_134 : subd8_1 [-8, 3, -2] = true := by decide +kernel
theorem subd8_1_135 : subd8_1 [-8, 3, -1] = true := by decide +kernel
theorem subd8_1_136 : subd8_1 [-8, 3, 0] = true := by decide +kernel
theorem subd8_1_137 : subd8_1 [-8, 3, 1] = true := by decide +kernel
theorem subd8_1_138 : subd8_1 [-8, 3, 2] = true := by decide +kernel
theorem subd8_1_139 : subd8_1 [-8, 3, 3] = true := by decide +kernel
theorem subd8_1_140 : subd8_1 [-8, 3, 4] = true := by decide +kernel
theorem subd8_1_141 : subd8_1 [-8, 3, 5] = true := by decide +kernel
theorem subd8_1_142 : subd8_1 [-8, 3, 6] = true := by decide +kernel
theorem subd8_1_143 : subd8_1 [-8, 3, 7] = true := by decide +kernel
theorem subd8_1_144 : subd8_1 [-8, 3, 8] = true := by decide +kernel
theorem subd8_1_145 : subd8_1 [-8, 4, -6] = true := by decide +kernel
theorem subd8_1_146 : subd8_1 [-8, 4, -5] = true := by decide +kernel
theorem subd8_1_147 : subd8_1 [-8, 4, -4] = true := by decide +kernel
theorem subd8_1_148 : subd8_1 [-8, 4, -3] = true := by decide +kernel
theorem subd8_1_149 : subd8_1 [-8, 4, -2] = true := by decide +kernel
theorem subd8_1_150 : subd8_1 [-8, 4, -1] = true := by decide +kernel
theorem subd8_1_151 : subd8_1 [-8, 4, 0] = true := by decide +kernel
theorem subd8_1_152 : subd8_1 [-8, 4, 1] = true := by decide +kernel
theorem subd8_1_153 : subd8_1 [-8, 4, 2] = true := by decide +kernel
theorem subd8_1_154 : subd8_1 [-8, 4, 3] = true := by decide +kernel
theorem subd8_1_155 : subd8_1 [-8, 4, 4] = true := by decide +kernel
theorem subd8_1_156 : subd8_1 [-8, 4, 5] = true := by decide +kernel
theorem subd8_1_157 : subd8_1 [-8, 4, 6] = true := by decide +kernel
theorem subd8_1_158 : subd8_1 [-8, 4, 7] = true := by decide +kernel
theorem subd8_1_159 : subd8_1 [-8, 4, 8] = true := by decide +kernel
theorem sbd8_1_4 : ∀ q ∈ blkd8_1_4, subd8_1 q = true := by
  unfold blkd8_1_4
  exact List.forall_mem_cons.2 ⟨subd8_1_128, List.forall_mem_cons.2 ⟨subd8_1_129, List.forall_mem_cons.2 ⟨subd8_1_130, List.forall_mem_cons.2 ⟨subd8_1_131, List.forall_mem_cons.2 ⟨subd8_1_132, List.forall_mem_cons.2 ⟨subd8_1_133, List.forall_mem_cons.2 ⟨subd8_1_134, List.forall_mem_cons.2 ⟨subd8_1_135, List.forall_mem_cons.2 ⟨subd8_1_136, List.forall_mem_cons.2 ⟨subd8_1_137, List.forall_mem_cons.2 ⟨subd8_1_138, List.forall_mem_cons.2 ⟨subd8_1_139, List.forall_mem_cons.2 ⟨subd8_1_140, List.forall_mem_cons.2 ⟨subd8_1_141, List.forall_mem_cons.2 ⟨subd8_1_142, List.forall_mem_cons.2 ⟨subd8_1_143, List.forall_mem_cons.2 ⟨subd8_1_144, List.forall_mem_cons.2 ⟨subd8_1_145, List.forall_mem_cons.2 ⟨subd8_1_146, List.forall_mem_cons.2 ⟨subd8_1_147, List.forall_mem_cons.2 ⟨subd8_1_148, List.forall_mem_cons.2 ⟨subd8_1_149, List.forall_mem_cons.2 ⟨subd8_1_150, List.forall_mem_cons.2 ⟨subd8_1_151, List.forall_mem_cons.2 ⟨subd8_1_152, List.forall_mem_cons.2 ⟨subd8_1_153, List.forall_mem_cons.2 ⟨subd8_1_154, List.forall_mem_cons.2 ⟨subd8_1_155, List.forall_mem_cons.2 ⟨subd8_1_156, List.forall_mem_cons.2 ⟨subd8_1_157, List.forall_mem_cons.2 ⟨subd8_1_158, List.forall_mem_cons.2 ⟨subd8_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_160 : subd8_1 [-8, 5, -6] = true := by decide +kernel
theorem subd8_1_161 : subd8_1 [-8, 5, -5] = true := by decide +kernel
theorem subd8_1_162 : subd8_1 [-8, 5, -4] = true := by decide +kernel
theorem subd8_1_163 : subd8_1 [-8, 5, -3] = true := by decide +kernel
theorem subd8_1_164 : subd8_1 [-8, 5, -2] = true := by decide +kernel
theorem subd8_1_165 : subd8_1 [-8, 5, -1] = true := by decide +kernel
theorem subd8_1_166 : subd8_1 [-8, 5, 0] = true := by decide +kernel
theorem subd8_1_167 : subd8_1 [-8, 5, 1] = true := by decide +kernel
theorem subd8_1_168 : subd8_1 [-8, 5, 2] = true := by decide +kernel
theorem subd8_1_169 : subd8_1 [-8, 5, 3] = true := by decide +kernel
theorem subd8_1_170 : subd8_1 [-8, 5, 4] = true := by decide +kernel
theorem subd8_1_171 : subd8_1 [-8, 5, 5] = true := by decide +kernel
theorem subd8_1_172 : subd8_1 [-8, 5, 6] = true := by decide +kernel
theorem subd8_1_173 : subd8_1 [-8, 5, 7] = true := by decide +kernel
theorem subd8_1_174 : subd8_1 [-8, 5, 8] = true := by decide +kernel
theorem subd8_1_175 : subd8_1 [-8, 6] = true := by decide +kernel
theorem subd8_1_176 : subd8_1 [-8, 7] = true := by decide +kernel
theorem subd8_1_177 : subd8_1 [-8, 8] = true := by decide +kernel
theorem subd8_1_178 : subd8_1 [-8, 9] = true := by decide +kernel
theorem subd8_1_179 : subd8_1 [-7, -7] = true := by decide +kernel
theorem subd8_1_180 : subd8_1 [-7, -6] = true := by decide +kernel
theorem subd8_1_181 : subd8_1 [-7, -5] = true := by decide +kernel
theorem subd8_1_182 : subd8_1 [-7, -4] = true := by decide +kernel
theorem subd8_1_183 : subd8_1 [-7, -3, -8] = true := by decide +kernel
theorem subd8_1_184 : subd8_1 [-7, -3, -7] = true := by decide +kernel
theorem subd8_1_185 : subd8_1 [-7, -3, -6] = true := by decide +kernel
theorem subd8_1_186 : subd8_1 [-7, -3, -5] = true := by decide +kernel
theorem subd8_1_187 : subd8_1 [-7, -3, -4] = true := by decide +kernel
theorem subd8_1_188 : subd8_1 [-7, -3, -3] = true := by decide +kernel
theorem subd8_1_189 : subd8_1 [-7, -3, -2] = true := by decide +kernel
theorem subd8_1_190 : subd8_1 [-7, -3, -1] = true := by decide +kernel
theorem subd8_1_191 : subd8_1 [-7, -3, 0] = true := by decide +kernel
theorem sbd8_1_5 : ∀ q ∈ blkd8_1_5, subd8_1 q = true := by
  unfold blkd8_1_5
  exact List.forall_mem_cons.2 ⟨subd8_1_160, List.forall_mem_cons.2 ⟨subd8_1_161, List.forall_mem_cons.2 ⟨subd8_1_162, List.forall_mem_cons.2 ⟨subd8_1_163, List.forall_mem_cons.2 ⟨subd8_1_164, List.forall_mem_cons.2 ⟨subd8_1_165, List.forall_mem_cons.2 ⟨subd8_1_166, List.forall_mem_cons.2 ⟨subd8_1_167, List.forall_mem_cons.2 ⟨subd8_1_168, List.forall_mem_cons.2 ⟨subd8_1_169, List.forall_mem_cons.2 ⟨subd8_1_170, List.forall_mem_cons.2 ⟨subd8_1_171, List.forall_mem_cons.2 ⟨subd8_1_172, List.forall_mem_cons.2 ⟨subd8_1_173, List.forall_mem_cons.2 ⟨subd8_1_174, List.forall_mem_cons.2 ⟨subd8_1_175, List.forall_mem_cons.2 ⟨subd8_1_176, List.forall_mem_cons.2 ⟨subd8_1_177, List.forall_mem_cons.2 ⟨subd8_1_178, List.forall_mem_cons.2 ⟨subd8_1_179, List.forall_mem_cons.2 ⟨subd8_1_180, List.forall_mem_cons.2 ⟨subd8_1_181, List.forall_mem_cons.2 ⟨subd8_1_182, List.forall_mem_cons.2 ⟨subd8_1_183, List.forall_mem_cons.2 ⟨subd8_1_184, List.forall_mem_cons.2 ⟨subd8_1_185, List.forall_mem_cons.2 ⟨subd8_1_186, List.forall_mem_cons.2 ⟨subd8_1_187, List.forall_mem_cons.2 ⟨subd8_1_188, List.forall_mem_cons.2 ⟨subd8_1_189, List.forall_mem_cons.2 ⟨subd8_1_190, List.forall_mem_cons.2 ⟨subd8_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_192 : subd8_1 [-7, -3, 1] = true := by decide +kernel
theorem subd8_1_193 : subd8_1 [-7, -3, 2] = true := by decide +kernel
theorem subd8_1_194 : subd8_1 [-7, -3, 3] = true := by decide +kernel
theorem subd8_1_195 : subd8_1 [-7, -3, 4] = true := by decide +kernel
theorem subd8_1_196 : subd8_1 [-7, -3, 5] = true := by decide +kernel
theorem subd8_1_197 : subd8_1 [-7, -3, 6] = true := by decide +kernel
theorem subd8_1_198 : subd8_1 [-7, -2, -8] = true := by decide +kernel
theorem subd8_1_199 : subd8_1 [-7, -2, -7] = true := by decide +kernel
theorem subd8_1_200 : subd8_1 [-7, -2, -6] = true := by decide +kernel
theorem subd8_1_201 : subd8_1 [-7, -2, -5] = true := by decide +kernel
theorem subd8_1_202 : subd8_1 [-7, -2, -4] = true := by decide +kernel
theorem subd8_1_203 : subd8_1 [-7, -2, -3] = true := by decide +kernel
theorem subd8_1_204 : subd8_1 [-7, -2, -2] = true := by decide +kernel
theorem subd8_1_205 : subd8_1 [-7, -2, -1] = true := by decide +kernel
theorem subd8_1_206 : subd8_1 [-7, -2, 0] = true := by decide +kernel
theorem subd8_1_207 : subd8_1 [-7, -2, 1] = true := by decide +kernel
theorem subd8_1_208 : subd8_1 [-7, -2, 2] = true := by decide +kernel
theorem subd8_1_209 : subd8_1 [-7, -2, 3] = true := by decide +kernel
theorem subd8_1_210 : subd8_1 [-7, -2, 4] = true := by decide +kernel
theorem subd8_1_211 : subd8_1 [-7, -2, 5] = true := by decide +kernel
theorem subd8_1_212 : subd8_1 [-7, -2, 6] = true := by decide +kernel
theorem subd8_1_213 : subd8_1 [-7, -2, 7] = true := by decide +kernel
theorem subd8_1_214 : subd8_1 [-7, -1, -8] = true := by decide +kernel
theorem subd8_1_215 : subd8_1 [-7, -1, -7] = true := by decide +kernel
theorem subd8_1_216 : subd8_1 [-7, -1, -6] = true := by decide +kernel
theorem subd8_1_217 : subd8_1 [-7, -1, -5] = true := by decide +kernel
theorem subd8_1_218 : subd8_1 [-7, -1, -4] = true := by decide +kernel
theorem subd8_1_219 : subd8_1 [-7, -1, -3] = true := by decide +kernel
theorem subd8_1_220 : subd8_1 [-7, -1, -2] = true := by decide +kernel
theorem subd8_1_221 : subd8_1 [-7, -1, -1] = true := by decide +kernel
theorem subd8_1_222 : subd8_1 [-7, -1, 0] = true := by decide +kernel
theorem subd8_1_223 : subd8_1 [-7, -1, 1] = true := by decide +kernel
theorem sbd8_1_6 : ∀ q ∈ blkd8_1_6, subd8_1 q = true := by
  unfold blkd8_1_6
  exact List.forall_mem_cons.2 ⟨subd8_1_192, List.forall_mem_cons.2 ⟨subd8_1_193, List.forall_mem_cons.2 ⟨subd8_1_194, List.forall_mem_cons.2 ⟨subd8_1_195, List.forall_mem_cons.2 ⟨subd8_1_196, List.forall_mem_cons.2 ⟨subd8_1_197, List.forall_mem_cons.2 ⟨subd8_1_198, List.forall_mem_cons.2 ⟨subd8_1_199, List.forall_mem_cons.2 ⟨subd8_1_200, List.forall_mem_cons.2 ⟨subd8_1_201, List.forall_mem_cons.2 ⟨subd8_1_202, List.forall_mem_cons.2 ⟨subd8_1_203, List.forall_mem_cons.2 ⟨subd8_1_204, List.forall_mem_cons.2 ⟨subd8_1_205, List.forall_mem_cons.2 ⟨subd8_1_206, List.forall_mem_cons.2 ⟨subd8_1_207, List.forall_mem_cons.2 ⟨subd8_1_208, List.forall_mem_cons.2 ⟨subd8_1_209, List.forall_mem_cons.2 ⟨subd8_1_210, List.forall_mem_cons.2 ⟨subd8_1_211, List.forall_mem_cons.2 ⟨subd8_1_212, List.forall_mem_cons.2 ⟨subd8_1_213, List.forall_mem_cons.2 ⟨subd8_1_214, List.forall_mem_cons.2 ⟨subd8_1_215, List.forall_mem_cons.2 ⟨subd8_1_216, List.forall_mem_cons.2 ⟨subd8_1_217, List.forall_mem_cons.2 ⟨subd8_1_218, List.forall_mem_cons.2 ⟨subd8_1_219, List.forall_mem_cons.2 ⟨subd8_1_220, List.forall_mem_cons.2 ⟨subd8_1_221, List.forall_mem_cons.2 ⟨subd8_1_222, List.forall_mem_cons.2 ⟨subd8_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_224 : subd8_1 [-7, -1, 2] = true := by decide +kernel
theorem subd8_1_225 : subd8_1 [-7, -1, 3] = true := by decide +kernel
theorem subd8_1_226 : subd8_1 [-7, -1, 4] = true := by decide +kernel
theorem subd8_1_227 : subd8_1 [-7, -1, 5] = true := by decide +kernel
theorem subd8_1_228 : subd8_1 [-7, -1, 6] = true := by decide +kernel
theorem subd8_1_229 : subd8_1 [-7, -1, 7] = true := by decide +kernel
theorem subd8_1_230 : subd8_1 [-7, 0, -8] = true := by decide +kernel
theorem subd8_1_231 : subd8_1 [-7, 0, -7] = true := by decide +kernel
theorem subd8_1_232 : subd8_1 [-7, 0, -6] = true := by decide +kernel
theorem subd8_1_233 : subd8_1 [-7, 0, -5] = true := by decide +kernel
theorem subd8_1_234 : subd8_1 [-7, 0, -4] = true := by decide +kernel
theorem subd8_1_235 : subd8_1 [-7, 0, -3] = true := by decide +kernel
theorem subd8_1_236 : subd8_1 [-7, 0, -2] = true := by decide +kernel
theorem subd8_1_237 : subd8_1 [-7, 0, -1] = true := by decide +kernel
theorem subd8_1_238 : subd8_1 [-7, 0, 0] = true := by decide +kernel
theorem subd8_1_239 : subd8_1 [-7, 0, 1] = true := by decide +kernel
theorem subd8_1_240 : subd8_1 [-7, 0, 2] = true := by decide +kernel
theorem subd8_1_241 : subd8_1 [-7, 0, 3] = true := by decide +kernel
theorem subd8_1_242 : subd8_1 [-7, 0, 4] = true := by decide +kernel
theorem subd8_1_243 : subd8_1 [-7, 0, 5] = true := by decide +kernel
theorem subd8_1_244 : subd8_1 [-7, 0, 6] = true := by decide +kernel
theorem subd8_1_245 : subd8_1 [-7, 0, 7] = true := by decide +kernel
theorem subd8_1_246 : subd8_1 [-7, 0, 8] = true := by decide +kernel
theorem subd8_1_247 : subd8_1 [-7, 1, -8] = true := by decide +kernel
theorem subd8_1_248 : subd8_1 [-7, 1, -7] = true := by decide +kernel
theorem subd8_1_249 : subd8_1 [-7, 1, -6] = true := by decide +kernel
theorem subd8_1_250 : subd8_1 [-7, 1, -5] = true := by decide +kernel
theorem subd8_1_251 : subd8_1 [-7, 1, -4] = true := by decide +kernel
theorem subd8_1_252 : subd8_1 [-7, 1, -3] = true := by decide +kernel
theorem subd8_1_253 : subd8_1 [-7, 1, -2] = true := by decide +kernel
theorem subd8_1_254 : subd8_1 [-7, 1, -1] = true := by decide +kernel
theorem subd8_1_255 : subd8_1 [-7, 1, 0] = true := by decide +kernel
theorem sbd8_1_7 : ∀ q ∈ blkd8_1_7, subd8_1 q = true := by
  unfold blkd8_1_7
  exact List.forall_mem_cons.2 ⟨subd8_1_224, List.forall_mem_cons.2 ⟨subd8_1_225, List.forall_mem_cons.2 ⟨subd8_1_226, List.forall_mem_cons.2 ⟨subd8_1_227, List.forall_mem_cons.2 ⟨subd8_1_228, List.forall_mem_cons.2 ⟨subd8_1_229, List.forall_mem_cons.2 ⟨subd8_1_230, List.forall_mem_cons.2 ⟨subd8_1_231, List.forall_mem_cons.2 ⟨subd8_1_232, List.forall_mem_cons.2 ⟨subd8_1_233, List.forall_mem_cons.2 ⟨subd8_1_234, List.forall_mem_cons.2 ⟨subd8_1_235, List.forall_mem_cons.2 ⟨subd8_1_236, List.forall_mem_cons.2 ⟨subd8_1_237, List.forall_mem_cons.2 ⟨subd8_1_238, List.forall_mem_cons.2 ⟨subd8_1_239, List.forall_mem_cons.2 ⟨subd8_1_240, List.forall_mem_cons.2 ⟨subd8_1_241, List.forall_mem_cons.2 ⟨subd8_1_242, List.forall_mem_cons.2 ⟨subd8_1_243, List.forall_mem_cons.2 ⟨subd8_1_244, List.forall_mem_cons.2 ⟨subd8_1_245, List.forall_mem_cons.2 ⟨subd8_1_246, List.forall_mem_cons.2 ⟨subd8_1_247, List.forall_mem_cons.2 ⟨subd8_1_248, List.forall_mem_cons.2 ⟨subd8_1_249, List.forall_mem_cons.2 ⟨subd8_1_250, List.forall_mem_cons.2 ⟨subd8_1_251, List.forall_mem_cons.2 ⟨subd8_1_252, List.forall_mem_cons.2 ⟨subd8_1_253, List.forall_mem_cons.2 ⟨subd8_1_254, List.forall_mem_cons.2 ⟨subd8_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_256 : subd8_1 [-7, 1, 1] = true := by decide +kernel
theorem subd8_1_257 : subd8_1 [-7, 1, 2] = true := by decide +kernel
theorem subd8_1_258 : subd8_1 [-7, 1, 3] = true := by decide +kernel
theorem subd8_1_259 : subd8_1 [-7, 1, 4] = true := by decide +kernel
theorem subd8_1_260 : subd8_1 [-7, 1, 5] = true := by decide +kernel
theorem subd8_1_261 : subd8_1 [-7, 1, 6] = true := by decide +kernel
theorem subd8_1_262 : subd8_1 [-7, 1, 7] = true := by decide +kernel
theorem subd8_1_263 : subd8_1 [-7, 1, 8] = true := by decide +kernel
theorem subd8_1_264 : subd8_1 [-7, 2, -8] = true := by decide +kernel
theorem subd8_1_265 : subd8_1 [-7, 2, -7] = true := by decide +kernel
theorem subd8_1_266 : subd8_1 [-7, 2, -6] = true := by decide +kernel
theorem subd8_1_267 : subd8_1 [-7, 2, -5] = true := by decide +kernel
theorem subd8_1_268 : subd8_1 [-7, 2, -4] = true := by decide +kernel
theorem subd8_1_269 : subd8_1 [-7, 2, -3] = true := by decide +kernel
theorem subd8_1_270 : subd8_1 [-7, 2, -2] = true := by decide +kernel
theorem subd8_1_271 : subd8_1 [-7, 2, -1] = true := by decide +kernel
theorem subd8_1_272 : subd8_1 [-7, 2, 0] = true := by decide +kernel
theorem subd8_1_273 : subd8_1 [-7, 2, 1] = true := by decide +kernel
theorem subd8_1_274 : subd8_1 [-7, 2, 2] = true := by decide +kernel
theorem subd8_1_275 : subd8_1 [-7, 2, 3] = true := by decide +kernel
theorem subd8_1_276 : subd8_1 [-7, 2, 4] = true := by decide +kernel
theorem subd8_1_277 : subd8_1 [-7, 2, 5] = true := by decide +kernel
theorem subd8_1_278 : subd8_1 [-7, 2, 6] = true := by decide +kernel
theorem subd8_1_279 : subd8_1 [-7, 2, 7] = true := by decide +kernel
theorem subd8_1_280 : subd8_1 [-7, 2, 8] = true := by decide +kernel
theorem subd8_1_281 : subd8_1 [-7, 2, 9] = true := by decide +kernel
theorem subd8_1_282 : subd8_1 [-7, 3, -8] = true := by decide +kernel
theorem subd8_1_283 : subd8_1 [-7, 3, -7] = true := by decide +kernel
theorem subd8_1_284 : subd8_1 [-7, 3, -6] = true := by decide +kernel
theorem subd8_1_285 : subd8_1 [-7, 3, -5] = true := by decide +kernel
theorem subd8_1_286 : subd8_1 [-7, 3, -4] = true := by decide +kernel
theorem subd8_1_287 : subd8_1 [-7, 3, -3] = true := by decide +kernel
theorem sbd8_1_8 : ∀ q ∈ blkd8_1_8, subd8_1 q = true := by
  unfold blkd8_1_8
  exact List.forall_mem_cons.2 ⟨subd8_1_256, List.forall_mem_cons.2 ⟨subd8_1_257, List.forall_mem_cons.2 ⟨subd8_1_258, List.forall_mem_cons.2 ⟨subd8_1_259, List.forall_mem_cons.2 ⟨subd8_1_260, List.forall_mem_cons.2 ⟨subd8_1_261, List.forall_mem_cons.2 ⟨subd8_1_262, List.forall_mem_cons.2 ⟨subd8_1_263, List.forall_mem_cons.2 ⟨subd8_1_264, List.forall_mem_cons.2 ⟨subd8_1_265, List.forall_mem_cons.2 ⟨subd8_1_266, List.forall_mem_cons.2 ⟨subd8_1_267, List.forall_mem_cons.2 ⟨subd8_1_268, List.forall_mem_cons.2 ⟨subd8_1_269, List.forall_mem_cons.2 ⟨subd8_1_270, List.forall_mem_cons.2 ⟨subd8_1_271, List.forall_mem_cons.2 ⟨subd8_1_272, List.forall_mem_cons.2 ⟨subd8_1_273, List.forall_mem_cons.2 ⟨subd8_1_274, List.forall_mem_cons.2 ⟨subd8_1_275, List.forall_mem_cons.2 ⟨subd8_1_276, List.forall_mem_cons.2 ⟨subd8_1_277, List.forall_mem_cons.2 ⟨subd8_1_278, List.forall_mem_cons.2 ⟨subd8_1_279, List.forall_mem_cons.2 ⟨subd8_1_280, List.forall_mem_cons.2 ⟨subd8_1_281, List.forall_mem_cons.2 ⟨subd8_1_282, List.forall_mem_cons.2 ⟨subd8_1_283, List.forall_mem_cons.2 ⟨subd8_1_284, List.forall_mem_cons.2 ⟨subd8_1_285, List.forall_mem_cons.2 ⟨subd8_1_286, List.forall_mem_cons.2 ⟨subd8_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_288 : subd8_1 [-7, 3, -2] = true := by decide +kernel
theorem subd8_1_289 : subd8_1 [-7, 3, -1] = true := by decide +kernel
theorem subd8_1_290 : subd8_1 [-7, 3, 0] = true := by decide +kernel
theorem subd8_1_291 : subd8_1 [-7, 3, 1] = true := by decide +kernel
theorem subd8_1_292 : subd8_1 [-7, 3, 2] = true := by decide +kernel
theorem subd8_1_293 : subd8_1 [-7, 3, 3] = true := by decide +kernel
theorem subd8_1_294 : subd8_1 [-7, 3, 4] = true := by decide +kernel
theorem subd8_1_295 : subd8_1 [-7, 3, 5] = true := by decide +kernel
theorem subd8_1_296 : subd8_1 [-7, 3, 6] = true := by decide +kernel
theorem subd8_1_297 : subd8_1 [-7, 3, 7] = true := by decide +kernel
theorem subd8_1_298 : subd8_1 [-7, 3, 8] = true := by decide +kernel
theorem subd8_1_299 : subd8_1 [-7, 3, 9] = true := by decide +kernel
theorem subd8_1_300 : subd8_1 [-7, 4, -7] = true := by decide +kernel
theorem subd8_1_301 : subd8_1 [-7, 4, -6] = true := by decide +kernel
theorem subd8_1_302 : subd8_1 [-7, 4, -5] = true := by decide +kernel
theorem subd8_1_303 : subd8_1 [-7, 4, -4] = true := by decide +kernel
theorem subd8_1_304 : subd8_1 [-7, 4, -3] = true := by decide +kernel
theorem subd8_1_305 : subd8_1 [-7, 4, -2] = true := by decide +kernel
theorem subd8_1_306 : subd8_1 [-7, 4, -1] = true := by decide +kernel
theorem subd8_1_307 : subd8_1 [-7, 4, 0] = true := by decide +kernel
theorem subd8_1_308 : subd8_1 [-7, 4, 1] = true := by decide +kernel
theorem subd8_1_309 : subd8_1 [-7, 4, 2] = true := by decide +kernel
theorem subd8_1_310 : subd8_1 [-7, 4, 3] = true := by decide +kernel
theorem subd8_1_311 : subd8_1 [-7, 4, 4] = true := by decide +kernel
theorem subd8_1_312 : subd8_1 [-7, 4, 5] = true := by decide +kernel
theorem subd8_1_313 : subd8_1 [-7, 4, 6] = true := by decide +kernel
theorem subd8_1_314 : subd8_1 [-7, 4, 7] = true := by decide +kernel
theorem subd8_1_315 : subd8_1 [-7, 4, 8] = true := by decide +kernel
theorem subd8_1_316 : subd8_1 [-7, 4, 9] = true := by decide +kernel
theorem subd8_1_317 : subd8_1 [-7, 5, -6] = true := by decide +kernel
theorem subd8_1_318 : subd8_1 [-7, 5, -5] = true := by decide +kernel
theorem subd8_1_319 : subd8_1 [-7, 5, -4] = true := by decide +kernel
theorem sbd8_1_9 : ∀ q ∈ blkd8_1_9, subd8_1 q = true := by
  unfold blkd8_1_9
  exact List.forall_mem_cons.2 ⟨subd8_1_288, List.forall_mem_cons.2 ⟨subd8_1_289, List.forall_mem_cons.2 ⟨subd8_1_290, List.forall_mem_cons.2 ⟨subd8_1_291, List.forall_mem_cons.2 ⟨subd8_1_292, List.forall_mem_cons.2 ⟨subd8_1_293, List.forall_mem_cons.2 ⟨subd8_1_294, List.forall_mem_cons.2 ⟨subd8_1_295, List.forall_mem_cons.2 ⟨subd8_1_296, List.forall_mem_cons.2 ⟨subd8_1_297, List.forall_mem_cons.2 ⟨subd8_1_298, List.forall_mem_cons.2 ⟨subd8_1_299, List.forall_mem_cons.2 ⟨subd8_1_300, List.forall_mem_cons.2 ⟨subd8_1_301, List.forall_mem_cons.2 ⟨subd8_1_302, List.forall_mem_cons.2 ⟨subd8_1_303, List.forall_mem_cons.2 ⟨subd8_1_304, List.forall_mem_cons.2 ⟨subd8_1_305, List.forall_mem_cons.2 ⟨subd8_1_306, List.forall_mem_cons.2 ⟨subd8_1_307, List.forall_mem_cons.2 ⟨subd8_1_308, List.forall_mem_cons.2 ⟨subd8_1_309, List.forall_mem_cons.2 ⟨subd8_1_310, List.forall_mem_cons.2 ⟨subd8_1_311, List.forall_mem_cons.2 ⟨subd8_1_312, List.forall_mem_cons.2 ⟨subd8_1_313, List.forall_mem_cons.2 ⟨subd8_1_314, List.forall_mem_cons.2 ⟨subd8_1_315, List.forall_mem_cons.2 ⟨subd8_1_316, List.forall_mem_cons.2 ⟨subd8_1_317, List.forall_mem_cons.2 ⟨subd8_1_318, List.forall_mem_cons.2 ⟨subd8_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_320 : subd8_1 [-7, 5, -3] = true := by decide +kernel
theorem subd8_1_321 : subd8_1 [-7, 5, -2] = true := by decide +kernel
theorem subd8_1_322 : subd8_1 [-7, 5, -1] = true := by decide +kernel
theorem subd8_1_323 : subd8_1 [-7, 5, 0] = true := by decide +kernel
theorem subd8_1_324 : subd8_1 [-7, 5, 1] = true := by decide +kernel
theorem subd8_1_325 : subd8_1 [-7, 5, 2] = true := by decide +kernel
theorem subd8_1_326 : subd8_1 [-7, 5, 3] = true := by decide +kernel
theorem subd8_1_327 : subd8_1 [-7, 5, 4] = true := by decide +kernel
theorem subd8_1_328 : subd8_1 [-7, 5, 5] = true := by decide +kernel
theorem subd8_1_329 : subd8_1 [-7, 5, 6] = true := by decide +kernel
theorem subd8_1_330 : subd8_1 [-7, 5, 7] = true := by decide +kernel
theorem subd8_1_331 : subd8_1 [-7, 5, 8] = true := by decide +kernel
theorem subd8_1_332 : subd8_1 [-7, 5, 9] = true := by decide +kernel
theorem subd8_1_333 : subd8_1 [-7, 6, -6] = true := by decide +kernel
theorem subd8_1_334 : subd8_1 [-7, 6, -5] = true := by decide +kernel
theorem subd8_1_335 : subd8_1 [-7, 6, -4] = true := by decide +kernel
theorem subd8_1_336 : subd8_1 [-7, 6, -3] = true := by decide +kernel
theorem subd8_1_337 : subd8_1 [-7, 6, -2] = true := by decide +kernel
theorem subd8_1_338 : subd8_1 [-7, 6, -1] = true := by decide +kernel
theorem subd8_1_339 : subd8_1 [-7, 6, 0] = true := by decide +kernel
theorem subd8_1_340 : subd8_1 [-7, 6, 1] = true := by decide +kernel
theorem subd8_1_341 : subd8_1 [-7, 6, 2] = true := by decide +kernel
theorem subd8_1_342 : subd8_1 [-7, 6, 3] = true := by decide +kernel
theorem subd8_1_343 : subd8_1 [-7, 6, 4] = true := by decide +kernel
theorem subd8_1_344 : subd8_1 [-7, 6, 5] = true := by decide +kernel
theorem subd8_1_345 : subd8_1 [-7, 6, 6] = true := by decide +kernel
theorem subd8_1_346 : subd8_1 [-7, 6, 7] = true := by decide +kernel
theorem subd8_1_347 : subd8_1 [-7, 6, 8] = true := by decide +kernel
theorem subd8_1_348 : subd8_1 [-7, 6, 9] = true := by decide +kernel
theorem subd8_1_349 : subd8_1 [-7, 7] = true := by decide +kernel
theorem subd8_1_350 : subd8_1 [-7, 8] = true := by decide +kernel
theorem subd8_1_351 : subd8_1 [-7, 9] = true := by decide +kernel
theorem sbd8_1_10 : ∀ q ∈ blkd8_1_10, subd8_1 q = true := by
  unfold blkd8_1_10
  exact List.forall_mem_cons.2 ⟨subd8_1_320, List.forall_mem_cons.2 ⟨subd8_1_321, List.forall_mem_cons.2 ⟨subd8_1_322, List.forall_mem_cons.2 ⟨subd8_1_323, List.forall_mem_cons.2 ⟨subd8_1_324, List.forall_mem_cons.2 ⟨subd8_1_325, List.forall_mem_cons.2 ⟨subd8_1_326, List.forall_mem_cons.2 ⟨subd8_1_327, List.forall_mem_cons.2 ⟨subd8_1_328, List.forall_mem_cons.2 ⟨subd8_1_329, List.forall_mem_cons.2 ⟨subd8_1_330, List.forall_mem_cons.2 ⟨subd8_1_331, List.forall_mem_cons.2 ⟨subd8_1_332, List.forall_mem_cons.2 ⟨subd8_1_333, List.forall_mem_cons.2 ⟨subd8_1_334, List.forall_mem_cons.2 ⟨subd8_1_335, List.forall_mem_cons.2 ⟨subd8_1_336, List.forall_mem_cons.2 ⟨subd8_1_337, List.forall_mem_cons.2 ⟨subd8_1_338, List.forall_mem_cons.2 ⟨subd8_1_339, List.forall_mem_cons.2 ⟨subd8_1_340, List.forall_mem_cons.2 ⟨subd8_1_341, List.forall_mem_cons.2 ⟨subd8_1_342, List.forall_mem_cons.2 ⟨subd8_1_343, List.forall_mem_cons.2 ⟨subd8_1_344, List.forall_mem_cons.2 ⟨subd8_1_345, List.forall_mem_cons.2 ⟨subd8_1_346, List.forall_mem_cons.2 ⟨subd8_1_347, List.forall_mem_cons.2 ⟨subd8_1_348, List.forall_mem_cons.2 ⟨subd8_1_349, List.forall_mem_cons.2 ⟨subd8_1_350, List.forall_mem_cons.2 ⟨subd8_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_352 : subd8_1 [-7, 10] = true := by decide +kernel
theorem subd8_1_353 : subd8_1 [-6, -8] = true := by decide +kernel
theorem subd8_1_354 : subd8_1 [-6, -7] = true := by decide +kernel
theorem subd8_1_355 : subd8_1 [-6, -6] = true := by decide +kernel
theorem subd8_1_356 : subd8_1 [-6, -5] = true := by decide +kernel
theorem subd8_1_357 : subd8_1 [-6, -4, -9] = true := by decide +kernel
theorem subd8_1_358 : subd8_1 [-6, -4, -8] = true := by decide +kernel
theorem subd8_1_359 : subd8_1 [-6, -4, -7] = true := by decide +kernel
theorem subd8_1_360 : subd8_1 [-6, -4, -6] = true := by decide +kernel
theorem subd8_1_361 : subd8_1 [-6, -4, -5] = true := by decide +kernel
theorem subd8_1_362 : subd8_1 [-6, -4, -4] = true := by decide +kernel
theorem subd8_1_363 : subd8_1 [-6, -4, -3] = true := by decide +kernel
theorem subd8_1_364 : subd8_1 [-6, -4, -2] = true := by decide +kernel
theorem subd8_1_365 : subd8_1 [-6, -4, -1] = true := by decide +kernel
theorem subd8_1_366 : subd8_1 [-6, -4, 0] = true := by decide +kernel
theorem subd8_1_367 : subd8_1 [-6, -4, 1] = true := by decide +kernel
theorem subd8_1_368 : subd8_1 [-6, -4, 2] = true := by decide +kernel
theorem subd8_1_369 : subd8_1 [-6, -4, 3] = true := by decide +kernel
theorem subd8_1_370 : subd8_1 [-6, -4, 4] = true := by decide +kernel
theorem subd8_1_371 : subd8_1 [-6, -4, 5] = true := by decide +kernel
theorem subd8_1_372 : subd8_1 [-6, -4, 6] = true := by decide +kernel
theorem subd8_1_373 : subd8_1 [-6, -3, -9] = true := by decide +kernel
theorem subd8_1_374 : subd8_1 [-6, -3, -8] = true := by decide +kernel
theorem subd8_1_375 : subd8_1 [-6, -3, -7] = true := by decide +kernel
theorem subd8_1_376 : subd8_1 [-6, -3, -6] = true := by decide +kernel
theorem subd8_1_377 : subd8_1 [-6, -3, -5] = true := by decide +kernel
theorem subd8_1_378 : subd8_1 [-6, -3, -4] = true := by decide +kernel
theorem subd8_1_379 : subd8_1 [-6, -3, -3] = true := by decide +kernel
theorem subd8_1_380 : subd8_1 [-6, -3, -2] = true := by decide +kernel
theorem subd8_1_381 : subd8_1 [-6, -3, -1] = true := by decide +kernel
theorem subd8_1_382 : subd8_1 [-6, -3, 0] = true := by decide +kernel
theorem subd8_1_383 : subd8_1 [-6, -3, 1] = true := by decide +kernel
theorem sbd8_1_11 : ∀ q ∈ blkd8_1_11, subd8_1 q = true := by
  unfold blkd8_1_11
  exact List.forall_mem_cons.2 ⟨subd8_1_352, List.forall_mem_cons.2 ⟨subd8_1_353, List.forall_mem_cons.2 ⟨subd8_1_354, List.forall_mem_cons.2 ⟨subd8_1_355, List.forall_mem_cons.2 ⟨subd8_1_356, List.forall_mem_cons.2 ⟨subd8_1_357, List.forall_mem_cons.2 ⟨subd8_1_358, List.forall_mem_cons.2 ⟨subd8_1_359, List.forall_mem_cons.2 ⟨subd8_1_360, List.forall_mem_cons.2 ⟨subd8_1_361, List.forall_mem_cons.2 ⟨subd8_1_362, List.forall_mem_cons.2 ⟨subd8_1_363, List.forall_mem_cons.2 ⟨subd8_1_364, List.forall_mem_cons.2 ⟨subd8_1_365, List.forall_mem_cons.2 ⟨subd8_1_366, List.forall_mem_cons.2 ⟨subd8_1_367, List.forall_mem_cons.2 ⟨subd8_1_368, List.forall_mem_cons.2 ⟨subd8_1_369, List.forall_mem_cons.2 ⟨subd8_1_370, List.forall_mem_cons.2 ⟨subd8_1_371, List.forall_mem_cons.2 ⟨subd8_1_372, List.forall_mem_cons.2 ⟨subd8_1_373, List.forall_mem_cons.2 ⟨subd8_1_374, List.forall_mem_cons.2 ⟨subd8_1_375, List.forall_mem_cons.2 ⟨subd8_1_376, List.forall_mem_cons.2 ⟨subd8_1_377, List.forall_mem_cons.2 ⟨subd8_1_378, List.forall_mem_cons.2 ⟨subd8_1_379, List.forall_mem_cons.2 ⟨subd8_1_380, List.forall_mem_cons.2 ⟨subd8_1_381, List.forall_mem_cons.2 ⟨subd8_1_382, List.forall_mem_cons.2 ⟨subd8_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_384 : subd8_1 [-6, -3, 2] = true := by decide +kernel
theorem subd8_1_385 : subd8_1 [-6, -3, 3] = true := by decide +kernel
theorem subd8_1_386 : subd8_1 [-6, -3, 4] = true := by decide +kernel
theorem subd8_1_387 : subd8_1 [-6, -3, 5] = true := by decide +kernel
theorem subd8_1_388 : subd8_1 [-6, -3, 6] = true := by decide +kernel
theorem subd8_1_389 : subd8_1 [-6, -3, 7] = true := by decide +kernel
theorem subd8_1_390 : subd8_1 [-6, -2, -9] = true := by decide +kernel
theorem subd8_1_391 : subd8_1 [-6, -2, -8] = true := by decide +kernel
theorem subd8_1_392 : subd8_1 [-6, -2, -7] = true := by decide +kernel
theorem subd8_1_393 : subd8_1 [-6, -2, -6] = true := by decide +kernel
theorem subd8_1_394 : subd8_1 [-6, -2, -5] = true := by decide +kernel
theorem subd8_1_395 : subd8_1 [-6, -2, -4] = true := by decide +kernel
theorem subd8_1_396 : subd8_1 [-6, -2, -3] = true := by decide +kernel
theorem subd8_1_397 : subd8_1 [-6, -2, -2] = true := by decide +kernel
theorem subd8_1_398 : subd8_1 [-6, -2, -1] = true := by decide +kernel
theorem subd8_1_399 : subd8_1 [-6, -2, 0] = true := by decide +kernel
theorem subd8_1_400 : subd8_1 [-6, -2, 1] = true := by decide +kernel
theorem subd8_1_401 : subd8_1 [-6, -2, 2] = true := by decide +kernel
theorem subd8_1_402 : subd8_1 [-6, -2, 3] = true := by decide +kernel
theorem subd8_1_403 : subd8_1 [-6, -2, 4] = true := by decide +kernel
theorem subd8_1_404 : subd8_1 [-6, -2, 5] = true := by decide +kernel
theorem subd8_1_405 : subd8_1 [-6, -2, 6] = true := by decide +kernel
theorem subd8_1_406 : subd8_1 [-6, -2, 7] = true := by decide +kernel
theorem subd8_1_407 : subd8_1 [-6, -1, -9] = true := by decide +kernel
theorem subd8_1_408 : subd8_1 [-6, -1, -8] = true := by decide +kernel
theorem subd8_1_409 : subd8_1 [-6, -1, -7] = true := by decide +kernel
theorem subd8_1_410 : subd8_1 [-6, -1, -6] = true := by decide +kernel
theorem subd8_1_411 : subd8_1 [-6, -1, -5] = true := by decide +kernel
theorem subd8_1_412 : subd8_1 [-6, -1, -4] = true := by decide +kernel
theorem subd8_1_413 : subd8_1 [-6, -1, -3] = true := by decide +kernel
theorem subd8_1_414 : subd8_1 [-6, -1, -2] = true := by decide +kernel
theorem subd8_1_415 : subd8_1 [-6, -1, -1] = true := by decide +kernel
theorem sbd8_1_12 : ∀ q ∈ blkd8_1_12, subd8_1 q = true := by
  unfold blkd8_1_12
  exact List.forall_mem_cons.2 ⟨subd8_1_384, List.forall_mem_cons.2 ⟨subd8_1_385, List.forall_mem_cons.2 ⟨subd8_1_386, List.forall_mem_cons.2 ⟨subd8_1_387, List.forall_mem_cons.2 ⟨subd8_1_388, List.forall_mem_cons.2 ⟨subd8_1_389, List.forall_mem_cons.2 ⟨subd8_1_390, List.forall_mem_cons.2 ⟨subd8_1_391, List.forall_mem_cons.2 ⟨subd8_1_392, List.forall_mem_cons.2 ⟨subd8_1_393, List.forall_mem_cons.2 ⟨subd8_1_394, List.forall_mem_cons.2 ⟨subd8_1_395, List.forall_mem_cons.2 ⟨subd8_1_396, List.forall_mem_cons.2 ⟨subd8_1_397, List.forall_mem_cons.2 ⟨subd8_1_398, List.forall_mem_cons.2 ⟨subd8_1_399, List.forall_mem_cons.2 ⟨subd8_1_400, List.forall_mem_cons.2 ⟨subd8_1_401, List.forall_mem_cons.2 ⟨subd8_1_402, List.forall_mem_cons.2 ⟨subd8_1_403, List.forall_mem_cons.2 ⟨subd8_1_404, List.forall_mem_cons.2 ⟨subd8_1_405, List.forall_mem_cons.2 ⟨subd8_1_406, List.forall_mem_cons.2 ⟨subd8_1_407, List.forall_mem_cons.2 ⟨subd8_1_408, List.forall_mem_cons.2 ⟨subd8_1_409, List.forall_mem_cons.2 ⟨subd8_1_410, List.forall_mem_cons.2 ⟨subd8_1_411, List.forall_mem_cons.2 ⟨subd8_1_412, List.forall_mem_cons.2 ⟨subd8_1_413, List.forall_mem_cons.2 ⟨subd8_1_414, List.forall_mem_cons.2 ⟨subd8_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_416 : subd8_1 [-6, -1, 0] = true := by decide +kernel
theorem subd8_1_417 : subd8_1 [-6, -1, 1] = true := by decide +kernel
theorem subd8_1_418 : subd8_1 [-6, -1, 2] = true := by decide +kernel
theorem subd8_1_419 : subd8_1 [-6, -1, 3] = true := by decide +kernel
theorem subd8_1_420 : subd8_1 [-6, -1, 4] = true := by decide +kernel
theorem subd8_1_421 : subd8_1 [-6, -1, 5] = true := by decide +kernel
theorem subd8_1_422 : subd8_1 [-6, -1, 6] = true := by decide +kernel
theorem subd8_1_423 : subd8_1 [-6, -1, 7] = true := by decide +kernel
theorem subd8_1_424 : subd8_1 [-6, -1, 8] = true := by decide +kernel
theorem subd8_1_425 : subd8_1 [-6, 0, -9] = true := by decide +kernel
theorem subd8_1_426 : subd8_1 [-6, 0, -8] = true := by decide +kernel
theorem subd8_1_427 : subd8_1 [-6, 0, -7] = true := by decide +kernel
theorem subd8_1_428 : subd8_1 [-6, 0, -6] = true := by decide +kernel
theorem subd8_1_429 : subd8_1 [-6, 0, -5] = true := by decide +kernel
theorem subd8_1_430 : subd8_1 [-6, 0, -4] = true := by decide +kernel
theorem subd8_1_431 : subd8_1 [-6, 0, -3] = true := by decide +kernel
theorem subd8_1_432 : subd8_1 [-6, 0, -2] = true := by decide +kernel
theorem subd8_1_433 : subd8_1 [-6, 0, -1] = true := by decide +kernel
theorem subd8_1_434 : subd8_1 [-6, 0, 0] = true := by decide +kernel
theorem subd8_1_435 : subd8_1 [-6, 0, 1] = true := by decide +kernel
theorem subd8_1_436 : subd8_1 [-6, 0, 2] = true := by decide +kernel
theorem subd8_1_437 : subd8_1 [-6, 0, 3] = true := by decide +kernel
theorem subd8_1_438 : subd8_1 [-6, 0, 4] = true := by decide +kernel
theorem subd8_1_439 : subd8_1 [-6, 0, 5] = true := by decide +kernel
theorem subd8_1_440 : subd8_1 [-6, 0, 6] = true := by decide +kernel
theorem subd8_1_441 : subd8_1 [-6, 0, 7] = true := by decide +kernel
theorem subd8_1_442 : subd8_1 [-6, 0, 8] = true := by decide +kernel
theorem subd8_1_443 : subd8_1 [-6, 0, 9] = true := by decide +kernel
theorem subd8_1_444 : subd8_1 [-6, 1, -9] = true := by decide +kernel
theorem subd8_1_445 : subd8_1 [-6, 1, -8] = true := by decide +kernel
theorem subd8_1_446 : subd8_1 [-6, 1, -7] = true := by decide +kernel
theorem subd8_1_447 : subd8_1 [-6, 1, -6] = true := by decide +kernel
theorem sbd8_1_13 : ∀ q ∈ blkd8_1_13, subd8_1 q = true := by
  unfold blkd8_1_13
  exact List.forall_mem_cons.2 ⟨subd8_1_416, List.forall_mem_cons.2 ⟨subd8_1_417, List.forall_mem_cons.2 ⟨subd8_1_418, List.forall_mem_cons.2 ⟨subd8_1_419, List.forall_mem_cons.2 ⟨subd8_1_420, List.forall_mem_cons.2 ⟨subd8_1_421, List.forall_mem_cons.2 ⟨subd8_1_422, List.forall_mem_cons.2 ⟨subd8_1_423, List.forall_mem_cons.2 ⟨subd8_1_424, List.forall_mem_cons.2 ⟨subd8_1_425, List.forall_mem_cons.2 ⟨subd8_1_426, List.forall_mem_cons.2 ⟨subd8_1_427, List.forall_mem_cons.2 ⟨subd8_1_428, List.forall_mem_cons.2 ⟨subd8_1_429, List.forall_mem_cons.2 ⟨subd8_1_430, List.forall_mem_cons.2 ⟨subd8_1_431, List.forall_mem_cons.2 ⟨subd8_1_432, List.forall_mem_cons.2 ⟨subd8_1_433, List.forall_mem_cons.2 ⟨subd8_1_434, List.forall_mem_cons.2 ⟨subd8_1_435, List.forall_mem_cons.2 ⟨subd8_1_436, List.forall_mem_cons.2 ⟨subd8_1_437, List.forall_mem_cons.2 ⟨subd8_1_438, List.forall_mem_cons.2 ⟨subd8_1_439, List.forall_mem_cons.2 ⟨subd8_1_440, List.forall_mem_cons.2 ⟨subd8_1_441, List.forall_mem_cons.2 ⟨subd8_1_442, List.forall_mem_cons.2 ⟨subd8_1_443, List.forall_mem_cons.2 ⟨subd8_1_444, List.forall_mem_cons.2 ⟨subd8_1_445, List.forall_mem_cons.2 ⟨subd8_1_446, List.forall_mem_cons.2 ⟨subd8_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_448 : subd8_1 [-6, 1, -5] = true := by decide +kernel
theorem subd8_1_449 : subd8_1 [-6, 1, -4] = true := by decide +kernel
theorem subd8_1_450 : subd8_1 [-6, 1, -3] = true := by decide +kernel
theorem subd8_1_451 : subd8_1 [-6, 1, -2] = true := by decide +kernel
theorem subd8_1_452 : subd8_1 [-6, 1, -1] = true := by decide +kernel
theorem subd8_1_453 : subd8_1 [-6, 1, 0] = true := by decide +kernel
theorem subd8_1_454 : subd8_1 [-6, 1, 1] = true := by decide +kernel
theorem subd8_1_455 : subd8_1 [-6, 1, 2] = true := by decide +kernel
theorem subd8_1_456 : subd8_1 [-6, 1, 3] = true := by decide +kernel
theorem subd8_1_457 : subd8_1 [-6, 1, 4] = true := by decide +kernel
theorem subd8_1_458 : subd8_1 [-6, 1, 5] = true := by decide +kernel
theorem subd8_1_459 : subd8_1 [-6, 1, 6] = true := by decide +kernel
theorem subd8_1_460 : subd8_1 [-6, 1, 7] = true := by decide +kernel
theorem subd8_1_461 : subd8_1 [-6, 1, 8] = true := by decide +kernel
theorem subd8_1_462 : subd8_1 [-6, 1, 9] = true := by decide +kernel
theorem subd8_1_463 : subd8_1 [-6, 2, -9] = true := by decide +kernel
theorem subd8_1_464 : subd8_1 [-6, 2, -8] = true := by decide +kernel
theorem subd8_1_465 : subd8_1 [-6, 2, -7] = true := by decide +kernel
theorem subd8_1_466 : subd8_1 [-6, 2, -6] = true := by decide +kernel
theorem subd8_1_467 : subd8_1 [-6, 2, -5] = true := by decide +kernel
theorem subd8_1_468 : subd8_1 [-6, 2, -4] = true := by decide +kernel
theorem subd8_1_469 : subd8_1 [-6, 2, -3] = true := by decide +kernel
theorem subd8_1_470 : subd8_1 [-6, 2, -2] = true := by decide +kernel
theorem subd8_1_471 : subd8_1 [-6, 2, -1] = true := by decide +kernel
theorem subd8_1_472 : subd8_1 [-6, 2, 0] = true := by decide +kernel
theorem subd8_1_473 : subd8_1 [-6, 2, 1] = true := by decide +kernel
theorem subd8_1_474 : subd8_1 [-6, 2, 2] = true := by decide +kernel
theorem subd8_1_475 : subd8_1 [-6, 2, 3] = true := by decide +kernel
theorem subd8_1_476 : subd8_1 [-6, 2, 4] = true := by decide +kernel
theorem subd8_1_477 : subd8_1 [-6, 2, 5] = true := by decide +kernel
theorem subd8_1_478 : subd8_1 [-6, 2, 6] = true := by decide +kernel
theorem subd8_1_479 : subd8_1 [-6, 2, 7] = true := by decide +kernel
theorem sbd8_1_14 : ∀ q ∈ blkd8_1_14, subd8_1 q = true := by
  unfold blkd8_1_14
  exact List.forall_mem_cons.2 ⟨subd8_1_448, List.forall_mem_cons.2 ⟨subd8_1_449, List.forall_mem_cons.2 ⟨subd8_1_450, List.forall_mem_cons.2 ⟨subd8_1_451, List.forall_mem_cons.2 ⟨subd8_1_452, List.forall_mem_cons.2 ⟨subd8_1_453, List.forall_mem_cons.2 ⟨subd8_1_454, List.forall_mem_cons.2 ⟨subd8_1_455, List.forall_mem_cons.2 ⟨subd8_1_456, List.forall_mem_cons.2 ⟨subd8_1_457, List.forall_mem_cons.2 ⟨subd8_1_458, List.forall_mem_cons.2 ⟨subd8_1_459, List.forall_mem_cons.2 ⟨subd8_1_460, List.forall_mem_cons.2 ⟨subd8_1_461, List.forall_mem_cons.2 ⟨subd8_1_462, List.forall_mem_cons.2 ⟨subd8_1_463, List.forall_mem_cons.2 ⟨subd8_1_464, List.forall_mem_cons.2 ⟨subd8_1_465, List.forall_mem_cons.2 ⟨subd8_1_466, List.forall_mem_cons.2 ⟨subd8_1_467, List.forall_mem_cons.2 ⟨subd8_1_468, List.forall_mem_cons.2 ⟨subd8_1_469, List.forall_mem_cons.2 ⟨subd8_1_470, List.forall_mem_cons.2 ⟨subd8_1_471, List.forall_mem_cons.2 ⟨subd8_1_472, List.forall_mem_cons.2 ⟨subd8_1_473, List.forall_mem_cons.2 ⟨subd8_1_474, List.forall_mem_cons.2 ⟨subd8_1_475, List.forall_mem_cons.2 ⟨subd8_1_476, List.forall_mem_cons.2 ⟨subd8_1_477, List.forall_mem_cons.2 ⟨subd8_1_478, List.forall_mem_cons.2 ⟨subd8_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
