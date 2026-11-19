import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_4_32 : subd7_4 [-3, 0, -2] = true := by decide +kernel
theorem subd7_4_33 : subd7_4 [-3, 0, -1] = true := by decide +kernel
theorem subd7_4_34 : subd7_4 [-3, 0, 0] = true := by decide +kernel
theorem subd7_4_35 : subd7_4 [-3, 0, 1] = true := by decide +kernel
theorem subd7_4_36 : subd7_4 [-3, 0, 2] = true := by decide +kernel
theorem subd7_4_37 : subd7_4 [-3, 0, 3] = true := by decide +kernel
theorem subd7_4_38 : subd7_4 [-3, 0, 4] = true := by decide +kernel
theorem subd7_4_39 : subd7_4 [-3, 0, 5] = true := by decide +kernel
theorem subd7_4_40 : subd7_4 [-3, 0, 6] = true := by decide +kernel
theorem subd7_4_41 : subd7_4 [-3, 1] = true := by decide +kernel
theorem subd7_4_42 : subd7_4 [-3, 2] = true := by decide +kernel
theorem subd7_4_43 : subd7_4 [-3, 3] = true := by decide +kernel
theorem subd7_4_44 : subd7_4 [-3, 4] = true := by decide +kernel
theorem subd7_4_45 : subd7_4 [-2, -5] = true := by decide +kernel
theorem subd7_4_46 : subd7_4 [-2, -4] = true := by decide +kernel
theorem subd7_4_47 : subd7_4 [-2, -3] = true := by decide +kernel
theorem subd7_4_48 : subd7_4 [-2, -2, -7] = true := by decide +kernel
theorem subd7_4_49 : subd7_4 [-2, -2, -6] = true := by decide +kernel
theorem subd7_4_50 : subd7_4 [-2, -2, -5] = true := by decide +kernel
theorem subd7_4_51 : subd7_4 [-2, -2, -4] = true := by decide +kernel
theorem subd7_4_52 : subd7_4 [-2, -2, -3] = true := by decide +kernel
theorem subd7_4_53 : subd7_4 [-2, -2, -2] = true := by decide +kernel
theorem subd7_4_54 : subd7_4 [-2, -2, -1] = true := by decide +kernel
theorem subd7_4_55 : subd7_4 [-2, -2, 0] = true := by decide +kernel
theorem subd7_4_56 : subd7_4 [-2, -2, 1] = true := by decide +kernel
theorem subd7_4_57 : subd7_4 [-2, -2, 2] = true := by decide +kernel
theorem subd7_4_58 : subd7_4 [-2, -2, 3] = true := by decide +kernel
theorem subd7_4_59 : subd7_4 [-2, -2, 4] = true := by decide +kernel
theorem subd7_4_60 : subd7_4 [-2, -2, 5] = true := by decide +kernel
theorem subd7_4_61 : subd7_4 [-2, -2, 6] = true := by decide +kernel
theorem subd7_4_62 : subd7_4 [-2, -1, -7] = true := by decide +kernel
theorem subd7_4_63 : subd7_4 [-2, -1, -6] = true := by decide +kernel
theorem sbd7_4_1 : ∀ q ∈ blkd7_4_1, subd7_4 q = true := by
  unfold blkd7_4_1
  exact List.forall_mem_cons.2 ⟨subd7_4_32, List.forall_mem_cons.2 ⟨subd7_4_33, List.forall_mem_cons.2 ⟨subd7_4_34, List.forall_mem_cons.2 ⟨subd7_4_35, List.forall_mem_cons.2 ⟨subd7_4_36, List.forall_mem_cons.2 ⟨subd7_4_37, List.forall_mem_cons.2 ⟨subd7_4_38, List.forall_mem_cons.2 ⟨subd7_4_39, List.forall_mem_cons.2 ⟨subd7_4_40, List.forall_mem_cons.2 ⟨subd7_4_41, List.forall_mem_cons.2 ⟨subd7_4_42, List.forall_mem_cons.2 ⟨subd7_4_43, List.forall_mem_cons.2 ⟨subd7_4_44, List.forall_mem_cons.2 ⟨subd7_4_45, List.forall_mem_cons.2 ⟨subd7_4_46, List.forall_mem_cons.2 ⟨subd7_4_47, List.forall_mem_cons.2 ⟨subd7_4_48, List.forall_mem_cons.2 ⟨subd7_4_49, List.forall_mem_cons.2 ⟨subd7_4_50, List.forall_mem_cons.2 ⟨subd7_4_51, List.forall_mem_cons.2 ⟨subd7_4_52, List.forall_mem_cons.2 ⟨subd7_4_53, List.forall_mem_cons.2 ⟨subd7_4_54, List.forall_mem_cons.2 ⟨subd7_4_55, List.forall_mem_cons.2 ⟨subd7_4_56, List.forall_mem_cons.2 ⟨subd7_4_57, List.forall_mem_cons.2 ⟨subd7_4_58, List.forall_mem_cons.2 ⟨subd7_4_59, List.forall_mem_cons.2 ⟨subd7_4_60, List.forall_mem_cons.2 ⟨subd7_4_61, List.forall_mem_cons.2 ⟨subd7_4_62, List.forall_mem_cons.2 ⟨subd7_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_64 : subd7_4 [-2, -1, -5] = true := by decide +kernel
theorem subd7_4_65 : subd7_4 [-2, -1, -4] = true := by decide +kernel
theorem subd7_4_66 : subd7_4 [-2, -1, -3] = true := by decide +kernel
theorem subd7_4_67 : subd7_4 [-2, -1, -2] = true := by decide +kernel
theorem subd7_4_68 : subd7_4 [-2, -1, -1] = true := by decide +kernel
theorem subd7_4_69 : subd7_4 [-2, -1, 0] = true := by decide +kernel
theorem subd7_4_70 : subd7_4 [-2, -1, 1] = true := by decide +kernel
theorem subd7_4_71 : subd7_4 [-2, -1, 2] = true := by decide +kernel
theorem subd7_4_72 : subd7_4 [-2, -1, 3] = true := by decide +kernel
theorem subd7_4_73 : subd7_4 [-2, -1, 4] = true := by decide +kernel
theorem subd7_4_74 : subd7_4 [-2, -1, 5] = true := by decide +kernel
theorem subd7_4_75 : subd7_4 [-2, -1, 6] = true := by decide +kernel
theorem subd7_4_76 : subd7_4 [-2, -1, 7] = true := by decide +kernel
theorem subd7_4_77 : subd7_4 [-2, 0, -8] = true := by decide +kernel
theorem subd7_4_78 : subd7_4 [-2, 0, -7] = true := by decide +kernel
theorem subd7_4_79 : subd7_4 [-2, 0, -6] = true := by decide +kernel
theorem subd7_4_80 : subd7_4 [-2, 0, -5] = true := by decide +kernel
theorem subd7_4_81 : subd7_4 [-2, 0, -4] = true := by decide +kernel
theorem subd7_4_82 : subd7_4 [-2, 0, -3] = true := by decide +kernel
theorem subd7_4_83 : subd7_4 [-2, 0, -2] = true := by decide +kernel
theorem subd7_4_84 : subd7_4 [-2, 0, -1] = true := by decide +kernel
theorem subd7_4_85 : subd7_4 [-2, 0, 0] = true := by decide +kernel
theorem subd7_4_86 : subd7_4 [-2, 0, 1] = true := by decide +kernel
theorem subd7_4_87 : subd7_4 [-2, 0, 2] = true := by decide +kernel
theorem subd7_4_88 : subd7_4 [-2, 0, 3] = true := by decide +kernel
theorem subd7_4_89 : subd7_4 [-2, 0, 4] = true := by decide +kernel
theorem subd7_4_90 : subd7_4 [-2, 0, 5] = true := by decide +kernel
theorem subd7_4_91 : subd7_4 [-2, 0, 6] = true := by decide +kernel
theorem subd7_4_92 : subd7_4 [-2, 0, 7] = true := by decide +kernel
theorem subd7_4_93 : subd7_4 [-2, 1, -7] = true := by decide +kernel
theorem subd7_4_94 : subd7_4 [-2, 1, -6] = true := by decide +kernel
theorem subd7_4_95 : subd7_4 [-2, 1, -5] = true := by decide +kernel
theorem sbd7_4_2 : ∀ q ∈ blkd7_4_2, subd7_4 q = true := by
  unfold blkd7_4_2
  exact List.forall_mem_cons.2 ⟨subd7_4_64, List.forall_mem_cons.2 ⟨subd7_4_65, List.forall_mem_cons.2 ⟨subd7_4_66, List.forall_mem_cons.2 ⟨subd7_4_67, List.forall_mem_cons.2 ⟨subd7_4_68, List.forall_mem_cons.2 ⟨subd7_4_69, List.forall_mem_cons.2 ⟨subd7_4_70, List.forall_mem_cons.2 ⟨subd7_4_71, List.forall_mem_cons.2 ⟨subd7_4_72, List.forall_mem_cons.2 ⟨subd7_4_73, List.forall_mem_cons.2 ⟨subd7_4_74, List.forall_mem_cons.2 ⟨subd7_4_75, List.forall_mem_cons.2 ⟨subd7_4_76, List.forall_mem_cons.2 ⟨subd7_4_77, List.forall_mem_cons.2 ⟨subd7_4_78, List.forall_mem_cons.2 ⟨subd7_4_79, List.forall_mem_cons.2 ⟨subd7_4_80, List.forall_mem_cons.2 ⟨subd7_4_81, List.forall_mem_cons.2 ⟨subd7_4_82, List.forall_mem_cons.2 ⟨subd7_4_83, List.forall_mem_cons.2 ⟨subd7_4_84, List.forall_mem_cons.2 ⟨subd7_4_85, List.forall_mem_cons.2 ⟨subd7_4_86, List.forall_mem_cons.2 ⟨subd7_4_87, List.forall_mem_cons.2 ⟨subd7_4_88, List.forall_mem_cons.2 ⟨subd7_4_89, List.forall_mem_cons.2 ⟨subd7_4_90, List.forall_mem_cons.2 ⟨subd7_4_91, List.forall_mem_cons.2 ⟨subd7_4_92, List.forall_mem_cons.2 ⟨subd7_4_93, List.forall_mem_cons.2 ⟨subd7_4_94, List.forall_mem_cons.2 ⟨subd7_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_96 : subd7_4 [-2, 1, -4] = true := by decide +kernel
theorem subd7_4_97 : subd7_4 [-2, 1, -3] = true := by decide +kernel
theorem subd7_4_98 : subd7_4 [-2, 1, -2] = true := by decide +kernel
theorem subd7_4_99 : subd7_4 [-2, 1, -1] = true := by decide +kernel
theorem subd7_4_100 : subd7_4 [-2, 1, 0] = true := by decide +kernel
theorem subd7_4_101 : subd7_4 [-2, 1, 1] = true := by decide +kernel
theorem subd7_4_102 : subd7_4 [-2, 1, 2] = true := by decide +kernel
theorem subd7_4_103 : subd7_4 [-2, 1, 3] = true := by decide +kernel
theorem subd7_4_104 : subd7_4 [-2, 1, 4] = true := by decide +kernel
theorem subd7_4_105 : subd7_4 [-2, 1, 5] = true := by decide +kernel
theorem subd7_4_106 : subd7_4 [-2, 1, 6] = true := by decide +kernel
theorem subd7_4_107 : subd7_4 [-2, 2, -7] = true := by decide +kernel
theorem subd7_4_108 : subd7_4 [-2, 2, -6] = true := by decide +kernel
theorem subd7_4_109 : subd7_4 [-2, 2, -5] = true := by decide +kernel
theorem subd7_4_110 : subd7_4 [-2, 2, -4] = true := by decide +kernel
theorem subd7_4_111 : subd7_4 [-2, 2, -3] = true := by decide +kernel
theorem subd7_4_112 : subd7_4 [-2, 2, -2] = true := by decide +kernel
theorem subd7_4_113 : subd7_4 [-2, 2, -1] = true := by decide +kernel
theorem subd7_4_114 : subd7_4 [-2, 2, 0] = true := by decide +kernel
theorem subd7_4_115 : subd7_4 [-2, 2, 1] = true := by decide +kernel
theorem subd7_4_116 : subd7_4 [-2, 2, 2] = true := by decide +kernel
theorem subd7_4_117 : subd7_4 [-2, 2, 3] = true := by decide +kernel
theorem subd7_4_118 : subd7_4 [-2, 2, 4] = true := by decide +kernel
theorem subd7_4_119 : subd7_4 [-2, 2, 5] = true := by decide +kernel
theorem subd7_4_120 : subd7_4 [-2, 2, 6] = true := by decide +kernel
theorem subd7_4_121 : subd7_4 [-2, 3] = true := by decide +kernel
theorem subd7_4_122 : subd7_4 [-2, 4] = true := by decide +kernel
theorem subd7_4_123 : subd7_4 [-1, -6] = true := by decide +kernel
theorem subd7_4_124 : subd7_4 [-1, -5] = true := by decide +kernel
theorem subd7_4_125 : subd7_4 [-1, -4] = true := by decide +kernel
theorem subd7_4_126 : subd7_4 [-1, -3] = true := by decide +kernel
theorem subd7_4_127 : subd7_4 [-1, -2, -7] = true := by decide +kernel
theorem sbd7_4_3 : ∀ q ∈ blkd7_4_3, subd7_4 q = true := by
  unfold blkd7_4_3
  exact List.forall_mem_cons.2 ⟨subd7_4_96, List.forall_mem_cons.2 ⟨subd7_4_97, List.forall_mem_cons.2 ⟨subd7_4_98, List.forall_mem_cons.2 ⟨subd7_4_99, List.forall_mem_cons.2 ⟨subd7_4_100, List.forall_mem_cons.2 ⟨subd7_4_101, List.forall_mem_cons.2 ⟨subd7_4_102, List.forall_mem_cons.2 ⟨subd7_4_103, List.forall_mem_cons.2 ⟨subd7_4_104, List.forall_mem_cons.2 ⟨subd7_4_105, List.forall_mem_cons.2 ⟨subd7_4_106, List.forall_mem_cons.2 ⟨subd7_4_107, List.forall_mem_cons.2 ⟨subd7_4_108, List.forall_mem_cons.2 ⟨subd7_4_109, List.forall_mem_cons.2 ⟨subd7_4_110, List.forall_mem_cons.2 ⟨subd7_4_111, List.forall_mem_cons.2 ⟨subd7_4_112, List.forall_mem_cons.2 ⟨subd7_4_113, List.forall_mem_cons.2 ⟨subd7_4_114, List.forall_mem_cons.2 ⟨subd7_4_115, List.forall_mem_cons.2 ⟨subd7_4_116, List.forall_mem_cons.2 ⟨subd7_4_117, List.forall_mem_cons.2 ⟨subd7_4_118, List.forall_mem_cons.2 ⟨subd7_4_119, List.forall_mem_cons.2 ⟨subd7_4_120, List.forall_mem_cons.2 ⟨subd7_4_121, List.forall_mem_cons.2 ⟨subd7_4_122, List.forall_mem_cons.2 ⟨subd7_4_123, List.forall_mem_cons.2 ⟨subd7_4_124, List.forall_mem_cons.2 ⟨subd7_4_125, List.forall_mem_cons.2 ⟨subd7_4_126, List.forall_mem_cons.2 ⟨subd7_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_128 : subd7_4 [-1, -2, -6] = true := by decide +kernel
theorem subd7_4_129 : subd7_4 [-1, -2, -5] = true := by decide +kernel
theorem subd7_4_130 : subd7_4 [-1, -2, -4] = true := by decide +kernel
theorem subd7_4_131 : subd7_4 [-1, -2, -3] = true := by decide +kernel
theorem subd7_4_132 : subd7_4 [-1, -2, -2] = true := by decide +kernel
theorem subd7_4_133 : subd7_4 [-1, -2, -1] = true := by decide +kernel
theorem subd7_4_134 : subd7_4 [-1, -2, 0] = true := by decide +kernel
theorem subd7_4_135 : subd7_4 [-1, -2, 1] = true := by decide +kernel
theorem subd7_4_136 : subd7_4 [-1, -2, 2] = true := by decide +kernel
theorem subd7_4_137 : subd7_4 [-1, -2, 3] = true := by decide +kernel
theorem subd7_4_138 : subd7_4 [-1, -2, 4] = true := by decide +kernel
theorem subd7_4_139 : subd7_4 [-1, -2, 5] = true := by decide +kernel
theorem subd7_4_140 : subd7_4 [-1, -2, 6] = true := by decide +kernel
theorem subd7_4_141 : subd7_4 [-1, -2, 7] = true := by decide +kernel
theorem subd7_4_142 : subd7_4 [-1, -1, -8] = true := by decide +kernel
theorem subd7_4_143 : subd7_4 [-1, -1, -7] = true := by decide +kernel
theorem subd7_4_144 : subd7_4 [-1, -1, -6] = true := by decide +kernel
theorem subd7_4_145 : subd7_4 [-1, -1, -5] = true := by decide +kernel
theorem subd7_4_146 : subd7_4 [-1, -1, -4] = true := by decide +kernel
theorem subd7_4_147 : subd7_4 [-1, -1, -3] = true := by decide +kernel
theorem subd7_4_148 : subd7_4 [-1, -1, -2] = true := by decide +kernel
theorem subd7_4_149 : subd7_4 [-1, -1, -1] = true := by decide +kernel
theorem subd7_4_150 : subd7_4 [-1, -1, 0] = true := by decide +kernel
theorem subd7_4_151 : subd7_4 [-1, -1, 1] = true := by decide +kernel
theorem subd7_4_152 : subd7_4 [-1, -1, 2] = true := by decide +kernel
theorem subd7_4_153 : subd7_4 [-1, -1, 3] = true := by decide +kernel
theorem subd7_4_154 : subd7_4 [-1, -1, 4] = true := by decide +kernel
theorem subd7_4_155 : subd7_4 [-1, -1, 5] = true := by decide +kernel
theorem subd7_4_156 : subd7_4 [-1, -1, 6] = true := by decide +kernel
theorem subd7_4_157 : subd7_4 [-1, -1, 7] = true := by decide +kernel
theorem subd7_4_158 : subd7_4 [-1, 0, -8] = true := by decide +kernel
theorem subd7_4_159 : subd7_4 [-1, 0, -7] = true := by decide +kernel
theorem sbd7_4_4 : ∀ q ∈ blkd7_4_4, subd7_4 q = true := by
  unfold blkd7_4_4
  exact List.forall_mem_cons.2 ⟨subd7_4_128, List.forall_mem_cons.2 ⟨subd7_4_129, List.forall_mem_cons.2 ⟨subd7_4_130, List.forall_mem_cons.2 ⟨subd7_4_131, List.forall_mem_cons.2 ⟨subd7_4_132, List.forall_mem_cons.2 ⟨subd7_4_133, List.forall_mem_cons.2 ⟨subd7_4_134, List.forall_mem_cons.2 ⟨subd7_4_135, List.forall_mem_cons.2 ⟨subd7_4_136, List.forall_mem_cons.2 ⟨subd7_4_137, List.forall_mem_cons.2 ⟨subd7_4_138, List.forall_mem_cons.2 ⟨subd7_4_139, List.forall_mem_cons.2 ⟨subd7_4_140, List.forall_mem_cons.2 ⟨subd7_4_141, List.forall_mem_cons.2 ⟨subd7_4_142, List.forall_mem_cons.2 ⟨subd7_4_143, List.forall_mem_cons.2 ⟨subd7_4_144, List.forall_mem_cons.2 ⟨subd7_4_145, List.forall_mem_cons.2 ⟨subd7_4_146, List.forall_mem_cons.2 ⟨subd7_4_147, List.forall_mem_cons.2 ⟨subd7_4_148, List.forall_mem_cons.2 ⟨subd7_4_149, List.forall_mem_cons.2 ⟨subd7_4_150, List.forall_mem_cons.2 ⟨subd7_4_151, List.forall_mem_cons.2 ⟨subd7_4_152, List.forall_mem_cons.2 ⟨subd7_4_153, List.forall_mem_cons.2 ⟨subd7_4_154, List.forall_mem_cons.2 ⟨subd7_4_155, List.forall_mem_cons.2 ⟨subd7_4_156, List.forall_mem_cons.2 ⟨subd7_4_157, List.forall_mem_cons.2 ⟨subd7_4_158, List.forall_mem_cons.2 ⟨subd7_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_160 : subd7_4 [-1, 0, -6] = true := by decide +kernel
theorem subd7_4_161 : subd7_4 [-1, 0, -5] = true := by decide +kernel
theorem subd7_4_162 : subd7_4 [-1, 0, -4] = true := by decide +kernel
theorem subd7_4_163 : subd7_4 [-1, 0, -3] = true := by decide +kernel
theorem subd7_4_164 : subd7_4 [-1, 0, -2] = true := by decide +kernel
theorem subd7_4_165 : subd7_4 [-1, 0, -1] = true := by decide +kernel
theorem subd7_4_166 : subd7_4 [-1, 0, 0] = true := by decide +kernel
theorem subd7_4_167 : subd7_4 [-1, 0, 1] = true := by decide +kernel
theorem subd7_4_168 : subd7_4 [-1, 0, 2] = true := by decide +kernel
theorem subd7_4_169 : subd7_4 [-1, 0, 3] = true := by decide +kernel
theorem subd7_4_170 : subd7_4 [-1, 0, 4] = true := by decide +kernel
theorem subd7_4_171 : subd7_4 [-1, 0, 5] = true := by decide +kernel
theorem subd7_4_172 : subd7_4 [-1, 0, 6] = true := by decide +kernel
theorem subd7_4_173 : subd7_4 [-1, 0, 7] = true := by decide +kernel
theorem subd7_4_174 : subd7_4 [-1, 1, -8] = true := by decide +kernel
theorem subd7_4_175 : subd7_4 [-1, 1, -7] = true := by decide +kernel
theorem subd7_4_176 : subd7_4 [-1, 1, -6] = true := by decide +kernel
theorem subd7_4_177 : subd7_4 [-1, 1, -5] = true := by decide +kernel
theorem subd7_4_178 : subd7_4 [-1, 1, -4] = true := by decide +kernel
theorem subd7_4_179 : subd7_4 [-1, 1, -3] = true := by decide +kernel
theorem subd7_4_180 : subd7_4 [-1, 1, -2] = true := by decide +kernel
theorem subd7_4_181 : subd7_4 [-1, 1, -1] = true := by decide +kernel
theorem subd7_4_182 : subd7_4 [-1, 1, 0] = true := by decide +kernel
theorem subd7_4_183 : subd7_4 [-1, 1, 1] = true := by decide +kernel
theorem subd7_4_184 : subd7_4 [-1, 1, 2] = true := by decide +kernel
theorem subd7_4_185 : subd7_4 [-1, 1, 3] = true := by decide +kernel
theorem subd7_4_186 : subd7_4 [-1, 1, 4] = true := by decide +kernel
theorem subd7_4_187 : subd7_4 [-1, 1, 5] = true := by decide +kernel
theorem subd7_4_188 : subd7_4 [-1, 1, 6] = true := by decide +kernel
theorem subd7_4_189 : subd7_4 [-1, 1, 7] = true := by decide +kernel
theorem subd7_4_190 : subd7_4 [-1, 2, -8] = true := by decide +kernel
theorem subd7_4_191 : subd7_4 [-1, 2, -7] = true := by decide +kernel
theorem sbd7_4_5 : ∀ q ∈ blkd7_4_5, subd7_4 q = true := by
  unfold blkd7_4_5
  exact List.forall_mem_cons.2 ⟨subd7_4_160, List.forall_mem_cons.2 ⟨subd7_4_161, List.forall_mem_cons.2 ⟨subd7_4_162, List.forall_mem_cons.2 ⟨subd7_4_163, List.forall_mem_cons.2 ⟨subd7_4_164, List.forall_mem_cons.2 ⟨subd7_4_165, List.forall_mem_cons.2 ⟨subd7_4_166, List.forall_mem_cons.2 ⟨subd7_4_167, List.forall_mem_cons.2 ⟨subd7_4_168, List.forall_mem_cons.2 ⟨subd7_4_169, List.forall_mem_cons.2 ⟨subd7_4_170, List.forall_mem_cons.2 ⟨subd7_4_171, List.forall_mem_cons.2 ⟨subd7_4_172, List.forall_mem_cons.2 ⟨subd7_4_173, List.forall_mem_cons.2 ⟨subd7_4_174, List.forall_mem_cons.2 ⟨subd7_4_175, List.forall_mem_cons.2 ⟨subd7_4_176, List.forall_mem_cons.2 ⟨subd7_4_177, List.forall_mem_cons.2 ⟨subd7_4_178, List.forall_mem_cons.2 ⟨subd7_4_179, List.forall_mem_cons.2 ⟨subd7_4_180, List.forall_mem_cons.2 ⟨subd7_4_181, List.forall_mem_cons.2 ⟨subd7_4_182, List.forall_mem_cons.2 ⟨subd7_4_183, List.forall_mem_cons.2 ⟨subd7_4_184, List.forall_mem_cons.2 ⟨subd7_4_185, List.forall_mem_cons.2 ⟨subd7_4_186, List.forall_mem_cons.2 ⟨subd7_4_187, List.forall_mem_cons.2 ⟨subd7_4_188, List.forall_mem_cons.2 ⟨subd7_4_189, List.forall_mem_cons.2 ⟨subd7_4_190, List.forall_mem_cons.2 ⟨subd7_4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_192 : subd7_4 [-1, 2, -6] = true := by decide +kernel
theorem subd7_4_193 : subd7_4 [-1, 2, -5] = true := by decide +kernel
theorem subd7_4_194 : subd7_4 [-1, 2, -4] = true := by decide +kernel
theorem subd7_4_195 : subd7_4 [-1, 2, -3] = true := by decide +kernel
theorem subd7_4_196 : subd7_4 [-1, 2, -2] = true := by decide +kernel
theorem subd7_4_197 : subd7_4 [-1, 2, -1] = true := by decide +kernel
theorem subd7_4_198 : subd7_4 [-1, 2, 0] = true := by decide +kernel
theorem subd7_4_199 : subd7_4 [-1, 2, 1] = true := by decide +kernel
theorem subd7_4_200 : subd7_4 [-1, 2, 2] = true := by decide +kernel
theorem subd7_4_201 : subd7_4 [-1, 2, 3] = true := by decide +kernel
theorem subd7_4_202 : subd7_4 [-1, 2, 4] = true := by decide +kernel
theorem subd7_4_203 : subd7_4 [-1, 2, 5] = true := by decide +kernel
theorem subd7_4_204 : subd7_4 [-1, 2, 6] = true := by decide +kernel
theorem subd7_4_205 : subd7_4 [-1, 3] = true := by decide +kernel
theorem subd7_4_206 : subd7_4 [-1, 4] = true := by decide +kernel
theorem subd7_4_207 : subd7_4 [-1, 5] = true := by decide +kernel
theorem subd7_4_208 : subd7_4 [0, -6] = true := by decide +kernel
theorem subd7_4_209 : subd7_4 [0, -5] = true := by decide +kernel
theorem subd7_4_210 : subd7_4 [0, -4] = true := by decide +kernel
theorem subd7_4_211 : subd7_4 [0, -3, -6] = true := by decide +kernel
theorem subd7_4_212 : subd7_4 [0, -3, -5] = true := by decide +kernel
theorem subd7_4_213 : subd7_4 [0, -3, -4] = true := by decide +kernel
theorem subd7_4_214 : subd7_4 [0, -3, -3] = true := by decide +kernel
theorem subd7_4_215 : subd7_4 [0, -3, -2] = true := by decide +kernel
theorem subd7_4_216 : subd7_4 [0, -3, -1] = true := by decide +kernel
theorem subd7_4_217 : subd7_4 [0, -3, 0] = true := by decide +kernel
theorem subd7_4_218 : subd7_4 [0, -3, 1] = true := by decide +kernel
theorem subd7_4_219 : subd7_4 [0, -3, 2] = true := by decide +kernel
theorem subd7_4_220 : subd7_4 [0, -3, 3] = true := by decide +kernel
theorem subd7_4_221 : subd7_4 [0, -3, 4] = true := by decide +kernel
theorem subd7_4_222 : subd7_4 [0, -3, 5] = true := by decide +kernel
theorem subd7_4_223 : subd7_4 [0, -3, 6] = true := by decide +kernel
theorem sbd7_4_6 : ∀ q ∈ blkd7_4_6, subd7_4 q = true := by
  unfold blkd7_4_6
  exact List.forall_mem_cons.2 ⟨subd7_4_192, List.forall_mem_cons.2 ⟨subd7_4_193, List.forall_mem_cons.2 ⟨subd7_4_194, List.forall_mem_cons.2 ⟨subd7_4_195, List.forall_mem_cons.2 ⟨subd7_4_196, List.forall_mem_cons.2 ⟨subd7_4_197, List.forall_mem_cons.2 ⟨subd7_4_198, List.forall_mem_cons.2 ⟨subd7_4_199, List.forall_mem_cons.2 ⟨subd7_4_200, List.forall_mem_cons.2 ⟨subd7_4_201, List.forall_mem_cons.2 ⟨subd7_4_202, List.forall_mem_cons.2 ⟨subd7_4_203, List.forall_mem_cons.2 ⟨subd7_4_204, List.forall_mem_cons.2 ⟨subd7_4_205, List.forall_mem_cons.2 ⟨subd7_4_206, List.forall_mem_cons.2 ⟨subd7_4_207, List.forall_mem_cons.2 ⟨subd7_4_208, List.forall_mem_cons.2 ⟨subd7_4_209, List.forall_mem_cons.2 ⟨subd7_4_210, List.forall_mem_cons.2 ⟨subd7_4_211, List.forall_mem_cons.2 ⟨subd7_4_212, List.forall_mem_cons.2 ⟨subd7_4_213, List.forall_mem_cons.2 ⟨subd7_4_214, List.forall_mem_cons.2 ⟨subd7_4_215, List.forall_mem_cons.2 ⟨subd7_4_216, List.forall_mem_cons.2 ⟨subd7_4_217, List.forall_mem_cons.2 ⟨subd7_4_218, List.forall_mem_cons.2 ⟨subd7_4_219, List.forall_mem_cons.2 ⟨subd7_4_220, List.forall_mem_cons.2 ⟨subd7_4_221, List.forall_mem_cons.2 ⟨subd7_4_222, List.forall_mem_cons.2 ⟨subd7_4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_224 : subd7_4 [0, -2, -7] = true := by decide +kernel
theorem subd7_4_225 : subd7_4 [0, -2, -6] = true := by decide +kernel
theorem subd7_4_226 : subd7_4 [0, -2, -5] = true := by decide +kernel
theorem subd7_4_227 : subd7_4 [0, -2, -4] = true := by decide +kernel
theorem subd7_4_228 : subd7_4 [0, -2, -3] = true := by decide +kernel
theorem subd7_4_229 : subd7_4 [0, -2, -2] = true := by decide +kernel
theorem subd7_4_230 : subd7_4 [0, -2, -1] = true := by decide +kernel
theorem subd7_4_231 : subd7_4 [0, -2, 0] = true := by decide +kernel
theorem subd7_4_232 : subd7_4 [0, -2, 1] = true := by decide +kernel
theorem subd7_4_233 : subd7_4 [0, -2, 2] = true := by decide +kernel
theorem subd7_4_234 : subd7_4 [0, -2, 3] = true := by decide +kernel
theorem subd7_4_235 : subd7_4 [0, -2, 4] = true := by decide +kernel
theorem subd7_4_236 : subd7_4 [0, -2, 5] = true := by decide +kernel
theorem subd7_4_237 : subd7_4 [0, -2, 6] = true := by decide +kernel
theorem subd7_4_238 : subd7_4 [0, -2, 7] = true := by decide +kernel
theorem subd7_4_239 : subd7_4 [0, -1, -8] = true := by decide +kernel
theorem subd7_4_240 : subd7_4 [0, -1, -7] = true := by decide +kernel
theorem subd7_4_241 : subd7_4 [0, -1, -6] = true := by decide +kernel
theorem subd7_4_242 : subd7_4 [0, -1, -5] = true := by decide +kernel
theorem subd7_4_243 : subd7_4 [0, -1, -4] = true := by decide +kernel
theorem subd7_4_244 : subd7_4 [0, -1, -3] = true := by decide +kernel
theorem subd7_4_245 : subd7_4 [0, -1, -2] = true := by decide +kernel
theorem subd7_4_246 : subd7_4 [0, -1, -1] = true := by decide +kernel
theorem subd7_4_247 : subd7_4 [0, -1, 0] = true := by decide +kernel
theorem subd7_4_248 : subd7_4 [0, -1, 1] = true := by decide +kernel
theorem subd7_4_249 : subd7_4 [0, -1, 2] = true := by decide +kernel
theorem subd7_4_250 : subd7_4 [0, -1, 3] = true := by decide +kernel
theorem subd7_4_251 : subd7_4 [0, -1, 4] = true := by decide +kernel
theorem subd7_4_252 : subd7_4 [0, -1, 5] = true := by decide +kernel
theorem subd7_4_253 : subd7_4 [0, -1, 6] = true := by decide +kernel
theorem subd7_4_254 : subd7_4 [0, -1, 7] = true := by decide +kernel
theorem subd7_4_255 : subd7_4 [0, 0, -8] = true := by decide +kernel
theorem sbd7_4_7 : ∀ q ∈ blkd7_4_7, subd7_4 q = true := by
  unfold blkd7_4_7
  exact List.forall_mem_cons.2 ⟨subd7_4_224, List.forall_mem_cons.2 ⟨subd7_4_225, List.forall_mem_cons.2 ⟨subd7_4_226, List.forall_mem_cons.2 ⟨subd7_4_227, List.forall_mem_cons.2 ⟨subd7_4_228, List.forall_mem_cons.2 ⟨subd7_4_229, List.forall_mem_cons.2 ⟨subd7_4_230, List.forall_mem_cons.2 ⟨subd7_4_231, List.forall_mem_cons.2 ⟨subd7_4_232, List.forall_mem_cons.2 ⟨subd7_4_233, List.forall_mem_cons.2 ⟨subd7_4_234, List.forall_mem_cons.2 ⟨subd7_4_235, List.forall_mem_cons.2 ⟨subd7_4_236, List.forall_mem_cons.2 ⟨subd7_4_237, List.forall_mem_cons.2 ⟨subd7_4_238, List.forall_mem_cons.2 ⟨subd7_4_239, List.forall_mem_cons.2 ⟨subd7_4_240, List.forall_mem_cons.2 ⟨subd7_4_241, List.forall_mem_cons.2 ⟨subd7_4_242, List.forall_mem_cons.2 ⟨subd7_4_243, List.forall_mem_cons.2 ⟨subd7_4_244, List.forall_mem_cons.2 ⟨subd7_4_245, List.forall_mem_cons.2 ⟨subd7_4_246, List.forall_mem_cons.2 ⟨subd7_4_247, List.forall_mem_cons.2 ⟨subd7_4_248, List.forall_mem_cons.2 ⟨subd7_4_249, List.forall_mem_cons.2 ⟨subd7_4_250, List.forall_mem_cons.2 ⟨subd7_4_251, List.forall_mem_cons.2 ⟨subd7_4_252, List.forall_mem_cons.2 ⟨subd7_4_253, List.forall_mem_cons.2 ⟨subd7_4_254, List.forall_mem_cons.2 ⟨subd7_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_256 : subd7_4 [0, 0, -7] = true := by decide +kernel
theorem subd7_4_257 : subd7_4 [0, 0, -6] = true := by decide +kernel
theorem subd7_4_258 : subd7_4 [0, 0, -5] = true := by decide +kernel
theorem subd7_4_259 : subd7_4 [0, 0, -4] = true := by decide +kernel
theorem subd7_4_260 : subd7_4 [0, 0, -3] = true := by decide +kernel
theorem subd7_4_261 : subd7_4 [0, 0, -2] = true := by decide +kernel
theorem subd7_4_262 : subd7_4 [0, 0, -1] = true := by decide +kernel
theorem subd7_4_263 : subd7_4 [0, 0, 0] = true := by decide +kernel
theorem subd7_4_264 : subd7_4 [0, 0, 1] = true := by decide +kernel
theorem subd7_4_265 : subd7_4 [0, 0, 2] = true := by decide +kernel
theorem subd7_4_266 : subd7_4 [0, 0, 3] = true := by decide +kernel
theorem subd7_4_267 : subd7_4 [0, 0, 4] = true := by decide +kernel
theorem subd7_4_268 : subd7_4 [0, 0, 5] = true := by decide +kernel
theorem subd7_4_269 : subd7_4 [0, 0, 6] = true := by decide +kernel
theorem subd7_4_270 : subd7_4 [0, 0, 7] = true := by decide +kernel
theorem subd7_4_271 : subd7_4 [0, 1, -8] = true := by decide +kernel
theorem subd7_4_272 : subd7_4 [0, 1, -7] = true := by decide +kernel
theorem subd7_4_273 : subd7_4 [0, 1, -6] = true := by decide +kernel
theorem subd7_4_274 : subd7_4 [0, 1, -5] = true := by decide +kernel
theorem subd7_4_275 : subd7_4 [0, 1, -4] = true := by decide +kernel
theorem subd7_4_276 : subd7_4 [0, 1, -3] = true := by decide +kernel
theorem subd7_4_277 : subd7_4 [0, 1, -2] = true := by decide +kernel
theorem subd7_4_278 : subd7_4 [0, 1, -1] = true := by decide +kernel
theorem subd7_4_279 : subd7_4 [0, 1, 0] = true := by decide +kernel
theorem subd7_4_280 : subd7_4 [0, 1, 1] = true := by decide +kernel
theorem subd7_4_281 : subd7_4 [0, 1, 2] = true := by decide +kernel
theorem subd7_4_282 : subd7_4 [0, 1, 3] = true := by decide +kernel
theorem subd7_4_283 : subd7_4 [0, 1, 4] = true := by decide +kernel
theorem subd7_4_284 : subd7_4 [0, 1, 5] = true := by decide +kernel
theorem subd7_4_285 : subd7_4 [0, 1, 6] = true := by decide +kernel
theorem subd7_4_286 : subd7_4 [0, 1, 7] = true := by decide +kernel
theorem subd7_4_287 : subd7_4 [0, 2, -8] = true := by decide +kernel
theorem sbd7_4_8 : ∀ q ∈ blkd7_4_8, subd7_4 q = true := by
  unfold blkd7_4_8
  exact List.forall_mem_cons.2 ⟨subd7_4_256, List.forall_mem_cons.2 ⟨subd7_4_257, List.forall_mem_cons.2 ⟨subd7_4_258, List.forall_mem_cons.2 ⟨subd7_4_259, List.forall_mem_cons.2 ⟨subd7_4_260, List.forall_mem_cons.2 ⟨subd7_4_261, List.forall_mem_cons.2 ⟨subd7_4_262, List.forall_mem_cons.2 ⟨subd7_4_263, List.forall_mem_cons.2 ⟨subd7_4_264, List.forall_mem_cons.2 ⟨subd7_4_265, List.forall_mem_cons.2 ⟨subd7_4_266, List.forall_mem_cons.2 ⟨subd7_4_267, List.forall_mem_cons.2 ⟨subd7_4_268, List.forall_mem_cons.2 ⟨subd7_4_269, List.forall_mem_cons.2 ⟨subd7_4_270, List.forall_mem_cons.2 ⟨subd7_4_271, List.forall_mem_cons.2 ⟨subd7_4_272, List.forall_mem_cons.2 ⟨subd7_4_273, List.forall_mem_cons.2 ⟨subd7_4_274, List.forall_mem_cons.2 ⟨subd7_4_275, List.forall_mem_cons.2 ⟨subd7_4_276, List.forall_mem_cons.2 ⟨subd7_4_277, List.forall_mem_cons.2 ⟨subd7_4_278, List.forall_mem_cons.2 ⟨subd7_4_279, List.forall_mem_cons.2 ⟨subd7_4_280, List.forall_mem_cons.2 ⟨subd7_4_281, List.forall_mem_cons.2 ⟨subd7_4_282, List.forall_mem_cons.2 ⟨subd7_4_283, List.forall_mem_cons.2 ⟨subd7_4_284, List.forall_mem_cons.2 ⟨subd7_4_285, List.forall_mem_cons.2 ⟨subd7_4_286, List.forall_mem_cons.2 ⟨subd7_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_288 : subd7_4 [0, 2, -7] = true := by decide +kernel
theorem subd7_4_289 : subd7_4 [0, 2, -6] = true := by decide +kernel
theorem subd7_4_290 : subd7_4 [0, 2, -5] = true := by decide +kernel
theorem subd7_4_291 : subd7_4 [0, 2, -4] = true := by decide +kernel
theorem subd7_4_292 : subd7_4 [0, 2, -3] = true := by decide +kernel
theorem subd7_4_293 : subd7_4 [0, 2, -2] = true := by decide +kernel
theorem subd7_4_294 : subd7_4 [0, 2, -1] = true := by decide +kernel
theorem subd7_4_295 : subd7_4 [0, 2, 0] = true := by decide +kernel
theorem subd7_4_296 : subd7_4 [0, 2, 1] = true := by decide +kernel
theorem subd7_4_297 : subd7_4 [0, 2, 2] = true := by decide +kernel
theorem subd7_4_298 : subd7_4 [0, 2, 3] = true := by decide +kernel
theorem subd7_4_299 : subd7_4 [0, 2, 4] = true := by decide +kernel
theorem subd7_4_300 : subd7_4 [0, 2, 5] = true := by decide +kernel
theorem subd7_4_301 : subd7_4 [0, 2, 6] = true := by decide +kernel
theorem subd7_4_302 : subd7_4 [0, 3, -7] = true := by decide +kernel
theorem subd7_4_303 : subd7_4 [0, 3, -6] = true := by decide +kernel
theorem subd7_4_304 : subd7_4 [0, 3, -5] = true := by decide +kernel
theorem subd7_4_305 : subd7_4 [0, 3, -4] = true := by decide +kernel
theorem subd7_4_306 : subd7_4 [0, 3, -3] = true := by decide +kernel
theorem subd7_4_307 : subd7_4 [0, 3, -2] = true := by decide +kernel
theorem subd7_4_308 : subd7_4 [0, 3, -1] = true := by decide +kernel
theorem subd7_4_309 : subd7_4 [0, 3, 0] = true := by decide +kernel
theorem subd7_4_310 : subd7_4 [0, 3, 1] = true := by decide +kernel
theorem subd7_4_311 : subd7_4 [0, 3, 2] = true := by decide +kernel
theorem subd7_4_312 : subd7_4 [0, 3, 3] = true := by decide +kernel
theorem subd7_4_313 : subd7_4 [0, 3, 4] = true := by decide +kernel
theorem subd7_4_314 : subd7_4 [0, 3, 5] = true := by decide +kernel
theorem subd7_4_315 : subd7_4 [0, 4] = true := by decide +kernel
theorem subd7_4_316 : subd7_4 [0, 5] = true := by decide +kernel
theorem subd7_4_317 : subd7_4 [1, -6] = true := by decide +kernel
theorem subd7_4_318 : subd7_4 [1, -5] = true := by decide +kernel
theorem subd7_4_319 : subd7_4 [1, -4] = true := by decide +kernel
theorem sbd7_4_9 : ∀ q ∈ blkd7_4_9, subd7_4 q = true := by
  unfold blkd7_4_9
  exact List.forall_mem_cons.2 ⟨subd7_4_288, List.forall_mem_cons.2 ⟨subd7_4_289, List.forall_mem_cons.2 ⟨subd7_4_290, List.forall_mem_cons.2 ⟨subd7_4_291, List.forall_mem_cons.2 ⟨subd7_4_292, List.forall_mem_cons.2 ⟨subd7_4_293, List.forall_mem_cons.2 ⟨subd7_4_294, List.forall_mem_cons.2 ⟨subd7_4_295, List.forall_mem_cons.2 ⟨subd7_4_296, List.forall_mem_cons.2 ⟨subd7_4_297, List.forall_mem_cons.2 ⟨subd7_4_298, List.forall_mem_cons.2 ⟨subd7_4_299, List.forall_mem_cons.2 ⟨subd7_4_300, List.forall_mem_cons.2 ⟨subd7_4_301, List.forall_mem_cons.2 ⟨subd7_4_302, List.forall_mem_cons.2 ⟨subd7_4_303, List.forall_mem_cons.2 ⟨subd7_4_304, List.forall_mem_cons.2 ⟨subd7_4_305, List.forall_mem_cons.2 ⟨subd7_4_306, List.forall_mem_cons.2 ⟨subd7_4_307, List.forall_mem_cons.2 ⟨subd7_4_308, List.forall_mem_cons.2 ⟨subd7_4_309, List.forall_mem_cons.2 ⟨subd7_4_310, List.forall_mem_cons.2 ⟨subd7_4_311, List.forall_mem_cons.2 ⟨subd7_4_312, List.forall_mem_cons.2 ⟨subd7_4_313, List.forall_mem_cons.2 ⟨subd7_4_314, List.forall_mem_cons.2 ⟨subd7_4_315, List.forall_mem_cons.2 ⟨subd7_4_316, List.forall_mem_cons.2 ⟨subd7_4_317, List.forall_mem_cons.2 ⟨subd7_4_318, List.forall_mem_cons.2 ⟨subd7_4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_320 : subd7_4 [1, -3] = true := by decide +kernel
theorem subd7_4_321 : subd7_4 [1, -2, -7] = true := by decide +kernel
theorem subd7_4_322 : subd7_4 [1, -2, -6] = true := by decide +kernel
theorem subd7_4_323 : subd7_4 [1, -2, -5] = true := by decide +kernel
theorem subd7_4_324 : subd7_4 [1, -2, -4] = true := by decide +kernel
theorem subd7_4_325 : subd7_4 [1, -2, -3] = true := by decide +kernel
theorem subd7_4_326 : subd7_4 [1, -2, -2] = true := by decide +kernel
theorem subd7_4_327 : subd7_4 [1, -2, -1] = true := by decide +kernel
theorem subd7_4_328 : subd7_4 [1, -2, 0] = true := by decide +kernel
theorem subd7_4_329 : subd7_4 [1, -2, 1] = true := by decide +kernel
theorem subd7_4_330 : subd7_4 [1, -2, 2] = true := by decide +kernel
theorem subd7_4_331 : subd7_4 [1, -2, 3] = true := by decide +kernel
theorem subd7_4_332 : subd7_4 [1, -2, 4] = true := by decide +kernel
theorem subd7_4_333 : subd7_4 [1, -2, 5] = true := by decide +kernel
theorem subd7_4_334 : subd7_4 [1, -2, 6] = true := by decide +kernel
theorem subd7_4_335 : subd7_4 [1, -2, 7] = true := by decide +kernel
theorem subd7_4_336 : subd7_4 [1, -1, -8] = true := by decide +kernel
theorem subd7_4_337 : subd7_4 [1, -1, -7] = true := by decide +kernel
theorem subd7_4_338 : subd7_4 [1, -1, -6] = true := by decide +kernel
theorem subd7_4_339 : subd7_4 [1, -1, -5] = true := by decide +kernel
theorem subd7_4_340 : subd7_4 [1, -1, -4] = true := by decide +kernel
theorem subd7_4_341 : subd7_4 [1, -1, -3] = true := by decide +kernel
theorem subd7_4_342 : subd7_4 [1, -1, -2] = true := by decide +kernel
theorem subd7_4_343 : subd7_4 [1, -1, -1] = true := by decide +kernel
theorem subd7_4_344 : subd7_4 [1, -1, 0] = true := by decide +kernel
theorem subd7_4_345 : subd7_4 [1, -1, 1] = true := by decide +kernel
theorem subd7_4_346 : subd7_4 [1, -1, 2] = true := by decide +kernel
theorem subd7_4_347 : subd7_4 [1, -1, 3] = true := by decide +kernel
theorem subd7_4_348 : subd7_4 [1, -1, 4] = true := by decide +kernel
theorem subd7_4_349 : subd7_4 [1, -1, 5] = true := by decide +kernel
theorem subd7_4_350 : subd7_4 [1, -1, 6] = true := by decide +kernel
theorem subd7_4_351 : subd7_4 [1, -1, 7] = true := by decide +kernel
theorem sbd7_4_10 : ∀ q ∈ blkd7_4_10, subd7_4 q = true := by
  unfold blkd7_4_10
  exact List.forall_mem_cons.2 ⟨subd7_4_320, List.forall_mem_cons.2 ⟨subd7_4_321, List.forall_mem_cons.2 ⟨subd7_4_322, List.forall_mem_cons.2 ⟨subd7_4_323, List.forall_mem_cons.2 ⟨subd7_4_324, List.forall_mem_cons.2 ⟨subd7_4_325, List.forall_mem_cons.2 ⟨subd7_4_326, List.forall_mem_cons.2 ⟨subd7_4_327, List.forall_mem_cons.2 ⟨subd7_4_328, List.forall_mem_cons.2 ⟨subd7_4_329, List.forall_mem_cons.2 ⟨subd7_4_330, List.forall_mem_cons.2 ⟨subd7_4_331, List.forall_mem_cons.2 ⟨subd7_4_332, List.forall_mem_cons.2 ⟨subd7_4_333, List.forall_mem_cons.2 ⟨subd7_4_334, List.forall_mem_cons.2 ⟨subd7_4_335, List.forall_mem_cons.2 ⟨subd7_4_336, List.forall_mem_cons.2 ⟨subd7_4_337, List.forall_mem_cons.2 ⟨subd7_4_338, List.forall_mem_cons.2 ⟨subd7_4_339, List.forall_mem_cons.2 ⟨subd7_4_340, List.forall_mem_cons.2 ⟨subd7_4_341, List.forall_mem_cons.2 ⟨subd7_4_342, List.forall_mem_cons.2 ⟨subd7_4_343, List.forall_mem_cons.2 ⟨subd7_4_344, List.forall_mem_cons.2 ⟨subd7_4_345, List.forall_mem_cons.2 ⟨subd7_4_346, List.forall_mem_cons.2 ⟨subd7_4_347, List.forall_mem_cons.2 ⟨subd7_4_348, List.forall_mem_cons.2 ⟨subd7_4_349, List.forall_mem_cons.2 ⟨subd7_4_350, List.forall_mem_cons.2 ⟨subd7_4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_352 : subd7_4 [1, 0, -8] = true := by decide +kernel
theorem subd7_4_353 : subd7_4 [1, 0, -7] = true := by decide +kernel
theorem subd7_4_354 : subd7_4 [1, 0, -6] = true := by decide +kernel
theorem subd7_4_355 : subd7_4 [1, 0, -5] = true := by decide +kernel
theorem subd7_4_356 : subd7_4 [1, 0, -4] = true := by decide +kernel
theorem subd7_4_357 : subd7_4 [1, 0, -3] = true := by decide +kernel
theorem subd7_4_358 : subd7_4 [1, 0, -2] = true := by decide +kernel
theorem subd7_4_359 : subd7_4 [1, 0, -1] = true := by decide +kernel
theorem subd7_4_360 : subd7_4 [1, 0, 0] = true := by decide +kernel
theorem subd7_4_361 : subd7_4 [1, 0, 1] = true := by decide +kernel
theorem subd7_4_362 : subd7_4 [1, 0, 2] = true := by decide +kernel
theorem subd7_4_363 : subd7_4 [1, 0, 3] = true := by decide +kernel
theorem subd7_4_364 : subd7_4 [1, 0, 4] = true := by decide +kernel
theorem subd7_4_365 : subd7_4 [1, 0, 5] = true := by decide +kernel
theorem subd7_4_366 : subd7_4 [1, 0, 6] = true := by decide +kernel
theorem subd7_4_367 : subd7_4 [1, 0, 7] = true := by decide +kernel
theorem subd7_4_368 : subd7_4 [1, 1, -8] = true := by decide +kernel
theorem subd7_4_369 : subd7_4 [1, 1, -7] = true := by decide +kernel
theorem subd7_4_370 : subd7_4 [1, 1, -6] = true := by decide +kernel
theorem subd7_4_371 : subd7_4 [1, 1, -5] = true := by decide +kernel
theorem subd7_4_372 : subd7_4 [1, 1, -4] = true := by decide +kernel
theorem subd7_4_373 : subd7_4 [1, 1, -3] = true := by decide +kernel
theorem subd7_4_374 : subd7_4 [1, 1, -2] = true := by decide +kernel
theorem subd7_4_375 : subd7_4 [1, 1, -1] = true := by decide +kernel
theorem subd7_4_376 : subd7_4 [1, 1, 0] = true := by decide +kernel
theorem subd7_4_377 : subd7_4 [1, 1, 1] = true := by decide +kernel
theorem subd7_4_378 : subd7_4 [1, 1, 2] = true := by decide +kernel
theorem subd7_4_379 : subd7_4 [1, 1, 3] = true := by decide +kernel
theorem subd7_4_380 : subd7_4 [1, 1, 4] = true := by decide +kernel
theorem subd7_4_381 : subd7_4 [1, 1, 5] = true := by decide +kernel
theorem subd7_4_382 : subd7_4 [1, 1, 6] = true := by decide +kernel
theorem subd7_4_383 : subd7_4 [1, 1, 7] = true := by decide +kernel
theorem sbd7_4_11 : ∀ q ∈ blkd7_4_11, subd7_4 q = true := by
  unfold blkd7_4_11
  exact List.forall_mem_cons.2 ⟨subd7_4_352, List.forall_mem_cons.2 ⟨subd7_4_353, List.forall_mem_cons.2 ⟨subd7_4_354, List.forall_mem_cons.2 ⟨subd7_4_355, List.forall_mem_cons.2 ⟨subd7_4_356, List.forall_mem_cons.2 ⟨subd7_4_357, List.forall_mem_cons.2 ⟨subd7_4_358, List.forall_mem_cons.2 ⟨subd7_4_359, List.forall_mem_cons.2 ⟨subd7_4_360, List.forall_mem_cons.2 ⟨subd7_4_361, List.forall_mem_cons.2 ⟨subd7_4_362, List.forall_mem_cons.2 ⟨subd7_4_363, List.forall_mem_cons.2 ⟨subd7_4_364, List.forall_mem_cons.2 ⟨subd7_4_365, List.forall_mem_cons.2 ⟨subd7_4_366, List.forall_mem_cons.2 ⟨subd7_4_367, List.forall_mem_cons.2 ⟨subd7_4_368, List.forall_mem_cons.2 ⟨subd7_4_369, List.forall_mem_cons.2 ⟨subd7_4_370, List.forall_mem_cons.2 ⟨subd7_4_371, List.forall_mem_cons.2 ⟨subd7_4_372, List.forall_mem_cons.2 ⟨subd7_4_373, List.forall_mem_cons.2 ⟨subd7_4_374, List.forall_mem_cons.2 ⟨subd7_4_375, List.forall_mem_cons.2 ⟨subd7_4_376, List.forall_mem_cons.2 ⟨subd7_4_377, List.forall_mem_cons.2 ⟨subd7_4_378, List.forall_mem_cons.2 ⟨subd7_4_379, List.forall_mem_cons.2 ⟨subd7_4_380, List.forall_mem_cons.2 ⟨subd7_4_381, List.forall_mem_cons.2 ⟨subd7_4_382, List.forall_mem_cons.2 ⟨subd7_4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_384 : subd7_4 [1, 2, -8] = true := by decide +kernel
theorem subd7_4_385 : subd7_4 [1, 2, -7] = true := by decide +kernel
theorem subd7_4_386 : subd7_4 [1, 2, -6] = true := by decide +kernel
theorem subd7_4_387 : subd7_4 [1, 2, -5] = true := by decide +kernel
theorem subd7_4_388 : subd7_4 [1, 2, -4] = true := by decide +kernel
theorem subd7_4_389 : subd7_4 [1, 2, -3] = true := by decide +kernel
theorem subd7_4_390 : subd7_4 [1, 2, -2] = true := by decide +kernel
theorem subd7_4_391 : subd7_4 [1, 2, -1] = true := by decide +kernel
theorem subd7_4_392 : subd7_4 [1, 2, 0] = true := by decide +kernel
theorem subd7_4_393 : subd7_4 [1, 2, 1] = true := by decide +kernel
theorem subd7_4_394 : subd7_4 [1, 2, 2] = true := by decide +kernel
theorem subd7_4_395 : subd7_4 [1, 2, 3] = true := by decide +kernel
theorem subd7_4_396 : subd7_4 [1, 2, 4] = true := by decide +kernel
theorem subd7_4_397 : subd7_4 [1, 2, 5] = true := by decide +kernel
theorem subd7_4_398 : subd7_4 [1, 2, 6] = true := by decide +kernel
theorem subd7_4_399 : subd7_4 [1, 3] = true := by decide +kernel
theorem subd7_4_400 : subd7_4 [1, 4] = true := by decide +kernel
theorem subd7_4_401 : subd7_4 [1, 5] = true := by decide +kernel
theorem subd7_4_402 : subd7_4 [2, -5] = true := by decide +kernel
theorem subd7_4_403 : subd7_4 [2, -4] = true := by decide +kernel
theorem subd7_4_404 : subd7_4 [2, -3] = true := by decide +kernel
theorem subd7_4_405 : subd7_4 [2, -2, -7] = true := by decide +kernel
theorem subd7_4_406 : subd7_4 [2, -2, -6] = true := by decide +kernel
theorem subd7_4_407 : subd7_4 [2, -2, -5] = true := by decide +kernel
theorem subd7_4_408 : subd7_4 [2, -2, -4] = true := by decide +kernel
theorem subd7_4_409 : subd7_4 [2, -2, -3] = true := by decide +kernel
theorem subd7_4_410 : subd7_4 [2, -2, -2] = true := by decide +kernel
theorem subd7_4_411 : subd7_4 [2, -2, -1] = true := by decide +kernel
theorem subd7_4_412 : subd7_4 [2, -2, 0] = true := by decide +kernel
theorem subd7_4_413 : subd7_4 [2, -2, 1] = true := by decide +kernel
theorem subd7_4_414 : subd7_4 [2, -2, 2] = true := by decide +kernel
theorem subd7_4_415 : subd7_4 [2, -2, 3] = true := by decide +kernel
theorem sbd7_4_12 : ∀ q ∈ blkd7_4_12, subd7_4 q = true := by
  unfold blkd7_4_12
  exact List.forall_mem_cons.2 ⟨subd7_4_384, List.forall_mem_cons.2 ⟨subd7_4_385, List.forall_mem_cons.2 ⟨subd7_4_386, List.forall_mem_cons.2 ⟨subd7_4_387, List.forall_mem_cons.2 ⟨subd7_4_388, List.forall_mem_cons.2 ⟨subd7_4_389, List.forall_mem_cons.2 ⟨subd7_4_390, List.forall_mem_cons.2 ⟨subd7_4_391, List.forall_mem_cons.2 ⟨subd7_4_392, List.forall_mem_cons.2 ⟨subd7_4_393, List.forall_mem_cons.2 ⟨subd7_4_394, List.forall_mem_cons.2 ⟨subd7_4_395, List.forall_mem_cons.2 ⟨subd7_4_396, List.forall_mem_cons.2 ⟨subd7_4_397, List.forall_mem_cons.2 ⟨subd7_4_398, List.forall_mem_cons.2 ⟨subd7_4_399, List.forall_mem_cons.2 ⟨subd7_4_400, List.forall_mem_cons.2 ⟨subd7_4_401, List.forall_mem_cons.2 ⟨subd7_4_402, List.forall_mem_cons.2 ⟨subd7_4_403, List.forall_mem_cons.2 ⟨subd7_4_404, List.forall_mem_cons.2 ⟨subd7_4_405, List.forall_mem_cons.2 ⟨subd7_4_406, List.forall_mem_cons.2 ⟨subd7_4_407, List.forall_mem_cons.2 ⟨subd7_4_408, List.forall_mem_cons.2 ⟨subd7_4_409, List.forall_mem_cons.2 ⟨subd7_4_410, List.forall_mem_cons.2 ⟨subd7_4_411, List.forall_mem_cons.2 ⟨subd7_4_412, List.forall_mem_cons.2 ⟨subd7_4_413, List.forall_mem_cons.2 ⟨subd7_4_414, List.forall_mem_cons.2 ⟨subd7_4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_416 : subd7_4 [2, -2, 4] = true := by decide +kernel
theorem subd7_4_417 : subd7_4 [2, -2, 5] = true := by decide +kernel
theorem subd7_4_418 : subd7_4 [2, -2, 6] = true := by decide +kernel
theorem subd7_4_419 : subd7_4 [2, -1, -7] = true := by decide +kernel
theorem subd7_4_420 : subd7_4 [2, -1, -6] = true := by decide +kernel
theorem subd7_4_421 : subd7_4 [2, -1, -5] = true := by decide +kernel
theorem subd7_4_422 : subd7_4 [2, -1, -4] = true := by decide +kernel
theorem subd7_4_423 : subd7_4 [2, -1, -3] = true := by decide +kernel
theorem subd7_4_424 : subd7_4 [2, -1, -2] = true := by decide +kernel
theorem subd7_4_425 : subd7_4 [2, -1, -1] = true := by decide +kernel
theorem subd7_4_426 : subd7_4 [2, -1, 0] = true := by decide +kernel
theorem subd7_4_427 : subd7_4 [2, -1, 1] = true := by decide +kernel
theorem subd7_4_428 : subd7_4 [2, -1, 2] = true := by decide +kernel
theorem subd7_4_429 : subd7_4 [2, -1, 3] = true := by decide +kernel
theorem subd7_4_430 : subd7_4 [2, -1, 4] = true := by decide +kernel
theorem subd7_4_431 : subd7_4 [2, -1, 5] = true := by decide +kernel
theorem subd7_4_432 : subd7_4 [2, -1, 6] = true := by decide +kernel
theorem subd7_4_433 : subd7_4 [2, 0, -8] = true := by decide +kernel
theorem subd7_4_434 : subd7_4 [2, 0, -7] = true := by decide +kernel
theorem subd7_4_435 : subd7_4 [2, 0, -6] = true := by decide +kernel
theorem subd7_4_436 : subd7_4 [2, 0, -5] = true := by decide +kernel
theorem subd7_4_437 : subd7_4 [2, 0, -4] = true := by decide +kernel
theorem subd7_4_438 : subd7_4 [2, 0, -3] = true := by decide +kernel
theorem subd7_4_439 : subd7_4 [2, 0, -2] = true := by decide +kernel
theorem subd7_4_440 : subd7_4 [2, 0, -1] = true := by decide +kernel
theorem subd7_4_441 : subd7_4 [2, 0, 0] = true := by decide +kernel
theorem subd7_4_442 : subd7_4 [2, 0, 1] = true := by decide +kernel
theorem subd7_4_443 : subd7_4 [2, 0, 2] = true := by decide +kernel
theorem subd7_4_444 : subd7_4 [2, 0, 3] = true := by decide +kernel
theorem subd7_4_445 : subd7_4 [2, 0, 4] = true := by decide +kernel
theorem subd7_4_446 : subd7_4 [2, 0, 5] = true := by decide +kernel
theorem subd7_4_447 : subd7_4 [2, 0, 6] = true := by decide +kernel
theorem sbd7_4_13 : ∀ q ∈ blkd7_4_13, subd7_4 q = true := by
  unfold blkd7_4_13
  exact List.forall_mem_cons.2 ⟨subd7_4_416, List.forall_mem_cons.2 ⟨subd7_4_417, List.forall_mem_cons.2 ⟨subd7_4_418, List.forall_mem_cons.2 ⟨subd7_4_419, List.forall_mem_cons.2 ⟨subd7_4_420, List.forall_mem_cons.2 ⟨subd7_4_421, List.forall_mem_cons.2 ⟨subd7_4_422, List.forall_mem_cons.2 ⟨subd7_4_423, List.forall_mem_cons.2 ⟨subd7_4_424, List.forall_mem_cons.2 ⟨subd7_4_425, List.forall_mem_cons.2 ⟨subd7_4_426, List.forall_mem_cons.2 ⟨subd7_4_427, List.forall_mem_cons.2 ⟨subd7_4_428, List.forall_mem_cons.2 ⟨subd7_4_429, List.forall_mem_cons.2 ⟨subd7_4_430, List.forall_mem_cons.2 ⟨subd7_4_431, List.forall_mem_cons.2 ⟨subd7_4_432, List.forall_mem_cons.2 ⟨subd7_4_433, List.forall_mem_cons.2 ⟨subd7_4_434, List.forall_mem_cons.2 ⟨subd7_4_435, List.forall_mem_cons.2 ⟨subd7_4_436, List.forall_mem_cons.2 ⟨subd7_4_437, List.forall_mem_cons.2 ⟨subd7_4_438, List.forall_mem_cons.2 ⟨subd7_4_439, List.forall_mem_cons.2 ⟨subd7_4_440, List.forall_mem_cons.2 ⟨subd7_4_441, List.forall_mem_cons.2 ⟨subd7_4_442, List.forall_mem_cons.2 ⟨subd7_4_443, List.forall_mem_cons.2 ⟨subd7_4_444, List.forall_mem_cons.2 ⟨subd7_4_445, List.forall_mem_cons.2 ⟨subd7_4_446, List.forall_mem_cons.2 ⟨subd7_4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
