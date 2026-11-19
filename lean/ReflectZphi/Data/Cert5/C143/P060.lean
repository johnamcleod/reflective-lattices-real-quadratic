import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_3_32 : subd18_3 [-4, 2] = true := by decide +kernel
theorem subd18_3_33 : subd18_3 [-4, 3] = true := by decide +kernel
theorem subd18_3_34 : subd18_3 [-4, 4] = true := by decide +kernel
theorem subd18_3_35 : subd18_3 [-4, 5] = true := by decide +kernel
theorem subd18_3_36 : subd18_3 [-4, 6] = true := by decide +kernel
theorem subd18_3_37 : subd18_3 [-3, -7] = true := by decide +kernel
theorem subd18_3_38 : subd18_3 [-3, -6] = true := by decide +kernel
theorem subd18_3_39 : subd18_3 [-3, -5] = true := by decide +kernel
theorem subd18_3_40 : subd18_3 [-3, -4] = true := by decide +kernel
theorem subd18_3_41 : subd18_3 [-3, -3] = true := by decide +kernel
theorem subd18_3_42 : subd18_3 [-3, -2] = true := by decide +kernel
theorem subd18_3_43 : subd18_3 [-3, -1] = true := by decide +kernel
theorem subd18_3_44 : subd18_3 [-3, 0] = true := by decide +kernel
theorem subd18_3_45 : subd18_3 [-3, 1] = true := by decide +kernel
theorem subd18_3_46 : subd18_3 [-3, 2] = true := by decide +kernel
theorem subd18_3_47 : subd18_3 [-3, 3] = true := by decide +kernel
theorem subd18_3_48 : subd18_3 [-3, 4] = true := by decide +kernel
theorem subd18_3_49 : subd18_3 [-3, 5] = true := by decide +kernel
theorem subd18_3_50 : subd18_3 [-3, 6] = true := by decide +kernel
theorem subd18_3_51 : subd18_3 [-2, -8] = true := by decide +kernel
theorem subd18_3_52 : subd18_3 [-2, -7] = true := by decide +kernel
theorem subd18_3_53 : subd18_3 [-2, -6] = true := by decide +kernel
theorem subd18_3_54 : subd18_3 [-2, -5] = true := by decide +kernel
theorem subd18_3_55 : subd18_3 [-2, -4] = true := by decide +kernel
theorem subd18_3_56 : subd18_3 [-2, -3] = true := by decide +kernel
theorem subd18_3_57 : subd18_3 [-2, -2, -5] = true := by decide +kernel
theorem subd18_3_58 : subd18_3 [-2, -2, -4] = true := by decide +kernel
theorem subd18_3_59 : subd18_3 [-2, -2, -3] = true := by decide +kernel
theorem subd18_3_60 : subd18_3 [-2, -2, -2] = true := by decide +kernel
theorem subd18_3_61 : subd18_3 [-2, -2, -1] = true := by decide +kernel
theorem subd18_3_62 : subd18_3 [-2, -2, 0] = true := by decide +kernel
theorem subd18_3_63 : subd18_3 [-2, -2, 1] = true := by decide +kernel
theorem sbd18_3_1 : ∀ q ∈ blkd18_3_1, subd18_3 q = true := by
  unfold blkd18_3_1
  exact List.forall_mem_cons.2 ⟨subd18_3_32, List.forall_mem_cons.2 ⟨subd18_3_33, List.forall_mem_cons.2 ⟨subd18_3_34, List.forall_mem_cons.2 ⟨subd18_3_35, List.forall_mem_cons.2 ⟨subd18_3_36, List.forall_mem_cons.2 ⟨subd18_3_37, List.forall_mem_cons.2 ⟨subd18_3_38, List.forall_mem_cons.2 ⟨subd18_3_39, List.forall_mem_cons.2 ⟨subd18_3_40, List.forall_mem_cons.2 ⟨subd18_3_41, List.forall_mem_cons.2 ⟨subd18_3_42, List.forall_mem_cons.2 ⟨subd18_3_43, List.forall_mem_cons.2 ⟨subd18_3_44, List.forall_mem_cons.2 ⟨subd18_3_45, List.forall_mem_cons.2 ⟨subd18_3_46, List.forall_mem_cons.2 ⟨subd18_3_47, List.forall_mem_cons.2 ⟨subd18_3_48, List.forall_mem_cons.2 ⟨subd18_3_49, List.forall_mem_cons.2 ⟨subd18_3_50, List.forall_mem_cons.2 ⟨subd18_3_51, List.forall_mem_cons.2 ⟨subd18_3_52, List.forall_mem_cons.2 ⟨subd18_3_53, List.forall_mem_cons.2 ⟨subd18_3_54, List.forall_mem_cons.2 ⟨subd18_3_55, List.forall_mem_cons.2 ⟨subd18_3_56, List.forall_mem_cons.2 ⟨subd18_3_57, List.forall_mem_cons.2 ⟨subd18_3_58, List.forall_mem_cons.2 ⟨subd18_3_59, List.forall_mem_cons.2 ⟨subd18_3_60, List.forall_mem_cons.2 ⟨subd18_3_61, List.forall_mem_cons.2 ⟨subd18_3_62, List.forall_mem_cons.2 ⟨subd18_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_64 : subd18_3 [-2, -2, 2] = true := by decide +kernel
theorem subd18_3_65 : subd18_3 [-2, -2, 3] = true := by decide +kernel
theorem subd18_3_66 : subd18_3 [-2, -2, 4] = true := by decide +kernel
theorem subd18_3_67 : subd18_3 [-2, -2, 5] = true := by decide +kernel
theorem subd18_3_68 : subd18_3 [-2, -2, 6] = true := by decide +kernel
theorem subd18_3_69 : subd18_3 [-2, -2, 7] = true := by decide +kernel
theorem subd18_3_70 : subd18_3 [-2, -1, -6] = true := by decide +kernel
theorem subd18_3_71 : subd18_3 [-2, -1, -5] = true := by decide +kernel
theorem subd18_3_72 : subd18_3 [-2, -1, -4] = true := by decide +kernel
theorem subd18_3_73 : subd18_3 [-2, -1, -3] = true := by decide +kernel
theorem subd18_3_74 : subd18_3 [-2, -1, -2] = true := by decide +kernel
theorem subd18_3_75 : subd18_3 [-2, -1, -1] = true := by decide +kernel
theorem subd18_3_76 : subd18_3 [-2, -1, 0] = true := by decide +kernel
theorem subd18_3_77 : subd18_3 [-2, -1, 1] = true := by decide +kernel
theorem subd18_3_78 : subd18_3 [-2, -1, 2] = true := by decide +kernel
theorem subd18_3_79 : subd18_3 [-2, -1, 3] = true := by decide +kernel
theorem subd18_3_80 : subd18_3 [-2, -1, 4] = true := by decide +kernel
theorem subd18_3_81 : subd18_3 [-2, -1, 5] = true := by decide +kernel
theorem subd18_3_82 : subd18_3 [-2, -1, 6] = true := by decide +kernel
theorem subd18_3_83 : subd18_3 [-2, -1, 7] = true := by decide +kernel
theorem subd18_3_84 : subd18_3 [-2, 0, -6] = true := by decide +kernel
theorem subd18_3_85 : subd18_3 [-2, 0, -5] = true := by decide +kernel
theorem subd18_3_86 : subd18_3 [-2, 0, -4] = true := by decide +kernel
theorem subd18_3_87 : subd18_3 [-2, 0, -3] = true := by decide +kernel
theorem subd18_3_88 : subd18_3 [-2, 0, -2] = true := by decide +kernel
theorem subd18_3_89 : subd18_3 [-2, 0, -1] = true := by decide +kernel
theorem subd18_3_90 : subd18_3 [-2, 0, 0] = true := by decide +kernel
theorem subd18_3_91 : subd18_3 [-2, 0, 1] = true := by decide +kernel
theorem subd18_3_92 : subd18_3 [-2, 0, 2] = true := by decide +kernel
theorem subd18_3_93 : subd18_3 [-2, 0, 3] = true := by decide +kernel
theorem subd18_3_94 : subd18_3 [-2, 0, 4] = true := by decide +kernel
theorem subd18_3_95 : subd18_3 [-2, 0, 5] = true := by decide +kernel
theorem sbd18_3_2 : ∀ q ∈ blkd18_3_2, subd18_3 q = true := by
  unfold blkd18_3_2
  exact List.forall_mem_cons.2 ⟨subd18_3_64, List.forall_mem_cons.2 ⟨subd18_3_65, List.forall_mem_cons.2 ⟨subd18_3_66, List.forall_mem_cons.2 ⟨subd18_3_67, List.forall_mem_cons.2 ⟨subd18_3_68, List.forall_mem_cons.2 ⟨subd18_3_69, List.forall_mem_cons.2 ⟨subd18_3_70, List.forall_mem_cons.2 ⟨subd18_3_71, List.forall_mem_cons.2 ⟨subd18_3_72, List.forall_mem_cons.2 ⟨subd18_3_73, List.forall_mem_cons.2 ⟨subd18_3_74, List.forall_mem_cons.2 ⟨subd18_3_75, List.forall_mem_cons.2 ⟨subd18_3_76, List.forall_mem_cons.2 ⟨subd18_3_77, List.forall_mem_cons.2 ⟨subd18_3_78, List.forall_mem_cons.2 ⟨subd18_3_79, List.forall_mem_cons.2 ⟨subd18_3_80, List.forall_mem_cons.2 ⟨subd18_3_81, List.forall_mem_cons.2 ⟨subd18_3_82, List.forall_mem_cons.2 ⟨subd18_3_83, List.forall_mem_cons.2 ⟨subd18_3_84, List.forall_mem_cons.2 ⟨subd18_3_85, List.forall_mem_cons.2 ⟨subd18_3_86, List.forall_mem_cons.2 ⟨subd18_3_87, List.forall_mem_cons.2 ⟨subd18_3_88, List.forall_mem_cons.2 ⟨subd18_3_89, List.forall_mem_cons.2 ⟨subd18_3_90, List.forall_mem_cons.2 ⟨subd18_3_91, List.forall_mem_cons.2 ⟨subd18_3_92, List.forall_mem_cons.2 ⟨subd18_3_93, List.forall_mem_cons.2 ⟨subd18_3_94, List.forall_mem_cons.2 ⟨subd18_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_96 : subd18_3 [-2, 0, 6] = true := by decide +kernel
theorem subd18_3_97 : subd18_3 [-2, 0, 7] = true := by decide +kernel
theorem subd18_3_98 : subd18_3 [-2, 1, -6] = true := by decide +kernel
theorem subd18_3_99 : subd18_3 [-2, 1, -5] = true := by decide +kernel
theorem subd18_3_100 : subd18_3 [-2, 1, -4] = true := by decide +kernel
theorem subd18_3_101 : subd18_3 [-2, 1, -3] = true := by decide +kernel
theorem subd18_3_102 : subd18_3 [-2, 1, -2] = true := by decide +kernel
theorem subd18_3_103 : subd18_3 [-2, 1, -1] = true := by decide +kernel
theorem subd18_3_104 : subd18_3 [-2, 1, 0] = true := by decide +kernel
theorem subd18_3_105 : subd18_3 [-2, 1, 1] = true := by decide +kernel
theorem subd18_3_106 : subd18_3 [-2, 1, 2] = true := by decide +kernel
theorem subd18_3_107 : subd18_3 [-2, 1, 3] = true := by decide +kernel
theorem subd18_3_108 : subd18_3 [-2, 1, 4] = true := by decide +kernel
theorem subd18_3_109 : subd18_3 [-2, 1, 5] = true := by decide +kernel
theorem subd18_3_110 : subd18_3 [-2, 1, 6] = true := by decide +kernel
theorem subd18_3_111 : subd18_3 [-2, 1, 7] = true := by decide +kernel
theorem subd18_3_112 : subd18_3 [-2, 2, -6] = true := by decide +kernel
theorem subd18_3_113 : subd18_3 [-2, 2, -5] = true := by decide +kernel
theorem subd18_3_114 : subd18_3 [-2, 2, -4] = true := by decide +kernel
theorem subd18_3_115 : subd18_3 [-2, 2, -3] = true := by decide +kernel
theorem subd18_3_116 : subd18_3 [-2, 2, -2] = true := by decide +kernel
theorem subd18_3_117 : subd18_3 [-2, 2, -1] = true := by decide +kernel
theorem subd18_3_118 : subd18_3 [-2, 2, 0] = true := by decide +kernel
theorem subd18_3_119 : subd18_3 [-2, 2, 1] = true := by decide +kernel
theorem subd18_3_120 : subd18_3 [-2, 2, 2] = true := by decide +kernel
theorem subd18_3_121 : subd18_3 [-2, 2, 3] = true := by decide +kernel
theorem subd18_3_122 : subd18_3 [-2, 2, 4] = true := by decide +kernel
theorem subd18_3_123 : subd18_3 [-2, 2, 5] = true := by decide +kernel
theorem subd18_3_124 : subd18_3 [-2, 2, 6] = true := by decide +kernel
theorem subd18_3_125 : subd18_3 [-2, 3] = true := by decide +kernel
theorem subd18_3_126 : subd18_3 [-2, 4] = true := by decide +kernel
theorem subd18_3_127 : subd18_3 [-2, 5] = true := by decide +kernel
theorem sbd18_3_3 : ∀ q ∈ blkd18_3_3, subd18_3 q = true := by
  unfold blkd18_3_3
  exact List.forall_mem_cons.2 ⟨subd18_3_96, List.forall_mem_cons.2 ⟨subd18_3_97, List.forall_mem_cons.2 ⟨subd18_3_98, List.forall_mem_cons.2 ⟨subd18_3_99, List.forall_mem_cons.2 ⟨subd18_3_100, List.forall_mem_cons.2 ⟨subd18_3_101, List.forall_mem_cons.2 ⟨subd18_3_102, List.forall_mem_cons.2 ⟨subd18_3_103, List.forall_mem_cons.2 ⟨subd18_3_104, List.forall_mem_cons.2 ⟨subd18_3_105, List.forall_mem_cons.2 ⟨subd18_3_106, List.forall_mem_cons.2 ⟨subd18_3_107, List.forall_mem_cons.2 ⟨subd18_3_108, List.forall_mem_cons.2 ⟨subd18_3_109, List.forall_mem_cons.2 ⟨subd18_3_110, List.forall_mem_cons.2 ⟨subd18_3_111, List.forall_mem_cons.2 ⟨subd18_3_112, List.forall_mem_cons.2 ⟨subd18_3_113, List.forall_mem_cons.2 ⟨subd18_3_114, List.forall_mem_cons.2 ⟨subd18_3_115, List.forall_mem_cons.2 ⟨subd18_3_116, List.forall_mem_cons.2 ⟨subd18_3_117, List.forall_mem_cons.2 ⟨subd18_3_118, List.forall_mem_cons.2 ⟨subd18_3_119, List.forall_mem_cons.2 ⟨subd18_3_120, List.forall_mem_cons.2 ⟨subd18_3_121, List.forall_mem_cons.2 ⟨subd18_3_122, List.forall_mem_cons.2 ⟨subd18_3_123, List.forall_mem_cons.2 ⟨subd18_3_124, List.forall_mem_cons.2 ⟨subd18_3_125, List.forall_mem_cons.2 ⟨subd18_3_126, List.forall_mem_cons.2 ⟨subd18_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_128 : subd18_3 [-2, 6] = true := by decide +kernel
theorem subd18_3_129 : subd18_3 [-2, 7] = true := by decide +kernel
theorem subd18_3_130 : subd18_3 [-1, -8] = true := by decide +kernel
theorem subd18_3_131 : subd18_3 [-1, -7] = true := by decide +kernel
theorem subd18_3_132 : subd18_3 [-1, -6] = true := by decide +kernel
theorem subd18_3_133 : subd18_3 [-1, -5] = true := by decide +kernel
theorem subd18_3_134 : subd18_3 [-1, -4] = true := by decide +kernel
theorem subd18_3_135 : subd18_3 [-1, -3] = true := by decide +kernel
theorem subd18_3_136 : subd18_3 [-1, -2, -6] = true := by decide +kernel
theorem subd18_3_137 : subd18_3 [-1, -2, -5] = true := by decide +kernel
theorem subd18_3_138 : subd18_3 [-1, -2, -4] = true := by decide +kernel
theorem subd18_3_139 : subd18_3 [-1, -2, -3] = true := by decide +kernel
theorem subd18_3_140 : subd18_3 [-1, -2, -2] = true := by decide +kernel
theorem subd18_3_141 : subd18_3 [-1, -2, -1] = true := by decide +kernel
theorem subd18_3_142 : subd18_3 [-1, -2, 0] = true := by decide +kernel
theorem subd18_3_143 : subd18_3 [-1, -2, 1] = true := by decide +kernel
theorem subd18_3_144 : subd18_3 [-1, -2, 2] = true := by decide +kernel
theorem subd18_3_145 : subd18_3 [-1, -2, 3] = true := by decide +kernel
theorem subd18_3_146 : subd18_3 [-1, -2, 4] = true := by decide +kernel
theorem subd18_3_147 : subd18_3 [-1, -2, 5] = true := by decide +kernel
theorem subd18_3_148 : subd18_3 [-1, -2, 6] = true := by decide +kernel
theorem subd18_3_149 : subd18_3 [-1, -2, 7] = true := by decide +kernel
theorem subd18_3_150 : subd18_3 [-1, -1, -6] = true := by decide +kernel
theorem subd18_3_151 : subd18_3 [-1, -1, -5] = true := by decide +kernel
theorem subd18_3_152 : subd18_3 [-1, -1, -4] = true := by decide +kernel
theorem subd18_3_153 : subd18_3 [-1, -1, -3] = true := by decide +kernel
theorem subd18_3_154 : subd18_3 [-1, -1, -2] = true := by decide +kernel
theorem subd18_3_155 : subd18_3 [-1, -1, -1] = true := by decide +kernel
theorem subd18_3_156 : subd18_3 [-1, -1, 0] = true := by decide +kernel
theorem subd18_3_157 : subd18_3 [-1, -1, 1] = true := by decide +kernel
theorem subd18_3_158 : subd18_3 [-1, -1, 2] = true := by decide +kernel
theorem subd18_3_159 : subd18_3 [-1, -1, 3] = true := by decide +kernel
theorem sbd18_3_4 : ∀ q ∈ blkd18_3_4, subd18_3 q = true := by
  unfold blkd18_3_4
  exact List.forall_mem_cons.2 ⟨subd18_3_128, List.forall_mem_cons.2 ⟨subd18_3_129, List.forall_mem_cons.2 ⟨subd18_3_130, List.forall_mem_cons.2 ⟨subd18_3_131, List.forall_mem_cons.2 ⟨subd18_3_132, List.forall_mem_cons.2 ⟨subd18_3_133, List.forall_mem_cons.2 ⟨subd18_3_134, List.forall_mem_cons.2 ⟨subd18_3_135, List.forall_mem_cons.2 ⟨subd18_3_136, List.forall_mem_cons.2 ⟨subd18_3_137, List.forall_mem_cons.2 ⟨subd18_3_138, List.forall_mem_cons.2 ⟨subd18_3_139, List.forall_mem_cons.2 ⟨subd18_3_140, List.forall_mem_cons.2 ⟨subd18_3_141, List.forall_mem_cons.2 ⟨subd18_3_142, List.forall_mem_cons.2 ⟨subd18_3_143, List.forall_mem_cons.2 ⟨subd18_3_144, List.forall_mem_cons.2 ⟨subd18_3_145, List.forall_mem_cons.2 ⟨subd18_3_146, List.forall_mem_cons.2 ⟨subd18_3_147, List.forall_mem_cons.2 ⟨subd18_3_148, List.forall_mem_cons.2 ⟨subd18_3_149, List.forall_mem_cons.2 ⟨subd18_3_150, List.forall_mem_cons.2 ⟨subd18_3_151, List.forall_mem_cons.2 ⟨subd18_3_152, List.forall_mem_cons.2 ⟨subd18_3_153, List.forall_mem_cons.2 ⟨subd18_3_154, List.forall_mem_cons.2 ⟨subd18_3_155, List.forall_mem_cons.2 ⟨subd18_3_156, List.forall_mem_cons.2 ⟨subd18_3_157, List.forall_mem_cons.2 ⟨subd18_3_158, List.forall_mem_cons.2 ⟨subd18_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_160 : subd18_3 [-1, -1, 4] = true := by decide +kernel
theorem subd18_3_161 : subd18_3 [-1, -1, 5] = true := by decide +kernel
theorem subd18_3_162 : subd18_3 [-1, -1, 6] = true := by decide +kernel
theorem subd18_3_163 : subd18_3 [-1, -1, 7] = true := by decide +kernel
theorem subd18_3_164 : subd18_3 [-1, 0, -7] = true := by decide +kernel
theorem subd18_3_165 : subd18_3 [-1, 0, -6] = true := by decide +kernel
theorem subd18_3_166 : subd18_3 [-1, 0, -5] = true := by decide +kernel
theorem subd18_3_167 : subd18_3 [-1, 0, -4] = true := by decide +kernel
theorem subd18_3_168 : subd18_3 [-1, 0, -3] = true := by decide +kernel
theorem subd18_3_169 : subd18_3 [-1, 0, -2] = true := by decide +kernel
theorem subd18_3_170 : subd18_3 [-1, 0, -1] = true := by decide +kernel
theorem subd18_3_171 : subd18_3 [-1, 0, 0] = true := by decide +kernel
theorem subd18_3_172 : subd18_3 [-1, 0, 1] = true := by decide +kernel
theorem subd18_3_173 : subd18_3 [-1, 0, 2] = true := by decide +kernel
theorem subd18_3_174 : subd18_3 [-1, 0, 3] = true := by decide +kernel
theorem subd18_3_175 : subd18_3 [-1, 0, 4] = true := by decide +kernel
theorem subd18_3_176 : subd18_3 [-1, 0, 5] = true := by decide +kernel
theorem subd18_3_177 : subd18_3 [-1, 0, 6] = true := by decide +kernel
theorem subd18_3_178 : subd18_3 [-1, 0, 7] = true := by decide +kernel
theorem subd18_3_179 : subd18_3 [-1, 1, -7] = true := by decide +kernel
theorem subd18_3_180 : subd18_3 [-1, 1, -6] = true := by decide +kernel
theorem subd18_3_181 : subd18_3 [-1, 1, -5] = true := by decide +kernel
theorem subd18_3_182 : subd18_3 [-1, 1, -4] = true := by decide +kernel
theorem subd18_3_183 : subd18_3 [-1, 1, -3] = true := by decide +kernel
theorem subd18_3_184 : subd18_3 [-1, 1, -2] = true := by decide +kernel
theorem subd18_3_185 : subd18_3 [-1, 1, -1] = true := by decide +kernel
theorem subd18_3_186 : subd18_3 [-1, 1, 0] = true := by decide +kernel
theorem subd18_3_187 : subd18_3 [-1, 1, 1] = true := by decide +kernel
theorem subd18_3_188 : subd18_3 [-1, 1, 2] = true := by decide +kernel
theorem subd18_3_189 : subd18_3 [-1, 1, 3] = true := by decide +kernel
theorem subd18_3_190 : subd18_3 [-1, 1, 4] = true := by decide +kernel
theorem subd18_3_191 : subd18_3 [-1, 1, 5] = true := by decide +kernel
theorem sbd18_3_5 : ∀ q ∈ blkd18_3_5, subd18_3 q = true := by
  unfold blkd18_3_5
  exact List.forall_mem_cons.2 ⟨subd18_3_160, List.forall_mem_cons.2 ⟨subd18_3_161, List.forall_mem_cons.2 ⟨subd18_3_162, List.forall_mem_cons.2 ⟨subd18_3_163, List.forall_mem_cons.2 ⟨subd18_3_164, List.forall_mem_cons.2 ⟨subd18_3_165, List.forall_mem_cons.2 ⟨subd18_3_166, List.forall_mem_cons.2 ⟨subd18_3_167, List.forall_mem_cons.2 ⟨subd18_3_168, List.forall_mem_cons.2 ⟨subd18_3_169, List.forall_mem_cons.2 ⟨subd18_3_170, List.forall_mem_cons.2 ⟨subd18_3_171, List.forall_mem_cons.2 ⟨subd18_3_172, List.forall_mem_cons.2 ⟨subd18_3_173, List.forall_mem_cons.2 ⟨subd18_3_174, List.forall_mem_cons.2 ⟨subd18_3_175, List.forall_mem_cons.2 ⟨subd18_3_176, List.forall_mem_cons.2 ⟨subd18_3_177, List.forall_mem_cons.2 ⟨subd18_3_178, List.forall_mem_cons.2 ⟨subd18_3_179, List.forall_mem_cons.2 ⟨subd18_3_180, List.forall_mem_cons.2 ⟨subd18_3_181, List.forall_mem_cons.2 ⟨subd18_3_182, List.forall_mem_cons.2 ⟨subd18_3_183, List.forall_mem_cons.2 ⟨subd18_3_184, List.forall_mem_cons.2 ⟨subd18_3_185, List.forall_mem_cons.2 ⟨subd18_3_186, List.forall_mem_cons.2 ⟨subd18_3_187, List.forall_mem_cons.2 ⟨subd18_3_188, List.forall_mem_cons.2 ⟨subd18_3_189, List.forall_mem_cons.2 ⟨subd18_3_190, List.forall_mem_cons.2 ⟨subd18_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_192 : subd18_3 [-1, 1, 6] = true := by decide +kernel
theorem subd18_3_193 : subd18_3 [-1, 2, -7] = true := by decide +kernel
theorem subd18_3_194 : subd18_3 [-1, 2, -6] = true := by decide +kernel
theorem subd18_3_195 : subd18_3 [-1, 2, -5] = true := by decide +kernel
theorem subd18_3_196 : subd18_3 [-1, 2, -4] = true := by decide +kernel
theorem subd18_3_197 : subd18_3 [-1, 2, -3] = true := by decide +kernel
theorem subd18_3_198 : subd18_3 [-1, 2, -2] = true := by decide +kernel
theorem subd18_3_199 : subd18_3 [-1, 2, -1] = true := by decide +kernel
theorem subd18_3_200 : subd18_3 [-1, 2, 0] = true := by decide +kernel
theorem subd18_3_201 : subd18_3 [-1, 2, 1] = true := by decide +kernel
theorem subd18_3_202 : subd18_3 [-1, 2, 2] = true := by decide +kernel
theorem subd18_3_203 : subd18_3 [-1, 2, 3] = true := by decide +kernel
theorem subd18_3_204 : subd18_3 [-1, 2, 4] = true := by decide +kernel
theorem subd18_3_205 : subd18_3 [-1, 2, 5] = true := by decide +kernel
theorem subd18_3_206 : subd18_3 [-1, 2, 6] = true := by decide +kernel
theorem subd18_3_207 : subd18_3 [-1, 3] = true := by decide +kernel
theorem subd18_3_208 : subd18_3 [-1, 4] = true := by decide +kernel
theorem subd18_3_209 : subd18_3 [-1, 5] = true := by decide +kernel
theorem subd18_3_210 : subd18_3 [-1, 6] = true := by decide +kernel
theorem subd18_3_211 : subd18_3 [-1, 7] = true := by decide +kernel
theorem subd18_3_212 : subd18_3 [0, -8] = true := by decide +kernel
theorem subd18_3_213 : subd18_3 [0, -7] = true := by decide +kernel
theorem subd18_3_214 : subd18_3 [0, -6] = true := by decide +kernel
theorem subd18_3_215 : subd18_3 [0, -5] = true := by decide +kernel
theorem subd18_3_216 : subd18_3 [0, -4] = true := by decide +kernel
theorem subd18_3_217 : subd18_3 [0, -3, -6] = true := by decide +kernel
theorem subd18_3_218 : subd18_3 [0, -3, -5] = true := by decide +kernel
theorem subd18_3_219 : subd18_3 [0, -3, -4] = true := by decide +kernel
theorem subd18_3_220 : subd18_3 [0, -3, -3] = true := by decide +kernel
theorem subd18_3_221 : subd18_3 [0, -3, -2] = true := by decide +kernel
theorem subd18_3_222 : subd18_3 [0, -3, -1] = true := by decide +kernel
theorem subd18_3_223 : subd18_3 [0, -3, 0] = true := by decide +kernel
theorem sbd18_3_6 : ∀ q ∈ blkd18_3_6, subd18_3 q = true := by
  unfold blkd18_3_6
  exact List.forall_mem_cons.2 ⟨subd18_3_192, List.forall_mem_cons.2 ⟨subd18_3_193, List.forall_mem_cons.2 ⟨subd18_3_194, List.forall_mem_cons.2 ⟨subd18_3_195, List.forall_mem_cons.2 ⟨subd18_3_196, List.forall_mem_cons.2 ⟨subd18_3_197, List.forall_mem_cons.2 ⟨subd18_3_198, List.forall_mem_cons.2 ⟨subd18_3_199, List.forall_mem_cons.2 ⟨subd18_3_200, List.forall_mem_cons.2 ⟨subd18_3_201, List.forall_mem_cons.2 ⟨subd18_3_202, List.forall_mem_cons.2 ⟨subd18_3_203, List.forall_mem_cons.2 ⟨subd18_3_204, List.forall_mem_cons.2 ⟨subd18_3_205, List.forall_mem_cons.2 ⟨subd18_3_206, List.forall_mem_cons.2 ⟨subd18_3_207, List.forall_mem_cons.2 ⟨subd18_3_208, List.forall_mem_cons.2 ⟨subd18_3_209, List.forall_mem_cons.2 ⟨subd18_3_210, List.forall_mem_cons.2 ⟨subd18_3_211, List.forall_mem_cons.2 ⟨subd18_3_212, List.forall_mem_cons.2 ⟨subd18_3_213, List.forall_mem_cons.2 ⟨subd18_3_214, List.forall_mem_cons.2 ⟨subd18_3_215, List.forall_mem_cons.2 ⟨subd18_3_216, List.forall_mem_cons.2 ⟨subd18_3_217, List.forall_mem_cons.2 ⟨subd18_3_218, List.forall_mem_cons.2 ⟨subd18_3_219, List.forall_mem_cons.2 ⟨subd18_3_220, List.forall_mem_cons.2 ⟨subd18_3_221, List.forall_mem_cons.2 ⟨subd18_3_222, List.forall_mem_cons.2 ⟨subd18_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_224 : subd18_3 [0, -3, 1] = true := by decide +kernel
theorem subd18_3_225 : subd18_3 [0, -3, 2] = true := by decide +kernel
theorem subd18_3_226 : subd18_3 [0, -3, 3] = true := by decide +kernel
theorem subd18_3_227 : subd18_3 [0, -3, 4] = true := by decide +kernel
theorem subd18_3_228 : subd18_3 [0, -3, 5] = true := by decide +kernel
theorem subd18_3_229 : subd18_3 [0, -3, 6] = true := by decide +kernel
theorem subd18_3_230 : subd18_3 [0, -2, -7] = true := by decide +kernel
theorem subd18_3_231 : subd18_3 [0, -2, -6] = true := by decide +kernel
theorem subd18_3_232 : subd18_3 [0, -2, -5] = true := by decide +kernel
theorem subd18_3_233 : subd18_3 [0, -2, -4] = true := by decide +kernel
theorem subd18_3_234 : subd18_3 [0, -2, -3] = true := by decide +kernel
theorem subd18_3_235 : subd18_3 [0, -2, -2] = true := by decide +kernel
theorem subd18_3_236 : subd18_3 [0, -2, -1] = true := by decide +kernel
theorem subd18_3_237 : subd18_3 [0, -2, 0] = true := by decide +kernel
theorem subd18_3_238 : subd18_3 [0, -2, 1] = true := by decide +kernel
theorem subd18_3_239 : subd18_3 [0, -2, 2] = true := by decide +kernel
theorem subd18_3_240 : subd18_3 [0, -2, 3] = true := by decide +kernel
theorem subd18_3_241 : subd18_3 [0, -2, 4] = true := by decide +kernel
theorem subd18_3_242 : subd18_3 [0, -2, 5] = true := by decide +kernel
theorem subd18_3_243 : subd18_3 [0, -2, 6] = true := by decide +kernel
theorem subd18_3_244 : subd18_3 [0, -1, -7] = true := by decide +kernel
theorem subd18_3_245 : subd18_3 [0, -1, -6] = true := by decide +kernel
theorem subd18_3_246 : subd18_3 [0, -1, -5] = true := by decide +kernel
theorem subd18_3_247 : subd18_3 [0, -1, -4] = true := by decide +kernel
theorem subd18_3_248 : subd18_3 [0, -1, -3] = true := by decide +kernel
theorem subd18_3_249 : subd18_3 [0, -1, -2] = true := by decide +kernel
theorem subd18_3_250 : subd18_3 [0, -1, -1] = true := by decide +kernel
theorem subd18_3_251 : subd18_3 [0, -1, 0] = true := by decide +kernel
theorem subd18_3_252 : subd18_3 [0, -1, 1] = true := by decide +kernel
theorem subd18_3_253 : subd18_3 [0, -1, 2] = true := by decide +kernel
theorem subd18_3_254 : subd18_3 [0, -1, 3] = true := by decide +kernel
theorem subd18_3_255 : subd18_3 [0, -1, 4] = true := by decide +kernel
theorem sbd18_3_7 : ∀ q ∈ blkd18_3_7, subd18_3 q = true := by
  unfold blkd18_3_7
  exact List.forall_mem_cons.2 ⟨subd18_3_224, List.forall_mem_cons.2 ⟨subd18_3_225, List.forall_mem_cons.2 ⟨subd18_3_226, List.forall_mem_cons.2 ⟨subd18_3_227, List.forall_mem_cons.2 ⟨subd18_3_228, List.forall_mem_cons.2 ⟨subd18_3_229, List.forall_mem_cons.2 ⟨subd18_3_230, List.forall_mem_cons.2 ⟨subd18_3_231, List.forall_mem_cons.2 ⟨subd18_3_232, List.forall_mem_cons.2 ⟨subd18_3_233, List.forall_mem_cons.2 ⟨subd18_3_234, List.forall_mem_cons.2 ⟨subd18_3_235, List.forall_mem_cons.2 ⟨subd18_3_236, List.forall_mem_cons.2 ⟨subd18_3_237, List.forall_mem_cons.2 ⟨subd18_3_238, List.forall_mem_cons.2 ⟨subd18_3_239, List.forall_mem_cons.2 ⟨subd18_3_240, List.forall_mem_cons.2 ⟨subd18_3_241, List.forall_mem_cons.2 ⟨subd18_3_242, List.forall_mem_cons.2 ⟨subd18_3_243, List.forall_mem_cons.2 ⟨subd18_3_244, List.forall_mem_cons.2 ⟨subd18_3_245, List.forall_mem_cons.2 ⟨subd18_3_246, List.forall_mem_cons.2 ⟨subd18_3_247, List.forall_mem_cons.2 ⟨subd18_3_248, List.forall_mem_cons.2 ⟨subd18_3_249, List.forall_mem_cons.2 ⟨subd18_3_250, List.forall_mem_cons.2 ⟨subd18_3_251, List.forall_mem_cons.2 ⟨subd18_3_252, List.forall_mem_cons.2 ⟨subd18_3_253, List.forall_mem_cons.2 ⟨subd18_3_254, List.forall_mem_cons.2 ⟨subd18_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_256 : subd18_3 [0, -1, 5] = true := by decide +kernel
theorem subd18_3_257 : subd18_3 [0, -1, 6] = true := by decide +kernel
theorem subd18_3_258 : subd18_3 [0, 0, -7] = true := by decide +kernel
theorem subd18_3_259 : subd18_3 [0, 0, -6] = true := by decide +kernel
theorem subd18_3_260 : subd18_3 [0, 0, -5] = true := by decide +kernel
theorem subd18_3_261 : subd18_3 [0, 0, -4] = true := by decide +kernel
theorem subd18_3_262 : subd18_3 [0, 0, -3] = true := by decide +kernel
theorem subd18_3_263 : subd18_3 [0, 0, -2] = true := by decide +kernel
theorem subd18_3_264 : subd18_3 [0, 0, -1] = true := by decide +kernel
theorem subd18_3_265 : subd18_3 [0, 0, 0] = true := by decide +kernel
theorem subd18_3_266 : subd18_3 [0, 0, 1] = true := by decide +kernel
theorem subd18_3_267 : subd18_3 [0, 0, 2] = true := by decide +kernel
theorem subd18_3_268 : subd18_3 [0, 0, 3] = true := by decide +kernel
theorem subd18_3_269 : subd18_3 [0, 0, 4] = true := by decide +kernel
theorem subd18_3_270 : subd18_3 [0, 0, 5] = true := by decide +kernel
theorem subd18_3_271 : subd18_3 [0, 0, 6] = true := by decide +kernel
theorem subd18_3_272 : subd18_3 [0, 1, -7] = true := by decide +kernel
theorem subd18_3_273 : subd18_3 [0, 1, -6] = true := by decide +kernel
theorem subd18_3_274 : subd18_3 [0, 1, -5] = true := by decide +kernel
theorem subd18_3_275 : subd18_3 [0, 1, -4] = true := by decide +kernel
theorem subd18_3_276 : subd18_3 [0, 1, -3] = true := by decide +kernel
theorem subd18_3_277 : subd18_3 [0, 1, -2] = true := by decide +kernel
theorem subd18_3_278 : subd18_3 [0, 1, -1] = true := by decide +kernel
theorem subd18_3_279 : subd18_3 [0, 1, 0] = true := by decide +kernel
theorem subd18_3_280 : subd18_3 [0, 1, 1] = true := by decide +kernel
theorem subd18_3_281 : subd18_3 [0, 1, 2] = true := by decide +kernel
theorem subd18_3_282 : subd18_3 [0, 1, 3] = true := by decide +kernel
theorem subd18_3_283 : subd18_3 [0, 1, 4] = true := by decide +kernel
theorem subd18_3_284 : subd18_3 [0, 1, 5] = true := by decide +kernel
theorem subd18_3_285 : subd18_3 [0, 1, 6] = true := by decide +kernel
theorem subd18_3_286 : subd18_3 [0, 2, -7] = true := by decide +kernel
theorem subd18_3_287 : subd18_3 [0, 2, -6] = true := by decide +kernel
theorem sbd18_3_8 : ∀ q ∈ blkd18_3_8, subd18_3 q = true := by
  unfold blkd18_3_8
  exact List.forall_mem_cons.2 ⟨subd18_3_256, List.forall_mem_cons.2 ⟨subd18_3_257, List.forall_mem_cons.2 ⟨subd18_3_258, List.forall_mem_cons.2 ⟨subd18_3_259, List.forall_mem_cons.2 ⟨subd18_3_260, List.forall_mem_cons.2 ⟨subd18_3_261, List.forall_mem_cons.2 ⟨subd18_3_262, List.forall_mem_cons.2 ⟨subd18_3_263, List.forall_mem_cons.2 ⟨subd18_3_264, List.forall_mem_cons.2 ⟨subd18_3_265, List.forall_mem_cons.2 ⟨subd18_3_266, List.forall_mem_cons.2 ⟨subd18_3_267, List.forall_mem_cons.2 ⟨subd18_3_268, List.forall_mem_cons.2 ⟨subd18_3_269, List.forall_mem_cons.2 ⟨subd18_3_270, List.forall_mem_cons.2 ⟨subd18_3_271, List.forall_mem_cons.2 ⟨subd18_3_272, List.forall_mem_cons.2 ⟨subd18_3_273, List.forall_mem_cons.2 ⟨subd18_3_274, List.forall_mem_cons.2 ⟨subd18_3_275, List.forall_mem_cons.2 ⟨subd18_3_276, List.forall_mem_cons.2 ⟨subd18_3_277, List.forall_mem_cons.2 ⟨subd18_3_278, List.forall_mem_cons.2 ⟨subd18_3_279, List.forall_mem_cons.2 ⟨subd18_3_280, List.forall_mem_cons.2 ⟨subd18_3_281, List.forall_mem_cons.2 ⟨subd18_3_282, List.forall_mem_cons.2 ⟨subd18_3_283, List.forall_mem_cons.2 ⟨subd18_3_284, List.forall_mem_cons.2 ⟨subd18_3_285, List.forall_mem_cons.2 ⟨subd18_3_286, List.forall_mem_cons.2 ⟨subd18_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_288 : subd18_3 [0, 2, -5] = true := by decide +kernel
theorem subd18_3_289 : subd18_3 [0, 2, -4] = true := by decide +kernel
theorem subd18_3_290 : subd18_3 [0, 2, -3] = true := by decide +kernel
theorem subd18_3_291 : subd18_3 [0, 2, -2] = true := by decide +kernel
theorem subd18_3_292 : subd18_3 [0, 2, -1] = true := by decide +kernel
theorem subd18_3_293 : subd18_3 [0, 2, 0] = true := by decide +kernel
theorem subd18_3_294 : subd18_3 [0, 2, 1] = true := by decide +kernel
theorem subd18_3_295 : subd18_3 [0, 2, 2] = true := by decide +kernel
theorem subd18_3_296 : subd18_3 [0, 2, 3] = true := by decide +kernel
theorem subd18_3_297 : subd18_3 [0, 2, 4] = true := by decide +kernel
theorem subd18_3_298 : subd18_3 [0, 2, 5] = true := by decide +kernel
theorem subd18_3_299 : subd18_3 [0, 2, 6] = true := by decide +kernel
theorem subd18_3_300 : subd18_3 [0, 3, -7] = true := by decide +kernel
theorem subd18_3_301 : subd18_3 [0, 3, -6] = true := by decide +kernel
theorem subd18_3_302 : subd18_3 [0, 3, -5] = true := by decide +kernel
theorem subd18_3_303 : subd18_3 [0, 3, -4] = true := by decide +kernel
theorem subd18_3_304 : subd18_3 [0, 3, -3] = true := by decide +kernel
theorem subd18_3_305 : subd18_3 [0, 3, -2] = true := by decide +kernel
theorem subd18_3_306 : subd18_3 [0, 3, -1] = true := by decide +kernel
theorem subd18_3_307 : subd18_3 [0, 3, 0] = true := by decide +kernel
theorem subd18_3_308 : subd18_3 [0, 3, 1] = true := by decide +kernel
theorem subd18_3_309 : subd18_3 [0, 3, 2] = true := by decide +kernel
theorem subd18_3_310 : subd18_3 [0, 3, 3] = true := by decide +kernel
theorem subd18_3_311 : subd18_3 [0, 3, 4] = true := by decide +kernel
theorem subd18_3_312 : subd18_3 [0, 3, 5] = true := by decide +kernel
theorem subd18_3_313 : subd18_3 [0, 4] = true := by decide +kernel
theorem subd18_3_314 : subd18_3 [0, 5] = true := by decide +kernel
theorem subd18_3_315 : subd18_3 [0, 6] = true := by decide +kernel
theorem subd18_3_316 : subd18_3 [0, 7] = true := by decide +kernel
theorem subd18_3_317 : subd18_3 [1, -8] = true := by decide +kernel
theorem subd18_3_318 : subd18_3 [1, -7] = true := by decide +kernel
theorem subd18_3_319 : subd18_3 [1, -6] = true := by decide +kernel
theorem sbd18_3_9 : ∀ q ∈ blkd18_3_9, subd18_3 q = true := by
  unfold blkd18_3_9
  exact List.forall_mem_cons.2 ⟨subd18_3_288, List.forall_mem_cons.2 ⟨subd18_3_289, List.forall_mem_cons.2 ⟨subd18_3_290, List.forall_mem_cons.2 ⟨subd18_3_291, List.forall_mem_cons.2 ⟨subd18_3_292, List.forall_mem_cons.2 ⟨subd18_3_293, List.forall_mem_cons.2 ⟨subd18_3_294, List.forall_mem_cons.2 ⟨subd18_3_295, List.forall_mem_cons.2 ⟨subd18_3_296, List.forall_mem_cons.2 ⟨subd18_3_297, List.forall_mem_cons.2 ⟨subd18_3_298, List.forall_mem_cons.2 ⟨subd18_3_299, List.forall_mem_cons.2 ⟨subd18_3_300, List.forall_mem_cons.2 ⟨subd18_3_301, List.forall_mem_cons.2 ⟨subd18_3_302, List.forall_mem_cons.2 ⟨subd18_3_303, List.forall_mem_cons.2 ⟨subd18_3_304, List.forall_mem_cons.2 ⟨subd18_3_305, List.forall_mem_cons.2 ⟨subd18_3_306, List.forall_mem_cons.2 ⟨subd18_3_307, List.forall_mem_cons.2 ⟨subd18_3_308, List.forall_mem_cons.2 ⟨subd18_3_309, List.forall_mem_cons.2 ⟨subd18_3_310, List.forall_mem_cons.2 ⟨subd18_3_311, List.forall_mem_cons.2 ⟨subd18_3_312, List.forall_mem_cons.2 ⟨subd18_3_313, List.forall_mem_cons.2 ⟨subd18_3_314, List.forall_mem_cons.2 ⟨subd18_3_315, List.forall_mem_cons.2 ⟨subd18_3_316, List.forall_mem_cons.2 ⟨subd18_3_317, List.forall_mem_cons.2 ⟨subd18_3_318, List.forall_mem_cons.2 ⟨subd18_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
