import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_2_32 : subd13_2 [-2, 0, 2] = true := by decide +kernel
theorem subd13_2_33 : subd13_2 [-2, 0, 3] = true := by decide +kernel
theorem subd13_2_34 : subd13_2 [-2, 0, 4] = true := by decide +kernel
theorem subd13_2_35 : subd13_2 [-2, 0, 5] = true := by decide +kernel
theorem subd13_2_36 : subd13_2 [-2, 0, 6] = true := by decide +kernel
theorem subd13_2_37 : subd13_2 [-2, 1] = true := by decide +kernel
theorem subd13_2_38 : subd13_2 [-2, 2] = true := by decide +kernel
theorem subd13_2_39 : subd13_2 [-2, 3] = true := by decide +kernel
theorem subd13_2_40 : subd13_2 [-2, 4] = true := by decide +kernel
theorem subd13_2_41 : subd13_2 [-2, 5] = true := by decide +kernel
theorem subd13_2_42 : subd13_2 [-1, -6] = true := by decide +kernel
theorem subd13_2_43 : subd13_2 [-1, -5] = true := by decide +kernel
theorem subd13_2_44 : subd13_2 [-1, -4] = true := by decide +kernel
theorem subd13_2_45 : subd13_2 [-1, -3] = true := by decide +kernel
theorem subd13_2_46 : subd13_2 [-1, -2] = true := by decide +kernel
theorem subd13_2_47 : subd13_2 [-1, -1, -7] = true := by decide +kernel
theorem subd13_2_48 : subd13_2 [-1, -1, -6] = true := by decide +kernel
theorem subd13_2_49 : subd13_2 [-1, -1, -5] = true := by decide +kernel
theorem subd13_2_50 : subd13_2 [-1, -1, -4] = true := by decide +kernel
theorem subd13_2_51 : subd13_2 [-1, -1, -3] = true := by decide +kernel
theorem subd13_2_52 : subd13_2 [-1, -1, -2] = true := by decide +kernel
theorem subd13_2_53 : subd13_2 [-1, -1, -1] = true := by decide +kernel
theorem subd13_2_54 : subd13_2 [-1, -1, 0] = true := by decide +kernel
theorem subd13_2_55 : subd13_2 [-1, -1, 1] = true := by decide +kernel
theorem subd13_2_56 : subd13_2 [-1, -1, 2] = true := by decide +kernel
theorem subd13_2_57 : subd13_2 [-1, -1, 3] = true := by decide +kernel
theorem subd13_2_58 : subd13_2 [-1, -1, 4] = true := by decide +kernel
theorem subd13_2_59 : subd13_2 [-1, -1, 5] = true := by decide +kernel
theorem subd13_2_60 : subd13_2 [-1, -1, 6] = true := by decide +kernel
theorem subd13_2_61 : subd13_2 [-1, 0, -7] = true := by decide +kernel
theorem subd13_2_62 : subd13_2 [-1, 0, -6] = true := by decide +kernel
theorem subd13_2_63 : subd13_2 [-1, 0, -5] = true := by decide +kernel
theorem sbd13_2_1 : ∀ q ∈ blkd13_2_1, subd13_2 q = true := by
  unfold blkd13_2_1
  exact List.forall_mem_cons.2 ⟨subd13_2_32, List.forall_mem_cons.2 ⟨subd13_2_33, List.forall_mem_cons.2 ⟨subd13_2_34, List.forall_mem_cons.2 ⟨subd13_2_35, List.forall_mem_cons.2 ⟨subd13_2_36, List.forall_mem_cons.2 ⟨subd13_2_37, List.forall_mem_cons.2 ⟨subd13_2_38, List.forall_mem_cons.2 ⟨subd13_2_39, List.forall_mem_cons.2 ⟨subd13_2_40, List.forall_mem_cons.2 ⟨subd13_2_41, List.forall_mem_cons.2 ⟨subd13_2_42, List.forall_mem_cons.2 ⟨subd13_2_43, List.forall_mem_cons.2 ⟨subd13_2_44, List.forall_mem_cons.2 ⟨subd13_2_45, List.forall_mem_cons.2 ⟨subd13_2_46, List.forall_mem_cons.2 ⟨subd13_2_47, List.forall_mem_cons.2 ⟨subd13_2_48, List.forall_mem_cons.2 ⟨subd13_2_49, List.forall_mem_cons.2 ⟨subd13_2_50, List.forall_mem_cons.2 ⟨subd13_2_51, List.forall_mem_cons.2 ⟨subd13_2_52, List.forall_mem_cons.2 ⟨subd13_2_53, List.forall_mem_cons.2 ⟨subd13_2_54, List.forall_mem_cons.2 ⟨subd13_2_55, List.forall_mem_cons.2 ⟨subd13_2_56, List.forall_mem_cons.2 ⟨subd13_2_57, List.forall_mem_cons.2 ⟨subd13_2_58, List.forall_mem_cons.2 ⟨subd13_2_59, List.forall_mem_cons.2 ⟨subd13_2_60, List.forall_mem_cons.2 ⟨subd13_2_61, List.forall_mem_cons.2 ⟨subd13_2_62, List.forall_mem_cons.2 ⟨subd13_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_64 : subd13_2 [-1, 0, -4] = true := by decide +kernel
theorem subd13_2_65 : subd13_2 [-1, 0, -3] = true := by decide +kernel
theorem subd13_2_66 : subd13_2 [-1, 0, -2] = true := by decide +kernel
theorem subd13_2_67 : subd13_2 [-1, 0, -1] = true := by decide +kernel
theorem subd13_2_68 : subd13_2 [-1, 0, 0] = true := by decide +kernel
theorem subd13_2_69 : subd13_2 [-1, 0, 1] = true := by decide +kernel
theorem subd13_2_70 : subd13_2 [-1, 0, 2] = true := by decide +kernel
theorem subd13_2_71 : subd13_2 [-1, 0, 3] = true := by decide +kernel
theorem subd13_2_72 : subd13_2 [-1, 0, 4] = true := by decide +kernel
theorem subd13_2_73 : subd13_2 [-1, 0, 5] = true := by decide +kernel
theorem subd13_2_74 : subd13_2 [-1, 0, 6] = true := by decide +kernel
theorem subd13_2_75 : subd13_2 [-1, 1, -6] = true := by decide +kernel
theorem subd13_2_76 : subd13_2 [-1, 1, -5] = true := by decide +kernel
theorem subd13_2_77 : subd13_2 [-1, 1, -4] = true := by decide +kernel
theorem subd13_2_78 : subd13_2 [-1, 1, -3] = true := by decide +kernel
theorem subd13_2_79 : subd13_2 [-1, 1, -2] = true := by decide +kernel
theorem subd13_2_80 : subd13_2 [-1, 1, -1] = true := by decide +kernel
theorem subd13_2_81 : subd13_2 [-1, 1, 0] = true := by decide +kernel
theorem subd13_2_82 : subd13_2 [-1, 1, 1] = true := by decide +kernel
theorem subd13_2_83 : subd13_2 [-1, 1, 2] = true := by decide +kernel
theorem subd13_2_84 : subd13_2 [-1, 1, 3] = true := by decide +kernel
theorem subd13_2_85 : subd13_2 [-1, 1, 4] = true := by decide +kernel
theorem subd13_2_86 : subd13_2 [-1, 1, 5] = true := by decide +kernel
theorem subd13_2_87 : subd13_2 [-1, 1, 6] = true := by decide +kernel
theorem subd13_2_88 : subd13_2 [-1, 1, 7] = true := by decide +kernel
theorem subd13_2_89 : subd13_2 [-1, 2, -5] = true := by decide +kernel
theorem subd13_2_90 : subd13_2 [-1, 2, -4] = true := by decide +kernel
theorem subd13_2_91 : subd13_2 [-1, 2, -3] = true := by decide +kernel
theorem subd13_2_92 : subd13_2 [-1, 2, -2] = true := by decide +kernel
theorem subd13_2_93 : subd13_2 [-1, 2, -1] = true := by decide +kernel
theorem subd13_2_94 : subd13_2 [-1, 2, 0] = true := by decide +kernel
theorem subd13_2_95 : subd13_2 [-1, 2, 1] = true := by decide +kernel
theorem sbd13_2_2 : ∀ q ∈ blkd13_2_2, subd13_2 q = true := by
  unfold blkd13_2_2
  exact List.forall_mem_cons.2 ⟨subd13_2_64, List.forall_mem_cons.2 ⟨subd13_2_65, List.forall_mem_cons.2 ⟨subd13_2_66, List.forall_mem_cons.2 ⟨subd13_2_67, List.forall_mem_cons.2 ⟨subd13_2_68, List.forall_mem_cons.2 ⟨subd13_2_69, List.forall_mem_cons.2 ⟨subd13_2_70, List.forall_mem_cons.2 ⟨subd13_2_71, List.forall_mem_cons.2 ⟨subd13_2_72, List.forall_mem_cons.2 ⟨subd13_2_73, List.forall_mem_cons.2 ⟨subd13_2_74, List.forall_mem_cons.2 ⟨subd13_2_75, List.forall_mem_cons.2 ⟨subd13_2_76, List.forall_mem_cons.2 ⟨subd13_2_77, List.forall_mem_cons.2 ⟨subd13_2_78, List.forall_mem_cons.2 ⟨subd13_2_79, List.forall_mem_cons.2 ⟨subd13_2_80, List.forall_mem_cons.2 ⟨subd13_2_81, List.forall_mem_cons.2 ⟨subd13_2_82, List.forall_mem_cons.2 ⟨subd13_2_83, List.forall_mem_cons.2 ⟨subd13_2_84, List.forall_mem_cons.2 ⟨subd13_2_85, List.forall_mem_cons.2 ⟨subd13_2_86, List.forall_mem_cons.2 ⟨subd13_2_87, List.forall_mem_cons.2 ⟨subd13_2_88, List.forall_mem_cons.2 ⟨subd13_2_89, List.forall_mem_cons.2 ⟨subd13_2_90, List.forall_mem_cons.2 ⟨subd13_2_91, List.forall_mem_cons.2 ⟨subd13_2_92, List.forall_mem_cons.2 ⟨subd13_2_93, List.forall_mem_cons.2 ⟨subd13_2_94, List.forall_mem_cons.2 ⟨subd13_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_96 : subd13_2 [-1, 2, 2] = true := by decide +kernel
theorem subd13_2_97 : subd13_2 [-1, 2, 3] = true := by decide +kernel
theorem subd13_2_98 : subd13_2 [-1, 2, 4] = true := by decide +kernel
theorem subd13_2_99 : subd13_2 [-1, 2, 5] = true := by decide +kernel
theorem subd13_2_100 : subd13_2 [-1, 2, 6] = true := by decide +kernel
theorem subd13_2_101 : subd13_2 [-1, 2, 7] = true := by decide +kernel
theorem subd13_2_102 : subd13_2 [-1, 3] = true := by decide +kernel
theorem subd13_2_103 : subd13_2 [-1, 4] = true := by decide +kernel
theorem subd13_2_104 : subd13_2 [-1, 5] = true := by decide +kernel
theorem subd13_2_105 : subd13_2 [0, -6] = true := by decide +kernel
theorem subd13_2_106 : subd13_2 [0, -5] = true := by decide +kernel
theorem subd13_2_107 : subd13_2 [0, -4] = true := by decide +kernel
theorem subd13_2_108 : subd13_2 [0, -3] = true := by decide +kernel
theorem subd13_2_109 : subd13_2 [0, -2, -8] = true := by decide +kernel
theorem subd13_2_110 : subd13_2 [0, -2, -7] = true := by decide +kernel
theorem subd13_2_111 : subd13_2 [0, -2, -6] = true := by decide +kernel
theorem subd13_2_112 : subd13_2 [0, -2, -5] = true := by decide +kernel
theorem subd13_2_113 : subd13_2 [0, -2, -4] = true := by decide +kernel
theorem subd13_2_114 : subd13_2 [0, -2, -3] = true := by decide +kernel
theorem subd13_2_115 : subd13_2 [0, -2, -2] = true := by decide +kernel
theorem subd13_2_116 : subd13_2 [0, -2, -1] = true := by decide +kernel
theorem subd13_2_117 : subd13_2 [0, -2, 0] = true := by decide +kernel
theorem subd13_2_118 : subd13_2 [0, -2, 1] = true := by decide +kernel
theorem subd13_2_119 : subd13_2 [0, -2, 2] = true := by decide +kernel
theorem subd13_2_120 : subd13_2 [0, -2, 3] = true := by decide +kernel
theorem subd13_2_121 : subd13_2 [0, -2, 4] = true := by decide +kernel
theorem subd13_2_122 : subd13_2 [0, -2, 5] = true := by decide +kernel
theorem subd13_2_123 : subd13_2 [0, -1, -8] = true := by decide +kernel
theorem subd13_2_124 : subd13_2 [0, -1, -7] = true := by decide +kernel
theorem subd13_2_125 : subd13_2 [0, -1, -6] = true := by decide +kernel
theorem subd13_2_126 : subd13_2 [0, -1, -5] = true := by decide +kernel
theorem subd13_2_127 : subd13_2 [0, -1, -4] = true := by decide +kernel
theorem sbd13_2_3 : ∀ q ∈ blkd13_2_3, subd13_2 q = true := by
  unfold blkd13_2_3
  exact List.forall_mem_cons.2 ⟨subd13_2_96, List.forall_mem_cons.2 ⟨subd13_2_97, List.forall_mem_cons.2 ⟨subd13_2_98, List.forall_mem_cons.2 ⟨subd13_2_99, List.forall_mem_cons.2 ⟨subd13_2_100, List.forall_mem_cons.2 ⟨subd13_2_101, List.forall_mem_cons.2 ⟨subd13_2_102, List.forall_mem_cons.2 ⟨subd13_2_103, List.forall_mem_cons.2 ⟨subd13_2_104, List.forall_mem_cons.2 ⟨subd13_2_105, List.forall_mem_cons.2 ⟨subd13_2_106, List.forall_mem_cons.2 ⟨subd13_2_107, List.forall_mem_cons.2 ⟨subd13_2_108, List.forall_mem_cons.2 ⟨subd13_2_109, List.forall_mem_cons.2 ⟨subd13_2_110, List.forall_mem_cons.2 ⟨subd13_2_111, List.forall_mem_cons.2 ⟨subd13_2_112, List.forall_mem_cons.2 ⟨subd13_2_113, List.forall_mem_cons.2 ⟨subd13_2_114, List.forall_mem_cons.2 ⟨subd13_2_115, List.forall_mem_cons.2 ⟨subd13_2_116, List.forall_mem_cons.2 ⟨subd13_2_117, List.forall_mem_cons.2 ⟨subd13_2_118, List.forall_mem_cons.2 ⟨subd13_2_119, List.forall_mem_cons.2 ⟨subd13_2_120, List.forall_mem_cons.2 ⟨subd13_2_121, List.forall_mem_cons.2 ⟨subd13_2_122, List.forall_mem_cons.2 ⟨subd13_2_123, List.forall_mem_cons.2 ⟨subd13_2_124, List.forall_mem_cons.2 ⟨subd13_2_125, List.forall_mem_cons.2 ⟨subd13_2_126, List.forall_mem_cons.2 ⟨subd13_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_128 : subd13_2 [0, -1, -3] = true := by decide +kernel
theorem subd13_2_129 : subd13_2 [0, -1, -2] = true := by decide +kernel
theorem subd13_2_130 : subd13_2 [0, -1, -1] = true := by decide +kernel
theorem subd13_2_131 : subd13_2 [0, -1, 0] = true := by decide +kernel
theorem subd13_2_132 : subd13_2 [0, -1, 1] = true := by decide +kernel
theorem subd13_2_133 : subd13_2 [0, -1, 2] = true := by decide +kernel
theorem subd13_2_134 : subd13_2 [0, -1, 3] = true := by decide +kernel
theorem subd13_2_135 : subd13_2 [0, -1, 4] = true := by decide +kernel
theorem subd13_2_136 : subd13_2 [0, -1, 5] = true := by decide +kernel
theorem subd13_2_137 : subd13_2 [0, -1, 6] = true := by decide +kernel
theorem subd13_2_138 : subd13_2 [0, 0, -7] = true := by decide +kernel
theorem subd13_2_139 : subd13_2 [0, 0, -6] = true := by decide +kernel
theorem subd13_2_140 : subd13_2 [0, 0, -5] = true := by decide +kernel
theorem subd13_2_141 : subd13_2 [0, 0, -4] = true := by decide +kernel
theorem subd13_2_142 : subd13_2 [0, 0, -3] = true := by decide +kernel
theorem subd13_2_143 : subd13_2 [0, 0, -2] = true := by decide +kernel
theorem subd13_2_144 : subd13_2 [0, 0, -1] = true := by decide +kernel
theorem subd13_2_145 : subd13_2 [0, 0, 0] = true := by decide +kernel
theorem subd13_2_146 : subd13_2 [0, 0, 1] = true := by decide +kernel
theorem subd13_2_147 : subd13_2 [0, 0, 2] = true := by decide +kernel
theorem subd13_2_148 : subd13_2 [0, 0, 3] = true := by decide +kernel
theorem subd13_2_149 : subd13_2 [0, 0, 4] = true := by decide +kernel
theorem subd13_2_150 : subd13_2 [0, 0, 5] = true := by decide +kernel
theorem subd13_2_151 : subd13_2 [0, 0, 6] = true := by decide +kernel
theorem subd13_2_152 : subd13_2 [0, 1, -7] = true := by decide +kernel
theorem subd13_2_153 : subd13_2 [0, 1, -6] = true := by decide +kernel
theorem subd13_2_154 : subd13_2 [0, 1, -5] = true := by decide +kernel
theorem subd13_2_155 : subd13_2 [0, 1, -4] = true := by decide +kernel
theorem subd13_2_156 : subd13_2 [0, 1, -3] = true := by decide +kernel
theorem subd13_2_157 : subd13_2 [0, 1, -2] = true := by decide +kernel
theorem subd13_2_158 : subd13_2 [0, 1, -1] = true := by decide +kernel
theorem subd13_2_159 : subd13_2 [0, 1, 0] = true := by decide +kernel
theorem sbd13_2_4 : ∀ q ∈ blkd13_2_4, subd13_2 q = true := by
  unfold blkd13_2_4
  exact List.forall_mem_cons.2 ⟨subd13_2_128, List.forall_mem_cons.2 ⟨subd13_2_129, List.forall_mem_cons.2 ⟨subd13_2_130, List.forall_mem_cons.2 ⟨subd13_2_131, List.forall_mem_cons.2 ⟨subd13_2_132, List.forall_mem_cons.2 ⟨subd13_2_133, List.forall_mem_cons.2 ⟨subd13_2_134, List.forall_mem_cons.2 ⟨subd13_2_135, List.forall_mem_cons.2 ⟨subd13_2_136, List.forall_mem_cons.2 ⟨subd13_2_137, List.forall_mem_cons.2 ⟨subd13_2_138, List.forall_mem_cons.2 ⟨subd13_2_139, List.forall_mem_cons.2 ⟨subd13_2_140, List.forall_mem_cons.2 ⟨subd13_2_141, List.forall_mem_cons.2 ⟨subd13_2_142, List.forall_mem_cons.2 ⟨subd13_2_143, List.forall_mem_cons.2 ⟨subd13_2_144, List.forall_mem_cons.2 ⟨subd13_2_145, List.forall_mem_cons.2 ⟨subd13_2_146, List.forall_mem_cons.2 ⟨subd13_2_147, List.forall_mem_cons.2 ⟨subd13_2_148, List.forall_mem_cons.2 ⟨subd13_2_149, List.forall_mem_cons.2 ⟨subd13_2_150, List.forall_mem_cons.2 ⟨subd13_2_151, List.forall_mem_cons.2 ⟨subd13_2_152, List.forall_mem_cons.2 ⟨subd13_2_153, List.forall_mem_cons.2 ⟨subd13_2_154, List.forall_mem_cons.2 ⟨subd13_2_155, List.forall_mem_cons.2 ⟨subd13_2_156, List.forall_mem_cons.2 ⟨subd13_2_157, List.forall_mem_cons.2 ⟨subd13_2_158, List.forall_mem_cons.2 ⟨subd13_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_160 : subd13_2 [0, 1, 1] = true := by decide +kernel
theorem subd13_2_161 : subd13_2 [0, 1, 2] = true := by decide +kernel
theorem subd13_2_162 : subd13_2 [0, 1, 3] = true := by decide +kernel
theorem subd13_2_163 : subd13_2 [0, 1, 4] = true := by decide +kernel
theorem subd13_2_164 : subd13_2 [0, 1, 5] = true := by decide +kernel
theorem subd13_2_165 : subd13_2 [0, 1, 6] = true := by decide +kernel
theorem subd13_2_166 : subd13_2 [0, 1, 7] = true := by decide +kernel
theorem subd13_2_167 : subd13_2 [0, 2, -6] = true := by decide +kernel
theorem subd13_2_168 : subd13_2 [0, 2, -5] = true := by decide +kernel
theorem subd13_2_169 : subd13_2 [0, 2, -4] = true := by decide +kernel
theorem subd13_2_170 : subd13_2 [0, 2, -3] = true := by decide +kernel
theorem subd13_2_171 : subd13_2 [0, 2, -2] = true := by decide +kernel
theorem subd13_2_172 : subd13_2 [0, 2, -1] = true := by decide +kernel
theorem subd13_2_173 : subd13_2 [0, 2, 0] = true := by decide +kernel
theorem subd13_2_174 : subd13_2 [0, 2, 1] = true := by decide +kernel
theorem subd13_2_175 : subd13_2 [0, 2, 2] = true := by decide +kernel
theorem subd13_2_176 : subd13_2 [0, 2, 3] = true := by decide +kernel
theorem subd13_2_177 : subd13_2 [0, 2, 4] = true := by decide +kernel
theorem subd13_2_178 : subd13_2 [0, 2, 5] = true := by decide +kernel
theorem subd13_2_179 : subd13_2 [0, 2, 6] = true := by decide +kernel
theorem subd13_2_180 : subd13_2 [0, 2, 7] = true := by decide +kernel
theorem subd13_2_181 : subd13_2 [0, 3] = true := by decide +kernel
theorem subd13_2_182 : subd13_2 [0, 4] = true := by decide +kernel
theorem subd13_2_183 : subd13_2 [0, 5] = true := by decide +kernel
theorem subd13_2_184 : subd13_2 [1, -6] = true := by decide +kernel
theorem subd13_2_185 : subd13_2 [1, -5] = true := by decide +kernel
theorem subd13_2_186 : subd13_2 [1, -4] = true := by decide +kernel
theorem subd13_2_187 : subd13_2 [1, -3] = true := by decide +kernel
theorem subd13_2_188 : subd13_2 [1, -2, -8] = true := by decide +kernel
theorem subd13_2_189 : subd13_2 [1, -2, -7] = true := by decide +kernel
theorem subd13_2_190 : subd13_2 [1, -2, -6] = true := by decide +kernel
theorem subd13_2_191 : subd13_2 [1, -2, -5] = true := by decide +kernel
theorem sbd13_2_5 : ∀ q ∈ blkd13_2_5, subd13_2 q = true := by
  unfold blkd13_2_5
  exact List.forall_mem_cons.2 ⟨subd13_2_160, List.forall_mem_cons.2 ⟨subd13_2_161, List.forall_mem_cons.2 ⟨subd13_2_162, List.forall_mem_cons.2 ⟨subd13_2_163, List.forall_mem_cons.2 ⟨subd13_2_164, List.forall_mem_cons.2 ⟨subd13_2_165, List.forall_mem_cons.2 ⟨subd13_2_166, List.forall_mem_cons.2 ⟨subd13_2_167, List.forall_mem_cons.2 ⟨subd13_2_168, List.forall_mem_cons.2 ⟨subd13_2_169, List.forall_mem_cons.2 ⟨subd13_2_170, List.forall_mem_cons.2 ⟨subd13_2_171, List.forall_mem_cons.2 ⟨subd13_2_172, List.forall_mem_cons.2 ⟨subd13_2_173, List.forall_mem_cons.2 ⟨subd13_2_174, List.forall_mem_cons.2 ⟨subd13_2_175, List.forall_mem_cons.2 ⟨subd13_2_176, List.forall_mem_cons.2 ⟨subd13_2_177, List.forall_mem_cons.2 ⟨subd13_2_178, List.forall_mem_cons.2 ⟨subd13_2_179, List.forall_mem_cons.2 ⟨subd13_2_180, List.forall_mem_cons.2 ⟨subd13_2_181, List.forall_mem_cons.2 ⟨subd13_2_182, List.forall_mem_cons.2 ⟨subd13_2_183, List.forall_mem_cons.2 ⟨subd13_2_184, List.forall_mem_cons.2 ⟨subd13_2_185, List.forall_mem_cons.2 ⟨subd13_2_186, List.forall_mem_cons.2 ⟨subd13_2_187, List.forall_mem_cons.2 ⟨subd13_2_188, List.forall_mem_cons.2 ⟨subd13_2_189, List.forall_mem_cons.2 ⟨subd13_2_190, List.forall_mem_cons.2 ⟨subd13_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_192 : subd13_2 [1, -2, -4] = true := by decide +kernel
theorem subd13_2_193 : subd13_2 [1, -2, -3] = true := by decide +kernel
theorem subd13_2_194 : subd13_2 [1, -2, -2] = true := by decide +kernel
theorem subd13_2_195 : subd13_2 [1, -2, -1] = true := by decide +kernel
theorem subd13_2_196 : subd13_2 [1, -2, 0] = true := by decide +kernel
theorem subd13_2_197 : subd13_2 [1, -2, 1] = true := by decide +kernel
theorem subd13_2_198 : subd13_2 [1, -2, 2] = true := by decide +kernel
theorem subd13_2_199 : subd13_2 [1, -2, 3] = true := by decide +kernel
theorem subd13_2_200 : subd13_2 [1, -2, 4] = true := by decide +kernel
theorem subd13_2_201 : subd13_2 [1, -1, -8] = true := by decide +kernel
theorem subd13_2_202 : subd13_2 [1, -1, -7] = true := by decide +kernel
theorem subd13_2_203 : subd13_2 [1, -1, -6] = true := by decide +kernel
theorem subd13_2_204 : subd13_2 [1, -1, -5] = true := by decide +kernel
theorem subd13_2_205 : subd13_2 [1, -1, -4] = true := by decide +kernel
theorem subd13_2_206 : subd13_2 [1, -1, -3] = true := by decide +kernel
theorem subd13_2_207 : subd13_2 [1, -1, -2] = true := by decide +kernel
theorem subd13_2_208 : subd13_2 [1, -1, -1] = true := by decide +kernel
theorem subd13_2_209 : subd13_2 [1, -1, 0] = true := by decide +kernel
theorem subd13_2_210 : subd13_2 [1, -1, 1] = true := by decide +kernel
theorem subd13_2_211 : subd13_2 [1, -1, 2] = true := by decide +kernel
theorem subd13_2_212 : subd13_2 [1, -1, 3] = true := by decide +kernel
theorem subd13_2_213 : subd13_2 [1, -1, 4] = true := by decide +kernel
theorem subd13_2_214 : subd13_2 [1, -1, 5] = true := by decide +kernel
theorem subd13_2_215 : subd13_2 [1, 0, -7] = true := by decide +kernel
theorem subd13_2_216 : subd13_2 [1, 0, -6] = true := by decide +kernel
theorem subd13_2_217 : subd13_2 [1, 0, -5] = true := by decide +kernel
theorem subd13_2_218 : subd13_2 [1, 0, -4] = true := by decide +kernel
theorem subd13_2_219 : subd13_2 [1, 0, -3] = true := by decide +kernel
theorem subd13_2_220 : subd13_2 [1, 0, -2] = true := by decide +kernel
theorem subd13_2_221 : subd13_2 [1, 0, -1] = true := by decide +kernel
theorem subd13_2_222 : subd13_2 [1, 0, 0] = true := by decide +kernel
theorem subd13_2_223 : subd13_2 [1, 0, 1] = true := by decide +kernel
theorem sbd13_2_6 : ∀ q ∈ blkd13_2_6, subd13_2 q = true := by
  unfold blkd13_2_6
  exact List.forall_mem_cons.2 ⟨subd13_2_192, List.forall_mem_cons.2 ⟨subd13_2_193, List.forall_mem_cons.2 ⟨subd13_2_194, List.forall_mem_cons.2 ⟨subd13_2_195, List.forall_mem_cons.2 ⟨subd13_2_196, List.forall_mem_cons.2 ⟨subd13_2_197, List.forall_mem_cons.2 ⟨subd13_2_198, List.forall_mem_cons.2 ⟨subd13_2_199, List.forall_mem_cons.2 ⟨subd13_2_200, List.forall_mem_cons.2 ⟨subd13_2_201, List.forall_mem_cons.2 ⟨subd13_2_202, List.forall_mem_cons.2 ⟨subd13_2_203, List.forall_mem_cons.2 ⟨subd13_2_204, List.forall_mem_cons.2 ⟨subd13_2_205, List.forall_mem_cons.2 ⟨subd13_2_206, List.forall_mem_cons.2 ⟨subd13_2_207, List.forall_mem_cons.2 ⟨subd13_2_208, List.forall_mem_cons.2 ⟨subd13_2_209, List.forall_mem_cons.2 ⟨subd13_2_210, List.forall_mem_cons.2 ⟨subd13_2_211, List.forall_mem_cons.2 ⟨subd13_2_212, List.forall_mem_cons.2 ⟨subd13_2_213, List.forall_mem_cons.2 ⟨subd13_2_214, List.forall_mem_cons.2 ⟨subd13_2_215, List.forall_mem_cons.2 ⟨subd13_2_216, List.forall_mem_cons.2 ⟨subd13_2_217, List.forall_mem_cons.2 ⟨subd13_2_218, List.forall_mem_cons.2 ⟨subd13_2_219, List.forall_mem_cons.2 ⟨subd13_2_220, List.forall_mem_cons.2 ⟨subd13_2_221, List.forall_mem_cons.2 ⟨subd13_2_222, List.forall_mem_cons.2 ⟨subd13_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_224 : subd13_2 [1, 0, 2] = true := by decide +kernel
theorem subd13_2_225 : subd13_2 [1, 0, 3] = true := by decide +kernel
theorem subd13_2_226 : subd13_2 [1, 0, 4] = true := by decide +kernel
theorem subd13_2_227 : subd13_2 [1, 0, 5] = true := by decide +kernel
theorem subd13_2_228 : subd13_2 [1, 0, 6] = true := by decide +kernel
theorem subd13_2_229 : subd13_2 [1, 1, -7] = true := by decide +kernel
theorem subd13_2_230 : subd13_2 [1, 1, -6] = true := by decide +kernel
theorem subd13_2_231 : subd13_2 [1, 1, -5] = true := by decide +kernel
theorem subd13_2_232 : subd13_2 [1, 1, -4] = true := by decide +kernel
theorem subd13_2_233 : subd13_2 [1, 1, -3] = true := by decide +kernel
theorem subd13_2_234 : subd13_2 [1, 1, -2] = true := by decide +kernel
theorem subd13_2_235 : subd13_2 [1, 1, -1] = true := by decide +kernel
theorem subd13_2_236 : subd13_2 [1, 1, 0] = true := by decide +kernel
theorem subd13_2_237 : subd13_2 [1, 1, 1] = true := by decide +kernel
theorem subd13_2_238 : subd13_2 [1, 1, 2] = true := by decide +kernel
theorem subd13_2_239 : subd13_2 [1, 1, 3] = true := by decide +kernel
theorem subd13_2_240 : subd13_2 [1, 1, 4] = true := by decide +kernel
theorem subd13_2_241 : subd13_2 [1, 1, 5] = true := by decide +kernel
theorem subd13_2_242 : subd13_2 [1, 1, 6] = true := by decide +kernel
theorem subd13_2_243 : subd13_2 [1, 2] = true := by decide +kernel
theorem subd13_2_244 : subd13_2 [1, 3] = true := by decide +kernel
theorem subd13_2_245 : subd13_2 [1, 4] = true := by decide +kernel
theorem subd13_2_246 : subd13_2 [1, 5] = true := by decide +kernel
theorem subd13_2_247 : subd13_2 [2, -6] = true := by decide +kernel
theorem subd13_2_248 : subd13_2 [2, -5] = true := by decide +kernel
theorem subd13_2_249 : subd13_2 [2, -4] = true := by decide +kernel
theorem subd13_2_250 : subd13_2 [2, -3] = true := by decide +kernel
theorem subd13_2_251 : subd13_2 [2, -2] = true := by decide +kernel
theorem subd13_2_252 : subd13_2 [2, -1] = true := by decide +kernel
theorem subd13_2_253 : subd13_2 [2, 0, -7] = true := by decide +kernel
theorem subd13_2_254 : subd13_2 [2, 0, -6] = true := by decide +kernel
theorem subd13_2_255 : subd13_2 [2, 0, -5] = true := by decide +kernel
theorem sbd13_2_7 : ∀ q ∈ blkd13_2_7, subd13_2 q = true := by
  unfold blkd13_2_7
  exact List.forall_mem_cons.2 ⟨subd13_2_224, List.forall_mem_cons.2 ⟨subd13_2_225, List.forall_mem_cons.2 ⟨subd13_2_226, List.forall_mem_cons.2 ⟨subd13_2_227, List.forall_mem_cons.2 ⟨subd13_2_228, List.forall_mem_cons.2 ⟨subd13_2_229, List.forall_mem_cons.2 ⟨subd13_2_230, List.forall_mem_cons.2 ⟨subd13_2_231, List.forall_mem_cons.2 ⟨subd13_2_232, List.forall_mem_cons.2 ⟨subd13_2_233, List.forall_mem_cons.2 ⟨subd13_2_234, List.forall_mem_cons.2 ⟨subd13_2_235, List.forall_mem_cons.2 ⟨subd13_2_236, List.forall_mem_cons.2 ⟨subd13_2_237, List.forall_mem_cons.2 ⟨subd13_2_238, List.forall_mem_cons.2 ⟨subd13_2_239, List.forall_mem_cons.2 ⟨subd13_2_240, List.forall_mem_cons.2 ⟨subd13_2_241, List.forall_mem_cons.2 ⟨subd13_2_242, List.forall_mem_cons.2 ⟨subd13_2_243, List.forall_mem_cons.2 ⟨subd13_2_244, List.forall_mem_cons.2 ⟨subd13_2_245, List.forall_mem_cons.2 ⟨subd13_2_246, List.forall_mem_cons.2 ⟨subd13_2_247, List.forall_mem_cons.2 ⟨subd13_2_248, List.forall_mem_cons.2 ⟨subd13_2_249, List.forall_mem_cons.2 ⟨subd13_2_250, List.forall_mem_cons.2 ⟨subd13_2_251, List.forall_mem_cons.2 ⟨subd13_2_252, List.forall_mem_cons.2 ⟨subd13_2_253, List.forall_mem_cons.2 ⟨subd13_2_254, List.forall_mem_cons.2 ⟨subd13_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_256 : subd13_2 [2, 0, -4] = true := by decide +kernel
theorem subd13_2_257 : subd13_2 [2, 0, -3] = true := by decide +kernel
theorem subd13_2_258 : subd13_2 [2, 0, -2] = true := by decide +kernel
theorem subd13_2_259 : subd13_2 [2, 0, -1] = true := by decide +kernel
theorem subd13_2_260 : subd13_2 [2, 0, 0] = true := by decide +kernel
theorem subd13_2_261 : subd13_2 [2, 0, 1] = true := by decide +kernel
theorem subd13_2_262 : subd13_2 [2, 0, 2] = true := by decide +kernel
theorem subd13_2_263 : subd13_2 [2, 0, 3] = true := by decide +kernel
theorem subd13_2_264 : subd13_2 [2, 0, 4] = true := by decide +kernel
theorem subd13_2_265 : subd13_2 [2, 0, 5] = true := by decide +kernel
theorem subd13_2_266 : subd13_2 [2, 1] = true := by decide +kernel
theorem subd13_2_267 : subd13_2 [2, 2] = true := by decide +kernel
theorem subd13_2_268 : subd13_2 [2, 3] = true := by decide +kernel
theorem subd13_2_269 : subd13_2 [2, 4] = true := by decide +kernel
theorem subd13_2_270 : subd13_2 [3, -5] = true := by decide +kernel
theorem subd13_2_271 : subd13_2 [3, -4] = true := by decide +kernel
theorem subd13_2_272 : subd13_2 [3, -3] = true := by decide +kernel
theorem subd13_2_273 : subd13_2 [3, -2] = true := by decide +kernel
theorem subd13_2_274 : subd13_2 [3, -1] = true := by decide +kernel
theorem subd13_2_275 : subd13_2 [3, 0] = true := by decide +kernel
theorem subd13_2_276 : subd13_2 [3, 1] = true := by decide +kernel
theorem subd13_2_277 : subd13_2 [3, 2] = true := by decide +kernel
theorem subd13_2_278 : subd13_2 [3, 3] = true := by decide +kernel
theorem subd13_2_279 : subd13_2 [3, 4] = true := by decide +kernel
theorem subd13_2_280 : subd13_2 [4, -4] = true := by decide +kernel
theorem subd13_2_281 : subd13_2 [4, -3] = true := by decide +kernel
theorem subd13_2_282 : subd13_2 [4, -2] = true := by decide +kernel
theorem subd13_2_283 : subd13_2 [4, -1] = true := by decide +kernel
theorem subd13_2_284 : subd13_2 [4, 0] = true := by decide +kernel
theorem subd13_2_285 : subd13_2 [4, 1] = true := by decide +kernel
theorem subd13_2_286 : subd13_2 [4, 2] = true := by decide +kernel
theorem subd13_2_287 : subd13_2 [4, 3] = true := by decide +kernel
theorem sbd13_2_8 : ∀ q ∈ blkd13_2_8, subd13_2 q = true := by
  unfold blkd13_2_8
  exact List.forall_mem_cons.2 ⟨subd13_2_256, List.forall_mem_cons.2 ⟨subd13_2_257, List.forall_mem_cons.2 ⟨subd13_2_258, List.forall_mem_cons.2 ⟨subd13_2_259, List.forall_mem_cons.2 ⟨subd13_2_260, List.forall_mem_cons.2 ⟨subd13_2_261, List.forall_mem_cons.2 ⟨subd13_2_262, List.forall_mem_cons.2 ⟨subd13_2_263, List.forall_mem_cons.2 ⟨subd13_2_264, List.forall_mem_cons.2 ⟨subd13_2_265, List.forall_mem_cons.2 ⟨subd13_2_266, List.forall_mem_cons.2 ⟨subd13_2_267, List.forall_mem_cons.2 ⟨subd13_2_268, List.forall_mem_cons.2 ⟨subd13_2_269, List.forall_mem_cons.2 ⟨subd13_2_270, List.forall_mem_cons.2 ⟨subd13_2_271, List.forall_mem_cons.2 ⟨subd13_2_272, List.forall_mem_cons.2 ⟨subd13_2_273, List.forall_mem_cons.2 ⟨subd13_2_274, List.forall_mem_cons.2 ⟨subd13_2_275, List.forall_mem_cons.2 ⟨subd13_2_276, List.forall_mem_cons.2 ⟨subd13_2_277, List.forall_mem_cons.2 ⟨subd13_2_278, List.forall_mem_cons.2 ⟨subd13_2_279, List.forall_mem_cons.2 ⟨subd13_2_280, List.forall_mem_cons.2 ⟨subd13_2_281, List.forall_mem_cons.2 ⟨subd13_2_282, List.forall_mem_cons.2 ⟨subd13_2_283, List.forall_mem_cons.2 ⟨subd13_2_284, List.forall_mem_cons.2 ⟨subd13_2_285, List.forall_mem_cons.2 ⟨subd13_2_286, List.forall_mem_cons.2 ⟨subd13_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_288 : subd13_2 [5] = true := by decide +kernel
theorem sbd13_2_9 : ∀ q ∈ blkd13_2_9, subd13_2 q = true := by
  unfold blkd13_2_9
  exact List.forall_mem_cons.2 ⟨subd13_2_288, List.forall_mem_nil _⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
