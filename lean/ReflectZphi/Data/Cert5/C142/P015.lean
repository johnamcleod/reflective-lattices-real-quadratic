import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_32 : subd10_2 [-2, 0, -8] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [-2, 0, -7] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [-2, 0, -6] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [-2, 0, -5] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [-2, 0, -4] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [-2, 0, -3] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [-2, 0, -2] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [-2, 0, -1] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [-2, 0, 0] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [-2, 0, 1] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [-2, 0, 2] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [-2, 0, 3] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [-2, 0, 4] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [-2, 0, 5] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [-2, 0, 6] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [-2, 1, -9] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [-2, 1, -8] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [-2, 1, -7] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [-2, 1, -6] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [-2, 1, -5] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [-2, 1, -4] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [-2, 1, -3] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [-2, 1, -2] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [-2, 1, -1] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [-2, 1, 0] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [-2, 1, 1] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [-2, 1, 2] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [-2, 1, 3] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [-2, 1, 4] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [-2, 1, 5] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [-2, 1, 6] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [-2, 2, -9] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [-2, 2, -8] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [-2, 2, -7] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [-2, 2, -6] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [-2, 2, -5] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [-2, 2, -4] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [-2, 2, -3] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [-2, 2, -2] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [-2, 2, -1] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [-2, 2, 0] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [-2, 2, 1] = true := by decide +kernel
theorem subd10_2_74 : subd10_2 [-2, 2, 2] = true := by decide +kernel
theorem subd10_2_75 : subd10_2 [-2, 2, 3] = true := by decide +kernel
theorem subd10_2_76 : subd10_2 [-2, 2, 4] = true := by decide +kernel
theorem subd10_2_77 : subd10_2 [-2, 2, 5] = true := by decide +kernel
theorem subd10_2_78 : subd10_2 [-2, 3, -9] = true := by decide +kernel
theorem subd10_2_79 : subd10_2 [-2, 3, -8] = true := by decide +kernel
theorem subd10_2_80 : subd10_2 [-2, 3, -7] = true := by decide +kernel
theorem subd10_2_81 : subd10_2 [-2, 3, -6] = true := by decide +kernel
theorem subd10_2_82 : subd10_2 [-2, 3, -5] = true := by decide +kernel
theorem subd10_2_83 : subd10_2 [-2, 3, -4] = true := by decide +kernel
theorem subd10_2_84 : subd10_2 [-2, 3, -3] = true := by decide +kernel
theorem subd10_2_85 : subd10_2 [-2, 3, -2] = true := by decide +kernel
theorem subd10_2_86 : subd10_2 [-2, 3, -1] = true := by decide +kernel
theorem subd10_2_87 : subd10_2 [-2, 3, 0] = true := by decide +kernel
theorem subd10_2_88 : subd10_2 [-2, 3, 1] = true := by decide +kernel
theorem subd10_2_89 : subd10_2 [-2, 3, 2] = true := by decide +kernel
theorem subd10_2_90 : subd10_2 [-2, 3, 3] = true := by decide +kernel
theorem subd10_2_91 : subd10_2 [-2, 3, 4] = true := by decide +kernel
theorem subd10_2_92 : subd10_2 [-2, 4] = true := by decide +kernel
theorem subd10_2_93 : subd10_2 [-2, 5] = true := by decide +kernel
theorem subd10_2_94 : subd10_2 [-1, -5] = true := by decide +kernel
theorem subd10_2_95 : subd10_2 [-1, -4] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_cons.2 ⟨subd10_2_74, List.forall_mem_cons.2 ⟨subd10_2_75, List.forall_mem_cons.2 ⟨subd10_2_76, List.forall_mem_cons.2 ⟨subd10_2_77, List.forall_mem_cons.2 ⟨subd10_2_78, List.forall_mem_cons.2 ⟨subd10_2_79, List.forall_mem_cons.2 ⟨subd10_2_80, List.forall_mem_cons.2 ⟨subd10_2_81, List.forall_mem_cons.2 ⟨subd10_2_82, List.forall_mem_cons.2 ⟨subd10_2_83, List.forall_mem_cons.2 ⟨subd10_2_84, List.forall_mem_cons.2 ⟨subd10_2_85, List.forall_mem_cons.2 ⟨subd10_2_86, List.forall_mem_cons.2 ⟨subd10_2_87, List.forall_mem_cons.2 ⟨subd10_2_88, List.forall_mem_cons.2 ⟨subd10_2_89, List.forall_mem_cons.2 ⟨subd10_2_90, List.forall_mem_cons.2 ⟨subd10_2_91, List.forall_mem_cons.2 ⟨subd10_2_92, List.forall_mem_cons.2 ⟨subd10_2_93, List.forall_mem_cons.2 ⟨subd10_2_94, List.forall_mem_cons.2 ⟨subd10_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_96 : subd10_2 [-1, -3] = true := by decide +kernel
theorem subd10_2_97 : subd10_2 [-1, -2, -7] = true := by decide +kernel
theorem subd10_2_98 : subd10_2 [-1, -2, -6] = true := by decide +kernel
theorem subd10_2_99 : subd10_2 [-1, -2, -5] = true := by decide +kernel
theorem subd10_2_100 : subd10_2 [-1, -2, -4] = true := by decide +kernel
theorem subd10_2_101 : subd10_2 [-1, -2, -3] = true := by decide +kernel
theorem subd10_2_102 : subd10_2 [-1, -2, -2] = true := by decide +kernel
theorem subd10_2_103 : subd10_2 [-1, -2, -1] = true := by decide +kernel
theorem subd10_2_104 : subd10_2 [-1, -2, 0] = true := by decide +kernel
theorem subd10_2_105 : subd10_2 [-1, -2, 1] = true := by decide +kernel
theorem subd10_2_106 : subd10_2 [-1, -2, 2] = true := by decide +kernel
theorem subd10_2_107 : subd10_2 [-1, -2, 3] = true := by decide +kernel
theorem subd10_2_108 : subd10_2 [-1, -2, 4] = true := by decide +kernel
theorem subd10_2_109 : subd10_2 [-1, -2, 5] = true := by decide +kernel
theorem subd10_2_110 : subd10_2 [-1, -2, 6] = true := by decide +kernel
theorem subd10_2_111 : subd10_2 [-1, -2, 7] = true := by decide +kernel
theorem subd10_2_112 : subd10_2 [-1, -1, -8] = true := by decide +kernel
theorem subd10_2_113 : subd10_2 [-1, -1, -7] = true := by decide +kernel
theorem subd10_2_114 : subd10_2 [-1, -1, -6] = true := by decide +kernel
theorem subd10_2_115 : subd10_2 [-1, -1, -5] = true := by decide +kernel
theorem subd10_2_116 : subd10_2 [-1, -1, -4] = true := by decide +kernel
theorem subd10_2_117 : subd10_2 [-1, -1, -3] = true := by decide +kernel
theorem subd10_2_118 : subd10_2 [-1, -1, -2] = true := by decide +kernel
theorem subd10_2_119 : subd10_2 [-1, -1, -1] = true := by decide +kernel
theorem subd10_2_120 : subd10_2 [-1, -1, 0] = true := by decide +kernel
theorem subd10_2_121 : subd10_2 [-1, -1, 1] = true := by decide +kernel
theorem subd10_2_122 : subd10_2 [-1, -1, 2] = true := by decide +kernel
theorem subd10_2_123 : subd10_2 [-1, -1, 3] = true := by decide +kernel
theorem subd10_2_124 : subd10_2 [-1, -1, 4] = true := by decide +kernel
theorem subd10_2_125 : subd10_2 [-1, -1, 5] = true := by decide +kernel
theorem subd10_2_126 : subd10_2 [-1, -1, 6] = true := by decide +kernel
theorem subd10_2_127 : subd10_2 [-1, -1, 7] = true := by decide +kernel
theorem sbd10_2_3 : ∀ q ∈ blkd10_2_3, subd10_2 q = true := by
  unfold blkd10_2_3
  exact List.forall_mem_cons.2 ⟨subd10_2_96, List.forall_mem_cons.2 ⟨subd10_2_97, List.forall_mem_cons.2 ⟨subd10_2_98, List.forall_mem_cons.2 ⟨subd10_2_99, List.forall_mem_cons.2 ⟨subd10_2_100, List.forall_mem_cons.2 ⟨subd10_2_101, List.forall_mem_cons.2 ⟨subd10_2_102, List.forall_mem_cons.2 ⟨subd10_2_103, List.forall_mem_cons.2 ⟨subd10_2_104, List.forall_mem_cons.2 ⟨subd10_2_105, List.forall_mem_cons.2 ⟨subd10_2_106, List.forall_mem_cons.2 ⟨subd10_2_107, List.forall_mem_cons.2 ⟨subd10_2_108, List.forall_mem_cons.2 ⟨subd10_2_109, List.forall_mem_cons.2 ⟨subd10_2_110, List.forall_mem_cons.2 ⟨subd10_2_111, List.forall_mem_cons.2 ⟨subd10_2_112, List.forall_mem_cons.2 ⟨subd10_2_113, List.forall_mem_cons.2 ⟨subd10_2_114, List.forall_mem_cons.2 ⟨subd10_2_115, List.forall_mem_cons.2 ⟨subd10_2_116, List.forall_mem_cons.2 ⟨subd10_2_117, List.forall_mem_cons.2 ⟨subd10_2_118, List.forall_mem_cons.2 ⟨subd10_2_119, List.forall_mem_cons.2 ⟨subd10_2_120, List.forall_mem_cons.2 ⟨subd10_2_121, List.forall_mem_cons.2 ⟨subd10_2_122, List.forall_mem_cons.2 ⟨subd10_2_123, List.forall_mem_cons.2 ⟨subd10_2_124, List.forall_mem_cons.2 ⟨subd10_2_125, List.forall_mem_cons.2 ⟨subd10_2_126, List.forall_mem_cons.2 ⟨subd10_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_128 : subd10_2 [-1, 0, -9] = true := by decide +kernel
theorem subd10_2_129 : subd10_2 [-1, 0, -8] = true := by decide +kernel
theorem subd10_2_130 : subd10_2 [-1, 0, -7] = true := by decide +kernel
theorem subd10_2_131 : subd10_2 [-1, 0, -6] = true := by decide +kernel
theorem subd10_2_132 : subd10_2 [-1, 0, -5] = true := by decide +kernel
theorem subd10_2_133 : subd10_2 [-1, 0, -4] = true := by decide +kernel
theorem subd10_2_134 : subd10_2 [-1, 0, -3] = true := by decide +kernel
theorem subd10_2_135 : subd10_2 [-1, 0, -2] = true := by decide +kernel
theorem subd10_2_136 : subd10_2 [-1, 0, -1] = true := by decide +kernel
theorem subd10_2_137 : subd10_2 [-1, 0, 0] = true := by decide +kernel
theorem subd10_2_138 : subd10_2 [-1, 0, 1] = true := by decide +kernel
theorem subd10_2_139 : subd10_2 [-1, 0, 2] = true := by decide +kernel
theorem subd10_2_140 : subd10_2 [-1, 0, 3] = true := by decide +kernel
theorem subd10_2_141 : subd10_2 [-1, 0, 4] = true := by decide +kernel
theorem subd10_2_142 : subd10_2 [-1, 0, 5] = true := by decide +kernel
theorem subd10_2_143 : subd10_2 [-1, 0, 6] = true := by decide +kernel
theorem subd10_2_144 : subd10_2 [-1, 0, 7] = true := by decide +kernel
theorem subd10_2_145 : subd10_2 [-1, 1, -9] = true := by decide +kernel
theorem subd10_2_146 : subd10_2 [-1, 1, -8] = true := by decide +kernel
theorem subd10_2_147 : subd10_2 [-1, 1, -7] = true := by decide +kernel
theorem subd10_2_148 : subd10_2 [-1, 1, -6] = true := by decide +kernel
theorem subd10_2_149 : subd10_2 [-1, 1, -5] = true := by decide +kernel
theorem subd10_2_150 : subd10_2 [-1, 1, -4] = true := by decide +kernel
theorem subd10_2_151 : subd10_2 [-1, 1, -3] = true := by decide +kernel
theorem subd10_2_152 : subd10_2 [-1, 1, -2] = true := by decide +kernel
theorem subd10_2_153 : subd10_2 [-1, 1, -1] = true := by decide +kernel
theorem subd10_2_154 : subd10_2 [-1, 1, 0] = true := by decide +kernel
theorem subd10_2_155 : subd10_2 [-1, 1, 1] = true := by decide +kernel
theorem subd10_2_156 : subd10_2 [-1, 1, 2] = true := by decide +kernel
theorem subd10_2_157 : subd10_2 [-1, 1, 3] = true := by decide +kernel
theorem subd10_2_158 : subd10_2 [-1, 1, 4] = true := by decide +kernel
theorem subd10_2_159 : subd10_2 [-1, 1, 5] = true := by decide +kernel
theorem sbd10_2_4 : ∀ q ∈ blkd10_2_4, subd10_2 q = true := by
  unfold blkd10_2_4
  exact List.forall_mem_cons.2 ⟨subd10_2_128, List.forall_mem_cons.2 ⟨subd10_2_129, List.forall_mem_cons.2 ⟨subd10_2_130, List.forall_mem_cons.2 ⟨subd10_2_131, List.forall_mem_cons.2 ⟨subd10_2_132, List.forall_mem_cons.2 ⟨subd10_2_133, List.forall_mem_cons.2 ⟨subd10_2_134, List.forall_mem_cons.2 ⟨subd10_2_135, List.forall_mem_cons.2 ⟨subd10_2_136, List.forall_mem_cons.2 ⟨subd10_2_137, List.forall_mem_cons.2 ⟨subd10_2_138, List.forall_mem_cons.2 ⟨subd10_2_139, List.forall_mem_cons.2 ⟨subd10_2_140, List.forall_mem_cons.2 ⟨subd10_2_141, List.forall_mem_cons.2 ⟨subd10_2_142, List.forall_mem_cons.2 ⟨subd10_2_143, List.forall_mem_cons.2 ⟨subd10_2_144, List.forall_mem_cons.2 ⟨subd10_2_145, List.forall_mem_cons.2 ⟨subd10_2_146, List.forall_mem_cons.2 ⟨subd10_2_147, List.forall_mem_cons.2 ⟨subd10_2_148, List.forall_mem_cons.2 ⟨subd10_2_149, List.forall_mem_cons.2 ⟨subd10_2_150, List.forall_mem_cons.2 ⟨subd10_2_151, List.forall_mem_cons.2 ⟨subd10_2_152, List.forall_mem_cons.2 ⟨subd10_2_153, List.forall_mem_cons.2 ⟨subd10_2_154, List.forall_mem_cons.2 ⟨subd10_2_155, List.forall_mem_cons.2 ⟨subd10_2_156, List.forall_mem_cons.2 ⟨subd10_2_157, List.forall_mem_cons.2 ⟨subd10_2_158, List.forall_mem_cons.2 ⟨subd10_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_160 : subd10_2 [-1, 1, 6] = true := by decide +kernel
theorem subd10_2_161 : subd10_2 [-1, 1, 7] = true := by decide +kernel
theorem subd10_2_162 : subd10_2 [-1, 2, -9] = true := by decide +kernel
theorem subd10_2_163 : subd10_2 [-1, 2, -8] = true := by decide +kernel
theorem subd10_2_164 : subd10_2 [-1, 2, -7] = true := by decide +kernel
theorem subd10_2_165 : subd10_2 [-1, 2, -6] = true := by decide +kernel
theorem subd10_2_166 : subd10_2 [-1, 2, -5] = true := by decide +kernel
theorem subd10_2_167 : subd10_2 [-1, 2, -4] = true := by decide +kernel
theorem subd10_2_168 : subd10_2 [-1, 2, -3] = true := by decide +kernel
theorem subd10_2_169 : subd10_2 [-1, 2, -2] = true := by decide +kernel
theorem subd10_2_170 : subd10_2 [-1, 2, -1] = true := by decide +kernel
theorem subd10_2_171 : subd10_2 [-1, 2, 0] = true := by decide +kernel
theorem subd10_2_172 : subd10_2 [-1, 2, 1] = true := by decide +kernel
theorem subd10_2_173 : subd10_2 [-1, 2, 2] = true := by decide +kernel
theorem subd10_2_174 : subd10_2 [-1, 2, 3] = true := by decide +kernel
theorem subd10_2_175 : subd10_2 [-1, 2, 4] = true := by decide +kernel
theorem subd10_2_176 : subd10_2 [-1, 2, 5] = true := by decide +kernel
theorem subd10_2_177 : subd10_2 [-1, 2, 6] = true := by decide +kernel
theorem subd10_2_178 : subd10_2 [-1, 3, -9] = true := by decide +kernel
theorem subd10_2_179 : subd10_2 [-1, 3, -8] = true := by decide +kernel
theorem subd10_2_180 : subd10_2 [-1, 3, -7] = true := by decide +kernel
theorem subd10_2_181 : subd10_2 [-1, 3, -6] = true := by decide +kernel
theorem subd10_2_182 : subd10_2 [-1, 3, -5] = true := by decide +kernel
theorem subd10_2_183 : subd10_2 [-1, 3, -4] = true := by decide +kernel
theorem subd10_2_184 : subd10_2 [-1, 3, -3] = true := by decide +kernel
theorem subd10_2_185 : subd10_2 [-1, 3, -2] = true := by decide +kernel
theorem subd10_2_186 : subd10_2 [-1, 3, -1] = true := by decide +kernel
theorem subd10_2_187 : subd10_2 [-1, 3, 0] = true := by decide +kernel
theorem subd10_2_188 : subd10_2 [-1, 3, 1] = true := by decide +kernel
theorem subd10_2_189 : subd10_2 [-1, 3, 2] = true := by decide +kernel
theorem subd10_2_190 : subd10_2 [-1, 3, 3] = true := by decide +kernel
theorem subd10_2_191 : subd10_2 [-1, 3, 4] = true := by decide +kernel
theorem sbd10_2_5 : ∀ q ∈ blkd10_2_5, subd10_2 q = true := by
  unfold blkd10_2_5
  exact List.forall_mem_cons.2 ⟨subd10_2_160, List.forall_mem_cons.2 ⟨subd10_2_161, List.forall_mem_cons.2 ⟨subd10_2_162, List.forall_mem_cons.2 ⟨subd10_2_163, List.forall_mem_cons.2 ⟨subd10_2_164, List.forall_mem_cons.2 ⟨subd10_2_165, List.forall_mem_cons.2 ⟨subd10_2_166, List.forall_mem_cons.2 ⟨subd10_2_167, List.forall_mem_cons.2 ⟨subd10_2_168, List.forall_mem_cons.2 ⟨subd10_2_169, List.forall_mem_cons.2 ⟨subd10_2_170, List.forall_mem_cons.2 ⟨subd10_2_171, List.forall_mem_cons.2 ⟨subd10_2_172, List.forall_mem_cons.2 ⟨subd10_2_173, List.forall_mem_cons.2 ⟨subd10_2_174, List.forall_mem_cons.2 ⟨subd10_2_175, List.forall_mem_cons.2 ⟨subd10_2_176, List.forall_mem_cons.2 ⟨subd10_2_177, List.forall_mem_cons.2 ⟨subd10_2_178, List.forall_mem_cons.2 ⟨subd10_2_179, List.forall_mem_cons.2 ⟨subd10_2_180, List.forall_mem_cons.2 ⟨subd10_2_181, List.forall_mem_cons.2 ⟨subd10_2_182, List.forall_mem_cons.2 ⟨subd10_2_183, List.forall_mem_cons.2 ⟨subd10_2_184, List.forall_mem_cons.2 ⟨subd10_2_185, List.forall_mem_cons.2 ⟨subd10_2_186, List.forall_mem_cons.2 ⟨subd10_2_187, List.forall_mem_cons.2 ⟨subd10_2_188, List.forall_mem_cons.2 ⟨subd10_2_189, List.forall_mem_cons.2 ⟨subd10_2_190, List.forall_mem_cons.2 ⟨subd10_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_192 : subd10_2 [-1, 3, 5] = true := by decide +kernel
theorem subd10_2_193 : subd10_2 [-1, 4] = true := by decide +kernel
theorem subd10_2_194 : subd10_2 [-1, 5] = true := by decide +kernel
theorem subd10_2_195 : subd10_2 [0, -6] = true := by decide +kernel
theorem subd10_2_196 : subd10_2 [0, -5] = true := by decide +kernel
theorem subd10_2_197 : subd10_2 [0, -4] = true := by decide +kernel
theorem subd10_2_198 : subd10_2 [0, -3, -6] = true := by decide +kernel
theorem subd10_2_199 : subd10_2 [0, -3, -5] = true := by decide +kernel
theorem subd10_2_200 : subd10_2 [0, -3, -4] = true := by decide +kernel
theorem subd10_2_201 : subd10_2 [0, -3, -3] = true := by decide +kernel
theorem subd10_2_202 : subd10_2 [0, -3, -2] = true := by decide +kernel
theorem subd10_2_203 : subd10_2 [0, -3, -1] = true := by decide +kernel
theorem subd10_2_204 : subd10_2 [0, -3, 0] = true := by decide +kernel
theorem subd10_2_205 : subd10_2 [0, -3, 1] = true := by decide +kernel
theorem subd10_2_206 : subd10_2 [0, -3, 2] = true := by decide +kernel
theorem subd10_2_207 : subd10_2 [0, -3, 3] = true := by decide +kernel
theorem subd10_2_208 : subd10_2 [0, -3, 4] = true := by decide +kernel
theorem subd10_2_209 : subd10_2 [0, -3, 5] = true := by decide +kernel
theorem subd10_2_210 : subd10_2 [0, -3, 6] = true := by decide +kernel
theorem subd10_2_211 : subd10_2 [0, -3, 7] = true := by decide +kernel
theorem subd10_2_212 : subd10_2 [0, -2, -7] = true := by decide +kernel
theorem subd10_2_213 : subd10_2 [0, -2, -6] = true := by decide +kernel
theorem subd10_2_214 : subd10_2 [0, -2, -5] = true := by decide +kernel
theorem subd10_2_215 : subd10_2 [0, -2, -4] = true := by decide +kernel
theorem subd10_2_216 : subd10_2 [0, -2, -3] = true := by decide +kernel
theorem subd10_2_217 : subd10_2 [0, -2, -2] = true := by decide +kernel
theorem subd10_2_218 : subd10_2 [0, -2, -1] = true := by decide +kernel
theorem subd10_2_219 : subd10_2 [0, -2, 0] = true := by decide +kernel
theorem subd10_2_220 : subd10_2 [0, -2, 1] = true := by decide +kernel
theorem subd10_2_221 : subd10_2 [0, -2, 2] = true := by decide +kernel
theorem subd10_2_222 : subd10_2 [0, -2, 3] = true := by decide +kernel
theorem subd10_2_223 : subd10_2 [0, -2, 4] = true := by decide +kernel
theorem sbd10_2_6 : ∀ q ∈ blkd10_2_6, subd10_2 q = true := by
  unfold blkd10_2_6
  exact List.forall_mem_cons.2 ⟨subd10_2_192, List.forall_mem_cons.2 ⟨subd10_2_193, List.forall_mem_cons.2 ⟨subd10_2_194, List.forall_mem_cons.2 ⟨subd10_2_195, List.forall_mem_cons.2 ⟨subd10_2_196, List.forall_mem_cons.2 ⟨subd10_2_197, List.forall_mem_cons.2 ⟨subd10_2_198, List.forall_mem_cons.2 ⟨subd10_2_199, List.forall_mem_cons.2 ⟨subd10_2_200, List.forall_mem_cons.2 ⟨subd10_2_201, List.forall_mem_cons.2 ⟨subd10_2_202, List.forall_mem_cons.2 ⟨subd10_2_203, List.forall_mem_cons.2 ⟨subd10_2_204, List.forall_mem_cons.2 ⟨subd10_2_205, List.forall_mem_cons.2 ⟨subd10_2_206, List.forall_mem_cons.2 ⟨subd10_2_207, List.forall_mem_cons.2 ⟨subd10_2_208, List.forall_mem_cons.2 ⟨subd10_2_209, List.forall_mem_cons.2 ⟨subd10_2_210, List.forall_mem_cons.2 ⟨subd10_2_211, List.forall_mem_cons.2 ⟨subd10_2_212, List.forall_mem_cons.2 ⟨subd10_2_213, List.forall_mem_cons.2 ⟨subd10_2_214, List.forall_mem_cons.2 ⟨subd10_2_215, List.forall_mem_cons.2 ⟨subd10_2_216, List.forall_mem_cons.2 ⟨subd10_2_217, List.forall_mem_cons.2 ⟨subd10_2_218, List.forall_mem_cons.2 ⟨subd10_2_219, List.forall_mem_cons.2 ⟨subd10_2_220, List.forall_mem_cons.2 ⟨subd10_2_221, List.forall_mem_cons.2 ⟨subd10_2_222, List.forall_mem_cons.2 ⟨subd10_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_224 : subd10_2 [0, -2, 5] = true := by decide +kernel
theorem subd10_2_225 : subd10_2 [0, -2, 6] = true := by decide +kernel
theorem subd10_2_226 : subd10_2 [0, -2, 7] = true := by decide +kernel
theorem subd10_2_227 : subd10_2 [0, -2, 8] = true := by decide +kernel
theorem subd10_2_228 : subd10_2 [0, -1, -8] = true := by decide +kernel
theorem subd10_2_229 : subd10_2 [0, -1, -7] = true := by decide +kernel
theorem subd10_2_230 : subd10_2 [0, -1, -6] = true := by decide +kernel
theorem subd10_2_231 : subd10_2 [0, -1, -5] = true := by decide +kernel
theorem subd10_2_232 : subd10_2 [0, -1, -4] = true := by decide +kernel
theorem subd10_2_233 : subd10_2 [0, -1, -3] = true := by decide +kernel
theorem subd10_2_234 : subd10_2 [0, -1, -2] = true := by decide +kernel
theorem subd10_2_235 : subd10_2 [0, -1, -1] = true := by decide +kernel
theorem subd10_2_236 : subd10_2 [0, -1, 0] = true := by decide +kernel
theorem subd10_2_237 : subd10_2 [0, -1, 1] = true := by decide +kernel
theorem subd10_2_238 : subd10_2 [0, -1, 2] = true := by decide +kernel
theorem subd10_2_239 : subd10_2 [0, -1, 3] = true := by decide +kernel
theorem subd10_2_240 : subd10_2 [0, -1, 4] = true := by decide +kernel
theorem subd10_2_241 : subd10_2 [0, -1, 5] = true := by decide +kernel
theorem subd10_2_242 : subd10_2 [0, -1, 6] = true := by decide +kernel
theorem subd10_2_243 : subd10_2 [0, -1, 7] = true := by decide +kernel
theorem subd10_2_244 : subd10_2 [0, -1, 8] = true := by decide +kernel
theorem subd10_2_245 : subd10_2 [0, 0, -9] = true := by decide +kernel
theorem subd10_2_246 : subd10_2 [0, 0, -8] = true := by decide +kernel
theorem subd10_2_247 : subd10_2 [0, 0, -7] = true := by decide +kernel
theorem subd10_2_248 : subd10_2 [0, 0, -6] = true := by decide +kernel
theorem subd10_2_249 : subd10_2 [0, 0, -5] = true := by decide +kernel
theorem subd10_2_250 : subd10_2 [0, 0, -4] = true := by decide +kernel
theorem subd10_2_251 : subd10_2 [0, 0, -3] = true := by decide +kernel
theorem subd10_2_252 : subd10_2 [0, 0, -2] = true := by decide +kernel
theorem subd10_2_253 : subd10_2 [0, 0, -1] = true := by decide +kernel
theorem subd10_2_254 : subd10_2 [0, 0, 0] = true := by decide +kernel
theorem subd10_2_255 : subd10_2 [0, 0, 1] = true := by decide +kernel
theorem sbd10_2_7 : ∀ q ∈ blkd10_2_7, subd10_2 q = true := by
  unfold blkd10_2_7
  exact List.forall_mem_cons.2 ⟨subd10_2_224, List.forall_mem_cons.2 ⟨subd10_2_225, List.forall_mem_cons.2 ⟨subd10_2_226, List.forall_mem_cons.2 ⟨subd10_2_227, List.forall_mem_cons.2 ⟨subd10_2_228, List.forall_mem_cons.2 ⟨subd10_2_229, List.forall_mem_cons.2 ⟨subd10_2_230, List.forall_mem_cons.2 ⟨subd10_2_231, List.forall_mem_cons.2 ⟨subd10_2_232, List.forall_mem_cons.2 ⟨subd10_2_233, List.forall_mem_cons.2 ⟨subd10_2_234, List.forall_mem_cons.2 ⟨subd10_2_235, List.forall_mem_cons.2 ⟨subd10_2_236, List.forall_mem_cons.2 ⟨subd10_2_237, List.forall_mem_cons.2 ⟨subd10_2_238, List.forall_mem_cons.2 ⟨subd10_2_239, List.forall_mem_cons.2 ⟨subd10_2_240, List.forall_mem_cons.2 ⟨subd10_2_241, List.forall_mem_cons.2 ⟨subd10_2_242, List.forall_mem_cons.2 ⟨subd10_2_243, List.forall_mem_cons.2 ⟨subd10_2_244, List.forall_mem_cons.2 ⟨subd10_2_245, List.forall_mem_cons.2 ⟨subd10_2_246, List.forall_mem_cons.2 ⟨subd10_2_247, List.forall_mem_cons.2 ⟨subd10_2_248, List.forall_mem_cons.2 ⟨subd10_2_249, List.forall_mem_cons.2 ⟨subd10_2_250, List.forall_mem_cons.2 ⟨subd10_2_251, List.forall_mem_cons.2 ⟨subd10_2_252, List.forall_mem_cons.2 ⟨subd10_2_253, List.forall_mem_cons.2 ⟨subd10_2_254, List.forall_mem_cons.2 ⟨subd10_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_256 : subd10_2 [0, 0, 2] = true := by decide +kernel
theorem subd10_2_257 : subd10_2 [0, 0, 3] = true := by decide +kernel
theorem subd10_2_258 : subd10_2 [0, 0, 4] = true := by decide +kernel
theorem subd10_2_259 : subd10_2 [0, 0, 5] = true := by decide +kernel
theorem subd10_2_260 : subd10_2 [0, 0, 6] = true := by decide +kernel
theorem subd10_2_261 : subd10_2 [0, 0, 7] = true := by decide +kernel
theorem subd10_2_262 : subd10_2 [0, 0, 8] = true := by decide +kernel
theorem subd10_2_263 : subd10_2 [0, 1, -9] = true := by decide +kernel
theorem subd10_2_264 : subd10_2 [0, 1, -8] = true := by decide +kernel
theorem subd10_2_265 : subd10_2 [0, 1, -7] = true := by decide +kernel
theorem subd10_2_266 : subd10_2 [0, 1, -6] = true := by decide +kernel
theorem subd10_2_267 : subd10_2 [0, 1, -5] = true := by decide +kernel
theorem subd10_2_268 : subd10_2 [0, 1, -4] = true := by decide +kernel
theorem subd10_2_269 : subd10_2 [0, 1, -3] = true := by decide +kernel
theorem subd10_2_270 : subd10_2 [0, 1, -2] = true := by decide +kernel
theorem subd10_2_271 : subd10_2 [0, 1, -1] = true := by decide +kernel
theorem subd10_2_272 : subd10_2 [0, 1, 0] = true := by decide +kernel
theorem subd10_2_273 : subd10_2 [0, 1, 1] = true := by decide +kernel
theorem subd10_2_274 : subd10_2 [0, 1, 2] = true := by decide +kernel
theorem subd10_2_275 : subd10_2 [0, 1, 3] = true := by decide +kernel
theorem subd10_2_276 : subd10_2 [0, 1, 4] = true := by decide +kernel
theorem subd10_2_277 : subd10_2 [0, 1, 5] = true := by decide +kernel
theorem subd10_2_278 : subd10_2 [0, 1, 6] = true := by decide +kernel
theorem subd10_2_279 : subd10_2 [0, 1, 7] = true := by decide +kernel
theorem subd10_2_280 : subd10_2 [0, 2, -9] = true := by decide +kernel
theorem subd10_2_281 : subd10_2 [0, 2, -8] = true := by decide +kernel
theorem subd10_2_282 : subd10_2 [0, 2, -7] = true := by decide +kernel
theorem subd10_2_283 : subd10_2 [0, 2, -6] = true := by decide +kernel
theorem subd10_2_284 : subd10_2 [0, 2, -5] = true := by decide +kernel
theorem subd10_2_285 : subd10_2 [0, 2, -4] = true := by decide +kernel
theorem subd10_2_286 : subd10_2 [0, 2, -3] = true := by decide +kernel
theorem subd10_2_287 : subd10_2 [0, 2, -2] = true := by decide +kernel
theorem sbd10_2_8 : ∀ q ∈ blkd10_2_8, subd10_2 q = true := by
  unfold blkd10_2_8
  exact List.forall_mem_cons.2 ⟨subd10_2_256, List.forall_mem_cons.2 ⟨subd10_2_257, List.forall_mem_cons.2 ⟨subd10_2_258, List.forall_mem_cons.2 ⟨subd10_2_259, List.forall_mem_cons.2 ⟨subd10_2_260, List.forall_mem_cons.2 ⟨subd10_2_261, List.forall_mem_cons.2 ⟨subd10_2_262, List.forall_mem_cons.2 ⟨subd10_2_263, List.forall_mem_cons.2 ⟨subd10_2_264, List.forall_mem_cons.2 ⟨subd10_2_265, List.forall_mem_cons.2 ⟨subd10_2_266, List.forall_mem_cons.2 ⟨subd10_2_267, List.forall_mem_cons.2 ⟨subd10_2_268, List.forall_mem_cons.2 ⟨subd10_2_269, List.forall_mem_cons.2 ⟨subd10_2_270, List.forall_mem_cons.2 ⟨subd10_2_271, List.forall_mem_cons.2 ⟨subd10_2_272, List.forall_mem_cons.2 ⟨subd10_2_273, List.forall_mem_cons.2 ⟨subd10_2_274, List.forall_mem_cons.2 ⟨subd10_2_275, List.forall_mem_cons.2 ⟨subd10_2_276, List.forall_mem_cons.2 ⟨subd10_2_277, List.forall_mem_cons.2 ⟨subd10_2_278, List.forall_mem_cons.2 ⟨subd10_2_279, List.forall_mem_cons.2 ⟨subd10_2_280, List.forall_mem_cons.2 ⟨subd10_2_281, List.forall_mem_cons.2 ⟨subd10_2_282, List.forall_mem_cons.2 ⟨subd10_2_283, List.forall_mem_cons.2 ⟨subd10_2_284, List.forall_mem_cons.2 ⟨subd10_2_285, List.forall_mem_cons.2 ⟨subd10_2_286, List.forall_mem_cons.2 ⟨subd10_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_288 : subd10_2 [0, 2, -1] = true := by decide +kernel
theorem subd10_2_289 : subd10_2 [0, 2, 0] = true := by decide +kernel
theorem subd10_2_290 : subd10_2 [0, 2, 1] = true := by decide +kernel
theorem subd10_2_291 : subd10_2 [0, 2, 2] = true := by decide +kernel
theorem subd10_2_292 : subd10_2 [0, 2, 3] = true := by decide +kernel
theorem subd10_2_293 : subd10_2 [0, 2, 4] = true := by decide +kernel
theorem subd10_2_294 : subd10_2 [0, 2, 5] = true := by decide +kernel
theorem subd10_2_295 : subd10_2 [0, 2, 6] = true := by decide +kernel
theorem subd10_2_296 : subd10_2 [0, 3, -8] = true := by decide +kernel
theorem subd10_2_297 : subd10_2 [0, 3, -7] = true := by decide +kernel
theorem subd10_2_298 : subd10_2 [0, 3, -6] = true := by decide +kernel
theorem subd10_2_299 : subd10_2 [0, 3, -5] = true := by decide +kernel
theorem subd10_2_300 : subd10_2 [0, 3, -4] = true := by decide +kernel
theorem subd10_2_301 : subd10_2 [0, 3, -3] = true := by decide +kernel
theorem subd10_2_302 : subd10_2 [0, 3, -2] = true := by decide +kernel
theorem subd10_2_303 : subd10_2 [0, 3, -1] = true := by decide +kernel
theorem subd10_2_304 : subd10_2 [0, 3, 0] = true := by decide +kernel
theorem subd10_2_305 : subd10_2 [0, 3, 1] = true := by decide +kernel
theorem subd10_2_306 : subd10_2 [0, 3, 2] = true := by decide +kernel
theorem subd10_2_307 : subd10_2 [0, 3, 3] = true := by decide +kernel
theorem subd10_2_308 : subd10_2 [0, 3, 4] = true := by decide +kernel
theorem subd10_2_309 : subd10_2 [0, 3, 5] = true := by decide +kernel
theorem subd10_2_310 : subd10_2 [0, 4] = true := by decide +kernel
theorem subd10_2_311 : subd10_2 [0, 5] = true := by decide +kernel
theorem subd10_2_312 : subd10_2 [1, -6] = true := by decide +kernel
theorem subd10_2_313 : subd10_2 [1, -5] = true := by decide +kernel
theorem subd10_2_314 : subd10_2 [1, -4] = true := by decide +kernel
theorem subd10_2_315 : subd10_2 [1, -3, -6] = true := by decide +kernel
theorem subd10_2_316 : subd10_2 [1, -3, -5] = true := by decide +kernel
theorem subd10_2_317 : subd10_2 [1, -3, -4] = true := by decide +kernel
theorem subd10_2_318 : subd10_2 [1, -3, -3] = true := by decide +kernel
theorem subd10_2_319 : subd10_2 [1, -3, -2] = true := by decide +kernel
theorem sbd10_2_9 : ∀ q ∈ blkd10_2_9, subd10_2 q = true := by
  unfold blkd10_2_9
  exact List.forall_mem_cons.2 ⟨subd10_2_288, List.forall_mem_cons.2 ⟨subd10_2_289, List.forall_mem_cons.2 ⟨subd10_2_290, List.forall_mem_cons.2 ⟨subd10_2_291, List.forall_mem_cons.2 ⟨subd10_2_292, List.forall_mem_cons.2 ⟨subd10_2_293, List.forall_mem_cons.2 ⟨subd10_2_294, List.forall_mem_cons.2 ⟨subd10_2_295, List.forall_mem_cons.2 ⟨subd10_2_296, List.forall_mem_cons.2 ⟨subd10_2_297, List.forall_mem_cons.2 ⟨subd10_2_298, List.forall_mem_cons.2 ⟨subd10_2_299, List.forall_mem_cons.2 ⟨subd10_2_300, List.forall_mem_cons.2 ⟨subd10_2_301, List.forall_mem_cons.2 ⟨subd10_2_302, List.forall_mem_cons.2 ⟨subd10_2_303, List.forall_mem_cons.2 ⟨subd10_2_304, List.forall_mem_cons.2 ⟨subd10_2_305, List.forall_mem_cons.2 ⟨subd10_2_306, List.forall_mem_cons.2 ⟨subd10_2_307, List.forall_mem_cons.2 ⟨subd10_2_308, List.forall_mem_cons.2 ⟨subd10_2_309, List.forall_mem_cons.2 ⟨subd10_2_310, List.forall_mem_cons.2 ⟨subd10_2_311, List.forall_mem_cons.2 ⟨subd10_2_312, List.forall_mem_cons.2 ⟨subd10_2_313, List.forall_mem_cons.2 ⟨subd10_2_314, List.forall_mem_cons.2 ⟨subd10_2_315, List.forall_mem_cons.2 ⟨subd10_2_316, List.forall_mem_cons.2 ⟨subd10_2_317, List.forall_mem_cons.2 ⟨subd10_2_318, List.forall_mem_cons.2 ⟨subd10_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_320 : subd10_2 [1, -3, -1] = true := by decide +kernel
theorem subd10_2_321 : subd10_2 [1, -3, 0] = true := by decide +kernel
theorem subd10_2_322 : subd10_2 [1, -3, 1] = true := by decide +kernel
theorem subd10_2_323 : subd10_2 [1, -3, 2] = true := by decide +kernel
theorem subd10_2_324 : subd10_2 [1, -3, 3] = true := by decide +kernel
theorem subd10_2_325 : subd10_2 [1, -3, 4] = true := by decide +kernel
theorem subd10_2_326 : subd10_2 [1, -3, 5] = true := by decide +kernel
theorem subd10_2_327 : subd10_2 [1, -3, 6] = true := by decide +kernel
theorem subd10_2_328 : subd10_2 [1, -3, 7] = true := by decide +kernel
theorem subd10_2_329 : subd10_2 [1, -3, 8] = true := by decide +kernel
theorem subd10_2_330 : subd10_2 [1, -2, -7] = true := by decide +kernel
theorem subd10_2_331 : subd10_2 [1, -2, -6] = true := by decide +kernel
theorem subd10_2_332 : subd10_2 [1, -2, -5] = true := by decide +kernel
theorem subd10_2_333 : subd10_2 [1, -2, -4] = true := by decide +kernel
theorem subd10_2_334 : subd10_2 [1, -2, -3] = true := by decide +kernel
theorem subd10_2_335 : subd10_2 [1, -2, -2] = true := by decide +kernel
theorem subd10_2_336 : subd10_2 [1, -2, -1] = true := by decide +kernel
theorem subd10_2_337 : subd10_2 [1, -2, 0] = true := by decide +kernel
theorem subd10_2_338 : subd10_2 [1, -2, 1] = true := by decide +kernel
theorem subd10_2_339 : subd10_2 [1, -2, 2] = true := by decide +kernel
theorem subd10_2_340 : subd10_2 [1, -2, 3] = true := by decide +kernel
theorem subd10_2_341 : subd10_2 [1, -2, 4] = true := by decide +kernel
theorem subd10_2_342 : subd10_2 [1, -2, 5] = true := by decide +kernel
theorem subd10_2_343 : subd10_2 [1, -2, 6] = true := by decide +kernel
theorem subd10_2_344 : subd10_2 [1, -2, 7] = true := by decide +kernel
theorem subd10_2_345 : subd10_2 [1, -2, 8] = true := by decide +kernel
theorem subd10_2_346 : subd10_2 [1, -1, -8] = true := by decide +kernel
theorem subd10_2_347 : subd10_2 [1, -1, -7] = true := by decide +kernel
theorem subd10_2_348 : subd10_2 [1, -1, -6] = true := by decide +kernel
theorem subd10_2_349 : subd10_2 [1, -1, -5] = true := by decide +kernel
theorem subd10_2_350 : subd10_2 [1, -1, -4] = true := by decide +kernel
theorem subd10_2_351 : subd10_2 [1, -1, -3] = true := by decide +kernel
theorem sbd10_2_10 : ∀ q ∈ blkd10_2_10, subd10_2 q = true := by
  unfold blkd10_2_10
  exact List.forall_mem_cons.2 ⟨subd10_2_320, List.forall_mem_cons.2 ⟨subd10_2_321, List.forall_mem_cons.2 ⟨subd10_2_322, List.forall_mem_cons.2 ⟨subd10_2_323, List.forall_mem_cons.2 ⟨subd10_2_324, List.forall_mem_cons.2 ⟨subd10_2_325, List.forall_mem_cons.2 ⟨subd10_2_326, List.forall_mem_cons.2 ⟨subd10_2_327, List.forall_mem_cons.2 ⟨subd10_2_328, List.forall_mem_cons.2 ⟨subd10_2_329, List.forall_mem_cons.2 ⟨subd10_2_330, List.forall_mem_cons.2 ⟨subd10_2_331, List.forall_mem_cons.2 ⟨subd10_2_332, List.forall_mem_cons.2 ⟨subd10_2_333, List.forall_mem_cons.2 ⟨subd10_2_334, List.forall_mem_cons.2 ⟨subd10_2_335, List.forall_mem_cons.2 ⟨subd10_2_336, List.forall_mem_cons.2 ⟨subd10_2_337, List.forall_mem_cons.2 ⟨subd10_2_338, List.forall_mem_cons.2 ⟨subd10_2_339, List.forall_mem_cons.2 ⟨subd10_2_340, List.forall_mem_cons.2 ⟨subd10_2_341, List.forall_mem_cons.2 ⟨subd10_2_342, List.forall_mem_cons.2 ⟨subd10_2_343, List.forall_mem_cons.2 ⟨subd10_2_344, List.forall_mem_cons.2 ⟨subd10_2_345, List.forall_mem_cons.2 ⟨subd10_2_346, List.forall_mem_cons.2 ⟨subd10_2_347, List.forall_mem_cons.2 ⟨subd10_2_348, List.forall_mem_cons.2 ⟨subd10_2_349, List.forall_mem_cons.2 ⟨subd10_2_350, List.forall_mem_cons.2 ⟨subd10_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_352 : subd10_2 [1, -1, -2] = true := by decide +kernel
theorem subd10_2_353 : subd10_2 [1, -1, -1] = true := by decide +kernel
theorem subd10_2_354 : subd10_2 [1, -1, 0] = true := by decide +kernel
theorem subd10_2_355 : subd10_2 [1, -1, 1] = true := by decide +kernel
theorem subd10_2_356 : subd10_2 [1, -1, 2] = true := by decide +kernel
theorem subd10_2_357 : subd10_2 [1, -1, 3] = true := by decide +kernel
theorem subd10_2_358 : subd10_2 [1, -1, 4] = true := by decide +kernel
theorem subd10_2_359 : subd10_2 [1, -1, 5] = true := by decide +kernel
theorem subd10_2_360 : subd10_2 [1, -1, 6] = true := by decide +kernel
theorem subd10_2_361 : subd10_2 [1, -1, 7] = true := by decide +kernel
theorem subd10_2_362 : subd10_2 [1, -1, 8] = true := by decide +kernel
theorem subd10_2_363 : subd10_2 [1, 0, -8] = true := by decide +kernel
theorem subd10_2_364 : subd10_2 [1, 0, -7] = true := by decide +kernel
theorem subd10_2_365 : subd10_2 [1, 0, -6] = true := by decide +kernel
theorem subd10_2_366 : subd10_2 [1, 0, -5] = true := by decide +kernel
theorem subd10_2_367 : subd10_2 [1, 0, -4] = true := by decide +kernel
theorem subd10_2_368 : subd10_2 [1, 0, -3] = true := by decide +kernel
theorem subd10_2_369 : subd10_2 [1, 0, -2] = true := by decide +kernel
theorem subd10_2_370 : subd10_2 [1, 0, -1] = true := by decide +kernel
theorem subd10_2_371 : subd10_2 [1, 0, 0] = true := by decide +kernel
theorem subd10_2_372 : subd10_2 [1, 0, 1] = true := by decide +kernel
theorem subd10_2_373 : subd10_2 [1, 0, 2] = true := by decide +kernel
theorem subd10_2_374 : subd10_2 [1, 0, 3] = true := by decide +kernel
theorem subd10_2_375 : subd10_2 [1, 0, 4] = true := by decide +kernel
theorem subd10_2_376 : subd10_2 [1, 0, 5] = true := by decide +kernel
theorem subd10_2_377 : subd10_2 [1, 0, 6] = true := by decide +kernel
theorem subd10_2_378 : subd10_2 [1, 0, 7] = true := by decide +kernel
theorem subd10_2_379 : subd10_2 [1, 0, 8] = true := by decide +kernel
theorem subd10_2_380 : subd10_2 [1, 1, -8] = true := by decide +kernel
theorem subd10_2_381 : subd10_2 [1, 1, -7] = true := by decide +kernel
theorem subd10_2_382 : subd10_2 [1, 1, -6] = true := by decide +kernel
theorem subd10_2_383 : subd10_2 [1, 1, -5] = true := by decide +kernel
theorem sbd10_2_11 : ∀ q ∈ blkd10_2_11, subd10_2 q = true := by
  unfold blkd10_2_11
  exact List.forall_mem_cons.2 ⟨subd10_2_352, List.forall_mem_cons.2 ⟨subd10_2_353, List.forall_mem_cons.2 ⟨subd10_2_354, List.forall_mem_cons.2 ⟨subd10_2_355, List.forall_mem_cons.2 ⟨subd10_2_356, List.forall_mem_cons.2 ⟨subd10_2_357, List.forall_mem_cons.2 ⟨subd10_2_358, List.forall_mem_cons.2 ⟨subd10_2_359, List.forall_mem_cons.2 ⟨subd10_2_360, List.forall_mem_cons.2 ⟨subd10_2_361, List.forall_mem_cons.2 ⟨subd10_2_362, List.forall_mem_cons.2 ⟨subd10_2_363, List.forall_mem_cons.2 ⟨subd10_2_364, List.forall_mem_cons.2 ⟨subd10_2_365, List.forall_mem_cons.2 ⟨subd10_2_366, List.forall_mem_cons.2 ⟨subd10_2_367, List.forall_mem_cons.2 ⟨subd10_2_368, List.forall_mem_cons.2 ⟨subd10_2_369, List.forall_mem_cons.2 ⟨subd10_2_370, List.forall_mem_cons.2 ⟨subd10_2_371, List.forall_mem_cons.2 ⟨subd10_2_372, List.forall_mem_cons.2 ⟨subd10_2_373, List.forall_mem_cons.2 ⟨subd10_2_374, List.forall_mem_cons.2 ⟨subd10_2_375, List.forall_mem_cons.2 ⟨subd10_2_376, List.forall_mem_cons.2 ⟨subd10_2_377, List.forall_mem_cons.2 ⟨subd10_2_378, List.forall_mem_cons.2 ⟨subd10_2_379, List.forall_mem_cons.2 ⟨subd10_2_380, List.forall_mem_cons.2 ⟨subd10_2_381, List.forall_mem_cons.2 ⟨subd10_2_382, List.forall_mem_cons.2 ⟨subd10_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_384 : subd10_2 [1, 1, -4] = true := by decide +kernel
theorem subd10_2_385 : subd10_2 [1, 1, -3] = true := by decide +kernel
theorem subd10_2_386 : subd10_2 [1, 1, -2] = true := by decide +kernel
theorem subd10_2_387 : subd10_2 [1, 1, -1] = true := by decide +kernel
theorem subd10_2_388 : subd10_2 [1, 1, 0] = true := by decide +kernel
theorem subd10_2_389 : subd10_2 [1, 1, 1] = true := by decide +kernel
theorem subd10_2_390 : subd10_2 [1, 1, 2] = true := by decide +kernel
theorem subd10_2_391 : subd10_2 [1, 1, 3] = true := by decide +kernel
theorem subd10_2_392 : subd10_2 [1, 1, 4] = true := by decide +kernel
theorem subd10_2_393 : subd10_2 [1, 1, 5] = true := by decide +kernel
theorem subd10_2_394 : subd10_2 [1, 1, 6] = true := by decide +kernel
theorem subd10_2_395 : subd10_2 [1, 1, 7] = true := by decide +kernel
theorem subd10_2_396 : subd10_2 [1, 2, -8] = true := by decide +kernel
theorem subd10_2_397 : subd10_2 [1, 2, -7] = true := by decide +kernel
theorem subd10_2_398 : subd10_2 [1, 2, -6] = true := by decide +kernel
theorem subd10_2_399 : subd10_2 [1, 2, -5] = true := by decide +kernel
theorem subd10_2_400 : subd10_2 [1, 2, -4] = true := by decide +kernel
theorem subd10_2_401 : subd10_2 [1, 2, -3] = true := by decide +kernel
theorem subd10_2_402 : subd10_2 [1, 2, -2] = true := by decide +kernel
theorem subd10_2_403 : subd10_2 [1, 2, -1] = true := by decide +kernel
theorem subd10_2_404 : subd10_2 [1, 2, 0] = true := by decide +kernel
theorem subd10_2_405 : subd10_2 [1, 2, 1] = true := by decide +kernel
theorem subd10_2_406 : subd10_2 [1, 2, 2] = true := by decide +kernel
theorem subd10_2_407 : subd10_2 [1, 2, 3] = true := by decide +kernel
theorem subd10_2_408 : subd10_2 [1, 2, 4] = true := by decide +kernel
theorem subd10_2_409 : subd10_2 [1, 2, 5] = true := by decide +kernel
theorem subd10_2_410 : subd10_2 [1, 2, 6] = true := by decide +kernel
theorem subd10_2_411 : subd10_2 [1, 3] = true := by decide +kernel
theorem subd10_2_412 : subd10_2 [1, 4] = true := by decide +kernel
theorem subd10_2_413 : subd10_2 [2, -6] = true := by decide +kernel
theorem subd10_2_414 : subd10_2 [2, -5] = true := by decide +kernel
theorem subd10_2_415 : subd10_2 [2, -4] = true := by decide +kernel
theorem sbd10_2_12 : ∀ q ∈ blkd10_2_12, subd10_2 q = true := by
  unfold blkd10_2_12
  exact List.forall_mem_cons.2 ⟨subd10_2_384, List.forall_mem_cons.2 ⟨subd10_2_385, List.forall_mem_cons.2 ⟨subd10_2_386, List.forall_mem_cons.2 ⟨subd10_2_387, List.forall_mem_cons.2 ⟨subd10_2_388, List.forall_mem_cons.2 ⟨subd10_2_389, List.forall_mem_cons.2 ⟨subd10_2_390, List.forall_mem_cons.2 ⟨subd10_2_391, List.forall_mem_cons.2 ⟨subd10_2_392, List.forall_mem_cons.2 ⟨subd10_2_393, List.forall_mem_cons.2 ⟨subd10_2_394, List.forall_mem_cons.2 ⟨subd10_2_395, List.forall_mem_cons.2 ⟨subd10_2_396, List.forall_mem_cons.2 ⟨subd10_2_397, List.forall_mem_cons.2 ⟨subd10_2_398, List.forall_mem_cons.2 ⟨subd10_2_399, List.forall_mem_cons.2 ⟨subd10_2_400, List.forall_mem_cons.2 ⟨subd10_2_401, List.forall_mem_cons.2 ⟨subd10_2_402, List.forall_mem_cons.2 ⟨subd10_2_403, List.forall_mem_cons.2 ⟨subd10_2_404, List.forall_mem_cons.2 ⟨subd10_2_405, List.forall_mem_cons.2 ⟨subd10_2_406, List.forall_mem_cons.2 ⟨subd10_2_407, List.forall_mem_cons.2 ⟨subd10_2_408, List.forall_mem_cons.2 ⟨subd10_2_409, List.forall_mem_cons.2 ⟨subd10_2_410, List.forall_mem_cons.2 ⟨subd10_2_411, List.forall_mem_cons.2 ⟨subd10_2_412, List.forall_mem_cons.2 ⟨subd10_2_413, List.forall_mem_cons.2 ⟨subd10_2_414, List.forall_mem_cons.2 ⟨subd10_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_416 : subd10_2 [2, -3, -5] = true := by decide +kernel
theorem subd10_2_417 : subd10_2 [2, -3, -4] = true := by decide +kernel
theorem subd10_2_418 : subd10_2 [2, -3, -3] = true := by decide +kernel
theorem subd10_2_419 : subd10_2 [2, -3, -2] = true := by decide +kernel
theorem subd10_2_420 : subd10_2 [2, -3, -1] = true := by decide +kernel
theorem subd10_2_421 : subd10_2 [2, -3, 0] = true := by decide +kernel
theorem subd10_2_422 : subd10_2 [2, -3, 1] = true := by decide +kernel
theorem subd10_2_423 : subd10_2 [2, -3, 2] = true := by decide +kernel
theorem subd10_2_424 : subd10_2 [2, -3, 3] = true := by decide +kernel
theorem subd10_2_425 : subd10_2 [2, -3, 4] = true := by decide +kernel
theorem subd10_2_426 : subd10_2 [2, -3, 5] = true := by decide +kernel
theorem subd10_2_427 : subd10_2 [2, -3, 6] = true := by decide +kernel
theorem subd10_2_428 : subd10_2 [2, -3, 7] = true := by decide +kernel
theorem subd10_2_429 : subd10_2 [2, -3, 8] = true := by decide +kernel
theorem subd10_2_430 : subd10_2 [2, -2, -6] = true := by decide +kernel
theorem subd10_2_431 : subd10_2 [2, -2, -5] = true := by decide +kernel
theorem subd10_2_432 : subd10_2 [2, -2, -4] = true := by decide +kernel
theorem subd10_2_433 : subd10_2 [2, -2, -3] = true := by decide +kernel
theorem subd10_2_434 : subd10_2 [2, -2, -2] = true := by decide +kernel
theorem subd10_2_435 : subd10_2 [2, -2, -1] = true := by decide +kernel
theorem subd10_2_436 : subd10_2 [2, -2, 0] = true := by decide +kernel
theorem subd10_2_437 : subd10_2 [2, -2, 1] = true := by decide +kernel
theorem subd10_2_438 : subd10_2 [2, -2, 2] = true := by decide +kernel
theorem subd10_2_439 : subd10_2 [2, -2, 3] = true := by decide +kernel
theorem subd10_2_440 : subd10_2 [2, -2, 4] = true := by decide +kernel
theorem subd10_2_441 : subd10_2 [2, -2, 5] = true := by decide +kernel
theorem subd10_2_442 : subd10_2 [2, -2, 6] = true := by decide +kernel
theorem subd10_2_443 : subd10_2 [2, -2, 7] = true := by decide +kernel
theorem subd10_2_444 : subd10_2 [2, -2, 8] = true := by decide +kernel
theorem subd10_2_445 : subd10_2 [2, -1, -7] = true := by decide +kernel
theorem subd10_2_446 : subd10_2 [2, -1, -6] = true := by decide +kernel
theorem subd10_2_447 : subd10_2 [2, -1, -5] = true := by decide +kernel
theorem sbd10_2_13 : ∀ q ∈ blkd10_2_13, subd10_2 q = true := by
  unfold blkd10_2_13
  exact List.forall_mem_cons.2 ⟨subd10_2_416, List.forall_mem_cons.2 ⟨subd10_2_417, List.forall_mem_cons.2 ⟨subd10_2_418, List.forall_mem_cons.2 ⟨subd10_2_419, List.forall_mem_cons.2 ⟨subd10_2_420, List.forall_mem_cons.2 ⟨subd10_2_421, List.forall_mem_cons.2 ⟨subd10_2_422, List.forall_mem_cons.2 ⟨subd10_2_423, List.forall_mem_cons.2 ⟨subd10_2_424, List.forall_mem_cons.2 ⟨subd10_2_425, List.forall_mem_cons.2 ⟨subd10_2_426, List.forall_mem_cons.2 ⟨subd10_2_427, List.forall_mem_cons.2 ⟨subd10_2_428, List.forall_mem_cons.2 ⟨subd10_2_429, List.forall_mem_cons.2 ⟨subd10_2_430, List.forall_mem_cons.2 ⟨subd10_2_431, List.forall_mem_cons.2 ⟨subd10_2_432, List.forall_mem_cons.2 ⟨subd10_2_433, List.forall_mem_cons.2 ⟨subd10_2_434, List.forall_mem_cons.2 ⟨subd10_2_435, List.forall_mem_cons.2 ⟨subd10_2_436, List.forall_mem_cons.2 ⟨subd10_2_437, List.forall_mem_cons.2 ⟨subd10_2_438, List.forall_mem_cons.2 ⟨subd10_2_439, List.forall_mem_cons.2 ⟨subd10_2_440, List.forall_mem_cons.2 ⟨subd10_2_441, List.forall_mem_cons.2 ⟨subd10_2_442, List.forall_mem_cons.2 ⟨subd10_2_443, List.forall_mem_cons.2 ⟨subd10_2_444, List.forall_mem_cons.2 ⟨subd10_2_445, List.forall_mem_cons.2 ⟨subd10_2_446, List.forall_mem_cons.2 ⟨subd10_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_448 : subd10_2 [2, -1, -4] = true := by decide +kernel
theorem subd10_2_449 : subd10_2 [2, -1, -3] = true := by decide +kernel
theorem subd10_2_450 : subd10_2 [2, -1, -2] = true := by decide +kernel
theorem subd10_2_451 : subd10_2 [2, -1, -1] = true := by decide +kernel
theorem subd10_2_452 : subd10_2 [2, -1, 0] = true := by decide +kernel
theorem subd10_2_453 : subd10_2 [2, -1, 1] = true := by decide +kernel
theorem subd10_2_454 : subd10_2 [2, -1, 2] = true := by decide +kernel
theorem subd10_2_455 : subd10_2 [2, -1, 3] = true := by decide +kernel
theorem subd10_2_456 : subd10_2 [2, -1, 4] = true := by decide +kernel
theorem subd10_2_457 : subd10_2 [2, -1, 5] = true := by decide +kernel
theorem subd10_2_458 : subd10_2 [2, -1, 6] = true := by decide +kernel
theorem subd10_2_459 : subd10_2 [2, -1, 7] = true := by decide +kernel
theorem subd10_2_460 : subd10_2 [2, -1, 8] = true := by decide +kernel
theorem subd10_2_461 : subd10_2 [2, 0, -7] = true := by decide +kernel
theorem subd10_2_462 : subd10_2 [2, 0, -6] = true := by decide +kernel
theorem subd10_2_463 : subd10_2 [2, 0, -5] = true := by decide +kernel
theorem subd10_2_464 : subd10_2 [2, 0, -4] = true := by decide +kernel
theorem subd10_2_465 : subd10_2 [2, 0, -3] = true := by decide +kernel
theorem subd10_2_466 : subd10_2 [2, 0, -2] = true := by decide +kernel
theorem subd10_2_467 : subd10_2 [2, 0, -1] = true := by decide +kernel
theorem subd10_2_468 : subd10_2 [2, 0, 0] = true := by decide +kernel
theorem subd10_2_469 : subd10_2 [2, 0, 1] = true := by decide +kernel
theorem subd10_2_470 : subd10_2 [2, 0, 2] = true := by decide +kernel
theorem subd10_2_471 : subd10_2 [2, 0, 3] = true := by decide +kernel
theorem subd10_2_472 : subd10_2 [2, 0, 4] = true := by decide +kernel
theorem subd10_2_473 : subd10_2 [2, 0, 5] = true := by decide +kernel
theorem subd10_2_474 : subd10_2 [2, 0, 6] = true := by decide +kernel
theorem subd10_2_475 : subd10_2 [2, 0, 7] = true := by decide +kernel
theorem subd10_2_476 : subd10_2 [2, 1, -7] = true := by decide +kernel
theorem subd10_2_477 : subd10_2 [2, 1, -6] = true := by decide +kernel
theorem subd10_2_478 : subd10_2 [2, 1, -5] = true := by decide +kernel
theorem subd10_2_479 : subd10_2 [2, 1, -4] = true := by decide +kernel
theorem sbd10_2_14 : ∀ q ∈ blkd10_2_14, subd10_2 q = true := by
  unfold blkd10_2_14
  exact List.forall_mem_cons.2 ⟨subd10_2_448, List.forall_mem_cons.2 ⟨subd10_2_449, List.forall_mem_cons.2 ⟨subd10_2_450, List.forall_mem_cons.2 ⟨subd10_2_451, List.forall_mem_cons.2 ⟨subd10_2_452, List.forall_mem_cons.2 ⟨subd10_2_453, List.forall_mem_cons.2 ⟨subd10_2_454, List.forall_mem_cons.2 ⟨subd10_2_455, List.forall_mem_cons.2 ⟨subd10_2_456, List.forall_mem_cons.2 ⟨subd10_2_457, List.forall_mem_cons.2 ⟨subd10_2_458, List.forall_mem_cons.2 ⟨subd10_2_459, List.forall_mem_cons.2 ⟨subd10_2_460, List.forall_mem_cons.2 ⟨subd10_2_461, List.forall_mem_cons.2 ⟨subd10_2_462, List.forall_mem_cons.2 ⟨subd10_2_463, List.forall_mem_cons.2 ⟨subd10_2_464, List.forall_mem_cons.2 ⟨subd10_2_465, List.forall_mem_cons.2 ⟨subd10_2_466, List.forall_mem_cons.2 ⟨subd10_2_467, List.forall_mem_cons.2 ⟨subd10_2_468, List.forall_mem_cons.2 ⟨subd10_2_469, List.forall_mem_cons.2 ⟨subd10_2_470, List.forall_mem_cons.2 ⟨subd10_2_471, List.forall_mem_cons.2 ⟨subd10_2_472, List.forall_mem_cons.2 ⟨subd10_2_473, List.forall_mem_cons.2 ⟨subd10_2_474, List.forall_mem_cons.2 ⟨subd10_2_475, List.forall_mem_cons.2 ⟨subd10_2_476, List.forall_mem_cons.2 ⟨subd10_2_477, List.forall_mem_cons.2 ⟨subd10_2_478, List.forall_mem_cons.2 ⟨subd10_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_480 : subd10_2 [2, 1, -3] = true := by decide +kernel
theorem subd10_2_481 : subd10_2 [2, 1, -2] = true := by decide +kernel
theorem subd10_2_482 : subd10_2 [2, 1, -1] = true := by decide +kernel
theorem subd10_2_483 : subd10_2 [2, 1, 0] = true := by decide +kernel
theorem subd10_2_484 : subd10_2 [2, 1, 1] = true := by decide +kernel
theorem subd10_2_485 : subd10_2 [2, 1, 2] = true := by decide +kernel
theorem subd10_2_486 : subd10_2 [2, 1, 3] = true := by decide +kernel
theorem subd10_2_487 : subd10_2 [2, 1, 4] = true := by decide +kernel
theorem subd10_2_488 : subd10_2 [2, 1, 5] = true := by decide +kernel
theorem subd10_2_489 : subd10_2 [2, 1, 6] = true := by decide +kernel
theorem subd10_2_490 : subd10_2 [2, 2] = true := by decide +kernel
theorem subd10_2_491 : subd10_2 [2, 3] = true := by decide +kernel
theorem subd10_2_492 : subd10_2 [3, -6] = true := by decide +kernel
theorem subd10_2_493 : subd10_2 [3, -5] = true := by decide +kernel
theorem subd10_2_494 : subd10_2 [3, -4] = true := by decide +kernel
theorem subd10_2_495 : subd10_2 [3, -3] = true := by decide +kernel
theorem subd10_2_496 : subd10_2 [3, -2] = true := by decide +kernel
theorem subd10_2_497 : subd10_2 [3, -1] = true := by decide +kernel
theorem subd10_2_498 : subd10_2 [3, 0] = true := by decide +kernel
theorem subd10_2_499 : subd10_2 [3, 1] = true := by decide +kernel
theorem subd10_2_500 : subd10_2 [3, 2] = true := by decide +kernel
theorem subd10_2_501 : subd10_2 [4, -5] = true := by decide +kernel
theorem subd10_2_502 : subd10_2 [4, -4] = true := by decide +kernel
theorem subd10_2_503 : subd10_2 [4, -3] = true := by decide +kernel
theorem subd10_2_504 : subd10_2 [4, -2] = true := by decide +kernel
theorem subd10_2_505 : subd10_2 [4, -1] = true := by decide +kernel
theorem subd10_2_506 : subd10_2 [4, 0] = true := by decide +kernel
theorem sbd10_2_15 : ∀ q ∈ blkd10_2_15, subd10_2 q = true := by
  unfold blkd10_2_15
  exact List.forall_mem_cons.2 ⟨subd10_2_480, List.forall_mem_cons.2 ⟨subd10_2_481, List.forall_mem_cons.2 ⟨subd10_2_482, List.forall_mem_cons.2 ⟨subd10_2_483, List.forall_mem_cons.2 ⟨subd10_2_484, List.forall_mem_cons.2 ⟨subd10_2_485, List.forall_mem_cons.2 ⟨subd10_2_486, List.forall_mem_cons.2 ⟨subd10_2_487, List.forall_mem_cons.2 ⟨subd10_2_488, List.forall_mem_cons.2 ⟨subd10_2_489, List.forall_mem_cons.2 ⟨subd10_2_490, List.forall_mem_cons.2 ⟨subd10_2_491, List.forall_mem_cons.2 ⟨subd10_2_492, List.forall_mem_cons.2 ⟨subd10_2_493, List.forall_mem_cons.2 ⟨subd10_2_494, List.forall_mem_cons.2 ⟨subd10_2_495, List.forall_mem_cons.2 ⟨subd10_2_496, List.forall_mem_cons.2 ⟨subd10_2_497, List.forall_mem_cons.2 ⟨subd10_2_498, List.forall_mem_cons.2 ⟨subd10_2_499, List.forall_mem_cons.2 ⟨subd10_2_500, List.forall_mem_cons.2 ⟨subd10_2_501, List.forall_mem_cons.2 ⟨subd10_2_502, List.forall_mem_cons.2 ⟨subd10_2_503, List.forall_mem_cons.2 ⟨subd10_2_504, List.forall_mem_cons.2 ⟨subd10_2_505, List.forall_mem_cons.2 ⟨subd10_2_506, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
