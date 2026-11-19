import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_5_32 : subd10_5 [-2, -1, 2] = true := by decide +kernel
theorem subd10_5_33 : subd10_5 [-2, -1, 3] = true := by decide +kernel
theorem subd10_5_34 : subd10_5 [-2, -1, 4] = true := by decide +kernel
theorem subd10_5_35 : subd10_5 [-2, -1, 5] = true := by decide +kernel
theorem subd10_5_36 : subd10_5 [-2, -1, 6] = true := by decide +kernel
theorem subd10_5_37 : subd10_5 [-2, -1, 7] = true := by decide +kernel
theorem subd10_5_38 : subd10_5 [-2, -1, 8] = true := by decide +kernel
theorem subd10_5_39 : subd10_5 [-2, -1, 9] = true := by decide +kernel
theorem subd10_5_40 : subd10_5 [-2, 0, -9] = true := by decide +kernel
theorem subd10_5_41 : subd10_5 [-2, 0, -8] = true := by decide +kernel
theorem subd10_5_42 : subd10_5 [-2, 0, -7] = true := by decide +kernel
theorem subd10_5_43 : subd10_5 [-2, 0, -6] = true := by decide +kernel
theorem subd10_5_44 : subd10_5 [-2, 0, -5] = true := by decide +kernel
theorem subd10_5_45 : subd10_5 [-2, 0, -4] = true := by decide +kernel
theorem subd10_5_46 : subd10_5 [-2, 0, -3] = true := by decide +kernel
theorem subd10_5_47 : subd10_5 [-2, 0, -2] = true := by decide +kernel
theorem subd10_5_48 : subd10_5 [-2, 0, -1] = true := by decide +kernel
theorem subd10_5_49 : subd10_5 [-2, 0, 0] = true := by decide +kernel
theorem subd10_5_50 : subd10_5 [-2, 0, 1] = true := by decide +kernel
theorem subd10_5_51 : subd10_5 [-2, 0, 2] = true := by decide +kernel
theorem subd10_5_52 : subd10_5 [-2, 0, 3] = true := by decide +kernel
theorem subd10_5_53 : subd10_5 [-2, 0, 4] = true := by decide +kernel
theorem subd10_5_54 : subd10_5 [-2, 0, 5] = true := by decide +kernel
theorem subd10_5_55 : subd10_5 [-2, 0, 6] = true := by decide +kernel
theorem subd10_5_56 : subd10_5 [-2, 0, 7] = true := by decide +kernel
theorem subd10_5_57 : subd10_5 [-2, 0, 8] = true := by decide +kernel
theorem subd10_5_58 : subd10_5 [-2, 0, 9] = true := by decide +kernel
theorem subd10_5_59 : subd10_5 [-2, 1, -8] = true := by decide +kernel
theorem subd10_5_60 : subd10_5 [-2, 1, -7] = true := by decide +kernel
theorem subd10_5_61 : subd10_5 [-2, 1, -6] = true := by decide +kernel
theorem subd10_5_62 : subd10_5 [-2, 1, -5] = true := by decide +kernel
theorem subd10_5_63 : subd10_5 [-2, 1, -4] = true := by decide +kernel
theorem sbd10_5_1 : ∀ q ∈ blkd10_5_1, subd10_5 q = true := by
  unfold blkd10_5_1
  exact List.forall_mem_cons.2 ⟨subd10_5_32, List.forall_mem_cons.2 ⟨subd10_5_33, List.forall_mem_cons.2 ⟨subd10_5_34, List.forall_mem_cons.2 ⟨subd10_5_35, List.forall_mem_cons.2 ⟨subd10_5_36, List.forall_mem_cons.2 ⟨subd10_5_37, List.forall_mem_cons.2 ⟨subd10_5_38, List.forall_mem_cons.2 ⟨subd10_5_39, List.forall_mem_cons.2 ⟨subd10_5_40, List.forall_mem_cons.2 ⟨subd10_5_41, List.forall_mem_cons.2 ⟨subd10_5_42, List.forall_mem_cons.2 ⟨subd10_5_43, List.forall_mem_cons.2 ⟨subd10_5_44, List.forall_mem_cons.2 ⟨subd10_5_45, List.forall_mem_cons.2 ⟨subd10_5_46, List.forall_mem_cons.2 ⟨subd10_5_47, List.forall_mem_cons.2 ⟨subd10_5_48, List.forall_mem_cons.2 ⟨subd10_5_49, List.forall_mem_cons.2 ⟨subd10_5_50, List.forall_mem_cons.2 ⟨subd10_5_51, List.forall_mem_cons.2 ⟨subd10_5_52, List.forall_mem_cons.2 ⟨subd10_5_53, List.forall_mem_cons.2 ⟨subd10_5_54, List.forall_mem_cons.2 ⟨subd10_5_55, List.forall_mem_cons.2 ⟨subd10_5_56, List.forall_mem_cons.2 ⟨subd10_5_57, List.forall_mem_cons.2 ⟨subd10_5_58, List.forall_mem_cons.2 ⟨subd10_5_59, List.forall_mem_cons.2 ⟨subd10_5_60, List.forall_mem_cons.2 ⟨subd10_5_61, List.forall_mem_cons.2 ⟨subd10_5_62, List.forall_mem_cons.2 ⟨subd10_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_64 : subd10_5 [-2, 1, -3] = true := by decide +kernel
theorem subd10_5_65 : subd10_5 [-2, 1, -2] = true := by decide +kernel
theorem subd10_5_66 : subd10_5 [-2, 1, -1] = true := by decide +kernel
theorem subd10_5_67 : subd10_5 [-2, 1, 0] = true := by decide +kernel
theorem subd10_5_68 : subd10_5 [-2, 1, 1] = true := by decide +kernel
theorem subd10_5_69 : subd10_5 [-2, 1, 2] = true := by decide +kernel
theorem subd10_5_70 : subd10_5 [-2, 1, 3] = true := by decide +kernel
theorem subd10_5_71 : subd10_5 [-2, 1, 4] = true := by decide +kernel
theorem subd10_5_72 : subd10_5 [-2, 1, 5] = true := by decide +kernel
theorem subd10_5_73 : subd10_5 [-2, 1, 6] = true := by decide +kernel
theorem subd10_5_74 : subd10_5 [-2, 1, 7] = true := by decide +kernel
theorem subd10_5_75 : subd10_5 [-2, 1, 8] = true := by decide +kernel
theorem subd10_5_76 : subd10_5 [-2, 1, 9] = true := by decide +kernel
theorem subd10_5_77 : subd10_5 [-2, 2] = true := by decide +kernel
theorem subd10_5_78 : subd10_5 [-1, -4] = true := by decide +kernel
theorem subd10_5_79 : subd10_5 [-1, -3] = true := by decide +kernel
theorem subd10_5_80 : subd10_5 [-1, -2, -9] = true := by decide +kernel
theorem subd10_5_81 : subd10_5 [-1, -2, -8] = true := by decide +kernel
theorem subd10_5_82 : subd10_5 [-1, -2, -7] = true := by decide +kernel
theorem subd10_5_83 : subd10_5 [-1, -2, -6] = true := by decide +kernel
theorem subd10_5_84 : subd10_5 [-1, -2, -5] = true := by decide +kernel
theorem subd10_5_85 : subd10_5 [-1, -2, -4] = true := by decide +kernel
theorem subd10_5_86 : subd10_5 [-1, -2, -3] = true := by decide +kernel
theorem subd10_5_87 : subd10_5 [-1, -2, -2] = true := by decide +kernel
theorem subd10_5_88 : subd10_5 [-1, -2, -1] = true := by decide +kernel
theorem subd10_5_89 : subd10_5 [-1, -2, 0] = true := by decide +kernel
theorem subd10_5_90 : subd10_5 [-1, -2, 1] = true := by decide +kernel
theorem subd10_5_91 : subd10_5 [-1, -2, 2] = true := by decide +kernel
theorem subd10_5_92 : subd10_5 [-1, -2, 3] = true := by decide +kernel
theorem subd10_5_93 : subd10_5 [-1, -2, 4] = true := by decide +kernel
theorem subd10_5_94 : subd10_5 [-1, -2, 5] = true := by decide +kernel
theorem subd10_5_95 : subd10_5 [-1, -2, 6] = true := by decide +kernel
theorem sbd10_5_2 : ∀ q ∈ blkd10_5_2, subd10_5 q = true := by
  unfold blkd10_5_2
  exact List.forall_mem_cons.2 ⟨subd10_5_64, List.forall_mem_cons.2 ⟨subd10_5_65, List.forall_mem_cons.2 ⟨subd10_5_66, List.forall_mem_cons.2 ⟨subd10_5_67, List.forall_mem_cons.2 ⟨subd10_5_68, List.forall_mem_cons.2 ⟨subd10_5_69, List.forall_mem_cons.2 ⟨subd10_5_70, List.forall_mem_cons.2 ⟨subd10_5_71, List.forall_mem_cons.2 ⟨subd10_5_72, List.forall_mem_cons.2 ⟨subd10_5_73, List.forall_mem_cons.2 ⟨subd10_5_74, List.forall_mem_cons.2 ⟨subd10_5_75, List.forall_mem_cons.2 ⟨subd10_5_76, List.forall_mem_cons.2 ⟨subd10_5_77, List.forall_mem_cons.2 ⟨subd10_5_78, List.forall_mem_cons.2 ⟨subd10_5_79, List.forall_mem_cons.2 ⟨subd10_5_80, List.forall_mem_cons.2 ⟨subd10_5_81, List.forall_mem_cons.2 ⟨subd10_5_82, List.forall_mem_cons.2 ⟨subd10_5_83, List.forall_mem_cons.2 ⟨subd10_5_84, List.forall_mem_cons.2 ⟨subd10_5_85, List.forall_mem_cons.2 ⟨subd10_5_86, List.forall_mem_cons.2 ⟨subd10_5_87, List.forall_mem_cons.2 ⟨subd10_5_88, List.forall_mem_cons.2 ⟨subd10_5_89, List.forall_mem_cons.2 ⟨subd10_5_90, List.forall_mem_cons.2 ⟨subd10_5_91, List.forall_mem_cons.2 ⟨subd10_5_92, List.forall_mem_cons.2 ⟨subd10_5_93, List.forall_mem_cons.2 ⟨subd10_5_94, List.forall_mem_cons.2 ⟨subd10_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_96 : subd10_5 [-1, -2, 7] = true := by decide +kernel
theorem subd10_5_97 : subd10_5 [-1, -2, 8] = true := by decide +kernel
theorem subd10_5_98 : subd10_5 [-1, -1, -10] = true := by decide +kernel
theorem subd10_5_99 : subd10_5 [-1, -1, -9] = true := by decide +kernel
theorem subd10_5_100 : subd10_5 [-1, -1, -8] = true := by decide +kernel
theorem subd10_5_101 : subd10_5 [-1, -1, -7] = true := by decide +kernel
theorem subd10_5_102 : subd10_5 [-1, -1, -6] = true := by decide +kernel
theorem subd10_5_103 : subd10_5 [-1, -1, -5] = true := by decide +kernel
theorem subd10_5_104 : subd10_5 [-1, -1, -4] = true := by decide +kernel
theorem subd10_5_105 : subd10_5 [-1, -1, -3] = true := by decide +kernel
theorem subd10_5_106 : subd10_5 [-1, -1, -2] = true := by decide +kernel
theorem subd10_5_107 : subd10_5 [-1, -1, -1] = true := by decide +kernel
theorem subd10_5_108 : subd10_5 [-1, -1, 0] = true := by decide +kernel
theorem subd10_5_109 : subd10_5 [-1, -1, 1] = true := by decide +kernel
theorem subd10_5_110 : subd10_5 [-1, -1, 2] = true := by decide +kernel
theorem subd10_5_111 : subd10_5 [-1, -1, 3] = true := by decide +kernel
theorem subd10_5_112 : subd10_5 [-1, -1, 4] = true := by decide +kernel
theorem subd10_5_113 : subd10_5 [-1, -1, 5] = true := by decide +kernel
theorem subd10_5_114 : subd10_5 [-1, -1, 6] = true := by decide +kernel
theorem subd10_5_115 : subd10_5 [-1, -1, 7] = true := by decide +kernel
theorem subd10_5_116 : subd10_5 [-1, -1, 8] = true := by decide +kernel
theorem subd10_5_117 : subd10_5 [-1, -1, 9] = true := by decide +kernel
theorem subd10_5_118 : subd10_5 [-1, -1, 10] = true := by decide +kernel
theorem subd10_5_119 : subd10_5 [-1, 0, -11] = true := by decide +kernel
theorem subd10_5_120 : subd10_5 [-1, 0, -10] = true := by decide +kernel
theorem subd10_5_121 : subd10_5 [-1, 0, -9] = true := by decide +kernel
theorem subd10_5_122 : subd10_5 [-1, 0, -8] = true := by decide +kernel
theorem subd10_5_123 : subd10_5 [-1, 0, -7] = true := by decide +kernel
theorem subd10_5_124 : subd10_5 [-1, 0, -6] = true := by decide +kernel
theorem subd10_5_125 : subd10_5 [-1, 0, -5] = true := by decide +kernel
theorem subd10_5_126 : subd10_5 [-1, 0, -4] = true := by decide +kernel
theorem subd10_5_127 : subd10_5 [-1, 0, -3] = true := by decide +kernel
theorem sbd10_5_3 : ∀ q ∈ blkd10_5_3, subd10_5 q = true := by
  unfold blkd10_5_3
  exact List.forall_mem_cons.2 ⟨subd10_5_96, List.forall_mem_cons.2 ⟨subd10_5_97, List.forall_mem_cons.2 ⟨subd10_5_98, List.forall_mem_cons.2 ⟨subd10_5_99, List.forall_mem_cons.2 ⟨subd10_5_100, List.forall_mem_cons.2 ⟨subd10_5_101, List.forall_mem_cons.2 ⟨subd10_5_102, List.forall_mem_cons.2 ⟨subd10_5_103, List.forall_mem_cons.2 ⟨subd10_5_104, List.forall_mem_cons.2 ⟨subd10_5_105, List.forall_mem_cons.2 ⟨subd10_5_106, List.forall_mem_cons.2 ⟨subd10_5_107, List.forall_mem_cons.2 ⟨subd10_5_108, List.forall_mem_cons.2 ⟨subd10_5_109, List.forall_mem_cons.2 ⟨subd10_5_110, List.forall_mem_cons.2 ⟨subd10_5_111, List.forall_mem_cons.2 ⟨subd10_5_112, List.forall_mem_cons.2 ⟨subd10_5_113, List.forall_mem_cons.2 ⟨subd10_5_114, List.forall_mem_cons.2 ⟨subd10_5_115, List.forall_mem_cons.2 ⟨subd10_5_116, List.forall_mem_cons.2 ⟨subd10_5_117, List.forall_mem_cons.2 ⟨subd10_5_118, List.forall_mem_cons.2 ⟨subd10_5_119, List.forall_mem_cons.2 ⟨subd10_5_120, List.forall_mem_cons.2 ⟨subd10_5_121, List.forall_mem_cons.2 ⟨subd10_5_122, List.forall_mem_cons.2 ⟨subd10_5_123, List.forall_mem_cons.2 ⟨subd10_5_124, List.forall_mem_cons.2 ⟨subd10_5_125, List.forall_mem_cons.2 ⟨subd10_5_126, List.forall_mem_cons.2 ⟨subd10_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_128 : subd10_5 [-1, 0, -2] = true := by decide +kernel
theorem subd10_5_129 : subd10_5 [-1, 0, -1] = true := by decide +kernel
theorem subd10_5_130 : subd10_5 [-1, 0, 0] = true := by decide +kernel
theorem subd10_5_131 : subd10_5 [-1, 0, 1] = true := by decide +kernel
theorem subd10_5_132 : subd10_5 [-1, 0, 2] = true := by decide +kernel
theorem subd10_5_133 : subd10_5 [-1, 0, 3] = true := by decide +kernel
theorem subd10_5_134 : subd10_5 [-1, 0, 4] = true := by decide +kernel
theorem subd10_5_135 : subd10_5 [-1, 0, 5] = true := by decide +kernel
theorem subd10_5_136 : subd10_5 [-1, 0, 6] = true := by decide +kernel
theorem subd10_5_137 : subd10_5 [-1, 0, 7] = true := by decide +kernel
theorem subd10_5_138 : subd10_5 [-1, 0, 8] = true := by decide +kernel
theorem subd10_5_139 : subd10_5 [-1, 0, 9] = true := by decide +kernel
theorem subd10_5_140 : subd10_5 [-1, 0, 10] = true := by decide +kernel
theorem subd10_5_141 : subd10_5 [-1, 1, -10] = true := by decide +kernel
theorem subd10_5_142 : subd10_5 [-1, 1, -9] = true := by decide +kernel
theorem subd10_5_143 : subd10_5 [-1, 1, -8] = true := by decide +kernel
theorem subd10_5_144 : subd10_5 [-1, 1, -7] = true := by decide +kernel
theorem subd10_5_145 : subd10_5 [-1, 1, -6] = true := by decide +kernel
theorem subd10_5_146 : subd10_5 [-1, 1, -5] = true := by decide +kernel
theorem subd10_5_147 : subd10_5 [-1, 1, -4] = true := by decide +kernel
theorem subd10_5_148 : subd10_5 [-1, 1, -3] = true := by decide +kernel
theorem subd10_5_149 : subd10_5 [-1, 1, -2] = true := by decide +kernel
theorem subd10_5_150 : subd10_5 [-1, 1, -1] = true := by decide +kernel
theorem subd10_5_151 : subd10_5 [-1, 1, 0] = true := by decide +kernel
theorem subd10_5_152 : subd10_5 [-1, 1, 1] = true := by decide +kernel
theorem subd10_5_153 : subd10_5 [-1, 1, 2] = true := by decide +kernel
theorem subd10_5_154 : subd10_5 [-1, 1, 3] = true := by decide +kernel
theorem subd10_5_155 : subd10_5 [-1, 1, 4] = true := by decide +kernel
theorem subd10_5_156 : subd10_5 [-1, 1, 5] = true := by decide +kernel
theorem subd10_5_157 : subd10_5 [-1, 1, 6] = true := by decide +kernel
theorem subd10_5_158 : subd10_5 [-1, 1, 7] = true := by decide +kernel
theorem subd10_5_159 : subd10_5 [-1, 1, 8] = true := by decide +kernel
theorem sbd10_5_4 : ∀ q ∈ blkd10_5_4, subd10_5 q = true := by
  unfold blkd10_5_4
  exact List.forall_mem_cons.2 ⟨subd10_5_128, List.forall_mem_cons.2 ⟨subd10_5_129, List.forall_mem_cons.2 ⟨subd10_5_130, List.forall_mem_cons.2 ⟨subd10_5_131, List.forall_mem_cons.2 ⟨subd10_5_132, List.forall_mem_cons.2 ⟨subd10_5_133, List.forall_mem_cons.2 ⟨subd10_5_134, List.forall_mem_cons.2 ⟨subd10_5_135, List.forall_mem_cons.2 ⟨subd10_5_136, List.forall_mem_cons.2 ⟨subd10_5_137, List.forall_mem_cons.2 ⟨subd10_5_138, List.forall_mem_cons.2 ⟨subd10_5_139, List.forall_mem_cons.2 ⟨subd10_5_140, List.forall_mem_cons.2 ⟨subd10_5_141, List.forall_mem_cons.2 ⟨subd10_5_142, List.forall_mem_cons.2 ⟨subd10_5_143, List.forall_mem_cons.2 ⟨subd10_5_144, List.forall_mem_cons.2 ⟨subd10_5_145, List.forall_mem_cons.2 ⟨subd10_5_146, List.forall_mem_cons.2 ⟨subd10_5_147, List.forall_mem_cons.2 ⟨subd10_5_148, List.forall_mem_cons.2 ⟨subd10_5_149, List.forall_mem_cons.2 ⟨subd10_5_150, List.forall_mem_cons.2 ⟨subd10_5_151, List.forall_mem_cons.2 ⟨subd10_5_152, List.forall_mem_cons.2 ⟨subd10_5_153, List.forall_mem_cons.2 ⟨subd10_5_154, List.forall_mem_cons.2 ⟨subd10_5_155, List.forall_mem_cons.2 ⟨subd10_5_156, List.forall_mem_cons.2 ⟨subd10_5_157, List.forall_mem_cons.2 ⟨subd10_5_158, List.forall_mem_cons.2 ⟨subd10_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_160 : subd10_5 [-1, 1, 9] = true := by decide +kernel
theorem subd10_5_161 : subd10_5 [-1, 1, 10] = true := by decide +kernel
theorem subd10_5_162 : subd10_5 [-1, 2, -8] = true := by decide +kernel
theorem subd10_5_163 : subd10_5 [-1, 2, -7] = true := by decide +kernel
theorem subd10_5_164 : subd10_5 [-1, 2, -6] = true := by decide +kernel
theorem subd10_5_165 : subd10_5 [-1, 2, -5] = true := by decide +kernel
theorem subd10_5_166 : subd10_5 [-1, 2, -4] = true := by decide +kernel
theorem subd10_5_167 : subd10_5 [-1, 2, -3] = true := by decide +kernel
theorem subd10_5_168 : subd10_5 [-1, 2, -2] = true := by decide +kernel
theorem subd10_5_169 : subd10_5 [-1, 2, -1] = true := by decide +kernel
theorem subd10_5_170 : subd10_5 [-1, 2, 0] = true := by decide +kernel
theorem subd10_5_171 : subd10_5 [-1, 2, 1] = true := by decide +kernel
theorem subd10_5_172 : subd10_5 [-1, 2, 2] = true := by decide +kernel
theorem subd10_5_173 : subd10_5 [-1, 2, 3] = true := by decide +kernel
theorem subd10_5_174 : subd10_5 [-1, 2, 4] = true := by decide +kernel
theorem subd10_5_175 : subd10_5 [-1, 2, 5] = true := by decide +kernel
theorem subd10_5_176 : subd10_5 [-1, 2, 6] = true := by decide +kernel
theorem subd10_5_177 : subd10_5 [-1, 2, 7] = true := by decide +kernel
theorem subd10_5_178 : subd10_5 [-1, 2, 8] = true := by decide +kernel
theorem subd10_5_179 : subd10_5 [-1, 2, 9] = true := by decide +kernel
theorem subd10_5_180 : subd10_5 [-1, 3] = true := by decide +kernel
theorem subd10_5_181 : subd10_5 [0, -4] = true := by decide +kernel
theorem subd10_5_182 : subd10_5 [0, -3] = true := by decide +kernel
theorem subd10_5_183 : subd10_5 [0, -2, -10] = true := by decide +kernel
theorem subd10_5_184 : subd10_5 [0, -2, -9] = true := by decide +kernel
theorem subd10_5_185 : subd10_5 [0, -2, -8] = true := by decide +kernel
theorem subd10_5_186 : subd10_5 [0, -2, -7] = true := by decide +kernel
theorem subd10_5_187 : subd10_5 [0, -2, -6] = true := by decide +kernel
theorem subd10_5_188 : subd10_5 [0, -2, -5] = true := by decide +kernel
theorem subd10_5_189 : subd10_5 [0, -2, -4] = true := by decide +kernel
theorem subd10_5_190 : subd10_5 [0, -2, -3] = true := by decide +kernel
theorem subd10_5_191 : subd10_5 [0, -2, -2] = true := by decide +kernel
theorem sbd10_5_5 : ∀ q ∈ blkd10_5_5, subd10_5 q = true := by
  unfold blkd10_5_5
  exact List.forall_mem_cons.2 ⟨subd10_5_160, List.forall_mem_cons.2 ⟨subd10_5_161, List.forall_mem_cons.2 ⟨subd10_5_162, List.forall_mem_cons.2 ⟨subd10_5_163, List.forall_mem_cons.2 ⟨subd10_5_164, List.forall_mem_cons.2 ⟨subd10_5_165, List.forall_mem_cons.2 ⟨subd10_5_166, List.forall_mem_cons.2 ⟨subd10_5_167, List.forall_mem_cons.2 ⟨subd10_5_168, List.forall_mem_cons.2 ⟨subd10_5_169, List.forall_mem_cons.2 ⟨subd10_5_170, List.forall_mem_cons.2 ⟨subd10_5_171, List.forall_mem_cons.2 ⟨subd10_5_172, List.forall_mem_cons.2 ⟨subd10_5_173, List.forall_mem_cons.2 ⟨subd10_5_174, List.forall_mem_cons.2 ⟨subd10_5_175, List.forall_mem_cons.2 ⟨subd10_5_176, List.forall_mem_cons.2 ⟨subd10_5_177, List.forall_mem_cons.2 ⟨subd10_5_178, List.forall_mem_cons.2 ⟨subd10_5_179, List.forall_mem_cons.2 ⟨subd10_5_180, List.forall_mem_cons.2 ⟨subd10_5_181, List.forall_mem_cons.2 ⟨subd10_5_182, List.forall_mem_cons.2 ⟨subd10_5_183, List.forall_mem_cons.2 ⟨subd10_5_184, List.forall_mem_cons.2 ⟨subd10_5_185, List.forall_mem_cons.2 ⟨subd10_5_186, List.forall_mem_cons.2 ⟨subd10_5_187, List.forall_mem_cons.2 ⟨subd10_5_188, List.forall_mem_cons.2 ⟨subd10_5_189, List.forall_mem_cons.2 ⟨subd10_5_190, List.forall_mem_cons.2 ⟨subd10_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_192 : subd10_5 [0, -2, -1] = true := by decide +kernel
theorem subd10_5_193 : subd10_5 [0, -2, 0] = true := by decide +kernel
theorem subd10_5_194 : subd10_5 [0, -2, 1] = true := by decide +kernel
theorem subd10_5_195 : subd10_5 [0, -2, 2] = true := by decide +kernel
theorem subd10_5_196 : subd10_5 [0, -2, 3] = true := by decide +kernel
theorem subd10_5_197 : subd10_5 [0, -2, 4] = true := by decide +kernel
theorem subd10_5_198 : subd10_5 [0, -2, 5] = true := by decide +kernel
theorem subd10_5_199 : subd10_5 [0, -2, 6] = true := by decide +kernel
theorem subd10_5_200 : subd10_5 [0, -2, 7] = true := by decide +kernel
theorem subd10_5_201 : subd10_5 [0, -2, 8] = true := by decide +kernel
theorem subd10_5_202 : subd10_5 [0, -1, -11] = true := by decide +kernel
theorem subd10_5_203 : subd10_5 [0, -1, -10] = true := by decide +kernel
theorem subd10_5_204 : subd10_5 [0, -1, -9] = true := by decide +kernel
theorem subd10_5_205 : subd10_5 [0, -1, -8] = true := by decide +kernel
theorem subd10_5_206 : subd10_5 [0, -1, -7] = true := by decide +kernel
theorem subd10_5_207 : subd10_5 [0, -1, -6] = true := by decide +kernel
theorem subd10_5_208 : subd10_5 [0, -1, -5] = true := by decide +kernel
theorem subd10_5_209 : subd10_5 [0, -1, -4] = true := by decide +kernel
theorem subd10_5_210 : subd10_5 [0, -1, -3] = true := by decide +kernel
theorem subd10_5_211 : subd10_5 [0, -1, -2] = true := by decide +kernel
theorem subd10_5_212 : subd10_5 [0, -1, -1] = true := by decide +kernel
theorem subd10_5_213 : subd10_5 [0, -1, 0] = true := by decide +kernel
theorem subd10_5_214 : subd10_5 [0, -1, 1] = true := by decide +kernel
theorem subd10_5_215 : subd10_5 [0, -1, 2] = true := by decide +kernel
theorem subd10_5_216 : subd10_5 [0, -1, 3] = true := by decide +kernel
theorem subd10_5_217 : subd10_5 [0, -1, 4] = true := by decide +kernel
theorem subd10_5_218 : subd10_5 [0, -1, 5] = true := by decide +kernel
theorem subd10_5_219 : subd10_5 [0, -1, 6] = true := by decide +kernel
theorem subd10_5_220 : subd10_5 [0, -1, 7] = true := by decide +kernel
theorem subd10_5_221 : subd10_5 [0, -1, 8] = true := by decide +kernel
theorem subd10_5_222 : subd10_5 [0, -1, 9] = true := by decide +kernel
theorem subd10_5_223 : subd10_5 [0, -1, 10] = true := by decide +kernel
theorem sbd10_5_6 : ∀ q ∈ blkd10_5_6, subd10_5 q = true := by
  unfold blkd10_5_6
  exact List.forall_mem_cons.2 ⟨subd10_5_192, List.forall_mem_cons.2 ⟨subd10_5_193, List.forall_mem_cons.2 ⟨subd10_5_194, List.forall_mem_cons.2 ⟨subd10_5_195, List.forall_mem_cons.2 ⟨subd10_5_196, List.forall_mem_cons.2 ⟨subd10_5_197, List.forall_mem_cons.2 ⟨subd10_5_198, List.forall_mem_cons.2 ⟨subd10_5_199, List.forall_mem_cons.2 ⟨subd10_5_200, List.forall_mem_cons.2 ⟨subd10_5_201, List.forall_mem_cons.2 ⟨subd10_5_202, List.forall_mem_cons.2 ⟨subd10_5_203, List.forall_mem_cons.2 ⟨subd10_5_204, List.forall_mem_cons.2 ⟨subd10_5_205, List.forall_mem_cons.2 ⟨subd10_5_206, List.forall_mem_cons.2 ⟨subd10_5_207, List.forall_mem_cons.2 ⟨subd10_5_208, List.forall_mem_cons.2 ⟨subd10_5_209, List.forall_mem_cons.2 ⟨subd10_5_210, List.forall_mem_cons.2 ⟨subd10_5_211, List.forall_mem_cons.2 ⟨subd10_5_212, List.forall_mem_cons.2 ⟨subd10_5_213, List.forall_mem_cons.2 ⟨subd10_5_214, List.forall_mem_cons.2 ⟨subd10_5_215, List.forall_mem_cons.2 ⟨subd10_5_216, List.forall_mem_cons.2 ⟨subd10_5_217, List.forall_mem_cons.2 ⟨subd10_5_218, List.forall_mem_cons.2 ⟨subd10_5_219, List.forall_mem_cons.2 ⟨subd10_5_220, List.forall_mem_cons.2 ⟨subd10_5_221, List.forall_mem_cons.2 ⟨subd10_5_222, List.forall_mem_cons.2 ⟨subd10_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_224 : subd10_5 [0, 0, -12] = true := by decide +kernel
theorem subd10_5_225 : subd10_5 [0, 0, -11] = true := by decide +kernel
theorem subd10_5_226 : subd10_5 [0, 0, -10] = true := by decide +kernel
theorem subd10_5_227 : subd10_5 [0, 0, -9] = true := by decide +kernel
theorem subd10_5_228 : subd10_5 [0, 0, -8] = true := by decide +kernel
theorem subd10_5_229 : subd10_5 [0, 0, -7] = true := by decide +kernel
theorem subd10_5_230 : subd10_5 [0, 0, -6] = true := by decide +kernel
theorem subd10_5_231 : subd10_5 [0, 0, -5] = true := by decide +kernel
theorem subd10_5_232 : subd10_5 [0, 0, -4] = true := by decide +kernel
theorem subd10_5_233 : subd10_5 [0, 0, -3] = true := by decide +kernel
theorem subd10_5_234 : subd10_5 [0, 0, -2] = true := by decide +kernel
theorem subd10_5_235 : subd10_5 [0, 0, -1] = true := by decide +kernel
theorem subd10_5_236 : subd10_5 [0, 0, 0] = true := by decide +kernel
theorem subd10_5_237 : subd10_5 [0, 0, 1] = true := by decide +kernel
theorem subd10_5_238 : subd10_5 [0, 0, 2] = true := by decide +kernel
theorem subd10_5_239 : subd10_5 [0, 0, 3] = true := by decide +kernel
theorem subd10_5_240 : subd10_5 [0, 0, 4] = true := by decide +kernel
theorem subd10_5_241 : subd10_5 [0, 0, 5] = true := by decide +kernel
theorem subd10_5_242 : subd10_5 [0, 0, 6] = true := by decide +kernel
theorem subd10_5_243 : subd10_5 [0, 0, 7] = true := by decide +kernel
theorem subd10_5_244 : subd10_5 [0, 0, 8] = true := by decide +kernel
theorem subd10_5_245 : subd10_5 [0, 0, 9] = true := by decide +kernel
theorem subd10_5_246 : subd10_5 [0, 0, 10] = true := by decide +kernel
theorem subd10_5_247 : subd10_5 [0, 0, 11] = true := by decide +kernel
theorem subd10_5_248 : subd10_5 [0, 1, -11] = true := by decide +kernel
theorem subd10_5_249 : subd10_5 [0, 1, -10] = true := by decide +kernel
theorem subd10_5_250 : subd10_5 [0, 1, -9] = true := by decide +kernel
theorem subd10_5_251 : subd10_5 [0, 1, -8] = true := by decide +kernel
theorem subd10_5_252 : subd10_5 [0, 1, -7] = true := by decide +kernel
theorem subd10_5_253 : subd10_5 [0, 1, -6] = true := by decide +kernel
theorem subd10_5_254 : subd10_5 [0, 1, -5] = true := by decide +kernel
theorem subd10_5_255 : subd10_5 [0, 1, -4] = true := by decide +kernel
theorem sbd10_5_7 : ∀ q ∈ blkd10_5_7, subd10_5 q = true := by
  unfold blkd10_5_7
  exact List.forall_mem_cons.2 ⟨subd10_5_224, List.forall_mem_cons.2 ⟨subd10_5_225, List.forall_mem_cons.2 ⟨subd10_5_226, List.forall_mem_cons.2 ⟨subd10_5_227, List.forall_mem_cons.2 ⟨subd10_5_228, List.forall_mem_cons.2 ⟨subd10_5_229, List.forall_mem_cons.2 ⟨subd10_5_230, List.forall_mem_cons.2 ⟨subd10_5_231, List.forall_mem_cons.2 ⟨subd10_5_232, List.forall_mem_cons.2 ⟨subd10_5_233, List.forall_mem_cons.2 ⟨subd10_5_234, List.forall_mem_cons.2 ⟨subd10_5_235, List.forall_mem_cons.2 ⟨subd10_5_236, List.forall_mem_cons.2 ⟨subd10_5_237, List.forall_mem_cons.2 ⟨subd10_5_238, List.forall_mem_cons.2 ⟨subd10_5_239, List.forall_mem_cons.2 ⟨subd10_5_240, List.forall_mem_cons.2 ⟨subd10_5_241, List.forall_mem_cons.2 ⟨subd10_5_242, List.forall_mem_cons.2 ⟨subd10_5_243, List.forall_mem_cons.2 ⟨subd10_5_244, List.forall_mem_cons.2 ⟨subd10_5_245, List.forall_mem_cons.2 ⟨subd10_5_246, List.forall_mem_cons.2 ⟨subd10_5_247, List.forall_mem_cons.2 ⟨subd10_5_248, List.forall_mem_cons.2 ⟨subd10_5_249, List.forall_mem_cons.2 ⟨subd10_5_250, List.forall_mem_cons.2 ⟨subd10_5_251, List.forall_mem_cons.2 ⟨subd10_5_252, List.forall_mem_cons.2 ⟨subd10_5_253, List.forall_mem_cons.2 ⟨subd10_5_254, List.forall_mem_cons.2 ⟨subd10_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_256 : subd10_5 [0, 1, -3] = true := by decide +kernel
theorem subd10_5_257 : subd10_5 [0, 1, -2] = true := by decide +kernel
theorem subd10_5_258 : subd10_5 [0, 1, -1] = true := by decide +kernel
theorem subd10_5_259 : subd10_5 [0, 1, 0] = true := by decide +kernel
theorem subd10_5_260 : subd10_5 [0, 1, 1] = true := by decide +kernel
theorem subd10_5_261 : subd10_5 [0, 1, 2] = true := by decide +kernel
theorem subd10_5_262 : subd10_5 [0, 1, 3] = true := by decide +kernel
theorem subd10_5_263 : subd10_5 [0, 1, 4] = true := by decide +kernel
theorem subd10_5_264 : subd10_5 [0, 1, 5] = true := by decide +kernel
theorem subd10_5_265 : subd10_5 [0, 1, 6] = true := by decide +kernel
theorem subd10_5_266 : subd10_5 [0, 1, 7] = true := by decide +kernel
theorem subd10_5_267 : subd10_5 [0, 1, 8] = true := by decide +kernel
theorem subd10_5_268 : subd10_5 [0, 1, 9] = true := by decide +kernel
theorem subd10_5_269 : subd10_5 [0, 1, 10] = true := by decide +kernel
theorem subd10_5_270 : subd10_5 [0, 2, -9] = true := by decide +kernel
theorem subd10_5_271 : subd10_5 [0, 2, -8] = true := by decide +kernel
theorem subd10_5_272 : subd10_5 [0, 2, -7] = true := by decide +kernel
theorem subd10_5_273 : subd10_5 [0, 2, -6] = true := by decide +kernel
theorem subd10_5_274 : subd10_5 [0, 2, -5] = true := by decide +kernel
theorem subd10_5_275 : subd10_5 [0, 2, -4] = true := by decide +kernel
theorem subd10_5_276 : subd10_5 [0, 2, -3] = true := by decide +kernel
theorem subd10_5_277 : subd10_5 [0, 2, -2] = true := by decide +kernel
theorem subd10_5_278 : subd10_5 [0, 2, -1] = true := by decide +kernel
theorem subd10_5_279 : subd10_5 [0, 2, 0] = true := by decide +kernel
theorem subd10_5_280 : subd10_5 [0, 2, 1] = true := by decide +kernel
theorem subd10_5_281 : subd10_5 [0, 2, 2] = true := by decide +kernel
theorem subd10_5_282 : subd10_5 [0, 2, 3] = true := by decide +kernel
theorem subd10_5_283 : subd10_5 [0, 2, 4] = true := by decide +kernel
theorem subd10_5_284 : subd10_5 [0, 2, 5] = true := by decide +kernel
theorem subd10_5_285 : subd10_5 [0, 2, 6] = true := by decide +kernel
theorem subd10_5_286 : subd10_5 [0, 2, 7] = true := by decide +kernel
theorem subd10_5_287 : subd10_5 [0, 2, 8] = true := by decide +kernel
theorem sbd10_5_8 : ∀ q ∈ blkd10_5_8, subd10_5 q = true := by
  unfold blkd10_5_8
  exact List.forall_mem_cons.2 ⟨subd10_5_256, List.forall_mem_cons.2 ⟨subd10_5_257, List.forall_mem_cons.2 ⟨subd10_5_258, List.forall_mem_cons.2 ⟨subd10_5_259, List.forall_mem_cons.2 ⟨subd10_5_260, List.forall_mem_cons.2 ⟨subd10_5_261, List.forall_mem_cons.2 ⟨subd10_5_262, List.forall_mem_cons.2 ⟨subd10_5_263, List.forall_mem_cons.2 ⟨subd10_5_264, List.forall_mem_cons.2 ⟨subd10_5_265, List.forall_mem_cons.2 ⟨subd10_5_266, List.forall_mem_cons.2 ⟨subd10_5_267, List.forall_mem_cons.2 ⟨subd10_5_268, List.forall_mem_cons.2 ⟨subd10_5_269, List.forall_mem_cons.2 ⟨subd10_5_270, List.forall_mem_cons.2 ⟨subd10_5_271, List.forall_mem_cons.2 ⟨subd10_5_272, List.forall_mem_cons.2 ⟨subd10_5_273, List.forall_mem_cons.2 ⟨subd10_5_274, List.forall_mem_cons.2 ⟨subd10_5_275, List.forall_mem_cons.2 ⟨subd10_5_276, List.forall_mem_cons.2 ⟨subd10_5_277, List.forall_mem_cons.2 ⟨subd10_5_278, List.forall_mem_cons.2 ⟨subd10_5_279, List.forall_mem_cons.2 ⟨subd10_5_280, List.forall_mem_cons.2 ⟨subd10_5_281, List.forall_mem_cons.2 ⟨subd10_5_282, List.forall_mem_cons.2 ⟨subd10_5_283, List.forall_mem_cons.2 ⟨subd10_5_284, List.forall_mem_cons.2 ⟨subd10_5_285, List.forall_mem_cons.2 ⟨subd10_5_286, List.forall_mem_cons.2 ⟨subd10_5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_288 : subd10_5 [0, 2, 9] = true := by decide +kernel
theorem subd10_5_289 : subd10_5 [0, 3] = true := by decide +kernel
theorem subd10_5_290 : subd10_5 [1, -4] = true := by decide +kernel
theorem subd10_5_291 : subd10_5 [1, -3] = true := by decide +kernel
theorem subd10_5_292 : subd10_5 [1, -2, -10] = true := by decide +kernel
theorem subd10_5_293 : subd10_5 [1, -2, -9] = true := by decide +kernel
theorem subd10_5_294 : subd10_5 [1, -2, -8] = true := by decide +kernel
theorem subd10_5_295 : subd10_5 [1, -2, -7] = true := by decide +kernel
theorem subd10_5_296 : subd10_5 [1, -2, -6] = true := by decide +kernel
theorem subd10_5_297 : subd10_5 [1, -2, -5] = true := by decide +kernel
theorem subd10_5_298 : subd10_5 [1, -2, -4] = true := by decide +kernel
theorem subd10_5_299 : subd10_5 [1, -2, -3] = true := by decide +kernel
theorem subd10_5_300 : subd10_5 [1, -2, -2] = true := by decide +kernel
theorem subd10_5_301 : subd10_5 [1, -2, -1] = true := by decide +kernel
theorem subd10_5_302 : subd10_5 [1, -2, 0] = true := by decide +kernel
theorem subd10_5_303 : subd10_5 [1, -2, 1] = true := by decide +kernel
theorem subd10_5_304 : subd10_5 [1, -2, 2] = true := by decide +kernel
theorem subd10_5_305 : subd10_5 [1, -2, 3] = true := by decide +kernel
theorem subd10_5_306 : subd10_5 [1, -2, 4] = true := by decide +kernel
theorem subd10_5_307 : subd10_5 [1, -2, 5] = true := by decide +kernel
theorem subd10_5_308 : subd10_5 [1, -2, 6] = true := by decide +kernel
theorem subd10_5_309 : subd10_5 [1, -2, 7] = true := by decide +kernel
theorem subd10_5_310 : subd10_5 [1, -1, -11] = true := by decide +kernel
theorem subd10_5_311 : subd10_5 [1, -1, -10] = true := by decide +kernel
theorem subd10_5_312 : subd10_5 [1, -1, -9] = true := by decide +kernel
theorem subd10_5_313 : subd10_5 [1, -1, -8] = true := by decide +kernel
theorem subd10_5_314 : subd10_5 [1, -1, -7] = true := by decide +kernel
theorem subd10_5_315 : subd10_5 [1, -1, -6] = true := by decide +kernel
theorem subd10_5_316 : subd10_5 [1, -1, -5] = true := by decide +kernel
theorem subd10_5_317 : subd10_5 [1, -1, -4] = true := by decide +kernel
theorem subd10_5_318 : subd10_5 [1, -1, -3] = true := by decide +kernel
theorem subd10_5_319 : subd10_5 [1, -1, -2] = true := by decide +kernel
theorem sbd10_5_9 : ∀ q ∈ blkd10_5_9, subd10_5 q = true := by
  unfold blkd10_5_9
  exact List.forall_mem_cons.2 ⟨subd10_5_288, List.forall_mem_cons.2 ⟨subd10_5_289, List.forall_mem_cons.2 ⟨subd10_5_290, List.forall_mem_cons.2 ⟨subd10_5_291, List.forall_mem_cons.2 ⟨subd10_5_292, List.forall_mem_cons.2 ⟨subd10_5_293, List.forall_mem_cons.2 ⟨subd10_5_294, List.forall_mem_cons.2 ⟨subd10_5_295, List.forall_mem_cons.2 ⟨subd10_5_296, List.forall_mem_cons.2 ⟨subd10_5_297, List.forall_mem_cons.2 ⟨subd10_5_298, List.forall_mem_cons.2 ⟨subd10_5_299, List.forall_mem_cons.2 ⟨subd10_5_300, List.forall_mem_cons.2 ⟨subd10_5_301, List.forall_mem_cons.2 ⟨subd10_5_302, List.forall_mem_cons.2 ⟨subd10_5_303, List.forall_mem_cons.2 ⟨subd10_5_304, List.forall_mem_cons.2 ⟨subd10_5_305, List.forall_mem_cons.2 ⟨subd10_5_306, List.forall_mem_cons.2 ⟨subd10_5_307, List.forall_mem_cons.2 ⟨subd10_5_308, List.forall_mem_cons.2 ⟨subd10_5_309, List.forall_mem_cons.2 ⟨subd10_5_310, List.forall_mem_cons.2 ⟨subd10_5_311, List.forall_mem_cons.2 ⟨subd10_5_312, List.forall_mem_cons.2 ⟨subd10_5_313, List.forall_mem_cons.2 ⟨subd10_5_314, List.forall_mem_cons.2 ⟨subd10_5_315, List.forall_mem_cons.2 ⟨subd10_5_316, List.forall_mem_cons.2 ⟨subd10_5_317, List.forall_mem_cons.2 ⟨subd10_5_318, List.forall_mem_cons.2 ⟨subd10_5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_320 : subd10_5 [1, -1, -1] = true := by decide +kernel
theorem subd10_5_321 : subd10_5 [1, -1, 0] = true := by decide +kernel
theorem subd10_5_322 : subd10_5 [1, -1, 1] = true := by decide +kernel
theorem subd10_5_323 : subd10_5 [1, -1, 2] = true := by decide +kernel
theorem subd10_5_324 : subd10_5 [1, -1, 3] = true := by decide +kernel
theorem subd10_5_325 : subd10_5 [1, -1, 4] = true := by decide +kernel
theorem subd10_5_326 : subd10_5 [1, -1, 5] = true := by decide +kernel
theorem subd10_5_327 : subd10_5 [1, -1, 6] = true := by decide +kernel
theorem subd10_5_328 : subd10_5 [1, -1, 7] = true := by decide +kernel
theorem subd10_5_329 : subd10_5 [1, -1, 8] = true := by decide +kernel
theorem subd10_5_330 : subd10_5 [1, -1, 9] = true := by decide +kernel
theorem subd10_5_331 : subd10_5 [1, 0, -11] = true := by decide +kernel
theorem subd10_5_332 : subd10_5 [1, 0, -10] = true := by decide +kernel
theorem subd10_5_333 : subd10_5 [1, 0, -9] = true := by decide +kernel
theorem subd10_5_334 : subd10_5 [1, 0, -8] = true := by decide +kernel
theorem subd10_5_335 : subd10_5 [1, 0, -7] = true := by decide +kernel
theorem subd10_5_336 : subd10_5 [1, 0, -6] = true := by decide +kernel
theorem subd10_5_337 : subd10_5 [1, 0, -5] = true := by decide +kernel
theorem subd10_5_338 : subd10_5 [1, 0, -4] = true := by decide +kernel
theorem subd10_5_339 : subd10_5 [1, 0, -3] = true := by decide +kernel
theorem subd10_5_340 : subd10_5 [1, 0, -2] = true := by decide +kernel
theorem subd10_5_341 : subd10_5 [1, 0, -1] = true := by decide +kernel
theorem subd10_5_342 : subd10_5 [1, 0, 0] = true := by decide +kernel
theorem subd10_5_343 : subd10_5 [1, 0, 1] = true := by decide +kernel
theorem subd10_5_344 : subd10_5 [1, 0, 2] = true := by decide +kernel
theorem subd10_5_345 : subd10_5 [1, 0, 3] = true := by decide +kernel
theorem subd10_5_346 : subd10_5 [1, 0, 4] = true := by decide +kernel
theorem subd10_5_347 : subd10_5 [1, 0, 5] = true := by decide +kernel
theorem subd10_5_348 : subd10_5 [1, 0, 6] = true := by decide +kernel
theorem subd10_5_349 : subd10_5 [1, 0, 7] = true := by decide +kernel
theorem subd10_5_350 : subd10_5 [1, 0, 8] = true := by decide +kernel
theorem subd10_5_351 : subd10_5 [1, 0, 9] = true := by decide +kernel
theorem sbd10_5_10 : ∀ q ∈ blkd10_5_10, subd10_5 q = true := by
  unfold blkd10_5_10
  exact List.forall_mem_cons.2 ⟨subd10_5_320, List.forall_mem_cons.2 ⟨subd10_5_321, List.forall_mem_cons.2 ⟨subd10_5_322, List.forall_mem_cons.2 ⟨subd10_5_323, List.forall_mem_cons.2 ⟨subd10_5_324, List.forall_mem_cons.2 ⟨subd10_5_325, List.forall_mem_cons.2 ⟨subd10_5_326, List.forall_mem_cons.2 ⟨subd10_5_327, List.forall_mem_cons.2 ⟨subd10_5_328, List.forall_mem_cons.2 ⟨subd10_5_329, List.forall_mem_cons.2 ⟨subd10_5_330, List.forall_mem_cons.2 ⟨subd10_5_331, List.forall_mem_cons.2 ⟨subd10_5_332, List.forall_mem_cons.2 ⟨subd10_5_333, List.forall_mem_cons.2 ⟨subd10_5_334, List.forall_mem_cons.2 ⟨subd10_5_335, List.forall_mem_cons.2 ⟨subd10_5_336, List.forall_mem_cons.2 ⟨subd10_5_337, List.forall_mem_cons.2 ⟨subd10_5_338, List.forall_mem_cons.2 ⟨subd10_5_339, List.forall_mem_cons.2 ⟨subd10_5_340, List.forall_mem_cons.2 ⟨subd10_5_341, List.forall_mem_cons.2 ⟨subd10_5_342, List.forall_mem_cons.2 ⟨subd10_5_343, List.forall_mem_cons.2 ⟨subd10_5_344, List.forall_mem_cons.2 ⟨subd10_5_345, List.forall_mem_cons.2 ⟨subd10_5_346, List.forall_mem_cons.2 ⟨subd10_5_347, List.forall_mem_cons.2 ⟨subd10_5_348, List.forall_mem_cons.2 ⟨subd10_5_349, List.forall_mem_cons.2 ⟨subd10_5_350, List.forall_mem_cons.2 ⟨subd10_5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_352 : subd10_5 [1, 0, 10] = true := by decide +kernel
theorem subd10_5_353 : subd10_5 [1, 1, -11] = true := by decide +kernel
theorem subd10_5_354 : subd10_5 [1, 1, -10] = true := by decide +kernel
theorem subd10_5_355 : subd10_5 [1, 1, -9] = true := by decide +kernel
theorem subd10_5_356 : subd10_5 [1, 1, -8] = true := by decide +kernel
theorem subd10_5_357 : subd10_5 [1, 1, -7] = true := by decide +kernel
theorem subd10_5_358 : subd10_5 [1, 1, -6] = true := by decide +kernel
theorem subd10_5_359 : subd10_5 [1, 1, -5] = true := by decide +kernel
theorem subd10_5_360 : subd10_5 [1, 1, -4] = true := by decide +kernel
theorem subd10_5_361 : subd10_5 [1, 1, -3] = true := by decide +kernel
theorem subd10_5_362 : subd10_5 [1, 1, -2] = true := by decide +kernel
theorem subd10_5_363 : subd10_5 [1, 1, -1] = true := by decide +kernel
theorem subd10_5_364 : subd10_5 [1, 1, 0] = true := by decide +kernel
theorem subd10_5_365 : subd10_5 [1, 1, 1] = true := by decide +kernel
theorem subd10_5_366 : subd10_5 [1, 1, 2] = true := by decide +kernel
theorem subd10_5_367 : subd10_5 [1, 1, 3] = true := by decide +kernel
theorem subd10_5_368 : subd10_5 [1, 1, 4] = true := by decide +kernel
theorem subd10_5_369 : subd10_5 [1, 1, 5] = true := by decide +kernel
theorem subd10_5_370 : subd10_5 [1, 1, 6] = true := by decide +kernel
theorem subd10_5_371 : subd10_5 [1, 1, 7] = true := by decide +kernel
theorem subd10_5_372 : subd10_5 [1, 1, 8] = true := by decide +kernel
theorem subd10_5_373 : subd10_5 [1, 1, 9] = true := by decide +kernel
theorem subd10_5_374 : subd10_5 [1, 2, -9] = true := by decide +kernel
theorem subd10_5_375 : subd10_5 [1, 2, -8] = true := by decide +kernel
theorem subd10_5_376 : subd10_5 [1, 2, -7] = true := by decide +kernel
theorem subd10_5_377 : subd10_5 [1, 2, -6] = true := by decide +kernel
theorem subd10_5_378 : subd10_5 [1, 2, -5] = true := by decide +kernel
theorem subd10_5_379 : subd10_5 [1, 2, -4] = true := by decide +kernel
theorem subd10_5_380 : subd10_5 [1, 2, -3] = true := by decide +kernel
theorem subd10_5_381 : subd10_5 [1, 2, -2] = true := by decide +kernel
theorem subd10_5_382 : subd10_5 [1, 2, -1] = true := by decide +kernel
theorem subd10_5_383 : subd10_5 [1, 2, 0] = true := by decide +kernel
theorem sbd10_5_11 : ∀ q ∈ blkd10_5_11, subd10_5 q = true := by
  unfold blkd10_5_11
  exact List.forall_mem_cons.2 ⟨subd10_5_352, List.forall_mem_cons.2 ⟨subd10_5_353, List.forall_mem_cons.2 ⟨subd10_5_354, List.forall_mem_cons.2 ⟨subd10_5_355, List.forall_mem_cons.2 ⟨subd10_5_356, List.forall_mem_cons.2 ⟨subd10_5_357, List.forall_mem_cons.2 ⟨subd10_5_358, List.forall_mem_cons.2 ⟨subd10_5_359, List.forall_mem_cons.2 ⟨subd10_5_360, List.forall_mem_cons.2 ⟨subd10_5_361, List.forall_mem_cons.2 ⟨subd10_5_362, List.forall_mem_cons.2 ⟨subd10_5_363, List.forall_mem_cons.2 ⟨subd10_5_364, List.forall_mem_cons.2 ⟨subd10_5_365, List.forall_mem_cons.2 ⟨subd10_5_366, List.forall_mem_cons.2 ⟨subd10_5_367, List.forall_mem_cons.2 ⟨subd10_5_368, List.forall_mem_cons.2 ⟨subd10_5_369, List.forall_mem_cons.2 ⟨subd10_5_370, List.forall_mem_cons.2 ⟨subd10_5_371, List.forall_mem_cons.2 ⟨subd10_5_372, List.forall_mem_cons.2 ⟨subd10_5_373, List.forall_mem_cons.2 ⟨subd10_5_374, List.forall_mem_cons.2 ⟨subd10_5_375, List.forall_mem_cons.2 ⟨subd10_5_376, List.forall_mem_cons.2 ⟨subd10_5_377, List.forall_mem_cons.2 ⟨subd10_5_378, List.forall_mem_cons.2 ⟨subd10_5_379, List.forall_mem_cons.2 ⟨subd10_5_380, List.forall_mem_cons.2 ⟨subd10_5_381, List.forall_mem_cons.2 ⟨subd10_5_382, List.forall_mem_cons.2 ⟨subd10_5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_384 : subd10_5 [1, 2, 1] = true := by decide +kernel
theorem subd10_5_385 : subd10_5 [1, 2, 2] = true := by decide +kernel
theorem subd10_5_386 : subd10_5 [1, 2, 3] = true := by decide +kernel
theorem subd10_5_387 : subd10_5 [1, 2, 4] = true := by decide +kernel
theorem subd10_5_388 : subd10_5 [1, 2, 5] = true := by decide +kernel
theorem subd10_5_389 : subd10_5 [1, 2, 6] = true := by decide +kernel
theorem subd10_5_390 : subd10_5 [1, 2, 7] = true := by decide +kernel
theorem subd10_5_391 : subd10_5 [1, 2, 8] = true := by decide +kernel
theorem subd10_5_392 : subd10_5 [1, 3] = true := by decide +kernel
theorem subd10_5_393 : subd10_5 [2, -3] = true := by decide +kernel
theorem subd10_5_394 : subd10_5 [2, -2] = true := by decide +kernel
theorem subd10_5_395 : subd10_5 [2, -1, -10] = true := by decide +kernel
theorem subd10_5_396 : subd10_5 [2, -1, -9] = true := by decide +kernel
theorem subd10_5_397 : subd10_5 [2, -1, -8] = true := by decide +kernel
theorem subd10_5_398 : subd10_5 [2, -1, -7] = true := by decide +kernel
theorem subd10_5_399 : subd10_5 [2, -1, -6] = true := by decide +kernel
theorem subd10_5_400 : subd10_5 [2, -1, -5] = true := by decide +kernel
theorem subd10_5_401 : subd10_5 [2, -1, -4] = true := by decide +kernel
theorem subd10_5_402 : subd10_5 [2, -1, -3] = true := by decide +kernel
theorem subd10_5_403 : subd10_5 [2, -1, -2] = true := by decide +kernel
theorem subd10_5_404 : subd10_5 [2, -1, -1] = true := by decide +kernel
theorem subd10_5_405 : subd10_5 [2, -1, 0] = true := by decide +kernel
theorem subd10_5_406 : subd10_5 [2, -1, 1] = true := by decide +kernel
theorem subd10_5_407 : subd10_5 [2, -1, 2] = true := by decide +kernel
theorem subd10_5_408 : subd10_5 [2, -1, 3] = true := by decide +kernel
theorem subd10_5_409 : subd10_5 [2, -1, 4] = true := by decide +kernel
theorem subd10_5_410 : subd10_5 [2, -1, 5] = true := by decide +kernel
theorem subd10_5_411 : subd10_5 [2, -1, 6] = true := by decide +kernel
theorem subd10_5_412 : subd10_5 [2, -1, 7] = true := by decide +kernel
theorem subd10_5_413 : subd10_5 [2, 0, -10] = true := by decide +kernel
theorem subd10_5_414 : subd10_5 [2, 0, -9] = true := by decide +kernel
theorem subd10_5_415 : subd10_5 [2, 0, -8] = true := by decide +kernel
theorem sbd10_5_12 : ∀ q ∈ blkd10_5_12, subd10_5 q = true := by
  unfold blkd10_5_12
  exact List.forall_mem_cons.2 ⟨subd10_5_384, List.forall_mem_cons.2 ⟨subd10_5_385, List.forall_mem_cons.2 ⟨subd10_5_386, List.forall_mem_cons.2 ⟨subd10_5_387, List.forall_mem_cons.2 ⟨subd10_5_388, List.forall_mem_cons.2 ⟨subd10_5_389, List.forall_mem_cons.2 ⟨subd10_5_390, List.forall_mem_cons.2 ⟨subd10_5_391, List.forall_mem_cons.2 ⟨subd10_5_392, List.forall_mem_cons.2 ⟨subd10_5_393, List.forall_mem_cons.2 ⟨subd10_5_394, List.forall_mem_cons.2 ⟨subd10_5_395, List.forall_mem_cons.2 ⟨subd10_5_396, List.forall_mem_cons.2 ⟨subd10_5_397, List.forall_mem_cons.2 ⟨subd10_5_398, List.forall_mem_cons.2 ⟨subd10_5_399, List.forall_mem_cons.2 ⟨subd10_5_400, List.forall_mem_cons.2 ⟨subd10_5_401, List.forall_mem_cons.2 ⟨subd10_5_402, List.forall_mem_cons.2 ⟨subd10_5_403, List.forall_mem_cons.2 ⟨subd10_5_404, List.forall_mem_cons.2 ⟨subd10_5_405, List.forall_mem_cons.2 ⟨subd10_5_406, List.forall_mem_cons.2 ⟨subd10_5_407, List.forall_mem_cons.2 ⟨subd10_5_408, List.forall_mem_cons.2 ⟨subd10_5_409, List.forall_mem_cons.2 ⟨subd10_5_410, List.forall_mem_cons.2 ⟨subd10_5_411, List.forall_mem_cons.2 ⟨subd10_5_412, List.forall_mem_cons.2 ⟨subd10_5_413, List.forall_mem_cons.2 ⟨subd10_5_414, List.forall_mem_cons.2 ⟨subd10_5_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_416 : subd10_5 [2, 0, -7] = true := by decide +kernel
theorem subd10_5_417 : subd10_5 [2, 0, -6] = true := by decide +kernel
theorem subd10_5_418 : subd10_5 [2, 0, -5] = true := by decide +kernel
theorem subd10_5_419 : subd10_5 [2, 0, -4] = true := by decide +kernel
theorem subd10_5_420 : subd10_5 [2, 0, -3] = true := by decide +kernel
theorem subd10_5_421 : subd10_5 [2, 0, -2] = true := by decide +kernel
theorem subd10_5_422 : subd10_5 [2, 0, -1] = true := by decide +kernel
theorem subd10_5_423 : subd10_5 [2, 0, 0] = true := by decide +kernel
theorem subd10_5_424 : subd10_5 [2, 0, 1] = true := by decide +kernel
theorem subd10_5_425 : subd10_5 [2, 0, 2] = true := by decide +kernel
theorem subd10_5_426 : subd10_5 [2, 0, 3] = true := by decide +kernel
theorem subd10_5_427 : subd10_5 [2, 0, 4] = true := by decide +kernel
theorem subd10_5_428 : subd10_5 [2, 0, 5] = true := by decide +kernel
theorem subd10_5_429 : subd10_5 [2, 0, 6] = true := by decide +kernel
theorem subd10_5_430 : subd10_5 [2, 0, 7] = true := by decide +kernel
theorem subd10_5_431 : subd10_5 [2, 0, 8] = true := by decide +kernel
theorem subd10_5_432 : subd10_5 [2, 1, -10] = true := by decide +kernel
theorem subd10_5_433 : subd10_5 [2, 1, -9] = true := by decide +kernel
theorem subd10_5_434 : subd10_5 [2, 1, -8] = true := by decide +kernel
theorem subd10_5_435 : subd10_5 [2, 1, -7] = true := by decide +kernel
theorem subd10_5_436 : subd10_5 [2, 1, -6] = true := by decide +kernel
theorem subd10_5_437 : subd10_5 [2, 1, -5] = true := by decide +kernel
theorem subd10_5_438 : subd10_5 [2, 1, -4] = true := by decide +kernel
theorem subd10_5_439 : subd10_5 [2, 1, -3] = true := by decide +kernel
theorem subd10_5_440 : subd10_5 [2, 1, -2] = true := by decide +kernel
theorem subd10_5_441 : subd10_5 [2, 1, -1] = true := by decide +kernel
theorem subd10_5_442 : subd10_5 [2, 1, 0] = true := by decide +kernel
theorem subd10_5_443 : subd10_5 [2, 1, 1] = true := by decide +kernel
theorem subd10_5_444 : subd10_5 [2, 1, 2] = true := by decide +kernel
theorem subd10_5_445 : subd10_5 [2, 1, 3] = true := by decide +kernel
theorem subd10_5_446 : subd10_5 [2, 1, 4] = true := by decide +kernel
theorem subd10_5_447 : subd10_5 [2, 1, 5] = true := by decide +kernel
theorem sbd10_5_13 : ∀ q ∈ blkd10_5_13, subd10_5 q = true := by
  unfold blkd10_5_13
  exact List.forall_mem_cons.2 ⟨subd10_5_416, List.forall_mem_cons.2 ⟨subd10_5_417, List.forall_mem_cons.2 ⟨subd10_5_418, List.forall_mem_cons.2 ⟨subd10_5_419, List.forall_mem_cons.2 ⟨subd10_5_420, List.forall_mem_cons.2 ⟨subd10_5_421, List.forall_mem_cons.2 ⟨subd10_5_422, List.forall_mem_cons.2 ⟨subd10_5_423, List.forall_mem_cons.2 ⟨subd10_5_424, List.forall_mem_cons.2 ⟨subd10_5_425, List.forall_mem_cons.2 ⟨subd10_5_426, List.forall_mem_cons.2 ⟨subd10_5_427, List.forall_mem_cons.2 ⟨subd10_5_428, List.forall_mem_cons.2 ⟨subd10_5_429, List.forall_mem_cons.2 ⟨subd10_5_430, List.forall_mem_cons.2 ⟨subd10_5_431, List.forall_mem_cons.2 ⟨subd10_5_432, List.forall_mem_cons.2 ⟨subd10_5_433, List.forall_mem_cons.2 ⟨subd10_5_434, List.forall_mem_cons.2 ⟨subd10_5_435, List.forall_mem_cons.2 ⟨subd10_5_436, List.forall_mem_cons.2 ⟨subd10_5_437, List.forall_mem_cons.2 ⟨subd10_5_438, List.forall_mem_cons.2 ⟨subd10_5_439, List.forall_mem_cons.2 ⟨subd10_5_440, List.forall_mem_cons.2 ⟨subd10_5_441, List.forall_mem_cons.2 ⟨subd10_5_442, List.forall_mem_cons.2 ⟨subd10_5_443, List.forall_mem_cons.2 ⟨subd10_5_444, List.forall_mem_cons.2 ⟨subd10_5_445, List.forall_mem_cons.2 ⟨subd10_5_446, List.forall_mem_cons.2 ⟨subd10_5_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_448 : subd10_5 [2, 1, 6] = true := by decide +kernel
theorem subd10_5_449 : subd10_5 [2, 1, 7] = true := by decide +kernel
theorem subd10_5_450 : subd10_5 [2, 2, -8] = true := by decide +kernel
theorem subd10_5_451 : subd10_5 [2, 2, -7] = true := by decide +kernel
theorem subd10_5_452 : subd10_5 [2, 2, -6] = true := by decide +kernel
theorem subd10_5_453 : subd10_5 [2, 2, -5] = true := by decide +kernel
theorem subd10_5_454 : subd10_5 [2, 2, -4] = true := by decide +kernel
theorem subd10_5_455 : subd10_5 [2, 2, -3] = true := by decide +kernel
theorem subd10_5_456 : subd10_5 [2, 2, -2] = true := by decide +kernel
theorem subd10_5_457 : subd10_5 [2, 2, -1] = true := by decide +kernel
theorem subd10_5_458 : subd10_5 [2, 2, 0] = true := by decide +kernel
theorem subd10_5_459 : subd10_5 [2, 2, 1] = true := by decide +kernel
theorem subd10_5_460 : subd10_5 [2, 2, 2] = true := by decide +kernel
theorem subd10_5_461 : subd10_5 [2, 2, 3] = true := by decide +kernel
theorem subd10_5_462 : subd10_5 [2, 2, 4] = true := by decide +kernel
theorem subd10_5_463 : subd10_5 [2, 2, 5] = true := by decide +kernel
theorem subd10_5_464 : subd10_5 [2, 2, 6] = true := by decide +kernel
theorem subd10_5_465 : subd10_5 [2, 3] = true := by decide +kernel
theorem subd10_5_466 : subd10_5 [3, -2] = true := by decide +kernel
theorem subd10_5_467 : subd10_5 [3, -1] = true := by decide +kernel
theorem subd10_5_468 : subd10_5 [3, 0] = true := by decide +kernel
theorem subd10_5_469 : subd10_5 [3, 1] = true := by decide +kernel
theorem subd10_5_470 : subd10_5 [3, 2] = true := by decide +kernel
theorem sbd10_5_14 : ∀ q ∈ blkd10_5_14, subd10_5 q = true := by
  unfold blkd10_5_14
  exact List.forall_mem_cons.2 ⟨subd10_5_448, List.forall_mem_cons.2 ⟨subd10_5_449, List.forall_mem_cons.2 ⟨subd10_5_450, List.forall_mem_cons.2 ⟨subd10_5_451, List.forall_mem_cons.2 ⟨subd10_5_452, List.forall_mem_cons.2 ⟨subd10_5_453, List.forall_mem_cons.2 ⟨subd10_5_454, List.forall_mem_cons.2 ⟨subd10_5_455, List.forall_mem_cons.2 ⟨subd10_5_456, List.forall_mem_cons.2 ⟨subd10_5_457, List.forall_mem_cons.2 ⟨subd10_5_458, List.forall_mem_cons.2 ⟨subd10_5_459, List.forall_mem_cons.2 ⟨subd10_5_460, List.forall_mem_cons.2 ⟨subd10_5_461, List.forall_mem_cons.2 ⟨subd10_5_462, List.forall_mem_cons.2 ⟨subd10_5_463, List.forall_mem_cons.2 ⟨subd10_5_464, List.forall_mem_cons.2 ⟨subd10_5_465, List.forall_mem_cons.2 ⟨subd10_5_466, List.forall_mem_cons.2 ⟨subd10_5_467, List.forall_mem_cons.2 ⟨subd10_5_468, List.forall_mem_cons.2 ⟨subd10_5_469, List.forall_mem_cons.2 ⟨subd10_5_470, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
