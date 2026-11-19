import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_32 : subd10_3 [-4, -2, 6] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [-4, -2, 7] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [-4, -1, -7] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [-4, -1, -6] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [-4, -1, -5] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [-4, -1, -4] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [-4, -1, -3] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [-4, -1, -2] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [-4, -1, -1] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [-4, -1, 0] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [-4, -1, 1] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [-4, -1, 2] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [-4, -1, 3] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [-4, -1, 4] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [-4, -1, 5] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [-4, -1, 6] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [-4, -1, 7] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [-4, 0, -8] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [-4, 0, -7] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [-4, 0, -6] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [-4, 0, -5] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [-4, 0, -4] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [-4, 0, -3] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [-4, 0, -2] = true := by decide +kernel
theorem subd10_3_56 : subd10_3 [-4, 0, -1] = true := by decide +kernel
theorem subd10_3_57 : subd10_3 [-4, 0, 0] = true := by decide +kernel
theorem subd10_3_58 : subd10_3 [-4, 0, 1] = true := by decide +kernel
theorem subd10_3_59 : subd10_3 [-4, 0, 2] = true := by decide +kernel
theorem subd10_3_60 : subd10_3 [-4, 0, 3] = true := by decide +kernel
theorem subd10_3_61 : subd10_3 [-4, 0, 4] = true := by decide +kernel
theorem subd10_3_62 : subd10_3 [-4, 0, 5] = true := by decide +kernel
theorem subd10_3_63 : subd10_3 [-4, 0, 6] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_cons.2 ⟨subd10_3_56, List.forall_mem_cons.2 ⟨subd10_3_57, List.forall_mem_cons.2 ⟨subd10_3_58, List.forall_mem_cons.2 ⟨subd10_3_59, List.forall_mem_cons.2 ⟨subd10_3_60, List.forall_mem_cons.2 ⟨subd10_3_61, List.forall_mem_cons.2 ⟨subd10_3_62, List.forall_mem_cons.2 ⟨subd10_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_64 : subd10_3 [-4, 0, 7] = true := by decide +kernel
theorem subd10_3_65 : subd10_3 [-4, 1, -8] = true := by decide +kernel
theorem subd10_3_66 : subd10_3 [-4, 1, -7] = true := by decide +kernel
theorem subd10_3_67 : subd10_3 [-4, 1, -6] = true := by decide +kernel
theorem subd10_3_68 : subd10_3 [-4, 1, -5] = true := by decide +kernel
theorem subd10_3_69 : subd10_3 [-4, 1, -4] = true := by decide +kernel
theorem subd10_3_70 : subd10_3 [-4, 1, -3] = true := by decide +kernel
theorem subd10_3_71 : subd10_3 [-4, 1, -2] = true := by decide +kernel
theorem subd10_3_72 : subd10_3 [-4, 1, -1] = true := by decide +kernel
theorem subd10_3_73 : subd10_3 [-4, 1, 0] = true := by decide +kernel
theorem subd10_3_74 : subd10_3 [-4, 1, 1] = true := by decide +kernel
theorem subd10_3_75 : subd10_3 [-4, 1, 2] = true := by decide +kernel
theorem subd10_3_76 : subd10_3 [-4, 1, 3] = true := by decide +kernel
theorem subd10_3_77 : subd10_3 [-4, 1, 4] = true := by decide +kernel
theorem subd10_3_78 : subd10_3 [-4, 1, 5] = true := by decide +kernel
theorem subd10_3_79 : subd10_3 [-4, 1, 6] = true := by decide +kernel
theorem subd10_3_80 : subd10_3 [-4, 2, -8] = true := by decide +kernel
theorem subd10_3_81 : subd10_3 [-4, 2, -7] = true := by decide +kernel
theorem subd10_3_82 : subd10_3 [-4, 2, -6] = true := by decide +kernel
theorem subd10_3_83 : subd10_3 [-4, 2, -5] = true := by decide +kernel
theorem subd10_3_84 : subd10_3 [-4, 2, -4] = true := by decide +kernel
theorem subd10_3_85 : subd10_3 [-4, 2, -3] = true := by decide +kernel
theorem subd10_3_86 : subd10_3 [-4, 2, -2] = true := by decide +kernel
theorem subd10_3_87 : subd10_3 [-4, 2, -1] = true := by decide +kernel
theorem subd10_3_88 : subd10_3 [-4, 2, 0] = true := by decide +kernel
theorem subd10_3_89 : subd10_3 [-4, 2, 1] = true := by decide +kernel
theorem subd10_3_90 : subd10_3 [-4, 2, 2] = true := by decide +kernel
theorem subd10_3_91 : subd10_3 [-4, 2, 3] = true := by decide +kernel
theorem subd10_3_92 : subd10_3 [-4, 2, 4] = true := by decide +kernel
theorem subd10_3_93 : subd10_3 [-4, 2, 5] = true := by decide +kernel
theorem subd10_3_94 : subd10_3 [-4, 2, 6] = true := by decide +kernel
theorem subd10_3_95 : subd10_3 [-4, 3, -8] = true := by decide +kernel
theorem sbd10_3_2 : ∀ q ∈ blkd10_3_2, subd10_3 q = true := by
  unfold blkd10_3_2
  exact List.forall_mem_cons.2 ⟨subd10_3_64, List.forall_mem_cons.2 ⟨subd10_3_65, List.forall_mem_cons.2 ⟨subd10_3_66, List.forall_mem_cons.2 ⟨subd10_3_67, List.forall_mem_cons.2 ⟨subd10_3_68, List.forall_mem_cons.2 ⟨subd10_3_69, List.forall_mem_cons.2 ⟨subd10_3_70, List.forall_mem_cons.2 ⟨subd10_3_71, List.forall_mem_cons.2 ⟨subd10_3_72, List.forall_mem_cons.2 ⟨subd10_3_73, List.forall_mem_cons.2 ⟨subd10_3_74, List.forall_mem_cons.2 ⟨subd10_3_75, List.forall_mem_cons.2 ⟨subd10_3_76, List.forall_mem_cons.2 ⟨subd10_3_77, List.forall_mem_cons.2 ⟨subd10_3_78, List.forall_mem_cons.2 ⟨subd10_3_79, List.forall_mem_cons.2 ⟨subd10_3_80, List.forall_mem_cons.2 ⟨subd10_3_81, List.forall_mem_cons.2 ⟨subd10_3_82, List.forall_mem_cons.2 ⟨subd10_3_83, List.forall_mem_cons.2 ⟨subd10_3_84, List.forall_mem_cons.2 ⟨subd10_3_85, List.forall_mem_cons.2 ⟨subd10_3_86, List.forall_mem_cons.2 ⟨subd10_3_87, List.forall_mem_cons.2 ⟨subd10_3_88, List.forall_mem_cons.2 ⟨subd10_3_89, List.forall_mem_cons.2 ⟨subd10_3_90, List.forall_mem_cons.2 ⟨subd10_3_91, List.forall_mem_cons.2 ⟨subd10_3_92, List.forall_mem_cons.2 ⟨subd10_3_93, List.forall_mem_cons.2 ⟨subd10_3_94, List.forall_mem_cons.2 ⟨subd10_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_96 : subd10_3 [-4, 3, -7] = true := by decide +kernel
theorem subd10_3_97 : subd10_3 [-4, 3, -6] = true := by decide +kernel
theorem subd10_3_98 : subd10_3 [-4, 3, -5] = true := by decide +kernel
theorem subd10_3_99 : subd10_3 [-4, 3, -4] = true := by decide +kernel
theorem subd10_3_100 : subd10_3 [-4, 3, -3] = true := by decide +kernel
theorem subd10_3_101 : subd10_3 [-4, 3, -2] = true := by decide +kernel
theorem subd10_3_102 : subd10_3 [-4, 3, -1] = true := by decide +kernel
theorem subd10_3_103 : subd10_3 [-4, 3, 0] = true := by decide +kernel
theorem subd10_3_104 : subd10_3 [-4, 3, 1] = true := by decide +kernel
theorem subd10_3_105 : subd10_3 [-4, 3, 2] = true := by decide +kernel
theorem subd10_3_106 : subd10_3 [-4, 3, 3] = true := by decide +kernel
theorem subd10_3_107 : subd10_3 [-4, 3, 4] = true := by decide +kernel
theorem subd10_3_108 : subd10_3 [-4, 3, 5] = true := by decide +kernel
theorem subd10_3_109 : subd10_3 [-4, 4] = true := by decide +kernel
theorem subd10_3_110 : subd10_3 [-4, 5] = true := by decide +kernel
theorem subd10_3_111 : subd10_3 [-3, -6] = true := by decide +kernel
theorem subd10_3_112 : subd10_3 [-3, -5] = true := by decide +kernel
theorem subd10_3_113 : subd10_3 [-3, -4] = true := by decide +kernel
theorem subd10_3_114 : subd10_3 [-3, -3, -6] = true := by decide +kernel
theorem subd10_3_115 : subd10_3 [-3, -3, -5] = true := by decide +kernel
theorem subd10_3_116 : subd10_3 [-3, -3, -4] = true := by decide +kernel
theorem subd10_3_117 : subd10_3 [-3, -3, -3] = true := by decide +kernel
theorem subd10_3_118 : subd10_3 [-3, -3, -2] = true := by decide +kernel
theorem subd10_3_119 : subd10_3 [-3, -3, -1] = true := by decide +kernel
theorem subd10_3_120 : subd10_3 [-3, -3, 0] = true := by decide +kernel
theorem subd10_3_121 : subd10_3 [-3, -3, 1] = true := by decide +kernel
theorem subd10_3_122 : subd10_3 [-3, -3, 2] = true := by decide +kernel
theorem subd10_3_123 : subd10_3 [-3, -3, 3] = true := by decide +kernel
theorem subd10_3_124 : subd10_3 [-3, -3, 4] = true := by decide +kernel
theorem subd10_3_125 : subd10_3 [-3, -3, 5] = true := by decide +kernel
theorem subd10_3_126 : subd10_3 [-3, -3, 6] = true := by decide +kernel
theorem subd10_3_127 : subd10_3 [-3, -3, 7] = true := by decide +kernel
theorem sbd10_3_3 : ∀ q ∈ blkd10_3_3, subd10_3 q = true := by
  unfold blkd10_3_3
  exact List.forall_mem_cons.2 ⟨subd10_3_96, List.forall_mem_cons.2 ⟨subd10_3_97, List.forall_mem_cons.2 ⟨subd10_3_98, List.forall_mem_cons.2 ⟨subd10_3_99, List.forall_mem_cons.2 ⟨subd10_3_100, List.forall_mem_cons.2 ⟨subd10_3_101, List.forall_mem_cons.2 ⟨subd10_3_102, List.forall_mem_cons.2 ⟨subd10_3_103, List.forall_mem_cons.2 ⟨subd10_3_104, List.forall_mem_cons.2 ⟨subd10_3_105, List.forall_mem_cons.2 ⟨subd10_3_106, List.forall_mem_cons.2 ⟨subd10_3_107, List.forall_mem_cons.2 ⟨subd10_3_108, List.forall_mem_cons.2 ⟨subd10_3_109, List.forall_mem_cons.2 ⟨subd10_3_110, List.forall_mem_cons.2 ⟨subd10_3_111, List.forall_mem_cons.2 ⟨subd10_3_112, List.forall_mem_cons.2 ⟨subd10_3_113, List.forall_mem_cons.2 ⟨subd10_3_114, List.forall_mem_cons.2 ⟨subd10_3_115, List.forall_mem_cons.2 ⟨subd10_3_116, List.forall_mem_cons.2 ⟨subd10_3_117, List.forall_mem_cons.2 ⟨subd10_3_118, List.forall_mem_cons.2 ⟨subd10_3_119, List.forall_mem_cons.2 ⟨subd10_3_120, List.forall_mem_cons.2 ⟨subd10_3_121, List.forall_mem_cons.2 ⟨subd10_3_122, List.forall_mem_cons.2 ⟨subd10_3_123, List.forall_mem_cons.2 ⟨subd10_3_124, List.forall_mem_cons.2 ⟨subd10_3_125, List.forall_mem_cons.2 ⟨subd10_3_126, List.forall_mem_cons.2 ⟨subd10_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_128 : subd10_3 [-3, -2, -7] = true := by decide +kernel
theorem subd10_3_129 : subd10_3 [-3, -2, -6] = true := by decide +kernel
theorem subd10_3_130 : subd10_3 [-3, -2, -5] = true := by decide +kernel
theorem subd10_3_131 : subd10_3 [-3, -2, -4] = true := by decide +kernel
theorem subd10_3_132 : subd10_3 [-3, -2, -3] = true := by decide +kernel
theorem subd10_3_133 : subd10_3 [-3, -2, -2] = true := by decide +kernel
theorem subd10_3_134 : subd10_3 [-3, -2, -1] = true := by decide +kernel
theorem subd10_3_135 : subd10_3 [-3, -2, 0] = true := by decide +kernel
theorem subd10_3_136 : subd10_3 [-3, -2, 1] = true := by decide +kernel
theorem subd10_3_137 : subd10_3 [-3, -2, 2] = true := by decide +kernel
theorem subd10_3_138 : subd10_3 [-3, -2, 3] = true := by decide +kernel
theorem subd10_3_139 : subd10_3 [-3, -2, 4] = true := by decide +kernel
theorem subd10_3_140 : subd10_3 [-3, -2, 5] = true := by decide +kernel
theorem subd10_3_141 : subd10_3 [-3, -2, 6] = true := by decide +kernel
theorem subd10_3_142 : subd10_3 [-3, -2, 7] = true := by decide +kernel
theorem subd10_3_143 : subd10_3 [-3, -2, 8] = true := by decide +kernel
theorem subd10_3_144 : subd10_3 [-3, -1, -8] = true := by decide +kernel
theorem subd10_3_145 : subd10_3 [-3, -1, -7] = true := by decide +kernel
theorem subd10_3_146 : subd10_3 [-3, -1, -6] = true := by decide +kernel
theorem subd10_3_147 : subd10_3 [-3, -1, -5] = true := by decide +kernel
theorem subd10_3_148 : subd10_3 [-3, -1, -4] = true := by decide +kernel
theorem subd10_3_149 : subd10_3 [-3, -1, -3] = true := by decide +kernel
theorem subd10_3_150 : subd10_3 [-3, -1, -2] = true := by decide +kernel
theorem subd10_3_151 : subd10_3 [-3, -1, -1] = true := by decide +kernel
theorem subd10_3_152 : subd10_3 [-3, -1, 0] = true := by decide +kernel
theorem subd10_3_153 : subd10_3 [-3, -1, 1] = true := by decide +kernel
theorem subd10_3_154 : subd10_3 [-3, -1, 2] = true := by decide +kernel
theorem subd10_3_155 : subd10_3 [-3, -1, 3] = true := by decide +kernel
theorem subd10_3_156 : subd10_3 [-3, -1, 4] = true := by decide +kernel
theorem subd10_3_157 : subd10_3 [-3, -1, 5] = true := by decide +kernel
theorem subd10_3_158 : subd10_3 [-3, -1, 6] = true := by decide +kernel
theorem subd10_3_159 : subd10_3 [-3, -1, 7] = true := by decide +kernel
theorem sbd10_3_4 : ∀ q ∈ blkd10_3_4, subd10_3 q = true := by
  unfold blkd10_3_4
  exact List.forall_mem_cons.2 ⟨subd10_3_128, List.forall_mem_cons.2 ⟨subd10_3_129, List.forall_mem_cons.2 ⟨subd10_3_130, List.forall_mem_cons.2 ⟨subd10_3_131, List.forall_mem_cons.2 ⟨subd10_3_132, List.forall_mem_cons.2 ⟨subd10_3_133, List.forall_mem_cons.2 ⟨subd10_3_134, List.forall_mem_cons.2 ⟨subd10_3_135, List.forall_mem_cons.2 ⟨subd10_3_136, List.forall_mem_cons.2 ⟨subd10_3_137, List.forall_mem_cons.2 ⟨subd10_3_138, List.forall_mem_cons.2 ⟨subd10_3_139, List.forall_mem_cons.2 ⟨subd10_3_140, List.forall_mem_cons.2 ⟨subd10_3_141, List.forall_mem_cons.2 ⟨subd10_3_142, List.forall_mem_cons.2 ⟨subd10_3_143, List.forall_mem_cons.2 ⟨subd10_3_144, List.forall_mem_cons.2 ⟨subd10_3_145, List.forall_mem_cons.2 ⟨subd10_3_146, List.forall_mem_cons.2 ⟨subd10_3_147, List.forall_mem_cons.2 ⟨subd10_3_148, List.forall_mem_cons.2 ⟨subd10_3_149, List.forall_mem_cons.2 ⟨subd10_3_150, List.forall_mem_cons.2 ⟨subd10_3_151, List.forall_mem_cons.2 ⟨subd10_3_152, List.forall_mem_cons.2 ⟨subd10_3_153, List.forall_mem_cons.2 ⟨subd10_3_154, List.forall_mem_cons.2 ⟨subd10_3_155, List.forall_mem_cons.2 ⟨subd10_3_156, List.forall_mem_cons.2 ⟨subd10_3_157, List.forall_mem_cons.2 ⟨subd10_3_158, List.forall_mem_cons.2 ⟨subd10_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_160 : subd10_3 [-3, -1, 8] = true := by decide +kernel
theorem subd10_3_161 : subd10_3 [-3, 0, -9] = true := by decide +kernel
theorem subd10_3_162 : subd10_3 [-3, 0, -8] = true := by decide +kernel
theorem subd10_3_163 : subd10_3 [-3, 0, -7] = true := by decide +kernel
theorem subd10_3_164 : subd10_3 [-3, 0, -6] = true := by decide +kernel
theorem subd10_3_165 : subd10_3 [-3, 0, -5] = true := by decide +kernel
theorem subd10_3_166 : subd10_3 [-3, 0, -4] = true := by decide +kernel
theorem subd10_3_167 : subd10_3 [-3, 0, -3] = true := by decide +kernel
theorem subd10_3_168 : subd10_3 [-3, 0, -2] = true := by decide +kernel
theorem subd10_3_169 : subd10_3 [-3, 0, -1] = true := by decide +kernel
theorem subd10_3_170 : subd10_3 [-3, 0, 0] = true := by decide +kernel
theorem subd10_3_171 : subd10_3 [-3, 0, 1] = true := by decide +kernel
theorem subd10_3_172 : subd10_3 [-3, 0, 2] = true := by decide +kernel
theorem subd10_3_173 : subd10_3 [-3, 0, 3] = true := by decide +kernel
theorem subd10_3_174 : subd10_3 [-3, 0, 4] = true := by decide +kernel
theorem subd10_3_175 : subd10_3 [-3, 0, 5] = true := by decide +kernel
theorem subd10_3_176 : subd10_3 [-3, 0, 6] = true := by decide +kernel
theorem subd10_3_177 : subd10_3 [-3, 0, 7] = true := by decide +kernel
theorem subd10_3_178 : subd10_3 [-3, 0, 8] = true := by decide +kernel
theorem subd10_3_179 : subd10_3 [-3, 1, -9] = true := by decide +kernel
theorem subd10_3_180 : subd10_3 [-3, 1, -8] = true := by decide +kernel
theorem subd10_3_181 : subd10_3 [-3, 1, -7] = true := by decide +kernel
theorem subd10_3_182 : subd10_3 [-3, 1, -6] = true := by decide +kernel
theorem subd10_3_183 : subd10_3 [-3, 1, -5] = true := by decide +kernel
theorem subd10_3_184 : subd10_3 [-3, 1, -4] = true := by decide +kernel
theorem subd10_3_185 : subd10_3 [-3, 1, -3] = true := by decide +kernel
theorem subd10_3_186 : subd10_3 [-3, 1, -2] = true := by decide +kernel
theorem subd10_3_187 : subd10_3 [-3, 1, -1] = true := by decide +kernel
theorem subd10_3_188 : subd10_3 [-3, 1, 0] = true := by decide +kernel
theorem subd10_3_189 : subd10_3 [-3, 1, 1] = true := by decide +kernel
theorem subd10_3_190 : subd10_3 [-3, 1, 2] = true := by decide +kernel
theorem subd10_3_191 : subd10_3 [-3, 1, 3] = true := by decide +kernel
theorem sbd10_3_5 : ∀ q ∈ blkd10_3_5, subd10_3 q = true := by
  unfold blkd10_3_5
  exact List.forall_mem_cons.2 ⟨subd10_3_160, List.forall_mem_cons.2 ⟨subd10_3_161, List.forall_mem_cons.2 ⟨subd10_3_162, List.forall_mem_cons.2 ⟨subd10_3_163, List.forall_mem_cons.2 ⟨subd10_3_164, List.forall_mem_cons.2 ⟨subd10_3_165, List.forall_mem_cons.2 ⟨subd10_3_166, List.forall_mem_cons.2 ⟨subd10_3_167, List.forall_mem_cons.2 ⟨subd10_3_168, List.forall_mem_cons.2 ⟨subd10_3_169, List.forall_mem_cons.2 ⟨subd10_3_170, List.forall_mem_cons.2 ⟨subd10_3_171, List.forall_mem_cons.2 ⟨subd10_3_172, List.forall_mem_cons.2 ⟨subd10_3_173, List.forall_mem_cons.2 ⟨subd10_3_174, List.forall_mem_cons.2 ⟨subd10_3_175, List.forall_mem_cons.2 ⟨subd10_3_176, List.forall_mem_cons.2 ⟨subd10_3_177, List.forall_mem_cons.2 ⟨subd10_3_178, List.forall_mem_cons.2 ⟨subd10_3_179, List.forall_mem_cons.2 ⟨subd10_3_180, List.forall_mem_cons.2 ⟨subd10_3_181, List.forall_mem_cons.2 ⟨subd10_3_182, List.forall_mem_cons.2 ⟨subd10_3_183, List.forall_mem_cons.2 ⟨subd10_3_184, List.forall_mem_cons.2 ⟨subd10_3_185, List.forall_mem_cons.2 ⟨subd10_3_186, List.forall_mem_cons.2 ⟨subd10_3_187, List.forall_mem_cons.2 ⟨subd10_3_188, List.forall_mem_cons.2 ⟨subd10_3_189, List.forall_mem_cons.2 ⟨subd10_3_190, List.forall_mem_cons.2 ⟨subd10_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_192 : subd10_3 [-3, 1, 4] = true := by decide +kernel
theorem subd10_3_193 : subd10_3 [-3, 1, 5] = true := by decide +kernel
theorem subd10_3_194 : subd10_3 [-3, 1, 6] = true := by decide +kernel
theorem subd10_3_195 : subd10_3 [-3, 1, 7] = true := by decide +kernel
theorem subd10_3_196 : subd10_3 [-3, 2, -9] = true := by decide +kernel
theorem subd10_3_197 : subd10_3 [-3, 2, -8] = true := by decide +kernel
theorem subd10_3_198 : subd10_3 [-3, 2, -7] = true := by decide +kernel
theorem subd10_3_199 : subd10_3 [-3, 2, -6] = true := by decide +kernel
theorem subd10_3_200 : subd10_3 [-3, 2, -5] = true := by decide +kernel
theorem subd10_3_201 : subd10_3 [-3, 2, -4] = true := by decide +kernel
theorem subd10_3_202 : subd10_3 [-3, 2, -3] = true := by decide +kernel
theorem subd10_3_203 : subd10_3 [-3, 2, -2] = true := by decide +kernel
theorem subd10_3_204 : subd10_3 [-3, 2, -1] = true := by decide +kernel
theorem subd10_3_205 : subd10_3 [-3, 2, 0] = true := by decide +kernel
theorem subd10_3_206 : subd10_3 [-3, 2, 1] = true := by decide +kernel
theorem subd10_3_207 : subd10_3 [-3, 2, 2] = true := by decide +kernel
theorem subd10_3_208 : subd10_3 [-3, 2, 3] = true := by decide +kernel
theorem subd10_3_209 : subd10_3 [-3, 2, 4] = true := by decide +kernel
theorem subd10_3_210 : subd10_3 [-3, 2, 5] = true := by decide +kernel
theorem subd10_3_211 : subd10_3 [-3, 2, 6] = true := by decide +kernel
theorem subd10_3_212 : subd10_3 [-3, 2, 7] = true := by decide +kernel
theorem subd10_3_213 : subd10_3 [-3, 3, -9] = true := by decide +kernel
theorem subd10_3_214 : subd10_3 [-3, 3, -8] = true := by decide +kernel
theorem subd10_3_215 : subd10_3 [-3, 3, -7] = true := by decide +kernel
theorem subd10_3_216 : subd10_3 [-3, 3, -6] = true := by decide +kernel
theorem subd10_3_217 : subd10_3 [-3, 3, -5] = true := by decide +kernel
theorem subd10_3_218 : subd10_3 [-3, 3, -4] = true := by decide +kernel
theorem subd10_3_219 : subd10_3 [-3, 3, -3] = true := by decide +kernel
theorem subd10_3_220 : subd10_3 [-3, 3, -2] = true := by decide +kernel
theorem subd10_3_221 : subd10_3 [-3, 3, -1] = true := by decide +kernel
theorem subd10_3_222 : subd10_3 [-3, 3, 0] = true := by decide +kernel
theorem subd10_3_223 : subd10_3 [-3, 3, 1] = true := by decide +kernel
theorem sbd10_3_6 : ∀ q ∈ blkd10_3_6, subd10_3 q = true := by
  unfold blkd10_3_6
  exact List.forall_mem_cons.2 ⟨subd10_3_192, List.forall_mem_cons.2 ⟨subd10_3_193, List.forall_mem_cons.2 ⟨subd10_3_194, List.forall_mem_cons.2 ⟨subd10_3_195, List.forall_mem_cons.2 ⟨subd10_3_196, List.forall_mem_cons.2 ⟨subd10_3_197, List.forall_mem_cons.2 ⟨subd10_3_198, List.forall_mem_cons.2 ⟨subd10_3_199, List.forall_mem_cons.2 ⟨subd10_3_200, List.forall_mem_cons.2 ⟨subd10_3_201, List.forall_mem_cons.2 ⟨subd10_3_202, List.forall_mem_cons.2 ⟨subd10_3_203, List.forall_mem_cons.2 ⟨subd10_3_204, List.forall_mem_cons.2 ⟨subd10_3_205, List.forall_mem_cons.2 ⟨subd10_3_206, List.forall_mem_cons.2 ⟨subd10_3_207, List.forall_mem_cons.2 ⟨subd10_3_208, List.forall_mem_cons.2 ⟨subd10_3_209, List.forall_mem_cons.2 ⟨subd10_3_210, List.forall_mem_cons.2 ⟨subd10_3_211, List.forall_mem_cons.2 ⟨subd10_3_212, List.forall_mem_cons.2 ⟨subd10_3_213, List.forall_mem_cons.2 ⟨subd10_3_214, List.forall_mem_cons.2 ⟨subd10_3_215, List.forall_mem_cons.2 ⟨subd10_3_216, List.forall_mem_cons.2 ⟨subd10_3_217, List.forall_mem_cons.2 ⟨subd10_3_218, List.forall_mem_cons.2 ⟨subd10_3_219, List.forall_mem_cons.2 ⟨subd10_3_220, List.forall_mem_cons.2 ⟨subd10_3_221, List.forall_mem_cons.2 ⟨subd10_3_222, List.forall_mem_cons.2 ⟨subd10_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_224 : subd10_3 [-3, 3, 2] = true := by decide +kernel
theorem subd10_3_225 : subd10_3 [-3, 3, 3] = true := by decide +kernel
theorem subd10_3_226 : subd10_3 [-3, 3, 4] = true := by decide +kernel
theorem subd10_3_227 : subd10_3 [-3, 3, 5] = true := by decide +kernel
theorem subd10_3_228 : subd10_3 [-3, 3, 6] = true := by decide +kernel
theorem subd10_3_229 : subd10_3 [-3, 4] = true := by decide +kernel
theorem subd10_3_230 : subd10_3 [-3, 5] = true := by decide +kernel
theorem subd10_3_231 : subd10_3 [-3, 6] = true := by decide +kernel
theorem subd10_3_232 : subd10_3 [-2, -7] = true := by decide +kernel
theorem subd10_3_233 : subd10_3 [-2, -6] = true := by decide +kernel
theorem subd10_3_234 : subd10_3 [-2, -5] = true := by decide +kernel
theorem subd10_3_235 : subd10_3 [-2, -4, -6] = true := by decide +kernel
theorem subd10_3_236 : subd10_3 [-2, -4, -5] = true := by decide +kernel
theorem subd10_3_237 : subd10_3 [-2, -4, -4] = true := by decide +kernel
theorem subd10_3_238 : subd10_3 [-2, -4, -3] = true := by decide +kernel
theorem subd10_3_239 : subd10_3 [-2, -4, -2] = true := by decide +kernel
theorem subd10_3_240 : subd10_3 [-2, -4, -1] = true := by decide +kernel
theorem subd10_3_241 : subd10_3 [-2, -4, 0] = true := by decide +kernel
theorem subd10_3_242 : subd10_3 [-2, -4, 1] = true := by decide +kernel
theorem subd10_3_243 : subd10_3 [-2, -4, 2] = true := by decide +kernel
theorem subd10_3_244 : subd10_3 [-2, -4, 3] = true := by decide +kernel
theorem subd10_3_245 : subd10_3 [-2, -4, 4] = true := by decide +kernel
theorem subd10_3_246 : subd10_3 [-2, -4, 5] = true := by decide +kernel
theorem subd10_3_247 : subd10_3 [-2, -4, 6] = true := by decide +kernel
theorem subd10_3_248 : subd10_3 [-2, -4, 7] = true := by decide +kernel
theorem subd10_3_249 : subd10_3 [-2, -3, -7] = true := by decide +kernel
theorem subd10_3_250 : subd10_3 [-2, -3, -6] = true := by decide +kernel
theorem subd10_3_251 : subd10_3 [-2, -3, -5] = true := by decide +kernel
theorem subd10_3_252 : subd10_3 [-2, -3, -4] = true := by decide +kernel
theorem subd10_3_253 : subd10_3 [-2, -3, -3] = true := by decide +kernel
theorem subd10_3_254 : subd10_3 [-2, -3, -2] = true := by decide +kernel
theorem subd10_3_255 : subd10_3 [-2, -3, -1] = true := by decide +kernel
theorem sbd10_3_7 : ∀ q ∈ blkd10_3_7, subd10_3 q = true := by
  unfold blkd10_3_7
  exact List.forall_mem_cons.2 ⟨subd10_3_224, List.forall_mem_cons.2 ⟨subd10_3_225, List.forall_mem_cons.2 ⟨subd10_3_226, List.forall_mem_cons.2 ⟨subd10_3_227, List.forall_mem_cons.2 ⟨subd10_3_228, List.forall_mem_cons.2 ⟨subd10_3_229, List.forall_mem_cons.2 ⟨subd10_3_230, List.forall_mem_cons.2 ⟨subd10_3_231, List.forall_mem_cons.2 ⟨subd10_3_232, List.forall_mem_cons.2 ⟨subd10_3_233, List.forall_mem_cons.2 ⟨subd10_3_234, List.forall_mem_cons.2 ⟨subd10_3_235, List.forall_mem_cons.2 ⟨subd10_3_236, List.forall_mem_cons.2 ⟨subd10_3_237, List.forall_mem_cons.2 ⟨subd10_3_238, List.forall_mem_cons.2 ⟨subd10_3_239, List.forall_mem_cons.2 ⟨subd10_3_240, List.forall_mem_cons.2 ⟨subd10_3_241, List.forall_mem_cons.2 ⟨subd10_3_242, List.forall_mem_cons.2 ⟨subd10_3_243, List.forall_mem_cons.2 ⟨subd10_3_244, List.forall_mem_cons.2 ⟨subd10_3_245, List.forall_mem_cons.2 ⟨subd10_3_246, List.forall_mem_cons.2 ⟨subd10_3_247, List.forall_mem_cons.2 ⟨subd10_3_248, List.forall_mem_cons.2 ⟨subd10_3_249, List.forall_mem_cons.2 ⟨subd10_3_250, List.forall_mem_cons.2 ⟨subd10_3_251, List.forall_mem_cons.2 ⟨subd10_3_252, List.forall_mem_cons.2 ⟨subd10_3_253, List.forall_mem_cons.2 ⟨subd10_3_254, List.forall_mem_cons.2 ⟨subd10_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_256 : subd10_3 [-2, -3, 0] = true := by decide +kernel
theorem subd10_3_257 : subd10_3 [-2, -3, 1] = true := by decide +kernel
theorem subd10_3_258 : subd10_3 [-2, -3, 2] = true := by decide +kernel
theorem subd10_3_259 : subd10_3 [-2, -3, 3] = true := by decide +kernel
theorem subd10_3_260 : subd10_3 [-2, -3, 4] = true := by decide +kernel
theorem subd10_3_261 : subd10_3 [-2, -3, 5] = true := by decide +kernel
theorem subd10_3_262 : subd10_3 [-2, -3, 6] = true := by decide +kernel
theorem subd10_3_263 : subd10_3 [-2, -3, 7] = true := by decide +kernel
theorem subd10_3_264 : subd10_3 [-2, -3, 8] = true := by decide +kernel
theorem subd10_3_265 : subd10_3 [-2, -2, -8] = true := by decide +kernel
theorem subd10_3_266 : subd10_3 [-2, -2, -7] = true := by decide +kernel
theorem subd10_3_267 : subd10_3 [-2, -2, -6] = true := by decide +kernel
theorem subd10_3_268 : subd10_3 [-2, -2, -5] = true := by decide +kernel
theorem subd10_3_269 : subd10_3 [-2, -2, -4] = true := by decide +kernel
theorem subd10_3_270 : subd10_3 [-2, -2, -3] = true := by decide +kernel
theorem subd10_3_271 : subd10_3 [-2, -2, -2] = true := by decide +kernel
theorem subd10_3_272 : subd10_3 [-2, -2, -1] = true := by decide +kernel
theorem subd10_3_273 : subd10_3 [-2, -2, 0] = true := by decide +kernel
theorem subd10_3_274 : subd10_3 [-2, -2, 1] = true := by decide +kernel
theorem subd10_3_275 : subd10_3 [-2, -2, 2] = true := by decide +kernel
theorem subd10_3_276 : subd10_3 [-2, -2, 3] = true := by decide +kernel
theorem subd10_3_277 : subd10_3 [-2, -2, 4] = true := by decide +kernel
theorem subd10_3_278 : subd10_3 [-2, -2, 5] = true := by decide +kernel
theorem subd10_3_279 : subd10_3 [-2, -2, 6] = true := by decide +kernel
theorem subd10_3_280 : subd10_3 [-2, -2, 7] = true := by decide +kernel
theorem subd10_3_281 : subd10_3 [-2, -2, 8] = true := by decide +kernel
theorem subd10_3_282 : subd10_3 [-2, -1, -9] = true := by decide +kernel
theorem subd10_3_283 : subd10_3 [-2, -1, -8] = true := by decide +kernel
theorem subd10_3_284 : subd10_3 [-2, -1, -7] = true := by decide +kernel
theorem subd10_3_285 : subd10_3 [-2, -1, -6] = true := by decide +kernel
theorem subd10_3_286 : subd10_3 [-2, -1, -5] = true := by decide +kernel
theorem subd10_3_287 : subd10_3 [-2, -1, -4] = true := by decide +kernel
theorem sbd10_3_8 : ∀ q ∈ blkd10_3_8, subd10_3 q = true := by
  unfold blkd10_3_8
  exact List.forall_mem_cons.2 ⟨subd10_3_256, List.forall_mem_cons.2 ⟨subd10_3_257, List.forall_mem_cons.2 ⟨subd10_3_258, List.forall_mem_cons.2 ⟨subd10_3_259, List.forall_mem_cons.2 ⟨subd10_3_260, List.forall_mem_cons.2 ⟨subd10_3_261, List.forall_mem_cons.2 ⟨subd10_3_262, List.forall_mem_cons.2 ⟨subd10_3_263, List.forall_mem_cons.2 ⟨subd10_3_264, List.forall_mem_cons.2 ⟨subd10_3_265, List.forall_mem_cons.2 ⟨subd10_3_266, List.forall_mem_cons.2 ⟨subd10_3_267, List.forall_mem_cons.2 ⟨subd10_3_268, List.forall_mem_cons.2 ⟨subd10_3_269, List.forall_mem_cons.2 ⟨subd10_3_270, List.forall_mem_cons.2 ⟨subd10_3_271, List.forall_mem_cons.2 ⟨subd10_3_272, List.forall_mem_cons.2 ⟨subd10_3_273, List.forall_mem_cons.2 ⟨subd10_3_274, List.forall_mem_cons.2 ⟨subd10_3_275, List.forall_mem_cons.2 ⟨subd10_3_276, List.forall_mem_cons.2 ⟨subd10_3_277, List.forall_mem_cons.2 ⟨subd10_3_278, List.forall_mem_cons.2 ⟨subd10_3_279, List.forall_mem_cons.2 ⟨subd10_3_280, List.forall_mem_cons.2 ⟨subd10_3_281, List.forall_mem_cons.2 ⟨subd10_3_282, List.forall_mem_cons.2 ⟨subd10_3_283, List.forall_mem_cons.2 ⟨subd10_3_284, List.forall_mem_cons.2 ⟨subd10_3_285, List.forall_mem_cons.2 ⟨subd10_3_286, List.forall_mem_cons.2 ⟨subd10_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_288 : subd10_3 [-2, -1, -3] = true := by decide +kernel
theorem subd10_3_289 : subd10_3 [-2, -1, -2] = true := by decide +kernel
theorem subd10_3_290 : subd10_3 [-2, -1, -1] = true := by decide +kernel
theorem subd10_3_291 : subd10_3 [-2, -1, 0] = true := by decide +kernel
theorem subd10_3_292 : subd10_3 [-2, -1, 1] = true := by decide +kernel
theorem subd10_3_293 : subd10_3 [-2, -1, 2] = true := by decide +kernel
theorem subd10_3_294 : subd10_3 [-2, -1, 3] = true := by decide +kernel
theorem subd10_3_295 : subd10_3 [-2, -1, 4] = true := by decide +kernel
theorem subd10_3_296 : subd10_3 [-2, -1, 5] = true := by decide +kernel
theorem subd10_3_297 : subd10_3 [-2, -1, 6] = true := by decide +kernel
theorem subd10_3_298 : subd10_3 [-2, -1, 7] = true := by decide +kernel
theorem subd10_3_299 : subd10_3 [-2, -1, 8] = true := by decide +kernel
theorem subd10_3_300 : subd10_3 [-2, 0, -9] = true := by decide +kernel
theorem subd10_3_301 : subd10_3 [-2, 0, -8] = true := by decide +kernel
theorem subd10_3_302 : subd10_3 [-2, 0, -7] = true := by decide +kernel
theorem subd10_3_303 : subd10_3 [-2, 0, -6] = true := by decide +kernel
theorem subd10_3_304 : subd10_3 [-2, 0, -5] = true := by decide +kernel
theorem subd10_3_305 : subd10_3 [-2, 0, -4] = true := by decide +kernel
theorem subd10_3_306 : subd10_3 [-2, 0, -3] = true := by decide +kernel
theorem subd10_3_307 : subd10_3 [-2, 0, -2] = true := by decide +kernel
theorem subd10_3_308 : subd10_3 [-2, 0, -1] = true := by decide +kernel
theorem subd10_3_309 : subd10_3 [-2, 0, 0] = true := by decide +kernel
theorem subd10_3_310 : subd10_3 [-2, 0, 1] = true := by decide +kernel
theorem subd10_3_311 : subd10_3 [-2, 0, 2] = true := by decide +kernel
theorem subd10_3_312 : subd10_3 [-2, 0, 3] = true := by decide +kernel
theorem subd10_3_313 : subd10_3 [-2, 0, 4] = true := by decide +kernel
theorem subd10_3_314 : subd10_3 [-2, 0, 5] = true := by decide +kernel
theorem subd10_3_315 : subd10_3 [-2, 0, 6] = true := by decide +kernel
theorem subd10_3_316 : subd10_3 [-2, 0, 7] = true := by decide +kernel
theorem subd10_3_317 : subd10_3 [-2, 0, 8] = true := by decide +kernel
theorem subd10_3_318 : subd10_3 [-2, 1, -9] = true := by decide +kernel
theorem subd10_3_319 : subd10_3 [-2, 1, -8] = true := by decide +kernel
theorem sbd10_3_9 : ∀ q ∈ blkd10_3_9, subd10_3 q = true := by
  unfold blkd10_3_9
  exact List.forall_mem_cons.2 ⟨subd10_3_288, List.forall_mem_cons.2 ⟨subd10_3_289, List.forall_mem_cons.2 ⟨subd10_3_290, List.forall_mem_cons.2 ⟨subd10_3_291, List.forall_mem_cons.2 ⟨subd10_3_292, List.forall_mem_cons.2 ⟨subd10_3_293, List.forall_mem_cons.2 ⟨subd10_3_294, List.forall_mem_cons.2 ⟨subd10_3_295, List.forall_mem_cons.2 ⟨subd10_3_296, List.forall_mem_cons.2 ⟨subd10_3_297, List.forall_mem_cons.2 ⟨subd10_3_298, List.forall_mem_cons.2 ⟨subd10_3_299, List.forall_mem_cons.2 ⟨subd10_3_300, List.forall_mem_cons.2 ⟨subd10_3_301, List.forall_mem_cons.2 ⟨subd10_3_302, List.forall_mem_cons.2 ⟨subd10_3_303, List.forall_mem_cons.2 ⟨subd10_3_304, List.forall_mem_cons.2 ⟨subd10_3_305, List.forall_mem_cons.2 ⟨subd10_3_306, List.forall_mem_cons.2 ⟨subd10_3_307, List.forall_mem_cons.2 ⟨subd10_3_308, List.forall_mem_cons.2 ⟨subd10_3_309, List.forall_mem_cons.2 ⟨subd10_3_310, List.forall_mem_cons.2 ⟨subd10_3_311, List.forall_mem_cons.2 ⟨subd10_3_312, List.forall_mem_cons.2 ⟨subd10_3_313, List.forall_mem_cons.2 ⟨subd10_3_314, List.forall_mem_cons.2 ⟨subd10_3_315, List.forall_mem_cons.2 ⟨subd10_3_316, List.forall_mem_cons.2 ⟨subd10_3_317, List.forall_mem_cons.2 ⟨subd10_3_318, List.forall_mem_cons.2 ⟨subd10_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_320 : subd10_3 [-2, 1, -7] = true := by decide +kernel
theorem subd10_3_321 : subd10_3 [-2, 1, -6] = true := by decide +kernel
theorem subd10_3_322 : subd10_3 [-2, 1, -5] = true := by decide +kernel
theorem subd10_3_323 : subd10_3 [-2, 1, -4] = true := by decide +kernel
theorem subd10_3_324 : subd10_3 [-2, 1, -3] = true := by decide +kernel
theorem subd10_3_325 : subd10_3 [-2, 1, -2] = true := by decide +kernel
theorem subd10_3_326 : subd10_3 [-2, 1, -1] = true := by decide +kernel
theorem subd10_3_327 : subd10_3 [-2, 1, 0] = true := by decide +kernel
theorem subd10_3_328 : subd10_3 [-2, 1, 1] = true := by decide +kernel
theorem subd10_3_329 : subd10_3 [-2, 1, 2] = true := by decide +kernel
theorem subd10_3_330 : subd10_3 [-2, 1, 3] = true := by decide +kernel
theorem subd10_3_331 : subd10_3 [-2, 1, 4] = true := by decide +kernel
theorem subd10_3_332 : subd10_3 [-2, 1, 5] = true := by decide +kernel
theorem subd10_3_333 : subd10_3 [-2, 1, 6] = true := by decide +kernel
theorem subd10_3_334 : subd10_3 [-2, 1, 7] = true := by decide +kernel
theorem subd10_3_335 : subd10_3 [-2, 1, 8] = true := by decide +kernel
theorem subd10_3_336 : subd10_3 [-2, 2, -9] = true := by decide +kernel
theorem subd10_3_337 : subd10_3 [-2, 2, -8] = true := by decide +kernel
theorem subd10_3_338 : subd10_3 [-2, 2, -7] = true := by decide +kernel
theorem subd10_3_339 : subd10_3 [-2, 2, -6] = true := by decide +kernel
theorem subd10_3_340 : subd10_3 [-2, 2, -5] = true := by decide +kernel
theorem subd10_3_341 : subd10_3 [-2, 2, -4] = true := by decide +kernel
theorem subd10_3_342 : subd10_3 [-2, 2, -3] = true := by decide +kernel
theorem subd10_3_343 : subd10_3 [-2, 2, -2] = true := by decide +kernel
theorem subd10_3_344 : subd10_3 [-2, 2, -1] = true := by decide +kernel
theorem subd10_3_345 : subd10_3 [-2, 2, 0] = true := by decide +kernel
theorem subd10_3_346 : subd10_3 [-2, 2, 1] = true := by decide +kernel
theorem subd10_3_347 : subd10_3 [-2, 2, 2] = true := by decide +kernel
theorem subd10_3_348 : subd10_3 [-2, 2, 3] = true := by decide +kernel
theorem subd10_3_349 : subd10_3 [-2, 2, 4] = true := by decide +kernel
theorem subd10_3_350 : subd10_3 [-2, 2, 5] = true := by decide +kernel
theorem subd10_3_351 : subd10_3 [-2, 2, 6] = true := by decide +kernel
theorem sbd10_3_10 : ∀ q ∈ blkd10_3_10, subd10_3 q = true := by
  unfold blkd10_3_10
  exact List.forall_mem_cons.2 ⟨subd10_3_320, List.forall_mem_cons.2 ⟨subd10_3_321, List.forall_mem_cons.2 ⟨subd10_3_322, List.forall_mem_cons.2 ⟨subd10_3_323, List.forall_mem_cons.2 ⟨subd10_3_324, List.forall_mem_cons.2 ⟨subd10_3_325, List.forall_mem_cons.2 ⟨subd10_3_326, List.forall_mem_cons.2 ⟨subd10_3_327, List.forall_mem_cons.2 ⟨subd10_3_328, List.forall_mem_cons.2 ⟨subd10_3_329, List.forall_mem_cons.2 ⟨subd10_3_330, List.forall_mem_cons.2 ⟨subd10_3_331, List.forall_mem_cons.2 ⟨subd10_3_332, List.forall_mem_cons.2 ⟨subd10_3_333, List.forall_mem_cons.2 ⟨subd10_3_334, List.forall_mem_cons.2 ⟨subd10_3_335, List.forall_mem_cons.2 ⟨subd10_3_336, List.forall_mem_cons.2 ⟨subd10_3_337, List.forall_mem_cons.2 ⟨subd10_3_338, List.forall_mem_cons.2 ⟨subd10_3_339, List.forall_mem_cons.2 ⟨subd10_3_340, List.forall_mem_cons.2 ⟨subd10_3_341, List.forall_mem_cons.2 ⟨subd10_3_342, List.forall_mem_cons.2 ⟨subd10_3_343, List.forall_mem_cons.2 ⟨subd10_3_344, List.forall_mem_cons.2 ⟨subd10_3_345, List.forall_mem_cons.2 ⟨subd10_3_346, List.forall_mem_cons.2 ⟨subd10_3_347, List.forall_mem_cons.2 ⟨subd10_3_348, List.forall_mem_cons.2 ⟨subd10_3_349, List.forall_mem_cons.2 ⟨subd10_3_350, List.forall_mem_cons.2 ⟨subd10_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_352 : subd10_3 [-2, 2, 7] = true := by decide +kernel
theorem subd10_3_353 : subd10_3 [-2, 3, -9] = true := by decide +kernel
theorem subd10_3_354 : subd10_3 [-2, 3, -8] = true := by decide +kernel
theorem subd10_3_355 : subd10_3 [-2, 3, -7] = true := by decide +kernel
theorem subd10_3_356 : subd10_3 [-2, 3, -6] = true := by decide +kernel
theorem subd10_3_357 : subd10_3 [-2, 3, -5] = true := by decide +kernel
theorem subd10_3_358 : subd10_3 [-2, 3, -4] = true := by decide +kernel
theorem subd10_3_359 : subd10_3 [-2, 3, -3] = true := by decide +kernel
theorem subd10_3_360 : subd10_3 [-2, 3, -2] = true := by decide +kernel
theorem subd10_3_361 : subd10_3 [-2, 3, -1] = true := by decide +kernel
theorem subd10_3_362 : subd10_3 [-2, 3, 0] = true := by decide +kernel
theorem subd10_3_363 : subd10_3 [-2, 3, 1] = true := by decide +kernel
theorem subd10_3_364 : subd10_3 [-2, 3, 2] = true := by decide +kernel
theorem subd10_3_365 : subd10_3 [-2, 3, 3] = true := by decide +kernel
theorem subd10_3_366 : subd10_3 [-2, 3, 4] = true := by decide +kernel
theorem subd10_3_367 : subd10_3 [-2, 3, 5] = true := by decide +kernel
theorem subd10_3_368 : subd10_3 [-2, 3, 6] = true := by decide +kernel
theorem subd10_3_369 : subd10_3 [-2, 4, -8] = true := by decide +kernel
theorem subd10_3_370 : subd10_3 [-2, 4, -7] = true := by decide +kernel
theorem subd10_3_371 : subd10_3 [-2, 4, -6] = true := by decide +kernel
theorem subd10_3_372 : subd10_3 [-2, 4, -5] = true := by decide +kernel
theorem subd10_3_373 : subd10_3 [-2, 4, -4] = true := by decide +kernel
theorem subd10_3_374 : subd10_3 [-2, 4, -3] = true := by decide +kernel
theorem subd10_3_375 : subd10_3 [-2, 4, -2] = true := by decide +kernel
theorem subd10_3_376 : subd10_3 [-2, 4, -1] = true := by decide +kernel
theorem subd10_3_377 : subd10_3 [-2, 4, 0] = true := by decide +kernel
theorem subd10_3_378 : subd10_3 [-2, 4, 1] = true := by decide +kernel
theorem subd10_3_379 : subd10_3 [-2, 4, 2] = true := by decide +kernel
theorem subd10_3_380 : subd10_3 [-2, 4, 3] = true := by decide +kernel
theorem subd10_3_381 : subd10_3 [-2, 4, 4] = true := by decide +kernel
theorem subd10_3_382 : subd10_3 [-2, 4, 5] = true := by decide +kernel
theorem subd10_3_383 : subd10_3 [-2, 5] = true := by decide +kernel
theorem sbd10_3_11 : ∀ q ∈ blkd10_3_11, subd10_3 q = true := by
  unfold blkd10_3_11
  exact List.forall_mem_cons.2 ⟨subd10_3_352, List.forall_mem_cons.2 ⟨subd10_3_353, List.forall_mem_cons.2 ⟨subd10_3_354, List.forall_mem_cons.2 ⟨subd10_3_355, List.forall_mem_cons.2 ⟨subd10_3_356, List.forall_mem_cons.2 ⟨subd10_3_357, List.forall_mem_cons.2 ⟨subd10_3_358, List.forall_mem_cons.2 ⟨subd10_3_359, List.forall_mem_cons.2 ⟨subd10_3_360, List.forall_mem_cons.2 ⟨subd10_3_361, List.forall_mem_cons.2 ⟨subd10_3_362, List.forall_mem_cons.2 ⟨subd10_3_363, List.forall_mem_cons.2 ⟨subd10_3_364, List.forall_mem_cons.2 ⟨subd10_3_365, List.forall_mem_cons.2 ⟨subd10_3_366, List.forall_mem_cons.2 ⟨subd10_3_367, List.forall_mem_cons.2 ⟨subd10_3_368, List.forall_mem_cons.2 ⟨subd10_3_369, List.forall_mem_cons.2 ⟨subd10_3_370, List.forall_mem_cons.2 ⟨subd10_3_371, List.forall_mem_cons.2 ⟨subd10_3_372, List.forall_mem_cons.2 ⟨subd10_3_373, List.forall_mem_cons.2 ⟨subd10_3_374, List.forall_mem_cons.2 ⟨subd10_3_375, List.forall_mem_cons.2 ⟨subd10_3_376, List.forall_mem_cons.2 ⟨subd10_3_377, List.forall_mem_cons.2 ⟨subd10_3_378, List.forall_mem_cons.2 ⟨subd10_3_379, List.forall_mem_cons.2 ⟨subd10_3_380, List.forall_mem_cons.2 ⟨subd10_3_381, List.forall_mem_cons.2 ⟨subd10_3_382, List.forall_mem_cons.2 ⟨subd10_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_384 : subd10_3 [-2, 6] = true := by decide +kernel
theorem subd10_3_385 : subd10_3 [-1, -7] = true := by decide +kernel
theorem subd10_3_386 : subd10_3 [-1, -6] = true := by decide +kernel
theorem subd10_3_387 : subd10_3 [-1, -5] = true := by decide +kernel
theorem subd10_3_388 : subd10_3 [-1, -4, -6] = true := by decide +kernel
theorem subd10_3_389 : subd10_3 [-1, -4, -5] = true := by decide +kernel
theorem subd10_3_390 : subd10_3 [-1, -4, -4] = true := by decide +kernel
theorem subd10_3_391 : subd10_3 [-1, -4, -3] = true := by decide +kernel
theorem subd10_3_392 : subd10_3 [-1, -4, -2] = true := by decide +kernel
theorem subd10_3_393 : subd10_3 [-1, -4, -1] = true := by decide +kernel
theorem subd10_3_394 : subd10_3 [-1, -4, 0] = true := by decide +kernel
theorem subd10_3_395 : subd10_3 [-1, -4, 1] = true := by decide +kernel
theorem subd10_3_396 : subd10_3 [-1, -4, 2] = true := by decide +kernel
theorem subd10_3_397 : subd10_3 [-1, -4, 3] = true := by decide +kernel
theorem subd10_3_398 : subd10_3 [-1, -4, 4] = true := by decide +kernel
theorem subd10_3_399 : subd10_3 [-1, -4, 5] = true := by decide +kernel
theorem subd10_3_400 : subd10_3 [-1, -4, 6] = true := by decide +kernel
theorem subd10_3_401 : subd10_3 [-1, -4, 7] = true := by decide +kernel
theorem subd10_3_402 : subd10_3 [-1, -4, 8] = true := by decide +kernel
theorem subd10_3_403 : subd10_3 [-1, -3, -8] = true := by decide +kernel
theorem subd10_3_404 : subd10_3 [-1, -3, -7] = true := by decide +kernel
theorem subd10_3_405 : subd10_3 [-1, -3, -6] = true := by decide +kernel
theorem subd10_3_406 : subd10_3 [-1, -3, -5] = true := by decide +kernel
theorem subd10_3_407 : subd10_3 [-1, -3, -4] = true := by decide +kernel
theorem subd10_3_408 : subd10_3 [-1, -3, -3] = true := by decide +kernel
theorem subd10_3_409 : subd10_3 [-1, -3, -2] = true := by decide +kernel
theorem subd10_3_410 : subd10_3 [-1, -3, -1] = true := by decide +kernel
theorem subd10_3_411 : subd10_3 [-1, -3, 0] = true := by decide +kernel
theorem subd10_3_412 : subd10_3 [-1, -3, 1] = true := by decide +kernel
theorem subd10_3_413 : subd10_3 [-1, -3, 2] = true := by decide +kernel
theorem subd10_3_414 : subd10_3 [-1, -3, 3] = true := by decide +kernel
theorem subd10_3_415 : subd10_3 [-1, -3, 4] = true := by decide +kernel
theorem sbd10_3_12 : ∀ q ∈ blkd10_3_12, subd10_3 q = true := by
  unfold blkd10_3_12
  exact List.forall_mem_cons.2 ⟨subd10_3_384, List.forall_mem_cons.2 ⟨subd10_3_385, List.forall_mem_cons.2 ⟨subd10_3_386, List.forall_mem_cons.2 ⟨subd10_3_387, List.forall_mem_cons.2 ⟨subd10_3_388, List.forall_mem_cons.2 ⟨subd10_3_389, List.forall_mem_cons.2 ⟨subd10_3_390, List.forall_mem_cons.2 ⟨subd10_3_391, List.forall_mem_cons.2 ⟨subd10_3_392, List.forall_mem_cons.2 ⟨subd10_3_393, List.forall_mem_cons.2 ⟨subd10_3_394, List.forall_mem_cons.2 ⟨subd10_3_395, List.forall_mem_cons.2 ⟨subd10_3_396, List.forall_mem_cons.2 ⟨subd10_3_397, List.forall_mem_cons.2 ⟨subd10_3_398, List.forall_mem_cons.2 ⟨subd10_3_399, List.forall_mem_cons.2 ⟨subd10_3_400, List.forall_mem_cons.2 ⟨subd10_3_401, List.forall_mem_cons.2 ⟨subd10_3_402, List.forall_mem_cons.2 ⟨subd10_3_403, List.forall_mem_cons.2 ⟨subd10_3_404, List.forall_mem_cons.2 ⟨subd10_3_405, List.forall_mem_cons.2 ⟨subd10_3_406, List.forall_mem_cons.2 ⟨subd10_3_407, List.forall_mem_cons.2 ⟨subd10_3_408, List.forall_mem_cons.2 ⟨subd10_3_409, List.forall_mem_cons.2 ⟨subd10_3_410, List.forall_mem_cons.2 ⟨subd10_3_411, List.forall_mem_cons.2 ⟨subd10_3_412, List.forall_mem_cons.2 ⟨subd10_3_413, List.forall_mem_cons.2 ⟨subd10_3_414, List.forall_mem_cons.2 ⟨subd10_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_416 : subd10_3 [-1, -3, 5] = true := by decide +kernel
theorem subd10_3_417 : subd10_3 [-1, -3, 6] = true := by decide +kernel
theorem subd10_3_418 : subd10_3 [-1, -3, 7] = true := by decide +kernel
theorem subd10_3_419 : subd10_3 [-1, -3, 8] = true := by decide +kernel
theorem subd10_3_420 : subd10_3 [-1, -2, -8] = true := by decide +kernel
theorem subd10_3_421 : subd10_3 [-1, -2, -7] = true := by decide +kernel
theorem subd10_3_422 : subd10_3 [-1, -2, -6] = true := by decide +kernel
theorem subd10_3_423 : subd10_3 [-1, -2, -5] = true := by decide +kernel
theorem subd10_3_424 : subd10_3 [-1, -2, -4] = true := by decide +kernel
theorem subd10_3_425 : subd10_3 [-1, -2, -3] = true := by decide +kernel
theorem subd10_3_426 : subd10_3 [-1, -2, -2] = true := by decide +kernel
theorem subd10_3_427 : subd10_3 [-1, -2, -1] = true := by decide +kernel
theorem subd10_3_428 : subd10_3 [-1, -2, 0] = true := by decide +kernel
theorem subd10_3_429 : subd10_3 [-1, -2, 1] = true := by decide +kernel
theorem subd10_3_430 : subd10_3 [-1, -2, 2] = true := by decide +kernel
theorem subd10_3_431 : subd10_3 [-1, -2, 3] = true := by decide +kernel
theorem subd10_3_432 : subd10_3 [-1, -2, 4] = true := by decide +kernel
theorem subd10_3_433 : subd10_3 [-1, -2, 5] = true := by decide +kernel
theorem subd10_3_434 : subd10_3 [-1, -2, 6] = true := by decide +kernel
theorem subd10_3_435 : subd10_3 [-1, -2, 7] = true := by decide +kernel
theorem subd10_3_436 : subd10_3 [-1, -2, 8] = true := by decide +kernel
theorem subd10_3_437 : subd10_3 [-1, -2, 9] = true := by decide +kernel
theorem subd10_3_438 : subd10_3 [-1, -1, -9] = true := by decide +kernel
theorem subd10_3_439 : subd10_3 [-1, -1, -8] = true := by decide +kernel
theorem subd10_3_440 : subd10_3 [-1, -1, -7] = true := by decide +kernel
theorem subd10_3_441 : subd10_3 [-1, -1, -6] = true := by decide +kernel
theorem subd10_3_442 : subd10_3 [-1, -1, -5] = true := by decide +kernel
theorem subd10_3_443 : subd10_3 [-1, -1, -4] = true := by decide +kernel
theorem subd10_3_444 : subd10_3 [-1, -1, -3] = true := by decide +kernel
theorem subd10_3_445 : subd10_3 [-1, -1, -2] = true := by decide +kernel
theorem subd10_3_446 : subd10_3 [-1, -1, -1] = true := by decide +kernel
theorem subd10_3_447 : subd10_3 [-1, -1, 0] = true := by decide +kernel
theorem sbd10_3_13 : ∀ q ∈ blkd10_3_13, subd10_3 q = true := by
  unfold blkd10_3_13
  exact List.forall_mem_cons.2 ⟨subd10_3_416, List.forall_mem_cons.2 ⟨subd10_3_417, List.forall_mem_cons.2 ⟨subd10_3_418, List.forall_mem_cons.2 ⟨subd10_3_419, List.forall_mem_cons.2 ⟨subd10_3_420, List.forall_mem_cons.2 ⟨subd10_3_421, List.forall_mem_cons.2 ⟨subd10_3_422, List.forall_mem_cons.2 ⟨subd10_3_423, List.forall_mem_cons.2 ⟨subd10_3_424, List.forall_mem_cons.2 ⟨subd10_3_425, List.forall_mem_cons.2 ⟨subd10_3_426, List.forall_mem_cons.2 ⟨subd10_3_427, List.forall_mem_cons.2 ⟨subd10_3_428, List.forall_mem_cons.2 ⟨subd10_3_429, List.forall_mem_cons.2 ⟨subd10_3_430, List.forall_mem_cons.2 ⟨subd10_3_431, List.forall_mem_cons.2 ⟨subd10_3_432, List.forall_mem_cons.2 ⟨subd10_3_433, List.forall_mem_cons.2 ⟨subd10_3_434, List.forall_mem_cons.2 ⟨subd10_3_435, List.forall_mem_cons.2 ⟨subd10_3_436, List.forall_mem_cons.2 ⟨subd10_3_437, List.forall_mem_cons.2 ⟨subd10_3_438, List.forall_mem_cons.2 ⟨subd10_3_439, List.forall_mem_cons.2 ⟨subd10_3_440, List.forall_mem_cons.2 ⟨subd10_3_441, List.forall_mem_cons.2 ⟨subd10_3_442, List.forall_mem_cons.2 ⟨subd10_3_443, List.forall_mem_cons.2 ⟨subd10_3_444, List.forall_mem_cons.2 ⟨subd10_3_445, List.forall_mem_cons.2 ⟨subd10_3_446, List.forall_mem_cons.2 ⟨subd10_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_448 : subd10_3 [-1, -1, 1] = true := by decide +kernel
theorem subd10_3_449 : subd10_3 [-1, -1, 2] = true := by decide +kernel
theorem subd10_3_450 : subd10_3 [-1, -1, 3] = true := by decide +kernel
theorem subd10_3_451 : subd10_3 [-1, -1, 4] = true := by decide +kernel
theorem subd10_3_452 : subd10_3 [-1, -1, 5] = true := by decide +kernel
theorem subd10_3_453 : subd10_3 [-1, -1, 6] = true := by decide +kernel
theorem subd10_3_454 : subd10_3 [-1, -1, 7] = true := by decide +kernel
theorem subd10_3_455 : subd10_3 [-1, -1, 8] = true := by decide +kernel
theorem subd10_3_456 : subd10_3 [-1, -1, 9] = true := by decide +kernel
theorem subd10_3_457 : subd10_3 [-1, 0, -9] = true := by decide +kernel
theorem subd10_3_458 : subd10_3 [-1, 0, -8] = true := by decide +kernel
theorem subd10_3_459 : subd10_3 [-1, 0, -7] = true := by decide +kernel
theorem subd10_3_460 : subd10_3 [-1, 0, -6] = true := by decide +kernel
theorem subd10_3_461 : subd10_3 [-1, 0, -5] = true := by decide +kernel
theorem subd10_3_462 : subd10_3 [-1, 0, -4] = true := by decide +kernel
theorem subd10_3_463 : subd10_3 [-1, 0, -3] = true := by decide +kernel
theorem subd10_3_464 : subd10_3 [-1, 0, -2] = true := by decide +kernel
theorem subd10_3_465 : subd10_3 [-1, 0, -1] = true := by decide +kernel
theorem subd10_3_466 : subd10_3 [-1, 0, 0] = true := by decide +kernel
theorem subd10_3_467 : subd10_3 [-1, 0, 1] = true := by decide +kernel
theorem subd10_3_468 : subd10_3 [-1, 0, 2] = true := by decide +kernel
theorem subd10_3_469 : subd10_3 [-1, 0, 3] = true := by decide +kernel
theorem subd10_3_470 : subd10_3 [-1, 0, 4] = true := by decide +kernel
theorem subd10_3_471 : subd10_3 [-1, 0, 5] = true := by decide +kernel
theorem subd10_3_472 : subd10_3 [-1, 0, 6] = true := by decide +kernel
theorem subd10_3_473 : subd10_3 [-1, 0, 7] = true := by decide +kernel
theorem subd10_3_474 : subd10_3 [-1, 0, 8] = true := by decide +kernel
theorem subd10_3_475 : subd10_3 [-1, 1, -10] = true := by decide +kernel
theorem subd10_3_476 : subd10_3 [-1, 1, -9] = true := by decide +kernel
theorem subd10_3_477 : subd10_3 [-1, 1, -8] = true := by decide +kernel
theorem subd10_3_478 : subd10_3 [-1, 1, -7] = true := by decide +kernel
theorem subd10_3_479 : subd10_3 [-1, 1, -6] = true := by decide +kernel
theorem sbd10_3_14 : ∀ q ∈ blkd10_3_14, subd10_3 q = true := by
  unfold blkd10_3_14
  exact List.forall_mem_cons.2 ⟨subd10_3_448, List.forall_mem_cons.2 ⟨subd10_3_449, List.forall_mem_cons.2 ⟨subd10_3_450, List.forall_mem_cons.2 ⟨subd10_3_451, List.forall_mem_cons.2 ⟨subd10_3_452, List.forall_mem_cons.2 ⟨subd10_3_453, List.forall_mem_cons.2 ⟨subd10_3_454, List.forall_mem_cons.2 ⟨subd10_3_455, List.forall_mem_cons.2 ⟨subd10_3_456, List.forall_mem_cons.2 ⟨subd10_3_457, List.forall_mem_cons.2 ⟨subd10_3_458, List.forall_mem_cons.2 ⟨subd10_3_459, List.forall_mem_cons.2 ⟨subd10_3_460, List.forall_mem_cons.2 ⟨subd10_3_461, List.forall_mem_cons.2 ⟨subd10_3_462, List.forall_mem_cons.2 ⟨subd10_3_463, List.forall_mem_cons.2 ⟨subd10_3_464, List.forall_mem_cons.2 ⟨subd10_3_465, List.forall_mem_cons.2 ⟨subd10_3_466, List.forall_mem_cons.2 ⟨subd10_3_467, List.forall_mem_cons.2 ⟨subd10_3_468, List.forall_mem_cons.2 ⟨subd10_3_469, List.forall_mem_cons.2 ⟨subd10_3_470, List.forall_mem_cons.2 ⟨subd10_3_471, List.forall_mem_cons.2 ⟨subd10_3_472, List.forall_mem_cons.2 ⟨subd10_3_473, List.forall_mem_cons.2 ⟨subd10_3_474, List.forall_mem_cons.2 ⟨subd10_3_475, List.forall_mem_cons.2 ⟨subd10_3_476, List.forall_mem_cons.2 ⟨subd10_3_477, List.forall_mem_cons.2 ⟨subd10_3_478, List.forall_mem_cons.2 ⟨subd10_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_480 : subd10_3 [-1, 1, -5] = true := by decide +kernel
theorem subd10_3_481 : subd10_3 [-1, 1, -4] = true := by decide +kernel
theorem subd10_3_482 : subd10_3 [-1, 1, -3] = true := by decide +kernel
theorem subd10_3_483 : subd10_3 [-1, 1, -2] = true := by decide +kernel
theorem subd10_3_484 : subd10_3 [-1, 1, -1] = true := by decide +kernel
theorem subd10_3_485 : subd10_3 [-1, 1, 0] = true := by decide +kernel
theorem subd10_3_486 : subd10_3 [-1, 1, 1] = true := by decide +kernel
theorem subd10_3_487 : subd10_3 [-1, 1, 2] = true := by decide +kernel
theorem subd10_3_488 : subd10_3 [-1, 1, 3] = true := by decide +kernel
theorem subd10_3_489 : subd10_3 [-1, 1, 4] = true := by decide +kernel
theorem subd10_3_490 : subd10_3 [-1, 1, 5] = true := by decide +kernel
theorem subd10_3_491 : subd10_3 [-1, 1, 6] = true := by decide +kernel
theorem subd10_3_492 : subd10_3 [-1, 1, 7] = true := by decide +kernel
theorem subd10_3_493 : subd10_3 [-1, 1, 8] = true := by decide +kernel
theorem subd10_3_494 : subd10_3 [-1, 2, -10] = true := by decide +kernel
theorem subd10_3_495 : subd10_3 [-1, 2, -9] = true := by decide +kernel
theorem subd10_3_496 : subd10_3 [-1, 2, -8] = true := by decide +kernel
theorem subd10_3_497 : subd10_3 [-1, 2, -7] = true := by decide +kernel
theorem subd10_3_498 : subd10_3 [-1, 2, -6] = true := by decide +kernel
theorem subd10_3_499 : subd10_3 [-1, 2, -5] = true := by decide +kernel
theorem subd10_3_500 : subd10_3 [-1, 2, -4] = true := by decide +kernel
theorem subd10_3_501 : subd10_3 [-1, 2, -3] = true := by decide +kernel
theorem subd10_3_502 : subd10_3 [-1, 2, -2] = true := by decide +kernel
theorem subd10_3_503 : subd10_3 [-1, 2, -1] = true := by decide +kernel
theorem subd10_3_504 : subd10_3 [-1, 2, 0] = true := by decide +kernel
theorem subd10_3_505 : subd10_3 [-1, 2, 1] = true := by decide +kernel
theorem subd10_3_506 : subd10_3 [-1, 2, 2] = true := by decide +kernel
theorem subd10_3_507 : subd10_3 [-1, 2, 3] = true := by decide +kernel
theorem subd10_3_508 : subd10_3 [-1, 2, 4] = true := by decide +kernel
theorem subd10_3_509 : subd10_3 [-1, 2, 5] = true := by decide +kernel
theorem subd10_3_510 : subd10_3 [-1, 2, 6] = true := by decide +kernel
theorem subd10_3_511 : subd10_3 [-1, 2, 7] = true := by decide +kernel
theorem sbd10_3_15 : ∀ q ∈ blkd10_3_15, subd10_3 q = true := by
  unfold blkd10_3_15
  exact List.forall_mem_cons.2 ⟨subd10_3_480, List.forall_mem_cons.2 ⟨subd10_3_481, List.forall_mem_cons.2 ⟨subd10_3_482, List.forall_mem_cons.2 ⟨subd10_3_483, List.forall_mem_cons.2 ⟨subd10_3_484, List.forall_mem_cons.2 ⟨subd10_3_485, List.forall_mem_cons.2 ⟨subd10_3_486, List.forall_mem_cons.2 ⟨subd10_3_487, List.forall_mem_cons.2 ⟨subd10_3_488, List.forall_mem_cons.2 ⟨subd10_3_489, List.forall_mem_cons.2 ⟨subd10_3_490, List.forall_mem_cons.2 ⟨subd10_3_491, List.forall_mem_cons.2 ⟨subd10_3_492, List.forall_mem_cons.2 ⟨subd10_3_493, List.forall_mem_cons.2 ⟨subd10_3_494, List.forall_mem_cons.2 ⟨subd10_3_495, List.forall_mem_cons.2 ⟨subd10_3_496, List.forall_mem_cons.2 ⟨subd10_3_497, List.forall_mem_cons.2 ⟨subd10_3_498, List.forall_mem_cons.2 ⟨subd10_3_499, List.forall_mem_cons.2 ⟨subd10_3_500, List.forall_mem_cons.2 ⟨subd10_3_501, List.forall_mem_cons.2 ⟨subd10_3_502, List.forall_mem_cons.2 ⟨subd10_3_503, List.forall_mem_cons.2 ⟨subd10_3_504, List.forall_mem_cons.2 ⟨subd10_3_505, List.forall_mem_cons.2 ⟨subd10_3_506, List.forall_mem_cons.2 ⟨subd10_3_507, List.forall_mem_cons.2 ⟨subd10_3_508, List.forall_mem_cons.2 ⟨subd10_3_509, List.forall_mem_cons.2 ⟨subd10_3_510, List.forall_mem_cons.2 ⟨subd10_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
