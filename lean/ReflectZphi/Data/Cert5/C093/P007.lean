import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_32 : subd6_0 [-5, 0, 0] = true := by decide +kernel
theorem subd6_0_33 : subd6_0 [-5, 0, 1] = true := by decide +kernel
theorem subd6_0_34 : subd6_0 [-5, 0, 2] = true := by decide +kernel
theorem subd6_0_35 : subd6_0 [-5, 0, 3] = true := by decide +kernel
theorem subd6_0_36 : subd6_0 [-5, 0, 4] = true := by decide +kernel
theorem subd6_0_37 : subd6_0 [-5, 0, 5] = true := by decide +kernel
theorem subd6_0_38 : subd6_0 [-5, 0, 6] = true := by decide +kernel
theorem subd6_0_39 : subd6_0 [-5, 1, -7] = true := by decide +kernel
theorem subd6_0_40 : subd6_0 [-5, 1, -6] = true := by decide +kernel
theorem subd6_0_41 : subd6_0 [-5, 1, -5] = true := by decide +kernel
theorem subd6_0_42 : subd6_0 [-5, 1, -4] = true := by decide +kernel
theorem subd6_0_43 : subd6_0 [-5, 1, -3] = true := by decide +kernel
theorem subd6_0_44 : subd6_0 [-5, 1, -2] = true := by decide +kernel
theorem subd6_0_45 : subd6_0 [-5, 1, -1] = true := by decide +kernel
theorem subd6_0_46 : subd6_0 [-5, 1, 0] = true := by decide +kernel
theorem subd6_0_47 : subd6_0 [-5, 1, 1] = true := by decide +kernel
theorem subd6_0_48 : subd6_0 [-5, 1, 2] = true := by decide +kernel
theorem subd6_0_49 : subd6_0 [-5, 1, 3] = true := by decide +kernel
theorem subd6_0_50 : subd6_0 [-5, 1, 4] = true := by decide +kernel
theorem subd6_0_51 : subd6_0 [-5, 1, 5] = true := by decide +kernel
theorem subd6_0_52 : subd6_0 [-5, 1, 6] = true := by decide +kernel
theorem subd6_0_53 : subd6_0 [-5, 2] = true := by decide +kernel
theorem subd6_0_54 : subd6_0 [-5, 3] = true := by decide +kernel
theorem subd6_0_55 : subd6_0 [-5, 4] = true := by decide +kernel
theorem subd6_0_56 : subd6_0 [-5, 5] = true := by decide +kernel
theorem subd6_0_57 : subd6_0 [-5, 6] = true := by decide +kernel
theorem subd6_0_58 : subd6_0 [-4, -7] = true := by decide +kernel
theorem subd6_0_59 : subd6_0 [-4, -6] = true := by decide +kernel
theorem subd6_0_60 : subd6_0 [-4, -5] = true := by decide +kernel
theorem subd6_0_61 : subd6_0 [-4, -4] = true := by decide +kernel
theorem subd6_0_62 : subd6_0 [-4, -3, -6] = true := by decide +kernel
theorem subd6_0_63 : subd6_0 [-4, -3, -5] = true := by decide +kernel
theorem sbd6_0_1 : ∀ q ∈ blkd6_0_1, subd6_0 q = true := by
  unfold blkd6_0_1
  exact List.forall_mem_cons.2 ⟨subd6_0_32, List.forall_mem_cons.2 ⟨subd6_0_33, List.forall_mem_cons.2 ⟨subd6_0_34, List.forall_mem_cons.2 ⟨subd6_0_35, List.forall_mem_cons.2 ⟨subd6_0_36, List.forall_mem_cons.2 ⟨subd6_0_37, List.forall_mem_cons.2 ⟨subd6_0_38, List.forall_mem_cons.2 ⟨subd6_0_39, List.forall_mem_cons.2 ⟨subd6_0_40, List.forall_mem_cons.2 ⟨subd6_0_41, List.forall_mem_cons.2 ⟨subd6_0_42, List.forall_mem_cons.2 ⟨subd6_0_43, List.forall_mem_cons.2 ⟨subd6_0_44, List.forall_mem_cons.2 ⟨subd6_0_45, List.forall_mem_cons.2 ⟨subd6_0_46, List.forall_mem_cons.2 ⟨subd6_0_47, List.forall_mem_cons.2 ⟨subd6_0_48, List.forall_mem_cons.2 ⟨subd6_0_49, List.forall_mem_cons.2 ⟨subd6_0_50, List.forall_mem_cons.2 ⟨subd6_0_51, List.forall_mem_cons.2 ⟨subd6_0_52, List.forall_mem_cons.2 ⟨subd6_0_53, List.forall_mem_cons.2 ⟨subd6_0_54, List.forall_mem_cons.2 ⟨subd6_0_55, List.forall_mem_cons.2 ⟨subd6_0_56, List.forall_mem_cons.2 ⟨subd6_0_57, List.forall_mem_cons.2 ⟨subd6_0_58, List.forall_mem_cons.2 ⟨subd6_0_59, List.forall_mem_cons.2 ⟨subd6_0_60, List.forall_mem_cons.2 ⟨subd6_0_61, List.forall_mem_cons.2 ⟨subd6_0_62, List.forall_mem_cons.2 ⟨subd6_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_64 : subd6_0 [-4, -3, -4] = true := by decide +kernel
theorem subd6_0_65 : subd6_0 [-4, -3, -3] = true := by decide +kernel
theorem subd6_0_66 : subd6_0 [-4, -3, -2] = true := by decide +kernel
theorem subd6_0_67 : subd6_0 [-4, -3, -1] = true := by decide +kernel
theorem subd6_0_68 : subd6_0 [-4, -3, 0] = true := by decide +kernel
theorem subd6_0_69 : subd6_0 [-4, -3, 1] = true := by decide +kernel
theorem subd6_0_70 : subd6_0 [-4, -3, 2] = true := by decide +kernel
theorem subd6_0_71 : subd6_0 [-4, -3, 3] = true := by decide +kernel
theorem subd6_0_72 : subd6_0 [-4, -3, 4] = true := by decide +kernel
theorem subd6_0_73 : subd6_0 [-4, -3, 5] = true := by decide +kernel
theorem subd6_0_74 : subd6_0 [-4, -3, 6] = true := by decide +kernel
theorem subd6_0_75 : subd6_0 [-4, -3, 7] = true := by decide +kernel
theorem subd6_0_76 : subd6_0 [-4, -2, -7] = true := by decide +kernel
theorem subd6_0_77 : subd6_0 [-4, -2, -6] = true := by decide +kernel
theorem subd6_0_78 : subd6_0 [-4, -2, -5] = true := by decide +kernel
theorem subd6_0_79 : subd6_0 [-4, -2, -4] = true := by decide +kernel
theorem subd6_0_80 : subd6_0 [-4, -2, -3] = true := by decide +kernel
theorem subd6_0_81 : subd6_0 [-4, -2, -2] = true := by decide +kernel
theorem subd6_0_82 : subd6_0 [-4, -2, -1] = true := by decide +kernel
theorem subd6_0_83 : subd6_0 [-4, -2, 0] = true := by decide +kernel
theorem subd6_0_84 : subd6_0 [-4, -2, 1] = true := by decide +kernel
theorem subd6_0_85 : subd6_0 [-4, -2, 2] = true := by decide +kernel
theorem subd6_0_86 : subd6_0 [-4, -2, 3] = true := by decide +kernel
theorem subd6_0_87 : subd6_0 [-4, -2, 4] = true := by decide +kernel
theorem subd6_0_88 : subd6_0 [-4, -2, 5] = true := by decide +kernel
theorem subd6_0_89 : subd6_0 [-4, -2, 6] = true := by decide +kernel
theorem subd6_0_90 : subd6_0 [-4, -2, 7] = true := by decide +kernel
theorem subd6_0_91 : subd6_0 [-4, -1, -7] = true := by decide +kernel
theorem subd6_0_92 : subd6_0 [-4, -1, -6] = true := by decide +kernel
theorem subd6_0_93 : subd6_0 [-4, -1, -5] = true := by decide +kernel
theorem subd6_0_94 : subd6_0 [-4, -1, -4] = true := by decide +kernel
theorem subd6_0_95 : subd6_0 [-4, -1, -3] = true := by decide +kernel
theorem sbd6_0_2 : ∀ q ∈ blkd6_0_2, subd6_0 q = true := by
  unfold blkd6_0_2
  exact List.forall_mem_cons.2 ⟨subd6_0_64, List.forall_mem_cons.2 ⟨subd6_0_65, List.forall_mem_cons.2 ⟨subd6_0_66, List.forall_mem_cons.2 ⟨subd6_0_67, List.forall_mem_cons.2 ⟨subd6_0_68, List.forall_mem_cons.2 ⟨subd6_0_69, List.forall_mem_cons.2 ⟨subd6_0_70, List.forall_mem_cons.2 ⟨subd6_0_71, List.forall_mem_cons.2 ⟨subd6_0_72, List.forall_mem_cons.2 ⟨subd6_0_73, List.forall_mem_cons.2 ⟨subd6_0_74, List.forall_mem_cons.2 ⟨subd6_0_75, List.forall_mem_cons.2 ⟨subd6_0_76, List.forall_mem_cons.2 ⟨subd6_0_77, List.forall_mem_cons.2 ⟨subd6_0_78, List.forall_mem_cons.2 ⟨subd6_0_79, List.forall_mem_cons.2 ⟨subd6_0_80, List.forall_mem_cons.2 ⟨subd6_0_81, List.forall_mem_cons.2 ⟨subd6_0_82, List.forall_mem_cons.2 ⟨subd6_0_83, List.forall_mem_cons.2 ⟨subd6_0_84, List.forall_mem_cons.2 ⟨subd6_0_85, List.forall_mem_cons.2 ⟨subd6_0_86, List.forall_mem_cons.2 ⟨subd6_0_87, List.forall_mem_cons.2 ⟨subd6_0_88, List.forall_mem_cons.2 ⟨subd6_0_89, List.forall_mem_cons.2 ⟨subd6_0_90, List.forall_mem_cons.2 ⟨subd6_0_91, List.forall_mem_cons.2 ⟨subd6_0_92, List.forall_mem_cons.2 ⟨subd6_0_93, List.forall_mem_cons.2 ⟨subd6_0_94, List.forall_mem_cons.2 ⟨subd6_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_96 : subd6_0 [-4, -1, -2] = true := by decide +kernel
theorem subd6_0_97 : subd6_0 [-4, -1, -1] = true := by decide +kernel
theorem subd6_0_98 : subd6_0 [-4, -1, 0] = true := by decide +kernel
theorem subd6_0_99 : subd6_0 [-4, -1, 1] = true := by decide +kernel
theorem subd6_0_100 : subd6_0 [-4, -1, 2] = true := by decide +kernel
theorem subd6_0_101 : subd6_0 [-4, -1, 3] = true := by decide +kernel
theorem subd6_0_102 : subd6_0 [-4, -1, 4] = true := by decide +kernel
theorem subd6_0_103 : subd6_0 [-4, -1, 5] = true := by decide +kernel
theorem subd6_0_104 : subd6_0 [-4, -1, 6] = true := by decide +kernel
theorem subd6_0_105 : subd6_0 [-4, -1, 7] = true := by decide +kernel
theorem subd6_0_106 : subd6_0 [-4, 0, -7] = true := by decide +kernel
theorem subd6_0_107 : subd6_0 [-4, 0, -6] = true := by decide +kernel
theorem subd6_0_108 : subd6_0 [-4, 0, -5] = true := by decide +kernel
theorem subd6_0_109 : subd6_0 [-4, 0, -4] = true := by decide +kernel
theorem subd6_0_110 : subd6_0 [-4, 0, -3] = true := by decide +kernel
theorem subd6_0_111 : subd6_0 [-4, 0, -2] = true := by decide +kernel
theorem subd6_0_112 : subd6_0 [-4, 0, -1] = true := by decide +kernel
theorem subd6_0_113 : subd6_0 [-4, 0, 0] = true := by decide +kernel
theorem subd6_0_114 : subd6_0 [-4, 0, 1] = true := by decide +kernel
theorem subd6_0_115 : subd6_0 [-4, 0, 2] = true := by decide +kernel
theorem subd6_0_116 : subd6_0 [-4, 0, 3] = true := by decide +kernel
theorem subd6_0_117 : subd6_0 [-4, 0, 4] = true := by decide +kernel
theorem subd6_0_118 : subd6_0 [-4, 0, 5] = true := by decide +kernel
theorem subd6_0_119 : subd6_0 [-4, 0, 6] = true := by decide +kernel
theorem subd6_0_120 : subd6_0 [-4, 0, 7] = true := by decide +kernel
theorem subd6_0_121 : subd6_0 [-4, 1, -8] = true := by decide +kernel
theorem subd6_0_122 : subd6_0 [-4, 1, -7] = true := by decide +kernel
theorem subd6_0_123 : subd6_0 [-4, 1, -6] = true := by decide +kernel
theorem subd6_0_124 : subd6_0 [-4, 1, -5] = true := by decide +kernel
theorem subd6_0_125 : subd6_0 [-4, 1, -4] = true := by decide +kernel
theorem subd6_0_126 : subd6_0 [-4, 1, -3] = true := by decide +kernel
theorem subd6_0_127 : subd6_0 [-4, 1, -2] = true := by decide +kernel
theorem sbd6_0_3 : ∀ q ∈ blkd6_0_3, subd6_0 q = true := by
  unfold blkd6_0_3
  exact List.forall_mem_cons.2 ⟨subd6_0_96, List.forall_mem_cons.2 ⟨subd6_0_97, List.forall_mem_cons.2 ⟨subd6_0_98, List.forall_mem_cons.2 ⟨subd6_0_99, List.forall_mem_cons.2 ⟨subd6_0_100, List.forall_mem_cons.2 ⟨subd6_0_101, List.forall_mem_cons.2 ⟨subd6_0_102, List.forall_mem_cons.2 ⟨subd6_0_103, List.forall_mem_cons.2 ⟨subd6_0_104, List.forall_mem_cons.2 ⟨subd6_0_105, List.forall_mem_cons.2 ⟨subd6_0_106, List.forall_mem_cons.2 ⟨subd6_0_107, List.forall_mem_cons.2 ⟨subd6_0_108, List.forall_mem_cons.2 ⟨subd6_0_109, List.forall_mem_cons.2 ⟨subd6_0_110, List.forall_mem_cons.2 ⟨subd6_0_111, List.forall_mem_cons.2 ⟨subd6_0_112, List.forall_mem_cons.2 ⟨subd6_0_113, List.forall_mem_cons.2 ⟨subd6_0_114, List.forall_mem_cons.2 ⟨subd6_0_115, List.forall_mem_cons.2 ⟨subd6_0_116, List.forall_mem_cons.2 ⟨subd6_0_117, List.forall_mem_cons.2 ⟨subd6_0_118, List.forall_mem_cons.2 ⟨subd6_0_119, List.forall_mem_cons.2 ⟨subd6_0_120, List.forall_mem_cons.2 ⟨subd6_0_121, List.forall_mem_cons.2 ⟨subd6_0_122, List.forall_mem_cons.2 ⟨subd6_0_123, List.forall_mem_cons.2 ⟨subd6_0_124, List.forall_mem_cons.2 ⟨subd6_0_125, List.forall_mem_cons.2 ⟨subd6_0_126, List.forall_mem_cons.2 ⟨subd6_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_128 : subd6_0 [-4, 1, -1] = true := by decide +kernel
theorem subd6_0_129 : subd6_0 [-4, 1, 0] = true := by decide +kernel
theorem subd6_0_130 : subd6_0 [-4, 1, 1] = true := by decide +kernel
theorem subd6_0_131 : subd6_0 [-4, 1, 2] = true := by decide +kernel
theorem subd6_0_132 : subd6_0 [-4, 1, 3] = true := by decide +kernel
theorem subd6_0_133 : subd6_0 [-4, 1, 4] = true := by decide +kernel
theorem subd6_0_134 : subd6_0 [-4, 1, 5] = true := by decide +kernel
theorem subd6_0_135 : subd6_0 [-4, 1, 6] = true := by decide +kernel
theorem subd6_0_136 : subd6_0 [-4, 1, 7] = true := by decide +kernel
theorem subd6_0_137 : subd6_0 [-4, 2, -7] = true := by decide +kernel
theorem subd6_0_138 : subd6_0 [-4, 2, -6] = true := by decide +kernel
theorem subd6_0_139 : subd6_0 [-4, 2, -5] = true := by decide +kernel
theorem subd6_0_140 : subd6_0 [-4, 2, -4] = true := by decide +kernel
theorem subd6_0_141 : subd6_0 [-4, 2, -3] = true := by decide +kernel
theorem subd6_0_142 : subd6_0 [-4, 2, -2] = true := by decide +kernel
theorem subd6_0_143 : subd6_0 [-4, 2, -1] = true := by decide +kernel
theorem subd6_0_144 : subd6_0 [-4, 2, 0] = true := by decide +kernel
theorem subd6_0_145 : subd6_0 [-4, 2, 1] = true := by decide +kernel
theorem subd6_0_146 : subd6_0 [-4, 2, 2] = true := by decide +kernel
theorem subd6_0_147 : subd6_0 [-4, 2, 3] = true := by decide +kernel
theorem subd6_0_148 : subd6_0 [-4, 2, 4] = true := by decide +kernel
theorem subd6_0_149 : subd6_0 [-4, 2, 5] = true := by decide +kernel
theorem subd6_0_150 : subd6_0 [-4, 2, 6] = true := by decide +kernel
theorem subd6_0_151 : subd6_0 [-4, 2, 7] = true := by decide +kernel
theorem subd6_0_152 : subd6_0 [-4, 3, -7] = true := by decide +kernel
theorem subd6_0_153 : subd6_0 [-4, 3, -6] = true := by decide +kernel
theorem subd6_0_154 : subd6_0 [-4, 3, -5] = true := by decide +kernel
theorem subd6_0_155 : subd6_0 [-4, 3, -4] = true := by decide +kernel
theorem subd6_0_156 : subd6_0 [-4, 3, -3] = true := by decide +kernel
theorem subd6_0_157 : subd6_0 [-4, 3, -2] = true := by decide +kernel
theorem subd6_0_158 : subd6_0 [-4, 3, -1] = true := by decide +kernel
theorem subd6_0_159 : subd6_0 [-4, 3, 0] = true := by decide +kernel
theorem sbd6_0_4 : ∀ q ∈ blkd6_0_4, subd6_0 q = true := by
  unfold blkd6_0_4
  exact List.forall_mem_cons.2 ⟨subd6_0_128, List.forall_mem_cons.2 ⟨subd6_0_129, List.forall_mem_cons.2 ⟨subd6_0_130, List.forall_mem_cons.2 ⟨subd6_0_131, List.forall_mem_cons.2 ⟨subd6_0_132, List.forall_mem_cons.2 ⟨subd6_0_133, List.forall_mem_cons.2 ⟨subd6_0_134, List.forall_mem_cons.2 ⟨subd6_0_135, List.forall_mem_cons.2 ⟨subd6_0_136, List.forall_mem_cons.2 ⟨subd6_0_137, List.forall_mem_cons.2 ⟨subd6_0_138, List.forall_mem_cons.2 ⟨subd6_0_139, List.forall_mem_cons.2 ⟨subd6_0_140, List.forall_mem_cons.2 ⟨subd6_0_141, List.forall_mem_cons.2 ⟨subd6_0_142, List.forall_mem_cons.2 ⟨subd6_0_143, List.forall_mem_cons.2 ⟨subd6_0_144, List.forall_mem_cons.2 ⟨subd6_0_145, List.forall_mem_cons.2 ⟨subd6_0_146, List.forall_mem_cons.2 ⟨subd6_0_147, List.forall_mem_cons.2 ⟨subd6_0_148, List.forall_mem_cons.2 ⟨subd6_0_149, List.forall_mem_cons.2 ⟨subd6_0_150, List.forall_mem_cons.2 ⟨subd6_0_151, List.forall_mem_cons.2 ⟨subd6_0_152, List.forall_mem_cons.2 ⟨subd6_0_153, List.forall_mem_cons.2 ⟨subd6_0_154, List.forall_mem_cons.2 ⟨subd6_0_155, List.forall_mem_cons.2 ⟨subd6_0_156, List.forall_mem_cons.2 ⟨subd6_0_157, List.forall_mem_cons.2 ⟨subd6_0_158, List.forall_mem_cons.2 ⟨subd6_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_160 : subd6_0 [-4, 3, 1] = true := by decide +kernel
theorem subd6_0_161 : subd6_0 [-4, 3, 2] = true := by decide +kernel
theorem subd6_0_162 : subd6_0 [-4, 3, 3] = true := by decide +kernel
theorem subd6_0_163 : subd6_0 [-4, 3, 4] = true := by decide +kernel
theorem subd6_0_164 : subd6_0 [-4, 3, 5] = true := by decide +kernel
theorem subd6_0_165 : subd6_0 [-4, 3, 6] = true := by decide +kernel
theorem subd6_0_166 : subd6_0 [-4, 4, -7] = true := by decide +kernel
theorem subd6_0_167 : subd6_0 [-4, 4, -6] = true := by decide +kernel
theorem subd6_0_168 : subd6_0 [-4, 4, -5] = true := by decide +kernel
theorem subd6_0_169 : subd6_0 [-4, 4, -4] = true := by decide +kernel
theorem subd6_0_170 : subd6_0 [-4, 4, -3] = true := by decide +kernel
theorem subd6_0_171 : subd6_0 [-4, 4, -2] = true := by decide +kernel
theorem subd6_0_172 : subd6_0 [-4, 4, -1] = true := by decide +kernel
theorem subd6_0_173 : subd6_0 [-4, 4, 0] = true := by decide +kernel
theorem subd6_0_174 : subd6_0 [-4, 4, 1] = true := by decide +kernel
theorem subd6_0_175 : subd6_0 [-4, 4, 2] = true := by decide +kernel
theorem subd6_0_176 : subd6_0 [-4, 4, 3] = true := by decide +kernel
theorem subd6_0_177 : subd6_0 [-4, 4, 4] = true := by decide +kernel
theorem subd6_0_178 : subd6_0 [-4, 4, 5] = true := by decide +kernel
theorem subd6_0_179 : subd6_0 [-4, 4, 6] = true := by decide +kernel
theorem subd6_0_180 : subd6_0 [-4, 5] = true := by decide +kernel
theorem subd6_0_181 : subd6_0 [-4, 6] = true := by decide +kernel
theorem subd6_0_182 : subd6_0 [-4, 7] = true := by decide +kernel
theorem subd6_0_183 : subd6_0 [-3, -8] = true := by decide +kernel
theorem subd6_0_184 : subd6_0 [-3, -7] = true := by decide +kernel
theorem subd6_0_185 : subd6_0 [-3, -6] = true := by decide +kernel
theorem subd6_0_186 : subd6_0 [-3, -5] = true := by decide +kernel
theorem subd6_0_187 : subd6_0 [-3, -4, -6] = true := by decide +kernel
theorem subd6_0_188 : subd6_0 [-3, -4, -5] = true := by decide +kernel
theorem subd6_0_189 : subd6_0 [-3, -4, -4] = true := by decide +kernel
theorem subd6_0_190 : subd6_0 [-3, -4, -3] = true := by decide +kernel
theorem subd6_0_191 : subd6_0 [-3, -4, -2] = true := by decide +kernel
theorem sbd6_0_5 : ∀ q ∈ blkd6_0_5, subd6_0 q = true := by
  unfold blkd6_0_5
  exact List.forall_mem_cons.2 ⟨subd6_0_160, List.forall_mem_cons.2 ⟨subd6_0_161, List.forall_mem_cons.2 ⟨subd6_0_162, List.forall_mem_cons.2 ⟨subd6_0_163, List.forall_mem_cons.2 ⟨subd6_0_164, List.forall_mem_cons.2 ⟨subd6_0_165, List.forall_mem_cons.2 ⟨subd6_0_166, List.forall_mem_cons.2 ⟨subd6_0_167, List.forall_mem_cons.2 ⟨subd6_0_168, List.forall_mem_cons.2 ⟨subd6_0_169, List.forall_mem_cons.2 ⟨subd6_0_170, List.forall_mem_cons.2 ⟨subd6_0_171, List.forall_mem_cons.2 ⟨subd6_0_172, List.forall_mem_cons.2 ⟨subd6_0_173, List.forall_mem_cons.2 ⟨subd6_0_174, List.forall_mem_cons.2 ⟨subd6_0_175, List.forall_mem_cons.2 ⟨subd6_0_176, List.forall_mem_cons.2 ⟨subd6_0_177, List.forall_mem_cons.2 ⟨subd6_0_178, List.forall_mem_cons.2 ⟨subd6_0_179, List.forall_mem_cons.2 ⟨subd6_0_180, List.forall_mem_cons.2 ⟨subd6_0_181, List.forall_mem_cons.2 ⟨subd6_0_182, List.forall_mem_cons.2 ⟨subd6_0_183, List.forall_mem_cons.2 ⟨subd6_0_184, List.forall_mem_cons.2 ⟨subd6_0_185, List.forall_mem_cons.2 ⟨subd6_0_186, List.forall_mem_cons.2 ⟨subd6_0_187, List.forall_mem_cons.2 ⟨subd6_0_188, List.forall_mem_cons.2 ⟨subd6_0_189, List.forall_mem_cons.2 ⟨subd6_0_190, List.forall_mem_cons.2 ⟨subd6_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_192 : subd6_0 [-3, -4, -1] = true := by decide +kernel
theorem subd6_0_193 : subd6_0 [-3, -4, 0] = true := by decide +kernel
theorem subd6_0_194 : subd6_0 [-3, -4, 1] = true := by decide +kernel
theorem subd6_0_195 : subd6_0 [-3, -4, 2] = true := by decide +kernel
theorem subd6_0_196 : subd6_0 [-3, -4, 3] = true := by decide +kernel
theorem subd6_0_197 : subd6_0 [-3, -4, 4] = true := by decide +kernel
theorem subd6_0_198 : subd6_0 [-3, -4, 5] = true := by decide +kernel
theorem subd6_0_199 : subd6_0 [-3, -4, 6] = true := by decide +kernel
theorem subd6_0_200 : subd6_0 [-3, -4, 7] = true := by decide +kernel
theorem subd6_0_201 : subd6_0 [-3, -3, -7] = true := by decide +kernel
theorem subd6_0_202 : subd6_0 [-3, -3, -6] = true := by decide +kernel
theorem subd6_0_203 : subd6_0 [-3, -3, -5] = true := by decide +kernel
theorem subd6_0_204 : subd6_0 [-3, -3, -4] = true := by decide +kernel
theorem subd6_0_205 : subd6_0 [-3, -3, -3] = true := by decide +kernel
theorem subd6_0_206 : subd6_0 [-3, -3, -2] = true := by decide +kernel
theorem subd6_0_207 : subd6_0 [-3, -3, -1] = true := by decide +kernel
theorem subd6_0_208 : subd6_0 [-3, -3, 0] = true := by decide +kernel
theorem subd6_0_209 : subd6_0 [-3, -3, 1] = true := by decide +kernel
theorem subd6_0_210 : subd6_0 [-3, -3, 2] = true := by decide +kernel
theorem subd6_0_211 : subd6_0 [-3, -3, 3] = true := by decide +kernel
theorem subd6_0_212 : subd6_0 [-3, -3, 4] = true := by decide +kernel
theorem subd6_0_213 : subd6_0 [-3, -3, 5] = true := by decide +kernel
theorem subd6_0_214 : subd6_0 [-3, -3, 6] = true := by decide +kernel
theorem subd6_0_215 : subd6_0 [-3, -3, 7] = true := by decide +kernel
theorem subd6_0_216 : subd6_0 [-3, -2, -7] = true := by decide +kernel
theorem subd6_0_217 : subd6_0 [-3, -2, -6] = true := by decide +kernel
theorem subd6_0_218 : subd6_0 [-3, -2, -5] = true := by decide +kernel
theorem subd6_0_219 : subd6_0 [-3, -2, -4] = true := by decide +kernel
theorem subd6_0_220 : subd6_0 [-3, -2, -3] = true := by decide +kernel
theorem subd6_0_221 : subd6_0 [-3, -2, -2] = true := by decide +kernel
theorem subd6_0_222 : subd6_0 [-3, -2, -1] = true := by decide +kernel
theorem subd6_0_223 : subd6_0 [-3, -2, 0] = true := by decide +kernel
theorem sbd6_0_6 : ∀ q ∈ blkd6_0_6, subd6_0 q = true := by
  unfold blkd6_0_6
  exact List.forall_mem_cons.2 ⟨subd6_0_192, List.forall_mem_cons.2 ⟨subd6_0_193, List.forall_mem_cons.2 ⟨subd6_0_194, List.forall_mem_cons.2 ⟨subd6_0_195, List.forall_mem_cons.2 ⟨subd6_0_196, List.forall_mem_cons.2 ⟨subd6_0_197, List.forall_mem_cons.2 ⟨subd6_0_198, List.forall_mem_cons.2 ⟨subd6_0_199, List.forall_mem_cons.2 ⟨subd6_0_200, List.forall_mem_cons.2 ⟨subd6_0_201, List.forall_mem_cons.2 ⟨subd6_0_202, List.forall_mem_cons.2 ⟨subd6_0_203, List.forall_mem_cons.2 ⟨subd6_0_204, List.forall_mem_cons.2 ⟨subd6_0_205, List.forall_mem_cons.2 ⟨subd6_0_206, List.forall_mem_cons.2 ⟨subd6_0_207, List.forall_mem_cons.2 ⟨subd6_0_208, List.forall_mem_cons.2 ⟨subd6_0_209, List.forall_mem_cons.2 ⟨subd6_0_210, List.forall_mem_cons.2 ⟨subd6_0_211, List.forall_mem_cons.2 ⟨subd6_0_212, List.forall_mem_cons.2 ⟨subd6_0_213, List.forall_mem_cons.2 ⟨subd6_0_214, List.forall_mem_cons.2 ⟨subd6_0_215, List.forall_mem_cons.2 ⟨subd6_0_216, List.forall_mem_cons.2 ⟨subd6_0_217, List.forall_mem_cons.2 ⟨subd6_0_218, List.forall_mem_cons.2 ⟨subd6_0_219, List.forall_mem_cons.2 ⟨subd6_0_220, List.forall_mem_cons.2 ⟨subd6_0_221, List.forall_mem_cons.2 ⟨subd6_0_222, List.forall_mem_cons.2 ⟨subd6_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_224 : subd6_0 [-3, -2, 1] = true := by decide +kernel
theorem subd6_0_225 : subd6_0 [-3, -2, 2] = true := by decide +kernel
theorem subd6_0_226 : subd6_0 [-3, -2, 3] = true := by decide +kernel
theorem subd6_0_227 : subd6_0 [-3, -2, 4] = true := by decide +kernel
theorem subd6_0_228 : subd6_0 [-3, -2, 5] = true := by decide +kernel
theorem subd6_0_229 : subd6_0 [-3, -2, 6] = true := by decide +kernel
theorem subd6_0_230 : subd6_0 [-3, -2, 7] = true := by decide +kernel
theorem subd6_0_231 : subd6_0 [-3, -2, 8] = true := by decide +kernel
theorem subd6_0_232 : subd6_0 [-3, -1, -8] = true := by decide +kernel
theorem subd6_0_233 : subd6_0 [-3, -1, -7] = true := by decide +kernel
theorem subd6_0_234 : subd6_0 [-3, -1, -6] = true := by decide +kernel
theorem subd6_0_235 : subd6_0 [-3, -1, -5] = true := by decide +kernel
theorem subd6_0_236 : subd6_0 [-3, -1, -4] = true := by decide +kernel
theorem subd6_0_237 : subd6_0 [-3, -1, -3] = true := by decide +kernel
theorem subd6_0_238 : subd6_0 [-3, -1, -2] = true := by decide +kernel
theorem subd6_0_239 : subd6_0 [-3, -1, -1] = true := by decide +kernel
theorem subd6_0_240 : subd6_0 [-3, -1, 0] = true := by decide +kernel
theorem subd6_0_241 : subd6_0 [-3, -1, 1] = true := by decide +kernel
theorem subd6_0_242 : subd6_0 [-3, -1, 2] = true := by decide +kernel
theorem subd6_0_243 : subd6_0 [-3, -1, 3] = true := by decide +kernel
theorem subd6_0_244 : subd6_0 [-3, -1, 4] = true := by decide +kernel
theorem subd6_0_245 : subd6_0 [-3, -1, 5] = true := by decide +kernel
theorem subd6_0_246 : subd6_0 [-3, -1, 6] = true := by decide +kernel
theorem subd6_0_247 : subd6_0 [-3, -1, 7] = true := by decide +kernel
theorem subd6_0_248 : subd6_0 [-3, -1, 8] = true := by decide +kernel
theorem subd6_0_249 : subd6_0 [-3, 0, -8] = true := by decide +kernel
theorem subd6_0_250 : subd6_0 [-3, 0, -7] = true := by decide +kernel
theorem subd6_0_251 : subd6_0 [-3, 0, -6] = true := by decide +kernel
theorem subd6_0_252 : subd6_0 [-3, 0, -5] = true := by decide +kernel
theorem subd6_0_253 : subd6_0 [-3, 0, -4] = true := by decide +kernel
theorem subd6_0_254 : subd6_0 [-3, 0, -3] = true := by decide +kernel
theorem subd6_0_255 : subd6_0 [-3, 0, -2] = true := by decide +kernel
theorem sbd6_0_7 : ∀ q ∈ blkd6_0_7, subd6_0 q = true := by
  unfold blkd6_0_7
  exact List.forall_mem_cons.2 ⟨subd6_0_224, List.forall_mem_cons.2 ⟨subd6_0_225, List.forall_mem_cons.2 ⟨subd6_0_226, List.forall_mem_cons.2 ⟨subd6_0_227, List.forall_mem_cons.2 ⟨subd6_0_228, List.forall_mem_cons.2 ⟨subd6_0_229, List.forall_mem_cons.2 ⟨subd6_0_230, List.forall_mem_cons.2 ⟨subd6_0_231, List.forall_mem_cons.2 ⟨subd6_0_232, List.forall_mem_cons.2 ⟨subd6_0_233, List.forall_mem_cons.2 ⟨subd6_0_234, List.forall_mem_cons.2 ⟨subd6_0_235, List.forall_mem_cons.2 ⟨subd6_0_236, List.forall_mem_cons.2 ⟨subd6_0_237, List.forall_mem_cons.2 ⟨subd6_0_238, List.forall_mem_cons.2 ⟨subd6_0_239, List.forall_mem_cons.2 ⟨subd6_0_240, List.forall_mem_cons.2 ⟨subd6_0_241, List.forall_mem_cons.2 ⟨subd6_0_242, List.forall_mem_cons.2 ⟨subd6_0_243, List.forall_mem_cons.2 ⟨subd6_0_244, List.forall_mem_cons.2 ⟨subd6_0_245, List.forall_mem_cons.2 ⟨subd6_0_246, List.forall_mem_cons.2 ⟨subd6_0_247, List.forall_mem_cons.2 ⟨subd6_0_248, List.forall_mem_cons.2 ⟨subd6_0_249, List.forall_mem_cons.2 ⟨subd6_0_250, List.forall_mem_cons.2 ⟨subd6_0_251, List.forall_mem_cons.2 ⟨subd6_0_252, List.forall_mem_cons.2 ⟨subd6_0_253, List.forall_mem_cons.2 ⟨subd6_0_254, List.forall_mem_cons.2 ⟨subd6_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_256 : subd6_0 [-3, 0, -1] = true := by decide +kernel
theorem subd6_0_257 : subd6_0 [-3, 0, 0] = true := by decide +kernel
theorem subd6_0_258 : subd6_0 [-3, 0, 1] = true := by decide +kernel
theorem subd6_0_259 : subd6_0 [-3, 0, 2] = true := by decide +kernel
theorem subd6_0_260 : subd6_0 [-3, 0, 3] = true := by decide +kernel
theorem subd6_0_261 : subd6_0 [-3, 0, 4] = true := by decide +kernel
theorem subd6_0_262 : subd6_0 [-3, 0, 5] = true := by decide +kernel
theorem subd6_0_263 : subd6_0 [-3, 0, 6] = true := by decide +kernel
theorem subd6_0_264 : subd6_0 [-3, 0, 7] = true := by decide +kernel
theorem subd6_0_265 : subd6_0 [-3, 0, 8] = true := by decide +kernel
theorem subd6_0_266 : subd6_0 [-3, 1, -8] = true := by decide +kernel
theorem subd6_0_267 : subd6_0 [-3, 1, -7] = true := by decide +kernel
theorem subd6_0_268 : subd6_0 [-3, 1, -6] = true := by decide +kernel
theorem subd6_0_269 : subd6_0 [-3, 1, -5] = true := by decide +kernel
theorem subd6_0_270 : subd6_0 [-3, 1, -4] = true := by decide +kernel
theorem subd6_0_271 : subd6_0 [-3, 1, -3] = true := by decide +kernel
theorem subd6_0_272 : subd6_0 [-3, 1, -2] = true := by decide +kernel
theorem subd6_0_273 : subd6_0 [-3, 1, -1] = true := by decide +kernel
theorem subd6_0_274 : subd6_0 [-3, 1, 0] = true := by decide +kernel
theorem subd6_0_275 : subd6_0 [-3, 1, 1] = true := by decide +kernel
theorem subd6_0_276 : subd6_0 [-3, 1, 2] = true := by decide +kernel
theorem subd6_0_277 : subd6_0 [-3, 1, 3] = true := by decide +kernel
theorem subd6_0_278 : subd6_0 [-3, 1, 4] = true := by decide +kernel
theorem subd6_0_279 : subd6_0 [-3, 1, 5] = true := by decide +kernel
theorem subd6_0_280 : subd6_0 [-3, 1, 6] = true := by decide +kernel
theorem subd6_0_281 : subd6_0 [-3, 1, 7] = true := by decide +kernel
theorem subd6_0_282 : subd6_0 [-3, 1, 8] = true := by decide +kernel
theorem subd6_0_283 : subd6_0 [-3, 2, -8] = true := by decide +kernel
theorem subd6_0_284 : subd6_0 [-3, 2, -7] = true := by decide +kernel
theorem subd6_0_285 : subd6_0 [-3, 2, -6] = true := by decide +kernel
theorem subd6_0_286 : subd6_0 [-3, 2, -5] = true := by decide +kernel
theorem subd6_0_287 : subd6_0 [-3, 2, -4] = true := by decide +kernel
theorem sbd6_0_8 : ∀ q ∈ blkd6_0_8, subd6_0 q = true := by
  unfold blkd6_0_8
  exact List.forall_mem_cons.2 ⟨subd6_0_256, List.forall_mem_cons.2 ⟨subd6_0_257, List.forall_mem_cons.2 ⟨subd6_0_258, List.forall_mem_cons.2 ⟨subd6_0_259, List.forall_mem_cons.2 ⟨subd6_0_260, List.forall_mem_cons.2 ⟨subd6_0_261, List.forall_mem_cons.2 ⟨subd6_0_262, List.forall_mem_cons.2 ⟨subd6_0_263, List.forall_mem_cons.2 ⟨subd6_0_264, List.forall_mem_cons.2 ⟨subd6_0_265, List.forall_mem_cons.2 ⟨subd6_0_266, List.forall_mem_cons.2 ⟨subd6_0_267, List.forall_mem_cons.2 ⟨subd6_0_268, List.forall_mem_cons.2 ⟨subd6_0_269, List.forall_mem_cons.2 ⟨subd6_0_270, List.forall_mem_cons.2 ⟨subd6_0_271, List.forall_mem_cons.2 ⟨subd6_0_272, List.forall_mem_cons.2 ⟨subd6_0_273, List.forall_mem_cons.2 ⟨subd6_0_274, List.forall_mem_cons.2 ⟨subd6_0_275, List.forall_mem_cons.2 ⟨subd6_0_276, List.forall_mem_cons.2 ⟨subd6_0_277, List.forall_mem_cons.2 ⟨subd6_0_278, List.forall_mem_cons.2 ⟨subd6_0_279, List.forall_mem_cons.2 ⟨subd6_0_280, List.forall_mem_cons.2 ⟨subd6_0_281, List.forall_mem_cons.2 ⟨subd6_0_282, List.forall_mem_cons.2 ⟨subd6_0_283, List.forall_mem_cons.2 ⟨subd6_0_284, List.forall_mem_cons.2 ⟨subd6_0_285, List.forall_mem_cons.2 ⟨subd6_0_286, List.forall_mem_cons.2 ⟨subd6_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_288 : subd6_0 [-3, 2, -3] = true := by decide +kernel
theorem subd6_0_289 : subd6_0 [-3, 2, -2] = true := by decide +kernel
theorem subd6_0_290 : subd6_0 [-3, 2, -1] = true := by decide +kernel
theorem subd6_0_291 : subd6_0 [-3, 2, 0] = true := by decide +kernel
theorem subd6_0_292 : subd6_0 [-3, 2, 1] = true := by decide +kernel
theorem subd6_0_293 : subd6_0 [-3, 2, 2] = true := by decide +kernel
theorem subd6_0_294 : subd6_0 [-3, 2, 3] = true := by decide +kernel
theorem subd6_0_295 : subd6_0 [-3, 2, 4] = true := by decide +kernel
theorem subd6_0_296 : subd6_0 [-3, 2, 5] = true := by decide +kernel
theorem subd6_0_297 : subd6_0 [-3, 2, 6] = true := by decide +kernel
theorem subd6_0_298 : subd6_0 [-3, 2, 7] = true := by decide +kernel
theorem subd6_0_299 : subd6_0 [-3, 3, -8] = true := by decide +kernel
theorem subd6_0_300 : subd6_0 [-3, 3, -7] = true := by decide +kernel
theorem subd6_0_301 : subd6_0 [-3, 3, -6] = true := by decide +kernel
theorem subd6_0_302 : subd6_0 [-3, 3, -5] = true := by decide +kernel
theorem subd6_0_303 : subd6_0 [-3, 3, -4] = true := by decide +kernel
theorem subd6_0_304 : subd6_0 [-3, 3, -3] = true := by decide +kernel
theorem subd6_0_305 : subd6_0 [-3, 3, -2] = true := by decide +kernel
theorem subd6_0_306 : subd6_0 [-3, 3, -1] = true := by decide +kernel
theorem subd6_0_307 : subd6_0 [-3, 3, 0] = true := by decide +kernel
theorem subd6_0_308 : subd6_0 [-3, 3, 1] = true := by decide +kernel
theorem subd6_0_309 : subd6_0 [-3, 3, 2] = true := by decide +kernel
theorem subd6_0_310 : subd6_0 [-3, 3, 3] = true := by decide +kernel
theorem subd6_0_311 : subd6_0 [-3, 3, 4] = true := by decide +kernel
theorem subd6_0_312 : subd6_0 [-3, 3, 5] = true := by decide +kernel
theorem subd6_0_313 : subd6_0 [-3, 3, 6] = true := by decide +kernel
theorem subd6_0_314 : subd6_0 [-3, 3, 7] = true := by decide +kernel
theorem subd6_0_315 : subd6_0 [-3, 4, -8] = true := by decide +kernel
theorem subd6_0_316 : subd6_0 [-3, 4, -7] = true := by decide +kernel
theorem subd6_0_317 : subd6_0 [-3, 4, -6] = true := by decide +kernel
theorem subd6_0_318 : subd6_0 [-3, 4, -5] = true := by decide +kernel
theorem subd6_0_319 : subd6_0 [-3, 4, -4] = true := by decide +kernel
theorem sbd6_0_9 : ∀ q ∈ blkd6_0_9, subd6_0 q = true := by
  unfold blkd6_0_9
  exact List.forall_mem_cons.2 ⟨subd6_0_288, List.forall_mem_cons.2 ⟨subd6_0_289, List.forall_mem_cons.2 ⟨subd6_0_290, List.forall_mem_cons.2 ⟨subd6_0_291, List.forall_mem_cons.2 ⟨subd6_0_292, List.forall_mem_cons.2 ⟨subd6_0_293, List.forall_mem_cons.2 ⟨subd6_0_294, List.forall_mem_cons.2 ⟨subd6_0_295, List.forall_mem_cons.2 ⟨subd6_0_296, List.forall_mem_cons.2 ⟨subd6_0_297, List.forall_mem_cons.2 ⟨subd6_0_298, List.forall_mem_cons.2 ⟨subd6_0_299, List.forall_mem_cons.2 ⟨subd6_0_300, List.forall_mem_cons.2 ⟨subd6_0_301, List.forall_mem_cons.2 ⟨subd6_0_302, List.forall_mem_cons.2 ⟨subd6_0_303, List.forall_mem_cons.2 ⟨subd6_0_304, List.forall_mem_cons.2 ⟨subd6_0_305, List.forall_mem_cons.2 ⟨subd6_0_306, List.forall_mem_cons.2 ⟨subd6_0_307, List.forall_mem_cons.2 ⟨subd6_0_308, List.forall_mem_cons.2 ⟨subd6_0_309, List.forall_mem_cons.2 ⟨subd6_0_310, List.forall_mem_cons.2 ⟨subd6_0_311, List.forall_mem_cons.2 ⟨subd6_0_312, List.forall_mem_cons.2 ⟨subd6_0_313, List.forall_mem_cons.2 ⟨subd6_0_314, List.forall_mem_cons.2 ⟨subd6_0_315, List.forall_mem_cons.2 ⟨subd6_0_316, List.forall_mem_cons.2 ⟨subd6_0_317, List.forall_mem_cons.2 ⟨subd6_0_318, List.forall_mem_cons.2 ⟨subd6_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_320 : subd6_0 [-3, 4, -3] = true := by decide +kernel
theorem subd6_0_321 : subd6_0 [-3, 4, -2] = true := by decide +kernel
theorem subd6_0_322 : subd6_0 [-3, 4, -1] = true := by decide +kernel
theorem subd6_0_323 : subd6_0 [-3, 4, 0] = true := by decide +kernel
theorem subd6_0_324 : subd6_0 [-3, 4, 1] = true := by decide +kernel
theorem subd6_0_325 : subd6_0 [-3, 4, 2] = true := by decide +kernel
theorem subd6_0_326 : subd6_0 [-3, 4, 3] = true := by decide +kernel
theorem subd6_0_327 : subd6_0 [-3, 4, 4] = true := by decide +kernel
theorem subd6_0_328 : subd6_0 [-3, 4, 5] = true := by decide +kernel
theorem subd6_0_329 : subd6_0 [-3, 4, 6] = true := by decide +kernel
theorem subd6_0_330 : subd6_0 [-3, 5] = true := by decide +kernel
theorem subd6_0_331 : subd6_0 [-3, 6] = true := by decide +kernel
theorem subd6_0_332 : subd6_0 [-3, 7] = true := by decide +kernel
theorem subd6_0_333 : subd6_0 [-2, -8] = true := by decide +kernel
theorem subd6_0_334 : subd6_0 [-2, -7] = true := by decide +kernel
theorem subd6_0_335 : subd6_0 [-2, -6] = true := by decide +kernel
theorem subd6_0_336 : subd6_0 [-2, -5] = true := by decide +kernel
theorem subd6_0_337 : subd6_0 [-2, -4, -7] = true := by decide +kernel
theorem subd6_0_338 : subd6_0 [-2, -4, -6] = true := by decide +kernel
theorem subd6_0_339 : subd6_0 [-2, -4, -5] = true := by decide +kernel
theorem subd6_0_340 : subd6_0 [-2, -4, -4] = true := by decide +kernel
theorem subd6_0_341 : subd6_0 [-2, -4, -3] = true := by decide +kernel
theorem subd6_0_342 : subd6_0 [-2, -4, -2] = true := by decide +kernel
theorem subd6_0_343 : subd6_0 [-2, -4, -1] = true := by decide +kernel
theorem subd6_0_344 : subd6_0 [-2, -4, 0] = true := by decide +kernel
theorem subd6_0_345 : subd6_0 [-2, -4, 1] = true := by decide +kernel
theorem subd6_0_346 : subd6_0 [-2, -4, 2] = true := by decide +kernel
theorem subd6_0_347 : subd6_0 [-2, -4, 3] = true := by decide +kernel
theorem subd6_0_348 : subd6_0 [-2, -4, 4] = true := by decide +kernel
theorem subd6_0_349 : subd6_0 [-2, -4, 5] = true := by decide +kernel
theorem subd6_0_350 : subd6_0 [-2, -4, 6] = true := by decide +kernel
theorem subd6_0_351 : subd6_0 [-2, -4, 7] = true := by decide +kernel
theorem sbd6_0_10 : ∀ q ∈ blkd6_0_10, subd6_0 q = true := by
  unfold blkd6_0_10
  exact List.forall_mem_cons.2 ⟨subd6_0_320, List.forall_mem_cons.2 ⟨subd6_0_321, List.forall_mem_cons.2 ⟨subd6_0_322, List.forall_mem_cons.2 ⟨subd6_0_323, List.forall_mem_cons.2 ⟨subd6_0_324, List.forall_mem_cons.2 ⟨subd6_0_325, List.forall_mem_cons.2 ⟨subd6_0_326, List.forall_mem_cons.2 ⟨subd6_0_327, List.forall_mem_cons.2 ⟨subd6_0_328, List.forall_mem_cons.2 ⟨subd6_0_329, List.forall_mem_cons.2 ⟨subd6_0_330, List.forall_mem_cons.2 ⟨subd6_0_331, List.forall_mem_cons.2 ⟨subd6_0_332, List.forall_mem_cons.2 ⟨subd6_0_333, List.forall_mem_cons.2 ⟨subd6_0_334, List.forall_mem_cons.2 ⟨subd6_0_335, List.forall_mem_cons.2 ⟨subd6_0_336, List.forall_mem_cons.2 ⟨subd6_0_337, List.forall_mem_cons.2 ⟨subd6_0_338, List.forall_mem_cons.2 ⟨subd6_0_339, List.forall_mem_cons.2 ⟨subd6_0_340, List.forall_mem_cons.2 ⟨subd6_0_341, List.forall_mem_cons.2 ⟨subd6_0_342, List.forall_mem_cons.2 ⟨subd6_0_343, List.forall_mem_cons.2 ⟨subd6_0_344, List.forall_mem_cons.2 ⟨subd6_0_345, List.forall_mem_cons.2 ⟨subd6_0_346, List.forall_mem_cons.2 ⟨subd6_0_347, List.forall_mem_cons.2 ⟨subd6_0_348, List.forall_mem_cons.2 ⟨subd6_0_349, List.forall_mem_cons.2 ⟨subd6_0_350, List.forall_mem_cons.2 ⟨subd6_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_352 : subd6_0 [-2, -3, -7] = true := by decide +kernel
theorem subd6_0_353 : subd6_0 [-2, -3, -6] = true := by decide +kernel
theorem subd6_0_354 : subd6_0 [-2, -3, -5] = true := by decide +kernel
theorem subd6_0_355 : subd6_0 [-2, -3, -4] = true := by decide +kernel
theorem subd6_0_356 : subd6_0 [-2, -3, -3] = true := by decide +kernel
theorem subd6_0_357 : subd6_0 [-2, -3, -2] = true := by decide +kernel
theorem subd6_0_358 : subd6_0 [-2, -3, -1] = true := by decide +kernel
theorem subd6_0_359 : subd6_0 [-2, -3, 0] = true := by decide +kernel
theorem subd6_0_360 : subd6_0 [-2, -3, 1] = true := by decide +kernel
theorem subd6_0_361 : subd6_0 [-2, -3, 2] = true := by decide +kernel
theorem subd6_0_362 : subd6_0 [-2, -3, 3] = true := by decide +kernel
theorem subd6_0_363 : subd6_0 [-2, -3, 4] = true := by decide +kernel
theorem subd6_0_364 : subd6_0 [-2, -3, 5] = true := by decide +kernel
theorem subd6_0_365 : subd6_0 [-2, -3, 6] = true := by decide +kernel
theorem subd6_0_366 : subd6_0 [-2, -3, 7] = true := by decide +kernel
theorem subd6_0_367 : subd6_0 [-2, -3, 8] = true := by decide +kernel
theorem subd6_0_368 : subd6_0 [-2, -2, -8] = true := by decide +kernel
theorem subd6_0_369 : subd6_0 [-2, -2, -7] = true := by decide +kernel
theorem subd6_0_370 : subd6_0 [-2, -2, -6] = true := by decide +kernel
theorem subd6_0_371 : subd6_0 [-2, -2, -5] = true := by decide +kernel
theorem subd6_0_372 : subd6_0 [-2, -2, -4] = true := by decide +kernel
theorem subd6_0_373 : subd6_0 [-2, -2, -3] = true := by decide +kernel
theorem subd6_0_374 : subd6_0 [-2, -2, -2] = true := by decide +kernel
theorem subd6_0_375 : subd6_0 [-2, -2, -1] = true := by decide +kernel
theorem subd6_0_376 : subd6_0 [-2, -2, 0] = true := by decide +kernel
theorem subd6_0_377 : subd6_0 [-2, -2, 1] = true := by decide +kernel
theorem subd6_0_378 : subd6_0 [-2, -2, 2] = true := by decide +kernel
theorem subd6_0_379 : subd6_0 [-2, -2, 3] = true := by decide +kernel
theorem subd6_0_380 : subd6_0 [-2, -2, 4] = true := by decide +kernel
theorem subd6_0_381 : subd6_0 [-2, -2, 5] = true := by decide +kernel
theorem subd6_0_382 : subd6_0 [-2, -2, 6] = true := by decide +kernel
theorem subd6_0_383 : subd6_0 [-2, -2, 7] = true := by decide +kernel
theorem sbd6_0_11 : ∀ q ∈ blkd6_0_11, subd6_0 q = true := by
  unfold blkd6_0_11
  exact List.forall_mem_cons.2 ⟨subd6_0_352, List.forall_mem_cons.2 ⟨subd6_0_353, List.forall_mem_cons.2 ⟨subd6_0_354, List.forall_mem_cons.2 ⟨subd6_0_355, List.forall_mem_cons.2 ⟨subd6_0_356, List.forall_mem_cons.2 ⟨subd6_0_357, List.forall_mem_cons.2 ⟨subd6_0_358, List.forall_mem_cons.2 ⟨subd6_0_359, List.forall_mem_cons.2 ⟨subd6_0_360, List.forall_mem_cons.2 ⟨subd6_0_361, List.forall_mem_cons.2 ⟨subd6_0_362, List.forall_mem_cons.2 ⟨subd6_0_363, List.forall_mem_cons.2 ⟨subd6_0_364, List.forall_mem_cons.2 ⟨subd6_0_365, List.forall_mem_cons.2 ⟨subd6_0_366, List.forall_mem_cons.2 ⟨subd6_0_367, List.forall_mem_cons.2 ⟨subd6_0_368, List.forall_mem_cons.2 ⟨subd6_0_369, List.forall_mem_cons.2 ⟨subd6_0_370, List.forall_mem_cons.2 ⟨subd6_0_371, List.forall_mem_cons.2 ⟨subd6_0_372, List.forall_mem_cons.2 ⟨subd6_0_373, List.forall_mem_cons.2 ⟨subd6_0_374, List.forall_mem_cons.2 ⟨subd6_0_375, List.forall_mem_cons.2 ⟨subd6_0_376, List.forall_mem_cons.2 ⟨subd6_0_377, List.forall_mem_cons.2 ⟨subd6_0_378, List.forall_mem_cons.2 ⟨subd6_0_379, List.forall_mem_cons.2 ⟨subd6_0_380, List.forall_mem_cons.2 ⟨subd6_0_381, List.forall_mem_cons.2 ⟨subd6_0_382, List.forall_mem_cons.2 ⟨subd6_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_384 : subd6_0 [-2, -2, 8] = true := by decide +kernel
theorem subd6_0_385 : subd6_0 [-2, -1, -8] = true := by decide +kernel
theorem subd6_0_386 : subd6_0 [-2, -1, -7] = true := by decide +kernel
theorem subd6_0_387 : subd6_0 [-2, -1, -6] = true := by decide +kernel
theorem subd6_0_388 : subd6_0 [-2, -1, -5] = true := by decide +kernel
theorem subd6_0_389 : subd6_0 [-2, -1, -4] = true := by decide +kernel
theorem subd6_0_390 : subd6_0 [-2, -1, -3] = true := by decide +kernel
theorem subd6_0_391 : subd6_0 [-2, -1, -2] = true := by decide +kernel
theorem subd6_0_392 : subd6_0 [-2, -1, -1] = true := by decide +kernel
theorem subd6_0_393 : subd6_0 [-2, -1, 0] = true := by decide +kernel
theorem subd6_0_394 : subd6_0 [-2, -1, 1] = true := by decide +kernel
theorem subd6_0_395 : subd6_0 [-2, -1, 2] = true := by decide +kernel
theorem subd6_0_396 : subd6_0 [-2, -1, 3] = true := by decide +kernel
theorem subd6_0_397 : subd6_0 [-2, -1, 4] = true := by decide +kernel
theorem subd6_0_398 : subd6_0 [-2, -1, 5] = true := by decide +kernel
theorem subd6_0_399 : subd6_0 [-2, -1, 6] = true := by decide +kernel
theorem subd6_0_400 : subd6_0 [-2, -1, 7] = true := by decide +kernel
theorem subd6_0_401 : subd6_0 [-2, -1, 8] = true := by decide +kernel
theorem subd6_0_402 : subd6_0 [-2, 0, -9] = true := by decide +kernel
theorem subd6_0_403 : subd6_0 [-2, 0, -8] = true := by decide +kernel
theorem subd6_0_404 : subd6_0 [-2, 0, -7] = true := by decide +kernel
theorem subd6_0_405 : subd6_0 [-2, 0, -6] = true := by decide +kernel
theorem subd6_0_406 : subd6_0 [-2, 0, -5] = true := by decide +kernel
theorem subd6_0_407 : subd6_0 [-2, 0, -4] = true := by decide +kernel
theorem subd6_0_408 : subd6_0 [-2, 0, -3] = true := by decide +kernel
theorem subd6_0_409 : subd6_0 [-2, 0, -2] = true := by decide +kernel
theorem subd6_0_410 : subd6_0 [-2, 0, -1] = true := by decide +kernel
theorem subd6_0_411 : subd6_0 [-2, 0, 0] = true := by decide +kernel
theorem subd6_0_412 : subd6_0 [-2, 0, 1] = true := by decide +kernel
theorem subd6_0_413 : subd6_0 [-2, 0, 2] = true := by decide +kernel
theorem subd6_0_414 : subd6_0 [-2, 0, 3] = true := by decide +kernel
theorem subd6_0_415 : subd6_0 [-2, 0, 4] = true := by decide +kernel
theorem sbd6_0_12 : ∀ q ∈ blkd6_0_12, subd6_0 q = true := by
  unfold blkd6_0_12
  exact List.forall_mem_cons.2 ⟨subd6_0_384, List.forall_mem_cons.2 ⟨subd6_0_385, List.forall_mem_cons.2 ⟨subd6_0_386, List.forall_mem_cons.2 ⟨subd6_0_387, List.forall_mem_cons.2 ⟨subd6_0_388, List.forall_mem_cons.2 ⟨subd6_0_389, List.forall_mem_cons.2 ⟨subd6_0_390, List.forall_mem_cons.2 ⟨subd6_0_391, List.forall_mem_cons.2 ⟨subd6_0_392, List.forall_mem_cons.2 ⟨subd6_0_393, List.forall_mem_cons.2 ⟨subd6_0_394, List.forall_mem_cons.2 ⟨subd6_0_395, List.forall_mem_cons.2 ⟨subd6_0_396, List.forall_mem_cons.2 ⟨subd6_0_397, List.forall_mem_cons.2 ⟨subd6_0_398, List.forall_mem_cons.2 ⟨subd6_0_399, List.forall_mem_cons.2 ⟨subd6_0_400, List.forall_mem_cons.2 ⟨subd6_0_401, List.forall_mem_cons.2 ⟨subd6_0_402, List.forall_mem_cons.2 ⟨subd6_0_403, List.forall_mem_cons.2 ⟨subd6_0_404, List.forall_mem_cons.2 ⟨subd6_0_405, List.forall_mem_cons.2 ⟨subd6_0_406, List.forall_mem_cons.2 ⟨subd6_0_407, List.forall_mem_cons.2 ⟨subd6_0_408, List.forall_mem_cons.2 ⟨subd6_0_409, List.forall_mem_cons.2 ⟨subd6_0_410, List.forall_mem_cons.2 ⟨subd6_0_411, List.forall_mem_cons.2 ⟨subd6_0_412, List.forall_mem_cons.2 ⟨subd6_0_413, List.forall_mem_cons.2 ⟨subd6_0_414, List.forall_mem_cons.2 ⟨subd6_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_416 : subd6_0 [-2, 0, 5] = true := by decide +kernel
theorem subd6_0_417 : subd6_0 [-2, 0, 6] = true := by decide +kernel
theorem subd6_0_418 : subd6_0 [-2, 0, 7] = true := by decide +kernel
theorem subd6_0_419 : subd6_0 [-2, 0, 8] = true := by decide +kernel
theorem subd6_0_420 : subd6_0 [-2, 1, -9] = true := by decide +kernel
theorem subd6_0_421 : subd6_0 [-2, 1, -8] = true := by decide +kernel
theorem subd6_0_422 : subd6_0 [-2, 1, -7] = true := by decide +kernel
theorem subd6_0_423 : subd6_0 [-2, 1, -6] = true := by decide +kernel
theorem subd6_0_424 : subd6_0 [-2, 1, -5] = true := by decide +kernel
theorem subd6_0_425 : subd6_0 [-2, 1, -4] = true := by decide +kernel
theorem subd6_0_426 : subd6_0 [-2, 1, -3] = true := by decide +kernel
theorem subd6_0_427 : subd6_0 [-2, 1, -2] = true := by decide +kernel
theorem subd6_0_428 : subd6_0 [-2, 1, -1] = true := by decide +kernel
theorem subd6_0_429 : subd6_0 [-2, 1, 0] = true := by decide +kernel
theorem subd6_0_430 : subd6_0 [-2, 1, 1] = true := by decide +kernel
theorem subd6_0_431 : subd6_0 [-2, 1, 2] = true := by decide +kernel
theorem subd6_0_432 : subd6_0 [-2, 1, 3] = true := by decide +kernel
theorem subd6_0_433 : subd6_0 [-2, 1, 4] = true := by decide +kernel
theorem subd6_0_434 : subd6_0 [-2, 1, 5] = true := by decide +kernel
theorem subd6_0_435 : subd6_0 [-2, 1, 6] = true := by decide +kernel
theorem subd6_0_436 : subd6_0 [-2, 1, 7] = true := by decide +kernel
theorem subd6_0_437 : subd6_0 [-2, 1, 8] = true := by decide +kernel
theorem subd6_0_438 : subd6_0 [-2, 2, -9] = true := by decide +kernel
theorem subd6_0_439 : subd6_0 [-2, 2, -8] = true := by decide +kernel
theorem subd6_0_440 : subd6_0 [-2, 2, -7] = true := by decide +kernel
theorem subd6_0_441 : subd6_0 [-2, 2, -6] = true := by decide +kernel
theorem subd6_0_442 : subd6_0 [-2, 2, -5] = true := by decide +kernel
theorem subd6_0_443 : subd6_0 [-2, 2, -4] = true := by decide +kernel
theorem subd6_0_444 : subd6_0 [-2, 2, -3] = true := by decide +kernel
theorem subd6_0_445 : subd6_0 [-2, 2, -2] = true := by decide +kernel
theorem subd6_0_446 : subd6_0 [-2, 2, -1] = true := by decide +kernel
theorem subd6_0_447 : subd6_0 [-2, 2, 0] = true := by decide +kernel
theorem sbd6_0_13 : ∀ q ∈ blkd6_0_13, subd6_0 q = true := by
  unfold blkd6_0_13
  exact List.forall_mem_cons.2 ⟨subd6_0_416, List.forall_mem_cons.2 ⟨subd6_0_417, List.forall_mem_cons.2 ⟨subd6_0_418, List.forall_mem_cons.2 ⟨subd6_0_419, List.forall_mem_cons.2 ⟨subd6_0_420, List.forall_mem_cons.2 ⟨subd6_0_421, List.forall_mem_cons.2 ⟨subd6_0_422, List.forall_mem_cons.2 ⟨subd6_0_423, List.forall_mem_cons.2 ⟨subd6_0_424, List.forall_mem_cons.2 ⟨subd6_0_425, List.forall_mem_cons.2 ⟨subd6_0_426, List.forall_mem_cons.2 ⟨subd6_0_427, List.forall_mem_cons.2 ⟨subd6_0_428, List.forall_mem_cons.2 ⟨subd6_0_429, List.forall_mem_cons.2 ⟨subd6_0_430, List.forall_mem_cons.2 ⟨subd6_0_431, List.forall_mem_cons.2 ⟨subd6_0_432, List.forall_mem_cons.2 ⟨subd6_0_433, List.forall_mem_cons.2 ⟨subd6_0_434, List.forall_mem_cons.2 ⟨subd6_0_435, List.forall_mem_cons.2 ⟨subd6_0_436, List.forall_mem_cons.2 ⟨subd6_0_437, List.forall_mem_cons.2 ⟨subd6_0_438, List.forall_mem_cons.2 ⟨subd6_0_439, List.forall_mem_cons.2 ⟨subd6_0_440, List.forall_mem_cons.2 ⟨subd6_0_441, List.forall_mem_cons.2 ⟨subd6_0_442, List.forall_mem_cons.2 ⟨subd6_0_443, List.forall_mem_cons.2 ⟨subd6_0_444, List.forall_mem_cons.2 ⟨subd6_0_445, List.forall_mem_cons.2 ⟨subd6_0_446, List.forall_mem_cons.2 ⟨subd6_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_448 : subd6_0 [-2, 2, 1] = true := by decide +kernel
theorem subd6_0_449 : subd6_0 [-2, 2, 2] = true := by decide +kernel
theorem subd6_0_450 : subd6_0 [-2, 2, 3] = true := by decide +kernel
theorem subd6_0_451 : subd6_0 [-2, 2, 4] = true := by decide +kernel
theorem subd6_0_452 : subd6_0 [-2, 2, 5] = true := by decide +kernel
theorem subd6_0_453 : subd6_0 [-2, 2, 6] = true := by decide +kernel
theorem subd6_0_454 : subd6_0 [-2, 2, 7] = true := by decide +kernel
theorem subd6_0_455 : subd6_0 [-2, 3, -8] = true := by decide +kernel
theorem subd6_0_456 : subd6_0 [-2, 3, -7] = true := by decide +kernel
theorem subd6_0_457 : subd6_0 [-2, 3, -6] = true := by decide +kernel
theorem subd6_0_458 : subd6_0 [-2, 3, -5] = true := by decide +kernel
theorem subd6_0_459 : subd6_0 [-2, 3, -4] = true := by decide +kernel
theorem subd6_0_460 : subd6_0 [-2, 3, -3] = true := by decide +kernel
theorem subd6_0_461 : subd6_0 [-2, 3, -2] = true := by decide +kernel
theorem subd6_0_462 : subd6_0 [-2, 3, -1] = true := by decide +kernel
theorem subd6_0_463 : subd6_0 [-2, 3, 0] = true := by decide +kernel
theorem subd6_0_464 : subd6_0 [-2, 3, 1] = true := by decide +kernel
theorem subd6_0_465 : subd6_0 [-2, 3, 2] = true := by decide +kernel
theorem subd6_0_466 : subd6_0 [-2, 3, 3] = true := by decide +kernel
theorem subd6_0_467 : subd6_0 [-2, 3, 4] = true := by decide +kernel
theorem subd6_0_468 : subd6_0 [-2, 3, 5] = true := by decide +kernel
theorem subd6_0_469 : subd6_0 [-2, 3, 6] = true := by decide +kernel
theorem subd6_0_470 : subd6_0 [-2, 3, 7] = true := by decide +kernel
theorem subd6_0_471 : subd6_0 [-2, 4, -8] = true := by decide +kernel
theorem subd6_0_472 : subd6_0 [-2, 4, -7] = true := by decide +kernel
theorem subd6_0_473 : subd6_0 [-2, 4, -6] = true := by decide +kernel
theorem subd6_0_474 : subd6_0 [-2, 4, -5] = true := by decide +kernel
theorem subd6_0_475 : subd6_0 [-2, 4, -4] = true := by decide +kernel
theorem subd6_0_476 : subd6_0 [-2, 4, -3] = true := by decide +kernel
theorem subd6_0_477 : subd6_0 [-2, 4, -2] = true := by decide +kernel
theorem subd6_0_478 : subd6_0 [-2, 4, -1] = true := by decide +kernel
theorem subd6_0_479 : subd6_0 [-2, 4, 0] = true := by decide +kernel
theorem sbd6_0_14 : ∀ q ∈ blkd6_0_14, subd6_0 q = true := by
  unfold blkd6_0_14
  exact List.forall_mem_cons.2 ⟨subd6_0_448, List.forall_mem_cons.2 ⟨subd6_0_449, List.forall_mem_cons.2 ⟨subd6_0_450, List.forall_mem_cons.2 ⟨subd6_0_451, List.forall_mem_cons.2 ⟨subd6_0_452, List.forall_mem_cons.2 ⟨subd6_0_453, List.forall_mem_cons.2 ⟨subd6_0_454, List.forall_mem_cons.2 ⟨subd6_0_455, List.forall_mem_cons.2 ⟨subd6_0_456, List.forall_mem_cons.2 ⟨subd6_0_457, List.forall_mem_cons.2 ⟨subd6_0_458, List.forall_mem_cons.2 ⟨subd6_0_459, List.forall_mem_cons.2 ⟨subd6_0_460, List.forall_mem_cons.2 ⟨subd6_0_461, List.forall_mem_cons.2 ⟨subd6_0_462, List.forall_mem_cons.2 ⟨subd6_0_463, List.forall_mem_cons.2 ⟨subd6_0_464, List.forall_mem_cons.2 ⟨subd6_0_465, List.forall_mem_cons.2 ⟨subd6_0_466, List.forall_mem_cons.2 ⟨subd6_0_467, List.forall_mem_cons.2 ⟨subd6_0_468, List.forall_mem_cons.2 ⟨subd6_0_469, List.forall_mem_cons.2 ⟨subd6_0_470, List.forall_mem_cons.2 ⟨subd6_0_471, List.forall_mem_cons.2 ⟨subd6_0_472, List.forall_mem_cons.2 ⟨subd6_0_473, List.forall_mem_cons.2 ⟨subd6_0_474, List.forall_mem_cons.2 ⟨subd6_0_475, List.forall_mem_cons.2 ⟨subd6_0_476, List.forall_mem_cons.2 ⟨subd6_0_477, List.forall_mem_cons.2 ⟨subd6_0_478, List.forall_mem_cons.2 ⟨subd6_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
