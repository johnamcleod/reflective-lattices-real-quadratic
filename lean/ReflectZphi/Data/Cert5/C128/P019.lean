import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_32 : subd5_1 [-3, -1, 2] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [-3, -1, 3] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [-3, -1, 4] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [-3, -1, 5] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [-3, 0, -8] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [-3, 0, -7] = true := by decide +kernel
theorem subd5_1_38 : subd5_1 [-3, 0, -6] = true := by decide +kernel
theorem subd5_1_39 : subd5_1 [-3, 0, -5] = true := by decide +kernel
theorem subd5_1_40 : subd5_1 [-3, 0, -4] = true := by decide +kernel
theorem subd5_1_41 : subd5_1 [-3, 0, -3] = true := by decide +kernel
theorem subd5_1_42 : subd5_1 [-3, 0, -2] = true := by decide +kernel
theorem subd5_1_43 : subd5_1 [-3, 0, -1] = true := by decide +kernel
theorem subd5_1_44 : subd5_1 [-3, 0, 0] = true := by decide +kernel
theorem subd5_1_45 : subd5_1 [-3, 0, 1] = true := by decide +kernel
theorem subd5_1_46 : subd5_1 [-3, 0, 2] = true := by decide +kernel
theorem subd5_1_47 : subd5_1 [-3, 0, 3] = true := by decide +kernel
theorem subd5_1_48 : subd5_1 [-3, 0, 4] = true := by decide +kernel
theorem subd5_1_49 : subd5_1 [-3, 1] = true := by decide +kernel
theorem subd5_1_50 : subd5_1 [-3, 2] = true := by decide +kernel
theorem subd5_1_51 : subd5_1 [-3, 3] = true := by decide +kernel
theorem subd5_1_52 : subd5_1 [-3, 4] = true := by decide +kernel
theorem subd5_1_53 : subd5_1 [-2, -6] = true := by decide +kernel
theorem subd5_1_54 : subd5_1 [-2, -5] = true := by decide +kernel
theorem subd5_1_55 : subd5_1 [-2, -4] = true := by decide +kernel
theorem subd5_1_56 : subd5_1 [-2, -3] = true := by decide +kernel
theorem subd5_1_57 : subd5_1 [-2, -2, -7] = true := by decide +kernel
theorem subd5_1_58 : subd5_1 [-2, -2, -6] = true := by decide +kernel
theorem subd5_1_59 : subd5_1 [-2, -2, -5] = true := by decide +kernel
theorem subd5_1_60 : subd5_1 [-2, -2, -4] = true := by decide +kernel
theorem subd5_1_61 : subd5_1 [-2, -2, -3] = true := by decide +kernel
theorem subd5_1_62 : subd5_1 [-2, -2, -2] = true := by decide +kernel
theorem subd5_1_63 : subd5_1 [-2, -2, -1] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_cons.2 ⟨subd5_1_38, List.forall_mem_cons.2 ⟨subd5_1_39, List.forall_mem_cons.2 ⟨subd5_1_40, List.forall_mem_cons.2 ⟨subd5_1_41, List.forall_mem_cons.2 ⟨subd5_1_42, List.forall_mem_cons.2 ⟨subd5_1_43, List.forall_mem_cons.2 ⟨subd5_1_44, List.forall_mem_cons.2 ⟨subd5_1_45, List.forall_mem_cons.2 ⟨subd5_1_46, List.forall_mem_cons.2 ⟨subd5_1_47, List.forall_mem_cons.2 ⟨subd5_1_48, List.forall_mem_cons.2 ⟨subd5_1_49, List.forall_mem_cons.2 ⟨subd5_1_50, List.forall_mem_cons.2 ⟨subd5_1_51, List.forall_mem_cons.2 ⟨subd5_1_52, List.forall_mem_cons.2 ⟨subd5_1_53, List.forall_mem_cons.2 ⟨subd5_1_54, List.forall_mem_cons.2 ⟨subd5_1_55, List.forall_mem_cons.2 ⟨subd5_1_56, List.forall_mem_cons.2 ⟨subd5_1_57, List.forall_mem_cons.2 ⟨subd5_1_58, List.forall_mem_cons.2 ⟨subd5_1_59, List.forall_mem_cons.2 ⟨subd5_1_60, List.forall_mem_cons.2 ⟨subd5_1_61, List.forall_mem_cons.2 ⟨subd5_1_62, List.forall_mem_cons.2 ⟨subd5_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_64 : subd5_1 [-2, -2, 0] = true := by decide +kernel
theorem subd5_1_65 : subd5_1 [-2, -2, 1] = true := by decide +kernel
theorem subd5_1_66 : subd5_1 [-2, -2, 2] = true := by decide +kernel
theorem subd5_1_67 : subd5_1 [-2, -2, 3] = true := by decide +kernel
theorem subd5_1_68 : subd5_1 [-2, -2, 4] = true := by decide +kernel
theorem subd5_1_69 : subd5_1 [-2, -2, 5] = true := by decide +kernel
theorem subd5_1_70 : subd5_1 [-2, -2, 6] = true := by decide +kernel
theorem subd5_1_71 : subd5_1 [-2, -1, -8] = true := by decide +kernel
theorem subd5_1_72 : subd5_1 [-2, -1, -7] = true := by decide +kernel
theorem subd5_1_73 : subd5_1 [-2, -1, -6] = true := by decide +kernel
theorem subd5_1_74 : subd5_1 [-2, -1, -5] = true := by decide +kernel
theorem subd5_1_75 : subd5_1 [-2, -1, -4] = true := by decide +kernel
theorem subd5_1_76 : subd5_1 [-2, -1, -3] = true := by decide +kernel
theorem subd5_1_77 : subd5_1 [-2, -1, -2] = true := by decide +kernel
theorem subd5_1_78 : subd5_1 [-2, -1, -1] = true := by decide +kernel
theorem subd5_1_79 : subd5_1 [-2, -1, 0] = true := by decide +kernel
theorem subd5_1_80 : subd5_1 [-2, -1, 1] = true := by decide +kernel
theorem subd5_1_81 : subd5_1 [-2, -1, 2] = true := by decide +kernel
theorem subd5_1_82 : subd5_1 [-2, -1, 3] = true := by decide +kernel
theorem subd5_1_83 : subd5_1 [-2, -1, 4] = true := by decide +kernel
theorem subd5_1_84 : subd5_1 [-2, -1, 5] = true := by decide +kernel
theorem subd5_1_85 : subd5_1 [-2, -1, 6] = true := by decide +kernel
theorem subd5_1_86 : subd5_1 [-2, 0, -8] = true := by decide +kernel
theorem subd5_1_87 : subd5_1 [-2, 0, -7] = true := by decide +kernel
theorem subd5_1_88 : subd5_1 [-2, 0, -6] = true := by decide +kernel
theorem subd5_1_89 : subd5_1 [-2, 0, -5] = true := by decide +kernel
theorem subd5_1_90 : subd5_1 [-2, 0, -4] = true := by decide +kernel
theorem subd5_1_91 : subd5_1 [-2, 0, -3] = true := by decide +kernel
theorem subd5_1_92 : subd5_1 [-2, 0, -2] = true := by decide +kernel
theorem subd5_1_93 : subd5_1 [-2, 0, -1] = true := by decide +kernel
theorem subd5_1_94 : subd5_1 [-2, 0, 0] = true := by decide +kernel
theorem subd5_1_95 : subd5_1 [-2, 0, 1] = true := by decide +kernel
theorem sbd5_1_2 : ∀ q ∈ blkd5_1_2, subd5_1 q = true := by
  unfold blkd5_1_2
  exact List.forall_mem_cons.2 ⟨subd5_1_64, List.forall_mem_cons.2 ⟨subd5_1_65, List.forall_mem_cons.2 ⟨subd5_1_66, List.forall_mem_cons.2 ⟨subd5_1_67, List.forall_mem_cons.2 ⟨subd5_1_68, List.forall_mem_cons.2 ⟨subd5_1_69, List.forall_mem_cons.2 ⟨subd5_1_70, List.forall_mem_cons.2 ⟨subd5_1_71, List.forall_mem_cons.2 ⟨subd5_1_72, List.forall_mem_cons.2 ⟨subd5_1_73, List.forall_mem_cons.2 ⟨subd5_1_74, List.forall_mem_cons.2 ⟨subd5_1_75, List.forall_mem_cons.2 ⟨subd5_1_76, List.forall_mem_cons.2 ⟨subd5_1_77, List.forall_mem_cons.2 ⟨subd5_1_78, List.forall_mem_cons.2 ⟨subd5_1_79, List.forall_mem_cons.2 ⟨subd5_1_80, List.forall_mem_cons.2 ⟨subd5_1_81, List.forall_mem_cons.2 ⟨subd5_1_82, List.forall_mem_cons.2 ⟨subd5_1_83, List.forall_mem_cons.2 ⟨subd5_1_84, List.forall_mem_cons.2 ⟨subd5_1_85, List.forall_mem_cons.2 ⟨subd5_1_86, List.forall_mem_cons.2 ⟨subd5_1_87, List.forall_mem_cons.2 ⟨subd5_1_88, List.forall_mem_cons.2 ⟨subd5_1_89, List.forall_mem_cons.2 ⟨subd5_1_90, List.forall_mem_cons.2 ⟨subd5_1_91, List.forall_mem_cons.2 ⟨subd5_1_92, List.forall_mem_cons.2 ⟨subd5_1_93, List.forall_mem_cons.2 ⟨subd5_1_94, List.forall_mem_cons.2 ⟨subd5_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_96 : subd5_1 [-2, 0, 2] = true := by decide +kernel
theorem subd5_1_97 : subd5_1 [-2, 0, 3] = true := by decide +kernel
theorem subd5_1_98 : subd5_1 [-2, 0, 4] = true := by decide +kernel
theorem subd5_1_99 : subd5_1 [-2, 0, 5] = true := by decide +kernel
theorem subd5_1_100 : subd5_1 [-2, 1, -9] = true := by decide +kernel
theorem subd5_1_101 : subd5_1 [-2, 1, -8] = true := by decide +kernel
theorem subd5_1_102 : subd5_1 [-2, 1, -7] = true := by decide +kernel
theorem subd5_1_103 : subd5_1 [-2, 1, -6] = true := by decide +kernel
theorem subd5_1_104 : subd5_1 [-2, 1, -5] = true := by decide +kernel
theorem subd5_1_105 : subd5_1 [-2, 1, -4] = true := by decide +kernel
theorem subd5_1_106 : subd5_1 [-2, 1, -3] = true := by decide +kernel
theorem subd5_1_107 : subd5_1 [-2, 1, -2] = true := by decide +kernel
theorem subd5_1_108 : subd5_1 [-2, 1, -1] = true := by decide +kernel
theorem subd5_1_109 : subd5_1 [-2, 1, 0] = true := by decide +kernel
theorem subd5_1_110 : subd5_1 [-2, 1, 1] = true := by decide +kernel
theorem subd5_1_111 : subd5_1 [-2, 1, 2] = true := by decide +kernel
theorem subd5_1_112 : subd5_1 [-2, 1, 3] = true := by decide +kernel
theorem subd5_1_113 : subd5_1 [-2, 1, 4] = true := by decide +kernel
theorem subd5_1_114 : subd5_1 [-2, 1, 5] = true := by decide +kernel
theorem subd5_1_115 : subd5_1 [-2, 2, -9] = true := by decide +kernel
theorem subd5_1_116 : subd5_1 [-2, 2, -8] = true := by decide +kernel
theorem subd5_1_117 : subd5_1 [-2, 2, -7] = true := by decide +kernel
theorem subd5_1_118 : subd5_1 [-2, 2, -6] = true := by decide +kernel
theorem subd5_1_119 : subd5_1 [-2, 2, -5] = true := by decide +kernel
theorem subd5_1_120 : subd5_1 [-2, 2, -4] = true := by decide +kernel
theorem subd5_1_121 : subd5_1 [-2, 2, -3] = true := by decide +kernel
theorem subd5_1_122 : subd5_1 [-2, 2, -2] = true := by decide +kernel
theorem subd5_1_123 : subd5_1 [-2, 2, -1] = true := by decide +kernel
theorem subd5_1_124 : subd5_1 [-2, 2, 0] = true := by decide +kernel
theorem subd5_1_125 : subd5_1 [-2, 2, 1] = true := by decide +kernel
theorem subd5_1_126 : subd5_1 [-2, 2, 2] = true := by decide +kernel
theorem subd5_1_127 : subd5_1 [-2, 2, 3] = true := by decide +kernel
theorem sbd5_1_3 : ∀ q ∈ blkd5_1_3, subd5_1 q = true := by
  unfold blkd5_1_3
  exact List.forall_mem_cons.2 ⟨subd5_1_96, List.forall_mem_cons.2 ⟨subd5_1_97, List.forall_mem_cons.2 ⟨subd5_1_98, List.forall_mem_cons.2 ⟨subd5_1_99, List.forall_mem_cons.2 ⟨subd5_1_100, List.forall_mem_cons.2 ⟨subd5_1_101, List.forall_mem_cons.2 ⟨subd5_1_102, List.forall_mem_cons.2 ⟨subd5_1_103, List.forall_mem_cons.2 ⟨subd5_1_104, List.forall_mem_cons.2 ⟨subd5_1_105, List.forall_mem_cons.2 ⟨subd5_1_106, List.forall_mem_cons.2 ⟨subd5_1_107, List.forall_mem_cons.2 ⟨subd5_1_108, List.forall_mem_cons.2 ⟨subd5_1_109, List.forall_mem_cons.2 ⟨subd5_1_110, List.forall_mem_cons.2 ⟨subd5_1_111, List.forall_mem_cons.2 ⟨subd5_1_112, List.forall_mem_cons.2 ⟨subd5_1_113, List.forall_mem_cons.2 ⟨subd5_1_114, List.forall_mem_cons.2 ⟨subd5_1_115, List.forall_mem_cons.2 ⟨subd5_1_116, List.forall_mem_cons.2 ⟨subd5_1_117, List.forall_mem_cons.2 ⟨subd5_1_118, List.forall_mem_cons.2 ⟨subd5_1_119, List.forall_mem_cons.2 ⟨subd5_1_120, List.forall_mem_cons.2 ⟨subd5_1_121, List.forall_mem_cons.2 ⟨subd5_1_122, List.forall_mem_cons.2 ⟨subd5_1_123, List.forall_mem_cons.2 ⟨subd5_1_124, List.forall_mem_cons.2 ⟨subd5_1_125, List.forall_mem_cons.2 ⟨subd5_1_126, List.forall_mem_cons.2 ⟨subd5_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_128 : subd5_1 [-2, 2, 4] = true := by decide +kernel
theorem subd5_1_129 : subd5_1 [-2, 3] = true := by decide +kernel
theorem subd5_1_130 : subd5_1 [-2, 4] = true := by decide +kernel
theorem subd5_1_131 : subd5_1 [-2, 5] = true := by decide +kernel
theorem subd5_1_132 : subd5_1 [-1, -6] = true := by decide +kernel
theorem subd5_1_133 : subd5_1 [-1, -5] = true := by decide +kernel
theorem subd5_1_134 : subd5_1 [-1, -4] = true := by decide +kernel
theorem subd5_1_135 : subd5_1 [-1, -3, -6] = true := by decide +kernel
theorem subd5_1_136 : subd5_1 [-1, -3, -5] = true := by decide +kernel
theorem subd5_1_137 : subd5_1 [-1, -3, -4] = true := by decide +kernel
theorem subd5_1_138 : subd5_1 [-1, -3, -3] = true := by decide +kernel
theorem subd5_1_139 : subd5_1 [-1, -3, -2] = true := by decide +kernel
theorem subd5_1_140 : subd5_1 [-1, -3, -1] = true := by decide +kernel
theorem subd5_1_141 : subd5_1 [-1, -3, 0] = true := by decide +kernel
theorem subd5_1_142 : subd5_1 [-1, -3, 1] = true := by decide +kernel
theorem subd5_1_143 : subd5_1 [-1, -3, 2] = true := by decide +kernel
theorem subd5_1_144 : subd5_1 [-1, -3, 3] = true := by decide +kernel
theorem subd5_1_145 : subd5_1 [-1, -3, 4] = true := by decide +kernel
theorem subd5_1_146 : subd5_1 [-1, -3, 5] = true := by decide +kernel
theorem subd5_1_147 : subd5_1 [-1, -3, 6] = true := by decide +kernel
theorem subd5_1_148 : subd5_1 [-1, -3, 7] = true := by decide +kernel
theorem subd5_1_149 : subd5_1 [-1, -2, -7] = true := by decide +kernel
theorem subd5_1_150 : subd5_1 [-1, -2, -6] = true := by decide +kernel
theorem subd5_1_151 : subd5_1 [-1, -2, -5] = true := by decide +kernel
theorem subd5_1_152 : subd5_1 [-1, -2, -4] = true := by decide +kernel
theorem subd5_1_153 : subd5_1 [-1, -2, -3] = true := by decide +kernel
theorem subd5_1_154 : subd5_1 [-1, -2, -2] = true := by decide +kernel
theorem subd5_1_155 : subd5_1 [-1, -2, -1] = true := by decide +kernel
theorem subd5_1_156 : subd5_1 [-1, -2, 0] = true := by decide +kernel
theorem subd5_1_157 : subd5_1 [-1, -2, 1] = true := by decide +kernel
theorem subd5_1_158 : subd5_1 [-1, -2, 2] = true := by decide +kernel
theorem subd5_1_159 : subd5_1 [-1, -2, 3] = true := by decide +kernel
theorem sbd5_1_4 : ∀ q ∈ blkd5_1_4, subd5_1 q = true := by
  unfold blkd5_1_4
  exact List.forall_mem_cons.2 ⟨subd5_1_128, List.forall_mem_cons.2 ⟨subd5_1_129, List.forall_mem_cons.2 ⟨subd5_1_130, List.forall_mem_cons.2 ⟨subd5_1_131, List.forall_mem_cons.2 ⟨subd5_1_132, List.forall_mem_cons.2 ⟨subd5_1_133, List.forall_mem_cons.2 ⟨subd5_1_134, List.forall_mem_cons.2 ⟨subd5_1_135, List.forall_mem_cons.2 ⟨subd5_1_136, List.forall_mem_cons.2 ⟨subd5_1_137, List.forall_mem_cons.2 ⟨subd5_1_138, List.forall_mem_cons.2 ⟨subd5_1_139, List.forall_mem_cons.2 ⟨subd5_1_140, List.forall_mem_cons.2 ⟨subd5_1_141, List.forall_mem_cons.2 ⟨subd5_1_142, List.forall_mem_cons.2 ⟨subd5_1_143, List.forall_mem_cons.2 ⟨subd5_1_144, List.forall_mem_cons.2 ⟨subd5_1_145, List.forall_mem_cons.2 ⟨subd5_1_146, List.forall_mem_cons.2 ⟨subd5_1_147, List.forall_mem_cons.2 ⟨subd5_1_148, List.forall_mem_cons.2 ⟨subd5_1_149, List.forall_mem_cons.2 ⟨subd5_1_150, List.forall_mem_cons.2 ⟨subd5_1_151, List.forall_mem_cons.2 ⟨subd5_1_152, List.forall_mem_cons.2 ⟨subd5_1_153, List.forall_mem_cons.2 ⟨subd5_1_154, List.forall_mem_cons.2 ⟨subd5_1_155, List.forall_mem_cons.2 ⟨subd5_1_156, List.forall_mem_cons.2 ⟨subd5_1_157, List.forall_mem_cons.2 ⟨subd5_1_158, List.forall_mem_cons.2 ⟨subd5_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_160 : subd5_1 [-1, -2, 4] = true := by decide +kernel
theorem subd5_1_161 : subd5_1 [-1, -2, 5] = true := by decide +kernel
theorem subd5_1_162 : subd5_1 [-1, -2, 6] = true := by decide +kernel
theorem subd5_1_163 : subd5_1 [-1, -2, 7] = true := by decide +kernel
theorem subd5_1_164 : subd5_1 [-1, -1, -8] = true := by decide +kernel
theorem subd5_1_165 : subd5_1 [-1, -1, -7] = true := by decide +kernel
theorem subd5_1_166 : subd5_1 [-1, -1, -6] = true := by decide +kernel
theorem subd5_1_167 : subd5_1 [-1, -1, -5] = true := by decide +kernel
theorem subd5_1_168 : subd5_1 [-1, -1, -4] = true := by decide +kernel
theorem subd5_1_169 : subd5_1 [-1, -1, -3] = true := by decide +kernel
theorem subd5_1_170 : subd5_1 [-1, -1, -2] = true := by decide +kernel
theorem subd5_1_171 : subd5_1 [-1, -1, -1] = true := by decide +kernel
theorem subd5_1_172 : subd5_1 [-1, -1, 0] = true := by decide +kernel
theorem subd5_1_173 : subd5_1 [-1, -1, 1] = true := by decide +kernel
theorem subd5_1_174 : subd5_1 [-1, -1, 2] = true := by decide +kernel
theorem subd5_1_175 : subd5_1 [-1, -1, 3] = true := by decide +kernel
theorem subd5_1_176 : subd5_1 [-1, -1, 4] = true := by decide +kernel
theorem subd5_1_177 : subd5_1 [-1, -1, 5] = true := by decide +kernel
theorem subd5_1_178 : subd5_1 [-1, -1, 6] = true := by decide +kernel
theorem subd5_1_179 : subd5_1 [-1, -1, 7] = true := by decide +kernel
theorem subd5_1_180 : subd5_1 [-1, 0, -8] = true := by decide +kernel
theorem subd5_1_181 : subd5_1 [-1, 0, -7] = true := by decide +kernel
theorem subd5_1_182 : subd5_1 [-1, 0, -6] = true := by decide +kernel
theorem subd5_1_183 : subd5_1 [-1, 0, -5] = true := by decide +kernel
theorem subd5_1_184 : subd5_1 [-1, 0, -4] = true := by decide +kernel
theorem subd5_1_185 : subd5_1 [-1, 0, -3] = true := by decide +kernel
theorem subd5_1_186 : subd5_1 [-1, 0, -2] = true := by decide +kernel
theorem subd5_1_187 : subd5_1 [-1, 0, -1] = true := by decide +kernel
theorem subd5_1_188 : subd5_1 [-1, 0, 0] = true := by decide +kernel
theorem subd5_1_189 : subd5_1 [-1, 0, 1] = true := by decide +kernel
theorem subd5_1_190 : subd5_1 [-1, 0, 2] = true := by decide +kernel
theorem subd5_1_191 : subd5_1 [-1, 0, 3] = true := by decide +kernel
theorem sbd5_1_5 : ∀ q ∈ blkd5_1_5, subd5_1 q = true := by
  unfold blkd5_1_5
  exact List.forall_mem_cons.2 ⟨subd5_1_160, List.forall_mem_cons.2 ⟨subd5_1_161, List.forall_mem_cons.2 ⟨subd5_1_162, List.forall_mem_cons.2 ⟨subd5_1_163, List.forall_mem_cons.2 ⟨subd5_1_164, List.forall_mem_cons.2 ⟨subd5_1_165, List.forall_mem_cons.2 ⟨subd5_1_166, List.forall_mem_cons.2 ⟨subd5_1_167, List.forall_mem_cons.2 ⟨subd5_1_168, List.forall_mem_cons.2 ⟨subd5_1_169, List.forall_mem_cons.2 ⟨subd5_1_170, List.forall_mem_cons.2 ⟨subd5_1_171, List.forall_mem_cons.2 ⟨subd5_1_172, List.forall_mem_cons.2 ⟨subd5_1_173, List.forall_mem_cons.2 ⟨subd5_1_174, List.forall_mem_cons.2 ⟨subd5_1_175, List.forall_mem_cons.2 ⟨subd5_1_176, List.forall_mem_cons.2 ⟨subd5_1_177, List.forall_mem_cons.2 ⟨subd5_1_178, List.forall_mem_cons.2 ⟨subd5_1_179, List.forall_mem_cons.2 ⟨subd5_1_180, List.forall_mem_cons.2 ⟨subd5_1_181, List.forall_mem_cons.2 ⟨subd5_1_182, List.forall_mem_cons.2 ⟨subd5_1_183, List.forall_mem_cons.2 ⟨subd5_1_184, List.forall_mem_cons.2 ⟨subd5_1_185, List.forall_mem_cons.2 ⟨subd5_1_186, List.forall_mem_cons.2 ⟨subd5_1_187, List.forall_mem_cons.2 ⟨subd5_1_188, List.forall_mem_cons.2 ⟨subd5_1_189, List.forall_mem_cons.2 ⟨subd5_1_190, List.forall_mem_cons.2 ⟨subd5_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_192 : subd5_1 [-1, 0, 4] = true := by decide +kernel
theorem subd5_1_193 : subd5_1 [-1, 0, 5] = true := by decide +kernel
theorem subd5_1_194 : subd5_1 [-1, 0, 6] = true := by decide +kernel
theorem subd5_1_195 : subd5_1 [-1, 1, -9] = true := by decide +kernel
theorem subd5_1_196 : subd5_1 [-1, 1, -8] = true := by decide +kernel
theorem subd5_1_197 : subd5_1 [-1, 1, -7] = true := by decide +kernel
theorem subd5_1_198 : subd5_1 [-1, 1, -6] = true := by decide +kernel
theorem subd5_1_199 : subd5_1 [-1, 1, -5] = true := by decide +kernel
theorem subd5_1_200 : subd5_1 [-1, 1, -4] = true := by decide +kernel
theorem subd5_1_201 : subd5_1 [-1, 1, -3] = true := by decide +kernel
theorem subd5_1_202 : subd5_1 [-1, 1, -2] = true := by decide +kernel
theorem subd5_1_203 : subd5_1 [-1, 1, -1] = true := by decide +kernel
theorem subd5_1_204 : subd5_1 [-1, 1, 0] = true := by decide +kernel
theorem subd5_1_205 : subd5_1 [-1, 1, 1] = true := by decide +kernel
theorem subd5_1_206 : subd5_1 [-1, 1, 2] = true := by decide +kernel
theorem subd5_1_207 : subd5_1 [-1, 1, 3] = true := by decide +kernel
theorem subd5_1_208 : subd5_1 [-1, 1, 4] = true := by decide +kernel
theorem subd5_1_209 : subd5_1 [-1, 1, 5] = true := by decide +kernel
theorem subd5_1_210 : subd5_1 [-1, 1, 6] = true := by decide +kernel
theorem subd5_1_211 : subd5_1 [-1, 2, -9] = true := by decide +kernel
theorem subd5_1_212 : subd5_1 [-1, 2, -8] = true := by decide +kernel
theorem subd5_1_213 : subd5_1 [-1, 2, -7] = true := by decide +kernel
theorem subd5_1_214 : subd5_1 [-1, 2, -6] = true := by decide +kernel
theorem subd5_1_215 : subd5_1 [-1, 2, -5] = true := by decide +kernel
theorem subd5_1_216 : subd5_1 [-1, 2, -4] = true := by decide +kernel
theorem subd5_1_217 : subd5_1 [-1, 2, -3] = true := by decide +kernel
theorem subd5_1_218 : subd5_1 [-1, 2, -2] = true := by decide +kernel
theorem subd5_1_219 : subd5_1 [-1, 2, -1] = true := by decide +kernel
theorem subd5_1_220 : subd5_1 [-1, 2, 0] = true := by decide +kernel
theorem subd5_1_221 : subd5_1 [-1, 2, 1] = true := by decide +kernel
theorem subd5_1_222 : subd5_1 [-1, 2, 2] = true := by decide +kernel
theorem subd5_1_223 : subd5_1 [-1, 2, 3] = true := by decide +kernel
theorem sbd5_1_6 : ∀ q ∈ blkd5_1_6, subd5_1 q = true := by
  unfold blkd5_1_6
  exact List.forall_mem_cons.2 ⟨subd5_1_192, List.forall_mem_cons.2 ⟨subd5_1_193, List.forall_mem_cons.2 ⟨subd5_1_194, List.forall_mem_cons.2 ⟨subd5_1_195, List.forall_mem_cons.2 ⟨subd5_1_196, List.forall_mem_cons.2 ⟨subd5_1_197, List.forall_mem_cons.2 ⟨subd5_1_198, List.forall_mem_cons.2 ⟨subd5_1_199, List.forall_mem_cons.2 ⟨subd5_1_200, List.forall_mem_cons.2 ⟨subd5_1_201, List.forall_mem_cons.2 ⟨subd5_1_202, List.forall_mem_cons.2 ⟨subd5_1_203, List.forall_mem_cons.2 ⟨subd5_1_204, List.forall_mem_cons.2 ⟨subd5_1_205, List.forall_mem_cons.2 ⟨subd5_1_206, List.forall_mem_cons.2 ⟨subd5_1_207, List.forall_mem_cons.2 ⟨subd5_1_208, List.forall_mem_cons.2 ⟨subd5_1_209, List.forall_mem_cons.2 ⟨subd5_1_210, List.forall_mem_cons.2 ⟨subd5_1_211, List.forall_mem_cons.2 ⟨subd5_1_212, List.forall_mem_cons.2 ⟨subd5_1_213, List.forall_mem_cons.2 ⟨subd5_1_214, List.forall_mem_cons.2 ⟨subd5_1_215, List.forall_mem_cons.2 ⟨subd5_1_216, List.forall_mem_cons.2 ⟨subd5_1_217, List.forall_mem_cons.2 ⟨subd5_1_218, List.forall_mem_cons.2 ⟨subd5_1_219, List.forall_mem_cons.2 ⟨subd5_1_220, List.forall_mem_cons.2 ⟨subd5_1_221, List.forall_mem_cons.2 ⟨subd5_1_222, List.forall_mem_cons.2 ⟨subd5_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_224 : subd5_1 [-1, 2, 4] = true := by decide +kernel
theorem subd5_1_225 : subd5_1 [-1, 2, 5] = true := by decide +kernel
theorem subd5_1_226 : subd5_1 [-1, 3, -8] = true := by decide +kernel
theorem subd5_1_227 : subd5_1 [-1, 3, -7] = true := by decide +kernel
theorem subd5_1_228 : subd5_1 [-1, 3, -6] = true := by decide +kernel
theorem subd5_1_229 : subd5_1 [-1, 3, -5] = true := by decide +kernel
theorem subd5_1_230 : subd5_1 [-1, 3, -4] = true := by decide +kernel
theorem subd5_1_231 : subd5_1 [-1, 3, -3] = true := by decide +kernel
theorem subd5_1_232 : subd5_1 [-1, 3, -2] = true := by decide +kernel
theorem subd5_1_233 : subd5_1 [-1, 3, -1] = true := by decide +kernel
theorem subd5_1_234 : subd5_1 [-1, 3, 0] = true := by decide +kernel
theorem subd5_1_235 : subd5_1 [-1, 3, 1] = true := by decide +kernel
theorem subd5_1_236 : subd5_1 [-1, 3, 2] = true := by decide +kernel
theorem subd5_1_237 : subd5_1 [-1, 3, 3] = true := by decide +kernel
theorem subd5_1_238 : subd5_1 [-1, 3, 4] = true := by decide +kernel
theorem subd5_1_239 : subd5_1 [-1, 4] = true := by decide +kernel
theorem subd5_1_240 : subd5_1 [-1, 5] = true := by decide +kernel
theorem subd5_1_241 : subd5_1 [0, -6] = true := by decide +kernel
theorem subd5_1_242 : subd5_1 [0, -5] = true := by decide +kernel
theorem subd5_1_243 : subd5_1 [0, -4] = true := by decide +kernel
theorem subd5_1_244 : subd5_1 [0, -3, -6] = true := by decide +kernel
theorem subd5_1_245 : subd5_1 [0, -3, -5] = true := by decide +kernel
theorem subd5_1_246 : subd5_1 [0, -3, -4] = true := by decide +kernel
theorem subd5_1_247 : subd5_1 [0, -3, -3] = true := by decide +kernel
theorem subd5_1_248 : subd5_1 [0, -3, -2] = true := by decide +kernel
theorem subd5_1_249 : subd5_1 [0, -3, -1] = true := by decide +kernel
theorem subd5_1_250 : subd5_1 [0, -3, 0] = true := by decide +kernel
theorem subd5_1_251 : subd5_1 [0, -3, 1] = true := by decide +kernel
theorem subd5_1_252 : subd5_1 [0, -3, 2] = true := by decide +kernel
theorem subd5_1_253 : subd5_1 [0, -3, 3] = true := by decide +kernel
theorem subd5_1_254 : subd5_1 [0, -3, 4] = true := by decide +kernel
theorem subd5_1_255 : subd5_1 [0, -3, 5] = true := by decide +kernel
theorem sbd5_1_7 : ∀ q ∈ blkd5_1_7, subd5_1 q = true := by
  unfold blkd5_1_7
  exact List.forall_mem_cons.2 ⟨subd5_1_224, List.forall_mem_cons.2 ⟨subd5_1_225, List.forall_mem_cons.2 ⟨subd5_1_226, List.forall_mem_cons.2 ⟨subd5_1_227, List.forall_mem_cons.2 ⟨subd5_1_228, List.forall_mem_cons.2 ⟨subd5_1_229, List.forall_mem_cons.2 ⟨subd5_1_230, List.forall_mem_cons.2 ⟨subd5_1_231, List.forall_mem_cons.2 ⟨subd5_1_232, List.forall_mem_cons.2 ⟨subd5_1_233, List.forall_mem_cons.2 ⟨subd5_1_234, List.forall_mem_cons.2 ⟨subd5_1_235, List.forall_mem_cons.2 ⟨subd5_1_236, List.forall_mem_cons.2 ⟨subd5_1_237, List.forall_mem_cons.2 ⟨subd5_1_238, List.forall_mem_cons.2 ⟨subd5_1_239, List.forall_mem_cons.2 ⟨subd5_1_240, List.forall_mem_cons.2 ⟨subd5_1_241, List.forall_mem_cons.2 ⟨subd5_1_242, List.forall_mem_cons.2 ⟨subd5_1_243, List.forall_mem_cons.2 ⟨subd5_1_244, List.forall_mem_cons.2 ⟨subd5_1_245, List.forall_mem_cons.2 ⟨subd5_1_246, List.forall_mem_cons.2 ⟨subd5_1_247, List.forall_mem_cons.2 ⟨subd5_1_248, List.forall_mem_cons.2 ⟨subd5_1_249, List.forall_mem_cons.2 ⟨subd5_1_250, List.forall_mem_cons.2 ⟨subd5_1_251, List.forall_mem_cons.2 ⟨subd5_1_252, List.forall_mem_cons.2 ⟨subd5_1_253, List.forall_mem_cons.2 ⟨subd5_1_254, List.forall_mem_cons.2 ⟨subd5_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_256 : subd5_1 [0, -3, 6] = true := by decide +kernel
theorem subd5_1_257 : subd5_1 [0, -3, 7] = true := by decide +kernel
theorem subd5_1_258 : subd5_1 [0, -2, -7] = true := by decide +kernel
theorem subd5_1_259 : subd5_1 [0, -2, -6] = true := by decide +kernel
theorem subd5_1_260 : subd5_1 [0, -2, -5] = true := by decide +kernel
theorem subd5_1_261 : subd5_1 [0, -2, -4] = true := by decide +kernel
theorem subd5_1_262 : subd5_1 [0, -2, -3] = true := by decide +kernel
theorem subd5_1_263 : subd5_1 [0, -2, -2] = true := by decide +kernel
theorem subd5_1_264 : subd5_1 [0, -2, -1] = true := by decide +kernel
theorem subd5_1_265 : subd5_1 [0, -2, 0] = true := by decide +kernel
theorem subd5_1_266 : subd5_1 [0, -2, 1] = true := by decide +kernel
theorem subd5_1_267 : subd5_1 [0, -2, 2] = true := by decide +kernel
theorem subd5_1_268 : subd5_1 [0, -2, 3] = true := by decide +kernel
theorem subd5_1_269 : subd5_1 [0, -2, 4] = true := by decide +kernel
theorem subd5_1_270 : subd5_1 [0, -2, 5] = true := by decide +kernel
theorem subd5_1_271 : subd5_1 [0, -2, 6] = true := by decide +kernel
theorem subd5_1_272 : subd5_1 [0, -2, 7] = true := by decide +kernel
theorem subd5_1_273 : subd5_1 [0, -1, -7] = true := by decide +kernel
theorem subd5_1_274 : subd5_1 [0, -1, -6] = true := by decide +kernel
theorem subd5_1_275 : subd5_1 [0, -1, -5] = true := by decide +kernel
theorem subd5_1_276 : subd5_1 [0, -1, -4] = true := by decide +kernel
theorem subd5_1_277 : subd5_1 [0, -1, -3] = true := by decide +kernel
theorem subd5_1_278 : subd5_1 [0, -1, -2] = true := by decide +kernel
theorem subd5_1_279 : subd5_1 [0, -1, -1] = true := by decide +kernel
theorem subd5_1_280 : subd5_1 [0, -1, 0] = true := by decide +kernel
theorem subd5_1_281 : subd5_1 [0, -1, 1] = true := by decide +kernel
theorem subd5_1_282 : subd5_1 [0, -1, 2] = true := by decide +kernel
theorem subd5_1_283 : subd5_1 [0, -1, 3] = true := by decide +kernel
theorem subd5_1_284 : subd5_1 [0, -1, 4] = true := by decide +kernel
theorem subd5_1_285 : subd5_1 [0, -1, 5] = true := by decide +kernel
theorem subd5_1_286 : subd5_1 [0, -1, 6] = true := by decide +kernel
theorem subd5_1_287 : subd5_1 [0, -1, 7] = true := by decide +kernel
theorem sbd5_1_8 : ∀ q ∈ blkd5_1_8, subd5_1 q = true := by
  unfold blkd5_1_8
  exact List.forall_mem_cons.2 ⟨subd5_1_256, List.forall_mem_cons.2 ⟨subd5_1_257, List.forall_mem_cons.2 ⟨subd5_1_258, List.forall_mem_cons.2 ⟨subd5_1_259, List.forall_mem_cons.2 ⟨subd5_1_260, List.forall_mem_cons.2 ⟨subd5_1_261, List.forall_mem_cons.2 ⟨subd5_1_262, List.forall_mem_cons.2 ⟨subd5_1_263, List.forall_mem_cons.2 ⟨subd5_1_264, List.forall_mem_cons.2 ⟨subd5_1_265, List.forall_mem_cons.2 ⟨subd5_1_266, List.forall_mem_cons.2 ⟨subd5_1_267, List.forall_mem_cons.2 ⟨subd5_1_268, List.forall_mem_cons.2 ⟨subd5_1_269, List.forall_mem_cons.2 ⟨subd5_1_270, List.forall_mem_cons.2 ⟨subd5_1_271, List.forall_mem_cons.2 ⟨subd5_1_272, List.forall_mem_cons.2 ⟨subd5_1_273, List.forall_mem_cons.2 ⟨subd5_1_274, List.forall_mem_cons.2 ⟨subd5_1_275, List.forall_mem_cons.2 ⟨subd5_1_276, List.forall_mem_cons.2 ⟨subd5_1_277, List.forall_mem_cons.2 ⟨subd5_1_278, List.forall_mem_cons.2 ⟨subd5_1_279, List.forall_mem_cons.2 ⟨subd5_1_280, List.forall_mem_cons.2 ⟨subd5_1_281, List.forall_mem_cons.2 ⟨subd5_1_282, List.forall_mem_cons.2 ⟨subd5_1_283, List.forall_mem_cons.2 ⟨subd5_1_284, List.forall_mem_cons.2 ⟨subd5_1_285, List.forall_mem_cons.2 ⟨subd5_1_286, List.forall_mem_cons.2 ⟨subd5_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_288 : subd5_1 [0, 0, -8] = true := by decide +kernel
theorem subd5_1_289 : subd5_1 [0, 0, -7] = true := by decide +kernel
theorem subd5_1_290 : subd5_1 [0, 0, -6] = true := by decide +kernel
theorem subd5_1_291 : subd5_1 [0, 0, -5] = true := by decide +kernel
theorem subd5_1_292 : subd5_1 [0, 0, -4] = true := by decide +kernel
theorem subd5_1_293 : subd5_1 [0, 0, -3] = true := by decide +kernel
theorem subd5_1_294 : subd5_1 [0, 0, -2] = true := by decide +kernel
theorem subd5_1_295 : subd5_1 [0, 0, -1] = true := by decide +kernel
theorem subd5_1_296 : subd5_1 [0, 0, 0] = true := by decide +kernel
theorem subd5_1_297 : subd5_1 [0, 0, 1] = true := by decide +kernel
theorem subd5_1_298 : subd5_1 [0, 0, 2] = true := by decide +kernel
theorem subd5_1_299 : subd5_1 [0, 0, 3] = true := by decide +kernel
theorem subd5_1_300 : subd5_1 [0, 0, 4] = true := by decide +kernel
theorem subd5_1_301 : subd5_1 [0, 0, 5] = true := by decide +kernel
theorem subd5_1_302 : subd5_1 [0, 0, 6] = true := by decide +kernel
theorem subd5_1_303 : subd5_1 [0, 0, 7] = true := by decide +kernel
theorem subd5_1_304 : subd5_1 [0, 1, -8] = true := by decide +kernel
theorem subd5_1_305 : subd5_1 [0, 1, -7] = true := by decide +kernel
theorem subd5_1_306 : subd5_1 [0, 1, -6] = true := by decide +kernel
theorem subd5_1_307 : subd5_1 [0, 1, -5] = true := by decide +kernel
theorem subd5_1_308 : subd5_1 [0, 1, -4] = true := by decide +kernel
theorem subd5_1_309 : subd5_1 [0, 1, -3] = true := by decide +kernel
theorem subd5_1_310 : subd5_1 [0, 1, -2] = true := by decide +kernel
theorem subd5_1_311 : subd5_1 [0, 1, -1] = true := by decide +kernel
theorem subd5_1_312 : subd5_1 [0, 1, 0] = true := by decide +kernel
theorem subd5_1_313 : subd5_1 [0, 1, 1] = true := by decide +kernel
theorem subd5_1_314 : subd5_1 [0, 1, 2] = true := by decide +kernel
theorem subd5_1_315 : subd5_1 [0, 1, 3] = true := by decide +kernel
theorem subd5_1_316 : subd5_1 [0, 1, 4] = true := by decide +kernel
theorem subd5_1_317 : subd5_1 [0, 1, 5] = true := by decide +kernel
theorem subd5_1_318 : subd5_1 [0, 1, 6] = true := by decide +kernel
theorem subd5_1_319 : subd5_1 [0, 2, -8] = true := by decide +kernel
theorem sbd5_1_9 : ∀ q ∈ blkd5_1_9, subd5_1 q = true := by
  unfold blkd5_1_9
  exact List.forall_mem_cons.2 ⟨subd5_1_288, List.forall_mem_cons.2 ⟨subd5_1_289, List.forall_mem_cons.2 ⟨subd5_1_290, List.forall_mem_cons.2 ⟨subd5_1_291, List.forall_mem_cons.2 ⟨subd5_1_292, List.forall_mem_cons.2 ⟨subd5_1_293, List.forall_mem_cons.2 ⟨subd5_1_294, List.forall_mem_cons.2 ⟨subd5_1_295, List.forall_mem_cons.2 ⟨subd5_1_296, List.forall_mem_cons.2 ⟨subd5_1_297, List.forall_mem_cons.2 ⟨subd5_1_298, List.forall_mem_cons.2 ⟨subd5_1_299, List.forall_mem_cons.2 ⟨subd5_1_300, List.forall_mem_cons.2 ⟨subd5_1_301, List.forall_mem_cons.2 ⟨subd5_1_302, List.forall_mem_cons.2 ⟨subd5_1_303, List.forall_mem_cons.2 ⟨subd5_1_304, List.forall_mem_cons.2 ⟨subd5_1_305, List.forall_mem_cons.2 ⟨subd5_1_306, List.forall_mem_cons.2 ⟨subd5_1_307, List.forall_mem_cons.2 ⟨subd5_1_308, List.forall_mem_cons.2 ⟨subd5_1_309, List.forall_mem_cons.2 ⟨subd5_1_310, List.forall_mem_cons.2 ⟨subd5_1_311, List.forall_mem_cons.2 ⟨subd5_1_312, List.forall_mem_cons.2 ⟨subd5_1_313, List.forall_mem_cons.2 ⟨subd5_1_314, List.forall_mem_cons.2 ⟨subd5_1_315, List.forall_mem_cons.2 ⟨subd5_1_316, List.forall_mem_cons.2 ⟨subd5_1_317, List.forall_mem_cons.2 ⟨subd5_1_318, List.forall_mem_cons.2 ⟨subd5_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_320 : subd5_1 [0, 2, -7] = true := by decide +kernel
theorem subd5_1_321 : subd5_1 [0, 2, -6] = true := by decide +kernel
theorem subd5_1_322 : subd5_1 [0, 2, -5] = true := by decide +kernel
theorem subd5_1_323 : subd5_1 [0, 2, -4] = true := by decide +kernel
theorem subd5_1_324 : subd5_1 [0, 2, -3] = true := by decide +kernel
theorem subd5_1_325 : subd5_1 [0, 2, -2] = true := by decide +kernel
theorem subd5_1_326 : subd5_1 [0, 2, -1] = true := by decide +kernel
theorem subd5_1_327 : subd5_1 [0, 2, 0] = true := by decide +kernel
theorem subd5_1_328 : subd5_1 [0, 2, 1] = true := by decide +kernel
theorem subd5_1_329 : subd5_1 [0, 2, 2] = true := by decide +kernel
theorem subd5_1_330 : subd5_1 [0, 2, 3] = true := by decide +kernel
theorem subd5_1_331 : subd5_1 [0, 2, 4] = true := by decide +kernel
theorem subd5_1_332 : subd5_1 [0, 2, 5] = true := by decide +kernel
theorem subd5_1_333 : subd5_1 [0, 2, 6] = true := by decide +kernel
theorem subd5_1_334 : subd5_1 [0, 3, -8] = true := by decide +kernel
theorem subd5_1_335 : subd5_1 [0, 3, -7] = true := by decide +kernel
theorem subd5_1_336 : subd5_1 [0, 3, -6] = true := by decide +kernel
theorem subd5_1_337 : subd5_1 [0, 3, -5] = true := by decide +kernel
theorem subd5_1_338 : subd5_1 [0, 3, -4] = true := by decide +kernel
theorem subd5_1_339 : subd5_1 [0, 3, -3] = true := by decide +kernel
theorem subd5_1_340 : subd5_1 [0, 3, -2] = true := by decide +kernel
theorem subd5_1_341 : subd5_1 [0, 3, -1] = true := by decide +kernel
theorem subd5_1_342 : subd5_1 [0, 3, 0] = true := by decide +kernel
theorem subd5_1_343 : subd5_1 [0, 3, 1] = true := by decide +kernel
theorem subd5_1_344 : subd5_1 [0, 3, 2] = true := by decide +kernel
theorem subd5_1_345 : subd5_1 [0, 3, 3] = true := by decide +kernel
theorem subd5_1_346 : subd5_1 [0, 3, 4] = true := by decide +kernel
theorem subd5_1_347 : subd5_1 [0, 3, 5] = true := by decide +kernel
theorem subd5_1_348 : subd5_1 [0, 4] = true := by decide +kernel
theorem subd5_1_349 : subd5_1 [0, 5] = true := by decide +kernel
theorem subd5_1_350 : subd5_1 [1, -6] = true := by decide +kernel
theorem subd5_1_351 : subd5_1 [1, -5] = true := by decide +kernel
theorem sbd5_1_10 : ∀ q ∈ blkd5_1_10, subd5_1 q = true := by
  unfold blkd5_1_10
  exact List.forall_mem_cons.2 ⟨subd5_1_320, List.forall_mem_cons.2 ⟨subd5_1_321, List.forall_mem_cons.2 ⟨subd5_1_322, List.forall_mem_cons.2 ⟨subd5_1_323, List.forall_mem_cons.2 ⟨subd5_1_324, List.forall_mem_cons.2 ⟨subd5_1_325, List.forall_mem_cons.2 ⟨subd5_1_326, List.forall_mem_cons.2 ⟨subd5_1_327, List.forall_mem_cons.2 ⟨subd5_1_328, List.forall_mem_cons.2 ⟨subd5_1_329, List.forall_mem_cons.2 ⟨subd5_1_330, List.forall_mem_cons.2 ⟨subd5_1_331, List.forall_mem_cons.2 ⟨subd5_1_332, List.forall_mem_cons.2 ⟨subd5_1_333, List.forall_mem_cons.2 ⟨subd5_1_334, List.forall_mem_cons.2 ⟨subd5_1_335, List.forall_mem_cons.2 ⟨subd5_1_336, List.forall_mem_cons.2 ⟨subd5_1_337, List.forall_mem_cons.2 ⟨subd5_1_338, List.forall_mem_cons.2 ⟨subd5_1_339, List.forall_mem_cons.2 ⟨subd5_1_340, List.forall_mem_cons.2 ⟨subd5_1_341, List.forall_mem_cons.2 ⟨subd5_1_342, List.forall_mem_cons.2 ⟨subd5_1_343, List.forall_mem_cons.2 ⟨subd5_1_344, List.forall_mem_cons.2 ⟨subd5_1_345, List.forall_mem_cons.2 ⟨subd5_1_346, List.forall_mem_cons.2 ⟨subd5_1_347, List.forall_mem_cons.2 ⟨subd5_1_348, List.forall_mem_cons.2 ⟨subd5_1_349, List.forall_mem_cons.2 ⟨subd5_1_350, List.forall_mem_cons.2 ⟨subd5_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_352 : subd5_1 [1, -4] = true := by decide +kernel
theorem subd5_1_353 : subd5_1 [1, -3, -5] = true := by decide +kernel
theorem subd5_1_354 : subd5_1 [1, -3, -4] = true := by decide +kernel
theorem subd5_1_355 : subd5_1 [1, -3, -3] = true := by decide +kernel
theorem subd5_1_356 : subd5_1 [1, -3, -2] = true := by decide +kernel
theorem subd5_1_357 : subd5_1 [1, -3, -1] = true := by decide +kernel
theorem subd5_1_358 : subd5_1 [1, -3, 0] = true := by decide +kernel
theorem subd5_1_359 : subd5_1 [1, -3, 1] = true := by decide +kernel
theorem subd5_1_360 : subd5_1 [1, -3, 2] = true := by decide +kernel
theorem subd5_1_361 : subd5_1 [1, -3, 3] = true := by decide +kernel
theorem subd5_1_362 : subd5_1 [1, -3, 4] = true := by decide +kernel
theorem subd5_1_363 : subd5_1 [1, -3, 5] = true := by decide +kernel
theorem subd5_1_364 : subd5_1 [1, -3, 6] = true := by decide +kernel
theorem subd5_1_365 : subd5_1 [1, -3, 7] = true := by decide +kernel
theorem subd5_1_366 : subd5_1 [1, -2, -6] = true := by decide +kernel
theorem subd5_1_367 : subd5_1 [1, -2, -5] = true := by decide +kernel
theorem subd5_1_368 : subd5_1 [1, -2, -4] = true := by decide +kernel
theorem subd5_1_369 : subd5_1 [1, -2, -3] = true := by decide +kernel
theorem subd5_1_370 : subd5_1 [1, -2, -2] = true := by decide +kernel
theorem subd5_1_371 : subd5_1 [1, -2, -1] = true := by decide +kernel
theorem subd5_1_372 : subd5_1 [1, -2, 0] = true := by decide +kernel
theorem subd5_1_373 : subd5_1 [1, -2, 1] = true := by decide +kernel
theorem subd5_1_374 : subd5_1 [1, -2, 2] = true := by decide +kernel
theorem subd5_1_375 : subd5_1 [1, -2, 3] = true := by decide +kernel
theorem subd5_1_376 : subd5_1 [1, -2, 4] = true := by decide +kernel
theorem subd5_1_377 : subd5_1 [1, -2, 5] = true := by decide +kernel
theorem subd5_1_378 : subd5_1 [1, -2, 6] = true := by decide +kernel
theorem subd5_1_379 : subd5_1 [1, -2, 7] = true := by decide +kernel
theorem subd5_1_380 : subd5_1 [1, -2, 8] = true := by decide +kernel
theorem subd5_1_381 : subd5_1 [1, -1, -7] = true := by decide +kernel
theorem subd5_1_382 : subd5_1 [1, -1, -6] = true := by decide +kernel
theorem subd5_1_383 : subd5_1 [1, -1, -5] = true := by decide +kernel
theorem sbd5_1_11 : ∀ q ∈ blkd5_1_11, subd5_1 q = true := by
  unfold blkd5_1_11
  exact List.forall_mem_cons.2 ⟨subd5_1_352, List.forall_mem_cons.2 ⟨subd5_1_353, List.forall_mem_cons.2 ⟨subd5_1_354, List.forall_mem_cons.2 ⟨subd5_1_355, List.forall_mem_cons.2 ⟨subd5_1_356, List.forall_mem_cons.2 ⟨subd5_1_357, List.forall_mem_cons.2 ⟨subd5_1_358, List.forall_mem_cons.2 ⟨subd5_1_359, List.forall_mem_cons.2 ⟨subd5_1_360, List.forall_mem_cons.2 ⟨subd5_1_361, List.forall_mem_cons.2 ⟨subd5_1_362, List.forall_mem_cons.2 ⟨subd5_1_363, List.forall_mem_cons.2 ⟨subd5_1_364, List.forall_mem_cons.2 ⟨subd5_1_365, List.forall_mem_cons.2 ⟨subd5_1_366, List.forall_mem_cons.2 ⟨subd5_1_367, List.forall_mem_cons.2 ⟨subd5_1_368, List.forall_mem_cons.2 ⟨subd5_1_369, List.forall_mem_cons.2 ⟨subd5_1_370, List.forall_mem_cons.2 ⟨subd5_1_371, List.forall_mem_cons.2 ⟨subd5_1_372, List.forall_mem_cons.2 ⟨subd5_1_373, List.forall_mem_cons.2 ⟨subd5_1_374, List.forall_mem_cons.2 ⟨subd5_1_375, List.forall_mem_cons.2 ⟨subd5_1_376, List.forall_mem_cons.2 ⟨subd5_1_377, List.forall_mem_cons.2 ⟨subd5_1_378, List.forall_mem_cons.2 ⟨subd5_1_379, List.forall_mem_cons.2 ⟨subd5_1_380, List.forall_mem_cons.2 ⟨subd5_1_381, List.forall_mem_cons.2 ⟨subd5_1_382, List.forall_mem_cons.2 ⟨subd5_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_384 : subd5_1 [1, -1, -4] = true := by decide +kernel
theorem subd5_1_385 : subd5_1 [1, -1, -3] = true := by decide +kernel
theorem subd5_1_386 : subd5_1 [1, -1, -2] = true := by decide +kernel
theorem subd5_1_387 : subd5_1 [1, -1, -1] = true := by decide +kernel
theorem subd5_1_388 : subd5_1 [1, -1, 0] = true := by decide +kernel
theorem subd5_1_389 : subd5_1 [1, -1, 1] = true := by decide +kernel
theorem subd5_1_390 : subd5_1 [1, -1, 2] = true := by decide +kernel
theorem subd5_1_391 : subd5_1 [1, -1, 3] = true := by decide +kernel
theorem subd5_1_392 : subd5_1 [1, -1, 4] = true := by decide +kernel
theorem subd5_1_393 : subd5_1 [1, -1, 5] = true := by decide +kernel
theorem subd5_1_394 : subd5_1 [1, -1, 6] = true := by decide +kernel
theorem subd5_1_395 : subd5_1 [1, -1, 7] = true := by decide +kernel
theorem subd5_1_396 : subd5_1 [1, -1, 8] = true := by decide +kernel
theorem subd5_1_397 : subd5_1 [1, 0, -7] = true := by decide +kernel
theorem subd5_1_398 : subd5_1 [1, 0, -6] = true := by decide +kernel
theorem subd5_1_399 : subd5_1 [1, 0, -5] = true := by decide +kernel
theorem subd5_1_400 : subd5_1 [1, 0, -4] = true := by decide +kernel
theorem subd5_1_401 : subd5_1 [1, 0, -3] = true := by decide +kernel
theorem subd5_1_402 : subd5_1 [1, 0, -2] = true := by decide +kernel
theorem subd5_1_403 : subd5_1 [1, 0, -1] = true := by decide +kernel
theorem subd5_1_404 : subd5_1 [1, 0, 0] = true := by decide +kernel
theorem subd5_1_405 : subd5_1 [1, 0, 1] = true := by decide +kernel
theorem subd5_1_406 : subd5_1 [1, 0, 2] = true := by decide +kernel
theorem subd5_1_407 : subd5_1 [1, 0, 3] = true := by decide +kernel
theorem subd5_1_408 : subd5_1 [1, 0, 4] = true := by decide +kernel
theorem subd5_1_409 : subd5_1 [1, 0, 5] = true := by decide +kernel
theorem subd5_1_410 : subd5_1 [1, 0, 6] = true := by decide +kernel
theorem subd5_1_411 : subd5_1 [1, 0, 7] = true := by decide +kernel
theorem subd5_1_412 : subd5_1 [1, 1, -8] = true := by decide +kernel
theorem subd5_1_413 : subd5_1 [1, 1, -7] = true := by decide +kernel
theorem subd5_1_414 : subd5_1 [1, 1, -6] = true := by decide +kernel
theorem subd5_1_415 : subd5_1 [1, 1, -5] = true := by decide +kernel
theorem sbd5_1_12 : ∀ q ∈ blkd5_1_12, subd5_1 q = true := by
  unfold blkd5_1_12
  exact List.forall_mem_cons.2 ⟨subd5_1_384, List.forall_mem_cons.2 ⟨subd5_1_385, List.forall_mem_cons.2 ⟨subd5_1_386, List.forall_mem_cons.2 ⟨subd5_1_387, List.forall_mem_cons.2 ⟨subd5_1_388, List.forall_mem_cons.2 ⟨subd5_1_389, List.forall_mem_cons.2 ⟨subd5_1_390, List.forall_mem_cons.2 ⟨subd5_1_391, List.forall_mem_cons.2 ⟨subd5_1_392, List.forall_mem_cons.2 ⟨subd5_1_393, List.forall_mem_cons.2 ⟨subd5_1_394, List.forall_mem_cons.2 ⟨subd5_1_395, List.forall_mem_cons.2 ⟨subd5_1_396, List.forall_mem_cons.2 ⟨subd5_1_397, List.forall_mem_cons.2 ⟨subd5_1_398, List.forall_mem_cons.2 ⟨subd5_1_399, List.forall_mem_cons.2 ⟨subd5_1_400, List.forall_mem_cons.2 ⟨subd5_1_401, List.forall_mem_cons.2 ⟨subd5_1_402, List.forall_mem_cons.2 ⟨subd5_1_403, List.forall_mem_cons.2 ⟨subd5_1_404, List.forall_mem_cons.2 ⟨subd5_1_405, List.forall_mem_cons.2 ⟨subd5_1_406, List.forall_mem_cons.2 ⟨subd5_1_407, List.forall_mem_cons.2 ⟨subd5_1_408, List.forall_mem_cons.2 ⟨subd5_1_409, List.forall_mem_cons.2 ⟨subd5_1_410, List.forall_mem_cons.2 ⟨subd5_1_411, List.forall_mem_cons.2 ⟨subd5_1_412, List.forall_mem_cons.2 ⟨subd5_1_413, List.forall_mem_cons.2 ⟨subd5_1_414, List.forall_mem_cons.2 ⟨subd5_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_416 : subd5_1 [1, 1, -4] = true := by decide +kernel
theorem subd5_1_417 : subd5_1 [1, 1, -3] = true := by decide +kernel
theorem subd5_1_418 : subd5_1 [1, 1, -2] = true := by decide +kernel
theorem subd5_1_419 : subd5_1 [1, 1, -1] = true := by decide +kernel
theorem subd5_1_420 : subd5_1 [1, 1, 0] = true := by decide +kernel
theorem subd5_1_421 : subd5_1 [1, 1, 1] = true := by decide +kernel
theorem subd5_1_422 : subd5_1 [1, 1, 2] = true := by decide +kernel
theorem subd5_1_423 : subd5_1 [1, 1, 3] = true := by decide +kernel
theorem subd5_1_424 : subd5_1 [1, 1, 4] = true := by decide +kernel
theorem subd5_1_425 : subd5_1 [1, 1, 5] = true := by decide +kernel
theorem subd5_1_426 : subd5_1 [1, 1, 6] = true := by decide +kernel
theorem subd5_1_427 : subd5_1 [1, 1, 7] = true := by decide +kernel
theorem subd5_1_428 : subd5_1 [1, 2, -8] = true := by decide +kernel
theorem subd5_1_429 : subd5_1 [1, 2, -7] = true := by decide +kernel
theorem subd5_1_430 : subd5_1 [1, 2, -6] = true := by decide +kernel
theorem subd5_1_431 : subd5_1 [1, 2, -5] = true := by decide +kernel
theorem subd5_1_432 : subd5_1 [1, 2, -4] = true := by decide +kernel
theorem subd5_1_433 : subd5_1 [1, 2, -3] = true := by decide +kernel
theorem subd5_1_434 : subd5_1 [1, 2, -2] = true := by decide +kernel
theorem subd5_1_435 : subd5_1 [1, 2, -1] = true := by decide +kernel
theorem subd5_1_436 : subd5_1 [1, 2, 0] = true := by decide +kernel
theorem subd5_1_437 : subd5_1 [1, 2, 1] = true := by decide +kernel
theorem subd5_1_438 : subd5_1 [1, 2, 2] = true := by decide +kernel
theorem subd5_1_439 : subd5_1 [1, 2, 3] = true := by decide +kernel
theorem subd5_1_440 : subd5_1 [1, 2, 4] = true := by decide +kernel
theorem subd5_1_441 : subd5_1 [1, 2, 5] = true := by decide +kernel
theorem subd5_1_442 : subd5_1 [1, 2, 6] = true := by decide +kernel
theorem subd5_1_443 : subd5_1 [1, 3, -8] = true := by decide +kernel
theorem subd5_1_444 : subd5_1 [1, 3, -7] = true := by decide +kernel
theorem subd5_1_445 : subd5_1 [1, 3, -6] = true := by decide +kernel
theorem subd5_1_446 : subd5_1 [1, 3, -5] = true := by decide +kernel
theorem subd5_1_447 : subd5_1 [1, 3, -4] = true := by decide +kernel
theorem sbd5_1_13 : ∀ q ∈ blkd5_1_13, subd5_1 q = true := by
  unfold blkd5_1_13
  exact List.forall_mem_cons.2 ⟨subd5_1_416, List.forall_mem_cons.2 ⟨subd5_1_417, List.forall_mem_cons.2 ⟨subd5_1_418, List.forall_mem_cons.2 ⟨subd5_1_419, List.forall_mem_cons.2 ⟨subd5_1_420, List.forall_mem_cons.2 ⟨subd5_1_421, List.forall_mem_cons.2 ⟨subd5_1_422, List.forall_mem_cons.2 ⟨subd5_1_423, List.forall_mem_cons.2 ⟨subd5_1_424, List.forall_mem_cons.2 ⟨subd5_1_425, List.forall_mem_cons.2 ⟨subd5_1_426, List.forall_mem_cons.2 ⟨subd5_1_427, List.forall_mem_cons.2 ⟨subd5_1_428, List.forall_mem_cons.2 ⟨subd5_1_429, List.forall_mem_cons.2 ⟨subd5_1_430, List.forall_mem_cons.2 ⟨subd5_1_431, List.forall_mem_cons.2 ⟨subd5_1_432, List.forall_mem_cons.2 ⟨subd5_1_433, List.forall_mem_cons.2 ⟨subd5_1_434, List.forall_mem_cons.2 ⟨subd5_1_435, List.forall_mem_cons.2 ⟨subd5_1_436, List.forall_mem_cons.2 ⟨subd5_1_437, List.forall_mem_cons.2 ⟨subd5_1_438, List.forall_mem_cons.2 ⟨subd5_1_439, List.forall_mem_cons.2 ⟨subd5_1_440, List.forall_mem_cons.2 ⟨subd5_1_441, List.forall_mem_cons.2 ⟨subd5_1_442, List.forall_mem_cons.2 ⟨subd5_1_443, List.forall_mem_cons.2 ⟨subd5_1_444, List.forall_mem_cons.2 ⟨subd5_1_445, List.forall_mem_cons.2 ⟨subd5_1_446, List.forall_mem_cons.2 ⟨subd5_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_448 : subd5_1 [1, 3, -3] = true := by decide +kernel
theorem subd5_1_449 : subd5_1 [1, 3, -2] = true := by decide +kernel
theorem subd5_1_450 : subd5_1 [1, 3, -1] = true := by decide +kernel
theorem subd5_1_451 : subd5_1 [1, 3, 0] = true := by decide +kernel
theorem subd5_1_452 : subd5_1 [1, 3, 1] = true := by decide +kernel
theorem subd5_1_453 : subd5_1 [1, 3, 2] = true := by decide +kernel
theorem subd5_1_454 : subd5_1 [1, 3, 3] = true := by decide +kernel
theorem subd5_1_455 : subd5_1 [1, 3, 4] = true := by decide +kernel
theorem subd5_1_456 : subd5_1 [1, 3, 5] = true := by decide +kernel
theorem subd5_1_457 : subd5_1 [1, 4] = true := by decide +kernel
theorem subd5_1_458 : subd5_1 [1, 5] = true := by decide +kernel
theorem subd5_1_459 : subd5_1 [2, -6] = true := by decide +kernel
theorem subd5_1_460 : subd5_1 [2, -5] = true := by decide +kernel
theorem subd5_1_461 : subd5_1 [2, -4] = true := by decide +kernel
theorem subd5_1_462 : subd5_1 [2, -3] = true := by decide +kernel
theorem subd5_1_463 : subd5_1 [2, -2, -5] = true := by decide +kernel
theorem subd5_1_464 : subd5_1 [2, -2, -4] = true := by decide +kernel
theorem subd5_1_465 : subd5_1 [2, -2, -3] = true := by decide +kernel
theorem subd5_1_466 : subd5_1 [2, -2, -2] = true := by decide +kernel
theorem subd5_1_467 : subd5_1 [2, -2, -1] = true := by decide +kernel
theorem subd5_1_468 : subd5_1 [2, -2, 0] = true := by decide +kernel
theorem subd5_1_469 : subd5_1 [2, -2, 1] = true := by decide +kernel
theorem subd5_1_470 : subd5_1 [2, -2, 2] = true := by decide +kernel
theorem subd5_1_471 : subd5_1 [2, -2, 3] = true := by decide +kernel
theorem subd5_1_472 : subd5_1 [2, -2, 4] = true := by decide +kernel
theorem subd5_1_473 : subd5_1 [2, -2, 5] = true := by decide +kernel
theorem subd5_1_474 : subd5_1 [2, -2, 6] = true := by decide +kernel
theorem subd5_1_475 : subd5_1 [2, -2, 7] = true := by decide +kernel
theorem subd5_1_476 : subd5_1 [2, -2, 8] = true := by decide +kernel
theorem subd5_1_477 : subd5_1 [2, -1, -6] = true := by decide +kernel
theorem subd5_1_478 : subd5_1 [2, -1, -5] = true := by decide +kernel
theorem subd5_1_479 : subd5_1 [2, -1, -4] = true := by decide +kernel
theorem sbd5_1_14 : ∀ q ∈ blkd5_1_14, subd5_1 q = true := by
  unfold blkd5_1_14
  exact List.forall_mem_cons.2 ⟨subd5_1_448, List.forall_mem_cons.2 ⟨subd5_1_449, List.forall_mem_cons.2 ⟨subd5_1_450, List.forall_mem_cons.2 ⟨subd5_1_451, List.forall_mem_cons.2 ⟨subd5_1_452, List.forall_mem_cons.2 ⟨subd5_1_453, List.forall_mem_cons.2 ⟨subd5_1_454, List.forall_mem_cons.2 ⟨subd5_1_455, List.forall_mem_cons.2 ⟨subd5_1_456, List.forall_mem_cons.2 ⟨subd5_1_457, List.forall_mem_cons.2 ⟨subd5_1_458, List.forall_mem_cons.2 ⟨subd5_1_459, List.forall_mem_cons.2 ⟨subd5_1_460, List.forall_mem_cons.2 ⟨subd5_1_461, List.forall_mem_cons.2 ⟨subd5_1_462, List.forall_mem_cons.2 ⟨subd5_1_463, List.forall_mem_cons.2 ⟨subd5_1_464, List.forall_mem_cons.2 ⟨subd5_1_465, List.forall_mem_cons.2 ⟨subd5_1_466, List.forall_mem_cons.2 ⟨subd5_1_467, List.forall_mem_cons.2 ⟨subd5_1_468, List.forall_mem_cons.2 ⟨subd5_1_469, List.forall_mem_cons.2 ⟨subd5_1_470, List.forall_mem_cons.2 ⟨subd5_1_471, List.forall_mem_cons.2 ⟨subd5_1_472, List.forall_mem_cons.2 ⟨subd5_1_473, List.forall_mem_cons.2 ⟨subd5_1_474, List.forall_mem_cons.2 ⟨subd5_1_475, List.forall_mem_cons.2 ⟨subd5_1_476, List.forall_mem_cons.2 ⟨subd5_1_477, List.forall_mem_cons.2 ⟨subd5_1_478, List.forall_mem_cons.2 ⟨subd5_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
