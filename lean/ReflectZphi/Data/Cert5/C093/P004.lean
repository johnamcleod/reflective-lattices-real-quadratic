import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_32 : subd5_0 [-4, 1, 1] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [-4, 1, 2] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [-4, 1, 3] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [-4, 1, 4] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [-4, 2] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [-4, 3] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [-4, 4] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [-3, -5] = true := by decide +kernel
theorem subd5_0_40 : subd5_0 [-3, -4] = true := by decide +kernel
theorem subd5_0_41 : subd5_0 [-3, -3] = true := by decide +kernel
theorem subd5_0_42 : subd5_0 [-3, -2, -8] = true := by decide +kernel
theorem subd5_0_43 : subd5_0 [-3, -2, -7] = true := by decide +kernel
theorem subd5_0_44 : subd5_0 [-3, -2, -6] = true := by decide +kernel
theorem subd5_0_45 : subd5_0 [-3, -2, -5] = true := by decide +kernel
theorem subd5_0_46 : subd5_0 [-3, -2, -4] = true := by decide +kernel
theorem subd5_0_47 : subd5_0 [-3, -2, -3] = true := by decide +kernel
theorem subd5_0_48 : subd5_0 [-3, -2, -2] = true := by decide +kernel
theorem subd5_0_49 : subd5_0 [-3, -2, -1] = true := by decide +kernel
theorem subd5_0_50 : subd5_0 [-3, -2, 0] = true := by decide +kernel
theorem subd5_0_51 : subd5_0 [-3, -2, 1] = true := by decide +kernel
theorem subd5_0_52 : subd5_0 [-3, -2, 2] = true := by decide +kernel
theorem subd5_0_53 : subd5_0 [-3, -2, 3] = true := by decide +kernel
theorem subd5_0_54 : subd5_0 [-3, -2, 4] = true := by decide +kernel
theorem subd5_0_55 : subd5_0 [-3, -2, 5] = true := by decide +kernel
theorem subd5_0_56 : subd5_0 [-3, -2, 6] = true := by decide +kernel
theorem subd5_0_57 : subd5_0 [-3, -1, -9] = true := by decide +kernel
theorem subd5_0_58 : subd5_0 [-3, -1, -8] = true := by decide +kernel
theorem subd5_0_59 : subd5_0 [-3, -1, -7] = true := by decide +kernel
theorem subd5_0_60 : subd5_0 [-3, -1, -6] = true := by decide +kernel
theorem subd5_0_61 : subd5_0 [-3, -1, -5] = true := by decide +kernel
theorem subd5_0_62 : subd5_0 [-3, -1, -4] = true := by decide +kernel
theorem subd5_0_63 : subd5_0 [-3, -1, -3] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_cons.2 ⟨subd5_0_40, List.forall_mem_cons.2 ⟨subd5_0_41, List.forall_mem_cons.2 ⟨subd5_0_42, List.forall_mem_cons.2 ⟨subd5_0_43, List.forall_mem_cons.2 ⟨subd5_0_44, List.forall_mem_cons.2 ⟨subd5_0_45, List.forall_mem_cons.2 ⟨subd5_0_46, List.forall_mem_cons.2 ⟨subd5_0_47, List.forall_mem_cons.2 ⟨subd5_0_48, List.forall_mem_cons.2 ⟨subd5_0_49, List.forall_mem_cons.2 ⟨subd5_0_50, List.forall_mem_cons.2 ⟨subd5_0_51, List.forall_mem_cons.2 ⟨subd5_0_52, List.forall_mem_cons.2 ⟨subd5_0_53, List.forall_mem_cons.2 ⟨subd5_0_54, List.forall_mem_cons.2 ⟨subd5_0_55, List.forall_mem_cons.2 ⟨subd5_0_56, List.forall_mem_cons.2 ⟨subd5_0_57, List.forall_mem_cons.2 ⟨subd5_0_58, List.forall_mem_cons.2 ⟨subd5_0_59, List.forall_mem_cons.2 ⟨subd5_0_60, List.forall_mem_cons.2 ⟨subd5_0_61, List.forall_mem_cons.2 ⟨subd5_0_62, List.forall_mem_cons.2 ⟨subd5_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_64 : subd5_0 [-3, -1, -2] = true := by decide +kernel
theorem subd5_0_65 : subd5_0 [-3, -1, -1] = true := by decide +kernel
theorem subd5_0_66 : subd5_0 [-3, -1, 0] = true := by decide +kernel
theorem subd5_0_67 : subd5_0 [-3, -1, 1] = true := by decide +kernel
theorem subd5_0_68 : subd5_0 [-3, -1, 2] = true := by decide +kernel
theorem subd5_0_69 : subd5_0 [-3, -1, 3] = true := by decide +kernel
theorem subd5_0_70 : subd5_0 [-3, -1, 4] = true := by decide +kernel
theorem subd5_0_71 : subd5_0 [-3, -1, 5] = true := by decide +kernel
theorem subd5_0_72 : subd5_0 [-3, -1, 6] = true := by decide +kernel
theorem subd5_0_73 : subd5_0 [-3, 0, -10] = true := by decide +kernel
theorem subd5_0_74 : subd5_0 [-3, 0, -9] = true := by decide +kernel
theorem subd5_0_75 : subd5_0 [-3, 0, -8] = true := by decide +kernel
theorem subd5_0_76 : subd5_0 [-3, 0, -7] = true := by decide +kernel
theorem subd5_0_77 : subd5_0 [-3, 0, -6] = true := by decide +kernel
theorem subd5_0_78 : subd5_0 [-3, 0, -5] = true := by decide +kernel
theorem subd5_0_79 : subd5_0 [-3, 0, -4] = true := by decide +kernel
theorem subd5_0_80 : subd5_0 [-3, 0, -3] = true := by decide +kernel
theorem subd5_0_81 : subd5_0 [-3, 0, -2] = true := by decide +kernel
theorem subd5_0_82 : subd5_0 [-3, 0, -1] = true := by decide +kernel
theorem subd5_0_83 : subd5_0 [-3, 0, 0] = true := by decide +kernel
theorem subd5_0_84 : subd5_0 [-3, 0, 1] = true := by decide +kernel
theorem subd5_0_85 : subd5_0 [-3, 0, 2] = true := by decide +kernel
theorem subd5_0_86 : subd5_0 [-3, 0, 3] = true := by decide +kernel
theorem subd5_0_87 : subd5_0 [-3, 0, 4] = true := by decide +kernel
theorem subd5_0_88 : subd5_0 [-3, 0, 5] = true := by decide +kernel
theorem subd5_0_89 : subd5_0 [-3, 0, 6] = true := by decide +kernel
theorem subd5_0_90 : subd5_0 [-3, 1, -10] = true := by decide +kernel
theorem subd5_0_91 : subd5_0 [-3, 1, -9] = true := by decide +kernel
theorem subd5_0_92 : subd5_0 [-3, 1, -8] = true := by decide +kernel
theorem subd5_0_93 : subd5_0 [-3, 1, -7] = true := by decide +kernel
theorem subd5_0_94 : subd5_0 [-3, 1, -6] = true := by decide +kernel
theorem subd5_0_95 : subd5_0 [-3, 1, -5] = true := by decide +kernel
theorem sbd5_0_2 : ∀ q ∈ blkd5_0_2, subd5_0 q = true := by
  unfold blkd5_0_2
  exact List.forall_mem_cons.2 ⟨subd5_0_64, List.forall_mem_cons.2 ⟨subd5_0_65, List.forall_mem_cons.2 ⟨subd5_0_66, List.forall_mem_cons.2 ⟨subd5_0_67, List.forall_mem_cons.2 ⟨subd5_0_68, List.forall_mem_cons.2 ⟨subd5_0_69, List.forall_mem_cons.2 ⟨subd5_0_70, List.forall_mem_cons.2 ⟨subd5_0_71, List.forall_mem_cons.2 ⟨subd5_0_72, List.forall_mem_cons.2 ⟨subd5_0_73, List.forall_mem_cons.2 ⟨subd5_0_74, List.forall_mem_cons.2 ⟨subd5_0_75, List.forall_mem_cons.2 ⟨subd5_0_76, List.forall_mem_cons.2 ⟨subd5_0_77, List.forall_mem_cons.2 ⟨subd5_0_78, List.forall_mem_cons.2 ⟨subd5_0_79, List.forall_mem_cons.2 ⟨subd5_0_80, List.forall_mem_cons.2 ⟨subd5_0_81, List.forall_mem_cons.2 ⟨subd5_0_82, List.forall_mem_cons.2 ⟨subd5_0_83, List.forall_mem_cons.2 ⟨subd5_0_84, List.forall_mem_cons.2 ⟨subd5_0_85, List.forall_mem_cons.2 ⟨subd5_0_86, List.forall_mem_cons.2 ⟨subd5_0_87, List.forall_mem_cons.2 ⟨subd5_0_88, List.forall_mem_cons.2 ⟨subd5_0_89, List.forall_mem_cons.2 ⟨subd5_0_90, List.forall_mem_cons.2 ⟨subd5_0_91, List.forall_mem_cons.2 ⟨subd5_0_92, List.forall_mem_cons.2 ⟨subd5_0_93, List.forall_mem_cons.2 ⟨subd5_0_94, List.forall_mem_cons.2 ⟨subd5_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_96 : subd5_0 [-3, 1, -4] = true := by decide +kernel
theorem subd5_0_97 : subd5_0 [-3, 1, -3] = true := by decide +kernel
theorem subd5_0_98 : subd5_0 [-3, 1, -2] = true := by decide +kernel
theorem subd5_0_99 : subd5_0 [-3, 1, -1] = true := by decide +kernel
theorem subd5_0_100 : subd5_0 [-3, 1, 0] = true := by decide +kernel
theorem subd5_0_101 : subd5_0 [-3, 1, 1] = true := by decide +kernel
theorem subd5_0_102 : subd5_0 [-3, 1, 2] = true := by decide +kernel
theorem subd5_0_103 : subd5_0 [-3, 1, 3] = true := by decide +kernel
theorem subd5_0_104 : subd5_0 [-3, 1, 4] = true := by decide +kernel
theorem subd5_0_105 : subd5_0 [-3, 1, 5] = true := by decide +kernel
theorem subd5_0_106 : subd5_0 [-3, 1, 6] = true := by decide +kernel
theorem subd5_0_107 : subd5_0 [-3, 2, -10] = true := by decide +kernel
theorem subd5_0_108 : subd5_0 [-3, 2, -9] = true := by decide +kernel
theorem subd5_0_109 : subd5_0 [-3, 2, -8] = true := by decide +kernel
theorem subd5_0_110 : subd5_0 [-3, 2, -7] = true := by decide +kernel
theorem subd5_0_111 : subd5_0 [-3, 2, -6] = true := by decide +kernel
theorem subd5_0_112 : subd5_0 [-3, 2, -5] = true := by decide +kernel
theorem subd5_0_113 : subd5_0 [-3, 2, -4] = true := by decide +kernel
theorem subd5_0_114 : subd5_0 [-3, 2, -3] = true := by decide +kernel
theorem subd5_0_115 : subd5_0 [-3, 2, -2] = true := by decide +kernel
theorem subd5_0_116 : subd5_0 [-3, 2, -1] = true := by decide +kernel
theorem subd5_0_117 : subd5_0 [-3, 2, 0] = true := by decide +kernel
theorem subd5_0_118 : subd5_0 [-3, 2, 1] = true := by decide +kernel
theorem subd5_0_119 : subd5_0 [-3, 2, 2] = true := by decide +kernel
theorem subd5_0_120 : subd5_0 [-3, 2, 3] = true := by decide +kernel
theorem subd5_0_121 : subd5_0 [-3, 2, 4] = true := by decide +kernel
theorem subd5_0_122 : subd5_0 [-3, 2, 5] = true := by decide +kernel
theorem subd5_0_123 : subd5_0 [-3, 3, -9] = true := by decide +kernel
theorem subd5_0_124 : subd5_0 [-3, 3, -8] = true := by decide +kernel
theorem subd5_0_125 : subd5_0 [-3, 3, -7] = true := by decide +kernel
theorem subd5_0_126 : subd5_0 [-3, 3, -6] = true := by decide +kernel
theorem subd5_0_127 : subd5_0 [-3, 3, -5] = true := by decide +kernel
theorem sbd5_0_3 : ∀ q ∈ blkd5_0_3, subd5_0 q = true := by
  unfold blkd5_0_3
  exact List.forall_mem_cons.2 ⟨subd5_0_96, List.forall_mem_cons.2 ⟨subd5_0_97, List.forall_mem_cons.2 ⟨subd5_0_98, List.forall_mem_cons.2 ⟨subd5_0_99, List.forall_mem_cons.2 ⟨subd5_0_100, List.forall_mem_cons.2 ⟨subd5_0_101, List.forall_mem_cons.2 ⟨subd5_0_102, List.forall_mem_cons.2 ⟨subd5_0_103, List.forall_mem_cons.2 ⟨subd5_0_104, List.forall_mem_cons.2 ⟨subd5_0_105, List.forall_mem_cons.2 ⟨subd5_0_106, List.forall_mem_cons.2 ⟨subd5_0_107, List.forall_mem_cons.2 ⟨subd5_0_108, List.forall_mem_cons.2 ⟨subd5_0_109, List.forall_mem_cons.2 ⟨subd5_0_110, List.forall_mem_cons.2 ⟨subd5_0_111, List.forall_mem_cons.2 ⟨subd5_0_112, List.forall_mem_cons.2 ⟨subd5_0_113, List.forall_mem_cons.2 ⟨subd5_0_114, List.forall_mem_cons.2 ⟨subd5_0_115, List.forall_mem_cons.2 ⟨subd5_0_116, List.forall_mem_cons.2 ⟨subd5_0_117, List.forall_mem_cons.2 ⟨subd5_0_118, List.forall_mem_cons.2 ⟨subd5_0_119, List.forall_mem_cons.2 ⟨subd5_0_120, List.forall_mem_cons.2 ⟨subd5_0_121, List.forall_mem_cons.2 ⟨subd5_0_122, List.forall_mem_cons.2 ⟨subd5_0_123, List.forall_mem_cons.2 ⟨subd5_0_124, List.forall_mem_cons.2 ⟨subd5_0_125, List.forall_mem_cons.2 ⟨subd5_0_126, List.forall_mem_cons.2 ⟨subd5_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_128 : subd5_0 [-3, 3, -4] = true := by decide +kernel
theorem subd5_0_129 : subd5_0 [-3, 3, -3] = true := by decide +kernel
theorem subd5_0_130 : subd5_0 [-3, 3, -2] = true := by decide +kernel
theorem subd5_0_131 : subd5_0 [-3, 3, -1] = true := by decide +kernel
theorem subd5_0_132 : subd5_0 [-3, 3, 0] = true := by decide +kernel
theorem subd5_0_133 : subd5_0 [-3, 3, 1] = true := by decide +kernel
theorem subd5_0_134 : subd5_0 [-3, 3, 2] = true := by decide +kernel
theorem subd5_0_135 : subd5_0 [-3, 3, 3] = true := by decide +kernel
theorem subd5_0_136 : subd5_0 [-3, 3, 4] = true := by decide +kernel
theorem subd5_0_137 : subd5_0 [-3, 4] = true := by decide +kernel
theorem subd5_0_138 : subd5_0 [-2, -6] = true := by decide +kernel
theorem subd5_0_139 : subd5_0 [-2, -5] = true := by decide +kernel
theorem subd5_0_140 : subd5_0 [-2, -4] = true := by decide +kernel
theorem subd5_0_141 : subd5_0 [-2, -3, -7] = true := by decide +kernel
theorem subd5_0_142 : subd5_0 [-2, -3, -6] = true := by decide +kernel
theorem subd5_0_143 : subd5_0 [-2, -3, -5] = true := by decide +kernel
theorem subd5_0_144 : subd5_0 [-2, -3, -4] = true := by decide +kernel
theorem subd5_0_145 : subd5_0 [-2, -3, -3] = true := by decide +kernel
theorem subd5_0_146 : subd5_0 [-2, -3, -2] = true := by decide +kernel
theorem subd5_0_147 : subd5_0 [-2, -3, -1] = true := by decide +kernel
theorem subd5_0_148 : subd5_0 [-2, -3, 0] = true := by decide +kernel
theorem subd5_0_149 : subd5_0 [-2, -3, 1] = true := by decide +kernel
theorem subd5_0_150 : subd5_0 [-2, -3, 2] = true := by decide +kernel
theorem subd5_0_151 : subd5_0 [-2, -3, 3] = true := by decide +kernel
theorem subd5_0_152 : subd5_0 [-2, -3, 4] = true := by decide +kernel
theorem subd5_0_153 : subd5_0 [-2, -3, 5] = true := by decide +kernel
theorem subd5_0_154 : subd5_0 [-2, -3, 6] = true := by decide +kernel
theorem subd5_0_155 : subd5_0 [-2, -3, 7] = true := by decide +kernel
theorem subd5_0_156 : subd5_0 [-2, -2, -9] = true := by decide +kernel
theorem subd5_0_157 : subd5_0 [-2, -2, -8] = true := by decide +kernel
theorem subd5_0_158 : subd5_0 [-2, -2, -7] = true := by decide +kernel
theorem subd5_0_159 : subd5_0 [-2, -2, -6] = true := by decide +kernel
theorem sbd5_0_4 : ∀ q ∈ blkd5_0_4, subd5_0 q = true := by
  unfold blkd5_0_4
  exact List.forall_mem_cons.2 ⟨subd5_0_128, List.forall_mem_cons.2 ⟨subd5_0_129, List.forall_mem_cons.2 ⟨subd5_0_130, List.forall_mem_cons.2 ⟨subd5_0_131, List.forall_mem_cons.2 ⟨subd5_0_132, List.forall_mem_cons.2 ⟨subd5_0_133, List.forall_mem_cons.2 ⟨subd5_0_134, List.forall_mem_cons.2 ⟨subd5_0_135, List.forall_mem_cons.2 ⟨subd5_0_136, List.forall_mem_cons.2 ⟨subd5_0_137, List.forall_mem_cons.2 ⟨subd5_0_138, List.forall_mem_cons.2 ⟨subd5_0_139, List.forall_mem_cons.2 ⟨subd5_0_140, List.forall_mem_cons.2 ⟨subd5_0_141, List.forall_mem_cons.2 ⟨subd5_0_142, List.forall_mem_cons.2 ⟨subd5_0_143, List.forall_mem_cons.2 ⟨subd5_0_144, List.forall_mem_cons.2 ⟨subd5_0_145, List.forall_mem_cons.2 ⟨subd5_0_146, List.forall_mem_cons.2 ⟨subd5_0_147, List.forall_mem_cons.2 ⟨subd5_0_148, List.forall_mem_cons.2 ⟨subd5_0_149, List.forall_mem_cons.2 ⟨subd5_0_150, List.forall_mem_cons.2 ⟨subd5_0_151, List.forall_mem_cons.2 ⟨subd5_0_152, List.forall_mem_cons.2 ⟨subd5_0_153, List.forall_mem_cons.2 ⟨subd5_0_154, List.forall_mem_cons.2 ⟨subd5_0_155, List.forall_mem_cons.2 ⟨subd5_0_156, List.forall_mem_cons.2 ⟨subd5_0_157, List.forall_mem_cons.2 ⟨subd5_0_158, List.forall_mem_cons.2 ⟨subd5_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_160 : subd5_0 [-2, -2, -5] = true := by decide +kernel
theorem subd5_0_161 : subd5_0 [-2, -2, -4] = true := by decide +kernel
theorem subd5_0_162 : subd5_0 [-2, -2, -3] = true := by decide +kernel
theorem subd5_0_163 : subd5_0 [-2, -2, -2] = true := by decide +kernel
theorem subd5_0_164 : subd5_0 [-2, -2, -1] = true := by decide +kernel
theorem subd5_0_165 : subd5_0 [-2, -2, 0] = true := by decide +kernel
theorem subd5_0_166 : subd5_0 [-2, -2, 1] = true := by decide +kernel
theorem subd5_0_167 : subd5_0 [-2, -2, 2] = true := by decide +kernel
theorem subd5_0_168 : subd5_0 [-2, -2, 3] = true := by decide +kernel
theorem subd5_0_169 : subd5_0 [-2, -2, 4] = true := by decide +kernel
theorem subd5_0_170 : subd5_0 [-2, -2, 5] = true := by decide +kernel
theorem subd5_0_171 : subd5_0 [-2, -2, 6] = true := by decide +kernel
theorem subd5_0_172 : subd5_0 [-2, -2, 7] = true := by decide +kernel
theorem subd5_0_173 : subd5_0 [-2, -2, 8] = true := by decide +kernel
theorem subd5_0_174 : subd5_0 [-2, -1, -10] = true := by decide +kernel
theorem subd5_0_175 : subd5_0 [-2, -1, -9] = true := by decide +kernel
theorem subd5_0_176 : subd5_0 [-2, -1, -8] = true := by decide +kernel
theorem subd5_0_177 : subd5_0 [-2, -1, -7] = true := by decide +kernel
theorem subd5_0_178 : subd5_0 [-2, -1, -6] = true := by decide +kernel
theorem subd5_0_179 : subd5_0 [-2, -1, -5] = true := by decide +kernel
theorem subd5_0_180 : subd5_0 [-2, -1, -4] = true := by decide +kernel
theorem subd5_0_181 : subd5_0 [-2, -1, -3] = true := by decide +kernel
theorem subd5_0_182 : subd5_0 [-2, -1, -2] = true := by decide +kernel
theorem subd5_0_183 : subd5_0 [-2, -1, -1] = true := by decide +kernel
theorem subd5_0_184 : subd5_0 [-2, -1, 0] = true := by decide +kernel
theorem subd5_0_185 : subd5_0 [-2, -1, 1] = true := by decide +kernel
theorem subd5_0_186 : subd5_0 [-2, -1, 2] = true := by decide +kernel
theorem subd5_0_187 : subd5_0 [-2, -1, 3] = true := by decide +kernel
theorem subd5_0_188 : subd5_0 [-2, -1, 4] = true := by decide +kernel
theorem subd5_0_189 : subd5_0 [-2, -1, 5] = true := by decide +kernel
theorem subd5_0_190 : subd5_0 [-2, -1, 6] = true := by decide +kernel
theorem subd5_0_191 : subd5_0 [-2, -1, 7] = true := by decide +kernel
theorem sbd5_0_5 : ∀ q ∈ blkd5_0_5, subd5_0 q = true := by
  unfold blkd5_0_5
  exact List.forall_mem_cons.2 ⟨subd5_0_160, List.forall_mem_cons.2 ⟨subd5_0_161, List.forall_mem_cons.2 ⟨subd5_0_162, List.forall_mem_cons.2 ⟨subd5_0_163, List.forall_mem_cons.2 ⟨subd5_0_164, List.forall_mem_cons.2 ⟨subd5_0_165, List.forall_mem_cons.2 ⟨subd5_0_166, List.forall_mem_cons.2 ⟨subd5_0_167, List.forall_mem_cons.2 ⟨subd5_0_168, List.forall_mem_cons.2 ⟨subd5_0_169, List.forall_mem_cons.2 ⟨subd5_0_170, List.forall_mem_cons.2 ⟨subd5_0_171, List.forall_mem_cons.2 ⟨subd5_0_172, List.forall_mem_cons.2 ⟨subd5_0_173, List.forall_mem_cons.2 ⟨subd5_0_174, List.forall_mem_cons.2 ⟨subd5_0_175, List.forall_mem_cons.2 ⟨subd5_0_176, List.forall_mem_cons.2 ⟨subd5_0_177, List.forall_mem_cons.2 ⟨subd5_0_178, List.forall_mem_cons.2 ⟨subd5_0_179, List.forall_mem_cons.2 ⟨subd5_0_180, List.forall_mem_cons.2 ⟨subd5_0_181, List.forall_mem_cons.2 ⟨subd5_0_182, List.forall_mem_cons.2 ⟨subd5_0_183, List.forall_mem_cons.2 ⟨subd5_0_184, List.forall_mem_cons.2 ⟨subd5_0_185, List.forall_mem_cons.2 ⟨subd5_0_186, List.forall_mem_cons.2 ⟨subd5_0_187, List.forall_mem_cons.2 ⟨subd5_0_188, List.forall_mem_cons.2 ⟨subd5_0_189, List.forall_mem_cons.2 ⟨subd5_0_190, List.forall_mem_cons.2 ⟨subd5_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_192 : subd5_0 [-2, -1, 8] = true := by decide +kernel
theorem subd5_0_193 : subd5_0 [-2, 0, -10] = true := by decide +kernel
theorem subd5_0_194 : subd5_0 [-2, 0, -9] = true := by decide +kernel
theorem subd5_0_195 : subd5_0 [-2, 0, -8] = true := by decide +kernel
theorem subd5_0_196 : subd5_0 [-2, 0, -7] = true := by decide +kernel
theorem subd5_0_197 : subd5_0 [-2, 0, -6] = true := by decide +kernel
theorem subd5_0_198 : subd5_0 [-2, 0, -5] = true := by decide +kernel
theorem subd5_0_199 : subd5_0 [-2, 0, -4] = true := by decide +kernel
theorem subd5_0_200 : subd5_0 [-2, 0, -3] = true := by decide +kernel
theorem subd5_0_201 : subd5_0 [-2, 0, -2] = true := by decide +kernel
theorem subd5_0_202 : subd5_0 [-2, 0, -1] = true := by decide +kernel
theorem subd5_0_203 : subd5_0 [-2, 0, 0] = true := by decide +kernel
theorem subd5_0_204 : subd5_0 [-2, 0, 1] = true := by decide +kernel
theorem subd5_0_205 : subd5_0 [-2, 0, 2] = true := by decide +kernel
theorem subd5_0_206 : subd5_0 [-2, 0, 3] = true := by decide +kernel
theorem subd5_0_207 : subd5_0 [-2, 0, 4] = true := by decide +kernel
theorem subd5_0_208 : subd5_0 [-2, 0, 5] = true := by decide +kernel
theorem subd5_0_209 : subd5_0 [-2, 0, 6] = true := by decide +kernel
theorem subd5_0_210 : subd5_0 [-2, 0, 7] = true := by decide +kernel
theorem subd5_0_211 : subd5_0 [-2, 0, 8] = true := by decide +kernel
theorem subd5_0_212 : subd5_0 [-2, 1, -10] = true := by decide +kernel
theorem subd5_0_213 : subd5_0 [-2, 1, -9] = true := by decide +kernel
theorem subd5_0_214 : subd5_0 [-2, 1, -8] = true := by decide +kernel
theorem subd5_0_215 : subd5_0 [-2, 1, -7] = true := by decide +kernel
theorem subd5_0_216 : subd5_0 [-2, 1, -6] = true := by decide +kernel
theorem subd5_0_217 : subd5_0 [-2, 1, -5] = true := by decide +kernel
theorem subd5_0_218 : subd5_0 [-2, 1, -4] = true := by decide +kernel
theorem subd5_0_219 : subd5_0 [-2, 1, -3] = true := by decide +kernel
theorem subd5_0_220 : subd5_0 [-2, 1, -2] = true := by decide +kernel
theorem subd5_0_221 : subd5_0 [-2, 1, -1] = true := by decide +kernel
theorem subd5_0_222 : subd5_0 [-2, 1, 0] = true := by decide +kernel
theorem subd5_0_223 : subd5_0 [-2, 1, 1] = true := by decide +kernel
theorem sbd5_0_6 : ∀ q ∈ blkd5_0_6, subd5_0 q = true := by
  unfold blkd5_0_6
  exact List.forall_mem_cons.2 ⟨subd5_0_192, List.forall_mem_cons.2 ⟨subd5_0_193, List.forall_mem_cons.2 ⟨subd5_0_194, List.forall_mem_cons.2 ⟨subd5_0_195, List.forall_mem_cons.2 ⟨subd5_0_196, List.forall_mem_cons.2 ⟨subd5_0_197, List.forall_mem_cons.2 ⟨subd5_0_198, List.forall_mem_cons.2 ⟨subd5_0_199, List.forall_mem_cons.2 ⟨subd5_0_200, List.forall_mem_cons.2 ⟨subd5_0_201, List.forall_mem_cons.2 ⟨subd5_0_202, List.forall_mem_cons.2 ⟨subd5_0_203, List.forall_mem_cons.2 ⟨subd5_0_204, List.forall_mem_cons.2 ⟨subd5_0_205, List.forall_mem_cons.2 ⟨subd5_0_206, List.forall_mem_cons.2 ⟨subd5_0_207, List.forall_mem_cons.2 ⟨subd5_0_208, List.forall_mem_cons.2 ⟨subd5_0_209, List.forall_mem_cons.2 ⟨subd5_0_210, List.forall_mem_cons.2 ⟨subd5_0_211, List.forall_mem_cons.2 ⟨subd5_0_212, List.forall_mem_cons.2 ⟨subd5_0_213, List.forall_mem_cons.2 ⟨subd5_0_214, List.forall_mem_cons.2 ⟨subd5_0_215, List.forall_mem_cons.2 ⟨subd5_0_216, List.forall_mem_cons.2 ⟨subd5_0_217, List.forall_mem_cons.2 ⟨subd5_0_218, List.forall_mem_cons.2 ⟨subd5_0_219, List.forall_mem_cons.2 ⟨subd5_0_220, List.forall_mem_cons.2 ⟨subd5_0_221, List.forall_mem_cons.2 ⟨subd5_0_222, List.forall_mem_cons.2 ⟨subd5_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_224 : subd5_0 [-2, 1, 2] = true := by decide +kernel
theorem subd5_0_225 : subd5_0 [-2, 1, 3] = true := by decide +kernel
theorem subd5_0_226 : subd5_0 [-2, 1, 4] = true := by decide +kernel
theorem subd5_0_227 : subd5_0 [-2, 1, 5] = true := by decide +kernel
theorem subd5_0_228 : subd5_0 [-2, 1, 6] = true := by decide +kernel
theorem subd5_0_229 : subd5_0 [-2, 1, 7] = true := by decide +kernel
theorem subd5_0_230 : subd5_0 [-2, 2, -10] = true := by decide +kernel
theorem subd5_0_231 : subd5_0 [-2, 2, -9] = true := by decide +kernel
theorem subd5_0_232 : subd5_0 [-2, 2, -8] = true := by decide +kernel
theorem subd5_0_233 : subd5_0 [-2, 2, -7] = true := by decide +kernel
theorem subd5_0_234 : subd5_0 [-2, 2, -6] = true := by decide +kernel
theorem subd5_0_235 : subd5_0 [-2, 2, -5] = true := by decide +kernel
theorem subd5_0_236 : subd5_0 [-2, 2, -4] = true := by decide +kernel
theorem subd5_0_237 : subd5_0 [-2, 2, -3] = true := by decide +kernel
theorem subd5_0_238 : subd5_0 [-2, 2, -2] = true := by decide +kernel
theorem subd5_0_239 : subd5_0 [-2, 2, -1] = true := by decide +kernel
theorem subd5_0_240 : subd5_0 [-2, 2, 0] = true := by decide +kernel
theorem subd5_0_241 : subd5_0 [-2, 2, 1] = true := by decide +kernel
theorem subd5_0_242 : subd5_0 [-2, 2, 2] = true := by decide +kernel
theorem subd5_0_243 : subd5_0 [-2, 2, 3] = true := by decide +kernel
theorem subd5_0_244 : subd5_0 [-2, 2, 4] = true := by decide +kernel
theorem subd5_0_245 : subd5_0 [-2, 2, 5] = true := by decide +kernel
theorem subd5_0_246 : subd5_0 [-2, 2, 6] = true := by decide +kernel
theorem subd5_0_247 : subd5_0 [-2, 3, -10] = true := by decide +kernel
theorem subd5_0_248 : subd5_0 [-2, 3, -9] = true := by decide +kernel
theorem subd5_0_249 : subd5_0 [-2, 3, -8] = true := by decide +kernel
theorem subd5_0_250 : subd5_0 [-2, 3, -7] = true := by decide +kernel
theorem subd5_0_251 : subd5_0 [-2, 3, -6] = true := by decide +kernel
theorem subd5_0_252 : subd5_0 [-2, 3, -5] = true := by decide +kernel
theorem subd5_0_253 : subd5_0 [-2, 3, -4] = true := by decide +kernel
theorem subd5_0_254 : subd5_0 [-2, 3, -3] = true := by decide +kernel
theorem subd5_0_255 : subd5_0 [-2, 3, -2] = true := by decide +kernel
theorem sbd5_0_7 : ∀ q ∈ blkd5_0_7, subd5_0 q = true := by
  unfold blkd5_0_7
  exact List.forall_mem_cons.2 ⟨subd5_0_224, List.forall_mem_cons.2 ⟨subd5_0_225, List.forall_mem_cons.2 ⟨subd5_0_226, List.forall_mem_cons.2 ⟨subd5_0_227, List.forall_mem_cons.2 ⟨subd5_0_228, List.forall_mem_cons.2 ⟨subd5_0_229, List.forall_mem_cons.2 ⟨subd5_0_230, List.forall_mem_cons.2 ⟨subd5_0_231, List.forall_mem_cons.2 ⟨subd5_0_232, List.forall_mem_cons.2 ⟨subd5_0_233, List.forall_mem_cons.2 ⟨subd5_0_234, List.forall_mem_cons.2 ⟨subd5_0_235, List.forall_mem_cons.2 ⟨subd5_0_236, List.forall_mem_cons.2 ⟨subd5_0_237, List.forall_mem_cons.2 ⟨subd5_0_238, List.forall_mem_cons.2 ⟨subd5_0_239, List.forall_mem_cons.2 ⟨subd5_0_240, List.forall_mem_cons.2 ⟨subd5_0_241, List.forall_mem_cons.2 ⟨subd5_0_242, List.forall_mem_cons.2 ⟨subd5_0_243, List.forall_mem_cons.2 ⟨subd5_0_244, List.forall_mem_cons.2 ⟨subd5_0_245, List.forall_mem_cons.2 ⟨subd5_0_246, List.forall_mem_cons.2 ⟨subd5_0_247, List.forall_mem_cons.2 ⟨subd5_0_248, List.forall_mem_cons.2 ⟨subd5_0_249, List.forall_mem_cons.2 ⟨subd5_0_250, List.forall_mem_cons.2 ⟨subd5_0_251, List.forall_mem_cons.2 ⟨subd5_0_252, List.forall_mem_cons.2 ⟨subd5_0_253, List.forall_mem_cons.2 ⟨subd5_0_254, List.forall_mem_cons.2 ⟨subd5_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_256 : subd5_0 [-2, 3, -1] = true := by decide +kernel
theorem subd5_0_257 : subd5_0 [-2, 3, 0] = true := by decide +kernel
theorem subd5_0_258 : subd5_0 [-2, 3, 1] = true := by decide +kernel
theorem subd5_0_259 : subd5_0 [-2, 3, 2] = true := by decide +kernel
theorem subd5_0_260 : subd5_0 [-2, 3, 3] = true := by decide +kernel
theorem subd5_0_261 : subd5_0 [-2, 3, 4] = true := by decide +kernel
theorem subd5_0_262 : subd5_0 [-2, 3, 5] = true := by decide +kernel
theorem subd5_0_263 : subd5_0 [-2, 4] = true := by decide +kernel
theorem subd5_0_264 : subd5_0 [-2, 5] = true := by decide +kernel
theorem subd5_0_265 : subd5_0 [-1, -6] = true := by decide +kernel
theorem subd5_0_266 : subd5_0 [-1, -5] = true := by decide +kernel
theorem subd5_0_267 : subd5_0 [-1, -4, -6] = true := by decide +kernel
theorem subd5_0_268 : subd5_0 [-1, -4, -5] = true := by decide +kernel
theorem subd5_0_269 : subd5_0 [-1, -4, -4] = true := by decide +kernel
theorem subd5_0_270 : subd5_0 [-1, -4, -3] = true := by decide +kernel
theorem subd5_0_271 : subd5_0 [-1, -4, -2] = true := by decide +kernel
theorem subd5_0_272 : subd5_0 [-1, -4, -1] = true := by decide +kernel
theorem subd5_0_273 : subd5_0 [-1, -4, 0] = true := by decide +kernel
theorem subd5_0_274 : subd5_0 [-1, -4, 1] = true := by decide +kernel
theorem subd5_0_275 : subd5_0 [-1, -4, 2] = true := by decide +kernel
theorem subd5_0_276 : subd5_0 [-1, -4, 3] = true := by decide +kernel
theorem subd5_0_277 : subd5_0 [-1, -4, 4] = true := by decide +kernel
theorem subd5_0_278 : subd5_0 [-1, -4, 5] = true := by decide +kernel
theorem subd5_0_279 : subd5_0 [-1, -4, 6] = true := by decide +kernel
theorem subd5_0_280 : subd5_0 [-1, -4, 7] = true := by decide +kernel
theorem subd5_0_281 : subd5_0 [-1, -3, -8] = true := by decide +kernel
theorem subd5_0_282 : subd5_0 [-1, -3, -7] = true := by decide +kernel
theorem subd5_0_283 : subd5_0 [-1, -3, -6] = true := by decide +kernel
theorem subd5_0_284 : subd5_0 [-1, -3, -5] = true := by decide +kernel
theorem subd5_0_285 : subd5_0 [-1, -3, -4] = true := by decide +kernel
theorem subd5_0_286 : subd5_0 [-1, -3, -3] = true := by decide +kernel
theorem subd5_0_287 : subd5_0 [-1, -3, -2] = true := by decide +kernel
theorem sbd5_0_8 : ∀ q ∈ blkd5_0_8, subd5_0 q = true := by
  unfold blkd5_0_8
  exact List.forall_mem_cons.2 ⟨subd5_0_256, List.forall_mem_cons.2 ⟨subd5_0_257, List.forall_mem_cons.2 ⟨subd5_0_258, List.forall_mem_cons.2 ⟨subd5_0_259, List.forall_mem_cons.2 ⟨subd5_0_260, List.forall_mem_cons.2 ⟨subd5_0_261, List.forall_mem_cons.2 ⟨subd5_0_262, List.forall_mem_cons.2 ⟨subd5_0_263, List.forall_mem_cons.2 ⟨subd5_0_264, List.forall_mem_cons.2 ⟨subd5_0_265, List.forall_mem_cons.2 ⟨subd5_0_266, List.forall_mem_cons.2 ⟨subd5_0_267, List.forall_mem_cons.2 ⟨subd5_0_268, List.forall_mem_cons.2 ⟨subd5_0_269, List.forall_mem_cons.2 ⟨subd5_0_270, List.forall_mem_cons.2 ⟨subd5_0_271, List.forall_mem_cons.2 ⟨subd5_0_272, List.forall_mem_cons.2 ⟨subd5_0_273, List.forall_mem_cons.2 ⟨subd5_0_274, List.forall_mem_cons.2 ⟨subd5_0_275, List.forall_mem_cons.2 ⟨subd5_0_276, List.forall_mem_cons.2 ⟨subd5_0_277, List.forall_mem_cons.2 ⟨subd5_0_278, List.forall_mem_cons.2 ⟨subd5_0_279, List.forall_mem_cons.2 ⟨subd5_0_280, List.forall_mem_cons.2 ⟨subd5_0_281, List.forall_mem_cons.2 ⟨subd5_0_282, List.forall_mem_cons.2 ⟨subd5_0_283, List.forall_mem_cons.2 ⟨subd5_0_284, List.forall_mem_cons.2 ⟨subd5_0_285, List.forall_mem_cons.2 ⟨subd5_0_286, List.forall_mem_cons.2 ⟨subd5_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_288 : subd5_0 [-1, -3, -1] = true := by decide +kernel
theorem subd5_0_289 : subd5_0 [-1, -3, 0] = true := by decide +kernel
theorem subd5_0_290 : subd5_0 [-1, -3, 1] = true := by decide +kernel
theorem subd5_0_291 : subd5_0 [-1, -3, 2] = true := by decide +kernel
theorem subd5_0_292 : subd5_0 [-1, -3, 3] = true := by decide +kernel
theorem subd5_0_293 : subd5_0 [-1, -3, 4] = true := by decide +kernel
theorem subd5_0_294 : subd5_0 [-1, -3, 5] = true := by decide +kernel
theorem subd5_0_295 : subd5_0 [-1, -3, 6] = true := by decide +kernel
theorem subd5_0_296 : subd5_0 [-1, -3, 7] = true := by decide +kernel
theorem subd5_0_297 : subd5_0 [-1, -3, 8] = true := by decide +kernel
theorem subd5_0_298 : subd5_0 [-1, -2, -9] = true := by decide +kernel
theorem subd5_0_299 : subd5_0 [-1, -2, -8] = true := by decide +kernel
theorem subd5_0_300 : subd5_0 [-1, -2, -7] = true := by decide +kernel
theorem subd5_0_301 : subd5_0 [-1, -2, -6] = true := by decide +kernel
theorem subd5_0_302 : subd5_0 [-1, -2, -5] = true := by decide +kernel
theorem subd5_0_303 : subd5_0 [-1, -2, -4] = true := by decide +kernel
theorem subd5_0_304 : subd5_0 [-1, -2, -3] = true := by decide +kernel
theorem subd5_0_305 : subd5_0 [-1, -2, -2] = true := by decide +kernel
theorem subd5_0_306 : subd5_0 [-1, -2, -1] = true := by decide +kernel
theorem subd5_0_307 : subd5_0 [-1, -2, 0] = true := by decide +kernel
theorem subd5_0_308 : subd5_0 [-1, -2, 1] = true := by decide +kernel
theorem subd5_0_309 : subd5_0 [-1, -2, 2] = true := by decide +kernel
theorem subd5_0_310 : subd5_0 [-1, -2, 3] = true := by decide +kernel
theorem subd5_0_311 : subd5_0 [-1, -2, 4] = true := by decide +kernel
theorem subd5_0_312 : subd5_0 [-1, -2, 5] = true := by decide +kernel
theorem subd5_0_313 : subd5_0 [-1, -2, 6] = true := by decide +kernel
theorem subd5_0_314 : subd5_0 [-1, -2, 7] = true := by decide +kernel
theorem subd5_0_315 : subd5_0 [-1, -2, 8] = true := by decide +kernel
theorem subd5_0_316 : subd5_0 [-1, -2, 9] = true := by decide +kernel
theorem subd5_0_317 : subd5_0 [-1, -1, -10] = true := by decide +kernel
theorem subd5_0_318 : subd5_0 [-1, -1, -9] = true := by decide +kernel
theorem subd5_0_319 : subd5_0 [-1, -1, -8] = true := by decide +kernel
theorem sbd5_0_9 : ∀ q ∈ blkd5_0_9, subd5_0 q = true := by
  unfold blkd5_0_9
  exact List.forall_mem_cons.2 ⟨subd5_0_288, List.forall_mem_cons.2 ⟨subd5_0_289, List.forall_mem_cons.2 ⟨subd5_0_290, List.forall_mem_cons.2 ⟨subd5_0_291, List.forall_mem_cons.2 ⟨subd5_0_292, List.forall_mem_cons.2 ⟨subd5_0_293, List.forall_mem_cons.2 ⟨subd5_0_294, List.forall_mem_cons.2 ⟨subd5_0_295, List.forall_mem_cons.2 ⟨subd5_0_296, List.forall_mem_cons.2 ⟨subd5_0_297, List.forall_mem_cons.2 ⟨subd5_0_298, List.forall_mem_cons.2 ⟨subd5_0_299, List.forall_mem_cons.2 ⟨subd5_0_300, List.forall_mem_cons.2 ⟨subd5_0_301, List.forall_mem_cons.2 ⟨subd5_0_302, List.forall_mem_cons.2 ⟨subd5_0_303, List.forall_mem_cons.2 ⟨subd5_0_304, List.forall_mem_cons.2 ⟨subd5_0_305, List.forall_mem_cons.2 ⟨subd5_0_306, List.forall_mem_cons.2 ⟨subd5_0_307, List.forall_mem_cons.2 ⟨subd5_0_308, List.forall_mem_cons.2 ⟨subd5_0_309, List.forall_mem_cons.2 ⟨subd5_0_310, List.forall_mem_cons.2 ⟨subd5_0_311, List.forall_mem_cons.2 ⟨subd5_0_312, List.forall_mem_cons.2 ⟨subd5_0_313, List.forall_mem_cons.2 ⟨subd5_0_314, List.forall_mem_cons.2 ⟨subd5_0_315, List.forall_mem_cons.2 ⟨subd5_0_316, List.forall_mem_cons.2 ⟨subd5_0_317, List.forall_mem_cons.2 ⟨subd5_0_318, List.forall_mem_cons.2 ⟨subd5_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_320 : subd5_0 [-1, -1, -7] = true := by decide +kernel
theorem subd5_0_321 : subd5_0 [-1, -1, -6] = true := by decide +kernel
theorem subd5_0_322 : subd5_0 [-1, -1, -5] = true := by decide +kernel
theorem subd5_0_323 : subd5_0 [-1, -1, -4] = true := by decide +kernel
theorem subd5_0_324 : subd5_0 [-1, -1, -3] = true := by decide +kernel
theorem subd5_0_325 : subd5_0 [-1, -1, -2] = true := by decide +kernel
theorem subd5_0_326 : subd5_0 [-1, -1, -1] = true := by decide +kernel
theorem subd5_0_327 : subd5_0 [-1, -1, 0] = true := by decide +kernel
theorem subd5_0_328 : subd5_0 [-1, -1, 1] = true := by decide +kernel
theorem subd5_0_329 : subd5_0 [-1, -1, 2] = true := by decide +kernel
theorem subd5_0_330 : subd5_0 [-1, -1, 3] = true := by decide +kernel
theorem subd5_0_331 : subd5_0 [-1, -1, 4] = true := by decide +kernel
theorem subd5_0_332 : subd5_0 [-1, -1, 5] = true := by decide +kernel
theorem subd5_0_333 : subd5_0 [-1, -1, 6] = true := by decide +kernel
theorem subd5_0_334 : subd5_0 [-1, -1, 7] = true := by decide +kernel
theorem subd5_0_335 : subd5_0 [-1, -1, 8] = true := by decide +kernel
theorem subd5_0_336 : subd5_0 [-1, -1, 9] = true := by decide +kernel
theorem subd5_0_337 : subd5_0 [-1, 0, -10] = true := by decide +kernel
theorem subd5_0_338 : subd5_0 [-1, 0, -9] = true := by decide +kernel
theorem subd5_0_339 : subd5_0 [-1, 0, -8] = true := by decide +kernel
theorem subd5_0_340 : subd5_0 [-1, 0, -7] = true := by decide +kernel
theorem subd5_0_341 : subd5_0 [-1, 0, -6] = true := by decide +kernel
theorem subd5_0_342 : subd5_0 [-1, 0, -5] = true := by decide +kernel
theorem subd5_0_343 : subd5_0 [-1, 0, -4] = true := by decide +kernel
theorem subd5_0_344 : subd5_0 [-1, 0, -3] = true := by decide +kernel
theorem subd5_0_345 : subd5_0 [-1, 0, -2] = true := by decide +kernel
theorem subd5_0_346 : subd5_0 [-1, 0, -1] = true := by decide +kernel
theorem subd5_0_347 : subd5_0 [-1, 0, 0] = true := by decide +kernel
theorem subd5_0_348 : subd5_0 [-1, 0, 1] = true := by decide +kernel
theorem subd5_0_349 : subd5_0 [-1, 0, 2] = true := by decide +kernel
theorem subd5_0_350 : subd5_0 [-1, 0, 3] = true := by decide +kernel
theorem subd5_0_351 : subd5_0 [-1, 0, 4] = true := by decide +kernel
theorem sbd5_0_10 : ∀ q ∈ blkd5_0_10, subd5_0 q = true := by
  unfold blkd5_0_10
  exact List.forall_mem_cons.2 ⟨subd5_0_320, List.forall_mem_cons.2 ⟨subd5_0_321, List.forall_mem_cons.2 ⟨subd5_0_322, List.forall_mem_cons.2 ⟨subd5_0_323, List.forall_mem_cons.2 ⟨subd5_0_324, List.forall_mem_cons.2 ⟨subd5_0_325, List.forall_mem_cons.2 ⟨subd5_0_326, List.forall_mem_cons.2 ⟨subd5_0_327, List.forall_mem_cons.2 ⟨subd5_0_328, List.forall_mem_cons.2 ⟨subd5_0_329, List.forall_mem_cons.2 ⟨subd5_0_330, List.forall_mem_cons.2 ⟨subd5_0_331, List.forall_mem_cons.2 ⟨subd5_0_332, List.forall_mem_cons.2 ⟨subd5_0_333, List.forall_mem_cons.2 ⟨subd5_0_334, List.forall_mem_cons.2 ⟨subd5_0_335, List.forall_mem_cons.2 ⟨subd5_0_336, List.forall_mem_cons.2 ⟨subd5_0_337, List.forall_mem_cons.2 ⟨subd5_0_338, List.forall_mem_cons.2 ⟨subd5_0_339, List.forall_mem_cons.2 ⟨subd5_0_340, List.forall_mem_cons.2 ⟨subd5_0_341, List.forall_mem_cons.2 ⟨subd5_0_342, List.forall_mem_cons.2 ⟨subd5_0_343, List.forall_mem_cons.2 ⟨subd5_0_344, List.forall_mem_cons.2 ⟨subd5_0_345, List.forall_mem_cons.2 ⟨subd5_0_346, List.forall_mem_cons.2 ⟨subd5_0_347, List.forall_mem_cons.2 ⟨subd5_0_348, List.forall_mem_cons.2 ⟨subd5_0_349, List.forall_mem_cons.2 ⟨subd5_0_350, List.forall_mem_cons.2 ⟨subd5_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_352 : subd5_0 [-1, 0, 5] = true := by decide +kernel
theorem subd5_0_353 : subd5_0 [-1, 0, 6] = true := by decide +kernel
theorem subd5_0_354 : subd5_0 [-1, 0, 7] = true := by decide +kernel
theorem subd5_0_355 : subd5_0 [-1, 0, 8] = true := by decide +kernel
theorem subd5_0_356 : subd5_0 [-1, 0, 9] = true := by decide +kernel
theorem subd5_0_357 : subd5_0 [-1, 1, -11] = true := by decide +kernel
theorem subd5_0_358 : subd5_0 [-1, 1, -10] = true := by decide +kernel
theorem subd5_0_359 : subd5_0 [-1, 1, -9] = true := by decide +kernel
theorem subd5_0_360 : subd5_0 [-1, 1, -8] = true := by decide +kernel
theorem subd5_0_361 : subd5_0 [-1, 1, -7] = true := by decide +kernel
theorem subd5_0_362 : subd5_0 [-1, 1, -6] = true := by decide +kernel
theorem subd5_0_363 : subd5_0 [-1, 1, -5] = true := by decide +kernel
theorem subd5_0_364 : subd5_0 [-1, 1, -4] = true := by decide +kernel
theorem subd5_0_365 : subd5_0 [-1, 1, -3] = true := by decide +kernel
theorem subd5_0_366 : subd5_0 [-1, 1, -2] = true := by decide +kernel
theorem subd5_0_367 : subd5_0 [-1, 1, -1] = true := by decide +kernel
theorem subd5_0_368 : subd5_0 [-1, 1, 0] = true := by decide +kernel
theorem subd5_0_369 : subd5_0 [-1, 1, 1] = true := by decide +kernel
theorem subd5_0_370 : subd5_0 [-1, 1, 2] = true := by decide +kernel
theorem subd5_0_371 : subd5_0 [-1, 1, 3] = true := by decide +kernel
theorem subd5_0_372 : subd5_0 [-1, 1, 4] = true := by decide +kernel
theorem subd5_0_373 : subd5_0 [-1, 1, 5] = true := by decide +kernel
theorem subd5_0_374 : subd5_0 [-1, 1, 6] = true := by decide +kernel
theorem subd5_0_375 : subd5_0 [-1, 1, 7] = true := by decide +kernel
theorem subd5_0_376 : subd5_0 [-1, 1, 8] = true := by decide +kernel
theorem subd5_0_377 : subd5_0 [-1, 2, -10] = true := by decide +kernel
theorem subd5_0_378 : subd5_0 [-1, 2, -9] = true := by decide +kernel
theorem subd5_0_379 : subd5_0 [-1, 2, -8] = true := by decide +kernel
theorem subd5_0_380 : subd5_0 [-1, 2, -7] = true := by decide +kernel
theorem subd5_0_381 : subd5_0 [-1, 2, -6] = true := by decide +kernel
theorem subd5_0_382 : subd5_0 [-1, 2, -5] = true := by decide +kernel
theorem subd5_0_383 : subd5_0 [-1, 2, -4] = true := by decide +kernel
theorem sbd5_0_11 : ∀ q ∈ blkd5_0_11, subd5_0 q = true := by
  unfold blkd5_0_11
  exact List.forall_mem_cons.2 ⟨subd5_0_352, List.forall_mem_cons.2 ⟨subd5_0_353, List.forall_mem_cons.2 ⟨subd5_0_354, List.forall_mem_cons.2 ⟨subd5_0_355, List.forall_mem_cons.2 ⟨subd5_0_356, List.forall_mem_cons.2 ⟨subd5_0_357, List.forall_mem_cons.2 ⟨subd5_0_358, List.forall_mem_cons.2 ⟨subd5_0_359, List.forall_mem_cons.2 ⟨subd5_0_360, List.forall_mem_cons.2 ⟨subd5_0_361, List.forall_mem_cons.2 ⟨subd5_0_362, List.forall_mem_cons.2 ⟨subd5_0_363, List.forall_mem_cons.2 ⟨subd5_0_364, List.forall_mem_cons.2 ⟨subd5_0_365, List.forall_mem_cons.2 ⟨subd5_0_366, List.forall_mem_cons.2 ⟨subd5_0_367, List.forall_mem_cons.2 ⟨subd5_0_368, List.forall_mem_cons.2 ⟨subd5_0_369, List.forall_mem_cons.2 ⟨subd5_0_370, List.forall_mem_cons.2 ⟨subd5_0_371, List.forall_mem_cons.2 ⟨subd5_0_372, List.forall_mem_cons.2 ⟨subd5_0_373, List.forall_mem_cons.2 ⟨subd5_0_374, List.forall_mem_cons.2 ⟨subd5_0_375, List.forall_mem_cons.2 ⟨subd5_0_376, List.forall_mem_cons.2 ⟨subd5_0_377, List.forall_mem_cons.2 ⟨subd5_0_378, List.forall_mem_cons.2 ⟨subd5_0_379, List.forall_mem_cons.2 ⟨subd5_0_380, List.forall_mem_cons.2 ⟨subd5_0_381, List.forall_mem_cons.2 ⟨subd5_0_382, List.forall_mem_cons.2 ⟨subd5_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_384 : subd5_0 [-1, 2, -3] = true := by decide +kernel
theorem subd5_0_385 : subd5_0 [-1, 2, -2] = true := by decide +kernel
theorem subd5_0_386 : subd5_0 [-1, 2, -1] = true := by decide +kernel
theorem subd5_0_387 : subd5_0 [-1, 2, 0] = true := by decide +kernel
theorem subd5_0_388 : subd5_0 [-1, 2, 1] = true := by decide +kernel
theorem subd5_0_389 : subd5_0 [-1, 2, 2] = true := by decide +kernel
theorem subd5_0_390 : subd5_0 [-1, 2, 3] = true := by decide +kernel
theorem subd5_0_391 : subd5_0 [-1, 2, 4] = true := by decide +kernel
theorem subd5_0_392 : subd5_0 [-1, 2, 5] = true := by decide +kernel
theorem subd5_0_393 : subd5_0 [-1, 2, 6] = true := by decide +kernel
theorem subd5_0_394 : subd5_0 [-1, 2, 7] = true := by decide +kernel
theorem subd5_0_395 : subd5_0 [-1, 3, -10] = true := by decide +kernel
theorem subd5_0_396 : subd5_0 [-1, 3, -9] = true := by decide +kernel
theorem subd5_0_397 : subd5_0 [-1, 3, -8] = true := by decide +kernel
theorem subd5_0_398 : subd5_0 [-1, 3, -7] = true := by decide +kernel
theorem subd5_0_399 : subd5_0 [-1, 3, -6] = true := by decide +kernel
theorem subd5_0_400 : subd5_0 [-1, 3, -5] = true := by decide +kernel
theorem subd5_0_401 : subd5_0 [-1, 3, -4] = true := by decide +kernel
theorem subd5_0_402 : subd5_0 [-1, 3, -3] = true := by decide +kernel
theorem subd5_0_403 : subd5_0 [-1, 3, -2] = true := by decide +kernel
theorem subd5_0_404 : subd5_0 [-1, 3, -1] = true := by decide +kernel
theorem subd5_0_405 : subd5_0 [-1, 3, 0] = true := by decide +kernel
theorem subd5_0_406 : subd5_0 [-1, 3, 1] = true := by decide +kernel
theorem subd5_0_407 : subd5_0 [-1, 3, 2] = true := by decide +kernel
theorem subd5_0_408 : subd5_0 [-1, 3, 3] = true := by decide +kernel
theorem subd5_0_409 : subd5_0 [-1, 3, 4] = true := by decide +kernel
theorem subd5_0_410 : subd5_0 [-1, 3, 5] = true := by decide +kernel
theorem subd5_0_411 : subd5_0 [-1, 3, 6] = true := by decide +kernel
theorem subd5_0_412 : subd5_0 [-1, 4, -9] = true := by decide +kernel
theorem subd5_0_413 : subd5_0 [-1, 4, -8] = true := by decide +kernel
theorem subd5_0_414 : subd5_0 [-1, 4, -7] = true := by decide +kernel
theorem subd5_0_415 : subd5_0 [-1, 4, -6] = true := by decide +kernel
theorem sbd5_0_12 : ∀ q ∈ blkd5_0_12, subd5_0 q = true := by
  unfold blkd5_0_12
  exact List.forall_mem_cons.2 ⟨subd5_0_384, List.forall_mem_cons.2 ⟨subd5_0_385, List.forall_mem_cons.2 ⟨subd5_0_386, List.forall_mem_cons.2 ⟨subd5_0_387, List.forall_mem_cons.2 ⟨subd5_0_388, List.forall_mem_cons.2 ⟨subd5_0_389, List.forall_mem_cons.2 ⟨subd5_0_390, List.forall_mem_cons.2 ⟨subd5_0_391, List.forall_mem_cons.2 ⟨subd5_0_392, List.forall_mem_cons.2 ⟨subd5_0_393, List.forall_mem_cons.2 ⟨subd5_0_394, List.forall_mem_cons.2 ⟨subd5_0_395, List.forall_mem_cons.2 ⟨subd5_0_396, List.forall_mem_cons.2 ⟨subd5_0_397, List.forall_mem_cons.2 ⟨subd5_0_398, List.forall_mem_cons.2 ⟨subd5_0_399, List.forall_mem_cons.2 ⟨subd5_0_400, List.forall_mem_cons.2 ⟨subd5_0_401, List.forall_mem_cons.2 ⟨subd5_0_402, List.forall_mem_cons.2 ⟨subd5_0_403, List.forall_mem_cons.2 ⟨subd5_0_404, List.forall_mem_cons.2 ⟨subd5_0_405, List.forall_mem_cons.2 ⟨subd5_0_406, List.forall_mem_cons.2 ⟨subd5_0_407, List.forall_mem_cons.2 ⟨subd5_0_408, List.forall_mem_cons.2 ⟨subd5_0_409, List.forall_mem_cons.2 ⟨subd5_0_410, List.forall_mem_cons.2 ⟨subd5_0_411, List.forall_mem_cons.2 ⟨subd5_0_412, List.forall_mem_cons.2 ⟨subd5_0_413, List.forall_mem_cons.2 ⟨subd5_0_414, List.forall_mem_cons.2 ⟨subd5_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_416 : subd5_0 [-1, 4, -5] = true := by decide +kernel
theorem subd5_0_417 : subd5_0 [-1, 4, -4] = true := by decide +kernel
theorem subd5_0_418 : subd5_0 [-1, 4, -3] = true := by decide +kernel
theorem subd5_0_419 : subd5_0 [-1, 4, -2] = true := by decide +kernel
theorem subd5_0_420 : subd5_0 [-1, 4, -1] = true := by decide +kernel
theorem subd5_0_421 : subd5_0 [-1, 4, 0] = true := by decide +kernel
theorem subd5_0_422 : subd5_0 [-1, 4, 1] = true := by decide +kernel
theorem subd5_0_423 : subd5_0 [-1, 4, 2] = true := by decide +kernel
theorem subd5_0_424 : subd5_0 [-1, 4, 3] = true := by decide +kernel
theorem subd5_0_425 : subd5_0 [-1, 4, 4] = true := by decide +kernel
theorem subd5_0_426 : subd5_0 [-1, 5] = true := by decide +kernel
theorem subd5_0_427 : subd5_0 [0, -6] = true := by decide +kernel
theorem subd5_0_428 : subd5_0 [0, -5] = true := by decide +kernel
theorem subd5_0_429 : subd5_0 [0, -4, -6] = true := by decide +kernel
theorem subd5_0_430 : subd5_0 [0, -4, -5] = true := by decide +kernel
theorem subd5_0_431 : subd5_0 [0, -4, -4] = true := by decide +kernel
theorem subd5_0_432 : subd5_0 [0, -4, -3] = true := by decide +kernel
theorem subd5_0_433 : subd5_0 [0, -4, -2] = true := by decide +kernel
theorem subd5_0_434 : subd5_0 [0, -4, -1] = true := by decide +kernel
theorem subd5_0_435 : subd5_0 [0, -4, 0] = true := by decide +kernel
theorem subd5_0_436 : subd5_0 [0, -4, 1] = true := by decide +kernel
theorem subd5_0_437 : subd5_0 [0, -4, 2] = true := by decide +kernel
theorem subd5_0_438 : subd5_0 [0, -4, 3] = true := by decide +kernel
theorem subd5_0_439 : subd5_0 [0, -4, 4] = true := by decide +kernel
theorem subd5_0_440 : subd5_0 [0, -4, 5] = true := by decide +kernel
theorem subd5_0_441 : subd5_0 [0, -4, 6] = true := by decide +kernel
theorem subd5_0_442 : subd5_0 [0, -4, 7] = true := by decide +kernel
theorem subd5_0_443 : subd5_0 [0, -4, 8] = true := by decide +kernel
theorem subd5_0_444 : subd5_0 [0, -3, -8] = true := by decide +kernel
theorem subd5_0_445 : subd5_0 [0, -3, -7] = true := by decide +kernel
theorem subd5_0_446 : subd5_0 [0, -3, -6] = true := by decide +kernel
theorem subd5_0_447 : subd5_0 [0, -3, -5] = true := by decide +kernel
theorem sbd5_0_13 : ∀ q ∈ blkd5_0_13, subd5_0 q = true := by
  unfold blkd5_0_13
  exact List.forall_mem_cons.2 ⟨subd5_0_416, List.forall_mem_cons.2 ⟨subd5_0_417, List.forall_mem_cons.2 ⟨subd5_0_418, List.forall_mem_cons.2 ⟨subd5_0_419, List.forall_mem_cons.2 ⟨subd5_0_420, List.forall_mem_cons.2 ⟨subd5_0_421, List.forall_mem_cons.2 ⟨subd5_0_422, List.forall_mem_cons.2 ⟨subd5_0_423, List.forall_mem_cons.2 ⟨subd5_0_424, List.forall_mem_cons.2 ⟨subd5_0_425, List.forall_mem_cons.2 ⟨subd5_0_426, List.forall_mem_cons.2 ⟨subd5_0_427, List.forall_mem_cons.2 ⟨subd5_0_428, List.forall_mem_cons.2 ⟨subd5_0_429, List.forall_mem_cons.2 ⟨subd5_0_430, List.forall_mem_cons.2 ⟨subd5_0_431, List.forall_mem_cons.2 ⟨subd5_0_432, List.forall_mem_cons.2 ⟨subd5_0_433, List.forall_mem_cons.2 ⟨subd5_0_434, List.forall_mem_cons.2 ⟨subd5_0_435, List.forall_mem_cons.2 ⟨subd5_0_436, List.forall_mem_cons.2 ⟨subd5_0_437, List.forall_mem_cons.2 ⟨subd5_0_438, List.forall_mem_cons.2 ⟨subd5_0_439, List.forall_mem_cons.2 ⟨subd5_0_440, List.forall_mem_cons.2 ⟨subd5_0_441, List.forall_mem_cons.2 ⟨subd5_0_442, List.forall_mem_cons.2 ⟨subd5_0_443, List.forall_mem_cons.2 ⟨subd5_0_444, List.forall_mem_cons.2 ⟨subd5_0_445, List.forall_mem_cons.2 ⟨subd5_0_446, List.forall_mem_cons.2 ⟨subd5_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_448 : subd5_0 [0, -3, -4] = true := by decide +kernel
theorem subd5_0_449 : subd5_0 [0, -3, -3] = true := by decide +kernel
theorem subd5_0_450 : subd5_0 [0, -3, -2] = true := by decide +kernel
theorem subd5_0_451 : subd5_0 [0, -3, -1] = true := by decide +kernel
theorem subd5_0_452 : subd5_0 [0, -3, 0] = true := by decide +kernel
theorem subd5_0_453 : subd5_0 [0, -3, 1] = true := by decide +kernel
theorem subd5_0_454 : subd5_0 [0, -3, 2] = true := by decide +kernel
theorem subd5_0_455 : subd5_0 [0, -3, 3] = true := by decide +kernel
theorem subd5_0_456 : subd5_0 [0, -3, 4] = true := by decide +kernel
theorem subd5_0_457 : subd5_0 [0, -3, 5] = true := by decide +kernel
theorem subd5_0_458 : subd5_0 [0, -3, 6] = true := by decide +kernel
theorem subd5_0_459 : subd5_0 [0, -3, 7] = true := by decide +kernel
theorem subd5_0_460 : subd5_0 [0, -3, 8] = true := by decide +kernel
theorem subd5_0_461 : subd5_0 [0, -3, 9] = true := by decide +kernel
theorem subd5_0_462 : subd5_0 [0, -2, -9] = true := by decide +kernel
theorem subd5_0_463 : subd5_0 [0, -2, -8] = true := by decide +kernel
theorem subd5_0_464 : subd5_0 [0, -2, -7] = true := by decide +kernel
theorem subd5_0_465 : subd5_0 [0, -2, -6] = true := by decide +kernel
theorem subd5_0_466 : subd5_0 [0, -2, -5] = true := by decide +kernel
theorem subd5_0_467 : subd5_0 [0, -2, -4] = true := by decide +kernel
theorem subd5_0_468 : subd5_0 [0, -2, -3] = true := by decide +kernel
theorem subd5_0_469 : subd5_0 [0, -2, -2] = true := by decide +kernel
theorem subd5_0_470 : subd5_0 [0, -2, -1] = true := by decide +kernel
theorem subd5_0_471 : subd5_0 [0, -2, 0] = true := by decide +kernel
theorem subd5_0_472 : subd5_0 [0, -2, 1] = true := by decide +kernel
theorem subd5_0_473 : subd5_0 [0, -2, 2] = true := by decide +kernel
theorem subd5_0_474 : subd5_0 [0, -2, 3] = true := by decide +kernel
theorem subd5_0_475 : subd5_0 [0, -2, 4] = true := by decide +kernel
theorem subd5_0_476 : subd5_0 [0, -2, 5] = true := by decide +kernel
theorem subd5_0_477 : subd5_0 [0, -2, 6] = true := by decide +kernel
theorem subd5_0_478 : subd5_0 [0, -2, 7] = true := by decide +kernel
theorem subd5_0_479 : subd5_0 [0, -2, 8] = true := by decide +kernel
theorem sbd5_0_14 : ∀ q ∈ blkd5_0_14, subd5_0 q = true := by
  unfold blkd5_0_14
  exact List.forall_mem_cons.2 ⟨subd5_0_448, List.forall_mem_cons.2 ⟨subd5_0_449, List.forall_mem_cons.2 ⟨subd5_0_450, List.forall_mem_cons.2 ⟨subd5_0_451, List.forall_mem_cons.2 ⟨subd5_0_452, List.forall_mem_cons.2 ⟨subd5_0_453, List.forall_mem_cons.2 ⟨subd5_0_454, List.forall_mem_cons.2 ⟨subd5_0_455, List.forall_mem_cons.2 ⟨subd5_0_456, List.forall_mem_cons.2 ⟨subd5_0_457, List.forall_mem_cons.2 ⟨subd5_0_458, List.forall_mem_cons.2 ⟨subd5_0_459, List.forall_mem_cons.2 ⟨subd5_0_460, List.forall_mem_cons.2 ⟨subd5_0_461, List.forall_mem_cons.2 ⟨subd5_0_462, List.forall_mem_cons.2 ⟨subd5_0_463, List.forall_mem_cons.2 ⟨subd5_0_464, List.forall_mem_cons.2 ⟨subd5_0_465, List.forall_mem_cons.2 ⟨subd5_0_466, List.forall_mem_cons.2 ⟨subd5_0_467, List.forall_mem_cons.2 ⟨subd5_0_468, List.forall_mem_cons.2 ⟨subd5_0_469, List.forall_mem_cons.2 ⟨subd5_0_470, List.forall_mem_cons.2 ⟨subd5_0_471, List.forall_mem_cons.2 ⟨subd5_0_472, List.forall_mem_cons.2 ⟨subd5_0_473, List.forall_mem_cons.2 ⟨subd5_0_474, List.forall_mem_cons.2 ⟨subd5_0_475, List.forall_mem_cons.2 ⟨subd5_0_476, List.forall_mem_cons.2 ⟨subd5_0_477, List.forall_mem_cons.2 ⟨subd5_0_478, List.forall_mem_cons.2 ⟨subd5_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_480 : subd5_0 [0, -2, 9] = true := by decide +kernel
theorem subd5_0_481 : subd5_0 [0, -1, -10] = true := by decide +kernel
theorem subd5_0_482 : subd5_0 [0, -1, -9] = true := by decide +kernel
theorem subd5_0_483 : subd5_0 [0, -1, -8] = true := by decide +kernel
theorem subd5_0_484 : subd5_0 [0, -1, -7] = true := by decide +kernel
theorem subd5_0_485 : subd5_0 [0, -1, -6] = true := by decide +kernel
theorem subd5_0_486 : subd5_0 [0, -1, -5] = true := by decide +kernel
theorem subd5_0_487 : subd5_0 [0, -1, -4] = true := by decide +kernel
theorem subd5_0_488 : subd5_0 [0, -1, -3] = true := by decide +kernel
theorem subd5_0_489 : subd5_0 [0, -1, -2] = true := by decide +kernel
theorem subd5_0_490 : subd5_0 [0, -1, -1] = true := by decide +kernel
theorem subd5_0_491 : subd5_0 [0, -1, 0] = true := by decide +kernel
theorem subd5_0_492 : subd5_0 [0, -1, 1] = true := by decide +kernel
theorem subd5_0_493 : subd5_0 [0, -1, 2] = true := by decide +kernel
theorem subd5_0_494 : subd5_0 [0, -1, 3] = true := by decide +kernel
theorem subd5_0_495 : subd5_0 [0, -1, 4] = true := by decide +kernel
theorem subd5_0_496 : subd5_0 [0, -1, 5] = true := by decide +kernel
theorem subd5_0_497 : subd5_0 [0, -1, 6] = true := by decide +kernel
theorem subd5_0_498 : subd5_0 [0, -1, 7] = true := by decide +kernel
theorem subd5_0_499 : subd5_0 [0, -1, 8] = true := by decide +kernel
theorem subd5_0_500 : subd5_0 [0, -1, 9] = true := by decide +kernel
theorem subd5_0_501 : subd5_0 [0, 0, -10] = true := by decide +kernel
theorem subd5_0_502 : subd5_0 [0, 0, -9] = true := by decide +kernel
theorem subd5_0_503 : subd5_0 [0, 0, -8] = true := by decide +kernel
theorem subd5_0_504 : subd5_0 [0, 0, -7] = true := by decide +kernel
theorem subd5_0_505 : subd5_0 [0, 0, -6] = true := by decide +kernel
theorem subd5_0_506 : subd5_0 [0, 0, -5] = true := by decide +kernel
theorem subd5_0_507 : subd5_0 [0, 0, -4] = true := by decide +kernel
theorem subd5_0_508 : subd5_0 [0, 0, -3] = true := by decide +kernel
theorem subd5_0_509 : subd5_0 [0, 0, -2] = true := by decide +kernel
theorem subd5_0_510 : subd5_0 [0, 0, -1] = true := by decide +kernel
theorem subd5_0_511 : subd5_0 [0, 0, 0] = true := by decide +kernel
theorem sbd5_0_15 : ∀ q ∈ blkd5_0_15, subd5_0 q = true := by
  unfold blkd5_0_15
  exact List.forall_mem_cons.2 ⟨subd5_0_480, List.forall_mem_cons.2 ⟨subd5_0_481, List.forall_mem_cons.2 ⟨subd5_0_482, List.forall_mem_cons.2 ⟨subd5_0_483, List.forall_mem_cons.2 ⟨subd5_0_484, List.forall_mem_cons.2 ⟨subd5_0_485, List.forall_mem_cons.2 ⟨subd5_0_486, List.forall_mem_cons.2 ⟨subd5_0_487, List.forall_mem_cons.2 ⟨subd5_0_488, List.forall_mem_cons.2 ⟨subd5_0_489, List.forall_mem_cons.2 ⟨subd5_0_490, List.forall_mem_cons.2 ⟨subd5_0_491, List.forall_mem_cons.2 ⟨subd5_0_492, List.forall_mem_cons.2 ⟨subd5_0_493, List.forall_mem_cons.2 ⟨subd5_0_494, List.forall_mem_cons.2 ⟨subd5_0_495, List.forall_mem_cons.2 ⟨subd5_0_496, List.forall_mem_cons.2 ⟨subd5_0_497, List.forall_mem_cons.2 ⟨subd5_0_498, List.forall_mem_cons.2 ⟨subd5_0_499, List.forall_mem_cons.2 ⟨subd5_0_500, List.forall_mem_cons.2 ⟨subd5_0_501, List.forall_mem_cons.2 ⟨subd5_0_502, List.forall_mem_cons.2 ⟨subd5_0_503, List.forall_mem_cons.2 ⟨subd5_0_504, List.forall_mem_cons.2 ⟨subd5_0_505, List.forall_mem_cons.2 ⟨subd5_0_506, List.forall_mem_cons.2 ⟨subd5_0_507, List.forall_mem_cons.2 ⟨subd5_0_508, List.forall_mem_cons.2 ⟨subd5_0_509, List.forall_mem_cons.2 ⟨subd5_0_510, List.forall_mem_cons.2 ⟨subd5_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
