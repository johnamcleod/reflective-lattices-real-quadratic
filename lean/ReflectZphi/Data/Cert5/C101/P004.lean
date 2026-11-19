import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_32 : subd8_1 [-1, 0, 0] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [-1, 0, 1] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [-1, 0, 2] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [-1, 0, 3] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [-1, 0, 4] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [-1, 0, 5] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [-1, 0, 6] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [-1, 0, 7] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [-1, 0, 8] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [-1, 0, 9] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [-1, 0, 10] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [-1, 1, -12] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [-1, 1, -11] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [-1, 1, -10] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [-1, 1, -9] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [-1, 1, -8] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [-1, 1, -7] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [-1, 1, -6] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [-1, 1, -5] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [-1, 1, -4] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [-1, 1, -3] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [-1, 1, -2] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [-1, 1, -1] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [-1, 1, 0] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [-1, 1, 1] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [-1, 1, 2] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [-1, 1, 3] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [-1, 1, 4] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [-1, 1, 5] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [-1, 1, 6] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [-1, 1, 7] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [-1, 1, 8] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [-1, 1, 9] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [-1, 1, 10] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [-1, 2, -9] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [-1, 2, -8] = true := by decide +kernel
theorem subd8_1_68 : subd8_1 [-1, 2, -7] = true := by decide +kernel
theorem subd8_1_69 : subd8_1 [-1, 2, -6] = true := by decide +kernel
theorem subd8_1_70 : subd8_1 [-1, 2, -5] = true := by decide +kernel
theorem subd8_1_71 : subd8_1 [-1, 2, -4] = true := by decide +kernel
theorem subd8_1_72 : subd8_1 [-1, 2, -3] = true := by decide +kernel
theorem subd8_1_73 : subd8_1 [-1, 2, -2] = true := by decide +kernel
theorem subd8_1_74 : subd8_1 [-1, 2, -1] = true := by decide +kernel
theorem subd8_1_75 : subd8_1 [-1, 2, 0] = true := by decide +kernel
theorem subd8_1_76 : subd8_1 [-1, 2, 1] = true := by decide +kernel
theorem subd8_1_77 : subd8_1 [-1, 2, 2] = true := by decide +kernel
theorem subd8_1_78 : subd8_1 [-1, 2, 3] = true := by decide +kernel
theorem subd8_1_79 : subd8_1 [-1, 2, 4] = true := by decide +kernel
theorem subd8_1_80 : subd8_1 [-1, 2, 5] = true := by decide +kernel
theorem subd8_1_81 : subd8_1 [-1, 2, 6] = true := by decide +kernel
theorem subd8_1_82 : subd8_1 [-1, 2, 7] = true := by decide +kernel
theorem subd8_1_83 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_84 : subd8_1 [0, -2, -8] = true := by decide +kernel
theorem subd8_1_85 : subd8_1 [0, -2, -7] = true := by decide +kernel
theorem subd8_1_86 : subd8_1 [0, -2, -6] = true := by decide +kernel
theorem subd8_1_87 : subd8_1 [0, -2, -5] = true := by decide +kernel
theorem subd8_1_88 : subd8_1 [0, -2, -4] = true := by decide +kernel
theorem subd8_1_89 : subd8_1 [0, -2, -3] = true := by decide +kernel
theorem subd8_1_90 : subd8_1 [0, -2, -2] = true := by decide +kernel
theorem subd8_1_91 : subd8_1 [0, -2, -1] = true := by decide +kernel
theorem subd8_1_92 : subd8_1 [0, -2, 0] = true := by decide +kernel
theorem subd8_1_93 : subd8_1 [0, -2, 1] = true := by decide +kernel
theorem subd8_1_94 : subd8_1 [0, -2, 2] = true := by decide +kernel
theorem subd8_1_95 : subd8_1 [0, -2, 3] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_cons.2 ⟨subd8_1_68, List.forall_mem_cons.2 ⟨subd8_1_69, List.forall_mem_cons.2 ⟨subd8_1_70, List.forall_mem_cons.2 ⟨subd8_1_71, List.forall_mem_cons.2 ⟨subd8_1_72, List.forall_mem_cons.2 ⟨subd8_1_73, List.forall_mem_cons.2 ⟨subd8_1_74, List.forall_mem_cons.2 ⟨subd8_1_75, List.forall_mem_cons.2 ⟨subd8_1_76, List.forall_mem_cons.2 ⟨subd8_1_77, List.forall_mem_cons.2 ⟨subd8_1_78, List.forall_mem_cons.2 ⟨subd8_1_79, List.forall_mem_cons.2 ⟨subd8_1_80, List.forall_mem_cons.2 ⟨subd8_1_81, List.forall_mem_cons.2 ⟨subd8_1_82, List.forall_mem_cons.2 ⟨subd8_1_83, List.forall_mem_cons.2 ⟨subd8_1_84, List.forall_mem_cons.2 ⟨subd8_1_85, List.forall_mem_cons.2 ⟨subd8_1_86, List.forall_mem_cons.2 ⟨subd8_1_87, List.forall_mem_cons.2 ⟨subd8_1_88, List.forall_mem_cons.2 ⟨subd8_1_89, List.forall_mem_cons.2 ⟨subd8_1_90, List.forall_mem_cons.2 ⟨subd8_1_91, List.forall_mem_cons.2 ⟨subd8_1_92, List.forall_mem_cons.2 ⟨subd8_1_93, List.forall_mem_cons.2 ⟨subd8_1_94, List.forall_mem_cons.2 ⟨subd8_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_96 : subd8_1 [0, -2, 4] = true := by decide +kernel
theorem subd8_1_97 : subd8_1 [0, -2, 5] = true := by decide +kernel
theorem subd8_1_98 : subd8_1 [0, -2, 6] = true := by decide +kernel
theorem subd8_1_99 : subd8_1 [0, -2, 7] = true := by decide +kernel
theorem subd8_1_100 : subd8_1 [0, -1, -12] = true := by decide +kernel
theorem subd8_1_101 : subd8_1 [0, -1, -11] = true := by decide +kernel
theorem subd8_1_102 : subd8_1 [0, -1, -10] = true := by decide +kernel
theorem subd8_1_103 : subd8_1 [0, -1, -9] = true := by decide +kernel
theorem subd8_1_104 : subd8_1 [0, -1, -8] = true := by decide +kernel
theorem subd8_1_105 : subd8_1 [0, -1, -7] = true := by decide +kernel
theorem subd8_1_106 : subd8_1 [0, -1, -6] = true := by decide +kernel
theorem subd8_1_107 : subd8_1 [0, -1, -5] = true := by decide +kernel
theorem subd8_1_108 : subd8_1 [0, -1, -4] = true := by decide +kernel
theorem subd8_1_109 : subd8_1 [0, -1, -3] = true := by decide +kernel
theorem subd8_1_110 : subd8_1 [0, -1, -2] = true := by decide +kernel
theorem subd8_1_111 : subd8_1 [0, -1, -1] = true := by decide +kernel
theorem subd8_1_112 : subd8_1 [0, -1, 0] = true := by decide +kernel
theorem subd8_1_113 : subd8_1 [0, -1, 1] = true := by decide +kernel
theorem subd8_1_114 : subd8_1 [0, -1, 2] = true := by decide +kernel
theorem subd8_1_115 : subd8_1 [0, -1, 3] = true := by decide +kernel
theorem subd8_1_116 : subd8_1 [0, -1, 4] = true := by decide +kernel
theorem subd8_1_117 : subd8_1 [0, -1, 5] = true := by decide +kernel
theorem subd8_1_118 : subd8_1 [0, -1, 6] = true := by decide +kernel
theorem subd8_1_119 : subd8_1 [0, -1, 7] = true := by decide +kernel
theorem subd8_1_120 : subd8_1 [0, -1, 8] = true := by decide +kernel
theorem subd8_1_121 : subd8_1 [0, -1, 9] = true := by decide +kernel
theorem subd8_1_122 : subd8_1 [0, -1, 10] = true := by decide +kernel
theorem subd8_1_123 : subd8_1 [0, -1, 11] = true := by decide +kernel
theorem subd8_1_124 : subd8_1 [0, 0, -13] = true := by decide +kernel
theorem subd8_1_125 : subd8_1 [0, 0, -12] = true := by decide +kernel
theorem subd8_1_126 : subd8_1 [0, 0, -11] = true := by decide +kernel
theorem subd8_1_127 : subd8_1 [0, 0, -10] = true := by decide +kernel
theorem sbd8_1_3 : ∀ q ∈ blkd8_1_3, subd8_1 q = true := by
  unfold blkd8_1_3
  exact List.forall_mem_cons.2 ⟨subd8_1_96, List.forall_mem_cons.2 ⟨subd8_1_97, List.forall_mem_cons.2 ⟨subd8_1_98, List.forall_mem_cons.2 ⟨subd8_1_99, List.forall_mem_cons.2 ⟨subd8_1_100, List.forall_mem_cons.2 ⟨subd8_1_101, List.forall_mem_cons.2 ⟨subd8_1_102, List.forall_mem_cons.2 ⟨subd8_1_103, List.forall_mem_cons.2 ⟨subd8_1_104, List.forall_mem_cons.2 ⟨subd8_1_105, List.forall_mem_cons.2 ⟨subd8_1_106, List.forall_mem_cons.2 ⟨subd8_1_107, List.forall_mem_cons.2 ⟨subd8_1_108, List.forall_mem_cons.2 ⟨subd8_1_109, List.forall_mem_cons.2 ⟨subd8_1_110, List.forall_mem_cons.2 ⟨subd8_1_111, List.forall_mem_cons.2 ⟨subd8_1_112, List.forall_mem_cons.2 ⟨subd8_1_113, List.forall_mem_cons.2 ⟨subd8_1_114, List.forall_mem_cons.2 ⟨subd8_1_115, List.forall_mem_cons.2 ⟨subd8_1_116, List.forall_mem_cons.2 ⟨subd8_1_117, List.forall_mem_cons.2 ⟨subd8_1_118, List.forall_mem_cons.2 ⟨subd8_1_119, List.forall_mem_cons.2 ⟨subd8_1_120, List.forall_mem_cons.2 ⟨subd8_1_121, List.forall_mem_cons.2 ⟨subd8_1_122, List.forall_mem_cons.2 ⟨subd8_1_123, List.forall_mem_cons.2 ⟨subd8_1_124, List.forall_mem_cons.2 ⟨subd8_1_125, List.forall_mem_cons.2 ⟨subd8_1_126, List.forall_mem_cons.2 ⟨subd8_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_128 : subd8_1 [0, 0, -9] = true := by decide +kernel
theorem subd8_1_129 : subd8_1 [0, 0, -8] = true := by decide +kernel
theorem subd8_1_130 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_131 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_132 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_133 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_134 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_135 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_136 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_137 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_138 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_139 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_140 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_141 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_142 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_143 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem subd8_1_144 : subd8_1 [0, 0, 7] = true := by decide +kernel
theorem subd8_1_145 : subd8_1 [0, 0, 8] = true := by decide +kernel
theorem subd8_1_146 : subd8_1 [0, 0, 9] = true := by decide +kernel
theorem subd8_1_147 : subd8_1 [0, 0, 10] = true := by decide +kernel
theorem subd8_1_148 : subd8_1 [0, 0, 11] = true := by decide +kernel
theorem subd8_1_149 : subd8_1 [0, 0, 12] = true := by decide +kernel
theorem subd8_1_150 : subd8_1 [0, 1, -12] = true := by decide +kernel
theorem subd8_1_151 : subd8_1 [0, 1, -11] = true := by decide +kernel
theorem subd8_1_152 : subd8_1 [0, 1, -10] = true := by decide +kernel
theorem subd8_1_153 : subd8_1 [0, 1, -9] = true := by decide +kernel
theorem subd8_1_154 : subd8_1 [0, 1, -8] = true := by decide +kernel
theorem subd8_1_155 : subd8_1 [0, 1, -7] = true := by decide +kernel
theorem subd8_1_156 : subd8_1 [0, 1, -6] = true := by decide +kernel
theorem subd8_1_157 : subd8_1 [0, 1, -5] = true := by decide +kernel
theorem subd8_1_158 : subd8_1 [0, 1, -4] = true := by decide +kernel
theorem subd8_1_159 : subd8_1 [0, 1, -3] = true := by decide +kernel
theorem sbd8_1_4 : ∀ q ∈ blkd8_1_4, subd8_1 q = true := by
  unfold blkd8_1_4
  exact List.forall_mem_cons.2 ⟨subd8_1_128, List.forall_mem_cons.2 ⟨subd8_1_129, List.forall_mem_cons.2 ⟨subd8_1_130, List.forall_mem_cons.2 ⟨subd8_1_131, List.forall_mem_cons.2 ⟨subd8_1_132, List.forall_mem_cons.2 ⟨subd8_1_133, List.forall_mem_cons.2 ⟨subd8_1_134, List.forall_mem_cons.2 ⟨subd8_1_135, List.forall_mem_cons.2 ⟨subd8_1_136, List.forall_mem_cons.2 ⟨subd8_1_137, List.forall_mem_cons.2 ⟨subd8_1_138, List.forall_mem_cons.2 ⟨subd8_1_139, List.forall_mem_cons.2 ⟨subd8_1_140, List.forall_mem_cons.2 ⟨subd8_1_141, List.forall_mem_cons.2 ⟨subd8_1_142, List.forall_mem_cons.2 ⟨subd8_1_143, List.forall_mem_cons.2 ⟨subd8_1_144, List.forall_mem_cons.2 ⟨subd8_1_145, List.forall_mem_cons.2 ⟨subd8_1_146, List.forall_mem_cons.2 ⟨subd8_1_147, List.forall_mem_cons.2 ⟨subd8_1_148, List.forall_mem_cons.2 ⟨subd8_1_149, List.forall_mem_cons.2 ⟨subd8_1_150, List.forall_mem_cons.2 ⟨subd8_1_151, List.forall_mem_cons.2 ⟨subd8_1_152, List.forall_mem_cons.2 ⟨subd8_1_153, List.forall_mem_cons.2 ⟨subd8_1_154, List.forall_mem_cons.2 ⟨subd8_1_155, List.forall_mem_cons.2 ⟨subd8_1_156, List.forall_mem_cons.2 ⟨subd8_1_157, List.forall_mem_cons.2 ⟨subd8_1_158, List.forall_mem_cons.2 ⟨subd8_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_160 : subd8_1 [0, 1, -2] = true := by decide +kernel
theorem subd8_1_161 : subd8_1 [0, 1, -1] = true := by decide +kernel
theorem subd8_1_162 : subd8_1 [0, 1, 0] = true := by decide +kernel
theorem subd8_1_163 : subd8_1 [0, 1, 1] = true := by decide +kernel
theorem subd8_1_164 : subd8_1 [0, 1, 2] = true := by decide +kernel
theorem subd8_1_165 : subd8_1 [0, 1, 3] = true := by decide +kernel
theorem subd8_1_166 : subd8_1 [0, 1, 4] = true := by decide +kernel
theorem subd8_1_167 : subd8_1 [0, 1, 5] = true := by decide +kernel
theorem subd8_1_168 : subd8_1 [0, 1, 6] = true := by decide +kernel
theorem subd8_1_169 : subd8_1 [0, 1, 7] = true := by decide +kernel
theorem subd8_1_170 : subd8_1 [0, 1, 8] = true := by decide +kernel
theorem subd8_1_171 : subd8_1 [0, 1, 9] = true := by decide +kernel
theorem subd8_1_172 : subd8_1 [0, 1, 10] = true := by decide +kernel
theorem subd8_1_173 : subd8_1 [0, 1, 11] = true := by decide +kernel
theorem subd8_1_174 : subd8_1 [0, 2, -8] = true := by decide +kernel
theorem subd8_1_175 : subd8_1 [0, 2, -7] = true := by decide +kernel
theorem subd8_1_176 : subd8_1 [0, 2, -6] = true := by decide +kernel
theorem subd8_1_177 : subd8_1 [0, 2, -5] = true := by decide +kernel
theorem subd8_1_178 : subd8_1 [0, 2, -4] = true := by decide +kernel
theorem subd8_1_179 : subd8_1 [0, 2, -3] = true := by decide +kernel
theorem subd8_1_180 : subd8_1 [0, 2, -2] = true := by decide +kernel
theorem subd8_1_181 : subd8_1 [0, 2, -1] = true := by decide +kernel
theorem subd8_1_182 : subd8_1 [0, 2, 0] = true := by decide +kernel
theorem subd8_1_183 : subd8_1 [0, 2, 1] = true := by decide +kernel
theorem subd8_1_184 : subd8_1 [0, 2, 2] = true := by decide +kernel
theorem subd8_1_185 : subd8_1 [0, 2, 3] = true := by decide +kernel
theorem subd8_1_186 : subd8_1 [0, 2, 4] = true := by decide +kernel
theorem subd8_1_187 : subd8_1 [0, 2, 5] = true := by decide +kernel
theorem subd8_1_188 : subd8_1 [0, 2, 6] = true := by decide +kernel
theorem subd8_1_189 : subd8_1 [0, 2, 7] = true := by decide +kernel
theorem subd8_1_190 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_191 : subd8_1 [1, -2, -8] = true := by decide +kernel
theorem sbd8_1_5 : ∀ q ∈ blkd8_1_5, subd8_1 q = true := by
  unfold blkd8_1_5
  exact List.forall_mem_cons.2 ⟨subd8_1_160, List.forall_mem_cons.2 ⟨subd8_1_161, List.forall_mem_cons.2 ⟨subd8_1_162, List.forall_mem_cons.2 ⟨subd8_1_163, List.forall_mem_cons.2 ⟨subd8_1_164, List.forall_mem_cons.2 ⟨subd8_1_165, List.forall_mem_cons.2 ⟨subd8_1_166, List.forall_mem_cons.2 ⟨subd8_1_167, List.forall_mem_cons.2 ⟨subd8_1_168, List.forall_mem_cons.2 ⟨subd8_1_169, List.forall_mem_cons.2 ⟨subd8_1_170, List.forall_mem_cons.2 ⟨subd8_1_171, List.forall_mem_cons.2 ⟨subd8_1_172, List.forall_mem_cons.2 ⟨subd8_1_173, List.forall_mem_cons.2 ⟨subd8_1_174, List.forall_mem_cons.2 ⟨subd8_1_175, List.forall_mem_cons.2 ⟨subd8_1_176, List.forall_mem_cons.2 ⟨subd8_1_177, List.forall_mem_cons.2 ⟨subd8_1_178, List.forall_mem_cons.2 ⟨subd8_1_179, List.forall_mem_cons.2 ⟨subd8_1_180, List.forall_mem_cons.2 ⟨subd8_1_181, List.forall_mem_cons.2 ⟨subd8_1_182, List.forall_mem_cons.2 ⟨subd8_1_183, List.forall_mem_cons.2 ⟨subd8_1_184, List.forall_mem_cons.2 ⟨subd8_1_185, List.forall_mem_cons.2 ⟨subd8_1_186, List.forall_mem_cons.2 ⟨subd8_1_187, List.forall_mem_cons.2 ⟨subd8_1_188, List.forall_mem_cons.2 ⟨subd8_1_189, List.forall_mem_cons.2 ⟨subd8_1_190, List.forall_mem_cons.2 ⟨subd8_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_192 : subd8_1 [1, -2, -7] = true := by decide +kernel
theorem subd8_1_193 : subd8_1 [1, -2, -6] = true := by decide +kernel
theorem subd8_1_194 : subd8_1 [1, -2, -5] = true := by decide +kernel
theorem subd8_1_195 : subd8_1 [1, -2, -4] = true := by decide +kernel
theorem subd8_1_196 : subd8_1 [1, -2, -3] = true := by decide +kernel
theorem subd8_1_197 : subd8_1 [1, -2, -2] = true := by decide +kernel
theorem subd8_1_198 : subd8_1 [1, -2, -1] = true := by decide +kernel
theorem subd8_1_199 : subd8_1 [1, -2, 0] = true := by decide +kernel
theorem subd8_1_200 : subd8_1 [1, -2, 1] = true := by decide +kernel
theorem subd8_1_201 : subd8_1 [1, -2, 2] = true := by decide +kernel
theorem subd8_1_202 : subd8_1 [1, -2, 3] = true := by decide +kernel
theorem subd8_1_203 : subd8_1 [1, -2, 4] = true := by decide +kernel
theorem subd8_1_204 : subd8_1 [1, -2, 5] = true := by decide +kernel
theorem subd8_1_205 : subd8_1 [1, -2, 6] = true := by decide +kernel
theorem subd8_1_206 : subd8_1 [1, -2, 7] = true := by decide +kernel
theorem subd8_1_207 : subd8_1 [1, -2, 8] = true := by decide +kernel
theorem subd8_1_208 : subd8_1 [1, -1, -11] = true := by decide +kernel
theorem subd8_1_209 : subd8_1 [1, -1, -10] = true := by decide +kernel
theorem subd8_1_210 : subd8_1 [1, -1, -9] = true := by decide +kernel
theorem subd8_1_211 : subd8_1 [1, -1, -8] = true := by decide +kernel
theorem subd8_1_212 : subd8_1 [1, -1, -7] = true := by decide +kernel
theorem subd8_1_213 : subd8_1 [1, -1, -6] = true := by decide +kernel
theorem subd8_1_214 : subd8_1 [1, -1, -5] = true := by decide +kernel
theorem subd8_1_215 : subd8_1 [1, -1, -4] = true := by decide +kernel
theorem subd8_1_216 : subd8_1 [1, -1, -3] = true := by decide +kernel
theorem subd8_1_217 : subd8_1 [1, -1, -2] = true := by decide +kernel
theorem subd8_1_218 : subd8_1 [1, -1, -1] = true := by decide +kernel
theorem subd8_1_219 : subd8_1 [1, -1, 0] = true := by decide +kernel
theorem subd8_1_220 : subd8_1 [1, -1, 1] = true := by decide +kernel
theorem subd8_1_221 : subd8_1 [1, -1, 2] = true := by decide +kernel
theorem subd8_1_222 : subd8_1 [1, -1, 3] = true := by decide +kernel
theorem subd8_1_223 : subd8_1 [1, -1, 4] = true := by decide +kernel
theorem sbd8_1_6 : ∀ q ∈ blkd8_1_6, subd8_1 q = true := by
  unfold blkd8_1_6
  exact List.forall_mem_cons.2 ⟨subd8_1_192, List.forall_mem_cons.2 ⟨subd8_1_193, List.forall_mem_cons.2 ⟨subd8_1_194, List.forall_mem_cons.2 ⟨subd8_1_195, List.forall_mem_cons.2 ⟨subd8_1_196, List.forall_mem_cons.2 ⟨subd8_1_197, List.forall_mem_cons.2 ⟨subd8_1_198, List.forall_mem_cons.2 ⟨subd8_1_199, List.forall_mem_cons.2 ⟨subd8_1_200, List.forall_mem_cons.2 ⟨subd8_1_201, List.forall_mem_cons.2 ⟨subd8_1_202, List.forall_mem_cons.2 ⟨subd8_1_203, List.forall_mem_cons.2 ⟨subd8_1_204, List.forall_mem_cons.2 ⟨subd8_1_205, List.forall_mem_cons.2 ⟨subd8_1_206, List.forall_mem_cons.2 ⟨subd8_1_207, List.forall_mem_cons.2 ⟨subd8_1_208, List.forall_mem_cons.2 ⟨subd8_1_209, List.forall_mem_cons.2 ⟨subd8_1_210, List.forall_mem_cons.2 ⟨subd8_1_211, List.forall_mem_cons.2 ⟨subd8_1_212, List.forall_mem_cons.2 ⟨subd8_1_213, List.forall_mem_cons.2 ⟨subd8_1_214, List.forall_mem_cons.2 ⟨subd8_1_215, List.forall_mem_cons.2 ⟨subd8_1_216, List.forall_mem_cons.2 ⟨subd8_1_217, List.forall_mem_cons.2 ⟨subd8_1_218, List.forall_mem_cons.2 ⟨subd8_1_219, List.forall_mem_cons.2 ⟨subd8_1_220, List.forall_mem_cons.2 ⟨subd8_1_221, List.forall_mem_cons.2 ⟨subd8_1_222, List.forall_mem_cons.2 ⟨subd8_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_224 : subd8_1 [1, -1, 5] = true := by decide +kernel
theorem subd8_1_225 : subd8_1 [1, -1, 6] = true := by decide +kernel
theorem subd8_1_226 : subd8_1 [1, -1, 7] = true := by decide +kernel
theorem subd8_1_227 : subd8_1 [1, -1, 8] = true := by decide +kernel
theorem subd8_1_228 : subd8_1 [1, -1, 9] = true := by decide +kernel
theorem subd8_1_229 : subd8_1 [1, -1, 10] = true := by decide +kernel
theorem subd8_1_230 : subd8_1 [1, -1, 11] = true := by decide +kernel
theorem subd8_1_231 : subd8_1 [1, 0, -11] = true := by decide +kernel
theorem subd8_1_232 : subd8_1 [1, 0, -10] = true := by decide +kernel
theorem subd8_1_233 : subd8_1 [1, 0, -9] = true := by decide +kernel
theorem subd8_1_234 : subd8_1 [1, 0, -8] = true := by decide +kernel
theorem subd8_1_235 : subd8_1 [1, 0, -7] = true := by decide +kernel
theorem subd8_1_236 : subd8_1 [1, 0, -6] = true := by decide +kernel
theorem subd8_1_237 : subd8_1 [1, 0, -5] = true := by decide +kernel
theorem subd8_1_238 : subd8_1 [1, 0, -4] = true := by decide +kernel
theorem subd8_1_239 : subd8_1 [1, 0, -3] = true := by decide +kernel
theorem subd8_1_240 : subd8_1 [1, 0, -2] = true := by decide +kernel
theorem subd8_1_241 : subd8_1 [1, 0, -1] = true := by decide +kernel
theorem subd8_1_242 : subd8_1 [1, 0, 0] = true := by decide +kernel
theorem subd8_1_243 : subd8_1 [1, 0, 1] = true := by decide +kernel
theorem subd8_1_244 : subd8_1 [1, 0, 2] = true := by decide +kernel
theorem subd8_1_245 : subd8_1 [1, 0, 3] = true := by decide +kernel
theorem subd8_1_246 : subd8_1 [1, 0, 4] = true := by decide +kernel
theorem subd8_1_247 : subd8_1 [1, 0, 5] = true := by decide +kernel
theorem subd8_1_248 : subd8_1 [1, 0, 6] = true := by decide +kernel
theorem subd8_1_249 : subd8_1 [1, 0, 7] = true := by decide +kernel
theorem subd8_1_250 : subd8_1 [1, 0, 8] = true := by decide +kernel
theorem subd8_1_251 : subd8_1 [1, 0, 9] = true := by decide +kernel
theorem subd8_1_252 : subd8_1 [1, 0, 10] = true := by decide +kernel
theorem subd8_1_253 : subd8_1 [1, 0, 11] = true := by decide +kernel
theorem subd8_1_254 : subd8_1 [1, 1, -9] = true := by decide +kernel
theorem subd8_1_255 : subd8_1 [1, 1, -8] = true := by decide +kernel
theorem sbd8_1_7 : ∀ q ∈ blkd8_1_7, subd8_1 q = true := by
  unfold blkd8_1_7
  exact List.forall_mem_cons.2 ⟨subd8_1_224, List.forall_mem_cons.2 ⟨subd8_1_225, List.forall_mem_cons.2 ⟨subd8_1_226, List.forall_mem_cons.2 ⟨subd8_1_227, List.forall_mem_cons.2 ⟨subd8_1_228, List.forall_mem_cons.2 ⟨subd8_1_229, List.forall_mem_cons.2 ⟨subd8_1_230, List.forall_mem_cons.2 ⟨subd8_1_231, List.forall_mem_cons.2 ⟨subd8_1_232, List.forall_mem_cons.2 ⟨subd8_1_233, List.forall_mem_cons.2 ⟨subd8_1_234, List.forall_mem_cons.2 ⟨subd8_1_235, List.forall_mem_cons.2 ⟨subd8_1_236, List.forall_mem_cons.2 ⟨subd8_1_237, List.forall_mem_cons.2 ⟨subd8_1_238, List.forall_mem_cons.2 ⟨subd8_1_239, List.forall_mem_cons.2 ⟨subd8_1_240, List.forall_mem_cons.2 ⟨subd8_1_241, List.forall_mem_cons.2 ⟨subd8_1_242, List.forall_mem_cons.2 ⟨subd8_1_243, List.forall_mem_cons.2 ⟨subd8_1_244, List.forall_mem_cons.2 ⟨subd8_1_245, List.forall_mem_cons.2 ⟨subd8_1_246, List.forall_mem_cons.2 ⟨subd8_1_247, List.forall_mem_cons.2 ⟨subd8_1_248, List.forall_mem_cons.2 ⟨subd8_1_249, List.forall_mem_cons.2 ⟨subd8_1_250, List.forall_mem_cons.2 ⟨subd8_1_251, List.forall_mem_cons.2 ⟨subd8_1_252, List.forall_mem_cons.2 ⟨subd8_1_253, List.forall_mem_cons.2 ⟨subd8_1_254, List.forall_mem_cons.2 ⟨subd8_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_256 : subd8_1 [1, 1, -7] = true := by decide +kernel
theorem subd8_1_257 : subd8_1 [1, 1, -6] = true := by decide +kernel
theorem subd8_1_258 : subd8_1 [1, 1, -5] = true := by decide +kernel
theorem subd8_1_259 : subd8_1 [1, 1, -4] = true := by decide +kernel
theorem subd8_1_260 : subd8_1 [1, 1, -3] = true := by decide +kernel
theorem subd8_1_261 : subd8_1 [1, 1, -2] = true := by decide +kernel
theorem subd8_1_262 : subd8_1 [1, 1, -1] = true := by decide +kernel
theorem subd8_1_263 : subd8_1 [1, 1, 0] = true := by decide +kernel
theorem subd8_1_264 : subd8_1 [1, 1, 1] = true := by decide +kernel
theorem subd8_1_265 : subd8_1 [1, 1, 2] = true := by decide +kernel
theorem subd8_1_266 : subd8_1 [1, 1, 3] = true := by decide +kernel
theorem subd8_1_267 : subd8_1 [1, 1, 4] = true := by decide +kernel
theorem subd8_1_268 : subd8_1 [1, 1, 5] = true := by decide +kernel
theorem subd8_1_269 : subd8_1 [1, 1, 6] = true := by decide +kernel
theorem subd8_1_270 : subd8_1 [1, 1, 7] = true := by decide +kernel
theorem subd8_1_271 : subd8_1 [1, 1, 8] = true := by decide +kernel
theorem subd8_1_272 : subd8_1 [2] = true := by decide +kernel
theorem sbd8_1_8 : ∀ q ∈ blkd8_1_8, subd8_1 q = true := by
  unfold blkd8_1_8
  exact List.forall_mem_cons.2 ⟨subd8_1_256, List.forall_mem_cons.2 ⟨subd8_1_257, List.forall_mem_cons.2 ⟨subd8_1_258, List.forall_mem_cons.2 ⟨subd8_1_259, List.forall_mem_cons.2 ⟨subd8_1_260, List.forall_mem_cons.2 ⟨subd8_1_261, List.forall_mem_cons.2 ⟨subd8_1_262, List.forall_mem_cons.2 ⟨subd8_1_263, List.forall_mem_cons.2 ⟨subd8_1_264, List.forall_mem_cons.2 ⟨subd8_1_265, List.forall_mem_cons.2 ⟨subd8_1_266, List.forall_mem_cons.2 ⟨subd8_1_267, List.forall_mem_cons.2 ⟨subd8_1_268, List.forall_mem_cons.2 ⟨subd8_1_269, List.forall_mem_cons.2 ⟨subd8_1_270, List.forall_mem_cons.2 ⟨subd8_1_271, List.forall_mem_cons.2 ⟨subd8_1_272, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-6, -5] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-6, -4] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-6, -3] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-6, -2] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-6, -1] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-6, 0] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-6, 1] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-6, 2] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-5, -6] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-5, -5] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-5, -4] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-5, -3] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-5, -2] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-5, -1] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [-5, 0] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [-5, 1] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [-5, 2] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [-5, 3] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [-4, -7] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [-4, -6] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [-4, -5] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [-4, -4] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [-4, -3] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [-4, -2] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [-4, -1] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [-4, 0] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [-4, 1] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [-4, 2] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [-4, 3] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [-4, 4] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [-3, -7] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [-3, -6] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
