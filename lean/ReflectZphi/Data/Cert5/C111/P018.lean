import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_32 : subd9_2 [-1, 0, 5] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [-1, 0, 6] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [-1, 0, 7] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [-1, 0, 8] = true := by decide +kernel
theorem subd9_2_36 : subd9_2 [-1, 0, 9] = true := by decide +kernel
theorem subd9_2_37 : subd9_2 [-1, 1, -7] = true := by decide +kernel
theorem subd9_2_38 : subd9_2 [-1, 1, -6] = true := by decide +kernel
theorem subd9_2_39 : subd9_2 [-1, 1, -5] = true := by decide +kernel
theorem subd9_2_40 : subd9_2 [-1, 1, -4] = true := by decide +kernel
theorem subd9_2_41 : subd9_2 [-1, 1, -3] = true := by decide +kernel
theorem subd9_2_42 : subd9_2 [-1, 1, -2] = true := by decide +kernel
theorem subd9_2_43 : subd9_2 [-1, 1, -1] = true := by decide +kernel
theorem subd9_2_44 : subd9_2 [-1, 1, 0] = true := by decide +kernel
theorem subd9_2_45 : subd9_2 [-1, 1, 1] = true := by decide +kernel
theorem subd9_2_46 : subd9_2 [-1, 1, 2] = true := by decide +kernel
theorem subd9_2_47 : subd9_2 [-1, 1, 3] = true := by decide +kernel
theorem subd9_2_48 : subd9_2 [-1, 1, 4] = true := by decide +kernel
theorem subd9_2_49 : subd9_2 [-1, 1, 5] = true := by decide +kernel
theorem subd9_2_50 : subd9_2 [-1, 1, 6] = true := by decide +kernel
theorem subd9_2_51 : subd9_2 [-1, 1, 7] = true := by decide +kernel
theorem subd9_2_52 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_53 : subd9_2 [0, -1, -10] = true := by decide +kernel
theorem subd9_2_54 : subd9_2 [0, -1, -9] = true := by decide +kernel
theorem subd9_2_55 : subd9_2 [0, -1, -8] = true := by decide +kernel
theorem subd9_2_56 : subd9_2 [0, -1, -7] = true := by decide +kernel
theorem subd9_2_57 : subd9_2 [0, -1, -6] = true := by decide +kernel
theorem subd9_2_58 : subd9_2 [0, -1, -5] = true := by decide +kernel
theorem subd9_2_59 : subd9_2 [0, -1, -4] = true := by decide +kernel
theorem subd9_2_60 : subd9_2 [0, -1, -3] = true := by decide +kernel
theorem subd9_2_61 : subd9_2 [0, -1, -2] = true := by decide +kernel
theorem subd9_2_62 : subd9_2 [0, -1, -1] = true := by decide +kernel
theorem subd9_2_63 : subd9_2 [0, -1, 0] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_cons.2 ⟨subd9_2_36, List.forall_mem_cons.2 ⟨subd9_2_37, List.forall_mem_cons.2 ⟨subd9_2_38, List.forall_mem_cons.2 ⟨subd9_2_39, List.forall_mem_cons.2 ⟨subd9_2_40, List.forall_mem_cons.2 ⟨subd9_2_41, List.forall_mem_cons.2 ⟨subd9_2_42, List.forall_mem_cons.2 ⟨subd9_2_43, List.forall_mem_cons.2 ⟨subd9_2_44, List.forall_mem_cons.2 ⟨subd9_2_45, List.forall_mem_cons.2 ⟨subd9_2_46, List.forall_mem_cons.2 ⟨subd9_2_47, List.forall_mem_cons.2 ⟨subd9_2_48, List.forall_mem_cons.2 ⟨subd9_2_49, List.forall_mem_cons.2 ⟨subd9_2_50, List.forall_mem_cons.2 ⟨subd9_2_51, List.forall_mem_cons.2 ⟨subd9_2_52, List.forall_mem_cons.2 ⟨subd9_2_53, List.forall_mem_cons.2 ⟨subd9_2_54, List.forall_mem_cons.2 ⟨subd9_2_55, List.forall_mem_cons.2 ⟨subd9_2_56, List.forall_mem_cons.2 ⟨subd9_2_57, List.forall_mem_cons.2 ⟨subd9_2_58, List.forall_mem_cons.2 ⟨subd9_2_59, List.forall_mem_cons.2 ⟨subd9_2_60, List.forall_mem_cons.2 ⟨subd9_2_61, List.forall_mem_cons.2 ⟨subd9_2_62, List.forall_mem_cons.2 ⟨subd9_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_64 : subd9_2 [0, -1, 1] = true := by decide +kernel
theorem subd9_2_65 : subd9_2 [0, -1, 2] = true := by decide +kernel
theorem subd9_2_66 : subd9_2 [0, -1, 3] = true := by decide +kernel
theorem subd9_2_67 : subd9_2 [0, -1, 4] = true := by decide +kernel
theorem subd9_2_68 : subd9_2 [0, -1, 5] = true := by decide +kernel
theorem subd9_2_69 : subd9_2 [0, -1, 6] = true := by decide +kernel
theorem subd9_2_70 : subd9_2 [0, -1, 7] = true := by decide +kernel
theorem subd9_2_71 : subd9_2 [0, -1, 8] = true := by decide +kernel
theorem subd9_2_72 : subd9_2 [0, -1, 9] = true := by decide +kernel
theorem subd9_2_73 : subd9_2 [0, 0, -12] = true := by decide +kernel
theorem subd9_2_74 : subd9_2 [0, 0, -11] = true := by decide +kernel
theorem subd9_2_75 : subd9_2 [0, 0, -10] = true := by decide +kernel
theorem subd9_2_76 : subd9_2 [0, 0, -9] = true := by decide +kernel
theorem subd9_2_77 : subd9_2 [0, 0, -8] = true := by decide +kernel
theorem subd9_2_78 : subd9_2 [0, 0, -7] = true := by decide +kernel
theorem subd9_2_79 : subd9_2 [0, 0, -6] = true := by decide +kernel
theorem subd9_2_80 : subd9_2 [0, 0, -5] = true := by decide +kernel
theorem subd9_2_81 : subd9_2 [0, 0, -4] = true := by decide +kernel
theorem subd9_2_82 : subd9_2 [0, 0, -3] = true := by decide +kernel
theorem subd9_2_83 : subd9_2 [0, 0, -2] = true := by decide +kernel
theorem subd9_2_84 : subd9_2 [0, 0, -1] = true := by decide +kernel
theorem subd9_2_85 : subd9_2 [0, 0, 0] = true := by decide +kernel
theorem subd9_2_86 : subd9_2 [0, 0, 1] = true := by decide +kernel
theorem subd9_2_87 : subd9_2 [0, 0, 2] = true := by decide +kernel
theorem subd9_2_88 : subd9_2 [0, 0, 3] = true := by decide +kernel
theorem subd9_2_89 : subd9_2 [0, 0, 4] = true := by decide +kernel
theorem subd9_2_90 : subd9_2 [0, 0, 5] = true := by decide +kernel
theorem subd9_2_91 : subd9_2 [0, 0, 6] = true := by decide +kernel
theorem subd9_2_92 : subd9_2 [0, 0, 7] = true := by decide +kernel
theorem subd9_2_93 : subd9_2 [0, 0, 8] = true := by decide +kernel
theorem subd9_2_94 : subd9_2 [0, 0, 9] = true := by decide +kernel
theorem subd9_2_95 : subd9_2 [0, 0, 10] = true := by decide +kernel
theorem sbd9_2_2 : ∀ q ∈ blkd9_2_2, subd9_2 q = true := by
  unfold blkd9_2_2
  exact List.forall_mem_cons.2 ⟨subd9_2_64, List.forall_mem_cons.2 ⟨subd9_2_65, List.forall_mem_cons.2 ⟨subd9_2_66, List.forall_mem_cons.2 ⟨subd9_2_67, List.forall_mem_cons.2 ⟨subd9_2_68, List.forall_mem_cons.2 ⟨subd9_2_69, List.forall_mem_cons.2 ⟨subd9_2_70, List.forall_mem_cons.2 ⟨subd9_2_71, List.forall_mem_cons.2 ⟨subd9_2_72, List.forall_mem_cons.2 ⟨subd9_2_73, List.forall_mem_cons.2 ⟨subd9_2_74, List.forall_mem_cons.2 ⟨subd9_2_75, List.forall_mem_cons.2 ⟨subd9_2_76, List.forall_mem_cons.2 ⟨subd9_2_77, List.forall_mem_cons.2 ⟨subd9_2_78, List.forall_mem_cons.2 ⟨subd9_2_79, List.forall_mem_cons.2 ⟨subd9_2_80, List.forall_mem_cons.2 ⟨subd9_2_81, List.forall_mem_cons.2 ⟨subd9_2_82, List.forall_mem_cons.2 ⟨subd9_2_83, List.forall_mem_cons.2 ⟨subd9_2_84, List.forall_mem_cons.2 ⟨subd9_2_85, List.forall_mem_cons.2 ⟨subd9_2_86, List.forall_mem_cons.2 ⟨subd9_2_87, List.forall_mem_cons.2 ⟨subd9_2_88, List.forall_mem_cons.2 ⟨subd9_2_89, List.forall_mem_cons.2 ⟨subd9_2_90, List.forall_mem_cons.2 ⟨subd9_2_91, List.forall_mem_cons.2 ⟨subd9_2_92, List.forall_mem_cons.2 ⟨subd9_2_93, List.forall_mem_cons.2 ⟨subd9_2_94, List.forall_mem_cons.2 ⟨subd9_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_96 : subd9_2 [0, 0, 11] = true := by decide +kernel
theorem subd9_2_97 : subd9_2 [0, 1, -10] = true := by decide +kernel
theorem subd9_2_98 : subd9_2 [0, 1, -9] = true := by decide +kernel
theorem subd9_2_99 : subd9_2 [0, 1, -8] = true := by decide +kernel
theorem subd9_2_100 : subd9_2 [0, 1, -7] = true := by decide +kernel
theorem subd9_2_101 : subd9_2 [0, 1, -6] = true := by decide +kernel
theorem subd9_2_102 : subd9_2 [0, 1, -5] = true := by decide +kernel
theorem subd9_2_103 : subd9_2 [0, 1, -4] = true := by decide +kernel
theorem subd9_2_104 : subd9_2 [0, 1, -3] = true := by decide +kernel
theorem subd9_2_105 : subd9_2 [0, 1, -2] = true := by decide +kernel
theorem subd9_2_106 : subd9_2 [0, 1, -1] = true := by decide +kernel
theorem subd9_2_107 : subd9_2 [0, 1, 0] = true := by decide +kernel
theorem subd9_2_108 : subd9_2 [0, 1, 1] = true := by decide +kernel
theorem subd9_2_109 : subd9_2 [0, 1, 2] = true := by decide +kernel
theorem subd9_2_110 : subd9_2 [0, 1, 3] = true := by decide +kernel
theorem subd9_2_111 : subd9_2 [0, 1, 4] = true := by decide +kernel
theorem subd9_2_112 : subd9_2 [0, 1, 5] = true := by decide +kernel
theorem subd9_2_113 : subd9_2 [0, 1, 6] = true := by decide +kernel
theorem subd9_2_114 : subd9_2 [0, 1, 7] = true := by decide +kernel
theorem subd9_2_115 : subd9_2 [0, 1, 8] = true := by decide +kernel
theorem subd9_2_116 : subd9_2 [0, 1, 9] = true := by decide +kernel
theorem subd9_2_117 : subd9_2 [1, -2] = true := by decide +kernel
theorem subd9_2_118 : subd9_2 [1, -1, -8] = true := by decide +kernel
theorem subd9_2_119 : subd9_2 [1, -1, -7] = true := by decide +kernel
theorem subd9_2_120 : subd9_2 [1, -1, -6] = true := by decide +kernel
theorem subd9_2_121 : subd9_2 [1, -1, -5] = true := by decide +kernel
theorem subd9_2_122 : subd9_2 [1, -1, -4] = true := by decide +kernel
theorem subd9_2_123 : subd9_2 [1, -1, -3] = true := by decide +kernel
theorem subd9_2_124 : subd9_2 [1, -1, -2] = true := by decide +kernel
theorem subd9_2_125 : subd9_2 [1, -1, -1] = true := by decide +kernel
theorem subd9_2_126 : subd9_2 [1, -1, 0] = true := by decide +kernel
theorem subd9_2_127 : subd9_2 [1, -1, 1] = true := by decide +kernel
theorem sbd9_2_3 : ∀ q ∈ blkd9_2_3, subd9_2 q = true := by
  unfold blkd9_2_3
  exact List.forall_mem_cons.2 ⟨subd9_2_96, List.forall_mem_cons.2 ⟨subd9_2_97, List.forall_mem_cons.2 ⟨subd9_2_98, List.forall_mem_cons.2 ⟨subd9_2_99, List.forall_mem_cons.2 ⟨subd9_2_100, List.forall_mem_cons.2 ⟨subd9_2_101, List.forall_mem_cons.2 ⟨subd9_2_102, List.forall_mem_cons.2 ⟨subd9_2_103, List.forall_mem_cons.2 ⟨subd9_2_104, List.forall_mem_cons.2 ⟨subd9_2_105, List.forall_mem_cons.2 ⟨subd9_2_106, List.forall_mem_cons.2 ⟨subd9_2_107, List.forall_mem_cons.2 ⟨subd9_2_108, List.forall_mem_cons.2 ⟨subd9_2_109, List.forall_mem_cons.2 ⟨subd9_2_110, List.forall_mem_cons.2 ⟨subd9_2_111, List.forall_mem_cons.2 ⟨subd9_2_112, List.forall_mem_cons.2 ⟨subd9_2_113, List.forall_mem_cons.2 ⟨subd9_2_114, List.forall_mem_cons.2 ⟨subd9_2_115, List.forall_mem_cons.2 ⟨subd9_2_116, List.forall_mem_cons.2 ⟨subd9_2_117, List.forall_mem_cons.2 ⟨subd9_2_118, List.forall_mem_cons.2 ⟨subd9_2_119, List.forall_mem_cons.2 ⟨subd9_2_120, List.forall_mem_cons.2 ⟨subd9_2_121, List.forall_mem_cons.2 ⟨subd9_2_122, List.forall_mem_cons.2 ⟨subd9_2_123, List.forall_mem_cons.2 ⟨subd9_2_124, List.forall_mem_cons.2 ⟨subd9_2_125, List.forall_mem_cons.2 ⟨subd9_2_126, List.forall_mem_cons.2 ⟨subd9_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_128 : subd9_2 [1, -1, 2] = true := by decide +kernel
theorem subd9_2_129 : subd9_2 [1, -1, 3] = true := by decide +kernel
theorem subd9_2_130 : subd9_2 [1, -1, 4] = true := by decide +kernel
theorem subd9_2_131 : subd9_2 [1, -1, 5] = true := by decide +kernel
theorem subd9_2_132 : subd9_2 [1, -1, 6] = true := by decide +kernel
theorem subd9_2_133 : subd9_2 [1, 0, -10] = true := by decide +kernel
theorem subd9_2_134 : subd9_2 [1, 0, -9] = true := by decide +kernel
theorem subd9_2_135 : subd9_2 [1, 0, -8] = true := by decide +kernel
theorem subd9_2_136 : subd9_2 [1, 0, -7] = true := by decide +kernel
theorem subd9_2_137 : subd9_2 [1, 0, -6] = true := by decide +kernel
theorem subd9_2_138 : subd9_2 [1, 0, -5] = true := by decide +kernel
theorem subd9_2_139 : subd9_2 [1, 0, -4] = true := by decide +kernel
theorem subd9_2_140 : subd9_2 [1, 0, -3] = true := by decide +kernel
theorem subd9_2_141 : subd9_2 [1, 0, -2] = true := by decide +kernel
theorem subd9_2_142 : subd9_2 [1, 0, -1] = true := by decide +kernel
theorem subd9_2_143 : subd9_2 [1, 0, 0] = true := by decide +kernel
theorem subd9_2_144 : subd9_2 [1, 0, 1] = true := by decide +kernel
theorem subd9_2_145 : subd9_2 [1, 0, 2] = true := by decide +kernel
theorem subd9_2_146 : subd9_2 [1, 0, 3] = true := by decide +kernel
theorem subd9_2_147 : subd9_2 [1, 0, 4] = true := by decide +kernel
theorem subd9_2_148 : subd9_2 [1, 0, 5] = true := by decide +kernel
theorem subd9_2_149 : subd9_2 [1, 0, 6] = true := by decide +kernel
theorem subd9_2_150 : subd9_2 [1, 0, 7] = true := by decide +kernel
theorem subd9_2_151 : subd9_2 [1, 0, 8] = true := by decide +kernel
theorem subd9_2_152 : subd9_2 [1, 0, 9] = true := by decide +kernel
theorem subd9_2_153 : subd9_2 [1, 1, -8] = true := by decide +kernel
theorem subd9_2_154 : subd9_2 [1, 1, -7] = true := by decide +kernel
theorem subd9_2_155 : subd9_2 [1, 1, -6] = true := by decide +kernel
theorem subd9_2_156 : subd9_2 [1, 1, -5] = true := by decide +kernel
theorem subd9_2_157 : subd9_2 [1, 1, -4] = true := by decide +kernel
theorem subd9_2_158 : subd9_2 [1, 1, -3] = true := by decide +kernel
theorem subd9_2_159 : subd9_2 [1, 1, -2] = true := by decide +kernel
theorem sbd9_2_4 : ∀ q ∈ blkd9_2_4, subd9_2 q = true := by
  unfold blkd9_2_4
  exact List.forall_mem_cons.2 ⟨subd9_2_128, List.forall_mem_cons.2 ⟨subd9_2_129, List.forall_mem_cons.2 ⟨subd9_2_130, List.forall_mem_cons.2 ⟨subd9_2_131, List.forall_mem_cons.2 ⟨subd9_2_132, List.forall_mem_cons.2 ⟨subd9_2_133, List.forall_mem_cons.2 ⟨subd9_2_134, List.forall_mem_cons.2 ⟨subd9_2_135, List.forall_mem_cons.2 ⟨subd9_2_136, List.forall_mem_cons.2 ⟨subd9_2_137, List.forall_mem_cons.2 ⟨subd9_2_138, List.forall_mem_cons.2 ⟨subd9_2_139, List.forall_mem_cons.2 ⟨subd9_2_140, List.forall_mem_cons.2 ⟨subd9_2_141, List.forall_mem_cons.2 ⟨subd9_2_142, List.forall_mem_cons.2 ⟨subd9_2_143, List.forall_mem_cons.2 ⟨subd9_2_144, List.forall_mem_cons.2 ⟨subd9_2_145, List.forall_mem_cons.2 ⟨subd9_2_146, List.forall_mem_cons.2 ⟨subd9_2_147, List.forall_mem_cons.2 ⟨subd9_2_148, List.forall_mem_cons.2 ⟨subd9_2_149, List.forall_mem_cons.2 ⟨subd9_2_150, List.forall_mem_cons.2 ⟨subd9_2_151, List.forall_mem_cons.2 ⟨subd9_2_152, List.forall_mem_cons.2 ⟨subd9_2_153, List.forall_mem_cons.2 ⟨subd9_2_154, List.forall_mem_cons.2 ⟨subd9_2_155, List.forall_mem_cons.2 ⟨subd9_2_156, List.forall_mem_cons.2 ⟨subd9_2_157, List.forall_mem_cons.2 ⟨subd9_2_158, List.forall_mem_cons.2 ⟨subd9_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_160 : subd9_2 [1, 1, -1] = true := by decide +kernel
theorem subd9_2_161 : subd9_2 [1, 1, 0] = true := by decide +kernel
theorem subd9_2_162 : subd9_2 [1, 1, 1] = true := by decide +kernel
theorem subd9_2_163 : subd9_2 [1, 1, 2] = true := by decide +kernel
theorem subd9_2_164 : subd9_2 [1, 1, 3] = true := by decide +kernel
theorem subd9_2_165 : subd9_2 [1, 1, 4] = true := by decide +kernel
theorem subd9_2_166 : subd9_2 [1, 1, 5] = true := by decide +kernel
theorem subd9_2_167 : subd9_2 [1, 1, 6] = true := by decide +kernel
theorem subd9_2_168 : subd9_2 [1, 1, 7] = true := by decide +kernel
theorem sbd9_2_5 : ∀ q ∈ blkd9_2_5, subd9_2 q = true := by
  unfold blkd9_2_5
  exact List.forall_mem_cons.2 ⟨subd9_2_160, List.forall_mem_cons.2 ⟨subd9_2_161, List.forall_mem_cons.2 ⟨subd9_2_162, List.forall_mem_cons.2 ⟨subd9_2_163, List.forall_mem_cons.2 ⟨subd9_2_164, List.forall_mem_cons.2 ⟨subd9_2_165, List.forall_mem_cons.2 ⟨subd9_2_166, List.forall_mem_cons.2 ⟨subd9_2_167, List.forall_mem_cons.2 ⟨subd9_2_168, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-4] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-3, -5] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-3, -4] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-3, -3] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-3, -2] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-3, -1] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-3, 0] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-3, 1] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-3, 2] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-3, 3] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-2, -5] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-2, -4] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [-2, 3] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [-2, 4] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [-1, -6] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [-1, -5] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [-1, 4] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [-1, 5] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_32 : subd9_3 [0, -6] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [0, -5] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [0, 4] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [0, 5] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [1, -6] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [1, 4] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [1, 5] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [2, -5] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [2, -4] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [2, -3] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [2, -2] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [2, -1] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [2, 0] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [2, 1] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [2, 2] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_64 : subd9_3 [2, 3] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [2, 4] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [3, -4] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [3, -3] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [3, -2] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [3, -1] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [3, 0] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [3, 1] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [3, 2] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [3, 3] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [3, 4] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [4] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [0] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C111
