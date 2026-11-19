import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_32 : subd11_1 [-2, 0, -8] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [-2, 0, -7] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [-2, 0, -6] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [-2, 0, -5] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [-2, 0, -4] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [-2, 0, -3] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [-2, 0, -2] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [-2, 0, -1] = true := by decide +kernel
theorem subd11_1_40 : subd11_1 [-2, 0, 0] = true := by decide +kernel
theorem subd11_1_41 : subd11_1 [-2, 0, 1] = true := by decide +kernel
theorem subd11_1_42 : subd11_1 [-2, 0, 2] = true := by decide +kernel
theorem subd11_1_43 : subd11_1 [-2, 0, 3] = true := by decide +kernel
theorem subd11_1_44 : subd11_1 [-2, 0, 4] = true := by decide +kernel
theorem subd11_1_45 : subd11_1 [-2, 0, 5] = true := by decide +kernel
theorem subd11_1_46 : subd11_1 [-2, 0, 6] = true := by decide +kernel
theorem subd11_1_47 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_48 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_49 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_50 : subd11_1 [-1, -2, -7] = true := by decide +kernel
theorem subd11_1_51 : subd11_1 [-1, -2, -6] = true := by decide +kernel
theorem subd11_1_52 : subd11_1 [-1, -2, -5] = true := by decide +kernel
theorem subd11_1_53 : subd11_1 [-1, -2, -4] = true := by decide +kernel
theorem subd11_1_54 : subd11_1 [-1, -2, -3] = true := by decide +kernel
theorem subd11_1_55 : subd11_1 [-1, -2, -2] = true := by decide +kernel
theorem subd11_1_56 : subd11_1 [-1, -2, -1] = true := by decide +kernel
theorem subd11_1_57 : subd11_1 [-1, -2, 0] = true := by decide +kernel
theorem subd11_1_58 : subd11_1 [-1, -2, 1] = true := by decide +kernel
theorem subd11_1_59 : subd11_1 [-1, -2, 2] = true := by decide +kernel
theorem subd11_1_60 : subd11_1 [-1, -2, 3] = true := by decide +kernel
theorem subd11_1_61 : subd11_1 [-1, -2, 4] = true := by decide +kernel
theorem subd11_1_62 : subd11_1 [-1, -2, 5] = true := by decide +kernel
theorem subd11_1_63 : subd11_1 [-1, -2, 6] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_cons.2 ⟨subd11_1_40, List.forall_mem_cons.2 ⟨subd11_1_41, List.forall_mem_cons.2 ⟨subd11_1_42, List.forall_mem_cons.2 ⟨subd11_1_43, List.forall_mem_cons.2 ⟨subd11_1_44, List.forall_mem_cons.2 ⟨subd11_1_45, List.forall_mem_cons.2 ⟨subd11_1_46, List.forall_mem_cons.2 ⟨subd11_1_47, List.forall_mem_cons.2 ⟨subd11_1_48, List.forall_mem_cons.2 ⟨subd11_1_49, List.forall_mem_cons.2 ⟨subd11_1_50, List.forall_mem_cons.2 ⟨subd11_1_51, List.forall_mem_cons.2 ⟨subd11_1_52, List.forall_mem_cons.2 ⟨subd11_1_53, List.forall_mem_cons.2 ⟨subd11_1_54, List.forall_mem_cons.2 ⟨subd11_1_55, List.forall_mem_cons.2 ⟨subd11_1_56, List.forall_mem_cons.2 ⟨subd11_1_57, List.forall_mem_cons.2 ⟨subd11_1_58, List.forall_mem_cons.2 ⟨subd11_1_59, List.forall_mem_cons.2 ⟨subd11_1_60, List.forall_mem_cons.2 ⟨subd11_1_61, List.forall_mem_cons.2 ⟨subd11_1_62, List.forall_mem_cons.2 ⟨subd11_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_64 : subd11_1 [-1, -2, 7] = true := by decide +kernel
theorem subd11_1_65 : subd11_1 [-1, -2, 8] = true := by decide +kernel
theorem subd11_1_66 : subd11_1 [-1, -1, -9] = true := by decide +kernel
theorem subd11_1_67 : subd11_1 [-1, -1, -8] = true := by decide +kernel
theorem subd11_1_68 : subd11_1 [-1, -1, -7] = true := by decide +kernel
theorem subd11_1_69 : subd11_1 [-1, -1, -6] = true := by decide +kernel
theorem subd11_1_70 : subd11_1 [-1, -1, -5] = true := by decide +kernel
theorem subd11_1_71 : subd11_1 [-1, -1, -4] = true := by decide +kernel
theorem subd11_1_72 : subd11_1 [-1, -1, -3] = true := by decide +kernel
theorem subd11_1_73 : subd11_1 [-1, -1, -2] = true := by decide +kernel
theorem subd11_1_74 : subd11_1 [-1, -1, -1] = true := by decide +kernel
theorem subd11_1_75 : subd11_1 [-1, -1, 0] = true := by decide +kernel
theorem subd11_1_76 : subd11_1 [-1, -1, 1] = true := by decide +kernel
theorem subd11_1_77 : subd11_1 [-1, -1, 2] = true := by decide +kernel
theorem subd11_1_78 : subd11_1 [-1, -1, 3] = true := by decide +kernel
theorem subd11_1_79 : subd11_1 [-1, -1, 4] = true := by decide +kernel
theorem subd11_1_80 : subd11_1 [-1, -1, 5] = true := by decide +kernel
theorem subd11_1_81 : subd11_1 [-1, -1, 6] = true := by decide +kernel
theorem subd11_1_82 : subd11_1 [-1, -1, 7] = true := by decide +kernel
theorem subd11_1_83 : subd11_1 [-1, -1, 8] = true := by decide +kernel
theorem subd11_1_84 : subd11_1 [-1, 0, -9] = true := by decide +kernel
theorem subd11_1_85 : subd11_1 [-1, 0, -8] = true := by decide +kernel
theorem subd11_1_86 : subd11_1 [-1, 0, -7] = true := by decide +kernel
theorem subd11_1_87 : subd11_1 [-1, 0, -6] = true := by decide +kernel
theorem subd11_1_88 : subd11_1 [-1, 0, -5] = true := by decide +kernel
theorem subd11_1_89 : subd11_1 [-1, 0, -4] = true := by decide +kernel
theorem subd11_1_90 : subd11_1 [-1, 0, -3] = true := by decide +kernel
theorem subd11_1_91 : subd11_1 [-1, 0, -2] = true := by decide +kernel
theorem subd11_1_92 : subd11_1 [-1, 0, -1] = true := by decide +kernel
theorem subd11_1_93 : subd11_1 [-1, 0, 0] = true := by decide +kernel
theorem subd11_1_94 : subd11_1 [-1, 0, 1] = true := by decide +kernel
theorem subd11_1_95 : subd11_1 [-1, 0, 2] = true := by decide +kernel
theorem sbd11_1_2 : ∀ q ∈ blkd11_1_2, subd11_1 q = true := by
  unfold blkd11_1_2
  exact List.forall_mem_cons.2 ⟨subd11_1_64, List.forall_mem_cons.2 ⟨subd11_1_65, List.forall_mem_cons.2 ⟨subd11_1_66, List.forall_mem_cons.2 ⟨subd11_1_67, List.forall_mem_cons.2 ⟨subd11_1_68, List.forall_mem_cons.2 ⟨subd11_1_69, List.forall_mem_cons.2 ⟨subd11_1_70, List.forall_mem_cons.2 ⟨subd11_1_71, List.forall_mem_cons.2 ⟨subd11_1_72, List.forall_mem_cons.2 ⟨subd11_1_73, List.forall_mem_cons.2 ⟨subd11_1_74, List.forall_mem_cons.2 ⟨subd11_1_75, List.forall_mem_cons.2 ⟨subd11_1_76, List.forall_mem_cons.2 ⟨subd11_1_77, List.forall_mem_cons.2 ⟨subd11_1_78, List.forall_mem_cons.2 ⟨subd11_1_79, List.forall_mem_cons.2 ⟨subd11_1_80, List.forall_mem_cons.2 ⟨subd11_1_81, List.forall_mem_cons.2 ⟨subd11_1_82, List.forall_mem_cons.2 ⟨subd11_1_83, List.forall_mem_cons.2 ⟨subd11_1_84, List.forall_mem_cons.2 ⟨subd11_1_85, List.forall_mem_cons.2 ⟨subd11_1_86, List.forall_mem_cons.2 ⟨subd11_1_87, List.forall_mem_cons.2 ⟨subd11_1_88, List.forall_mem_cons.2 ⟨subd11_1_89, List.forall_mem_cons.2 ⟨subd11_1_90, List.forall_mem_cons.2 ⟨subd11_1_91, List.forall_mem_cons.2 ⟨subd11_1_92, List.forall_mem_cons.2 ⟨subd11_1_93, List.forall_mem_cons.2 ⟨subd11_1_94, List.forall_mem_cons.2 ⟨subd11_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_96 : subd11_1 [-1, 0, 3] = true := by decide +kernel
theorem subd11_1_97 : subd11_1 [-1, 0, 4] = true := by decide +kernel
theorem subd11_1_98 : subd11_1 [-1, 0, 5] = true := by decide +kernel
theorem subd11_1_99 : subd11_1 [-1, 0, 6] = true := by decide +kernel
theorem subd11_1_100 : subd11_1 [-1, 0, 7] = true := by decide +kernel
theorem subd11_1_101 : subd11_1 [-1, 0, 8] = true := by decide +kernel
theorem subd11_1_102 : subd11_1 [-1, 1, -9] = true := by decide +kernel
theorem subd11_1_103 : subd11_1 [-1, 1, -8] = true := by decide +kernel
theorem subd11_1_104 : subd11_1 [-1, 1, -7] = true := by decide +kernel
theorem subd11_1_105 : subd11_1 [-1, 1, -6] = true := by decide +kernel
theorem subd11_1_106 : subd11_1 [-1, 1, -5] = true := by decide +kernel
theorem subd11_1_107 : subd11_1 [-1, 1, -4] = true := by decide +kernel
theorem subd11_1_108 : subd11_1 [-1, 1, -3] = true := by decide +kernel
theorem subd11_1_109 : subd11_1 [-1, 1, -2] = true := by decide +kernel
theorem subd11_1_110 : subd11_1 [-1, 1, -1] = true := by decide +kernel
theorem subd11_1_111 : subd11_1 [-1, 1, 0] = true := by decide +kernel
theorem subd11_1_112 : subd11_1 [-1, 1, 1] = true := by decide +kernel
theorem subd11_1_113 : subd11_1 [-1, 1, 2] = true := by decide +kernel
theorem subd11_1_114 : subd11_1 [-1, 1, 3] = true := by decide +kernel
theorem subd11_1_115 : subd11_1 [-1, 1, 4] = true := by decide +kernel
theorem subd11_1_116 : subd11_1 [-1, 1, 5] = true := by decide +kernel
theorem subd11_1_117 : subd11_1 [-1, 1, 6] = true := by decide +kernel
theorem subd11_1_118 : subd11_1 [-1, 1, 7] = true := by decide +kernel
theorem subd11_1_119 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_120 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_121 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_122 : subd11_1 [0, -2, -7] = true := by decide +kernel
theorem subd11_1_123 : subd11_1 [0, -2, -6] = true := by decide +kernel
theorem subd11_1_124 : subd11_1 [0, -2, -5] = true := by decide +kernel
theorem subd11_1_125 : subd11_1 [0, -2, -4] = true := by decide +kernel
theorem subd11_1_126 : subd11_1 [0, -2, -3] = true := by decide +kernel
theorem subd11_1_127 : subd11_1 [0, -2, -2] = true := by decide +kernel
theorem sbd11_1_3 : ∀ q ∈ blkd11_1_3, subd11_1 q = true := by
  unfold blkd11_1_3
  exact List.forall_mem_cons.2 ⟨subd11_1_96, List.forall_mem_cons.2 ⟨subd11_1_97, List.forall_mem_cons.2 ⟨subd11_1_98, List.forall_mem_cons.2 ⟨subd11_1_99, List.forall_mem_cons.2 ⟨subd11_1_100, List.forall_mem_cons.2 ⟨subd11_1_101, List.forall_mem_cons.2 ⟨subd11_1_102, List.forall_mem_cons.2 ⟨subd11_1_103, List.forall_mem_cons.2 ⟨subd11_1_104, List.forall_mem_cons.2 ⟨subd11_1_105, List.forall_mem_cons.2 ⟨subd11_1_106, List.forall_mem_cons.2 ⟨subd11_1_107, List.forall_mem_cons.2 ⟨subd11_1_108, List.forall_mem_cons.2 ⟨subd11_1_109, List.forall_mem_cons.2 ⟨subd11_1_110, List.forall_mem_cons.2 ⟨subd11_1_111, List.forall_mem_cons.2 ⟨subd11_1_112, List.forall_mem_cons.2 ⟨subd11_1_113, List.forall_mem_cons.2 ⟨subd11_1_114, List.forall_mem_cons.2 ⟨subd11_1_115, List.forall_mem_cons.2 ⟨subd11_1_116, List.forall_mem_cons.2 ⟨subd11_1_117, List.forall_mem_cons.2 ⟨subd11_1_118, List.forall_mem_cons.2 ⟨subd11_1_119, List.forall_mem_cons.2 ⟨subd11_1_120, List.forall_mem_cons.2 ⟨subd11_1_121, List.forall_mem_cons.2 ⟨subd11_1_122, List.forall_mem_cons.2 ⟨subd11_1_123, List.forall_mem_cons.2 ⟨subd11_1_124, List.forall_mem_cons.2 ⟨subd11_1_125, List.forall_mem_cons.2 ⟨subd11_1_126, List.forall_mem_cons.2 ⟨subd11_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_128 : subd11_1 [0, -2, -1] = true := by decide +kernel
theorem subd11_1_129 : subd11_1 [0, -2, 0] = true := by decide +kernel
theorem subd11_1_130 : subd11_1 [0, -2, 1] = true := by decide +kernel
theorem subd11_1_131 : subd11_1 [0, -2, 2] = true := by decide +kernel
theorem subd11_1_132 : subd11_1 [0, -2, 3] = true := by decide +kernel
theorem subd11_1_133 : subd11_1 [0, -2, 4] = true := by decide +kernel
theorem subd11_1_134 : subd11_1 [0, -2, 5] = true := by decide +kernel
theorem subd11_1_135 : subd11_1 [0, -2, 6] = true := by decide +kernel
theorem subd11_1_136 : subd11_1 [0, -2, 7] = true := by decide +kernel
theorem subd11_1_137 : subd11_1 [0, -2, 8] = true := by decide +kernel
theorem subd11_1_138 : subd11_1 [0, -1, -9] = true := by decide +kernel
theorem subd11_1_139 : subd11_1 [0, -1, -8] = true := by decide +kernel
theorem subd11_1_140 : subd11_1 [0, -1, -7] = true := by decide +kernel
theorem subd11_1_141 : subd11_1 [0, -1, -6] = true := by decide +kernel
theorem subd11_1_142 : subd11_1 [0, -1, -5] = true := by decide +kernel
theorem subd11_1_143 : subd11_1 [0, -1, -4] = true := by decide +kernel
theorem subd11_1_144 : subd11_1 [0, -1, -3] = true := by decide +kernel
theorem subd11_1_145 : subd11_1 [0, -1, -2] = true := by decide +kernel
theorem subd11_1_146 : subd11_1 [0, -1, -1] = true := by decide +kernel
theorem subd11_1_147 : subd11_1 [0, -1, 0] = true := by decide +kernel
theorem subd11_1_148 : subd11_1 [0, -1, 1] = true := by decide +kernel
theorem subd11_1_149 : subd11_1 [0, -1, 2] = true := by decide +kernel
theorem subd11_1_150 : subd11_1 [0, -1, 3] = true := by decide +kernel
theorem subd11_1_151 : subd11_1 [0, -1, 4] = true := by decide +kernel
theorem subd11_1_152 : subd11_1 [0, -1, 5] = true := by decide +kernel
theorem subd11_1_153 : subd11_1 [0, -1, 6] = true := by decide +kernel
theorem subd11_1_154 : subd11_1 [0, -1, 7] = true := by decide +kernel
theorem subd11_1_155 : subd11_1 [0, -1, 8] = true := by decide +kernel
theorem subd11_1_156 : subd11_1 [0, -1, 9] = true := by decide +kernel
theorem subd11_1_157 : subd11_1 [0, 0, -10] = true := by decide +kernel
theorem subd11_1_158 : subd11_1 [0, 0, -9] = true := by decide +kernel
theorem subd11_1_159 : subd11_1 [0, 0, -8] = true := by decide +kernel
theorem sbd11_1_4 : ∀ q ∈ blkd11_1_4, subd11_1 q = true := by
  unfold blkd11_1_4
  exact List.forall_mem_cons.2 ⟨subd11_1_128, List.forall_mem_cons.2 ⟨subd11_1_129, List.forall_mem_cons.2 ⟨subd11_1_130, List.forall_mem_cons.2 ⟨subd11_1_131, List.forall_mem_cons.2 ⟨subd11_1_132, List.forall_mem_cons.2 ⟨subd11_1_133, List.forall_mem_cons.2 ⟨subd11_1_134, List.forall_mem_cons.2 ⟨subd11_1_135, List.forall_mem_cons.2 ⟨subd11_1_136, List.forall_mem_cons.2 ⟨subd11_1_137, List.forall_mem_cons.2 ⟨subd11_1_138, List.forall_mem_cons.2 ⟨subd11_1_139, List.forall_mem_cons.2 ⟨subd11_1_140, List.forall_mem_cons.2 ⟨subd11_1_141, List.forall_mem_cons.2 ⟨subd11_1_142, List.forall_mem_cons.2 ⟨subd11_1_143, List.forall_mem_cons.2 ⟨subd11_1_144, List.forall_mem_cons.2 ⟨subd11_1_145, List.forall_mem_cons.2 ⟨subd11_1_146, List.forall_mem_cons.2 ⟨subd11_1_147, List.forall_mem_cons.2 ⟨subd11_1_148, List.forall_mem_cons.2 ⟨subd11_1_149, List.forall_mem_cons.2 ⟨subd11_1_150, List.forall_mem_cons.2 ⟨subd11_1_151, List.forall_mem_cons.2 ⟨subd11_1_152, List.forall_mem_cons.2 ⟨subd11_1_153, List.forall_mem_cons.2 ⟨subd11_1_154, List.forall_mem_cons.2 ⟨subd11_1_155, List.forall_mem_cons.2 ⟨subd11_1_156, List.forall_mem_cons.2 ⟨subd11_1_157, List.forall_mem_cons.2 ⟨subd11_1_158, List.forall_mem_cons.2 ⟨subd11_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_160 : subd11_1 [0, 0, -7] = true := by decide +kernel
theorem subd11_1_161 : subd11_1 [0, 0, -6] = true := by decide +kernel
theorem subd11_1_162 : subd11_1 [0, 0, -5] = true := by decide +kernel
theorem subd11_1_163 : subd11_1 [0, 0, -4] = true := by decide +kernel
theorem subd11_1_164 : subd11_1 [0, 0, -3] = true := by decide +kernel
theorem subd11_1_165 : subd11_1 [0, 0, -2] = true := by decide +kernel
theorem subd11_1_166 : subd11_1 [0, 0, -1] = true := by decide +kernel
theorem subd11_1_167 : subd11_1 [0, 0, 0] = true := by decide +kernel
theorem subd11_1_168 : subd11_1 [0, 0, 1] = true := by decide +kernel
theorem subd11_1_169 : subd11_1 [0, 0, 2] = true := by decide +kernel
theorem subd11_1_170 : subd11_1 [0, 0, 3] = true := by decide +kernel
theorem subd11_1_171 : subd11_1 [0, 0, 4] = true := by decide +kernel
theorem subd11_1_172 : subd11_1 [0, 0, 5] = true := by decide +kernel
theorem subd11_1_173 : subd11_1 [0, 0, 6] = true := by decide +kernel
theorem subd11_1_174 : subd11_1 [0, 0, 7] = true := by decide +kernel
theorem subd11_1_175 : subd11_1 [0, 0, 8] = true := by decide +kernel
theorem subd11_1_176 : subd11_1 [0, 0, 9] = true := by decide +kernel
theorem subd11_1_177 : subd11_1 [0, 1, -10] = true := by decide +kernel
theorem subd11_1_178 : subd11_1 [0, 1, -9] = true := by decide +kernel
theorem subd11_1_179 : subd11_1 [0, 1, -8] = true := by decide +kernel
theorem subd11_1_180 : subd11_1 [0, 1, -7] = true := by decide +kernel
theorem subd11_1_181 : subd11_1 [0, 1, -6] = true := by decide +kernel
theorem subd11_1_182 : subd11_1 [0, 1, -5] = true := by decide +kernel
theorem subd11_1_183 : subd11_1 [0, 1, -4] = true := by decide +kernel
theorem subd11_1_184 : subd11_1 [0, 1, -3] = true := by decide +kernel
theorem subd11_1_185 : subd11_1 [0, 1, -2] = true := by decide +kernel
theorem subd11_1_186 : subd11_1 [0, 1, -1] = true := by decide +kernel
theorem subd11_1_187 : subd11_1 [0, 1, 0] = true := by decide +kernel
theorem subd11_1_188 : subd11_1 [0, 1, 1] = true := by decide +kernel
theorem subd11_1_189 : subd11_1 [0, 1, 2] = true := by decide +kernel
theorem subd11_1_190 : subd11_1 [0, 1, 3] = true := by decide +kernel
theorem subd11_1_191 : subd11_1 [0, 1, 4] = true := by decide +kernel
theorem sbd11_1_5 : ∀ q ∈ blkd11_1_5, subd11_1 q = true := by
  unfold blkd11_1_5
  exact List.forall_mem_cons.2 ⟨subd11_1_160, List.forall_mem_cons.2 ⟨subd11_1_161, List.forall_mem_cons.2 ⟨subd11_1_162, List.forall_mem_cons.2 ⟨subd11_1_163, List.forall_mem_cons.2 ⟨subd11_1_164, List.forall_mem_cons.2 ⟨subd11_1_165, List.forall_mem_cons.2 ⟨subd11_1_166, List.forall_mem_cons.2 ⟨subd11_1_167, List.forall_mem_cons.2 ⟨subd11_1_168, List.forall_mem_cons.2 ⟨subd11_1_169, List.forall_mem_cons.2 ⟨subd11_1_170, List.forall_mem_cons.2 ⟨subd11_1_171, List.forall_mem_cons.2 ⟨subd11_1_172, List.forall_mem_cons.2 ⟨subd11_1_173, List.forall_mem_cons.2 ⟨subd11_1_174, List.forall_mem_cons.2 ⟨subd11_1_175, List.forall_mem_cons.2 ⟨subd11_1_176, List.forall_mem_cons.2 ⟨subd11_1_177, List.forall_mem_cons.2 ⟨subd11_1_178, List.forall_mem_cons.2 ⟨subd11_1_179, List.forall_mem_cons.2 ⟨subd11_1_180, List.forall_mem_cons.2 ⟨subd11_1_181, List.forall_mem_cons.2 ⟨subd11_1_182, List.forall_mem_cons.2 ⟨subd11_1_183, List.forall_mem_cons.2 ⟨subd11_1_184, List.forall_mem_cons.2 ⟨subd11_1_185, List.forall_mem_cons.2 ⟨subd11_1_186, List.forall_mem_cons.2 ⟨subd11_1_187, List.forall_mem_cons.2 ⟨subd11_1_188, List.forall_mem_cons.2 ⟨subd11_1_189, List.forall_mem_cons.2 ⟨subd11_1_190, List.forall_mem_cons.2 ⟨subd11_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_192 : subd11_1 [0, 1, 5] = true := by decide +kernel
theorem subd11_1_193 : subd11_1 [0, 1, 6] = true := by decide +kernel
theorem subd11_1_194 : subd11_1 [0, 1, 7] = true := by decide +kernel
theorem subd11_1_195 : subd11_1 [0, 1, 8] = true := by decide +kernel
theorem subd11_1_196 : subd11_1 [0, 2, -9] = true := by decide +kernel
theorem subd11_1_197 : subd11_1 [0, 2, -8] = true := by decide +kernel
theorem subd11_1_198 : subd11_1 [0, 2, -7] = true := by decide +kernel
theorem subd11_1_199 : subd11_1 [0, 2, -6] = true := by decide +kernel
theorem subd11_1_200 : subd11_1 [0, 2, -5] = true := by decide +kernel
theorem subd11_1_201 : subd11_1 [0, 2, -4] = true := by decide +kernel
theorem subd11_1_202 : subd11_1 [0, 2, -3] = true := by decide +kernel
theorem subd11_1_203 : subd11_1 [0, 2, -2] = true := by decide +kernel
theorem subd11_1_204 : subd11_1 [0, 2, -1] = true := by decide +kernel
theorem subd11_1_205 : subd11_1 [0, 2, 0] = true := by decide +kernel
theorem subd11_1_206 : subd11_1 [0, 2, 1] = true := by decide +kernel
theorem subd11_1_207 : subd11_1 [0, 2, 2] = true := by decide +kernel
theorem subd11_1_208 : subd11_1 [0, 2, 3] = true := by decide +kernel
theorem subd11_1_209 : subd11_1 [0, 2, 4] = true := by decide +kernel
theorem subd11_1_210 : subd11_1 [0, 2, 5] = true := by decide +kernel
theorem subd11_1_211 : subd11_1 [0, 2, 6] = true := by decide +kernel
theorem subd11_1_212 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_213 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_214 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_215 : subd11_1 [1, -1, -8] = true := by decide +kernel
theorem subd11_1_216 : subd11_1 [1, -1, -7] = true := by decide +kernel
theorem subd11_1_217 : subd11_1 [1, -1, -6] = true := by decide +kernel
theorem subd11_1_218 : subd11_1 [1, -1, -5] = true := by decide +kernel
theorem subd11_1_219 : subd11_1 [1, -1, -4] = true := by decide +kernel
theorem subd11_1_220 : subd11_1 [1, -1, -3] = true := by decide +kernel
theorem subd11_1_221 : subd11_1 [1, -1, -2] = true := by decide +kernel
theorem subd11_1_222 : subd11_1 [1, -1, -1] = true := by decide +kernel
theorem subd11_1_223 : subd11_1 [1, -1, 0] = true := by decide +kernel
theorem sbd11_1_6 : ∀ q ∈ blkd11_1_6, subd11_1 q = true := by
  unfold blkd11_1_6
  exact List.forall_mem_cons.2 ⟨subd11_1_192, List.forall_mem_cons.2 ⟨subd11_1_193, List.forall_mem_cons.2 ⟨subd11_1_194, List.forall_mem_cons.2 ⟨subd11_1_195, List.forall_mem_cons.2 ⟨subd11_1_196, List.forall_mem_cons.2 ⟨subd11_1_197, List.forall_mem_cons.2 ⟨subd11_1_198, List.forall_mem_cons.2 ⟨subd11_1_199, List.forall_mem_cons.2 ⟨subd11_1_200, List.forall_mem_cons.2 ⟨subd11_1_201, List.forall_mem_cons.2 ⟨subd11_1_202, List.forall_mem_cons.2 ⟨subd11_1_203, List.forall_mem_cons.2 ⟨subd11_1_204, List.forall_mem_cons.2 ⟨subd11_1_205, List.forall_mem_cons.2 ⟨subd11_1_206, List.forall_mem_cons.2 ⟨subd11_1_207, List.forall_mem_cons.2 ⟨subd11_1_208, List.forall_mem_cons.2 ⟨subd11_1_209, List.forall_mem_cons.2 ⟨subd11_1_210, List.forall_mem_cons.2 ⟨subd11_1_211, List.forall_mem_cons.2 ⟨subd11_1_212, List.forall_mem_cons.2 ⟨subd11_1_213, List.forall_mem_cons.2 ⟨subd11_1_214, List.forall_mem_cons.2 ⟨subd11_1_215, List.forall_mem_cons.2 ⟨subd11_1_216, List.forall_mem_cons.2 ⟨subd11_1_217, List.forall_mem_cons.2 ⟨subd11_1_218, List.forall_mem_cons.2 ⟨subd11_1_219, List.forall_mem_cons.2 ⟨subd11_1_220, List.forall_mem_cons.2 ⟨subd11_1_221, List.forall_mem_cons.2 ⟨subd11_1_222, List.forall_mem_cons.2 ⟨subd11_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_224 : subd11_1 [1, -1, 1] = true := by decide +kernel
theorem subd11_1_225 : subd11_1 [1, -1, 2] = true := by decide +kernel
theorem subd11_1_226 : subd11_1 [1, -1, 3] = true := by decide +kernel
theorem subd11_1_227 : subd11_1 [1, -1, 4] = true := by decide +kernel
theorem subd11_1_228 : subd11_1 [1, -1, 5] = true := by decide +kernel
theorem subd11_1_229 : subd11_1 [1, -1, 6] = true := by decide +kernel
theorem subd11_1_230 : subd11_1 [1, -1, 7] = true := by decide +kernel
theorem subd11_1_231 : subd11_1 [1, -1, 8] = true := by decide +kernel
theorem subd11_1_232 : subd11_1 [1, 0, -9] = true := by decide +kernel
theorem subd11_1_233 : subd11_1 [1, 0, -8] = true := by decide +kernel
theorem subd11_1_234 : subd11_1 [1, 0, -7] = true := by decide +kernel
theorem subd11_1_235 : subd11_1 [1, 0, -6] = true := by decide +kernel
theorem subd11_1_236 : subd11_1 [1, 0, -5] = true := by decide +kernel
theorem subd11_1_237 : subd11_1 [1, 0, -4] = true := by decide +kernel
theorem subd11_1_238 : subd11_1 [1, 0, -3] = true := by decide +kernel
theorem subd11_1_239 : subd11_1 [1, 0, -2] = true := by decide +kernel
theorem subd11_1_240 : subd11_1 [1, 0, -1] = true := by decide +kernel
theorem subd11_1_241 : subd11_1 [1, 0, 0] = true := by decide +kernel
theorem subd11_1_242 : subd11_1 [1, 0, 1] = true := by decide +kernel
theorem subd11_1_243 : subd11_1 [1, 0, 2] = true := by decide +kernel
theorem subd11_1_244 : subd11_1 [1, 0, 3] = true := by decide +kernel
theorem subd11_1_245 : subd11_1 [1, 0, 4] = true := by decide +kernel
theorem subd11_1_246 : subd11_1 [1, 0, 5] = true := by decide +kernel
theorem subd11_1_247 : subd11_1 [1, 0, 6] = true := by decide +kernel
theorem subd11_1_248 : subd11_1 [1, 0, 7] = true := by decide +kernel
theorem subd11_1_249 : subd11_1 [1, 0, 8] = true := by decide +kernel
theorem subd11_1_250 : subd11_1 [1, 1, -9] = true := by decide +kernel
theorem subd11_1_251 : subd11_1 [1, 1, -8] = true := by decide +kernel
theorem subd11_1_252 : subd11_1 [1, 1, -7] = true := by decide +kernel
theorem subd11_1_253 : subd11_1 [1, 1, -6] = true := by decide +kernel
theorem subd11_1_254 : subd11_1 [1, 1, -5] = true := by decide +kernel
theorem subd11_1_255 : subd11_1 [1, 1, -4] = true := by decide +kernel
theorem sbd11_1_7 : ∀ q ∈ blkd11_1_7, subd11_1 q = true := by
  unfold blkd11_1_7
  exact List.forall_mem_cons.2 ⟨subd11_1_224, List.forall_mem_cons.2 ⟨subd11_1_225, List.forall_mem_cons.2 ⟨subd11_1_226, List.forall_mem_cons.2 ⟨subd11_1_227, List.forall_mem_cons.2 ⟨subd11_1_228, List.forall_mem_cons.2 ⟨subd11_1_229, List.forall_mem_cons.2 ⟨subd11_1_230, List.forall_mem_cons.2 ⟨subd11_1_231, List.forall_mem_cons.2 ⟨subd11_1_232, List.forall_mem_cons.2 ⟨subd11_1_233, List.forall_mem_cons.2 ⟨subd11_1_234, List.forall_mem_cons.2 ⟨subd11_1_235, List.forall_mem_cons.2 ⟨subd11_1_236, List.forall_mem_cons.2 ⟨subd11_1_237, List.forall_mem_cons.2 ⟨subd11_1_238, List.forall_mem_cons.2 ⟨subd11_1_239, List.forall_mem_cons.2 ⟨subd11_1_240, List.forall_mem_cons.2 ⟨subd11_1_241, List.forall_mem_cons.2 ⟨subd11_1_242, List.forall_mem_cons.2 ⟨subd11_1_243, List.forall_mem_cons.2 ⟨subd11_1_244, List.forall_mem_cons.2 ⟨subd11_1_245, List.forall_mem_cons.2 ⟨subd11_1_246, List.forall_mem_cons.2 ⟨subd11_1_247, List.forall_mem_cons.2 ⟨subd11_1_248, List.forall_mem_cons.2 ⟨subd11_1_249, List.forall_mem_cons.2 ⟨subd11_1_250, List.forall_mem_cons.2 ⟨subd11_1_251, List.forall_mem_cons.2 ⟨subd11_1_252, List.forall_mem_cons.2 ⟨subd11_1_253, List.forall_mem_cons.2 ⟨subd11_1_254, List.forall_mem_cons.2 ⟨subd11_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_256 : subd11_1 [1, 1, -3] = true := by decide +kernel
theorem subd11_1_257 : subd11_1 [1, 1, -2] = true := by decide +kernel
theorem subd11_1_258 : subd11_1 [1, 1, -1] = true := by decide +kernel
theorem subd11_1_259 : subd11_1 [1, 1, 0] = true := by decide +kernel
theorem subd11_1_260 : subd11_1 [1, 1, 1] = true := by decide +kernel
theorem subd11_1_261 : subd11_1 [1, 1, 2] = true := by decide +kernel
theorem subd11_1_262 : subd11_1 [1, 1, 3] = true := by decide +kernel
theorem subd11_1_263 : subd11_1 [1, 1, 4] = true := by decide +kernel
theorem subd11_1_264 : subd11_1 [1, 1, 5] = true := by decide +kernel
theorem subd11_1_265 : subd11_1 [1, 1, 6] = true := by decide +kernel
theorem subd11_1_266 : subd11_1 [1, 1, 7] = true := by decide +kernel
theorem subd11_1_267 : subd11_1 [1, 1, 8] = true := by decide +kernel
theorem subd11_1_268 : subd11_1 [1, 2, -9] = true := by decide +kernel
theorem subd11_1_269 : subd11_1 [1, 2, -8] = true := by decide +kernel
theorem subd11_1_270 : subd11_1 [1, 2, -7] = true := by decide +kernel
theorem subd11_1_271 : subd11_1 [1, 2, -6] = true := by decide +kernel
theorem subd11_1_272 : subd11_1 [1, 2, -5] = true := by decide +kernel
theorem subd11_1_273 : subd11_1 [1, 2, -4] = true := by decide +kernel
theorem subd11_1_274 : subd11_1 [1, 2, -3] = true := by decide +kernel
theorem subd11_1_275 : subd11_1 [1, 2, -2] = true := by decide +kernel
theorem subd11_1_276 : subd11_1 [1, 2, -1] = true := by decide +kernel
theorem subd11_1_277 : subd11_1 [1, 2, 0] = true := by decide +kernel
theorem subd11_1_278 : subd11_1 [1, 2, 1] = true := by decide +kernel
theorem subd11_1_279 : subd11_1 [1, 2, 2] = true := by decide +kernel
theorem subd11_1_280 : subd11_1 [1, 2, 3] = true := by decide +kernel
theorem subd11_1_281 : subd11_1 [1, 2, 4] = true := by decide +kernel
theorem subd11_1_282 : subd11_1 [1, 2, 5] = true := by decide +kernel
theorem subd11_1_283 : subd11_1 [1, 2, 6] = true := by decide +kernel
theorem subd11_1_284 : subd11_1 [1, 3] = true := by decide +kernel
theorem subd11_1_285 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_286 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_287 : subd11_1 [2, 0, -7] = true := by decide +kernel
theorem sbd11_1_8 : ∀ q ∈ blkd11_1_8, subd11_1 q = true := by
  unfold blkd11_1_8
  exact List.forall_mem_cons.2 ⟨subd11_1_256, List.forall_mem_cons.2 ⟨subd11_1_257, List.forall_mem_cons.2 ⟨subd11_1_258, List.forall_mem_cons.2 ⟨subd11_1_259, List.forall_mem_cons.2 ⟨subd11_1_260, List.forall_mem_cons.2 ⟨subd11_1_261, List.forall_mem_cons.2 ⟨subd11_1_262, List.forall_mem_cons.2 ⟨subd11_1_263, List.forall_mem_cons.2 ⟨subd11_1_264, List.forall_mem_cons.2 ⟨subd11_1_265, List.forall_mem_cons.2 ⟨subd11_1_266, List.forall_mem_cons.2 ⟨subd11_1_267, List.forall_mem_cons.2 ⟨subd11_1_268, List.forall_mem_cons.2 ⟨subd11_1_269, List.forall_mem_cons.2 ⟨subd11_1_270, List.forall_mem_cons.2 ⟨subd11_1_271, List.forall_mem_cons.2 ⟨subd11_1_272, List.forall_mem_cons.2 ⟨subd11_1_273, List.forall_mem_cons.2 ⟨subd11_1_274, List.forall_mem_cons.2 ⟨subd11_1_275, List.forall_mem_cons.2 ⟨subd11_1_276, List.forall_mem_cons.2 ⟨subd11_1_277, List.forall_mem_cons.2 ⟨subd11_1_278, List.forall_mem_cons.2 ⟨subd11_1_279, List.forall_mem_cons.2 ⟨subd11_1_280, List.forall_mem_cons.2 ⟨subd11_1_281, List.forall_mem_cons.2 ⟨subd11_1_282, List.forall_mem_cons.2 ⟨subd11_1_283, List.forall_mem_cons.2 ⟨subd11_1_284, List.forall_mem_cons.2 ⟨subd11_1_285, List.forall_mem_cons.2 ⟨subd11_1_286, List.forall_mem_cons.2 ⟨subd11_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_288 : subd11_1 [2, 0, -6] = true := by decide +kernel
theorem subd11_1_289 : subd11_1 [2, 0, -5] = true := by decide +kernel
theorem subd11_1_290 : subd11_1 [2, 0, -4] = true := by decide +kernel
theorem subd11_1_291 : subd11_1 [2, 0, -3] = true := by decide +kernel
theorem subd11_1_292 : subd11_1 [2, 0, -2] = true := by decide +kernel
theorem subd11_1_293 : subd11_1 [2, 0, -1] = true := by decide +kernel
theorem subd11_1_294 : subd11_1 [2, 0, 0] = true := by decide +kernel
theorem subd11_1_295 : subd11_1 [2, 0, 1] = true := by decide +kernel
theorem subd11_1_296 : subd11_1 [2, 0, 2] = true := by decide +kernel
theorem subd11_1_297 : subd11_1 [2, 0, 3] = true := by decide +kernel
theorem subd11_1_298 : subd11_1 [2, 0, 4] = true := by decide +kernel
theorem subd11_1_299 : subd11_1 [2, 0, 5] = true := by decide +kernel
theorem subd11_1_300 : subd11_1 [2, 0, 6] = true := by decide +kernel
theorem subd11_1_301 : subd11_1 [2, 0, 7] = true := by decide +kernel
theorem subd11_1_302 : subd11_1 [2, 1, -8] = true := by decide +kernel
theorem subd11_1_303 : subd11_1 [2, 1, -7] = true := by decide +kernel
theorem subd11_1_304 : subd11_1 [2, 1, -6] = true := by decide +kernel
theorem subd11_1_305 : subd11_1 [2, 1, -5] = true := by decide +kernel
theorem subd11_1_306 : subd11_1 [2, 1, -4] = true := by decide +kernel
theorem subd11_1_307 : subd11_1 [2, 1, -3] = true := by decide +kernel
theorem subd11_1_308 : subd11_1 [2, 1, -2] = true := by decide +kernel
theorem subd11_1_309 : subd11_1 [2, 1, -1] = true := by decide +kernel
theorem subd11_1_310 : subd11_1 [2, 1, 0] = true := by decide +kernel
theorem subd11_1_311 : subd11_1 [2, 1, 1] = true := by decide +kernel
theorem subd11_1_312 : subd11_1 [2, 1, 2] = true := by decide +kernel
theorem subd11_1_313 : subd11_1 [2, 1, 3] = true := by decide +kernel
theorem subd11_1_314 : subd11_1 [2, 1, 4] = true := by decide +kernel
theorem subd11_1_315 : subd11_1 [2, 1, 5] = true := by decide +kernel
theorem subd11_1_316 : subd11_1 [2, 1, 6] = true := by decide +kernel
theorem subd11_1_317 : subd11_1 [2, 1, 7] = true := by decide +kernel
theorem subd11_1_318 : subd11_1 [2, 2, -7] = true := by decide +kernel
theorem subd11_1_319 : subd11_1 [2, 2, -6] = true := by decide +kernel
theorem sbd11_1_9 : ∀ q ∈ blkd11_1_9, subd11_1 q = true := by
  unfold blkd11_1_9
  exact List.forall_mem_cons.2 ⟨subd11_1_288, List.forall_mem_cons.2 ⟨subd11_1_289, List.forall_mem_cons.2 ⟨subd11_1_290, List.forall_mem_cons.2 ⟨subd11_1_291, List.forall_mem_cons.2 ⟨subd11_1_292, List.forall_mem_cons.2 ⟨subd11_1_293, List.forall_mem_cons.2 ⟨subd11_1_294, List.forall_mem_cons.2 ⟨subd11_1_295, List.forall_mem_cons.2 ⟨subd11_1_296, List.forall_mem_cons.2 ⟨subd11_1_297, List.forall_mem_cons.2 ⟨subd11_1_298, List.forall_mem_cons.2 ⟨subd11_1_299, List.forall_mem_cons.2 ⟨subd11_1_300, List.forall_mem_cons.2 ⟨subd11_1_301, List.forall_mem_cons.2 ⟨subd11_1_302, List.forall_mem_cons.2 ⟨subd11_1_303, List.forall_mem_cons.2 ⟨subd11_1_304, List.forall_mem_cons.2 ⟨subd11_1_305, List.forall_mem_cons.2 ⟨subd11_1_306, List.forall_mem_cons.2 ⟨subd11_1_307, List.forall_mem_cons.2 ⟨subd11_1_308, List.forall_mem_cons.2 ⟨subd11_1_309, List.forall_mem_cons.2 ⟨subd11_1_310, List.forall_mem_cons.2 ⟨subd11_1_311, List.forall_mem_cons.2 ⟨subd11_1_312, List.forall_mem_cons.2 ⟨subd11_1_313, List.forall_mem_cons.2 ⟨subd11_1_314, List.forall_mem_cons.2 ⟨subd11_1_315, List.forall_mem_cons.2 ⟨subd11_1_316, List.forall_mem_cons.2 ⟨subd11_1_317, List.forall_mem_cons.2 ⟨subd11_1_318, List.forall_mem_cons.2 ⟨subd11_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_320 : subd11_1 [2, 2, -5] = true := by decide +kernel
theorem subd11_1_321 : subd11_1 [2, 2, -4] = true := by decide +kernel
theorem subd11_1_322 : subd11_1 [2, 2, -3] = true := by decide +kernel
theorem subd11_1_323 : subd11_1 [2, 2, -2] = true := by decide +kernel
theorem subd11_1_324 : subd11_1 [2, 2, -1] = true := by decide +kernel
theorem subd11_1_325 : subd11_1 [2, 2, 0] = true := by decide +kernel
theorem subd11_1_326 : subd11_1 [2, 2, 1] = true := by decide +kernel
theorem subd11_1_327 : subd11_1 [2, 2, 2] = true := by decide +kernel
theorem subd11_1_328 : subd11_1 [2, 2, 3] = true := by decide +kernel
theorem subd11_1_329 : subd11_1 [2, 2, 4] = true := by decide +kernel
theorem subd11_1_330 : subd11_1 [2, 2, 5] = true := by decide +kernel
theorem subd11_1_331 : subd11_1 [2, 3] = true := by decide +kernel
theorem subd11_1_332 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_10 : ∀ q ∈ blkd11_1_10, subd11_1 q = true := by
  unfold blkd11_1_10
  exact List.forall_mem_cons.2 ⟨subd11_1_320, List.forall_mem_cons.2 ⟨subd11_1_321, List.forall_mem_cons.2 ⟨subd11_1_322, List.forall_mem_cons.2 ⟨subd11_1_323, List.forall_mem_cons.2 ⟨subd11_1_324, List.forall_mem_cons.2 ⟨subd11_1_325, List.forall_mem_cons.2 ⟨subd11_1_326, List.forall_mem_cons.2 ⟨subd11_1_327, List.forall_mem_cons.2 ⟨subd11_1_328, List.forall_mem_cons.2 ⟨subd11_1_329, List.forall_mem_cons.2 ⟨subd11_1_330, List.forall_mem_cons.2 ⟨subd11_1_331, List.forall_mem_cons.2 ⟨subd11_1_332, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-3] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-2, -1, -8] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-2, -1, -7] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-2, -1, -6] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-2, -1, -5] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-2, -1, -4] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-2, -1, -3] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-2, -1, -2] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-2, -1, -1] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-2, -1, 0] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-2, -1, 1] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-2, -1, 2] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-2, -1, 3] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-2, -1, 4] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-2, -1, 5] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [-2, -1, 6] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [-2, 0, -10] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [-2, 0, -9] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [-2, 0, -8] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [-2, 0, -7] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [-2, 0, -6] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [-2, 0, -5] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [-2, 0, -4] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [-2, 0, -3] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [-2, 0, -2] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [-2, 0, -1] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [-2, 0, 0] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [-2, 0, 1] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [-2, 0, 2] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [-2, 0, 3] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [-2, 0, 4] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [-2, 0, 5] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [-2, 0, 6] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [-2, 0, 7] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [-2, 0, 8] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [-2, 1, -9] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [-2, 1, -8] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [-2, 1, -7] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [-2, 1, -6] = true := by decide +kernel
theorem subd11_2_40 : subd11_2 [-2, 1, -5] = true := by decide +kernel
theorem subd11_2_41 : subd11_2 [-2, 1, -4] = true := by decide +kernel
theorem subd11_2_42 : subd11_2 [-2, 1, -3] = true := by decide +kernel
theorem subd11_2_43 : subd11_2 [-2, 1, -2] = true := by decide +kernel
theorem subd11_2_44 : subd11_2 [-2, 1, -1] = true := by decide +kernel
theorem subd11_2_45 : subd11_2 [-2, 1, 0] = true := by decide +kernel
theorem subd11_2_46 : subd11_2 [-2, 1, 1] = true := by decide +kernel
theorem subd11_2_47 : subd11_2 [-2, 1, 2] = true := by decide +kernel
theorem subd11_2_48 : subd11_2 [-2, 1, 3] = true := by decide +kernel
theorem subd11_2_49 : subd11_2 [-2, 1, 4] = true := by decide +kernel
theorem subd11_2_50 : subd11_2 [-2, 1, 5] = true := by decide +kernel
theorem subd11_2_51 : subd11_2 [-2, 1, 6] = true := by decide +kernel
theorem subd11_2_52 : subd11_2 [-2, 1, 7] = true := by decide +kernel
theorem subd11_2_53 : subd11_2 [-2, 1, 8] = true := by decide +kernel
theorem subd11_2_54 : subd11_2 [-2, 2] = true := by decide +kernel
theorem subd11_2_55 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_56 : subd11_2 [-1, -2, -8] = true := by decide +kernel
theorem subd11_2_57 : subd11_2 [-1, -2, -7] = true := by decide +kernel
theorem subd11_2_58 : subd11_2 [-1, -2, -6] = true := by decide +kernel
theorem subd11_2_59 : subd11_2 [-1, -2, -5] = true := by decide +kernel
theorem subd11_2_60 : subd11_2 [-1, -2, -4] = true := by decide +kernel
theorem subd11_2_61 : subd11_2 [-1, -2, -3] = true := by decide +kernel
theorem subd11_2_62 : subd11_2 [-1, -2, -2] = true := by decide +kernel
theorem subd11_2_63 : subd11_2 [-1, -2, -1] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_cons.2 ⟨subd11_2_40, List.forall_mem_cons.2 ⟨subd11_2_41, List.forall_mem_cons.2 ⟨subd11_2_42, List.forall_mem_cons.2 ⟨subd11_2_43, List.forall_mem_cons.2 ⟨subd11_2_44, List.forall_mem_cons.2 ⟨subd11_2_45, List.forall_mem_cons.2 ⟨subd11_2_46, List.forall_mem_cons.2 ⟨subd11_2_47, List.forall_mem_cons.2 ⟨subd11_2_48, List.forall_mem_cons.2 ⟨subd11_2_49, List.forall_mem_cons.2 ⟨subd11_2_50, List.forall_mem_cons.2 ⟨subd11_2_51, List.forall_mem_cons.2 ⟨subd11_2_52, List.forall_mem_cons.2 ⟨subd11_2_53, List.forall_mem_cons.2 ⟨subd11_2_54, List.forall_mem_cons.2 ⟨subd11_2_55, List.forall_mem_cons.2 ⟨subd11_2_56, List.forall_mem_cons.2 ⟨subd11_2_57, List.forall_mem_cons.2 ⟨subd11_2_58, List.forall_mem_cons.2 ⟨subd11_2_59, List.forall_mem_cons.2 ⟨subd11_2_60, List.forall_mem_cons.2 ⟨subd11_2_61, List.forall_mem_cons.2 ⟨subd11_2_62, List.forall_mem_cons.2 ⟨subd11_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_64 : subd11_2 [-1, -2, 0] = true := by decide +kernel
theorem subd11_2_65 : subd11_2 [-1, -2, 1] = true := by decide +kernel
theorem subd11_2_66 : subd11_2 [-1, -2, 2] = true := by decide +kernel
theorem subd11_2_67 : subd11_2 [-1, -2, 3] = true := by decide +kernel
theorem subd11_2_68 : subd11_2 [-1, -2, 4] = true := by decide +kernel
theorem subd11_2_69 : subd11_2 [-1, -2, 5] = true := by decide +kernel
theorem subd11_2_70 : subd11_2 [-1, -2, 6] = true := by decide +kernel
theorem subd11_2_71 : subd11_2 [-1, -1, -11] = true := by decide +kernel
theorem subd11_2_72 : subd11_2 [-1, -1, -10] = true := by decide +kernel
theorem subd11_2_73 : subd11_2 [-1, -1, -9] = true := by decide +kernel
theorem subd11_2_74 : subd11_2 [-1, -1, -8] = true := by decide +kernel
theorem subd11_2_75 : subd11_2 [-1, -1, -7] = true := by decide +kernel
theorem subd11_2_76 : subd11_2 [-1, -1, -6] = true := by decide +kernel
theorem subd11_2_77 : subd11_2 [-1, -1, -5] = true := by decide +kernel
theorem subd11_2_78 : subd11_2 [-1, -1, -4] = true := by decide +kernel
theorem subd11_2_79 : subd11_2 [-1, -1, -3] = true := by decide +kernel
theorem subd11_2_80 : subd11_2 [-1, -1, -2] = true := by decide +kernel
theorem subd11_2_81 : subd11_2 [-1, -1, -1] = true := by decide +kernel
theorem subd11_2_82 : subd11_2 [-1, -1, 0] = true := by decide +kernel
theorem subd11_2_83 : subd11_2 [-1, -1, 1] = true := by decide +kernel
theorem subd11_2_84 : subd11_2 [-1, -1, 2] = true := by decide +kernel
theorem subd11_2_85 : subd11_2 [-1, -1, 3] = true := by decide +kernel
theorem subd11_2_86 : subd11_2 [-1, -1, 4] = true := by decide +kernel
theorem subd11_2_87 : subd11_2 [-1, -1, 5] = true := by decide +kernel
theorem subd11_2_88 : subd11_2 [-1, -1, 6] = true := by decide +kernel
theorem subd11_2_89 : subd11_2 [-1, -1, 7] = true := by decide +kernel
theorem subd11_2_90 : subd11_2 [-1, -1, 8] = true := by decide +kernel
theorem subd11_2_91 : subd11_2 [-1, -1, 9] = true := by decide +kernel
theorem subd11_2_92 : subd11_2 [-1, 0, -12] = true := by decide +kernel
theorem subd11_2_93 : subd11_2 [-1, 0, -11] = true := by decide +kernel
theorem subd11_2_94 : subd11_2 [-1, 0, -10] = true := by decide +kernel
theorem subd11_2_95 : subd11_2 [-1, 0, -9] = true := by decide +kernel
theorem sbd11_2_2 : ∀ q ∈ blkd11_2_2, subd11_2 q = true := by
  unfold blkd11_2_2
  exact List.forall_mem_cons.2 ⟨subd11_2_64, List.forall_mem_cons.2 ⟨subd11_2_65, List.forall_mem_cons.2 ⟨subd11_2_66, List.forall_mem_cons.2 ⟨subd11_2_67, List.forall_mem_cons.2 ⟨subd11_2_68, List.forall_mem_cons.2 ⟨subd11_2_69, List.forall_mem_cons.2 ⟨subd11_2_70, List.forall_mem_cons.2 ⟨subd11_2_71, List.forall_mem_cons.2 ⟨subd11_2_72, List.forall_mem_cons.2 ⟨subd11_2_73, List.forall_mem_cons.2 ⟨subd11_2_74, List.forall_mem_cons.2 ⟨subd11_2_75, List.forall_mem_cons.2 ⟨subd11_2_76, List.forall_mem_cons.2 ⟨subd11_2_77, List.forall_mem_cons.2 ⟨subd11_2_78, List.forall_mem_cons.2 ⟨subd11_2_79, List.forall_mem_cons.2 ⟨subd11_2_80, List.forall_mem_cons.2 ⟨subd11_2_81, List.forall_mem_cons.2 ⟨subd11_2_82, List.forall_mem_cons.2 ⟨subd11_2_83, List.forall_mem_cons.2 ⟨subd11_2_84, List.forall_mem_cons.2 ⟨subd11_2_85, List.forall_mem_cons.2 ⟨subd11_2_86, List.forall_mem_cons.2 ⟨subd11_2_87, List.forall_mem_cons.2 ⟨subd11_2_88, List.forall_mem_cons.2 ⟨subd11_2_89, List.forall_mem_cons.2 ⟨subd11_2_90, List.forall_mem_cons.2 ⟨subd11_2_91, List.forall_mem_cons.2 ⟨subd11_2_92, List.forall_mem_cons.2 ⟨subd11_2_93, List.forall_mem_cons.2 ⟨subd11_2_94, List.forall_mem_cons.2 ⟨subd11_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
