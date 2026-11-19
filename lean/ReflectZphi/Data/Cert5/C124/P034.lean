import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_8_64 : subd7_8 [0, -1, 9] = true := by decide +kernel
theorem subd7_8_65 : subd7_8 [0, -1, 10] = true := by decide +kernel
theorem subd7_8_66 : subd7_8 [0, -1, 11] = true := by decide +kernel
theorem subd7_8_67 : subd7_8 [0, -1, 12] = true := by decide +kernel
theorem subd7_8_68 : subd7_8 [0, -1, 13] = true := by decide +kernel
theorem subd7_8_69 : subd7_8 [0, -1, 14] = true := by decide +kernel
theorem subd7_8_70 : subd7_8 [0, -1, 15] = true := by decide +kernel
theorem subd7_8_71 : subd7_8 [0, -1, 16] = true := by decide +kernel
theorem subd7_8_72 : subd7_8 [0, -1, 17] = true := by decide +kernel
theorem subd7_8_73 : subd7_8 [0, -1, 18] = true := by decide +kernel
theorem subd7_8_74 : subd7_8 [0, -1, 19] = true := by decide +kernel
theorem subd7_8_75 : subd7_8 [0, -1, 20] = true := by decide +kernel
theorem subd7_8_76 : subd7_8 [0, -1, 21] = true := by decide +kernel
theorem subd7_8_77 : subd7_8 [0, -1, 22] = true := by decide +kernel
theorem subd7_8_78 : subd7_8 [0, 0, -45] = true := by decide +kernel
theorem subd7_8_79 : subd7_8 [0, 0, -44] = true := by decide +kernel
theorem subd7_8_80 : subd7_8 [0, 0, -43] = true := by decide +kernel
theorem subd7_8_81 : subd7_8 [0, 0, -42] = true := by decide +kernel
theorem subd7_8_82 : subd7_8 [0, 0, -41] = true := by decide +kernel
theorem subd7_8_83 : subd7_8 [0, 0, -40] = true := by decide +kernel
theorem subd7_8_84 : subd7_8 [0, 0, -39] = true := by decide +kernel
theorem subd7_8_85 : subd7_8 [0, 0, -38] = true := by decide +kernel
theorem subd7_8_86 : subd7_8 [0, 0, -37] = true := by decide +kernel
theorem subd7_8_87 : subd7_8 [0, 0, -36] = true := by decide +kernel
theorem subd7_8_88 : subd7_8 [0, 0, -35] = true := by decide +kernel
theorem subd7_8_89 : subd7_8 [0, 0, -34] = true := by decide +kernel
theorem subd7_8_90 : subd7_8 [0, 0, -33] = true := by decide +kernel
theorem subd7_8_91 : subd7_8 [0, 0, -32] = true := by decide +kernel
theorem subd7_8_92 : subd7_8 [0, 0, -31] = true := by decide +kernel
theorem subd7_8_93 : subd7_8 [0, 0, -30] = true := by decide +kernel
theorem subd7_8_94 : subd7_8 [0, 0, -29] = true := by decide +kernel
theorem subd7_8_95 : subd7_8 [0, 0, -28] = true := by decide +kernel
theorem sbd7_8_2 : ∀ q ∈ blkd7_8_2, subd7_8 q = true := by
  unfold blkd7_8_2
  exact List.forall_mem_cons.2 ⟨subd7_8_64, List.forall_mem_cons.2 ⟨subd7_8_65, List.forall_mem_cons.2 ⟨subd7_8_66, List.forall_mem_cons.2 ⟨subd7_8_67, List.forall_mem_cons.2 ⟨subd7_8_68, List.forall_mem_cons.2 ⟨subd7_8_69, List.forall_mem_cons.2 ⟨subd7_8_70, List.forall_mem_cons.2 ⟨subd7_8_71, List.forall_mem_cons.2 ⟨subd7_8_72, List.forall_mem_cons.2 ⟨subd7_8_73, List.forall_mem_cons.2 ⟨subd7_8_74, List.forall_mem_cons.2 ⟨subd7_8_75, List.forall_mem_cons.2 ⟨subd7_8_76, List.forall_mem_cons.2 ⟨subd7_8_77, List.forall_mem_cons.2 ⟨subd7_8_78, List.forall_mem_cons.2 ⟨subd7_8_79, List.forall_mem_cons.2 ⟨subd7_8_80, List.forall_mem_cons.2 ⟨subd7_8_81, List.forall_mem_cons.2 ⟨subd7_8_82, List.forall_mem_cons.2 ⟨subd7_8_83, List.forall_mem_cons.2 ⟨subd7_8_84, List.forall_mem_cons.2 ⟨subd7_8_85, List.forall_mem_cons.2 ⟨subd7_8_86, List.forall_mem_cons.2 ⟨subd7_8_87, List.forall_mem_cons.2 ⟨subd7_8_88, List.forall_mem_cons.2 ⟨subd7_8_89, List.forall_mem_cons.2 ⟨subd7_8_90, List.forall_mem_cons.2 ⟨subd7_8_91, List.forall_mem_cons.2 ⟨subd7_8_92, List.forall_mem_cons.2 ⟨subd7_8_93, List.forall_mem_cons.2 ⟨subd7_8_94, List.forall_mem_cons.2 ⟨subd7_8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_8_96 : subd7_8 [0, 0, -27] = true := by decide +kernel
theorem subd7_8_97 : subd7_8 [0, 0, -26] = true := by decide +kernel
theorem subd7_8_98 : subd7_8 [0, 0, -25] = true := by decide +kernel
theorem subd7_8_99 : subd7_8 [0, 0, -24] = true := by decide +kernel
theorem subd7_8_100 : subd7_8 [0, 0, -23] = true := by decide +kernel
theorem subd7_8_101 : subd7_8 [0, 0, -22] = true := by decide +kernel
theorem subd7_8_102 : subd7_8 [0, 0, -21] = true := by decide +kernel
theorem subd7_8_103 : subd7_8 [0, 0, -20] = true := by decide +kernel
theorem subd7_8_104 : subd7_8 [0, 0, -19] = true := by decide +kernel
theorem subd7_8_105 : subd7_8 [0, 0, -18] = true := by decide +kernel
theorem subd7_8_106 : subd7_8 [0, 0, -17] = true := by decide +kernel
theorem subd7_8_107 : subd7_8 [0, 0, -16] = true := by decide +kernel
theorem subd7_8_108 : subd7_8 [0, 0, -15] = true := by decide +kernel
theorem subd7_8_109 : subd7_8 [0, 0, -14] = true := by decide +kernel
theorem subd7_8_110 : subd7_8 [0, 0, -13] = true := by decide +kernel
theorem subd7_8_111 : subd7_8 [0, 0, -12] = true := by decide +kernel
theorem subd7_8_112 : subd7_8 [0, 0, -11] = true := by decide +kernel
theorem subd7_8_113 : subd7_8 [0, 0, -10] = true := by decide +kernel
theorem subd7_8_114 : subd7_8 [0, 0, -9] = true := by decide +kernel
theorem subd7_8_115 : subd7_8 [0, 0, -8] = true := by decide +kernel
theorem subd7_8_116 : subd7_8 [0, 0, -7] = true := by decide +kernel
theorem subd7_8_117 : subd7_8 [0, 0, -6] = true := by decide +kernel
theorem subd7_8_118 : subd7_8 [0, 0, -5] = true := by decide +kernel
theorem subd7_8_119 : subd7_8 [0, 0, -4] = true := by decide +kernel
theorem subd7_8_120 : subd7_8 [0, 0, -3] = true := by decide +kernel
theorem subd7_8_121 : subd7_8 [0, 0, -2] = true := by decide +kernel
theorem subd7_8_122 : subd7_8 [0, 0, -1] = true := by decide +kernel
theorem subd7_8_123 : subd7_8 [0, 0, 0] = true := by decide +kernel
theorem subd7_8_124 : subd7_8 [0, 0, 1] = true := by decide +kernel
theorem subd7_8_125 : subd7_8 [0, 0, 2] = true := by decide +kernel
theorem subd7_8_126 : subd7_8 [0, 0, 3] = true := by decide +kernel
theorem subd7_8_127 : subd7_8 [0, 0, 4] = true := by decide +kernel
theorem sbd7_8_3 : ∀ q ∈ blkd7_8_3, subd7_8 q = true := by
  unfold blkd7_8_3
  exact List.forall_mem_cons.2 ⟨subd7_8_96, List.forall_mem_cons.2 ⟨subd7_8_97, List.forall_mem_cons.2 ⟨subd7_8_98, List.forall_mem_cons.2 ⟨subd7_8_99, List.forall_mem_cons.2 ⟨subd7_8_100, List.forall_mem_cons.2 ⟨subd7_8_101, List.forall_mem_cons.2 ⟨subd7_8_102, List.forall_mem_cons.2 ⟨subd7_8_103, List.forall_mem_cons.2 ⟨subd7_8_104, List.forall_mem_cons.2 ⟨subd7_8_105, List.forall_mem_cons.2 ⟨subd7_8_106, List.forall_mem_cons.2 ⟨subd7_8_107, List.forall_mem_cons.2 ⟨subd7_8_108, List.forall_mem_cons.2 ⟨subd7_8_109, List.forall_mem_cons.2 ⟨subd7_8_110, List.forall_mem_cons.2 ⟨subd7_8_111, List.forall_mem_cons.2 ⟨subd7_8_112, List.forall_mem_cons.2 ⟨subd7_8_113, List.forall_mem_cons.2 ⟨subd7_8_114, List.forall_mem_cons.2 ⟨subd7_8_115, List.forall_mem_cons.2 ⟨subd7_8_116, List.forall_mem_cons.2 ⟨subd7_8_117, List.forall_mem_cons.2 ⟨subd7_8_118, List.forall_mem_cons.2 ⟨subd7_8_119, List.forall_mem_cons.2 ⟨subd7_8_120, List.forall_mem_cons.2 ⟨subd7_8_121, List.forall_mem_cons.2 ⟨subd7_8_122, List.forall_mem_cons.2 ⟨subd7_8_123, List.forall_mem_cons.2 ⟨subd7_8_124, List.forall_mem_cons.2 ⟨subd7_8_125, List.forall_mem_cons.2 ⟨subd7_8_126, List.forall_mem_cons.2 ⟨subd7_8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_8_128 : subd7_8 [0, 0, 5] = true := by decide +kernel
theorem subd7_8_129 : subd7_8 [0, 0, 6] = true := by decide +kernel
theorem subd7_8_130 : subd7_8 [0, 0, 7] = true := by decide +kernel
theorem subd7_8_131 : subd7_8 [0, 0, 8] = true := by decide +kernel
theorem subd7_8_132 : subd7_8 [0, 0, 9] = true := by decide +kernel
theorem subd7_8_133 : subd7_8 [0, 0, 10] = true := by decide +kernel
theorem subd7_8_134 : subd7_8 [0, 0, 11] = true := by decide +kernel
theorem subd7_8_135 : subd7_8 [0, 0, 12] = true := by decide +kernel
theorem subd7_8_136 : subd7_8 [0, 0, 13] = true := by decide +kernel
theorem subd7_8_137 : subd7_8 [0, 0, 14] = true := by decide +kernel
theorem subd7_8_138 : subd7_8 [0, 0, 15] = true := by decide +kernel
theorem subd7_8_139 : subd7_8 [0, 0, 16] = true := by decide +kernel
theorem subd7_8_140 : subd7_8 [0, 0, 17] = true := by decide +kernel
theorem subd7_8_141 : subd7_8 [0, 0, 18] = true := by decide +kernel
theorem subd7_8_142 : subd7_8 [0, 0, 19] = true := by decide +kernel
theorem subd7_8_143 : subd7_8 [0, 0, 20] = true := by decide +kernel
theorem subd7_8_144 : subd7_8 [0, 0, 21] = true := by decide +kernel
theorem subd7_8_145 : subd7_8 [0, 0, 22] = true := by decide +kernel
theorem subd7_8_146 : subd7_8 [0, 0, 23] = true := by decide +kernel
theorem subd7_8_147 : subd7_8 [0, 0, 24] = true := by decide +kernel
theorem subd7_8_148 : subd7_8 [0, 0, 25] = true := by decide +kernel
theorem subd7_8_149 : subd7_8 [0, 0, 26] = true := by decide +kernel
theorem subd7_8_150 : subd7_8 [0, 0, 27] = true := by decide +kernel
theorem subd7_8_151 : subd7_8 [0, 0, 28] = true := by decide +kernel
theorem subd7_8_152 : subd7_8 [0, 0, 29] = true := by decide +kernel
theorem subd7_8_153 : subd7_8 [0, 0, 30] = true := by decide +kernel
theorem subd7_8_154 : subd7_8 [0, 0, 31] = true := by decide +kernel
theorem subd7_8_155 : subd7_8 [0, 0, 32] = true := by decide +kernel
theorem subd7_8_156 : subd7_8 [0, 0, 33] = true := by decide +kernel
theorem subd7_8_157 : subd7_8 [0, 0, 34] = true := by decide +kernel
theorem subd7_8_158 : subd7_8 [0, 0, 35] = true := by decide +kernel
theorem subd7_8_159 : subd7_8 [0, 0, 36] = true := by decide +kernel
theorem sbd7_8_4 : ∀ q ∈ blkd7_8_4, subd7_8 q = true := by
  unfold blkd7_8_4
  exact List.forall_mem_cons.2 ⟨subd7_8_128, List.forall_mem_cons.2 ⟨subd7_8_129, List.forall_mem_cons.2 ⟨subd7_8_130, List.forall_mem_cons.2 ⟨subd7_8_131, List.forall_mem_cons.2 ⟨subd7_8_132, List.forall_mem_cons.2 ⟨subd7_8_133, List.forall_mem_cons.2 ⟨subd7_8_134, List.forall_mem_cons.2 ⟨subd7_8_135, List.forall_mem_cons.2 ⟨subd7_8_136, List.forall_mem_cons.2 ⟨subd7_8_137, List.forall_mem_cons.2 ⟨subd7_8_138, List.forall_mem_cons.2 ⟨subd7_8_139, List.forall_mem_cons.2 ⟨subd7_8_140, List.forall_mem_cons.2 ⟨subd7_8_141, List.forall_mem_cons.2 ⟨subd7_8_142, List.forall_mem_cons.2 ⟨subd7_8_143, List.forall_mem_cons.2 ⟨subd7_8_144, List.forall_mem_cons.2 ⟨subd7_8_145, List.forall_mem_cons.2 ⟨subd7_8_146, List.forall_mem_cons.2 ⟨subd7_8_147, List.forall_mem_cons.2 ⟨subd7_8_148, List.forall_mem_cons.2 ⟨subd7_8_149, List.forall_mem_cons.2 ⟨subd7_8_150, List.forall_mem_cons.2 ⟨subd7_8_151, List.forall_mem_cons.2 ⟨subd7_8_152, List.forall_mem_cons.2 ⟨subd7_8_153, List.forall_mem_cons.2 ⟨subd7_8_154, List.forall_mem_cons.2 ⟨subd7_8_155, List.forall_mem_cons.2 ⟨subd7_8_156, List.forall_mem_cons.2 ⟨subd7_8_157, List.forall_mem_cons.2 ⟨subd7_8_158, List.forall_mem_cons.2 ⟨subd7_8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
