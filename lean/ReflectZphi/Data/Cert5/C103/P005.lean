import ReflectZphi.Data.Cert5.C103.Base

namespace ReflectZphi.Data.Cert5.C103

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_96 : subd5_0 [0, 0, 3] = true := by decide +kernel
theorem subd5_0_97 : subd5_0 [0, 0, 4] = true := by decide +kernel
theorem subd5_0_98 : subd5_0 [0, 0, 5] = true := by decide +kernel
theorem subd5_0_99 : subd5_0 [0, 0, 6] = true := by decide +kernel
theorem subd5_0_100 : subd5_0 [0, 0, 7] = true := by decide +kernel
theorem subd5_0_101 : subd5_0 [0, 1, -8] = true := by decide +kernel
theorem subd5_0_102 : subd5_0 [0, 1, -7] = true := by decide +kernel
theorem subd5_0_103 : subd5_0 [0, 1, -6] = true := by decide +kernel
theorem subd5_0_104 : subd5_0 [0, 1, -5] = true := by decide +kernel
theorem subd5_0_105 : subd5_0 [0, 1, -4] = true := by decide +kernel
theorem subd5_0_106 : subd5_0 [0, 1, -3] = true := by decide +kernel
theorem subd5_0_107 : subd5_0 [0, 1, -2] = true := by decide +kernel
theorem subd5_0_108 : subd5_0 [0, 1, -1] = true := by decide +kernel
theorem subd5_0_109 : subd5_0 [0, 1, 0] = true := by decide +kernel
theorem subd5_0_110 : subd5_0 [0, 1, 1] = true := by decide +kernel
theorem subd5_0_111 : subd5_0 [0, 1, 2] = true := by decide +kernel
theorem subd5_0_112 : subd5_0 [0, 1, 3] = true := by decide +kernel
theorem subd5_0_113 : subd5_0 [0, 1, 4] = true := by decide +kernel
theorem subd5_0_114 : subd5_0 [0, 1, 5] = true := by decide +kernel
theorem subd5_0_115 : subd5_0 [0, 1, 6] = true := by decide +kernel
theorem subd5_0_116 : subd5_0 [0, 1, 7] = true := by decide +kernel
theorem subd5_0_117 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_118 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_119 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_120 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_121 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_122 : subd5_0 [1, -1, -8] = true := by decide +kernel
theorem subd5_0_123 : subd5_0 [1, -1, -7] = true := by decide +kernel
theorem subd5_0_124 : subd5_0 [1, -1, -6] = true := by decide +kernel
theorem subd5_0_125 : subd5_0 [1, -1, -5] = true := by decide +kernel
theorem subd5_0_126 : subd5_0 [1, -1, -4] = true := by decide +kernel
theorem subd5_0_127 : subd5_0 [1, -1, -3] = true := by decide +kernel
theorem sbd5_0_3 : ∀ q ∈ blkd5_0_3, subd5_0 q = true := by
  unfold blkd5_0_3
  exact List.forall_mem_cons.2 ⟨subd5_0_96, List.forall_mem_cons.2 ⟨subd5_0_97, List.forall_mem_cons.2 ⟨subd5_0_98, List.forall_mem_cons.2 ⟨subd5_0_99, List.forall_mem_cons.2 ⟨subd5_0_100, List.forall_mem_cons.2 ⟨subd5_0_101, List.forall_mem_cons.2 ⟨subd5_0_102, List.forall_mem_cons.2 ⟨subd5_0_103, List.forall_mem_cons.2 ⟨subd5_0_104, List.forall_mem_cons.2 ⟨subd5_0_105, List.forall_mem_cons.2 ⟨subd5_0_106, List.forall_mem_cons.2 ⟨subd5_0_107, List.forall_mem_cons.2 ⟨subd5_0_108, List.forall_mem_cons.2 ⟨subd5_0_109, List.forall_mem_cons.2 ⟨subd5_0_110, List.forall_mem_cons.2 ⟨subd5_0_111, List.forall_mem_cons.2 ⟨subd5_0_112, List.forall_mem_cons.2 ⟨subd5_0_113, List.forall_mem_cons.2 ⟨subd5_0_114, List.forall_mem_cons.2 ⟨subd5_0_115, List.forall_mem_cons.2 ⟨subd5_0_116, List.forall_mem_cons.2 ⟨subd5_0_117, List.forall_mem_cons.2 ⟨subd5_0_118, List.forall_mem_cons.2 ⟨subd5_0_119, List.forall_mem_cons.2 ⟨subd5_0_120, List.forall_mem_cons.2 ⟨subd5_0_121, List.forall_mem_cons.2 ⟨subd5_0_122, List.forall_mem_cons.2 ⟨subd5_0_123, List.forall_mem_cons.2 ⟨subd5_0_124, List.forall_mem_cons.2 ⟨subd5_0_125, List.forall_mem_cons.2 ⟨subd5_0_126, List.forall_mem_cons.2 ⟨subd5_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_128 : subd5_0 [1, -1, -2] = true := by decide +kernel
theorem subd5_0_129 : subd5_0 [1, -1, -1] = true := by decide +kernel
theorem subd5_0_130 : subd5_0 [1, -1, 0] = true := by decide +kernel
theorem subd5_0_131 : subd5_0 [1, -1, 1] = true := by decide +kernel
theorem subd5_0_132 : subd5_0 [1, -1, 2] = true := by decide +kernel
theorem subd5_0_133 : subd5_0 [1, -1, 3] = true := by decide +kernel
theorem subd5_0_134 : subd5_0 [1, -1, 4] = true := by decide +kernel
theorem subd5_0_135 : subd5_0 [1, -1, 5] = true := by decide +kernel
theorem subd5_0_136 : subd5_0 [1, -1, 6] = true := by decide +kernel
theorem subd5_0_137 : subd5_0 [1, -1, 7] = true := by decide +kernel
theorem subd5_0_138 : subd5_0 [1, 0, -8] = true := by decide +kernel
theorem subd5_0_139 : subd5_0 [1, 0, -7] = true := by decide +kernel
theorem subd5_0_140 : subd5_0 [1, 0, -6] = true := by decide +kernel
theorem subd5_0_141 : subd5_0 [1, 0, -5] = true := by decide +kernel
theorem subd5_0_142 : subd5_0 [1, 0, -4] = true := by decide +kernel
theorem subd5_0_143 : subd5_0 [1, 0, -3] = true := by decide +kernel
theorem subd5_0_144 : subd5_0 [1, 0, -2] = true := by decide +kernel
theorem subd5_0_145 : subd5_0 [1, 0, -1] = true := by decide +kernel
theorem subd5_0_146 : subd5_0 [1, 0, 0] = true := by decide +kernel
theorem subd5_0_147 : subd5_0 [1, 0, 1] = true := by decide +kernel
theorem subd5_0_148 : subd5_0 [1, 0, 2] = true := by decide +kernel
theorem subd5_0_149 : subd5_0 [1, 0, 3] = true := by decide +kernel
theorem subd5_0_150 : subd5_0 [1, 0, 4] = true := by decide +kernel
theorem subd5_0_151 : subd5_0 [1, 0, 5] = true := by decide +kernel
theorem subd5_0_152 : subd5_0 [1, 0, 6] = true := by decide +kernel
theorem subd5_0_153 : subd5_0 [1, 0, 7] = true := by decide +kernel
theorem subd5_0_154 : subd5_0 [1, 1, -7] = true := by decide +kernel
theorem subd5_0_155 : subd5_0 [1, 1, -6] = true := by decide +kernel
theorem subd5_0_156 : subd5_0 [1, 1, -5] = true := by decide +kernel
theorem subd5_0_157 : subd5_0 [1, 1, -4] = true := by decide +kernel
theorem subd5_0_158 : subd5_0 [1, 1, -3] = true := by decide +kernel
theorem subd5_0_159 : subd5_0 [1, 1, -2] = true := by decide +kernel
theorem sbd5_0_4 : ∀ q ∈ blkd5_0_4, subd5_0 q = true := by
  unfold blkd5_0_4
  exact List.forall_mem_cons.2 ⟨subd5_0_128, List.forall_mem_cons.2 ⟨subd5_0_129, List.forall_mem_cons.2 ⟨subd5_0_130, List.forall_mem_cons.2 ⟨subd5_0_131, List.forall_mem_cons.2 ⟨subd5_0_132, List.forall_mem_cons.2 ⟨subd5_0_133, List.forall_mem_cons.2 ⟨subd5_0_134, List.forall_mem_cons.2 ⟨subd5_0_135, List.forall_mem_cons.2 ⟨subd5_0_136, List.forall_mem_cons.2 ⟨subd5_0_137, List.forall_mem_cons.2 ⟨subd5_0_138, List.forall_mem_cons.2 ⟨subd5_0_139, List.forall_mem_cons.2 ⟨subd5_0_140, List.forall_mem_cons.2 ⟨subd5_0_141, List.forall_mem_cons.2 ⟨subd5_0_142, List.forall_mem_cons.2 ⟨subd5_0_143, List.forall_mem_cons.2 ⟨subd5_0_144, List.forall_mem_cons.2 ⟨subd5_0_145, List.forall_mem_cons.2 ⟨subd5_0_146, List.forall_mem_cons.2 ⟨subd5_0_147, List.forall_mem_cons.2 ⟨subd5_0_148, List.forall_mem_cons.2 ⟨subd5_0_149, List.forall_mem_cons.2 ⟨subd5_0_150, List.forall_mem_cons.2 ⟨subd5_0_151, List.forall_mem_cons.2 ⟨subd5_0_152, List.forall_mem_cons.2 ⟨subd5_0_153, List.forall_mem_cons.2 ⟨subd5_0_154, List.forall_mem_cons.2 ⟨subd5_0_155, List.forall_mem_cons.2 ⟨subd5_0_156, List.forall_mem_cons.2 ⟨subd5_0_157, List.forall_mem_cons.2 ⟨subd5_0_158, List.forall_mem_cons.2 ⟨subd5_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_160 : subd5_0 [1, 1, -1] = true := by decide +kernel
theorem subd5_0_161 : subd5_0 [1, 1, 0] = true := by decide +kernel
theorem subd5_0_162 : subd5_0 [1, 1, 1] = true := by decide +kernel
theorem subd5_0_163 : subd5_0 [1, 1, 2] = true := by decide +kernel
theorem subd5_0_164 : subd5_0 [1, 1, 3] = true := by decide +kernel
theorem subd5_0_165 : subd5_0 [1, 1, 4] = true := by decide +kernel
theorem subd5_0_166 : subd5_0 [1, 1, 5] = true := by decide +kernel
theorem subd5_0_167 : subd5_0 [1, 1, 6] = true := by decide +kernel
theorem subd5_0_168 : subd5_0 [1, 1, 7] = true := by decide +kernel
theorem subd5_0_169 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_170 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_171 : subd5_0 [2, -4] = true := by decide +kernel
theorem subd5_0_172 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_173 : subd5_0 [2, -2] = true := by decide +kernel
theorem subd5_0_174 : subd5_0 [2, -1] = true := by decide +kernel
theorem subd5_0_175 : subd5_0 [2, 0] = true := by decide +kernel
theorem subd5_0_176 : subd5_0 [2, 1] = true := by decide +kernel
theorem subd5_0_177 : subd5_0 [2, 2] = true := by decide +kernel
theorem subd5_0_178 : subd5_0 [2, 3] = true := by decide +kernel
theorem subd5_0_179 : subd5_0 [3, -3] = true := by decide +kernel
theorem subd5_0_180 : subd5_0 [3, -2] = true := by decide +kernel
theorem subd5_0_181 : subd5_0 [3, -1] = true := by decide +kernel
theorem subd5_0_182 : subd5_0 [3, 0] = true := by decide +kernel
theorem subd5_0_183 : subd5_0 [3, 1] = true := by decide +kernel
theorem subd5_0_184 : subd5_0 [3, 2] = true := by decide +kernel
theorem sbd5_0_5 : ∀ q ∈ blkd5_0_5, subd5_0 q = true := by
  unfold blkd5_0_5
  exact List.forall_mem_cons.2 ⟨subd5_0_160, List.forall_mem_cons.2 ⟨subd5_0_161, List.forall_mem_cons.2 ⟨subd5_0_162, List.forall_mem_cons.2 ⟨subd5_0_163, List.forall_mem_cons.2 ⟨subd5_0_164, List.forall_mem_cons.2 ⟨subd5_0_165, List.forall_mem_cons.2 ⟨subd5_0_166, List.forall_mem_cons.2 ⟨subd5_0_167, List.forall_mem_cons.2 ⟨subd5_0_168, List.forall_mem_cons.2 ⟨subd5_0_169, List.forall_mem_cons.2 ⟨subd5_0_170, List.forall_mem_cons.2 ⟨subd5_0_171, List.forall_mem_cons.2 ⟨subd5_0_172, List.forall_mem_cons.2 ⟨subd5_0_173, List.forall_mem_cons.2 ⟨subd5_0_174, List.forall_mem_cons.2 ⟨subd5_0_175, List.forall_mem_cons.2 ⟨subd5_0_176, List.forall_mem_cons.2 ⟨subd5_0_177, List.forall_mem_cons.2 ⟨subd5_0_178, List.forall_mem_cons.2 ⟨subd5_0_179, List.forall_mem_cons.2 ⟨subd5_0_180, List.forall_mem_cons.2 ⟨subd5_0_181, List.forall_mem_cons.2 ⟨subd5_0_182, List.forall_mem_cons.2 ⟨subd5_0_183, List.forall_mem_cons.2 ⟨subd5_0_184, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-4] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-3, -4] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-3, -3] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-3, -2] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-3, -1] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-3, 0] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-3, 1] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-3, 2] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-3, 3] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-3, 4] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-2, -5] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-2, -4] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-2, -3] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-2, -2] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-2, -1] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [-2, 0] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [-2, 1] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [-2, 2] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [-2, 3] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [-2, 4] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [-2, 5] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [-1, -5] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [-1, -4] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [-1, 3] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [-1, 4] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [-1, 5] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [0, -6] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [0, -5] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [0, -4] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_38 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_39 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_40 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_41 : subd5_1 [0, 3] = true := by decide +kernel
theorem subd5_1_42 : subd5_1 [0, 4] = true := by decide +kernel
theorem subd5_1_43 : subd5_1 [0, 5] = true := by decide +kernel
theorem subd5_1_44 : subd5_1 [1, -6] = true := by decide +kernel
theorem subd5_1_45 : subd5_1 [1, -5] = true := by decide +kernel
theorem subd5_1_46 : subd5_1 [1, -4] = true := by decide +kernel
theorem subd5_1_47 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_48 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_49 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_50 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_51 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_52 : subd5_1 [1, 2] = true := by decide +kernel
theorem subd5_1_53 : subd5_1 [1, 3] = true := by decide +kernel
theorem subd5_1_54 : subd5_1 [1, 4] = true := by decide +kernel
theorem subd5_1_55 : subd5_1 [2, -6] = true := by decide +kernel
theorem subd5_1_56 : subd5_1 [2, -5] = true := by decide +kernel
theorem subd5_1_57 : subd5_1 [2, -4] = true := by decide +kernel
theorem subd5_1_58 : subd5_1 [2, -3] = true := by decide +kernel
theorem subd5_1_59 : subd5_1 [2, -2] = true := by decide +kernel
theorem subd5_1_60 : subd5_1 [2, -1] = true := by decide +kernel
theorem subd5_1_61 : subd5_1 [2, 0] = true := by decide +kernel
theorem subd5_1_62 : subd5_1 [2, 1] = true := by decide +kernel
theorem subd5_1_63 : subd5_1 [2, 2] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_cons.2 ⟨subd5_1_38, List.forall_mem_cons.2 ⟨subd5_1_39, List.forall_mem_cons.2 ⟨subd5_1_40, List.forall_mem_cons.2 ⟨subd5_1_41, List.forall_mem_cons.2 ⟨subd5_1_42, List.forall_mem_cons.2 ⟨subd5_1_43, List.forall_mem_cons.2 ⟨subd5_1_44, List.forall_mem_cons.2 ⟨subd5_1_45, List.forall_mem_cons.2 ⟨subd5_1_46, List.forall_mem_cons.2 ⟨subd5_1_47, List.forall_mem_cons.2 ⟨subd5_1_48, List.forall_mem_cons.2 ⟨subd5_1_49, List.forall_mem_cons.2 ⟨subd5_1_50, List.forall_mem_cons.2 ⟨subd5_1_51, List.forall_mem_cons.2 ⟨subd5_1_52, List.forall_mem_cons.2 ⟨subd5_1_53, List.forall_mem_cons.2 ⟨subd5_1_54, List.forall_mem_cons.2 ⟨subd5_1_55, List.forall_mem_cons.2 ⟨subd5_1_56, List.forall_mem_cons.2 ⟨subd5_1_57, List.forall_mem_cons.2 ⟨subd5_1_58, List.forall_mem_cons.2 ⟨subd5_1_59, List.forall_mem_cons.2 ⟨subd5_1_60, List.forall_mem_cons.2 ⟨subd5_1_61, List.forall_mem_cons.2 ⟨subd5_1_62, List.forall_mem_cons.2 ⟨subd5_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_64 : subd5_1 [2, 3] = true := by decide +kernel
theorem subd5_1_65 : subd5_1 [2, 4] = true := by decide +kernel
theorem subd5_1_66 : subd5_1 [3, -5] = true := by decide +kernel
theorem subd5_1_67 : subd5_1 [3, -4] = true := by decide +kernel
theorem subd5_1_68 : subd5_1 [3, -3] = true := by decide +kernel
theorem subd5_1_69 : subd5_1 [3, -2] = true := by decide +kernel
theorem subd5_1_70 : subd5_1 [3, -1] = true := by decide +kernel
theorem subd5_1_71 : subd5_1 [3, 0] = true := by decide +kernel
theorem subd5_1_72 : subd5_1 [3, 1] = true := by decide +kernel
theorem subd5_1_73 : subd5_1 [3, 2] = true := by decide +kernel
theorem subd5_1_74 : subd5_1 [3, 3] = true := by decide +kernel
theorem subd5_1_75 : subd5_1 [4] = true := by decide +kernel
theorem sbd5_1_2 : ∀ q ∈ blkd5_1_2, subd5_1 q = true := by
  unfold blkd5_1_2
  exact List.forall_mem_cons.2 ⟨subd5_1_64, List.forall_mem_cons.2 ⟨subd5_1_65, List.forall_mem_cons.2 ⟨subd5_1_66, List.forall_mem_cons.2 ⟨subd5_1_67, List.forall_mem_cons.2 ⟨subd5_1_68, List.forall_mem_cons.2 ⟨subd5_1_69, List.forall_mem_cons.2 ⟨subd5_1_70, List.forall_mem_cons.2 ⟨subd5_1_71, List.forall_mem_cons.2 ⟨subd5_1_72, List.forall_mem_cons.2 ⟨subd5_1_73, List.forall_mem_cons.2 ⟨subd5_1_74, List.forall_mem_cons.2 ⟨subd5_1_75, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C103
