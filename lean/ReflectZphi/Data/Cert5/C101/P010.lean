import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_128 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_129 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_130 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_131 : subd10_0 [1, 4] = true := by decide +kernel
theorem subd10_0_132 : subd10_0 [1, 5] = true := by decide +kernel
theorem subd10_0_133 : subd10_0 [1, 6] = true := by decide +kernel
theorem subd10_0_134 : subd10_0 [2, -8] = true := by decide +kernel
theorem subd10_0_135 : subd10_0 [2, -7] = true := by decide +kernel
theorem subd10_0_136 : subd10_0 [2, -6] = true := by decide +kernel
theorem subd10_0_137 : subd10_0 [2, -5] = true := by decide +kernel
theorem subd10_0_138 : subd10_0 [2, -4] = true := by decide +kernel
theorem subd10_0_139 : subd10_0 [2, -3] = true := by decide +kernel
theorem subd10_0_140 : subd10_0 [2, -2] = true := by decide +kernel
theorem subd10_0_141 : subd10_0 [2, -1] = true := by decide +kernel
theorem subd10_0_142 : subd10_0 [2, 0] = true := by decide +kernel
theorem subd10_0_143 : subd10_0 [2, 1] = true := by decide +kernel
theorem subd10_0_144 : subd10_0 [2, 2] = true := by decide +kernel
theorem subd10_0_145 : subd10_0 [2, 3] = true := by decide +kernel
theorem subd10_0_146 : subd10_0 [2, 4] = true := by decide +kernel
theorem subd10_0_147 : subd10_0 [2, 5] = true := by decide +kernel
theorem subd10_0_148 : subd10_0 [2, 6] = true := by decide +kernel
theorem subd10_0_149 : subd10_0 [3, -8] = true := by decide +kernel
theorem subd10_0_150 : subd10_0 [3, -7] = true := by decide +kernel
theorem subd10_0_151 : subd10_0 [3, -6] = true := by decide +kernel
theorem subd10_0_152 : subd10_0 [3, -5] = true := by decide +kernel
theorem subd10_0_153 : subd10_0 [3, -4] = true := by decide +kernel
theorem subd10_0_154 : subd10_0 [3, -3] = true := by decide +kernel
theorem subd10_0_155 : subd10_0 [3, -2] = true := by decide +kernel
theorem subd10_0_156 : subd10_0 [3, -1] = true := by decide +kernel
theorem subd10_0_157 : subd10_0 [3, 0] = true := by decide +kernel
theorem subd10_0_158 : subd10_0 [3, 1] = true := by decide +kernel
theorem subd10_0_159 : subd10_0 [3, 2] = true := by decide +kernel
theorem sbd10_0_4 : ∀ q ∈ blkd10_0_4, subd10_0 q = true := by
  unfold blkd10_0_4
  exact List.forall_mem_cons.2 ⟨subd10_0_128, List.forall_mem_cons.2 ⟨subd10_0_129, List.forall_mem_cons.2 ⟨subd10_0_130, List.forall_mem_cons.2 ⟨subd10_0_131, List.forall_mem_cons.2 ⟨subd10_0_132, List.forall_mem_cons.2 ⟨subd10_0_133, List.forall_mem_cons.2 ⟨subd10_0_134, List.forall_mem_cons.2 ⟨subd10_0_135, List.forall_mem_cons.2 ⟨subd10_0_136, List.forall_mem_cons.2 ⟨subd10_0_137, List.forall_mem_cons.2 ⟨subd10_0_138, List.forall_mem_cons.2 ⟨subd10_0_139, List.forall_mem_cons.2 ⟨subd10_0_140, List.forall_mem_cons.2 ⟨subd10_0_141, List.forall_mem_cons.2 ⟨subd10_0_142, List.forall_mem_cons.2 ⟨subd10_0_143, List.forall_mem_cons.2 ⟨subd10_0_144, List.forall_mem_cons.2 ⟨subd10_0_145, List.forall_mem_cons.2 ⟨subd10_0_146, List.forall_mem_cons.2 ⟨subd10_0_147, List.forall_mem_cons.2 ⟨subd10_0_148, List.forall_mem_cons.2 ⟨subd10_0_149, List.forall_mem_cons.2 ⟨subd10_0_150, List.forall_mem_cons.2 ⟨subd10_0_151, List.forall_mem_cons.2 ⟨subd10_0_152, List.forall_mem_cons.2 ⟨subd10_0_153, List.forall_mem_cons.2 ⟨subd10_0_154, List.forall_mem_cons.2 ⟨subd10_0_155, List.forall_mem_cons.2 ⟨subd10_0_156, List.forall_mem_cons.2 ⟨subd10_0_157, List.forall_mem_cons.2 ⟨subd10_0_158, List.forall_mem_cons.2 ⟨subd10_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_160 : subd10_0 [3, 3] = true := by decide +kernel
theorem subd10_0_161 : subd10_0 [3, 4] = true := by decide +kernel
theorem subd10_0_162 : subd10_0 [3, 5] = true := by decide +kernel
theorem subd10_0_163 : subd10_0 [4, -8] = true := by decide +kernel
theorem subd10_0_164 : subd10_0 [4, -7] = true := by decide +kernel
theorem subd10_0_165 : subd10_0 [4, -6] = true := by decide +kernel
theorem subd10_0_166 : subd10_0 [4, -5] = true := by decide +kernel
theorem subd10_0_167 : subd10_0 [4, -4] = true := by decide +kernel
theorem subd10_0_168 : subd10_0 [4, -3] = true := by decide +kernel
theorem subd10_0_169 : subd10_0 [4, -2] = true := by decide +kernel
theorem subd10_0_170 : subd10_0 [4, -1] = true := by decide +kernel
theorem subd10_0_171 : subd10_0 [4, 0] = true := by decide +kernel
theorem subd10_0_172 : subd10_0 [4, 1] = true := by decide +kernel
theorem subd10_0_173 : subd10_0 [4, 2] = true := by decide +kernel
theorem subd10_0_174 : subd10_0 [4, 3] = true := by decide +kernel
theorem subd10_0_175 : subd10_0 [4, 4] = true := by decide +kernel
theorem subd10_0_176 : subd10_0 [5, -7] = true := by decide +kernel
theorem subd10_0_177 : subd10_0 [5, -6] = true := by decide +kernel
theorem subd10_0_178 : subd10_0 [5, -5] = true := by decide +kernel
theorem subd10_0_179 : subd10_0 [5, -4] = true := by decide +kernel
theorem subd10_0_180 : subd10_0 [5, -3] = true := by decide +kernel
theorem subd10_0_181 : subd10_0 [5, -2] = true := by decide +kernel
theorem subd10_0_182 : subd10_0 [5, -1] = true := by decide +kernel
theorem subd10_0_183 : subd10_0 [5, 0] = true := by decide +kernel
theorem subd10_0_184 : subd10_0 [5, 1] = true := by decide +kernel
theorem subd10_0_185 : subd10_0 [5, 2] = true := by decide +kernel
theorem subd10_0_186 : subd10_0 [5, 3] = true := by decide +kernel
theorem subd10_0_187 : subd10_0 [6, -5] = true := by decide +kernel
theorem subd10_0_188 : subd10_0 [6, -4] = true := by decide +kernel
theorem subd10_0_189 : subd10_0 [6, -3] = true := by decide +kernel
theorem subd10_0_190 : subd10_0 [6, -2] = true := by decide +kernel
theorem subd10_0_191 : subd10_0 [6, -1] = true := by decide +kernel
theorem sbd10_0_5 : ∀ q ∈ blkd10_0_5, subd10_0 q = true := by
  unfold blkd10_0_5
  exact List.forall_mem_cons.2 ⟨subd10_0_160, List.forall_mem_cons.2 ⟨subd10_0_161, List.forall_mem_cons.2 ⟨subd10_0_162, List.forall_mem_cons.2 ⟨subd10_0_163, List.forall_mem_cons.2 ⟨subd10_0_164, List.forall_mem_cons.2 ⟨subd10_0_165, List.forall_mem_cons.2 ⟨subd10_0_166, List.forall_mem_cons.2 ⟨subd10_0_167, List.forall_mem_cons.2 ⟨subd10_0_168, List.forall_mem_cons.2 ⟨subd10_0_169, List.forall_mem_cons.2 ⟨subd10_0_170, List.forall_mem_cons.2 ⟨subd10_0_171, List.forall_mem_cons.2 ⟨subd10_0_172, List.forall_mem_cons.2 ⟨subd10_0_173, List.forall_mem_cons.2 ⟨subd10_0_174, List.forall_mem_cons.2 ⟨subd10_0_175, List.forall_mem_cons.2 ⟨subd10_0_176, List.forall_mem_cons.2 ⟨subd10_0_177, List.forall_mem_cons.2 ⟨subd10_0_178, List.forall_mem_cons.2 ⟨subd10_0_179, List.forall_mem_cons.2 ⟨subd10_0_180, List.forall_mem_cons.2 ⟨subd10_0_181, List.forall_mem_cons.2 ⟨subd10_0_182, List.forall_mem_cons.2 ⟨subd10_0_183, List.forall_mem_cons.2 ⟨subd10_0_184, List.forall_mem_cons.2 ⟨subd10_0_185, List.forall_mem_cons.2 ⟨subd10_0_186, List.forall_mem_cons.2 ⟨subd10_0_187, List.forall_mem_cons.2 ⟨subd10_0_188, List.forall_mem_cons.2 ⟨subd10_0_189, List.forall_mem_cons.2 ⟨subd10_0_190, List.forall_mem_cons.2 ⟨subd10_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_192 : subd10_0 [6, 0] = true := by decide +kernel
theorem subd10_0_193 : subd10_0 [6, 1] = true := by decide +kernel
theorem sbd10_0_6 : ∀ q ∈ blkd10_0_6, subd10_0 q = true := by
  unfold blkd10_0_6
  exact List.forall_mem_cons.2 ⟨subd10_0_192, List.forall_mem_cons.2 ⟨subd10_0_193, List.forall_mem_nil _⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-2, -1] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-2, 0, -9] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-2, 0, -8] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-2, 0, -7] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-2, 0, -6] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-2, 0, -5] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-2, 0, -4] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-2, 0, -3] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-2, 0, -2] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-2, 0, -1] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-2, 0, 0] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-2, 0, 1] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-2, 0, 2] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-2, 0, 3] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-2, 0, 4] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-2, 0, 5] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [-2, 0, 6] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [-2, 0, 7] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [-2, 0, 8] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [-2, 0, 9] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [-2, 0, 10] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [-2, 1, -10] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [-2, 1, -9] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [-2, 1, -8] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [-2, 1, -7] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [-2, 1, -6] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [-2, 1, -5] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [-2, 1, -4] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [-2, 1, -3] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [-2, 1, -2] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [-2, 1, -1] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [-2, 1, 0] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_32 : subd10_1 [-2, 1, 1] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [-2, 1, 2] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [-2, 1, 3] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [-2, 1, 4] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [-2, 1, 5] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [-2, 1, 6] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [-2, 1, 7] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [-2, 1, 8] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [-2, 1, 9] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [-2, 1, 10] = true := by decide +kernel
theorem subd10_1_42 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_43 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_44 : subd10_1 [-1, -1, -14] = true := by decide +kernel
theorem subd10_1_45 : subd10_1 [-1, -1, -13] = true := by decide +kernel
theorem subd10_1_46 : subd10_1 [-1, -1, -12] = true := by decide +kernel
theorem subd10_1_47 : subd10_1 [-1, -1, -11] = true := by decide +kernel
theorem subd10_1_48 : subd10_1 [-1, -1, -10] = true := by decide +kernel
theorem subd10_1_49 : subd10_1 [-1, -1, -9] = true := by decide +kernel
theorem subd10_1_50 : subd10_1 [-1, -1, -8] = true := by decide +kernel
theorem subd10_1_51 : subd10_1 [-1, -1, -7] = true := by decide +kernel
theorem subd10_1_52 : subd10_1 [-1, -1, -6] = true := by decide +kernel
theorem subd10_1_53 : subd10_1 [-1, -1, -5] = true := by decide +kernel
theorem subd10_1_54 : subd10_1 [-1, -1, -4] = true := by decide +kernel
theorem subd10_1_55 : subd10_1 [-1, -1, -3] = true := by decide +kernel
theorem subd10_1_56 : subd10_1 [-1, -1, -2] = true := by decide +kernel
theorem subd10_1_57 : subd10_1 [-1, -1, -1] = true := by decide +kernel
theorem subd10_1_58 : subd10_1 [-1, -1, 0] = true := by decide +kernel
theorem subd10_1_59 : subd10_1 [-1, -1, 1] = true := by decide +kernel
theorem subd10_1_60 : subd10_1 [-1, -1, 2] = true := by decide +kernel
theorem subd10_1_61 : subd10_1 [-1, -1, 3] = true := by decide +kernel
theorem subd10_1_62 : subd10_1 [-1, -1, 4] = true := by decide +kernel
theorem subd10_1_63 : subd10_1 [-1, -1, 5] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_cons.2 ⟨subd10_1_42, List.forall_mem_cons.2 ⟨subd10_1_43, List.forall_mem_cons.2 ⟨subd10_1_44, List.forall_mem_cons.2 ⟨subd10_1_45, List.forall_mem_cons.2 ⟨subd10_1_46, List.forall_mem_cons.2 ⟨subd10_1_47, List.forall_mem_cons.2 ⟨subd10_1_48, List.forall_mem_cons.2 ⟨subd10_1_49, List.forall_mem_cons.2 ⟨subd10_1_50, List.forall_mem_cons.2 ⟨subd10_1_51, List.forall_mem_cons.2 ⟨subd10_1_52, List.forall_mem_cons.2 ⟨subd10_1_53, List.forall_mem_cons.2 ⟨subd10_1_54, List.forall_mem_cons.2 ⟨subd10_1_55, List.forall_mem_cons.2 ⟨subd10_1_56, List.forall_mem_cons.2 ⟨subd10_1_57, List.forall_mem_cons.2 ⟨subd10_1_58, List.forall_mem_cons.2 ⟨subd10_1_59, List.forall_mem_cons.2 ⟨subd10_1_60, List.forall_mem_cons.2 ⟨subd10_1_61, List.forall_mem_cons.2 ⟨subd10_1_62, List.forall_mem_cons.2 ⟨subd10_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_64 : subd10_1 [-1, -1, 6] = true := by decide +kernel
theorem subd10_1_65 : subd10_1 [-1, -1, 7] = true := by decide +kernel
theorem subd10_1_66 : subd10_1 [-1, -1, 8] = true := by decide +kernel
theorem subd10_1_67 : subd10_1 [-1, -1, 9] = true := by decide +kernel
theorem subd10_1_68 : subd10_1 [-1, -1, 10] = true := by decide +kernel
theorem subd10_1_69 : subd10_1 [-1, -1, 11] = true := by decide +kernel
theorem subd10_1_70 : subd10_1 [-1, -1, 12] = true := by decide +kernel
theorem subd10_1_71 : subd10_1 [-1, -1, 13] = true := by decide +kernel
theorem subd10_1_72 : subd10_1 [-1, -1, 14] = true := by decide +kernel
theorem subd10_1_73 : subd10_1 [-1, -1, 15] = true := by decide +kernel
theorem subd10_1_74 : subd10_1 [-1, 0, -17] = true := by decide +kernel
theorem subd10_1_75 : subd10_1 [-1, 0, -16] = true := by decide +kernel
theorem subd10_1_76 : subd10_1 [-1, 0, -15] = true := by decide +kernel
theorem subd10_1_77 : subd10_1 [-1, 0, -14] = true := by decide +kernel
theorem subd10_1_78 : subd10_1 [-1, 0, -13] = true := by decide +kernel
theorem subd10_1_79 : subd10_1 [-1, 0, -12] = true := by decide +kernel
theorem subd10_1_80 : subd10_1 [-1, 0, -11] = true := by decide +kernel
theorem subd10_1_81 : subd10_1 [-1, 0, -10] = true := by decide +kernel
theorem subd10_1_82 : subd10_1 [-1, 0, -9] = true := by decide +kernel
theorem subd10_1_83 : subd10_1 [-1, 0, -8] = true := by decide +kernel
theorem subd10_1_84 : subd10_1 [-1, 0, -7] = true := by decide +kernel
theorem subd10_1_85 : subd10_1 [-1, 0, -6] = true := by decide +kernel
theorem subd10_1_86 : subd10_1 [-1, 0, -5] = true := by decide +kernel
theorem subd10_1_87 : subd10_1 [-1, 0, -4] = true := by decide +kernel
theorem subd10_1_88 : subd10_1 [-1, 0, -3] = true := by decide +kernel
theorem subd10_1_89 : subd10_1 [-1, 0, -2] = true := by decide +kernel
theorem subd10_1_90 : subd10_1 [-1, 0, -1] = true := by decide +kernel
theorem subd10_1_91 : subd10_1 [-1, 0, 0] = true := by decide +kernel
theorem subd10_1_92 : subd10_1 [-1, 0, 1] = true := by decide +kernel
theorem subd10_1_93 : subd10_1 [-1, 0, 2] = true := by decide +kernel
theorem subd10_1_94 : subd10_1 [-1, 0, 3] = true := by decide +kernel
theorem subd10_1_95 : subd10_1 [-1, 0, 4] = true := by decide +kernel
theorem sbd10_1_2 : ∀ q ∈ blkd10_1_2, subd10_1 q = true := by
  unfold blkd10_1_2
  exact List.forall_mem_cons.2 ⟨subd10_1_64, List.forall_mem_cons.2 ⟨subd10_1_65, List.forall_mem_cons.2 ⟨subd10_1_66, List.forall_mem_cons.2 ⟨subd10_1_67, List.forall_mem_cons.2 ⟨subd10_1_68, List.forall_mem_cons.2 ⟨subd10_1_69, List.forall_mem_cons.2 ⟨subd10_1_70, List.forall_mem_cons.2 ⟨subd10_1_71, List.forall_mem_cons.2 ⟨subd10_1_72, List.forall_mem_cons.2 ⟨subd10_1_73, List.forall_mem_cons.2 ⟨subd10_1_74, List.forall_mem_cons.2 ⟨subd10_1_75, List.forall_mem_cons.2 ⟨subd10_1_76, List.forall_mem_cons.2 ⟨subd10_1_77, List.forall_mem_cons.2 ⟨subd10_1_78, List.forall_mem_cons.2 ⟨subd10_1_79, List.forall_mem_cons.2 ⟨subd10_1_80, List.forall_mem_cons.2 ⟨subd10_1_81, List.forall_mem_cons.2 ⟨subd10_1_82, List.forall_mem_cons.2 ⟨subd10_1_83, List.forall_mem_cons.2 ⟨subd10_1_84, List.forall_mem_cons.2 ⟨subd10_1_85, List.forall_mem_cons.2 ⟨subd10_1_86, List.forall_mem_cons.2 ⟨subd10_1_87, List.forall_mem_cons.2 ⟨subd10_1_88, List.forall_mem_cons.2 ⟨subd10_1_89, List.forall_mem_cons.2 ⟨subd10_1_90, List.forall_mem_cons.2 ⟨subd10_1_91, List.forall_mem_cons.2 ⟨subd10_1_92, List.forall_mem_cons.2 ⟨subd10_1_93, List.forall_mem_cons.2 ⟨subd10_1_94, List.forall_mem_cons.2 ⟨subd10_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
