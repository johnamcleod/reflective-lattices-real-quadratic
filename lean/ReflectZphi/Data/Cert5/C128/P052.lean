import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_128 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_129 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_130 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_131 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_132 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_133 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_134 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_135 : subd8_1 [1, 4] = true := by decide +kernel
theorem subd8_1_136 : subd8_1 [1, 5] = true := by decide +kernel
theorem subd8_1_137 : subd8_1 [2, -7] = true := by decide +kernel
theorem subd8_1_138 : subd8_1 [2, -6] = true := by decide +kernel
theorem subd8_1_139 : subd8_1 [2, -5] = true := by decide +kernel
theorem subd8_1_140 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_141 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_142 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_143 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_144 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_145 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_146 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_147 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_148 : subd8_1 [2, 4] = true := by decide +kernel
theorem subd8_1_149 : subd8_1 [2, 5] = true := by decide +kernel
theorem subd8_1_150 : subd8_1 [3, -7] = true := by decide +kernel
theorem subd8_1_151 : subd8_1 [3, -6] = true := by decide +kernel
theorem subd8_1_152 : subd8_1 [3, -5] = true := by decide +kernel
theorem subd8_1_153 : subd8_1 [3, -4] = true := by decide +kernel
theorem subd8_1_154 : subd8_1 [3, -3] = true := by decide +kernel
theorem subd8_1_155 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_156 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_157 : subd8_1 [3, 0] = true := by decide +kernel
theorem subd8_1_158 : subd8_1 [3, 1] = true := by decide +kernel
theorem subd8_1_159 : subd8_1 [3, 2] = true := by decide +kernel
theorem sbd8_1_4 : ∀ q ∈ blkd8_1_4, subd8_1 q = true := by
  unfold blkd8_1_4
  exact List.forall_mem_cons.2 ⟨subd8_1_128, List.forall_mem_cons.2 ⟨subd8_1_129, List.forall_mem_cons.2 ⟨subd8_1_130, List.forall_mem_cons.2 ⟨subd8_1_131, List.forall_mem_cons.2 ⟨subd8_1_132, List.forall_mem_cons.2 ⟨subd8_1_133, List.forall_mem_cons.2 ⟨subd8_1_134, List.forall_mem_cons.2 ⟨subd8_1_135, List.forall_mem_cons.2 ⟨subd8_1_136, List.forall_mem_cons.2 ⟨subd8_1_137, List.forall_mem_cons.2 ⟨subd8_1_138, List.forall_mem_cons.2 ⟨subd8_1_139, List.forall_mem_cons.2 ⟨subd8_1_140, List.forall_mem_cons.2 ⟨subd8_1_141, List.forall_mem_cons.2 ⟨subd8_1_142, List.forall_mem_cons.2 ⟨subd8_1_143, List.forall_mem_cons.2 ⟨subd8_1_144, List.forall_mem_cons.2 ⟨subd8_1_145, List.forall_mem_cons.2 ⟨subd8_1_146, List.forall_mem_cons.2 ⟨subd8_1_147, List.forall_mem_cons.2 ⟨subd8_1_148, List.forall_mem_cons.2 ⟨subd8_1_149, List.forall_mem_cons.2 ⟨subd8_1_150, List.forall_mem_cons.2 ⟨subd8_1_151, List.forall_mem_cons.2 ⟨subd8_1_152, List.forall_mem_cons.2 ⟨subd8_1_153, List.forall_mem_cons.2 ⟨subd8_1_154, List.forall_mem_cons.2 ⟨subd8_1_155, List.forall_mem_cons.2 ⟨subd8_1_156, List.forall_mem_cons.2 ⟨subd8_1_157, List.forall_mem_cons.2 ⟨subd8_1_158, List.forall_mem_cons.2 ⟨subd8_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_160 : subd8_1 [3, 3] = true := by decide +kernel
theorem subd8_1_161 : subd8_1 [3, 4] = true := by decide +kernel
theorem subd8_1_162 : subd8_1 [4, -7] = true := by decide +kernel
theorem subd8_1_163 : subd8_1 [4, -6] = true := by decide +kernel
theorem subd8_1_164 : subd8_1 [4, -5] = true := by decide +kernel
theorem subd8_1_165 : subd8_1 [4, -4] = true := by decide +kernel
theorem subd8_1_166 : subd8_1 [4, -3] = true := by decide +kernel
theorem subd8_1_167 : subd8_1 [4, -2] = true := by decide +kernel
theorem subd8_1_168 : subd8_1 [4, -1] = true := by decide +kernel
theorem subd8_1_169 : subd8_1 [4, 0] = true := by decide +kernel
theorem subd8_1_170 : subd8_1 [4, 1] = true := by decide +kernel
theorem subd8_1_171 : subd8_1 [4, 2] = true := by decide +kernel
theorem subd8_1_172 : subd8_1 [4, 3] = true := by decide +kernel
theorem subd8_1_173 : subd8_1 [4, 4] = true := by decide +kernel
theorem subd8_1_174 : subd8_1 [5, -6] = true := by decide +kernel
theorem subd8_1_175 : subd8_1 [5, -5] = true := by decide +kernel
theorem subd8_1_176 : subd8_1 [5, -4] = true := by decide +kernel
theorem subd8_1_177 : subd8_1 [5, -3] = true := by decide +kernel
theorem subd8_1_178 : subd8_1 [5, -2] = true := by decide +kernel
theorem subd8_1_179 : subd8_1 [5, -1] = true := by decide +kernel
theorem subd8_1_180 : subd8_1 [5, 0] = true := by decide +kernel
theorem subd8_1_181 : subd8_1 [5, 1] = true := by decide +kernel
theorem subd8_1_182 : subd8_1 [5, 2] = true := by decide +kernel
theorem subd8_1_183 : subd8_1 [5, 3] = true := by decide +kernel
theorem subd8_1_184 : subd8_1 [6, -5] = true := by decide +kernel
theorem subd8_1_185 : subd8_1 [6, -4] = true := by decide +kernel
theorem subd8_1_186 : subd8_1 [6, -3] = true := by decide +kernel
theorem subd8_1_187 : subd8_1 [6, -2] = true := by decide +kernel
theorem subd8_1_188 : subd8_1 [6, -1] = true := by decide +kernel
theorem subd8_1_189 : subd8_1 [6, 0] = true := by decide +kernel
theorem subd8_1_190 : subd8_1 [6, 1] = true := by decide +kernel
theorem sbd8_1_5 : ∀ q ∈ blkd8_1_5, subd8_1 q = true := by
  unfold blkd8_1_5
  exact List.forall_mem_cons.2 ⟨subd8_1_160, List.forall_mem_cons.2 ⟨subd8_1_161, List.forall_mem_cons.2 ⟨subd8_1_162, List.forall_mem_cons.2 ⟨subd8_1_163, List.forall_mem_cons.2 ⟨subd8_1_164, List.forall_mem_cons.2 ⟨subd8_1_165, List.forall_mem_cons.2 ⟨subd8_1_166, List.forall_mem_cons.2 ⟨subd8_1_167, List.forall_mem_cons.2 ⟨subd8_1_168, List.forall_mem_cons.2 ⟨subd8_1_169, List.forall_mem_cons.2 ⟨subd8_1_170, List.forall_mem_cons.2 ⟨subd8_1_171, List.forall_mem_cons.2 ⟨subd8_1_172, List.forall_mem_cons.2 ⟨subd8_1_173, List.forall_mem_cons.2 ⟨subd8_1_174, List.forall_mem_cons.2 ⟨subd8_1_175, List.forall_mem_cons.2 ⟨subd8_1_176, List.forall_mem_cons.2 ⟨subd8_1_177, List.forall_mem_cons.2 ⟨subd8_1_178, List.forall_mem_cons.2 ⟨subd8_1_179, List.forall_mem_cons.2 ⟨subd8_1_180, List.forall_mem_cons.2 ⟨subd8_1_181, List.forall_mem_cons.2 ⟨subd8_1_182, List.forall_mem_cons.2 ⟨subd8_1_183, List.forall_mem_cons.2 ⟨subd8_1_184, List.forall_mem_cons.2 ⟨subd8_1_185, List.forall_mem_cons.2 ⟨subd8_1_186, List.forall_mem_cons.2 ⟨subd8_1_187, List.forall_mem_cons.2 ⟨subd8_1_188, List.forall_mem_cons.2 ⟨subd8_1_189, List.forall_mem_cons.2 ⟨subd8_1_190, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-4] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-3, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-3, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-3, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-3, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-3, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-3, 2] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-3, 3] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-3, 4] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-2, -4] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-2, -3] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-2, -1, -6] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-2, -1, -5] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-2, -1, -4] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-2, -1, -3] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-2, -1, -2] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-2, -1, -1] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-2, -1, 0] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-2, -1, 1] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-2, -1, 2] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-2, -1, 3] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-2, -1, 4] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-2, -1, 5] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-2, -1, 6] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-2, 0, -7] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-2, 0, -6] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-2, 0, -5] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-2, 0, -4] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-2, 0, -3] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-2, 0, -2] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-2, 0, -1] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-2, 0, 0] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-2, 0, 1] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-2, 0, 2] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-2, 0, 3] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-2, 0, 4] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-2, 0, 5] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-2, 0, 6] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-2, 0, 7] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-2, 1, -7] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-2, 1, -6] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-2, 1, -5] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-2, 1, -4] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-2, 1, -3] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-2, 1, -2] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-2, 1, -1] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-2, 1, 0] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-2, 1, 1] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-2, 1, 2] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-2, 1, 3] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-2, 1, 4] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-2, 1, 5] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-2, 1, 6] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-2, 1, 7] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-2, 2, -7] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [-2, 2, -6] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [-2, 2, -5] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [-2, 2, -4] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [-2, 2, -3] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [-2, 2, -2] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [-2, 2, -1] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [-2, 2, 0] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [-2, 2, 1] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
