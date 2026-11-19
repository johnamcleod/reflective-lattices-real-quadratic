import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_0_160 : subd15_0 [1, 1, 0] = true := by decide +kernel
theorem subd15_0_161 : subd15_0 [1, 1, 1] = true := by decide +kernel
theorem subd15_0_162 : subd15_0 [1, 1, 2] = true := by decide +kernel
theorem subd15_0_163 : subd15_0 [1, 1, 3] = true := by decide +kernel
theorem subd15_0_164 : subd15_0 [1, 1, 4] = true := by decide +kernel
theorem subd15_0_165 : subd15_0 [1, 1, 5] = true := by decide +kernel
theorem subd15_0_166 : subd15_0 [1, 1, 6] = true := by decide +kernel
theorem subd15_0_167 : subd15_0 [1, 2] = true := by decide +kernel
theorem subd15_0_168 : subd15_0 [1, 3] = true := by decide +kernel
theorem subd15_0_169 : subd15_0 [1, 4] = true := by decide +kernel
theorem subd15_0_170 : subd15_0 [1, 5] = true := by decide +kernel
theorem subd15_0_171 : subd15_0 [2, -6] = true := by decide +kernel
theorem subd15_0_172 : subd15_0 [2, -5] = true := by decide +kernel
theorem subd15_0_173 : subd15_0 [2, -4] = true := by decide +kernel
theorem subd15_0_174 : subd15_0 [2, -3] = true := by decide +kernel
theorem subd15_0_175 : subd15_0 [2, -2] = true := by decide +kernel
theorem subd15_0_176 : subd15_0 [2, -1] = true := by decide +kernel
theorem subd15_0_177 : subd15_0 [2, 0] = true := by decide +kernel
theorem subd15_0_178 : subd15_0 [2, 1] = true := by decide +kernel
theorem subd15_0_179 : subd15_0 [2, 2] = true := by decide +kernel
theorem subd15_0_180 : subd15_0 [2, 3] = true := by decide +kernel
theorem subd15_0_181 : subd15_0 [2, 4] = true := by decide +kernel
theorem subd15_0_182 : subd15_0 [2, 5] = true := by decide +kernel
theorem subd15_0_183 : subd15_0 [3, -5] = true := by decide +kernel
theorem subd15_0_184 : subd15_0 [3, -4] = true := by decide +kernel
theorem subd15_0_185 : subd15_0 [3, -3] = true := by decide +kernel
theorem subd15_0_186 : subd15_0 [3, -2] = true := by decide +kernel
theorem subd15_0_187 : subd15_0 [3, -1] = true := by decide +kernel
theorem subd15_0_188 : subd15_0 [3, 0] = true := by decide +kernel
theorem subd15_0_189 : subd15_0 [3, 1] = true := by decide +kernel
theorem subd15_0_190 : subd15_0 [3, 2] = true := by decide +kernel
theorem subd15_0_191 : subd15_0 [3, 3] = true := by decide +kernel
theorem sbd15_0_5 : ∀ q ∈ blkd15_0_5, subd15_0 q = true := by
  unfold blkd15_0_5
  exact List.forall_mem_cons.2 ⟨subd15_0_160, List.forall_mem_cons.2 ⟨subd15_0_161, List.forall_mem_cons.2 ⟨subd15_0_162, List.forall_mem_cons.2 ⟨subd15_0_163, List.forall_mem_cons.2 ⟨subd15_0_164, List.forall_mem_cons.2 ⟨subd15_0_165, List.forall_mem_cons.2 ⟨subd15_0_166, List.forall_mem_cons.2 ⟨subd15_0_167, List.forall_mem_cons.2 ⟨subd15_0_168, List.forall_mem_cons.2 ⟨subd15_0_169, List.forall_mem_cons.2 ⟨subd15_0_170, List.forall_mem_cons.2 ⟨subd15_0_171, List.forall_mem_cons.2 ⟨subd15_0_172, List.forall_mem_cons.2 ⟨subd15_0_173, List.forall_mem_cons.2 ⟨subd15_0_174, List.forall_mem_cons.2 ⟨subd15_0_175, List.forall_mem_cons.2 ⟨subd15_0_176, List.forall_mem_cons.2 ⟨subd15_0_177, List.forall_mem_cons.2 ⟨subd15_0_178, List.forall_mem_cons.2 ⟨subd15_0_179, List.forall_mem_cons.2 ⟨subd15_0_180, List.forall_mem_cons.2 ⟨subd15_0_181, List.forall_mem_cons.2 ⟨subd15_0_182, List.forall_mem_cons.2 ⟨subd15_0_183, List.forall_mem_cons.2 ⟨subd15_0_184, List.forall_mem_cons.2 ⟨subd15_0_185, List.forall_mem_cons.2 ⟨subd15_0_186, List.forall_mem_cons.2 ⟨subd15_0_187, List.forall_mem_cons.2 ⟨subd15_0_188, List.forall_mem_cons.2 ⟨subd15_0_189, List.forall_mem_cons.2 ⟨subd15_0_190, List.forall_mem_cons.2 ⟨subd15_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_192 : subd15_0 [3, 4] = true := by decide +kernel
theorem subd15_0_193 : subd15_0 [3, 5] = true := by decide +kernel
theorem subd15_0_194 : subd15_0 [4, -5] = true := by decide +kernel
theorem subd15_0_195 : subd15_0 [4, -4] = true := by decide +kernel
theorem subd15_0_196 : subd15_0 [4, -3] = true := by decide +kernel
theorem subd15_0_197 : subd15_0 [4, -2] = true := by decide +kernel
theorem subd15_0_198 : subd15_0 [4, -1] = true := by decide +kernel
theorem subd15_0_199 : subd15_0 [4, 0] = true := by decide +kernel
theorem subd15_0_200 : subd15_0 [4, 1] = true := by decide +kernel
theorem subd15_0_201 : subd15_0 [4, 2] = true := by decide +kernel
theorem subd15_0_202 : subd15_0 [4, 3] = true := by decide +kernel
theorem subd15_0_203 : subd15_0 [4, 4] = true := by decide +kernel
theorem subd15_0_204 : subd15_0 [4, 5] = true := by decide +kernel
theorem subd15_0_205 : subd15_0 [5, -4] = true := by decide +kernel
theorem subd15_0_206 : subd15_0 [5, -3] = true := by decide +kernel
theorem subd15_0_207 : subd15_0 [5, -2] = true := by decide +kernel
theorem subd15_0_208 : subd15_0 [5, -1] = true := by decide +kernel
theorem subd15_0_209 : subd15_0 [5, 0] = true := by decide +kernel
theorem subd15_0_210 : subd15_0 [5, 1] = true := by decide +kernel
theorem subd15_0_211 : subd15_0 [5, 2] = true := by decide +kernel
theorem subd15_0_212 : subd15_0 [5, 3] = true := by decide +kernel
theorem subd15_0_213 : subd15_0 [5, 4] = true := by decide +kernel
theorem subd15_0_214 : subd15_0 [6] = true := by decide +kernel
theorem sbd15_0_6 : ∀ q ∈ blkd15_0_6, subd15_0 q = true := by
  unfold blkd15_0_6
  exact List.forall_mem_cons.2 ⟨subd15_0_192, List.forall_mem_cons.2 ⟨subd15_0_193, List.forall_mem_cons.2 ⟨subd15_0_194, List.forall_mem_cons.2 ⟨subd15_0_195, List.forall_mem_cons.2 ⟨subd15_0_196, List.forall_mem_cons.2 ⟨subd15_0_197, List.forall_mem_cons.2 ⟨subd15_0_198, List.forall_mem_cons.2 ⟨subd15_0_199, List.forall_mem_cons.2 ⟨subd15_0_200, List.forall_mem_cons.2 ⟨subd15_0_201, List.forall_mem_cons.2 ⟨subd15_0_202, List.forall_mem_cons.2 ⟨subd15_0_203, List.forall_mem_cons.2 ⟨subd15_0_204, List.forall_mem_cons.2 ⟨subd15_0_205, List.forall_mem_cons.2 ⟨subd15_0_206, List.forall_mem_cons.2 ⟨subd15_0_207, List.forall_mem_cons.2 ⟨subd15_0_208, List.forall_mem_cons.2 ⟨subd15_0_209, List.forall_mem_cons.2 ⟨subd15_0_210, List.forall_mem_cons.2 ⟨subd15_0_211, List.forall_mem_cons.2 ⟨subd15_0_212, List.forall_mem_cons.2 ⟨subd15_0_213, List.forall_mem_cons.2 ⟨subd15_0_214, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-5, -1] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-5, 0] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-5, 1] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-5, 2] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-5, 3] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-5, 4] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-4, -3] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [-4, -2] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [-4, -1] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [-4, 0] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [-4, 1] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [-4, 2] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [-4, 3] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [-4, 4] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [-4, 5] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [-3, -5] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [-3, -4] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [-3, -3] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [-3, -2] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [-3, -1, -5] = true := by decide +kernel
theorem subd15_1_20 : subd15_1 [-3, -1, -4] = true := by decide +kernel
theorem subd15_1_21 : subd15_1 [-3, -1, -3] = true := by decide +kernel
theorem subd15_1_22 : subd15_1 [-3, -1, -2] = true := by decide +kernel
theorem subd15_1_23 : subd15_1 [-3, -1, -1] = true := by decide +kernel
theorem subd15_1_24 : subd15_1 [-3, -1, 0] = true := by decide +kernel
theorem subd15_1_25 : subd15_1 [-3, -1, 1] = true := by decide +kernel
theorem subd15_1_26 : subd15_1 [-3, -1, 2] = true := by decide +kernel
theorem subd15_1_27 : subd15_1 [-3, -1, 3] = true := by decide +kernel
theorem subd15_1_28 : subd15_1 [-3, -1, 4] = true := by decide +kernel
theorem subd15_1_29 : subd15_1 [-3, -1, 5] = true := by decide +kernel
theorem subd15_1_30 : subd15_1 [-3, -1, 6] = true := by decide +kernel
theorem subd15_1_31 : subd15_1 [-3, -1, 7] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_cons.2 ⟨subd15_1_20, List.forall_mem_cons.2 ⟨subd15_1_21, List.forall_mem_cons.2 ⟨subd15_1_22, List.forall_mem_cons.2 ⟨subd15_1_23, List.forall_mem_cons.2 ⟨subd15_1_24, List.forall_mem_cons.2 ⟨subd15_1_25, List.forall_mem_cons.2 ⟨subd15_1_26, List.forall_mem_cons.2 ⟨subd15_1_27, List.forall_mem_cons.2 ⟨subd15_1_28, List.forall_mem_cons.2 ⟨subd15_1_29, List.forall_mem_cons.2 ⟨subd15_1_30, List.forall_mem_cons.2 ⟨subd15_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_32 : subd15_1 [-3, 0, -6] = true := by decide +kernel
theorem subd15_1_33 : subd15_1 [-3, 0, -5] = true := by decide +kernel
theorem subd15_1_34 : subd15_1 [-3, 0, -4] = true := by decide +kernel
theorem subd15_1_35 : subd15_1 [-3, 0, -3] = true := by decide +kernel
theorem subd15_1_36 : subd15_1 [-3, 0, -2] = true := by decide +kernel
theorem subd15_1_37 : subd15_1 [-3, 0, -1] = true := by decide +kernel
theorem subd15_1_38 : subd15_1 [-3, 0, 0] = true := by decide +kernel
theorem subd15_1_39 : subd15_1 [-3, 0, 1] = true := by decide +kernel
theorem subd15_1_40 : subd15_1 [-3, 0, 2] = true := by decide +kernel
theorem subd15_1_41 : subd15_1 [-3, 0, 3] = true := by decide +kernel
theorem subd15_1_42 : subd15_1 [-3, 0, 4] = true := by decide +kernel
theorem subd15_1_43 : subd15_1 [-3, 0, 5] = true := by decide +kernel
theorem subd15_1_44 : subd15_1 [-3, 0, 6] = true := by decide +kernel
theorem subd15_1_45 : subd15_1 [-3, 0, 7] = true := by decide +kernel
theorem subd15_1_46 : subd15_1 [-3, 0, 8] = true := by decide +kernel
theorem subd15_1_47 : subd15_1 [-3, 1, -6] = true := by decide +kernel
theorem subd15_1_48 : subd15_1 [-3, 1, -5] = true := by decide +kernel
theorem subd15_1_49 : subd15_1 [-3, 1, -4] = true := by decide +kernel
theorem subd15_1_50 : subd15_1 [-3, 1, -3] = true := by decide +kernel
theorem subd15_1_51 : subd15_1 [-3, 1, -2] = true := by decide +kernel
theorem subd15_1_52 : subd15_1 [-3, 1, -1] = true := by decide +kernel
theorem subd15_1_53 : subd15_1 [-3, 1, 0] = true := by decide +kernel
theorem subd15_1_54 : subd15_1 [-3, 1, 1] = true := by decide +kernel
theorem subd15_1_55 : subd15_1 [-3, 1, 2] = true := by decide +kernel
theorem subd15_1_56 : subd15_1 [-3, 1, 3] = true := by decide +kernel
theorem subd15_1_57 : subd15_1 [-3, 1, 4] = true := by decide +kernel
theorem subd15_1_58 : subd15_1 [-3, 1, 5] = true := by decide +kernel
theorem subd15_1_59 : subd15_1 [-3, 1, 6] = true := by decide +kernel
theorem subd15_1_60 : subd15_1 [-3, 1, 7] = true := by decide +kernel
theorem subd15_1_61 : subd15_1 [-3, 2, -7] = true := by decide +kernel
theorem subd15_1_62 : subd15_1 [-3, 2, -6] = true := by decide +kernel
theorem subd15_1_63 : subd15_1 [-3, 2, -5] = true := by decide +kernel
theorem sbd15_1_1 : ∀ q ∈ blkd15_1_1, subd15_1 q = true := by
  unfold blkd15_1_1
  exact List.forall_mem_cons.2 ⟨subd15_1_32, List.forall_mem_cons.2 ⟨subd15_1_33, List.forall_mem_cons.2 ⟨subd15_1_34, List.forall_mem_cons.2 ⟨subd15_1_35, List.forall_mem_cons.2 ⟨subd15_1_36, List.forall_mem_cons.2 ⟨subd15_1_37, List.forall_mem_cons.2 ⟨subd15_1_38, List.forall_mem_cons.2 ⟨subd15_1_39, List.forall_mem_cons.2 ⟨subd15_1_40, List.forall_mem_cons.2 ⟨subd15_1_41, List.forall_mem_cons.2 ⟨subd15_1_42, List.forall_mem_cons.2 ⟨subd15_1_43, List.forall_mem_cons.2 ⟨subd15_1_44, List.forall_mem_cons.2 ⟨subd15_1_45, List.forall_mem_cons.2 ⟨subd15_1_46, List.forall_mem_cons.2 ⟨subd15_1_47, List.forall_mem_cons.2 ⟨subd15_1_48, List.forall_mem_cons.2 ⟨subd15_1_49, List.forall_mem_cons.2 ⟨subd15_1_50, List.forall_mem_cons.2 ⟨subd15_1_51, List.forall_mem_cons.2 ⟨subd15_1_52, List.forall_mem_cons.2 ⟨subd15_1_53, List.forall_mem_cons.2 ⟨subd15_1_54, List.forall_mem_cons.2 ⟨subd15_1_55, List.forall_mem_cons.2 ⟨subd15_1_56, List.forall_mem_cons.2 ⟨subd15_1_57, List.forall_mem_cons.2 ⟨subd15_1_58, List.forall_mem_cons.2 ⟨subd15_1_59, List.forall_mem_cons.2 ⟨subd15_1_60, List.forall_mem_cons.2 ⟨subd15_1_61, List.forall_mem_cons.2 ⟨subd15_1_62, List.forall_mem_cons.2 ⟨subd15_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_64 : subd15_1 [-3, 2, -4] = true := by decide +kernel
theorem subd15_1_65 : subd15_1 [-3, 2, -3] = true := by decide +kernel
theorem subd15_1_66 : subd15_1 [-3, 2, -2] = true := by decide +kernel
theorem subd15_1_67 : subd15_1 [-3, 2, -1] = true := by decide +kernel
theorem subd15_1_68 : subd15_1 [-3, 2, 0] = true := by decide +kernel
theorem subd15_1_69 : subd15_1 [-3, 2, 1] = true := by decide +kernel
theorem subd15_1_70 : subd15_1 [-3, 2, 2] = true := by decide +kernel
theorem subd15_1_71 : subd15_1 [-3, 2, 3] = true := by decide +kernel
theorem subd15_1_72 : subd15_1 [-3, 2, 4] = true := by decide +kernel
theorem subd15_1_73 : subd15_1 [-3, 2, 5] = true := by decide +kernel
theorem subd15_1_74 : subd15_1 [-3, 2, 6] = true := by decide +kernel
theorem subd15_1_75 : subd15_1 [-3, 2, 7] = true := by decide +kernel
theorem subd15_1_76 : subd15_1 [-3, 3, -7] = true := by decide +kernel
theorem subd15_1_77 : subd15_1 [-3, 3, -6] = true := by decide +kernel
theorem subd15_1_78 : subd15_1 [-3, 3, -5] = true := by decide +kernel
theorem subd15_1_79 : subd15_1 [-3, 3, -4] = true := by decide +kernel
theorem subd15_1_80 : subd15_1 [-3, 3, -3] = true := by decide +kernel
theorem subd15_1_81 : subd15_1 [-3, 3, -2] = true := by decide +kernel
theorem subd15_1_82 : subd15_1 [-3, 3, -1] = true := by decide +kernel
theorem subd15_1_83 : subd15_1 [-3, 3, 0] = true := by decide +kernel
theorem subd15_1_84 : subd15_1 [-3, 3, 1] = true := by decide +kernel
theorem subd15_1_85 : subd15_1 [-3, 3, 2] = true := by decide +kernel
theorem subd15_1_86 : subd15_1 [-3, 3, 3] = true := by decide +kernel
theorem subd15_1_87 : subd15_1 [-3, 3, 4] = true := by decide +kernel
theorem subd15_1_88 : subd15_1 [-3, 3, 5] = true := by decide +kernel
theorem subd15_1_89 : subd15_1 [-3, 3, 6] = true := by decide +kernel
theorem subd15_1_90 : subd15_1 [-3, 4] = true := by decide +kernel
theorem subd15_1_91 : subd15_1 [-3, 5] = true := by decide +kernel
theorem subd15_1_92 : subd15_1 [-3, 6] = true := by decide +kernel
theorem subd15_1_93 : subd15_1 [-2, -5] = true := by decide +kernel
theorem subd15_1_94 : subd15_1 [-2, -4] = true := by decide +kernel
theorem subd15_1_95 : subd15_1 [-2, -3] = true := by decide +kernel
theorem sbd15_1_2 : ∀ q ∈ blkd15_1_2, subd15_1 q = true := by
  unfold blkd15_1_2
  exact List.forall_mem_cons.2 ⟨subd15_1_64, List.forall_mem_cons.2 ⟨subd15_1_65, List.forall_mem_cons.2 ⟨subd15_1_66, List.forall_mem_cons.2 ⟨subd15_1_67, List.forall_mem_cons.2 ⟨subd15_1_68, List.forall_mem_cons.2 ⟨subd15_1_69, List.forall_mem_cons.2 ⟨subd15_1_70, List.forall_mem_cons.2 ⟨subd15_1_71, List.forall_mem_cons.2 ⟨subd15_1_72, List.forall_mem_cons.2 ⟨subd15_1_73, List.forall_mem_cons.2 ⟨subd15_1_74, List.forall_mem_cons.2 ⟨subd15_1_75, List.forall_mem_cons.2 ⟨subd15_1_76, List.forall_mem_cons.2 ⟨subd15_1_77, List.forall_mem_cons.2 ⟨subd15_1_78, List.forall_mem_cons.2 ⟨subd15_1_79, List.forall_mem_cons.2 ⟨subd15_1_80, List.forall_mem_cons.2 ⟨subd15_1_81, List.forall_mem_cons.2 ⟨subd15_1_82, List.forall_mem_cons.2 ⟨subd15_1_83, List.forall_mem_cons.2 ⟨subd15_1_84, List.forall_mem_cons.2 ⟨subd15_1_85, List.forall_mem_cons.2 ⟨subd15_1_86, List.forall_mem_cons.2 ⟨subd15_1_87, List.forall_mem_cons.2 ⟨subd15_1_88, List.forall_mem_cons.2 ⟨subd15_1_89, List.forall_mem_cons.2 ⟨subd15_1_90, List.forall_mem_cons.2 ⟨subd15_1_91, List.forall_mem_cons.2 ⟨subd15_1_92, List.forall_mem_cons.2 ⟨subd15_1_93, List.forall_mem_cons.2 ⟨subd15_1_94, List.forall_mem_cons.2 ⟨subd15_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_96 : subd15_1 [-2, -2, -6] = true := by decide +kernel
theorem subd15_1_97 : subd15_1 [-2, -2, -5] = true := by decide +kernel
theorem subd15_1_98 : subd15_1 [-2, -2, -4] = true := by decide +kernel
theorem subd15_1_99 : subd15_1 [-2, -2, -3] = true := by decide +kernel
theorem subd15_1_100 : subd15_1 [-2, -2, -2] = true := by decide +kernel
theorem subd15_1_101 : subd15_1 [-2, -2, -1] = true := by decide +kernel
theorem subd15_1_102 : subd15_1 [-2, -2, 0] = true := by decide +kernel
theorem subd15_1_103 : subd15_1 [-2, -2, 1] = true := by decide +kernel
theorem subd15_1_104 : subd15_1 [-2, -2, 2] = true := by decide +kernel
theorem subd15_1_105 : subd15_1 [-2, -2, 3] = true := by decide +kernel
theorem subd15_1_106 : subd15_1 [-2, -2, 4] = true := by decide +kernel
theorem subd15_1_107 : subd15_1 [-2, -2, 5] = true := by decide +kernel
theorem subd15_1_108 : subd15_1 [-2, -2, 6] = true := by decide +kernel
theorem subd15_1_109 : subd15_1 [-2, -2, 7] = true := by decide +kernel
theorem subd15_1_110 : subd15_1 [-2, -2, 8] = true := by decide +kernel
theorem subd15_1_111 : subd15_1 [-2, -1, -6] = true := by decide +kernel
theorem subd15_1_112 : subd15_1 [-2, -1, -5] = true := by decide +kernel
theorem subd15_1_113 : subd15_1 [-2, -1, -4] = true := by decide +kernel
theorem subd15_1_114 : subd15_1 [-2, -1, -3] = true := by decide +kernel
theorem subd15_1_115 : subd15_1 [-2, -1, -2] = true := by decide +kernel
theorem subd15_1_116 : subd15_1 [-2, -1, -1] = true := by decide +kernel
theorem subd15_1_117 : subd15_1 [-2, -1, 0] = true := by decide +kernel
theorem subd15_1_118 : subd15_1 [-2, -1, 1] = true := by decide +kernel
theorem subd15_1_119 : subd15_1 [-2, -1, 2] = true := by decide +kernel
theorem subd15_1_120 : subd15_1 [-2, -1, 3] = true := by decide +kernel
theorem subd15_1_121 : subd15_1 [-2, -1, 4] = true := by decide +kernel
theorem subd15_1_122 : subd15_1 [-2, -1, 5] = true := by decide +kernel
theorem subd15_1_123 : subd15_1 [-2, -1, 6] = true := by decide +kernel
theorem subd15_1_124 : subd15_1 [-2, -1, 7] = true := by decide +kernel
theorem subd15_1_125 : subd15_1 [-2, -1, 8] = true := by decide +kernel
theorem subd15_1_126 : subd15_1 [-2, 0, -7] = true := by decide +kernel
theorem subd15_1_127 : subd15_1 [-2, 0, -6] = true := by decide +kernel
theorem sbd15_1_3 : ∀ q ∈ blkd15_1_3, subd15_1 q = true := by
  unfold blkd15_1_3
  exact List.forall_mem_cons.2 ⟨subd15_1_96, List.forall_mem_cons.2 ⟨subd15_1_97, List.forall_mem_cons.2 ⟨subd15_1_98, List.forall_mem_cons.2 ⟨subd15_1_99, List.forall_mem_cons.2 ⟨subd15_1_100, List.forall_mem_cons.2 ⟨subd15_1_101, List.forall_mem_cons.2 ⟨subd15_1_102, List.forall_mem_cons.2 ⟨subd15_1_103, List.forall_mem_cons.2 ⟨subd15_1_104, List.forall_mem_cons.2 ⟨subd15_1_105, List.forall_mem_cons.2 ⟨subd15_1_106, List.forall_mem_cons.2 ⟨subd15_1_107, List.forall_mem_cons.2 ⟨subd15_1_108, List.forall_mem_cons.2 ⟨subd15_1_109, List.forall_mem_cons.2 ⟨subd15_1_110, List.forall_mem_cons.2 ⟨subd15_1_111, List.forall_mem_cons.2 ⟨subd15_1_112, List.forall_mem_cons.2 ⟨subd15_1_113, List.forall_mem_cons.2 ⟨subd15_1_114, List.forall_mem_cons.2 ⟨subd15_1_115, List.forall_mem_cons.2 ⟨subd15_1_116, List.forall_mem_cons.2 ⟨subd15_1_117, List.forall_mem_cons.2 ⟨subd15_1_118, List.forall_mem_cons.2 ⟨subd15_1_119, List.forall_mem_cons.2 ⟨subd15_1_120, List.forall_mem_cons.2 ⟨subd15_1_121, List.forall_mem_cons.2 ⟨subd15_1_122, List.forall_mem_cons.2 ⟨subd15_1_123, List.forall_mem_cons.2 ⟨subd15_1_124, List.forall_mem_cons.2 ⟨subd15_1_125, List.forall_mem_cons.2 ⟨subd15_1_126, List.forall_mem_cons.2 ⟨subd15_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
