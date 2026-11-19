import ReflectZphi.Data.Cert5.C043.Base

namespace ReflectZphi.Data.Cert5.C043
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_160 : sub0 [1, 1, -7] = true := by decide +kernel
theorem sub0_161 : sub0 [1, 1, -6] = true := by decide +kernel
theorem sub0_162 : sub0 [1, 1, -5] = true := by decide +kernel
theorem sub0_163 : sub0 [1, 1, -4] = true := by decide +kernel
theorem sub0_164 : sub0 [1, 1, -3] = true := by decide +kernel
theorem sub0_165 : sub0 [1, 1, -2] = true := by decide +kernel
theorem sub0_166 : sub0 [1, 1, -1] = true := by decide +kernel
theorem sub0_167 : sub0 [1, 1, 0] = true := by decide +kernel
theorem sub0_168 : sub0 [1, 1, 1] = true := by decide +kernel
theorem sub0_169 : sub0 [1, 1, 2] = true := by decide +kernel
theorem sub0_170 : sub0 [1, 1, 3] = true := by decide +kernel
theorem sub0_171 : sub0 [1, 1, 4] = true := by decide +kernel
theorem sub0_172 : sub0 [1, 1, 5] = true := by decide +kernel
theorem sub0_173 : sub0 [1, 1, 6] = true := by decide +kernel
theorem sub0_174 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_175 : sub0 [1, 3] = true := by decide +kernel
theorem sub0_176 : sub0 [1, 4] = true := by decide +kernel
theorem sub0_177 : sub0 [1, 5] = true := by decide +kernel
theorem sub0_178 : sub0 [1, 6] = true := by decide +kernel
theorem sub0_179 : sub0 [2, -6] = true := by decide +kernel
theorem sub0_180 : sub0 [2, -5] = true := by decide +kernel
theorem sub0_181 : sub0 [2, -4] = true := by decide +kernel
theorem sub0_182 : sub0 [2, -3] = true := by decide +kernel
theorem sub0_183 : sub0 [2, -2] = true := by decide +kernel
theorem sub0_184 : sub0 [2, -1] = true := by decide +kernel
theorem sub0_185 : sub0 [2, 0] = true := by decide +kernel
theorem sub0_186 : sub0 [2, 1] = true := by decide +kernel
theorem sub0_187 : sub0 [2, 2] = true := by decide +kernel
theorem sub0_188 : sub0 [2, 3] = true := by decide +kernel
theorem sub0_189 : sub0 [2, 4] = true := by decide +kernel
theorem sub0_190 : sub0 [2, 5] = true := by decide +kernel
theorem sub0_191 : sub0 [2, 6] = true := by decide +kernel
theorem sb0_5 : ∀ q ∈ blk0_5, sub0 q = true := by
  unfold blk0_5
  exact List.forall_mem_cons.2 ⟨sub0_160, List.forall_mem_cons.2 ⟨sub0_161, List.forall_mem_cons.2 ⟨sub0_162, List.forall_mem_cons.2 ⟨sub0_163, List.forall_mem_cons.2 ⟨sub0_164, List.forall_mem_cons.2 ⟨sub0_165, List.forall_mem_cons.2 ⟨sub0_166, List.forall_mem_cons.2 ⟨sub0_167, List.forall_mem_cons.2 ⟨sub0_168, List.forall_mem_cons.2 ⟨sub0_169, List.forall_mem_cons.2 ⟨sub0_170, List.forall_mem_cons.2 ⟨sub0_171, List.forall_mem_cons.2 ⟨sub0_172, List.forall_mem_cons.2 ⟨sub0_173, List.forall_mem_cons.2 ⟨sub0_174, List.forall_mem_cons.2 ⟨sub0_175, List.forall_mem_cons.2 ⟨sub0_176, List.forall_mem_cons.2 ⟨sub0_177, List.forall_mem_cons.2 ⟨sub0_178, List.forall_mem_cons.2 ⟨sub0_179, List.forall_mem_cons.2 ⟨sub0_180, List.forall_mem_cons.2 ⟨sub0_181, List.forall_mem_cons.2 ⟨sub0_182, List.forall_mem_cons.2 ⟨sub0_183, List.forall_mem_cons.2 ⟨sub0_184, List.forall_mem_cons.2 ⟨sub0_185, List.forall_mem_cons.2 ⟨sub0_186, List.forall_mem_cons.2 ⟨sub0_187, List.forall_mem_cons.2 ⟨sub0_188, List.forall_mem_cons.2 ⟨sub0_189, List.forall_mem_cons.2 ⟨sub0_190, List.forall_mem_cons.2 ⟨sub0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_192 : sub0 [3, -5] = true := by decide +kernel
theorem sub0_193 : sub0 [3, -4] = true := by decide +kernel
theorem sub0_194 : sub0 [3, -3] = true := by decide +kernel
theorem sub0_195 : sub0 [3, -2] = true := by decide +kernel
theorem sub0_196 : sub0 [3, -1] = true := by decide +kernel
theorem sub0_197 : sub0 [3, 0] = true := by decide +kernel
theorem sub0_198 : sub0 [3, 1] = true := by decide +kernel
theorem sub0_199 : sub0 [3, 2] = true := by decide +kernel
theorem sub0_200 : sub0 [3, 3] = true := by decide +kernel
theorem sub0_201 : sub0 [3, 4] = true := by decide +kernel
theorem sub0_202 : sub0 [3, 5] = true := by decide +kernel
theorem sub0_203 : sub0 [3, 6] = true := by decide +kernel
theorem sub0_204 : sub0 [4, -4] = true := by decide +kernel
theorem sub0_205 : sub0 [4, -3] = true := by decide +kernel
theorem sub0_206 : sub0 [4, -2] = true := by decide +kernel
theorem sub0_207 : sub0 [4, -1] = true := by decide +kernel
theorem sub0_208 : sub0 [4, 0] = true := by decide +kernel
theorem sub0_209 : sub0 [4, 1] = true := by decide +kernel
theorem sub0_210 : sub0 [4, 2] = true := by decide +kernel
theorem sub0_211 : sub0 [4, 3] = true := by decide +kernel
theorem sub0_212 : sub0 [4, 4] = true := by decide +kernel
theorem sub0_213 : sub0 [4, 5] = true := by decide +kernel
theorem sub0_214 : sub0 [4, 6] = true := by decide +kernel
theorem sub0_215 : sub0 [5, -3] = true := by decide +kernel
theorem sub0_216 : sub0 [5, -2] = true := by decide +kernel
theorem sub0_217 : sub0 [5, -1] = true := by decide +kernel
theorem sub0_218 : sub0 [5, 0] = true := by decide +kernel
theorem sub0_219 : sub0 [5, 1] = true := by decide +kernel
theorem sub0_220 : sub0 [5, 2] = true := by decide +kernel
theorem sub0_221 : sub0 [5, 3] = true := by decide +kernel
theorem sub0_222 : sub0 [5, 4] = true := by decide +kernel
theorem sub0_223 : sub0 [5, 5] = true := by decide +kernel
theorem sb0_6 : ∀ q ∈ blk0_6, sub0 q = true := by
  unfold blk0_6
  exact List.forall_mem_cons.2 ⟨sub0_192, List.forall_mem_cons.2 ⟨sub0_193, List.forall_mem_cons.2 ⟨sub0_194, List.forall_mem_cons.2 ⟨sub0_195, List.forall_mem_cons.2 ⟨sub0_196, List.forall_mem_cons.2 ⟨sub0_197, List.forall_mem_cons.2 ⟨sub0_198, List.forall_mem_cons.2 ⟨sub0_199, List.forall_mem_cons.2 ⟨sub0_200, List.forall_mem_cons.2 ⟨sub0_201, List.forall_mem_cons.2 ⟨sub0_202, List.forall_mem_cons.2 ⟨sub0_203, List.forall_mem_cons.2 ⟨sub0_204, List.forall_mem_cons.2 ⟨sub0_205, List.forall_mem_cons.2 ⟨sub0_206, List.forall_mem_cons.2 ⟨sub0_207, List.forall_mem_cons.2 ⟨sub0_208, List.forall_mem_cons.2 ⟨sub0_209, List.forall_mem_cons.2 ⟨sub0_210, List.forall_mem_cons.2 ⟨sub0_211, List.forall_mem_cons.2 ⟨sub0_212, List.forall_mem_cons.2 ⟨sub0_213, List.forall_mem_cons.2 ⟨sub0_214, List.forall_mem_cons.2 ⟨sub0_215, List.forall_mem_cons.2 ⟨sub0_216, List.forall_mem_cons.2 ⟨sub0_217, List.forall_mem_cons.2 ⟨sub0_218, List.forall_mem_cons.2 ⟨sub0_219, List.forall_mem_cons.2 ⟨sub0_220, List.forall_mem_cons.2 ⟨sub0_221, List.forall_mem_cons.2 ⟨sub0_222, List.forall_mem_cons.2 ⟨sub0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_224 : sub0 [6] = true := by decide +kernel
theorem sb0_7 : ∀ q ∈ blk0_7, sub0 q = true := by
  unfold blk0_7
  exact List.forall_mem_cons.2 ⟨sub0_224, List.forall_mem_nil _⟩
theorem sub1_0 : sub1 [-7] = true := by decide +kernel
theorem sub1_1 : sub1 [-6, -3] = true := by decide +kernel
theorem sub1_2 : sub1 [-6, -2] = true := by decide +kernel
theorem sub1_3 : sub1 [-6, -1] = true := by decide +kernel
theorem sub1_4 : sub1 [-6, 0] = true := by decide +kernel
theorem sub1_5 : sub1 [-6, 1] = true := by decide +kernel
theorem sub1_6 : sub1 [-6, 2] = true := by decide +kernel
theorem sub1_7 : sub1 [-6, 3] = true := by decide +kernel
theorem sub1_8 : sub1 [-6, 4] = true := by decide +kernel
theorem sub1_9 : sub1 [-5, -5] = true := by decide +kernel
theorem sub1_10 : sub1 [-5, -4] = true := by decide +kernel
theorem sub1_11 : sub1 [-5, -3] = true := by decide +kernel
theorem sub1_12 : sub1 [-5, -2] = true := by decide +kernel
theorem sub1_13 : sub1 [-5, -1] = true := by decide +kernel
theorem sub1_14 : sub1 [-5, 0] = true := by decide +kernel
theorem sub1_15 : sub1 [-5, 1] = true := by decide +kernel
theorem sub1_16 : sub1 [-5, 2] = true := by decide +kernel
theorem sub1_17 : sub1 [-5, 3] = true := by decide +kernel
theorem sub1_18 : sub1 [-5, 4] = true := by decide +kernel
theorem sub1_19 : sub1 [-5, 5] = true := by decide +kernel
theorem sub1_20 : sub1 [-4, -6] = true := by decide +kernel
theorem sub1_21 : sub1 [-4, -5] = true := by decide +kernel
theorem sub1_22 : sub1 [-4, -4] = true := by decide +kernel
theorem sub1_23 : sub1 [-4, -3] = true := by decide +kernel
theorem sub1_24 : sub1 [-4, -2] = true := by decide +kernel
theorem sub1_25 : sub1 [-4, -1, -7] = true := by decide +kernel
theorem sub1_26 : sub1 [-4, -1, -6] = true := by decide +kernel
theorem sub1_27 : sub1 [-4, -1, -5] = true := by decide +kernel
theorem sub1_28 : sub1 [-4, -1, -4] = true := by decide +kernel
theorem sub1_29 : sub1 [-4, -1, -3] = true := by decide +kernel
theorem sub1_30 : sub1 [-4, -1, -2] = true := by decide +kernel
theorem sub1_31 : sub1 [-4, -1, -1] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_cons.2 ⟨sub1_18, List.forall_mem_cons.2 ⟨sub1_19, List.forall_mem_cons.2 ⟨sub1_20, List.forall_mem_cons.2 ⟨sub1_21, List.forall_mem_cons.2 ⟨sub1_22, List.forall_mem_cons.2 ⟨sub1_23, List.forall_mem_cons.2 ⟨sub1_24, List.forall_mem_cons.2 ⟨sub1_25, List.forall_mem_cons.2 ⟨sub1_26, List.forall_mem_cons.2 ⟨sub1_27, List.forall_mem_cons.2 ⟨sub1_28, List.forall_mem_cons.2 ⟨sub1_29, List.forall_mem_cons.2 ⟨sub1_30, List.forall_mem_cons.2 ⟨sub1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_32 : sub1 [-4, -1, 0] = true := by decide +kernel
theorem sub1_33 : sub1 [-4, -1, 1] = true := by decide +kernel
theorem sub1_34 : sub1 [-4, -1, 2] = true := by decide +kernel
theorem sub1_35 : sub1 [-4, -1, 3] = true := by decide +kernel
theorem sub1_36 : sub1 [-4, -1, 4] = true := by decide +kernel
theorem sub1_37 : sub1 [-4, -1, 5] = true := by decide +kernel
theorem sub1_38 : sub1 [-4, -1, 6] = true := by decide +kernel
theorem sub1_39 : sub1 [-4, 0, -7] = true := by decide +kernel
theorem sub1_40 : sub1 [-4, 0, -6] = true := by decide +kernel
theorem sub1_41 : sub1 [-4, 0, -5] = true := by decide +kernel
theorem sub1_42 : sub1 [-4, 0, -4] = true := by decide +kernel
theorem sub1_43 : sub1 [-4, 0, -3] = true := by decide +kernel
theorem sub1_44 : sub1 [-4, 0, -2] = true := by decide +kernel
theorem sub1_45 : sub1 [-4, 0, -1] = true := by decide +kernel
theorem sub1_46 : sub1 [-4, 0, 0] = true := by decide +kernel
theorem sub1_47 : sub1 [-4, 0, 1] = true := by decide +kernel
theorem sub1_48 : sub1 [-4, 0, 2] = true := by decide +kernel
theorem sub1_49 : sub1 [-4, 0, 3] = true := by decide +kernel
theorem sub1_50 : sub1 [-4, 0, 4] = true := by decide +kernel
theorem sub1_51 : sub1 [-4, 0, 5] = true := by decide +kernel
theorem sub1_52 : sub1 [-4, 0, 6] = true := by decide +kernel
theorem sub1_53 : sub1 [-4, 1, -8] = true := by decide +kernel
theorem sub1_54 : sub1 [-4, 1, -7] = true := by decide +kernel
theorem sub1_55 : sub1 [-4, 1, -6] = true := by decide +kernel
theorem sub1_56 : sub1 [-4, 1, -5] = true := by decide +kernel
theorem sub1_57 : sub1 [-4, 1, -4] = true := by decide +kernel
theorem sub1_58 : sub1 [-4, 1, -3] = true := by decide +kernel
theorem sub1_59 : sub1 [-4, 1, -2] = true := by decide +kernel
theorem sub1_60 : sub1 [-4, 1, -1] = true := by decide +kernel
theorem sub1_61 : sub1 [-4, 1, 0] = true := by decide +kernel
theorem sub1_62 : sub1 [-4, 1, 1] = true := by decide +kernel
theorem sub1_63 : sub1 [-4, 1, 2] = true := by decide +kernel
theorem sb1_1 : ∀ q ∈ blk1_1, sub1 q = true := by
  unfold blk1_1
  exact List.forall_mem_cons.2 ⟨sub1_32, List.forall_mem_cons.2 ⟨sub1_33, List.forall_mem_cons.2 ⟨sub1_34, List.forall_mem_cons.2 ⟨sub1_35, List.forall_mem_cons.2 ⟨sub1_36, List.forall_mem_cons.2 ⟨sub1_37, List.forall_mem_cons.2 ⟨sub1_38, List.forall_mem_cons.2 ⟨sub1_39, List.forall_mem_cons.2 ⟨sub1_40, List.forall_mem_cons.2 ⟨sub1_41, List.forall_mem_cons.2 ⟨sub1_42, List.forall_mem_cons.2 ⟨sub1_43, List.forall_mem_cons.2 ⟨sub1_44, List.forall_mem_cons.2 ⟨sub1_45, List.forall_mem_cons.2 ⟨sub1_46, List.forall_mem_cons.2 ⟨sub1_47, List.forall_mem_cons.2 ⟨sub1_48, List.forall_mem_cons.2 ⟨sub1_49, List.forall_mem_cons.2 ⟨sub1_50, List.forall_mem_cons.2 ⟨sub1_51, List.forall_mem_cons.2 ⟨sub1_52, List.forall_mem_cons.2 ⟨sub1_53, List.forall_mem_cons.2 ⟨sub1_54, List.forall_mem_cons.2 ⟨sub1_55, List.forall_mem_cons.2 ⟨sub1_56, List.forall_mem_cons.2 ⟨sub1_57, List.forall_mem_cons.2 ⟨sub1_58, List.forall_mem_cons.2 ⟨sub1_59, List.forall_mem_cons.2 ⟨sub1_60, List.forall_mem_cons.2 ⟨sub1_61, List.forall_mem_cons.2 ⟨sub1_62, List.forall_mem_cons.2 ⟨sub1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_64 : sub1 [-4, 1, 3] = true := by decide +kernel
theorem sub1_65 : sub1 [-4, 1, 4] = true := by decide +kernel
theorem sub1_66 : sub1 [-4, 1, 5] = true := by decide +kernel
theorem sub1_67 : sub1 [-4, 1, 6] = true := by decide +kernel
theorem sub1_68 : sub1 [-4, 2, -8] = true := by decide +kernel
theorem sub1_69 : sub1 [-4, 2, -7] = true := by decide +kernel
theorem sub1_70 : sub1 [-4, 2, -6] = true := by decide +kernel
theorem sub1_71 : sub1 [-4, 2, -5] = true := by decide +kernel
theorem sub1_72 : sub1 [-4, 2, -4] = true := by decide +kernel
theorem sub1_73 : sub1 [-4, 2, -3] = true := by decide +kernel
theorem sub1_74 : sub1 [-4, 2, -2] = true := by decide +kernel
theorem sub1_75 : sub1 [-4, 2, -1] = true := by decide +kernel
theorem sub1_76 : sub1 [-4, 2, 0] = true := by decide +kernel
theorem sub1_77 : sub1 [-4, 2, 1] = true := by decide +kernel
theorem sub1_78 : sub1 [-4, 2, 2] = true := by decide +kernel
theorem sub1_79 : sub1 [-4, 2, 3] = true := by decide +kernel
theorem sub1_80 : sub1 [-4, 2, 4] = true := by decide +kernel
theorem sub1_81 : sub1 [-4, 2, 5] = true := by decide +kernel
theorem sub1_82 : sub1 [-4, 3] = true := by decide +kernel
theorem sub1_83 : sub1 [-4, 4] = true := by decide +kernel
theorem sub1_84 : sub1 [-4, 5] = true := by decide +kernel
theorem sub1_85 : sub1 [-4, 6] = true := by decide +kernel
theorem sub1_86 : sub1 [-3, -6] = true := by decide +kernel
theorem sub1_87 : sub1 [-3, -5] = true := by decide +kernel
theorem sub1_88 : sub1 [-3, -4] = true := by decide +kernel
theorem sub1_89 : sub1 [-3, -3] = true := by decide +kernel
theorem sub1_90 : sub1 [-3, -2, -7] = true := by decide +kernel
theorem sub1_91 : sub1 [-3, -2, -6] = true := by decide +kernel
theorem sub1_92 : sub1 [-3, -2, -5] = true := by decide +kernel
theorem sub1_93 : sub1 [-3, -2, -4] = true := by decide +kernel
theorem sub1_94 : sub1 [-3, -2, -3] = true := by decide +kernel
theorem sub1_95 : sub1 [-3, -2, -2] = true := by decide +kernel
theorem sb1_2 : ∀ q ∈ blk1_2, sub1 q = true := by
  unfold blk1_2
  exact List.forall_mem_cons.2 ⟨sub1_64, List.forall_mem_cons.2 ⟨sub1_65, List.forall_mem_cons.2 ⟨sub1_66, List.forall_mem_cons.2 ⟨sub1_67, List.forall_mem_cons.2 ⟨sub1_68, List.forall_mem_cons.2 ⟨sub1_69, List.forall_mem_cons.2 ⟨sub1_70, List.forall_mem_cons.2 ⟨sub1_71, List.forall_mem_cons.2 ⟨sub1_72, List.forall_mem_cons.2 ⟨sub1_73, List.forall_mem_cons.2 ⟨sub1_74, List.forall_mem_cons.2 ⟨sub1_75, List.forall_mem_cons.2 ⟨sub1_76, List.forall_mem_cons.2 ⟨sub1_77, List.forall_mem_cons.2 ⟨sub1_78, List.forall_mem_cons.2 ⟨sub1_79, List.forall_mem_cons.2 ⟨sub1_80, List.forall_mem_cons.2 ⟨sub1_81, List.forall_mem_cons.2 ⟨sub1_82, List.forall_mem_cons.2 ⟨sub1_83, List.forall_mem_cons.2 ⟨sub1_84, List.forall_mem_cons.2 ⟨sub1_85, List.forall_mem_cons.2 ⟨sub1_86, List.forall_mem_cons.2 ⟨sub1_87, List.forall_mem_cons.2 ⟨sub1_88, List.forall_mem_cons.2 ⟨sub1_89, List.forall_mem_cons.2 ⟨sub1_90, List.forall_mem_cons.2 ⟨sub1_91, List.forall_mem_cons.2 ⟨sub1_92, List.forall_mem_cons.2 ⟨sub1_93, List.forall_mem_cons.2 ⟨sub1_94, List.forall_mem_cons.2 ⟨sub1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C043
