import ReflectZphi.Data.Cert5.C091.Base

namespace ReflectZphi.Data.Cert5.C091

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_7_160 : subd4_7 [1, -1, -10] = true := by decide +kernel
theorem subd4_7_161 : subd4_7 [1, -1, -9] = true := by decide +kernel
theorem subd4_7_162 : subd4_7 [1, -1, -8] = true := by decide +kernel
theorem subd4_7_163 : subd4_7 [1, -1, -7] = true := by decide +kernel
theorem subd4_7_164 : subd4_7 [1, -1, -6] = true := by decide +kernel
theorem subd4_7_165 : subd4_7 [1, -1, -5] = true := by decide +kernel
theorem subd4_7_166 : subd4_7 [1, -1, -4] = true := by decide +kernel
theorem subd4_7_167 : subd4_7 [1, -1, -3] = true := by decide +kernel
theorem subd4_7_168 : subd4_7 [1, -1, -2] = true := by decide +kernel
theorem subd4_7_169 : subd4_7 [1, -1, -1] = true := by decide +kernel
theorem subd4_7_170 : subd4_7 [1, -1, 0] = true := by decide +kernel
theorem subd4_7_171 : subd4_7 [1, -1, 1] = true := by decide +kernel
theorem subd4_7_172 : subd4_7 [1, -1, 2] = true := by decide +kernel
theorem subd4_7_173 : subd4_7 [1, -1, 3] = true := by decide +kernel
theorem subd4_7_174 : subd4_7 [1, -1, 4] = true := by decide +kernel
theorem subd4_7_175 : subd4_7 [1, -1, 5] = true := by decide +kernel
theorem subd4_7_176 : subd4_7 [1, -1, 6] = true := by decide +kernel
theorem subd4_7_177 : subd4_7 [1, -1, 7] = true := by decide +kernel
theorem subd4_7_178 : subd4_7 [1, -1, 8] = true := by decide +kernel
theorem subd4_7_179 : subd4_7 [1, -1, 9] = true := by decide +kernel
theorem subd4_7_180 : subd4_7 [1, -1, 10] = true := by decide +kernel
theorem subd4_7_181 : subd4_7 [1, -1, 11] = true := by decide +kernel
theorem subd4_7_182 : subd4_7 [1, -1, 12] = true := by decide +kernel
theorem subd4_7_183 : subd4_7 [1, 0, -14] = true := by decide +kernel
theorem subd4_7_184 : subd4_7 [1, 0, -13] = true := by decide +kernel
theorem subd4_7_185 : subd4_7 [1, 0, -12] = true := by decide +kernel
theorem subd4_7_186 : subd4_7 [1, 0, -11] = true := by decide +kernel
theorem subd4_7_187 : subd4_7 [1, 0, -10] = true := by decide +kernel
theorem subd4_7_188 : subd4_7 [1, 0, -9] = true := by decide +kernel
theorem subd4_7_189 : subd4_7 [1, 0, -8] = true := by decide +kernel
theorem subd4_7_190 : subd4_7 [1, 0, -7] = true := by decide +kernel
theorem subd4_7_191 : subd4_7 [1, 0, -6] = true := by decide +kernel
theorem sbd4_7_5 : ∀ q ∈ blkd4_7_5, subd4_7 q = true := by
  unfold blkd4_7_5
  exact List.forall_mem_cons.2 ⟨subd4_7_160, List.forall_mem_cons.2 ⟨subd4_7_161, List.forall_mem_cons.2 ⟨subd4_7_162, List.forall_mem_cons.2 ⟨subd4_7_163, List.forall_mem_cons.2 ⟨subd4_7_164, List.forall_mem_cons.2 ⟨subd4_7_165, List.forall_mem_cons.2 ⟨subd4_7_166, List.forall_mem_cons.2 ⟨subd4_7_167, List.forall_mem_cons.2 ⟨subd4_7_168, List.forall_mem_cons.2 ⟨subd4_7_169, List.forall_mem_cons.2 ⟨subd4_7_170, List.forall_mem_cons.2 ⟨subd4_7_171, List.forall_mem_cons.2 ⟨subd4_7_172, List.forall_mem_cons.2 ⟨subd4_7_173, List.forall_mem_cons.2 ⟨subd4_7_174, List.forall_mem_cons.2 ⟨subd4_7_175, List.forall_mem_cons.2 ⟨subd4_7_176, List.forall_mem_cons.2 ⟨subd4_7_177, List.forall_mem_cons.2 ⟨subd4_7_178, List.forall_mem_cons.2 ⟨subd4_7_179, List.forall_mem_cons.2 ⟨subd4_7_180, List.forall_mem_cons.2 ⟨subd4_7_181, List.forall_mem_cons.2 ⟨subd4_7_182, List.forall_mem_cons.2 ⟨subd4_7_183, List.forall_mem_cons.2 ⟨subd4_7_184, List.forall_mem_cons.2 ⟨subd4_7_185, List.forall_mem_cons.2 ⟨subd4_7_186, List.forall_mem_cons.2 ⟨subd4_7_187, List.forall_mem_cons.2 ⟨subd4_7_188, List.forall_mem_cons.2 ⟨subd4_7_189, List.forall_mem_cons.2 ⟨subd4_7_190, List.forall_mem_cons.2 ⟨subd4_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_192 : subd4_7 [1, 0, -5] = true := by decide +kernel
theorem subd4_7_193 : subd4_7 [1, 0, -4] = true := by decide +kernel
theorem subd4_7_194 : subd4_7 [1, 0, -3] = true := by decide +kernel
theorem subd4_7_195 : subd4_7 [1, 0, -2] = true := by decide +kernel
theorem subd4_7_196 : subd4_7 [1, 0, -1] = true := by decide +kernel
theorem subd4_7_197 : subd4_7 [1, 0, 0] = true := by decide +kernel
theorem subd4_7_198 : subd4_7 [1, 0, 1] = true := by decide +kernel
theorem subd4_7_199 : subd4_7 [1, 0, 2] = true := by decide +kernel
theorem subd4_7_200 : subd4_7 [1, 0, 3] = true := by decide +kernel
theorem subd4_7_201 : subd4_7 [1, 0, 4] = true := by decide +kernel
theorem subd4_7_202 : subd4_7 [1, 0, 5] = true := by decide +kernel
theorem subd4_7_203 : subd4_7 [1, 0, 6] = true := by decide +kernel
theorem subd4_7_204 : subd4_7 [1, 0, 7] = true := by decide +kernel
theorem subd4_7_205 : subd4_7 [1, 0, 8] = true := by decide +kernel
theorem subd4_7_206 : subd4_7 [1, 0, 9] = true := by decide +kernel
theorem subd4_7_207 : subd4_7 [1, 0, 10] = true := by decide +kernel
theorem subd4_7_208 : subd4_7 [1, 0, 11] = true := by decide +kernel
theorem subd4_7_209 : subd4_7 [1, 0, 12] = true := by decide +kernel
theorem subd4_7_210 : subd4_7 [1, 0, 13] = true := by decide +kernel
theorem sbd4_7_6 : ∀ q ∈ blkd4_7_6, subd4_7 q = true := by
  unfold blkd4_7_6
  exact List.forall_mem_cons.2 ⟨subd4_7_192, List.forall_mem_cons.2 ⟨subd4_7_193, List.forall_mem_cons.2 ⟨subd4_7_194, List.forall_mem_cons.2 ⟨subd4_7_195, List.forall_mem_cons.2 ⟨subd4_7_196, List.forall_mem_cons.2 ⟨subd4_7_197, List.forall_mem_cons.2 ⟨subd4_7_198, List.forall_mem_cons.2 ⟨subd4_7_199, List.forall_mem_cons.2 ⟨subd4_7_200, List.forall_mem_cons.2 ⟨subd4_7_201, List.forall_mem_cons.2 ⟨subd4_7_202, List.forall_mem_cons.2 ⟨subd4_7_203, List.forall_mem_cons.2 ⟨subd4_7_204, List.forall_mem_cons.2 ⟨subd4_7_205, List.forall_mem_cons.2 ⟨subd4_7_206, List.forall_mem_cons.2 ⟨subd4_7_207, List.forall_mem_cons.2 ⟨subd4_7_208, List.forall_mem_cons.2 ⟨subd4_7_209, List.forall_mem_cons.2 ⟨subd4_7_210, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_0 : subd5_0 [-1] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [0] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [1] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_nil _⟩⟩⟩
theorem subd5_1_0 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [1] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_nil _⟩⟩⟩
theorem subd5_2_0 : subd5_2 [-2] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-1] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [0] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [1] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [2] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd5_3_0 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [0] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [1] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_nil _⟩⟩⟩
theorem subd5_4_0 : subd5_4 [-2] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-1, -2] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-1, -1] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-1, 0] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-1, 1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-1, 2] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [0, -3] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [0, -2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [0, -1] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [0, 0] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [0, 1] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [0, 2] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [1, -3] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [1, -2] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [1, -1] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [1, 0] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [1, 1] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [2] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_0 : subd5_5 [-4] = true := by decide +kernel
theorem subd5_5_1 : subd5_5 [-3] = true := by decide +kernel
theorem subd5_5_2 : subd5_5 [-2, -5] = true := by decide +kernel
theorem subd5_5_3 : subd5_5 [-2, -4] = true := by decide +kernel
theorem subd5_5_4 : subd5_5 [-2, -3] = true := by decide +kernel
theorem subd5_5_5 : subd5_5 [-2, -2] = true := by decide +kernel
theorem subd5_5_6 : subd5_5 [-2, -1] = true := by decide +kernel
theorem subd5_5_7 : subd5_5 [-2, 0] = true := by decide +kernel
theorem subd5_5_8 : subd5_5 [-2, 1] = true := by decide +kernel
theorem subd5_5_9 : subd5_5 [-2, 2] = true := by decide +kernel
theorem subd5_5_10 : subd5_5 [-1, -4] = true := by decide +kernel
theorem subd5_5_11 : subd5_5 [-1, -3] = true := by decide +kernel
theorem subd5_5_12 : subd5_5 [-1, -2] = true := by decide +kernel
theorem subd5_5_13 : subd5_5 [-1, -1] = true := by decide +kernel
theorem subd5_5_14 : subd5_5 [-1, 0] = true := by decide +kernel
theorem subd5_5_15 : subd5_5 [-1, 1] = true := by decide +kernel
theorem subd5_5_16 : subd5_5 [-1, 2] = true := by decide +kernel
theorem subd5_5_17 : subd5_5 [0, -4] = true := by decide +kernel
theorem subd5_5_18 : subd5_5 [0, -3] = true := by decide +kernel
theorem subd5_5_19 : subd5_5 [0, -2] = true := by decide +kernel
theorem subd5_5_20 : subd5_5 [0, -1] = true := by decide +kernel
theorem subd5_5_21 : subd5_5 [0, 0] = true := by decide +kernel
theorem subd5_5_22 : subd5_5 [0, 1] = true := by decide +kernel
theorem subd5_5_23 : subd5_5 [0, 2] = true := by decide +kernel
theorem subd5_5_24 : subd5_5 [0, 3] = true := by decide +kernel
theorem subd5_5_25 : subd5_5 [1, -3] = true := by decide +kernel
theorem subd5_5_26 : subd5_5 [1, -2] = true := by decide +kernel
theorem subd5_5_27 : subd5_5 [1, -1] = true := by decide +kernel
theorem subd5_5_28 : subd5_5 [1, 0] = true := by decide +kernel
theorem subd5_5_29 : subd5_5 [1, 1] = true := by decide +kernel
theorem subd5_5_30 : subd5_5 [1, 2] = true := by decide +kernel
theorem subd5_5_31 : subd5_5 [1, 3] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_cons.2 ⟨subd5_5_1, List.forall_mem_cons.2 ⟨subd5_5_2, List.forall_mem_cons.2 ⟨subd5_5_3, List.forall_mem_cons.2 ⟨subd5_5_4, List.forall_mem_cons.2 ⟨subd5_5_5, List.forall_mem_cons.2 ⟨subd5_5_6, List.forall_mem_cons.2 ⟨subd5_5_7, List.forall_mem_cons.2 ⟨subd5_5_8, List.forall_mem_cons.2 ⟨subd5_5_9, List.forall_mem_cons.2 ⟨subd5_5_10, List.forall_mem_cons.2 ⟨subd5_5_11, List.forall_mem_cons.2 ⟨subd5_5_12, List.forall_mem_cons.2 ⟨subd5_5_13, List.forall_mem_cons.2 ⟨subd5_5_14, List.forall_mem_cons.2 ⟨subd5_5_15, List.forall_mem_cons.2 ⟨subd5_5_16, List.forall_mem_cons.2 ⟨subd5_5_17, List.forall_mem_cons.2 ⟨subd5_5_18, List.forall_mem_cons.2 ⟨subd5_5_19, List.forall_mem_cons.2 ⟨subd5_5_20, List.forall_mem_cons.2 ⟨subd5_5_21, List.forall_mem_cons.2 ⟨subd5_5_22, List.forall_mem_cons.2 ⟨subd5_5_23, List.forall_mem_cons.2 ⟨subd5_5_24, List.forall_mem_cons.2 ⟨subd5_5_25, List.forall_mem_cons.2 ⟨subd5_5_26, List.forall_mem_cons.2 ⟨subd5_5_27, List.forall_mem_cons.2 ⟨subd5_5_28, List.forall_mem_cons.2 ⟨subd5_5_29, List.forall_mem_cons.2 ⟨subd5_5_30, List.forall_mem_cons.2 ⟨subd5_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_32 : subd5_5 [2, -3] = true := by decide +kernel
theorem subd5_5_33 : subd5_5 [2, -2] = true := by decide +kernel
theorem subd5_5_34 : subd5_5 [2, -1] = true := by decide +kernel
theorem subd5_5_35 : subd5_5 [2, 0] = true := by decide +kernel
theorem subd5_5_36 : subd5_5 [2, 1] = true := by decide +kernel
theorem subd5_5_37 : subd5_5 [2, 2] = true := by decide +kernel
theorem subd5_5_38 : subd5_5 [2, 3] = true := by decide +kernel
theorem subd5_5_39 : subd5_5 [2, 4] = true := by decide +kernel
theorem subd5_5_40 : subd5_5 [3] = true := by decide +kernel
theorem subd5_5_41 : subd5_5 [4] = true := by decide +kernel
theorem sbd5_5_1 : ∀ q ∈ blkd5_5_1, subd5_5 q = true := by
  unfold blkd5_5_1
  exact List.forall_mem_cons.2 ⟨subd5_5_32, List.forall_mem_cons.2 ⟨subd5_5_33, List.forall_mem_cons.2 ⟨subd5_5_34, List.forall_mem_cons.2 ⟨subd5_5_35, List.forall_mem_cons.2 ⟨subd5_5_36, List.forall_mem_cons.2 ⟨subd5_5_37, List.forall_mem_cons.2 ⟨subd5_5_38, List.forall_mem_cons.2 ⟨subd5_5_39, List.forall_mem_cons.2 ⟨subd5_5_40, List.forall_mem_cons.2 ⟨subd5_5_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_0 : subd5_6 [-3] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-2, -3] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [-2, -2] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [-2, -1] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [-2, 0] = true := by decide +kernel
theorem subd5_6_5 : subd5_6 [-2, 1] = true := by decide +kernel
theorem subd5_6_6 : subd5_6 [-2, 2] = true := by decide +kernel
theorem subd5_6_7 : subd5_6 [-2, 3] = true := by decide +kernel
theorem subd5_6_8 : subd5_6 [-2, 4] = true := by decide +kernel
theorem subd5_6_9 : subd5_6 [-1, -4] = true := by decide +kernel
theorem subd5_6_10 : subd5_6 [-1, -3] = true := by decide +kernel
theorem subd5_6_11 : subd5_6 [-1, -2] = true := by decide +kernel
theorem subd5_6_12 : subd5_6 [-1, -1] = true := by decide +kernel
theorem subd5_6_13 : subd5_6 [-1, 0] = true := by decide +kernel
theorem subd5_6_14 : subd5_6 [-1, 1] = true := by decide +kernel
theorem subd5_6_15 : subd5_6 [-1, 2] = true := by decide +kernel
theorem subd5_6_16 : subd5_6 [-1, 3] = true := by decide +kernel
theorem subd5_6_17 : subd5_6 [-1, 4] = true := by decide +kernel
theorem subd5_6_18 : subd5_6 [0, -5] = true := by decide +kernel
theorem subd5_6_19 : subd5_6 [0, -4] = true := by decide +kernel
theorem subd5_6_20 : subd5_6 [0, -3] = true := by decide +kernel
theorem subd5_6_21 : subd5_6 [0, -2] = true := by decide +kernel
theorem subd5_6_22 : subd5_6 [0, -1] = true := by decide +kernel
theorem subd5_6_23 : subd5_6 [0, 0] = true := by decide +kernel
theorem subd5_6_24 : subd5_6 [0, 1] = true := by decide +kernel
theorem subd5_6_25 : subd5_6 [0, 2] = true := by decide +kernel
theorem subd5_6_26 : subd5_6 [0, 3] = true := by decide +kernel
theorem subd5_6_27 : subd5_6 [0, 4] = true := by decide +kernel
theorem subd5_6_28 : subd5_6 [1, -5] = true := by decide +kernel
theorem subd5_6_29 : subd5_6 [1, -4] = true := by decide +kernel
theorem subd5_6_30 : subd5_6 [1, -3] = true := by decide +kernel
theorem subd5_6_31 : subd5_6 [1, -2] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_cons.2 ⟨subd5_6_5, List.forall_mem_cons.2 ⟨subd5_6_6, List.forall_mem_cons.2 ⟨subd5_6_7, List.forall_mem_cons.2 ⟨subd5_6_8, List.forall_mem_cons.2 ⟨subd5_6_9, List.forall_mem_cons.2 ⟨subd5_6_10, List.forall_mem_cons.2 ⟨subd5_6_11, List.forall_mem_cons.2 ⟨subd5_6_12, List.forall_mem_cons.2 ⟨subd5_6_13, List.forall_mem_cons.2 ⟨subd5_6_14, List.forall_mem_cons.2 ⟨subd5_6_15, List.forall_mem_cons.2 ⟨subd5_6_16, List.forall_mem_cons.2 ⟨subd5_6_17, List.forall_mem_cons.2 ⟨subd5_6_18, List.forall_mem_cons.2 ⟨subd5_6_19, List.forall_mem_cons.2 ⟨subd5_6_20, List.forall_mem_cons.2 ⟨subd5_6_21, List.forall_mem_cons.2 ⟨subd5_6_22, List.forall_mem_cons.2 ⟨subd5_6_23, List.forall_mem_cons.2 ⟨subd5_6_24, List.forall_mem_cons.2 ⟨subd5_6_25, List.forall_mem_cons.2 ⟨subd5_6_26, List.forall_mem_cons.2 ⟨subd5_6_27, List.forall_mem_cons.2 ⟨subd5_6_28, List.forall_mem_cons.2 ⟨subd5_6_29, List.forall_mem_cons.2 ⟨subd5_6_30, List.forall_mem_cons.2 ⟨subd5_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_32 : subd5_6 [1, -1] = true := by decide +kernel
theorem subd5_6_33 : subd5_6 [1, 0] = true := by decide +kernel
theorem subd5_6_34 : subd5_6 [1, 1] = true := by decide +kernel
theorem subd5_6_35 : subd5_6 [1, 2] = true := by decide +kernel
theorem subd5_6_36 : subd5_6 [1, 3] = true := by decide +kernel
theorem subd5_6_37 : subd5_6 [2, -5] = true := by decide +kernel
theorem subd5_6_38 : subd5_6 [2, -4] = true := by decide +kernel
theorem subd5_6_39 : subd5_6 [2, -3] = true := by decide +kernel
theorem subd5_6_40 : subd5_6 [2, -2] = true := by decide +kernel
theorem subd5_6_41 : subd5_6 [2, -1] = true := by decide +kernel
theorem subd5_6_42 : subd5_6 [2, 0] = true := by decide +kernel
theorem subd5_6_43 : subd5_6 [2, 1] = true := by decide +kernel
theorem subd5_6_44 : subd5_6 [2, 2] = true := by decide +kernel
theorem subd5_6_45 : subd5_6 [3] = true := by decide +kernel
theorem sbd5_6_1 : ∀ q ∈ blkd5_6_1, subd5_6 q = true := by
  unfold blkd5_6_1
  exact List.forall_mem_cons.2 ⟨subd5_6_32, List.forall_mem_cons.2 ⟨subd5_6_33, List.forall_mem_cons.2 ⟨subd5_6_34, List.forall_mem_cons.2 ⟨subd5_6_35, List.forall_mem_cons.2 ⟨subd5_6_36, List.forall_mem_cons.2 ⟨subd5_6_37, List.forall_mem_cons.2 ⟨subd5_6_38, List.forall_mem_cons.2 ⟨subd5_6_39, List.forall_mem_cons.2 ⟨subd5_6_40, List.forall_mem_cons.2 ⟨subd5_6_41, List.forall_mem_cons.2 ⟨subd5_6_42, List.forall_mem_cons.2 ⟨subd5_6_43, List.forall_mem_cons.2 ⟨subd5_6_44, List.forall_mem_cons.2 ⟨subd5_6_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_0 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-1, -1, -13] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-1, -1, -12] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-1, -1, -11] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-1, -1, -10] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-1, -1, -9] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [-1, -1, -8] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [-1, -1, -7] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [-1, -1, -6] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [-1, -1, -5] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [-1, -1, -4] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [-1, -1, -3] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [-1, -1, -2] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [-1, -1, -1] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [-1, -1, 0] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [-1, -1, 1] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [-1, -1, 2] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [-1, -1, 3] = true := by decide +kernel
theorem subd5_7_18 : subd5_7 [-1, -1, 4] = true := by decide +kernel
theorem subd5_7_19 : subd5_7 [-1, -1, 5] = true := by decide +kernel
theorem subd5_7_20 : subd5_7 [-1, -1, 6] = true := by decide +kernel
theorem subd5_7_21 : subd5_7 [-1, -1, 7] = true := by decide +kernel
theorem subd5_7_22 : subd5_7 [-1, -1, 8] = true := by decide +kernel
theorem subd5_7_23 : subd5_7 [-1, -1, 9] = true := by decide +kernel
theorem subd5_7_24 : subd5_7 [-1, -1, 10] = true := by decide +kernel
theorem subd5_7_25 : subd5_7 [-1, -1, 11] = true := by decide +kernel
theorem subd5_7_26 : subd5_7 [-1, -1, 12] = true := by decide +kernel
theorem subd5_7_27 : subd5_7 [-1, 0, -14] = true := by decide +kernel
theorem subd5_7_28 : subd5_7 [-1, 0, -13] = true := by decide +kernel
theorem subd5_7_29 : subd5_7 [-1, 0, -12] = true := by decide +kernel
theorem subd5_7_30 : subd5_7 [-1, 0, -11] = true := by decide +kernel
theorem subd5_7_31 : subd5_7 [-1, 0, -10] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_cons.2 ⟨subd5_7_18, List.forall_mem_cons.2 ⟨subd5_7_19, List.forall_mem_cons.2 ⟨subd5_7_20, List.forall_mem_cons.2 ⟨subd5_7_21, List.forall_mem_cons.2 ⟨subd5_7_22, List.forall_mem_cons.2 ⟨subd5_7_23, List.forall_mem_cons.2 ⟨subd5_7_24, List.forall_mem_cons.2 ⟨subd5_7_25, List.forall_mem_cons.2 ⟨subd5_7_26, List.forall_mem_cons.2 ⟨subd5_7_27, List.forall_mem_cons.2 ⟨subd5_7_28, List.forall_mem_cons.2 ⟨subd5_7_29, List.forall_mem_cons.2 ⟨subd5_7_30, List.forall_mem_cons.2 ⟨subd5_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_32 : subd5_7 [-1, 0, -9] = true := by decide +kernel
theorem subd5_7_33 : subd5_7 [-1, 0, -8] = true := by decide +kernel
theorem subd5_7_34 : subd5_7 [-1, 0, -7] = true := by decide +kernel
theorem subd5_7_35 : subd5_7 [-1, 0, -6] = true := by decide +kernel
theorem subd5_7_36 : subd5_7 [-1, 0, -5] = true := by decide +kernel
theorem subd5_7_37 : subd5_7 [-1, 0, -4] = true := by decide +kernel
theorem subd5_7_38 : subd5_7 [-1, 0, -3] = true := by decide +kernel
theorem subd5_7_39 : subd5_7 [-1, 0, -2] = true := by decide +kernel
theorem subd5_7_40 : subd5_7 [-1, 0, -1] = true := by decide +kernel
theorem subd5_7_41 : subd5_7 [-1, 0, 0] = true := by decide +kernel
theorem subd5_7_42 : subd5_7 [-1, 0, 1] = true := by decide +kernel
theorem subd5_7_43 : subd5_7 [-1, 0, 2] = true := by decide +kernel
theorem subd5_7_44 : subd5_7 [-1, 0, 3] = true := by decide +kernel
theorem subd5_7_45 : subd5_7 [-1, 0, 4] = true := by decide +kernel
theorem subd5_7_46 : subd5_7 [-1, 0, 5] = true := by decide +kernel
theorem subd5_7_47 : subd5_7 [-1, 0, 6] = true := by decide +kernel
theorem subd5_7_48 : subd5_7 [-1, 0, 7] = true := by decide +kernel
theorem subd5_7_49 : subd5_7 [-1, 0, 8] = true := by decide +kernel
theorem subd5_7_50 : subd5_7 [-1, 0, 9] = true := by decide +kernel
theorem subd5_7_51 : subd5_7 [-1, 0, 10] = true := by decide +kernel
theorem subd5_7_52 : subd5_7 [-1, 0, 11] = true := by decide +kernel
theorem subd5_7_53 : subd5_7 [-1, 0, 12] = true := by decide +kernel
theorem subd5_7_54 : subd5_7 [-1, 0, 13] = true := by decide +kernel
theorem subd5_7_55 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_56 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_57 : subd5_7 [0, -1, -15] = true := by decide +kernel
theorem subd5_7_58 : subd5_7 [0, -1, -14] = true := by decide +kernel
theorem subd5_7_59 : subd5_7 [0, -1, -13] = true := by decide +kernel
theorem subd5_7_60 : subd5_7 [0, -1, -12] = true := by decide +kernel
theorem subd5_7_61 : subd5_7 [0, -1, -11] = true := by decide +kernel
theorem subd5_7_62 : subd5_7 [0, -1, -10] = true := by decide +kernel
theorem subd5_7_63 : subd5_7 [0, -1, -9] = true := by decide +kernel
theorem sbd5_7_1 : ∀ q ∈ blkd5_7_1, subd5_7 q = true := by
  unfold blkd5_7_1
  exact List.forall_mem_cons.2 ⟨subd5_7_32, List.forall_mem_cons.2 ⟨subd5_7_33, List.forall_mem_cons.2 ⟨subd5_7_34, List.forall_mem_cons.2 ⟨subd5_7_35, List.forall_mem_cons.2 ⟨subd5_7_36, List.forall_mem_cons.2 ⟨subd5_7_37, List.forall_mem_cons.2 ⟨subd5_7_38, List.forall_mem_cons.2 ⟨subd5_7_39, List.forall_mem_cons.2 ⟨subd5_7_40, List.forall_mem_cons.2 ⟨subd5_7_41, List.forall_mem_cons.2 ⟨subd5_7_42, List.forall_mem_cons.2 ⟨subd5_7_43, List.forall_mem_cons.2 ⟨subd5_7_44, List.forall_mem_cons.2 ⟨subd5_7_45, List.forall_mem_cons.2 ⟨subd5_7_46, List.forall_mem_cons.2 ⟨subd5_7_47, List.forall_mem_cons.2 ⟨subd5_7_48, List.forall_mem_cons.2 ⟨subd5_7_49, List.forall_mem_cons.2 ⟨subd5_7_50, List.forall_mem_cons.2 ⟨subd5_7_51, List.forall_mem_cons.2 ⟨subd5_7_52, List.forall_mem_cons.2 ⟨subd5_7_53, List.forall_mem_cons.2 ⟨subd5_7_54, List.forall_mem_cons.2 ⟨subd5_7_55, List.forall_mem_cons.2 ⟨subd5_7_56, List.forall_mem_cons.2 ⟨subd5_7_57, List.forall_mem_cons.2 ⟨subd5_7_58, List.forall_mem_cons.2 ⟨subd5_7_59, List.forall_mem_cons.2 ⟨subd5_7_60, List.forall_mem_cons.2 ⟨subd5_7_61, List.forall_mem_cons.2 ⟨subd5_7_62, List.forall_mem_cons.2 ⟨subd5_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C091
