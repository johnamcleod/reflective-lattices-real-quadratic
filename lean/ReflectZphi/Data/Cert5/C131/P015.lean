import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_160 : subd10_1 [1, 4] = true := by decide +kernel
theorem subd10_1_161 : subd10_1 [1, 5] = true := by decide +kernel
theorem subd10_1_162 : subd10_1 [1, 6] = true := by decide +kernel
theorem subd10_1_163 : subd10_1 [2, -5] = true := by decide +kernel
theorem subd10_1_164 : subd10_1 [2, -4] = true := by decide +kernel
theorem subd10_1_165 : subd10_1 [2, -3] = true := by decide +kernel
theorem subd10_1_166 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_167 : subd10_1 [2, -1] = true := by decide +kernel
theorem subd10_1_168 : subd10_1 [2, 0] = true := by decide +kernel
theorem subd10_1_169 : subd10_1 [2, 1] = true := by decide +kernel
theorem subd10_1_170 : subd10_1 [2, 2] = true := by decide +kernel
theorem subd10_1_171 : subd10_1 [2, 3] = true := by decide +kernel
theorem subd10_1_172 : subd10_1 [2, 4] = true := by decide +kernel
theorem subd10_1_173 : subd10_1 [2, 5] = true := by decide +kernel
theorem subd10_1_174 : subd10_1 [2, 6] = true := by decide +kernel
theorem subd10_1_175 : subd10_1 [3, -4] = true := by decide +kernel
theorem subd10_1_176 : subd10_1 [3, -3] = true := by decide +kernel
theorem subd10_1_177 : subd10_1 [3, -2] = true := by decide +kernel
theorem subd10_1_178 : subd10_1 [3, -1] = true := by decide +kernel
theorem subd10_1_179 : subd10_1 [3, 0] = true := by decide +kernel
theorem subd10_1_180 : subd10_1 [3, 1] = true := by decide +kernel
theorem subd10_1_181 : subd10_1 [3, 2] = true := by decide +kernel
theorem subd10_1_182 : subd10_1 [3, 3] = true := by decide +kernel
theorem subd10_1_183 : subd10_1 [3, 4] = true := by decide +kernel
theorem subd10_1_184 : subd10_1 [3, 5] = true := by decide +kernel
theorem subd10_1_185 : subd10_1 [4, -3] = true := by decide +kernel
theorem subd10_1_186 : subd10_1 [4, -2] = true := by decide +kernel
theorem subd10_1_187 : subd10_1 [4, -1] = true := by decide +kernel
theorem subd10_1_188 : subd10_1 [4, 0] = true := by decide +kernel
theorem subd10_1_189 : subd10_1 [4, 1] = true := by decide +kernel
theorem subd10_1_190 : subd10_1 [4, 2] = true := by decide +kernel
theorem subd10_1_191 : subd10_1 [4, 3] = true := by decide +kernel
theorem sbd10_1_5 : ∀ q ∈ blkd10_1_5, subd10_1 q = true := by
  unfold blkd10_1_5
  exact List.forall_mem_cons.2 ⟨subd10_1_160, List.forall_mem_cons.2 ⟨subd10_1_161, List.forall_mem_cons.2 ⟨subd10_1_162, List.forall_mem_cons.2 ⟨subd10_1_163, List.forall_mem_cons.2 ⟨subd10_1_164, List.forall_mem_cons.2 ⟨subd10_1_165, List.forall_mem_cons.2 ⟨subd10_1_166, List.forall_mem_cons.2 ⟨subd10_1_167, List.forall_mem_cons.2 ⟨subd10_1_168, List.forall_mem_cons.2 ⟨subd10_1_169, List.forall_mem_cons.2 ⟨subd10_1_170, List.forall_mem_cons.2 ⟨subd10_1_171, List.forall_mem_cons.2 ⟨subd10_1_172, List.forall_mem_cons.2 ⟨subd10_1_173, List.forall_mem_cons.2 ⟨subd10_1_174, List.forall_mem_cons.2 ⟨subd10_1_175, List.forall_mem_cons.2 ⟨subd10_1_176, List.forall_mem_cons.2 ⟨subd10_1_177, List.forall_mem_cons.2 ⟨subd10_1_178, List.forall_mem_cons.2 ⟨subd10_1_179, List.forall_mem_cons.2 ⟨subd10_1_180, List.forall_mem_cons.2 ⟨subd10_1_181, List.forall_mem_cons.2 ⟨subd10_1_182, List.forall_mem_cons.2 ⟨subd10_1_183, List.forall_mem_cons.2 ⟨subd10_1_184, List.forall_mem_cons.2 ⟨subd10_1_185, List.forall_mem_cons.2 ⟨subd10_1_186, List.forall_mem_cons.2 ⟨subd10_1_187, List.forall_mem_cons.2 ⟨subd10_1_188, List.forall_mem_cons.2 ⟨subd10_1_189, List.forall_mem_cons.2 ⟨subd10_1_190, List.forall_mem_cons.2 ⟨subd10_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_192 : subd10_1 [4, 4] = true := by decide +kernel
theorem subd10_1_193 : subd10_1 [4, 5] = true := by decide +kernel
theorem subd10_1_194 : subd10_1 [5] = true := by decide +kernel
theorem sbd10_1_6 : ∀ q ∈ blkd10_1_6, subd10_1 q = true := by
  unfold blkd10_1_6
  exact List.forall_mem_cons.2 ⟨subd10_1_192, List.forall_mem_cons.2 ⟨subd10_1_193, List.forall_mem_cons.2 ⟨subd10_1_194, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-8, -7] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-8, -6] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-8, -5] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-8, -4] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-8, -3] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-8, -2] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-8, -1] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-7, -9] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-7, -8] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-7, -7] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-7, -6] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-7, -5] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-7, -4] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-7, -3] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-7, -2] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-7, -1] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-7, 0] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-7, 1] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-7, 2] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [-6, -10] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [-6, -9] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [-6, -8] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [-6, -7] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [-6, -6] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [-6, -5] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [-6, -4] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [-6, -3, -8] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [-6, -3, -7] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [-6, -3, -6] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [-6, -3, -5] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [-6, -3, -4] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [-6, -3, -3] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [-6, -3, -2] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [-6, -3, -1] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [-6, -3, 0] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [-6, -3, 1] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [-6, -3, 2] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [-6, -3, 3] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [-6, -3, 4] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [-6, -2] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [-6, -1] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [-6, 0] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [-6, 1] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [-6, 2] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [-6, 3] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [-6, 4] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [-5, -10] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [-5, -9] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [-5, -8] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [-5, -7] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [-5, -6, -8] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [-5, -6, -7] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [-5, -6, -6] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [-5, -6, -5] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [-5, -6, -4] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [-5, -6, -3] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [-5, -6, -2] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [-5, -6, -1] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [-5, -6, 0] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [-5, -6, 1] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [-5, -6, 2] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [-5, -6, 3] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [-5, -6, 4] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [-5, -6, 5] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [-5, -5, -8] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [-5, -5, -7] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [-5, -5, -6] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [-5, -5, -5] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [-5, -5, -4] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [-5, -5, -3] = true := by decide +kernel
theorem subd11_0_70 : subd11_0 [-5, -5, -2] = true := by decide +kernel
theorem subd11_0_71 : subd11_0 [-5, -5, -1] = true := by decide +kernel
theorem subd11_0_72 : subd11_0 [-5, -5, 0] = true := by decide +kernel
theorem subd11_0_73 : subd11_0 [-5, -5, 1] = true := by decide +kernel
theorem subd11_0_74 : subd11_0 [-5, -5, 2] = true := by decide +kernel
theorem subd11_0_75 : subd11_0 [-5, -5, 3] = true := by decide +kernel
theorem subd11_0_76 : subd11_0 [-5, -5, 4] = true := by decide +kernel
theorem subd11_0_77 : subd11_0 [-5, -5, 5] = true := by decide +kernel
theorem subd11_0_78 : subd11_0 [-5, -4, -8] = true := by decide +kernel
theorem subd11_0_79 : subd11_0 [-5, -4, -7] = true := by decide +kernel
theorem subd11_0_80 : subd11_0 [-5, -4, -6] = true := by decide +kernel
theorem subd11_0_81 : subd11_0 [-5, -4, -5] = true := by decide +kernel
theorem subd11_0_82 : subd11_0 [-5, -4, -4] = true := by decide +kernel
theorem subd11_0_83 : subd11_0 [-5, -4, -3] = true := by decide +kernel
theorem subd11_0_84 : subd11_0 [-5, -4, -2] = true := by decide +kernel
theorem subd11_0_85 : subd11_0 [-5, -4, -1] = true := by decide +kernel
theorem subd11_0_86 : subd11_0 [-5, -4, 0] = true := by decide +kernel
theorem subd11_0_87 : subd11_0 [-5, -4, 1] = true := by decide +kernel
theorem subd11_0_88 : subd11_0 [-5, -4, 2] = true := by decide +kernel
theorem subd11_0_89 : subd11_0 [-5, -4, 3] = true := by decide +kernel
theorem subd11_0_90 : subd11_0 [-5, -4, 4] = true := by decide +kernel
theorem subd11_0_91 : subd11_0 [-5, -4, 5] = true := by decide +kernel
theorem subd11_0_92 : subd11_0 [-5, -3, -9] = true := by decide +kernel
theorem subd11_0_93 : subd11_0 [-5, -3, -8] = true := by decide +kernel
theorem subd11_0_94 : subd11_0 [-5, -3, -7] = true := by decide +kernel
theorem subd11_0_95 : subd11_0 [-5, -3, -6] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_cons.2 ⟨subd11_0_70, List.forall_mem_cons.2 ⟨subd11_0_71, List.forall_mem_cons.2 ⟨subd11_0_72, List.forall_mem_cons.2 ⟨subd11_0_73, List.forall_mem_cons.2 ⟨subd11_0_74, List.forall_mem_cons.2 ⟨subd11_0_75, List.forall_mem_cons.2 ⟨subd11_0_76, List.forall_mem_cons.2 ⟨subd11_0_77, List.forall_mem_cons.2 ⟨subd11_0_78, List.forall_mem_cons.2 ⟨subd11_0_79, List.forall_mem_cons.2 ⟨subd11_0_80, List.forall_mem_cons.2 ⟨subd11_0_81, List.forall_mem_cons.2 ⟨subd11_0_82, List.forall_mem_cons.2 ⟨subd11_0_83, List.forall_mem_cons.2 ⟨subd11_0_84, List.forall_mem_cons.2 ⟨subd11_0_85, List.forall_mem_cons.2 ⟨subd11_0_86, List.forall_mem_cons.2 ⟨subd11_0_87, List.forall_mem_cons.2 ⟨subd11_0_88, List.forall_mem_cons.2 ⟨subd11_0_89, List.forall_mem_cons.2 ⟨subd11_0_90, List.forall_mem_cons.2 ⟨subd11_0_91, List.forall_mem_cons.2 ⟨subd11_0_92, List.forall_mem_cons.2 ⟨subd11_0_93, List.forall_mem_cons.2 ⟨subd11_0_94, List.forall_mem_cons.2 ⟨subd11_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_96 : subd11_0 [-5, -3, -5] = true := by decide +kernel
theorem subd11_0_97 : subd11_0 [-5, -3, -4] = true := by decide +kernel
theorem subd11_0_98 : subd11_0 [-5, -3, -3] = true := by decide +kernel
theorem subd11_0_99 : subd11_0 [-5, -3, -2] = true := by decide +kernel
theorem subd11_0_100 : subd11_0 [-5, -3, -1] = true := by decide +kernel
theorem subd11_0_101 : subd11_0 [-5, -3, 0] = true := by decide +kernel
theorem subd11_0_102 : subd11_0 [-5, -3, 1] = true := by decide +kernel
theorem subd11_0_103 : subd11_0 [-5, -3, 2] = true := by decide +kernel
theorem subd11_0_104 : subd11_0 [-5, -3, 3] = true := by decide +kernel
theorem subd11_0_105 : subd11_0 [-5, -3, 4] = true := by decide +kernel
theorem subd11_0_106 : subd11_0 [-5, -3, 5] = true := by decide +kernel
theorem subd11_0_107 : subd11_0 [-5, -2, -9] = true := by decide +kernel
theorem subd11_0_108 : subd11_0 [-5, -2, -8] = true := by decide +kernel
theorem subd11_0_109 : subd11_0 [-5, -2, -7] = true := by decide +kernel
theorem subd11_0_110 : subd11_0 [-5, -2, -6] = true := by decide +kernel
theorem subd11_0_111 : subd11_0 [-5, -2, -5] = true := by decide +kernel
theorem subd11_0_112 : subd11_0 [-5, -2, -4] = true := by decide +kernel
theorem subd11_0_113 : subd11_0 [-5, -2, -3] = true := by decide +kernel
theorem subd11_0_114 : subd11_0 [-5, -2, -2] = true := by decide +kernel
theorem subd11_0_115 : subd11_0 [-5, -2, -1] = true := by decide +kernel
theorem subd11_0_116 : subd11_0 [-5, -2, 0] = true := by decide +kernel
theorem subd11_0_117 : subd11_0 [-5, -2, 1] = true := by decide +kernel
theorem subd11_0_118 : subd11_0 [-5, -2, 2] = true := by decide +kernel
theorem subd11_0_119 : subd11_0 [-5, -2, 3] = true := by decide +kernel
theorem subd11_0_120 : subd11_0 [-5, -2, 4] = true := by decide +kernel
theorem subd11_0_121 : subd11_0 [-5, -2, 5] = true := by decide +kernel
theorem subd11_0_122 : subd11_0 [-5, -1, -9] = true := by decide +kernel
theorem subd11_0_123 : subd11_0 [-5, -1, -8] = true := by decide +kernel
theorem subd11_0_124 : subd11_0 [-5, -1, -7] = true := by decide +kernel
theorem subd11_0_125 : subd11_0 [-5, -1, -6] = true := by decide +kernel
theorem subd11_0_126 : subd11_0 [-5, -1, -5] = true := by decide +kernel
theorem subd11_0_127 : subd11_0 [-5, -1, -4] = true := by decide +kernel
theorem sbd11_0_3 : ∀ q ∈ blkd11_0_3, subd11_0 q = true := by
  unfold blkd11_0_3
  exact List.forall_mem_cons.2 ⟨subd11_0_96, List.forall_mem_cons.2 ⟨subd11_0_97, List.forall_mem_cons.2 ⟨subd11_0_98, List.forall_mem_cons.2 ⟨subd11_0_99, List.forall_mem_cons.2 ⟨subd11_0_100, List.forall_mem_cons.2 ⟨subd11_0_101, List.forall_mem_cons.2 ⟨subd11_0_102, List.forall_mem_cons.2 ⟨subd11_0_103, List.forall_mem_cons.2 ⟨subd11_0_104, List.forall_mem_cons.2 ⟨subd11_0_105, List.forall_mem_cons.2 ⟨subd11_0_106, List.forall_mem_cons.2 ⟨subd11_0_107, List.forall_mem_cons.2 ⟨subd11_0_108, List.forall_mem_cons.2 ⟨subd11_0_109, List.forall_mem_cons.2 ⟨subd11_0_110, List.forall_mem_cons.2 ⟨subd11_0_111, List.forall_mem_cons.2 ⟨subd11_0_112, List.forall_mem_cons.2 ⟨subd11_0_113, List.forall_mem_cons.2 ⟨subd11_0_114, List.forall_mem_cons.2 ⟨subd11_0_115, List.forall_mem_cons.2 ⟨subd11_0_116, List.forall_mem_cons.2 ⟨subd11_0_117, List.forall_mem_cons.2 ⟨subd11_0_118, List.forall_mem_cons.2 ⟨subd11_0_119, List.forall_mem_cons.2 ⟨subd11_0_120, List.forall_mem_cons.2 ⟨subd11_0_121, List.forall_mem_cons.2 ⟨subd11_0_122, List.forall_mem_cons.2 ⟨subd11_0_123, List.forall_mem_cons.2 ⟨subd11_0_124, List.forall_mem_cons.2 ⟨subd11_0_125, List.forall_mem_cons.2 ⟨subd11_0_126, List.forall_mem_cons.2 ⟨subd11_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_128 : subd11_0 [-5, -1, -3] = true := by decide +kernel
theorem subd11_0_129 : subd11_0 [-5, -1, -2] = true := by decide +kernel
theorem subd11_0_130 : subd11_0 [-5, -1, -1] = true := by decide +kernel
theorem subd11_0_131 : subd11_0 [-5, -1, 0] = true := by decide +kernel
theorem subd11_0_132 : subd11_0 [-5, -1, 1] = true := by decide +kernel
theorem subd11_0_133 : subd11_0 [-5, -1, 2] = true := by decide +kernel
theorem subd11_0_134 : subd11_0 [-5, -1, 3] = true := by decide +kernel
theorem subd11_0_135 : subd11_0 [-5, -1, 4] = true := by decide +kernel
theorem subd11_0_136 : subd11_0 [-5, -1, 5] = true := by decide +kernel
theorem subd11_0_137 : subd11_0 [-5, 0, -9] = true := by decide +kernel
theorem subd11_0_138 : subd11_0 [-5, 0, -8] = true := by decide +kernel
theorem subd11_0_139 : subd11_0 [-5, 0, -7] = true := by decide +kernel
theorem subd11_0_140 : subd11_0 [-5, 0, -6] = true := by decide +kernel
theorem subd11_0_141 : subd11_0 [-5, 0, -5] = true := by decide +kernel
theorem subd11_0_142 : subd11_0 [-5, 0, -4] = true := by decide +kernel
theorem subd11_0_143 : subd11_0 [-5, 0, -3] = true := by decide +kernel
theorem subd11_0_144 : subd11_0 [-5, 0, -2] = true := by decide +kernel
theorem subd11_0_145 : subd11_0 [-5, 0, -1] = true := by decide +kernel
theorem subd11_0_146 : subd11_0 [-5, 0, 0] = true := by decide +kernel
theorem subd11_0_147 : subd11_0 [-5, 0, 1] = true := by decide +kernel
theorem subd11_0_148 : subd11_0 [-5, 0, 2] = true := by decide +kernel
theorem subd11_0_149 : subd11_0 [-5, 0, 3] = true := by decide +kernel
theorem subd11_0_150 : subd11_0 [-5, 0, 4] = true := by decide +kernel
theorem subd11_0_151 : subd11_0 [-5, 0, 5] = true := by decide +kernel
theorem subd11_0_152 : subd11_0 [-5, 1, -8] = true := by decide +kernel
theorem subd11_0_153 : subd11_0 [-5, 1, -7] = true := by decide +kernel
theorem subd11_0_154 : subd11_0 [-5, 1, -6] = true := by decide +kernel
theorem subd11_0_155 : subd11_0 [-5, 1, -5] = true := by decide +kernel
theorem subd11_0_156 : subd11_0 [-5, 1, -4] = true := by decide +kernel
theorem subd11_0_157 : subd11_0 [-5, 1, -3] = true := by decide +kernel
theorem subd11_0_158 : subd11_0 [-5, 1, -2] = true := by decide +kernel
theorem subd11_0_159 : subd11_0 [-5, 1, -1] = true := by decide +kernel
theorem sbd11_0_4 : ∀ q ∈ blkd11_0_4, subd11_0 q = true := by
  unfold blkd11_0_4
  exact List.forall_mem_cons.2 ⟨subd11_0_128, List.forall_mem_cons.2 ⟨subd11_0_129, List.forall_mem_cons.2 ⟨subd11_0_130, List.forall_mem_cons.2 ⟨subd11_0_131, List.forall_mem_cons.2 ⟨subd11_0_132, List.forall_mem_cons.2 ⟨subd11_0_133, List.forall_mem_cons.2 ⟨subd11_0_134, List.forall_mem_cons.2 ⟨subd11_0_135, List.forall_mem_cons.2 ⟨subd11_0_136, List.forall_mem_cons.2 ⟨subd11_0_137, List.forall_mem_cons.2 ⟨subd11_0_138, List.forall_mem_cons.2 ⟨subd11_0_139, List.forall_mem_cons.2 ⟨subd11_0_140, List.forall_mem_cons.2 ⟨subd11_0_141, List.forall_mem_cons.2 ⟨subd11_0_142, List.forall_mem_cons.2 ⟨subd11_0_143, List.forall_mem_cons.2 ⟨subd11_0_144, List.forall_mem_cons.2 ⟨subd11_0_145, List.forall_mem_cons.2 ⟨subd11_0_146, List.forall_mem_cons.2 ⟨subd11_0_147, List.forall_mem_cons.2 ⟨subd11_0_148, List.forall_mem_cons.2 ⟨subd11_0_149, List.forall_mem_cons.2 ⟨subd11_0_150, List.forall_mem_cons.2 ⟨subd11_0_151, List.forall_mem_cons.2 ⟨subd11_0_152, List.forall_mem_cons.2 ⟨subd11_0_153, List.forall_mem_cons.2 ⟨subd11_0_154, List.forall_mem_cons.2 ⟨subd11_0_155, List.forall_mem_cons.2 ⟨subd11_0_156, List.forall_mem_cons.2 ⟨subd11_0_157, List.forall_mem_cons.2 ⟨subd11_0_158, List.forall_mem_cons.2 ⟨subd11_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
