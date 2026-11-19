import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_1_192 : subd12_1 [2, 2] = true := by decide +kernel
theorem subd12_1_193 : subd12_1 [2, 3] = true := by decide +kernel
theorem subd12_1_194 : subd12_1 [2, 4] = true := by decide +kernel
theorem subd12_1_195 : subd12_1 [2, 5] = true := by decide +kernel
theorem subd12_1_196 : subd12_1 [2, 6] = true := by decide +kernel
theorem subd12_1_197 : subd12_1 [3, -4] = true := by decide +kernel
theorem subd12_1_198 : subd12_1 [3, -3] = true := by decide +kernel
theorem subd12_1_199 : subd12_1 [3, -2] = true := by decide +kernel
theorem subd12_1_200 : subd12_1 [3, -1] = true := by decide +kernel
theorem subd12_1_201 : subd12_1 [3, 0] = true := by decide +kernel
theorem subd12_1_202 : subd12_1 [3, 1] = true := by decide +kernel
theorem subd12_1_203 : subd12_1 [3, 2] = true := by decide +kernel
theorem subd12_1_204 : subd12_1 [3, 3] = true := by decide +kernel
theorem subd12_1_205 : subd12_1 [3, 4] = true := by decide +kernel
theorem subd12_1_206 : subd12_1 [3, 5] = true := by decide +kernel
theorem subd12_1_207 : subd12_1 [4, -3] = true := by decide +kernel
theorem subd12_1_208 : subd12_1 [4, -2] = true := by decide +kernel
theorem subd12_1_209 : subd12_1 [4, -1] = true := by decide +kernel
theorem subd12_1_210 : subd12_1 [4, 0] = true := by decide +kernel
theorem subd12_1_211 : subd12_1 [4, 1] = true := by decide +kernel
theorem subd12_1_212 : subd12_1 [4, 2] = true := by decide +kernel
theorem subd12_1_213 : subd12_1 [4, 3] = true := by decide +kernel
theorem subd12_1_214 : subd12_1 [4, 4] = true := by decide +kernel
theorem subd12_1_215 : subd12_1 [4, 5] = true := by decide +kernel
theorem subd12_1_216 : subd12_1 [5] = true := by decide +kernel
theorem sbd12_1_6 : ∀ q ∈ blkd12_1_6, subd12_1 q = true := by
  unfold blkd12_1_6
  exact List.forall_mem_cons.2 ⟨subd12_1_192, List.forall_mem_cons.2 ⟨subd12_1_193, List.forall_mem_cons.2 ⟨subd12_1_194, List.forall_mem_cons.2 ⟨subd12_1_195, List.forall_mem_cons.2 ⟨subd12_1_196, List.forall_mem_cons.2 ⟨subd12_1_197, List.forall_mem_cons.2 ⟨subd12_1_198, List.forall_mem_cons.2 ⟨subd12_1_199, List.forall_mem_cons.2 ⟨subd12_1_200, List.forall_mem_cons.2 ⟨subd12_1_201, List.forall_mem_cons.2 ⟨subd12_1_202, List.forall_mem_cons.2 ⟨subd12_1_203, List.forall_mem_cons.2 ⟨subd12_1_204, List.forall_mem_cons.2 ⟨subd12_1_205, List.forall_mem_cons.2 ⟨subd12_1_206, List.forall_mem_cons.2 ⟨subd12_1_207, List.forall_mem_cons.2 ⟨subd12_1_208, List.forall_mem_cons.2 ⟨subd12_1_209, List.forall_mem_cons.2 ⟨subd12_1_210, List.forall_mem_cons.2 ⟨subd12_1_211, List.forall_mem_cons.2 ⟨subd12_1_212, List.forall_mem_cons.2 ⟨subd12_1_213, List.forall_mem_cons.2 ⟨subd12_1_214, List.forall_mem_cons.2 ⟨subd12_1_215, List.forall_mem_cons.2 ⟨subd12_1_216, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-6, -5] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [-6, -4] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [-6, -3] = true := by decide +kernel
theorem subd13_0_3 : subd13_0 [-6, -2] = true := by decide +kernel
theorem subd13_0_4 : subd13_0 [-6, -1] = true := by decide +kernel
theorem subd13_0_5 : subd13_0 [-6, 0] = true := by decide +kernel
theorem subd13_0_6 : subd13_0 [-6, 1] = true := by decide +kernel
theorem subd13_0_7 : subd13_0 [-5, -6] = true := by decide +kernel
theorem subd13_0_8 : subd13_0 [-5, -5] = true := by decide +kernel
theorem subd13_0_9 : subd13_0 [-5, -4] = true := by decide +kernel
theorem subd13_0_10 : subd13_0 [-5, -3] = true := by decide +kernel
theorem subd13_0_11 : subd13_0 [-5, -2] = true := by decide +kernel
theorem subd13_0_12 : subd13_0 [-5, -1] = true := by decide +kernel
theorem subd13_0_13 : subd13_0 [-5, 0] = true := by decide +kernel
theorem subd13_0_14 : subd13_0 [-5, 1] = true := by decide +kernel
theorem subd13_0_15 : subd13_0 [-5, 2] = true := by decide +kernel
theorem subd13_0_16 : subd13_0 [-4, -6] = true := by decide +kernel
theorem subd13_0_17 : subd13_0 [-4, -5] = true := by decide +kernel
theorem subd13_0_18 : subd13_0 [-4, -4] = true := by decide +kernel
theorem subd13_0_19 : subd13_0 [-4, -3] = true := by decide +kernel
theorem subd13_0_20 : subd13_0 [-4, -2] = true := by decide +kernel
theorem subd13_0_21 : subd13_0 [-4, -1] = true := by decide +kernel
theorem subd13_0_22 : subd13_0 [-4, 0] = true := by decide +kernel
theorem subd13_0_23 : subd13_0 [-4, 1] = true := by decide +kernel
theorem subd13_0_24 : subd13_0 [-4, 2] = true := by decide +kernel
theorem subd13_0_25 : subd13_0 [-4, 3] = true := by decide +kernel
theorem subd13_0_26 : subd13_0 [-3, -6] = true := by decide +kernel
theorem subd13_0_27 : subd13_0 [-3, -5] = true := by decide +kernel
theorem subd13_0_28 : subd13_0 [-3, -4] = true := by decide +kernel
theorem subd13_0_29 : subd13_0 [-3, -3] = true := by decide +kernel
theorem subd13_0_30 : subd13_0 [-3, -2] = true := by decide +kernel
theorem subd13_0_31 : subd13_0 [-3, -1] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_cons.2 ⟨subd13_0_3, List.forall_mem_cons.2 ⟨subd13_0_4, List.forall_mem_cons.2 ⟨subd13_0_5, List.forall_mem_cons.2 ⟨subd13_0_6, List.forall_mem_cons.2 ⟨subd13_0_7, List.forall_mem_cons.2 ⟨subd13_0_8, List.forall_mem_cons.2 ⟨subd13_0_9, List.forall_mem_cons.2 ⟨subd13_0_10, List.forall_mem_cons.2 ⟨subd13_0_11, List.forall_mem_cons.2 ⟨subd13_0_12, List.forall_mem_cons.2 ⟨subd13_0_13, List.forall_mem_cons.2 ⟨subd13_0_14, List.forall_mem_cons.2 ⟨subd13_0_15, List.forall_mem_cons.2 ⟨subd13_0_16, List.forall_mem_cons.2 ⟨subd13_0_17, List.forall_mem_cons.2 ⟨subd13_0_18, List.forall_mem_cons.2 ⟨subd13_0_19, List.forall_mem_cons.2 ⟨subd13_0_20, List.forall_mem_cons.2 ⟨subd13_0_21, List.forall_mem_cons.2 ⟨subd13_0_22, List.forall_mem_cons.2 ⟨subd13_0_23, List.forall_mem_cons.2 ⟨subd13_0_24, List.forall_mem_cons.2 ⟨subd13_0_25, List.forall_mem_cons.2 ⟨subd13_0_26, List.forall_mem_cons.2 ⟨subd13_0_27, List.forall_mem_cons.2 ⟨subd13_0_28, List.forall_mem_cons.2 ⟨subd13_0_29, List.forall_mem_cons.2 ⟨subd13_0_30, List.forall_mem_cons.2 ⟨subd13_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_32 : subd13_0 [-3, 0] = true := by decide +kernel
theorem subd13_0_33 : subd13_0 [-3, 1] = true := by decide +kernel
theorem subd13_0_34 : subd13_0 [-3, 2] = true := by decide +kernel
theorem subd13_0_35 : subd13_0 [-3, 3] = true := by decide +kernel
theorem subd13_0_36 : subd13_0 [-3, 4] = true := by decide +kernel
theorem subd13_0_37 : subd13_0 [-2, -7] = true := by decide +kernel
theorem subd13_0_38 : subd13_0 [-2, -6] = true := by decide +kernel
theorem subd13_0_39 : subd13_0 [-2, -5] = true := by decide +kernel
theorem subd13_0_40 : subd13_0 [-2, -4] = true := by decide +kernel
theorem subd13_0_41 : subd13_0 [-2, -3] = true := by decide +kernel
theorem subd13_0_42 : subd13_0 [-2, -2, -5] = true := by decide +kernel
theorem subd13_0_43 : subd13_0 [-2, -2, -4] = true := by decide +kernel
theorem subd13_0_44 : subd13_0 [-2, -2, -3] = true := by decide +kernel
theorem subd13_0_45 : subd13_0 [-2, -2, -2] = true := by decide +kernel
theorem subd13_0_46 : subd13_0 [-2, -2, -1] = true := by decide +kernel
theorem subd13_0_47 : subd13_0 [-2, -2, 0] = true := by decide +kernel
theorem subd13_0_48 : subd13_0 [-2, -2, 1] = true := by decide +kernel
theorem subd13_0_49 : subd13_0 [-2, -2, 2] = true := by decide +kernel
theorem subd13_0_50 : subd13_0 [-2, -2, 3] = true := by decide +kernel
theorem subd13_0_51 : subd13_0 [-2, -2, 4] = true := by decide +kernel
theorem subd13_0_52 : subd13_0 [-2, -2, 5] = true := by decide +kernel
theorem subd13_0_53 : subd13_0 [-2, -2, 6] = true := by decide +kernel
theorem subd13_0_54 : subd13_0 [-2, -2, 7] = true := by decide +kernel
theorem subd13_0_55 : subd13_0 [-2, -1, -6] = true := by decide +kernel
theorem subd13_0_56 : subd13_0 [-2, -1, -5] = true := by decide +kernel
theorem subd13_0_57 : subd13_0 [-2, -1, -4] = true := by decide +kernel
theorem subd13_0_58 : subd13_0 [-2, -1, -3] = true := by decide +kernel
theorem subd13_0_59 : subd13_0 [-2, -1, -2] = true := by decide +kernel
theorem subd13_0_60 : subd13_0 [-2, -1, -1] = true := by decide +kernel
theorem subd13_0_61 : subd13_0 [-2, -1, 0] = true := by decide +kernel
theorem subd13_0_62 : subd13_0 [-2, -1, 1] = true := by decide +kernel
theorem subd13_0_63 : subd13_0 [-2, -1, 2] = true := by decide +kernel
theorem sbd13_0_1 : ∀ q ∈ blkd13_0_1, subd13_0 q = true := by
  unfold blkd13_0_1
  exact List.forall_mem_cons.2 ⟨subd13_0_32, List.forall_mem_cons.2 ⟨subd13_0_33, List.forall_mem_cons.2 ⟨subd13_0_34, List.forall_mem_cons.2 ⟨subd13_0_35, List.forall_mem_cons.2 ⟨subd13_0_36, List.forall_mem_cons.2 ⟨subd13_0_37, List.forall_mem_cons.2 ⟨subd13_0_38, List.forall_mem_cons.2 ⟨subd13_0_39, List.forall_mem_cons.2 ⟨subd13_0_40, List.forall_mem_cons.2 ⟨subd13_0_41, List.forall_mem_cons.2 ⟨subd13_0_42, List.forall_mem_cons.2 ⟨subd13_0_43, List.forall_mem_cons.2 ⟨subd13_0_44, List.forall_mem_cons.2 ⟨subd13_0_45, List.forall_mem_cons.2 ⟨subd13_0_46, List.forall_mem_cons.2 ⟨subd13_0_47, List.forall_mem_cons.2 ⟨subd13_0_48, List.forall_mem_cons.2 ⟨subd13_0_49, List.forall_mem_cons.2 ⟨subd13_0_50, List.forall_mem_cons.2 ⟨subd13_0_51, List.forall_mem_cons.2 ⟨subd13_0_52, List.forall_mem_cons.2 ⟨subd13_0_53, List.forall_mem_cons.2 ⟨subd13_0_54, List.forall_mem_cons.2 ⟨subd13_0_55, List.forall_mem_cons.2 ⟨subd13_0_56, List.forall_mem_cons.2 ⟨subd13_0_57, List.forall_mem_cons.2 ⟨subd13_0_58, List.forall_mem_cons.2 ⟨subd13_0_59, List.forall_mem_cons.2 ⟨subd13_0_60, List.forall_mem_cons.2 ⟨subd13_0_61, List.forall_mem_cons.2 ⟨subd13_0_62, List.forall_mem_cons.2 ⟨subd13_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_64 : subd13_0 [-2, -1, 3] = true := by decide +kernel
theorem subd13_0_65 : subd13_0 [-2, -1, 4] = true := by decide +kernel
theorem subd13_0_66 : subd13_0 [-2, -1, 5] = true := by decide +kernel
theorem subd13_0_67 : subd13_0 [-2, -1, 6] = true := by decide +kernel
theorem subd13_0_68 : subd13_0 [-2, -1, 7] = true := by decide +kernel
theorem subd13_0_69 : subd13_0 [-2, 0, -6] = true := by decide +kernel
theorem subd13_0_70 : subd13_0 [-2, 0, -5] = true := by decide +kernel
theorem subd13_0_71 : subd13_0 [-2, 0, -4] = true := by decide +kernel
theorem subd13_0_72 : subd13_0 [-2, 0, -3] = true := by decide +kernel
theorem subd13_0_73 : subd13_0 [-2, 0, -2] = true := by decide +kernel
theorem subd13_0_74 : subd13_0 [-2, 0, -1] = true := by decide +kernel
theorem subd13_0_75 : subd13_0 [-2, 0, 0] = true := by decide +kernel
theorem subd13_0_76 : subd13_0 [-2, 0, 1] = true := by decide +kernel
theorem subd13_0_77 : subd13_0 [-2, 0, 2] = true := by decide +kernel
theorem subd13_0_78 : subd13_0 [-2, 0, 3] = true := by decide +kernel
theorem subd13_0_79 : subd13_0 [-2, 0, 4] = true := by decide +kernel
theorem subd13_0_80 : subd13_0 [-2, 0, 5] = true := by decide +kernel
theorem subd13_0_81 : subd13_0 [-2, 0, 6] = true := by decide +kernel
theorem subd13_0_82 : subd13_0 [-2, 0, 7] = true := by decide +kernel
theorem subd13_0_83 : subd13_0 [-2, 1, -6] = true := by decide +kernel
theorem subd13_0_84 : subd13_0 [-2, 1, -5] = true := by decide +kernel
theorem subd13_0_85 : subd13_0 [-2, 1, -4] = true := by decide +kernel
theorem subd13_0_86 : subd13_0 [-2, 1, -3] = true := by decide +kernel
theorem subd13_0_87 : subd13_0 [-2, 1, -2] = true := by decide +kernel
theorem subd13_0_88 : subd13_0 [-2, 1, -1] = true := by decide +kernel
theorem subd13_0_89 : subd13_0 [-2, 1, 0] = true := by decide +kernel
theorem subd13_0_90 : subd13_0 [-2, 1, 1] = true := by decide +kernel
theorem subd13_0_91 : subd13_0 [-2, 1, 2] = true := by decide +kernel
theorem subd13_0_92 : subd13_0 [-2, 1, 3] = true := by decide +kernel
theorem subd13_0_93 : subd13_0 [-2, 1, 4] = true := by decide +kernel
theorem subd13_0_94 : subd13_0 [-2, 1, 5] = true := by decide +kernel
theorem subd13_0_95 : subd13_0 [-2, 1, 6] = true := by decide +kernel
theorem sbd13_0_2 : ∀ q ∈ blkd13_0_2, subd13_0 q = true := by
  unfold blkd13_0_2
  exact List.forall_mem_cons.2 ⟨subd13_0_64, List.forall_mem_cons.2 ⟨subd13_0_65, List.forall_mem_cons.2 ⟨subd13_0_66, List.forall_mem_cons.2 ⟨subd13_0_67, List.forall_mem_cons.2 ⟨subd13_0_68, List.forall_mem_cons.2 ⟨subd13_0_69, List.forall_mem_cons.2 ⟨subd13_0_70, List.forall_mem_cons.2 ⟨subd13_0_71, List.forall_mem_cons.2 ⟨subd13_0_72, List.forall_mem_cons.2 ⟨subd13_0_73, List.forall_mem_cons.2 ⟨subd13_0_74, List.forall_mem_cons.2 ⟨subd13_0_75, List.forall_mem_cons.2 ⟨subd13_0_76, List.forall_mem_cons.2 ⟨subd13_0_77, List.forall_mem_cons.2 ⟨subd13_0_78, List.forall_mem_cons.2 ⟨subd13_0_79, List.forall_mem_cons.2 ⟨subd13_0_80, List.forall_mem_cons.2 ⟨subd13_0_81, List.forall_mem_cons.2 ⟨subd13_0_82, List.forall_mem_cons.2 ⟨subd13_0_83, List.forall_mem_cons.2 ⟨subd13_0_84, List.forall_mem_cons.2 ⟨subd13_0_85, List.forall_mem_cons.2 ⟨subd13_0_86, List.forall_mem_cons.2 ⟨subd13_0_87, List.forall_mem_cons.2 ⟨subd13_0_88, List.forall_mem_cons.2 ⟨subd13_0_89, List.forall_mem_cons.2 ⟨subd13_0_90, List.forall_mem_cons.2 ⟨subd13_0_91, List.forall_mem_cons.2 ⟨subd13_0_92, List.forall_mem_cons.2 ⟨subd13_0_93, List.forall_mem_cons.2 ⟨subd13_0_94, List.forall_mem_cons.2 ⟨subd13_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_96 : subd13_0 [-2, 1, 7] = true := by decide +kernel
theorem subd13_0_97 : subd13_0 [-2, 2] = true := by decide +kernel
theorem subd13_0_98 : subd13_0 [-2, 3] = true := by decide +kernel
theorem subd13_0_99 : subd13_0 [-2, 4] = true := by decide +kernel
theorem subd13_0_100 : subd13_0 [-2, 5] = true := by decide +kernel
theorem subd13_0_101 : subd13_0 [-1, -7] = true := by decide +kernel
theorem subd13_0_102 : subd13_0 [-1, -6] = true := by decide +kernel
theorem subd13_0_103 : subd13_0 [-1, -5] = true := by decide +kernel
theorem subd13_0_104 : subd13_0 [-1, -4] = true := by decide +kernel
theorem subd13_0_105 : subd13_0 [-1, -3] = true := by decide +kernel
theorem subd13_0_106 : subd13_0 [-1, -2, -6] = true := by decide +kernel
theorem subd13_0_107 : subd13_0 [-1, -2, -5] = true := by decide +kernel
theorem subd13_0_108 : subd13_0 [-1, -2, -4] = true := by decide +kernel
theorem subd13_0_109 : subd13_0 [-1, -2, -3] = true := by decide +kernel
theorem subd13_0_110 : subd13_0 [-1, -2, -2] = true := by decide +kernel
theorem subd13_0_111 : subd13_0 [-1, -2, -1] = true := by decide +kernel
theorem subd13_0_112 : subd13_0 [-1, -2, 0] = true := by decide +kernel
theorem subd13_0_113 : subd13_0 [-1, -2, 1] = true := by decide +kernel
theorem subd13_0_114 : subd13_0 [-1, -2, 2] = true := by decide +kernel
theorem subd13_0_115 : subd13_0 [-1, -2, 3] = true := by decide +kernel
theorem subd13_0_116 : subd13_0 [-1, -2, 4] = true := by decide +kernel
theorem subd13_0_117 : subd13_0 [-1, -2, 5] = true := by decide +kernel
theorem subd13_0_118 : subd13_0 [-1, -2, 6] = true := by decide +kernel
theorem subd13_0_119 : subd13_0 [-1, -2, 7] = true := by decide +kernel
theorem subd13_0_120 : subd13_0 [-1, -1, -7] = true := by decide +kernel
theorem subd13_0_121 : subd13_0 [-1, -1, -6] = true := by decide +kernel
theorem subd13_0_122 : subd13_0 [-1, -1, -5] = true := by decide +kernel
theorem subd13_0_123 : subd13_0 [-1, -1, -4] = true := by decide +kernel
theorem subd13_0_124 : subd13_0 [-1, -1, -3] = true := by decide +kernel
theorem subd13_0_125 : subd13_0 [-1, -1, -2] = true := by decide +kernel
theorem subd13_0_126 : subd13_0 [-1, -1, -1] = true := by decide +kernel
theorem subd13_0_127 : subd13_0 [-1, -1, 0] = true := by decide +kernel
theorem sbd13_0_3 : ∀ q ∈ blkd13_0_3, subd13_0 q = true := by
  unfold blkd13_0_3
  exact List.forall_mem_cons.2 ⟨subd13_0_96, List.forall_mem_cons.2 ⟨subd13_0_97, List.forall_mem_cons.2 ⟨subd13_0_98, List.forall_mem_cons.2 ⟨subd13_0_99, List.forall_mem_cons.2 ⟨subd13_0_100, List.forall_mem_cons.2 ⟨subd13_0_101, List.forall_mem_cons.2 ⟨subd13_0_102, List.forall_mem_cons.2 ⟨subd13_0_103, List.forall_mem_cons.2 ⟨subd13_0_104, List.forall_mem_cons.2 ⟨subd13_0_105, List.forall_mem_cons.2 ⟨subd13_0_106, List.forall_mem_cons.2 ⟨subd13_0_107, List.forall_mem_cons.2 ⟨subd13_0_108, List.forall_mem_cons.2 ⟨subd13_0_109, List.forall_mem_cons.2 ⟨subd13_0_110, List.forall_mem_cons.2 ⟨subd13_0_111, List.forall_mem_cons.2 ⟨subd13_0_112, List.forall_mem_cons.2 ⟨subd13_0_113, List.forall_mem_cons.2 ⟨subd13_0_114, List.forall_mem_cons.2 ⟨subd13_0_115, List.forall_mem_cons.2 ⟨subd13_0_116, List.forall_mem_cons.2 ⟨subd13_0_117, List.forall_mem_cons.2 ⟨subd13_0_118, List.forall_mem_cons.2 ⟨subd13_0_119, List.forall_mem_cons.2 ⟨subd13_0_120, List.forall_mem_cons.2 ⟨subd13_0_121, List.forall_mem_cons.2 ⟨subd13_0_122, List.forall_mem_cons.2 ⟨subd13_0_123, List.forall_mem_cons.2 ⟨subd13_0_124, List.forall_mem_cons.2 ⟨subd13_0_125, List.forall_mem_cons.2 ⟨subd13_0_126, List.forall_mem_cons.2 ⟨subd13_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_128 : subd13_0 [-1, -1, 1] = true := by decide +kernel
theorem subd13_0_129 : subd13_0 [-1, -1, 2] = true := by decide +kernel
theorem subd13_0_130 : subd13_0 [-1, -1, 3] = true := by decide +kernel
theorem subd13_0_131 : subd13_0 [-1, -1, 4] = true := by decide +kernel
theorem subd13_0_132 : subd13_0 [-1, -1, 5] = true := by decide +kernel
theorem subd13_0_133 : subd13_0 [-1, -1, 6] = true := by decide +kernel
theorem subd13_0_134 : subd13_0 [-1, -1, 7] = true := by decide +kernel
theorem subd13_0_135 : subd13_0 [-1, 0, -7] = true := by decide +kernel
theorem subd13_0_136 : subd13_0 [-1, 0, -6] = true := by decide +kernel
theorem subd13_0_137 : subd13_0 [-1, 0, -5] = true := by decide +kernel
theorem subd13_0_138 : subd13_0 [-1, 0, -4] = true := by decide +kernel
theorem subd13_0_139 : subd13_0 [-1, 0, -3] = true := by decide +kernel
theorem subd13_0_140 : subd13_0 [-1, 0, -2] = true := by decide +kernel
theorem subd13_0_141 : subd13_0 [-1, 0, -1] = true := by decide +kernel
theorem subd13_0_142 : subd13_0 [-1, 0, 0] = true := by decide +kernel
theorem subd13_0_143 : subd13_0 [-1, 0, 1] = true := by decide +kernel
theorem subd13_0_144 : subd13_0 [-1, 0, 2] = true := by decide +kernel
theorem subd13_0_145 : subd13_0 [-1, 0, 3] = true := by decide +kernel
theorem subd13_0_146 : subd13_0 [-1, 0, 4] = true := by decide +kernel
theorem subd13_0_147 : subd13_0 [-1, 0, 5] = true := by decide +kernel
theorem subd13_0_148 : subd13_0 [-1, 0, 6] = true := by decide +kernel
theorem subd13_0_149 : subd13_0 [-1, 0, 7] = true := by decide +kernel
theorem subd13_0_150 : subd13_0 [-1, 1, -7] = true := by decide +kernel
theorem subd13_0_151 : subd13_0 [-1, 1, -6] = true := by decide +kernel
theorem subd13_0_152 : subd13_0 [-1, 1, -5] = true := by decide +kernel
theorem subd13_0_153 : subd13_0 [-1, 1, -4] = true := by decide +kernel
theorem subd13_0_154 : subd13_0 [-1, 1, -3] = true := by decide +kernel
theorem subd13_0_155 : subd13_0 [-1, 1, -2] = true := by decide +kernel
theorem subd13_0_156 : subd13_0 [-1, 1, -1] = true := by decide +kernel
theorem subd13_0_157 : subd13_0 [-1, 1, 0] = true := by decide +kernel
theorem subd13_0_158 : subd13_0 [-1, 1, 1] = true := by decide +kernel
theorem subd13_0_159 : subd13_0 [-1, 1, 2] = true := by decide +kernel
theorem sbd13_0_4 : ∀ q ∈ blkd13_0_4, subd13_0 q = true := by
  unfold blkd13_0_4
  exact List.forall_mem_cons.2 ⟨subd13_0_128, List.forall_mem_cons.2 ⟨subd13_0_129, List.forall_mem_cons.2 ⟨subd13_0_130, List.forall_mem_cons.2 ⟨subd13_0_131, List.forall_mem_cons.2 ⟨subd13_0_132, List.forall_mem_cons.2 ⟨subd13_0_133, List.forall_mem_cons.2 ⟨subd13_0_134, List.forall_mem_cons.2 ⟨subd13_0_135, List.forall_mem_cons.2 ⟨subd13_0_136, List.forall_mem_cons.2 ⟨subd13_0_137, List.forall_mem_cons.2 ⟨subd13_0_138, List.forall_mem_cons.2 ⟨subd13_0_139, List.forall_mem_cons.2 ⟨subd13_0_140, List.forall_mem_cons.2 ⟨subd13_0_141, List.forall_mem_cons.2 ⟨subd13_0_142, List.forall_mem_cons.2 ⟨subd13_0_143, List.forall_mem_cons.2 ⟨subd13_0_144, List.forall_mem_cons.2 ⟨subd13_0_145, List.forall_mem_cons.2 ⟨subd13_0_146, List.forall_mem_cons.2 ⟨subd13_0_147, List.forall_mem_cons.2 ⟨subd13_0_148, List.forall_mem_cons.2 ⟨subd13_0_149, List.forall_mem_cons.2 ⟨subd13_0_150, List.forall_mem_cons.2 ⟨subd13_0_151, List.forall_mem_cons.2 ⟨subd13_0_152, List.forall_mem_cons.2 ⟨subd13_0_153, List.forall_mem_cons.2 ⟨subd13_0_154, List.forall_mem_cons.2 ⟨subd13_0_155, List.forall_mem_cons.2 ⟨subd13_0_156, List.forall_mem_cons.2 ⟨subd13_0_157, List.forall_mem_cons.2 ⟨subd13_0_158, List.forall_mem_cons.2 ⟨subd13_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
