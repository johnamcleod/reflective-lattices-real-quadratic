import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_5_192 : subd6_5 [3, -2] = true := by decide +kernel
theorem subd6_5_193 : subd6_5 [3, -1] = true := by decide +kernel
theorem subd6_5_194 : subd6_5 [3, 0] = true := by decide +kernel
theorem subd6_5_195 : subd6_5 [3, 1] = true := by decide +kernel
theorem subd6_5_196 : subd6_5 [3, 2] = true := by decide +kernel
theorem subd6_5_197 : subd6_5 [3, 3] = true := by decide +kernel
theorem subd6_5_198 : subd6_5 [4, -4] = true := by decide +kernel
theorem subd6_5_199 : subd6_5 [4, -3] = true := by decide +kernel
theorem subd6_5_200 : subd6_5 [4, -2] = true := by decide +kernel
theorem subd6_5_201 : subd6_5 [4, -1] = true := by decide +kernel
theorem subd6_5_202 : subd6_5 [4, 0] = true := by decide +kernel
theorem subd6_5_203 : subd6_5 [4, 1] = true := by decide +kernel
theorem subd6_5_204 : subd6_5 [4, 2] = true := by decide +kernel
theorem sbd6_5_6 : ∀ q ∈ blkd6_5_6, subd6_5 q = true := by
  unfold blkd6_5_6
  exact List.forall_mem_cons.2 ⟨subd6_5_192, List.forall_mem_cons.2 ⟨subd6_5_193, List.forall_mem_cons.2 ⟨subd6_5_194, List.forall_mem_cons.2 ⟨subd6_5_195, List.forall_mem_cons.2 ⟨subd6_5_196, List.forall_mem_cons.2 ⟨subd6_5_197, List.forall_mem_cons.2 ⟨subd6_5_198, List.forall_mem_cons.2 ⟨subd6_5_199, List.forall_mem_cons.2 ⟨subd6_5_200, List.forall_mem_cons.2 ⟨subd6_5_201, List.forall_mem_cons.2 ⟨subd6_5_202, List.forall_mem_cons.2 ⟨subd6_5_203, List.forall_mem_cons.2 ⟨subd6_5_204, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel
theorem subd6_6_0 : subd6_6 [-5, -4] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-5, -3] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [-5, -2] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [-5, -1] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [-5, 0] = true := by decide +kernel
theorem subd6_6_5 : subd6_6 [-5, 1] = true := by decide +kernel
theorem subd6_6_6 : subd6_6 [-5, 2] = true := by decide +kernel
theorem subd6_6_7 : subd6_6 [-4, -5] = true := by decide +kernel
theorem subd6_6_8 : subd6_6 [-4, -4] = true := by decide +kernel
theorem subd6_6_9 : subd6_6 [-4, -3] = true := by decide +kernel
theorem subd6_6_10 : subd6_6 [-4, -2] = true := by decide +kernel
theorem subd6_6_11 : subd6_6 [-4, -1] = true := by decide +kernel
theorem subd6_6_12 : subd6_6 [-4, 0] = true := by decide +kernel
theorem subd6_6_13 : subd6_6 [-4, 1] = true := by decide +kernel
theorem subd6_6_14 : subd6_6 [-4, 2] = true := by decide +kernel
theorem subd6_6_15 : subd6_6 [-4, 3] = true := by decide +kernel
theorem subd6_6_16 : subd6_6 [-3, -5] = true := by decide +kernel
theorem subd6_6_17 : subd6_6 [-3, -4] = true := by decide +kernel
theorem subd6_6_18 : subd6_6 [-3, -3] = true := by decide +kernel
theorem subd6_6_19 : subd6_6 [-3, -2] = true := by decide +kernel
theorem subd6_6_20 : subd6_6 [-3, -1] = true := by decide +kernel
theorem subd6_6_21 : subd6_6 [-3, 0] = true := by decide +kernel
theorem subd6_6_22 : subd6_6 [-3, 1] = true := by decide +kernel
theorem subd6_6_23 : subd6_6 [-3, 2] = true := by decide +kernel
theorem subd6_6_24 : subd6_6 [-3, 3] = true := by decide +kernel
theorem subd6_6_25 : subd6_6 [-3, 4] = true := by decide +kernel
theorem subd6_6_26 : subd6_6 [-2, -6] = true := by decide +kernel
theorem subd6_6_27 : subd6_6 [-2, -5] = true := by decide +kernel
theorem subd6_6_28 : subd6_6 [-2, -4] = true := by decide +kernel
theorem subd6_6_29 : subd6_6 [-2, -3] = true := by decide +kernel
theorem subd6_6_30 : subd6_6 [-2, -2] = true := by decide +kernel
theorem subd6_6_31 : subd6_6 [-2, -1, -7] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_cons.2 ⟨subd6_6_5, List.forall_mem_cons.2 ⟨subd6_6_6, List.forall_mem_cons.2 ⟨subd6_6_7, List.forall_mem_cons.2 ⟨subd6_6_8, List.forall_mem_cons.2 ⟨subd6_6_9, List.forall_mem_cons.2 ⟨subd6_6_10, List.forall_mem_cons.2 ⟨subd6_6_11, List.forall_mem_cons.2 ⟨subd6_6_12, List.forall_mem_cons.2 ⟨subd6_6_13, List.forall_mem_cons.2 ⟨subd6_6_14, List.forall_mem_cons.2 ⟨subd6_6_15, List.forall_mem_cons.2 ⟨subd6_6_16, List.forall_mem_cons.2 ⟨subd6_6_17, List.forall_mem_cons.2 ⟨subd6_6_18, List.forall_mem_cons.2 ⟨subd6_6_19, List.forall_mem_cons.2 ⟨subd6_6_20, List.forall_mem_cons.2 ⟨subd6_6_21, List.forall_mem_cons.2 ⟨subd6_6_22, List.forall_mem_cons.2 ⟨subd6_6_23, List.forall_mem_cons.2 ⟨subd6_6_24, List.forall_mem_cons.2 ⟨subd6_6_25, List.forall_mem_cons.2 ⟨subd6_6_26, List.forall_mem_cons.2 ⟨subd6_6_27, List.forall_mem_cons.2 ⟨subd6_6_28, List.forall_mem_cons.2 ⟨subd6_6_29, List.forall_mem_cons.2 ⟨subd6_6_30, List.forall_mem_cons.2 ⟨subd6_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_32 : subd6_6 [-2, -1, -6] = true := by decide +kernel
theorem subd6_6_33 : subd6_6 [-2, -1, -5] = true := by decide +kernel
theorem subd6_6_34 : subd6_6 [-2, -1, -4] = true := by decide +kernel
theorem subd6_6_35 : subd6_6 [-2, -1, -3] = true := by decide +kernel
theorem subd6_6_36 : subd6_6 [-2, -1, -2] = true := by decide +kernel
theorem subd6_6_37 : subd6_6 [-2, -1, -1] = true := by decide +kernel
theorem subd6_6_38 : subd6_6 [-2, -1, 0] = true := by decide +kernel
theorem subd6_6_39 : subd6_6 [-2, -1, 1] = true := by decide +kernel
theorem subd6_6_40 : subd6_6 [-2, -1, 2] = true := by decide +kernel
theorem subd6_6_41 : subd6_6 [-2, -1, 3] = true := by decide +kernel
theorem subd6_6_42 : subd6_6 [-2, -1, 4] = true := by decide +kernel
theorem subd6_6_43 : subd6_6 [-2, -1, 5] = true := by decide +kernel
theorem subd6_6_44 : subd6_6 [-2, -1, 6] = true := by decide +kernel
theorem subd6_6_45 : subd6_6 [-2, 0, -7] = true := by decide +kernel
theorem subd6_6_46 : subd6_6 [-2, 0, -6] = true := by decide +kernel
theorem subd6_6_47 : subd6_6 [-2, 0, -5] = true := by decide +kernel
theorem subd6_6_48 : subd6_6 [-2, 0, -4] = true := by decide +kernel
theorem subd6_6_49 : subd6_6 [-2, 0, -3] = true := by decide +kernel
theorem subd6_6_50 : subd6_6 [-2, 0, -2] = true := by decide +kernel
theorem subd6_6_51 : subd6_6 [-2, 0, -1] = true := by decide +kernel
theorem subd6_6_52 : subd6_6 [-2, 0, 0] = true := by decide +kernel
theorem subd6_6_53 : subd6_6 [-2, 0, 1] = true := by decide +kernel
theorem subd6_6_54 : subd6_6 [-2, 0, 2] = true := by decide +kernel
theorem subd6_6_55 : subd6_6 [-2, 0, 3] = true := by decide +kernel
theorem subd6_6_56 : subd6_6 [-2, 0, 4] = true := by decide +kernel
theorem subd6_6_57 : subd6_6 [-2, 0, 5] = true := by decide +kernel
theorem subd6_6_58 : subd6_6 [-2, 0, 6] = true := by decide +kernel
theorem subd6_6_59 : subd6_6 [-2, 1, -7] = true := by decide +kernel
theorem subd6_6_60 : subd6_6 [-2, 1, -6] = true := by decide +kernel
theorem subd6_6_61 : subd6_6 [-2, 1, -5] = true := by decide +kernel
theorem subd6_6_62 : subd6_6 [-2, 1, -4] = true := by decide +kernel
theorem subd6_6_63 : subd6_6 [-2, 1, -3] = true := by decide +kernel
theorem sbd6_6_1 : ∀ q ∈ blkd6_6_1, subd6_6 q = true := by
  unfold blkd6_6_1
  exact List.forall_mem_cons.2 ⟨subd6_6_32, List.forall_mem_cons.2 ⟨subd6_6_33, List.forall_mem_cons.2 ⟨subd6_6_34, List.forall_mem_cons.2 ⟨subd6_6_35, List.forall_mem_cons.2 ⟨subd6_6_36, List.forall_mem_cons.2 ⟨subd6_6_37, List.forall_mem_cons.2 ⟨subd6_6_38, List.forall_mem_cons.2 ⟨subd6_6_39, List.forall_mem_cons.2 ⟨subd6_6_40, List.forall_mem_cons.2 ⟨subd6_6_41, List.forall_mem_cons.2 ⟨subd6_6_42, List.forall_mem_cons.2 ⟨subd6_6_43, List.forall_mem_cons.2 ⟨subd6_6_44, List.forall_mem_cons.2 ⟨subd6_6_45, List.forall_mem_cons.2 ⟨subd6_6_46, List.forall_mem_cons.2 ⟨subd6_6_47, List.forall_mem_cons.2 ⟨subd6_6_48, List.forall_mem_cons.2 ⟨subd6_6_49, List.forall_mem_cons.2 ⟨subd6_6_50, List.forall_mem_cons.2 ⟨subd6_6_51, List.forall_mem_cons.2 ⟨subd6_6_52, List.forall_mem_cons.2 ⟨subd6_6_53, List.forall_mem_cons.2 ⟨subd6_6_54, List.forall_mem_cons.2 ⟨subd6_6_55, List.forall_mem_cons.2 ⟨subd6_6_56, List.forall_mem_cons.2 ⟨subd6_6_57, List.forall_mem_cons.2 ⟨subd6_6_58, List.forall_mem_cons.2 ⟨subd6_6_59, List.forall_mem_cons.2 ⟨subd6_6_60, List.forall_mem_cons.2 ⟨subd6_6_61, List.forall_mem_cons.2 ⟨subd6_6_62, List.forall_mem_cons.2 ⟨subd6_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_64 : subd6_6 [-2, 1, -2] = true := by decide +kernel
theorem subd6_6_65 : subd6_6 [-2, 1, -1] = true := by decide +kernel
theorem subd6_6_66 : subd6_6 [-2, 1, 0] = true := by decide +kernel
theorem subd6_6_67 : subd6_6 [-2, 1, 1] = true := by decide +kernel
theorem subd6_6_68 : subd6_6 [-2, 1, 2] = true := by decide +kernel
theorem subd6_6_69 : subd6_6 [-2, 1, 3] = true := by decide +kernel
theorem subd6_6_70 : subd6_6 [-2, 1, 4] = true := by decide +kernel
theorem subd6_6_71 : subd6_6 [-2, 1, 5] = true := by decide +kernel
theorem subd6_6_72 : subd6_6 [-2, 2] = true := by decide +kernel
theorem subd6_6_73 : subd6_6 [-2, 3] = true := by decide +kernel
theorem subd6_6_74 : subd6_6 [-2, 4] = true := by decide +kernel
theorem subd6_6_75 : subd6_6 [-2, 5] = true := by decide +kernel
theorem subd6_6_76 : subd6_6 [-1, -6] = true := by decide +kernel
theorem subd6_6_77 : subd6_6 [-1, -5] = true := by decide +kernel
theorem subd6_6_78 : subd6_6 [-1, -4] = true := by decide +kernel
theorem subd6_6_79 : subd6_6 [-1, -3] = true := by decide +kernel
theorem subd6_6_80 : subd6_6 [-1, -2, -6] = true := by decide +kernel
theorem subd6_6_81 : subd6_6 [-1, -2, -5] = true := by decide +kernel
theorem subd6_6_82 : subd6_6 [-1, -2, -4] = true := by decide +kernel
theorem subd6_6_83 : subd6_6 [-1, -2, -3] = true := by decide +kernel
theorem subd6_6_84 : subd6_6 [-1, -2, -2] = true := by decide +kernel
theorem subd6_6_85 : subd6_6 [-1, -2, -1] = true := by decide +kernel
theorem subd6_6_86 : subd6_6 [-1, -2, 0] = true := by decide +kernel
theorem subd6_6_87 : subd6_6 [-1, -2, 1] = true := by decide +kernel
theorem subd6_6_88 : subd6_6 [-1, -2, 2] = true := by decide +kernel
theorem subd6_6_89 : subd6_6 [-1, -2, 3] = true := by decide +kernel
theorem subd6_6_90 : subd6_6 [-1, -2, 4] = true := by decide +kernel
theorem subd6_6_91 : subd6_6 [-1, -2, 5] = true := by decide +kernel
theorem subd6_6_92 : subd6_6 [-1, -2, 6] = true := by decide +kernel
theorem subd6_6_93 : subd6_6 [-1, -1, -7] = true := by decide +kernel
theorem subd6_6_94 : subd6_6 [-1, -1, -6] = true := by decide +kernel
theorem subd6_6_95 : subd6_6 [-1, -1, -5] = true := by decide +kernel
theorem sbd6_6_2 : ∀ q ∈ blkd6_6_2, subd6_6 q = true := by
  unfold blkd6_6_2
  exact List.forall_mem_cons.2 ⟨subd6_6_64, List.forall_mem_cons.2 ⟨subd6_6_65, List.forall_mem_cons.2 ⟨subd6_6_66, List.forall_mem_cons.2 ⟨subd6_6_67, List.forall_mem_cons.2 ⟨subd6_6_68, List.forall_mem_cons.2 ⟨subd6_6_69, List.forall_mem_cons.2 ⟨subd6_6_70, List.forall_mem_cons.2 ⟨subd6_6_71, List.forall_mem_cons.2 ⟨subd6_6_72, List.forall_mem_cons.2 ⟨subd6_6_73, List.forall_mem_cons.2 ⟨subd6_6_74, List.forall_mem_cons.2 ⟨subd6_6_75, List.forall_mem_cons.2 ⟨subd6_6_76, List.forall_mem_cons.2 ⟨subd6_6_77, List.forall_mem_cons.2 ⟨subd6_6_78, List.forall_mem_cons.2 ⟨subd6_6_79, List.forall_mem_cons.2 ⟨subd6_6_80, List.forall_mem_cons.2 ⟨subd6_6_81, List.forall_mem_cons.2 ⟨subd6_6_82, List.forall_mem_cons.2 ⟨subd6_6_83, List.forall_mem_cons.2 ⟨subd6_6_84, List.forall_mem_cons.2 ⟨subd6_6_85, List.forall_mem_cons.2 ⟨subd6_6_86, List.forall_mem_cons.2 ⟨subd6_6_87, List.forall_mem_cons.2 ⟨subd6_6_88, List.forall_mem_cons.2 ⟨subd6_6_89, List.forall_mem_cons.2 ⟨subd6_6_90, List.forall_mem_cons.2 ⟨subd6_6_91, List.forall_mem_cons.2 ⟨subd6_6_92, List.forall_mem_cons.2 ⟨subd6_6_93, List.forall_mem_cons.2 ⟨subd6_6_94, List.forall_mem_cons.2 ⟨subd6_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_96 : subd6_6 [-1, -1, -4] = true := by decide +kernel
theorem subd6_6_97 : subd6_6 [-1, -1, -3] = true := by decide +kernel
theorem subd6_6_98 : subd6_6 [-1, -1, -2] = true := by decide +kernel
theorem subd6_6_99 : subd6_6 [-1, -1, -1] = true := by decide +kernel
theorem subd6_6_100 : subd6_6 [-1, -1, 0] = true := by decide +kernel
theorem subd6_6_101 : subd6_6 [-1, -1, 1] = true := by decide +kernel
theorem subd6_6_102 : subd6_6 [-1, -1, 2] = true := by decide +kernel
theorem subd6_6_103 : subd6_6 [-1, -1, 3] = true := by decide +kernel
theorem subd6_6_104 : subd6_6 [-1, -1, 4] = true := by decide +kernel
theorem subd6_6_105 : subd6_6 [-1, -1, 5] = true := by decide +kernel
theorem subd6_6_106 : subd6_6 [-1, -1, 6] = true := by decide +kernel
theorem subd6_6_107 : subd6_6 [-1, 0, -7] = true := by decide +kernel
theorem subd6_6_108 : subd6_6 [-1, 0, -6] = true := by decide +kernel
theorem subd6_6_109 : subd6_6 [-1, 0, -5] = true := by decide +kernel
theorem subd6_6_110 : subd6_6 [-1, 0, -4] = true := by decide +kernel
theorem subd6_6_111 : subd6_6 [-1, 0, -3] = true := by decide +kernel
theorem subd6_6_112 : subd6_6 [-1, 0, -2] = true := by decide +kernel
theorem subd6_6_113 : subd6_6 [-1, 0, -1] = true := by decide +kernel
theorem subd6_6_114 : subd6_6 [-1, 0, 0] = true := by decide +kernel
theorem subd6_6_115 : subd6_6 [-1, 0, 1] = true := by decide +kernel
theorem subd6_6_116 : subd6_6 [-1, 0, 2] = true := by decide +kernel
theorem subd6_6_117 : subd6_6 [-1, 0, 3] = true := by decide +kernel
theorem subd6_6_118 : subd6_6 [-1, 0, 4] = true := by decide +kernel
theorem subd6_6_119 : subd6_6 [-1, 0, 5] = true := by decide +kernel
theorem subd6_6_120 : subd6_6 [-1, 0, 6] = true := by decide +kernel
theorem subd6_6_121 : subd6_6 [-1, 1, -8] = true := by decide +kernel
theorem subd6_6_122 : subd6_6 [-1, 1, -7] = true := by decide +kernel
theorem subd6_6_123 : subd6_6 [-1, 1, -6] = true := by decide +kernel
theorem subd6_6_124 : subd6_6 [-1, 1, -5] = true := by decide +kernel
theorem subd6_6_125 : subd6_6 [-1, 1, -4] = true := by decide +kernel
theorem subd6_6_126 : subd6_6 [-1, 1, -3] = true := by decide +kernel
theorem subd6_6_127 : subd6_6 [-1, 1, -2] = true := by decide +kernel
theorem sbd6_6_3 : ∀ q ∈ blkd6_6_3, subd6_6 q = true := by
  unfold blkd6_6_3
  exact List.forall_mem_cons.2 ⟨subd6_6_96, List.forall_mem_cons.2 ⟨subd6_6_97, List.forall_mem_cons.2 ⟨subd6_6_98, List.forall_mem_cons.2 ⟨subd6_6_99, List.forall_mem_cons.2 ⟨subd6_6_100, List.forall_mem_cons.2 ⟨subd6_6_101, List.forall_mem_cons.2 ⟨subd6_6_102, List.forall_mem_cons.2 ⟨subd6_6_103, List.forall_mem_cons.2 ⟨subd6_6_104, List.forall_mem_cons.2 ⟨subd6_6_105, List.forall_mem_cons.2 ⟨subd6_6_106, List.forall_mem_cons.2 ⟨subd6_6_107, List.forall_mem_cons.2 ⟨subd6_6_108, List.forall_mem_cons.2 ⟨subd6_6_109, List.forall_mem_cons.2 ⟨subd6_6_110, List.forall_mem_cons.2 ⟨subd6_6_111, List.forall_mem_cons.2 ⟨subd6_6_112, List.forall_mem_cons.2 ⟨subd6_6_113, List.forall_mem_cons.2 ⟨subd6_6_114, List.forall_mem_cons.2 ⟨subd6_6_115, List.forall_mem_cons.2 ⟨subd6_6_116, List.forall_mem_cons.2 ⟨subd6_6_117, List.forall_mem_cons.2 ⟨subd6_6_118, List.forall_mem_cons.2 ⟨subd6_6_119, List.forall_mem_cons.2 ⟨subd6_6_120, List.forall_mem_cons.2 ⟨subd6_6_121, List.forall_mem_cons.2 ⟨subd6_6_122, List.forall_mem_cons.2 ⟨subd6_6_123, List.forall_mem_cons.2 ⟨subd6_6_124, List.forall_mem_cons.2 ⟨subd6_6_125, List.forall_mem_cons.2 ⟨subd6_6_126, List.forall_mem_cons.2 ⟨subd6_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_128 : subd6_6 [-1, 1, -1] = true := by decide +kernel
theorem subd6_6_129 : subd6_6 [-1, 1, 0] = true := by decide +kernel
theorem subd6_6_130 : subd6_6 [-1, 1, 1] = true := by decide +kernel
theorem subd6_6_131 : subd6_6 [-1, 1, 2] = true := by decide +kernel
theorem subd6_6_132 : subd6_6 [-1, 1, 3] = true := by decide +kernel
theorem subd6_6_133 : subd6_6 [-1, 1, 4] = true := by decide +kernel
theorem subd6_6_134 : subd6_6 [-1, 1, 5] = true := by decide +kernel
theorem subd6_6_135 : subd6_6 [-1, 1, 6] = true := by decide +kernel
theorem subd6_6_136 : subd6_6 [-1, 2, -7] = true := by decide +kernel
theorem subd6_6_137 : subd6_6 [-1, 2, -6] = true := by decide +kernel
theorem subd6_6_138 : subd6_6 [-1, 2, -5] = true := by decide +kernel
theorem subd6_6_139 : subd6_6 [-1, 2, -4] = true := by decide +kernel
theorem subd6_6_140 : subd6_6 [-1, 2, -3] = true := by decide +kernel
theorem subd6_6_141 : subd6_6 [-1, 2, -2] = true := by decide +kernel
theorem subd6_6_142 : subd6_6 [-1, 2, -1] = true := by decide +kernel
theorem subd6_6_143 : subd6_6 [-1, 2, 0] = true := by decide +kernel
theorem subd6_6_144 : subd6_6 [-1, 2, 1] = true := by decide +kernel
theorem subd6_6_145 : subd6_6 [-1, 2, 2] = true := by decide +kernel
theorem subd6_6_146 : subd6_6 [-1, 2, 3] = true := by decide +kernel
theorem subd6_6_147 : subd6_6 [-1, 2, 4] = true := by decide +kernel
theorem subd6_6_148 : subd6_6 [-1, 2, 5] = true := by decide +kernel
theorem subd6_6_149 : subd6_6 [-1, 3] = true := by decide +kernel
theorem subd6_6_150 : subd6_6 [-1, 4] = true := by decide +kernel
theorem subd6_6_151 : subd6_6 [-1, 5] = true := by decide +kernel
theorem subd6_6_152 : subd6_6 [0, -6] = true := by decide +kernel
theorem subd6_6_153 : subd6_6 [0, -5] = true := by decide +kernel
theorem subd6_6_154 : subd6_6 [0, -4] = true := by decide +kernel
theorem subd6_6_155 : subd6_6 [0, -3] = true := by decide +kernel
theorem subd6_6_156 : subd6_6 [0, -2, -6] = true := by decide +kernel
theorem subd6_6_157 : subd6_6 [0, -2, -5] = true := by decide +kernel
theorem subd6_6_158 : subd6_6 [0, -2, -4] = true := by decide +kernel
theorem subd6_6_159 : subd6_6 [0, -2, -3] = true := by decide +kernel
theorem sbd6_6_4 : ∀ q ∈ blkd6_6_4, subd6_6 q = true := by
  unfold blkd6_6_4
  exact List.forall_mem_cons.2 ⟨subd6_6_128, List.forall_mem_cons.2 ⟨subd6_6_129, List.forall_mem_cons.2 ⟨subd6_6_130, List.forall_mem_cons.2 ⟨subd6_6_131, List.forall_mem_cons.2 ⟨subd6_6_132, List.forall_mem_cons.2 ⟨subd6_6_133, List.forall_mem_cons.2 ⟨subd6_6_134, List.forall_mem_cons.2 ⟨subd6_6_135, List.forall_mem_cons.2 ⟨subd6_6_136, List.forall_mem_cons.2 ⟨subd6_6_137, List.forall_mem_cons.2 ⟨subd6_6_138, List.forall_mem_cons.2 ⟨subd6_6_139, List.forall_mem_cons.2 ⟨subd6_6_140, List.forall_mem_cons.2 ⟨subd6_6_141, List.forall_mem_cons.2 ⟨subd6_6_142, List.forall_mem_cons.2 ⟨subd6_6_143, List.forall_mem_cons.2 ⟨subd6_6_144, List.forall_mem_cons.2 ⟨subd6_6_145, List.forall_mem_cons.2 ⟨subd6_6_146, List.forall_mem_cons.2 ⟨subd6_6_147, List.forall_mem_cons.2 ⟨subd6_6_148, List.forall_mem_cons.2 ⟨subd6_6_149, List.forall_mem_cons.2 ⟨subd6_6_150, List.forall_mem_cons.2 ⟨subd6_6_151, List.forall_mem_cons.2 ⟨subd6_6_152, List.forall_mem_cons.2 ⟨subd6_6_153, List.forall_mem_cons.2 ⟨subd6_6_154, List.forall_mem_cons.2 ⟨subd6_6_155, List.forall_mem_cons.2 ⟨subd6_6_156, List.forall_mem_cons.2 ⟨subd6_6_157, List.forall_mem_cons.2 ⟨subd6_6_158, List.forall_mem_cons.2 ⟨subd6_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_160 : subd6_6 [0, -2, -2] = true := by decide +kernel
theorem subd6_6_161 : subd6_6 [0, -2, -1] = true := by decide +kernel
theorem subd6_6_162 : subd6_6 [0, -2, 0] = true := by decide +kernel
theorem subd6_6_163 : subd6_6 [0, -2, 1] = true := by decide +kernel
theorem subd6_6_164 : subd6_6 [0, -2, 2] = true := by decide +kernel
theorem subd6_6_165 : subd6_6 [0, -2, 3] = true := by decide +kernel
theorem subd6_6_166 : subd6_6 [0, -2, 4] = true := by decide +kernel
theorem subd6_6_167 : subd6_6 [0, -2, 5] = true := by decide +kernel
theorem subd6_6_168 : subd6_6 [0, -2, 6] = true := by decide +kernel
theorem subd6_6_169 : subd6_6 [0, -1, -7] = true := by decide +kernel
theorem subd6_6_170 : subd6_6 [0, -1, -6] = true := by decide +kernel
theorem subd6_6_171 : subd6_6 [0, -1, -5] = true := by decide +kernel
theorem subd6_6_172 : subd6_6 [0, -1, -4] = true := by decide +kernel
theorem subd6_6_173 : subd6_6 [0, -1, -3] = true := by decide +kernel
theorem subd6_6_174 : subd6_6 [0, -1, -2] = true := by decide +kernel
theorem subd6_6_175 : subd6_6 [0, -1, -1] = true := by decide +kernel
theorem subd6_6_176 : subd6_6 [0, -1, 0] = true := by decide +kernel
theorem subd6_6_177 : subd6_6 [0, -1, 1] = true := by decide +kernel
theorem subd6_6_178 : subd6_6 [0, -1, 2] = true := by decide +kernel
theorem subd6_6_179 : subd6_6 [0, -1, 3] = true := by decide +kernel
theorem subd6_6_180 : subd6_6 [0, -1, 4] = true := by decide +kernel
theorem subd6_6_181 : subd6_6 [0, -1, 5] = true := by decide +kernel
theorem subd6_6_182 : subd6_6 [0, -1, 6] = true := by decide +kernel
theorem subd6_6_183 : subd6_6 [0, -1, 7] = true := by decide +kernel
theorem subd6_6_184 : subd6_6 [0, 0, -7] = true := by decide +kernel
theorem subd6_6_185 : subd6_6 [0, 0, -6] = true := by decide +kernel
theorem subd6_6_186 : subd6_6 [0, 0, -5] = true := by decide +kernel
theorem subd6_6_187 : subd6_6 [0, 0, -4] = true := by decide +kernel
theorem subd6_6_188 : subd6_6 [0, 0, -3] = true := by decide +kernel
theorem subd6_6_189 : subd6_6 [0, 0, -2] = true := by decide +kernel
theorem subd6_6_190 : subd6_6 [0, 0, -1] = true := by decide +kernel
theorem subd6_6_191 : subd6_6 [0, 0, 0] = true := by decide +kernel
theorem sbd6_6_5 : ∀ q ∈ blkd6_6_5, subd6_6 q = true := by
  unfold blkd6_6_5
  exact List.forall_mem_cons.2 ⟨subd6_6_160, List.forall_mem_cons.2 ⟨subd6_6_161, List.forall_mem_cons.2 ⟨subd6_6_162, List.forall_mem_cons.2 ⟨subd6_6_163, List.forall_mem_cons.2 ⟨subd6_6_164, List.forall_mem_cons.2 ⟨subd6_6_165, List.forall_mem_cons.2 ⟨subd6_6_166, List.forall_mem_cons.2 ⟨subd6_6_167, List.forall_mem_cons.2 ⟨subd6_6_168, List.forall_mem_cons.2 ⟨subd6_6_169, List.forall_mem_cons.2 ⟨subd6_6_170, List.forall_mem_cons.2 ⟨subd6_6_171, List.forall_mem_cons.2 ⟨subd6_6_172, List.forall_mem_cons.2 ⟨subd6_6_173, List.forall_mem_cons.2 ⟨subd6_6_174, List.forall_mem_cons.2 ⟨subd6_6_175, List.forall_mem_cons.2 ⟨subd6_6_176, List.forall_mem_cons.2 ⟨subd6_6_177, List.forall_mem_cons.2 ⟨subd6_6_178, List.forall_mem_cons.2 ⟨subd6_6_179, List.forall_mem_cons.2 ⟨subd6_6_180, List.forall_mem_cons.2 ⟨subd6_6_181, List.forall_mem_cons.2 ⟨subd6_6_182, List.forall_mem_cons.2 ⟨subd6_6_183, List.forall_mem_cons.2 ⟨subd6_6_184, List.forall_mem_cons.2 ⟨subd6_6_185, List.forall_mem_cons.2 ⟨subd6_6_186, List.forall_mem_cons.2 ⟨subd6_6_187, List.forall_mem_cons.2 ⟨subd6_6_188, List.forall_mem_cons.2 ⟨subd6_6_189, List.forall_mem_cons.2 ⟨subd6_6_190, List.forall_mem_cons.2 ⟨subd6_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_192 : subd6_6 [0, 0, 1] = true := by decide +kernel
theorem subd6_6_193 : subd6_6 [0, 0, 2] = true := by decide +kernel
theorem subd6_6_194 : subd6_6 [0, 0, 3] = true := by decide +kernel
theorem subd6_6_195 : subd6_6 [0, 0, 4] = true := by decide +kernel
theorem subd6_6_196 : subd6_6 [0, 0, 5] = true := by decide +kernel
theorem subd6_6_197 : subd6_6 [0, 0, 6] = true := by decide +kernel
theorem subd6_6_198 : subd6_6 [0, 1, -8] = true := by decide +kernel
theorem subd6_6_199 : subd6_6 [0, 1, -7] = true := by decide +kernel
theorem subd6_6_200 : subd6_6 [0, 1, -6] = true := by decide +kernel
theorem subd6_6_201 : subd6_6 [0, 1, -5] = true := by decide +kernel
theorem subd6_6_202 : subd6_6 [0, 1, -4] = true := by decide +kernel
theorem subd6_6_203 : subd6_6 [0, 1, -3] = true := by decide +kernel
theorem subd6_6_204 : subd6_6 [0, 1, -2] = true := by decide +kernel
theorem subd6_6_205 : subd6_6 [0, 1, -1] = true := by decide +kernel
theorem subd6_6_206 : subd6_6 [0, 1, 0] = true := by decide +kernel
theorem subd6_6_207 : subd6_6 [0, 1, 1] = true := by decide +kernel
theorem subd6_6_208 : subd6_6 [0, 1, 2] = true := by decide +kernel
theorem subd6_6_209 : subd6_6 [0, 1, 3] = true := by decide +kernel
theorem subd6_6_210 : subd6_6 [0, 1, 4] = true := by decide +kernel
theorem subd6_6_211 : subd6_6 [0, 1, 5] = true := by decide +kernel
theorem subd6_6_212 : subd6_6 [0, 1, 6] = true := by decide +kernel
theorem subd6_6_213 : subd6_6 [0, 2, -7] = true := by decide +kernel
theorem subd6_6_214 : subd6_6 [0, 2, -6] = true := by decide +kernel
theorem subd6_6_215 : subd6_6 [0, 2, -5] = true := by decide +kernel
theorem subd6_6_216 : subd6_6 [0, 2, -4] = true := by decide +kernel
theorem subd6_6_217 : subd6_6 [0, 2, -3] = true := by decide +kernel
theorem subd6_6_218 : subd6_6 [0, 2, -2] = true := by decide +kernel
theorem subd6_6_219 : subd6_6 [0, 2, -1] = true := by decide +kernel
theorem subd6_6_220 : subd6_6 [0, 2, 0] = true := by decide +kernel
theorem subd6_6_221 : subd6_6 [0, 2, 1] = true := by decide +kernel
theorem subd6_6_222 : subd6_6 [0, 2, 2] = true := by decide +kernel
theorem subd6_6_223 : subd6_6 [0, 2, 3] = true := by decide +kernel
theorem sbd6_6_6 : ∀ q ∈ blkd6_6_6, subd6_6 q = true := by
  unfold blkd6_6_6
  exact List.forall_mem_cons.2 ⟨subd6_6_192, List.forall_mem_cons.2 ⟨subd6_6_193, List.forall_mem_cons.2 ⟨subd6_6_194, List.forall_mem_cons.2 ⟨subd6_6_195, List.forall_mem_cons.2 ⟨subd6_6_196, List.forall_mem_cons.2 ⟨subd6_6_197, List.forall_mem_cons.2 ⟨subd6_6_198, List.forall_mem_cons.2 ⟨subd6_6_199, List.forall_mem_cons.2 ⟨subd6_6_200, List.forall_mem_cons.2 ⟨subd6_6_201, List.forall_mem_cons.2 ⟨subd6_6_202, List.forall_mem_cons.2 ⟨subd6_6_203, List.forall_mem_cons.2 ⟨subd6_6_204, List.forall_mem_cons.2 ⟨subd6_6_205, List.forall_mem_cons.2 ⟨subd6_6_206, List.forall_mem_cons.2 ⟨subd6_6_207, List.forall_mem_cons.2 ⟨subd6_6_208, List.forall_mem_cons.2 ⟨subd6_6_209, List.forall_mem_cons.2 ⟨subd6_6_210, List.forall_mem_cons.2 ⟨subd6_6_211, List.forall_mem_cons.2 ⟨subd6_6_212, List.forall_mem_cons.2 ⟨subd6_6_213, List.forall_mem_cons.2 ⟨subd6_6_214, List.forall_mem_cons.2 ⟨subd6_6_215, List.forall_mem_cons.2 ⟨subd6_6_216, List.forall_mem_cons.2 ⟨subd6_6_217, List.forall_mem_cons.2 ⟨subd6_6_218, List.forall_mem_cons.2 ⟨subd6_6_219, List.forall_mem_cons.2 ⟨subd6_6_220, List.forall_mem_cons.2 ⟨subd6_6_221, List.forall_mem_cons.2 ⟨subd6_6_222, List.forall_mem_cons.2 ⟨subd6_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
