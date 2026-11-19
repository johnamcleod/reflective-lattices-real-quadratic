import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_3_1088 : subd14_3 [5, -3] = true := by decide +kernel
theorem subd14_3_1089 : subd14_3 [5, -2] = true := by decide +kernel
theorem subd14_3_1090 : subd14_3 [5, -1] = true := by decide +kernel
theorem subd14_3_1091 : subd14_3 [5, 0] = true := by decide +kernel
theorem subd14_3_1092 : subd14_3 [5, 1] = true := by decide +kernel
theorem sbd14_3_34 : ∀ q ∈ blkd14_3_34, subd14_3 q = true := by
  unfold blkd14_3_34
  exact List.forall_mem_cons.2 ⟨subd14_3_1088, List.forall_mem_cons.2 ⟨subd14_3_1089, List.forall_mem_cons.2 ⟨subd14_3_1090, List.forall_mem_cons.2 ⟨subd14_3_1091, List.forall_mem_cons.2 ⟨subd14_3_1092, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-6] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [-5, -5] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [-5, -4] = true := by decide +kernel
theorem subd15_0_3 : subd15_0 [-5, -3] = true := by decide +kernel
theorem subd15_0_4 : subd15_0 [-5, -2] = true := by decide +kernel
theorem subd15_0_5 : subd15_0 [-5, -1] = true := by decide +kernel
theorem subd15_0_6 : subd15_0 [-5, 0] = true := by decide +kernel
theorem subd15_0_7 : subd15_0 [-5, 1] = true := by decide +kernel
theorem subd15_0_8 : subd15_0 [-5, 2] = true := by decide +kernel
theorem subd15_0_9 : subd15_0 [-5, 3] = true := by decide +kernel
theorem subd15_0_10 : subd15_0 [-4, -6] = true := by decide +kernel
theorem subd15_0_11 : subd15_0 [-4, -5] = true := by decide +kernel
theorem subd15_0_12 : subd15_0 [-4, -4] = true := by decide +kernel
theorem subd15_0_13 : subd15_0 [-4, -3] = true := by decide +kernel
theorem subd15_0_14 : subd15_0 [-4, -2] = true := by decide +kernel
theorem subd15_0_15 : subd15_0 [-4, -1] = true := by decide +kernel
theorem subd15_0_16 : subd15_0 [-4, 0] = true := by decide +kernel
theorem subd15_0_17 : subd15_0 [-4, 1] = true := by decide +kernel
theorem subd15_0_18 : subd15_0 [-4, 2] = true := by decide +kernel
theorem subd15_0_19 : subd15_0 [-4, 3] = true := by decide +kernel
theorem subd15_0_20 : subd15_0 [-4, 4] = true := by decide +kernel
theorem subd15_0_21 : subd15_0 [-3, -6] = true := by decide +kernel
theorem subd15_0_22 : subd15_0 [-3, -5] = true := by decide +kernel
theorem subd15_0_23 : subd15_0 [-3, -4] = true := by decide +kernel
theorem subd15_0_24 : subd15_0 [-3, -3] = true := by decide +kernel
theorem subd15_0_25 : subd15_0 [-3, -2] = true := by decide +kernel
theorem subd15_0_26 : subd15_0 [-3, -1] = true := by decide +kernel
theorem subd15_0_27 : subd15_0 [-3, 0] = true := by decide +kernel
theorem subd15_0_28 : subd15_0 [-3, 1] = true := by decide +kernel
theorem subd15_0_29 : subd15_0 [-3, 2] = true := by decide +kernel
theorem subd15_0_30 : subd15_0 [-3, 3] = true := by decide +kernel
theorem subd15_0_31 : subd15_0 [-3, 4] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_cons.2 ⟨subd15_0_3, List.forall_mem_cons.2 ⟨subd15_0_4, List.forall_mem_cons.2 ⟨subd15_0_5, List.forall_mem_cons.2 ⟨subd15_0_6, List.forall_mem_cons.2 ⟨subd15_0_7, List.forall_mem_cons.2 ⟨subd15_0_8, List.forall_mem_cons.2 ⟨subd15_0_9, List.forall_mem_cons.2 ⟨subd15_0_10, List.forall_mem_cons.2 ⟨subd15_0_11, List.forall_mem_cons.2 ⟨subd15_0_12, List.forall_mem_cons.2 ⟨subd15_0_13, List.forall_mem_cons.2 ⟨subd15_0_14, List.forall_mem_cons.2 ⟨subd15_0_15, List.forall_mem_cons.2 ⟨subd15_0_16, List.forall_mem_cons.2 ⟨subd15_0_17, List.forall_mem_cons.2 ⟨subd15_0_18, List.forall_mem_cons.2 ⟨subd15_0_19, List.forall_mem_cons.2 ⟨subd15_0_20, List.forall_mem_cons.2 ⟨subd15_0_21, List.forall_mem_cons.2 ⟨subd15_0_22, List.forall_mem_cons.2 ⟨subd15_0_23, List.forall_mem_cons.2 ⟨subd15_0_24, List.forall_mem_cons.2 ⟨subd15_0_25, List.forall_mem_cons.2 ⟨subd15_0_26, List.forall_mem_cons.2 ⟨subd15_0_27, List.forall_mem_cons.2 ⟨subd15_0_28, List.forall_mem_cons.2 ⟨subd15_0_29, List.forall_mem_cons.2 ⟨subd15_0_30, List.forall_mem_cons.2 ⟨subd15_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_32 : subd15_0 [-2, -6] = true := by decide +kernel
theorem subd15_0_33 : subd15_0 [-2, -5] = true := by decide +kernel
theorem subd15_0_34 : subd15_0 [-2, -4] = true := by decide +kernel
theorem subd15_0_35 : subd15_0 [-2, -3] = true := by decide +kernel
theorem subd15_0_36 : subd15_0 [-2, -2] = true := by decide +kernel
theorem subd15_0_37 : subd15_0 [-2, -1] = true := by decide +kernel
theorem subd15_0_38 : subd15_0 [-2, 0] = true := by decide +kernel
theorem subd15_0_39 : subd15_0 [-2, 1] = true := by decide +kernel
theorem subd15_0_40 : subd15_0 [-2, 2] = true := by decide +kernel
theorem subd15_0_41 : subd15_0 [-2, 3] = true := by decide +kernel
theorem subd15_0_42 : subd15_0 [-2, 4] = true := by decide +kernel
theorem subd15_0_43 : subd15_0 [-2, 5] = true := by decide +kernel
theorem subd15_0_44 : subd15_0 [-1, -6] = true := by decide +kernel
theorem subd15_0_45 : subd15_0 [-1, -5] = true := by decide +kernel
theorem subd15_0_46 : subd15_0 [-1, -4] = true := by decide +kernel
theorem subd15_0_47 : subd15_0 [-1, -3] = true := by decide +kernel
theorem subd15_0_48 : subd15_0 [-1, -2] = true := by decide +kernel
theorem subd15_0_49 : subd15_0 [-1, -1, -7] = true := by decide +kernel
theorem subd15_0_50 : subd15_0 [-1, -1, -6] = true := by decide +kernel
theorem subd15_0_51 : subd15_0 [-1, -1, -5] = true := by decide +kernel
theorem subd15_0_52 : subd15_0 [-1, -1, -4] = true := by decide +kernel
theorem subd15_0_53 : subd15_0 [-1, -1, -3] = true := by decide +kernel
theorem subd15_0_54 : subd15_0 [-1, -1, -2] = true := by decide +kernel
theorem subd15_0_55 : subd15_0 [-1, -1, -1] = true := by decide +kernel
theorem subd15_0_56 : subd15_0 [-1, -1, 0] = true := by decide +kernel
theorem subd15_0_57 : subd15_0 [-1, -1, 1] = true := by decide +kernel
theorem subd15_0_58 : subd15_0 [-1, -1, 2] = true := by decide +kernel
theorem subd15_0_59 : subd15_0 [-1, -1, 3] = true := by decide +kernel
theorem subd15_0_60 : subd15_0 [-1, -1, 4] = true := by decide +kernel
theorem subd15_0_61 : subd15_0 [-1, -1, 5] = true := by decide +kernel
theorem subd15_0_62 : subd15_0 [-1, -1, 6] = true := by decide +kernel
theorem subd15_0_63 : subd15_0 [-1, 0, -7] = true := by decide +kernel
theorem sbd15_0_1 : ∀ q ∈ blkd15_0_1, subd15_0 q = true := by
  unfold blkd15_0_1
  exact List.forall_mem_cons.2 ⟨subd15_0_32, List.forall_mem_cons.2 ⟨subd15_0_33, List.forall_mem_cons.2 ⟨subd15_0_34, List.forall_mem_cons.2 ⟨subd15_0_35, List.forall_mem_cons.2 ⟨subd15_0_36, List.forall_mem_cons.2 ⟨subd15_0_37, List.forall_mem_cons.2 ⟨subd15_0_38, List.forall_mem_cons.2 ⟨subd15_0_39, List.forall_mem_cons.2 ⟨subd15_0_40, List.forall_mem_cons.2 ⟨subd15_0_41, List.forall_mem_cons.2 ⟨subd15_0_42, List.forall_mem_cons.2 ⟨subd15_0_43, List.forall_mem_cons.2 ⟨subd15_0_44, List.forall_mem_cons.2 ⟨subd15_0_45, List.forall_mem_cons.2 ⟨subd15_0_46, List.forall_mem_cons.2 ⟨subd15_0_47, List.forall_mem_cons.2 ⟨subd15_0_48, List.forall_mem_cons.2 ⟨subd15_0_49, List.forall_mem_cons.2 ⟨subd15_0_50, List.forall_mem_cons.2 ⟨subd15_0_51, List.forall_mem_cons.2 ⟨subd15_0_52, List.forall_mem_cons.2 ⟨subd15_0_53, List.forall_mem_cons.2 ⟨subd15_0_54, List.forall_mem_cons.2 ⟨subd15_0_55, List.forall_mem_cons.2 ⟨subd15_0_56, List.forall_mem_cons.2 ⟨subd15_0_57, List.forall_mem_cons.2 ⟨subd15_0_58, List.forall_mem_cons.2 ⟨subd15_0_59, List.forall_mem_cons.2 ⟨subd15_0_60, List.forall_mem_cons.2 ⟨subd15_0_61, List.forall_mem_cons.2 ⟨subd15_0_62, List.forall_mem_cons.2 ⟨subd15_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_64 : subd15_0 [-1, 0, -6] = true := by decide +kernel
theorem subd15_0_65 : subd15_0 [-1, 0, -5] = true := by decide +kernel
theorem subd15_0_66 : subd15_0 [-1, 0, -4] = true := by decide +kernel
theorem subd15_0_67 : subd15_0 [-1, 0, -3] = true := by decide +kernel
theorem subd15_0_68 : subd15_0 [-1, 0, -2] = true := by decide +kernel
theorem subd15_0_69 : subd15_0 [-1, 0, -1] = true := by decide +kernel
theorem subd15_0_70 : subd15_0 [-1, 0, 0] = true := by decide +kernel
theorem subd15_0_71 : subd15_0 [-1, 0, 1] = true := by decide +kernel
theorem subd15_0_72 : subd15_0 [-1, 0, 2] = true := by decide +kernel
theorem subd15_0_73 : subd15_0 [-1, 0, 3] = true := by decide +kernel
theorem subd15_0_74 : subd15_0 [-1, 0, 4] = true := by decide +kernel
theorem subd15_0_75 : subd15_0 [-1, 0, 5] = true := by decide +kernel
theorem subd15_0_76 : subd15_0 [-1, 0, 6] = true := by decide +kernel
theorem subd15_0_77 : subd15_0 [-1, 1] = true := by decide +kernel
theorem subd15_0_78 : subd15_0 [-1, 2] = true := by decide +kernel
theorem subd15_0_79 : subd15_0 [-1, 3] = true := by decide +kernel
theorem subd15_0_80 : subd15_0 [-1, 4] = true := by decide +kernel
theorem subd15_0_81 : subd15_0 [-1, 5] = true := by decide +kernel
theorem subd15_0_82 : subd15_0 [0, -6] = true := by decide +kernel
theorem subd15_0_83 : subd15_0 [0, -5] = true := by decide +kernel
theorem subd15_0_84 : subd15_0 [0, -4] = true := by decide +kernel
theorem subd15_0_85 : subd15_0 [0, -3] = true := by decide +kernel
theorem subd15_0_86 : subd15_0 [0, -2] = true := by decide +kernel
theorem subd15_0_87 : subd15_0 [0, -1, -7] = true := by decide +kernel
theorem subd15_0_88 : subd15_0 [0, -1, -6] = true := by decide +kernel
theorem subd15_0_89 : subd15_0 [0, -1, -5] = true := by decide +kernel
theorem subd15_0_90 : subd15_0 [0, -1, -4] = true := by decide +kernel
theorem subd15_0_91 : subd15_0 [0, -1, -3] = true := by decide +kernel
theorem subd15_0_92 : subd15_0 [0, -1, -2] = true := by decide +kernel
theorem subd15_0_93 : subd15_0 [0, -1, -1] = true := by decide +kernel
theorem subd15_0_94 : subd15_0 [0, -1, 0] = true := by decide +kernel
theorem subd15_0_95 : subd15_0 [0, -1, 1] = true := by decide +kernel
theorem sbd15_0_2 : ∀ q ∈ blkd15_0_2, subd15_0 q = true := by
  unfold blkd15_0_2
  exact List.forall_mem_cons.2 ⟨subd15_0_64, List.forall_mem_cons.2 ⟨subd15_0_65, List.forall_mem_cons.2 ⟨subd15_0_66, List.forall_mem_cons.2 ⟨subd15_0_67, List.forall_mem_cons.2 ⟨subd15_0_68, List.forall_mem_cons.2 ⟨subd15_0_69, List.forall_mem_cons.2 ⟨subd15_0_70, List.forall_mem_cons.2 ⟨subd15_0_71, List.forall_mem_cons.2 ⟨subd15_0_72, List.forall_mem_cons.2 ⟨subd15_0_73, List.forall_mem_cons.2 ⟨subd15_0_74, List.forall_mem_cons.2 ⟨subd15_0_75, List.forall_mem_cons.2 ⟨subd15_0_76, List.forall_mem_cons.2 ⟨subd15_0_77, List.forall_mem_cons.2 ⟨subd15_0_78, List.forall_mem_cons.2 ⟨subd15_0_79, List.forall_mem_cons.2 ⟨subd15_0_80, List.forall_mem_cons.2 ⟨subd15_0_81, List.forall_mem_cons.2 ⟨subd15_0_82, List.forall_mem_cons.2 ⟨subd15_0_83, List.forall_mem_cons.2 ⟨subd15_0_84, List.forall_mem_cons.2 ⟨subd15_0_85, List.forall_mem_cons.2 ⟨subd15_0_86, List.forall_mem_cons.2 ⟨subd15_0_87, List.forall_mem_cons.2 ⟨subd15_0_88, List.forall_mem_cons.2 ⟨subd15_0_89, List.forall_mem_cons.2 ⟨subd15_0_90, List.forall_mem_cons.2 ⟨subd15_0_91, List.forall_mem_cons.2 ⟨subd15_0_92, List.forall_mem_cons.2 ⟨subd15_0_93, List.forall_mem_cons.2 ⟨subd15_0_94, List.forall_mem_cons.2 ⟨subd15_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_96 : subd15_0 [0, -1, 2] = true := by decide +kernel
theorem subd15_0_97 : subd15_0 [0, -1, 3] = true := by decide +kernel
theorem subd15_0_98 : subd15_0 [0, -1, 4] = true := by decide +kernel
theorem subd15_0_99 : subd15_0 [0, -1, 5] = true := by decide +kernel
theorem subd15_0_100 : subd15_0 [0, -1, 6] = true := by decide +kernel
theorem subd15_0_101 : subd15_0 [0, 0, -7] = true := by decide +kernel
theorem subd15_0_102 : subd15_0 [0, 0, -6] = true := by decide +kernel
theorem subd15_0_103 : subd15_0 [0, 0, -5] = true := by decide +kernel
theorem subd15_0_104 : subd15_0 [0, 0, -4] = true := by decide +kernel
theorem subd15_0_105 : subd15_0 [0, 0, -3] = true := by decide +kernel
theorem subd15_0_106 : subd15_0 [0, 0, -2] = true := by decide +kernel
theorem subd15_0_107 : subd15_0 [0, 0, -1] = true := by decide +kernel
theorem subd15_0_108 : subd15_0 [0, 0, 0] = true := by decide +kernel
theorem subd15_0_109 : subd15_0 [0, 0, 1] = true := by decide +kernel
theorem subd15_0_110 : subd15_0 [0, 0, 2] = true := by decide +kernel
theorem subd15_0_111 : subd15_0 [0, 0, 3] = true := by decide +kernel
theorem subd15_0_112 : subd15_0 [0, 0, 4] = true := by decide +kernel
theorem subd15_0_113 : subd15_0 [0, 0, 5] = true := by decide +kernel
theorem subd15_0_114 : subd15_0 [0, 0, 6] = true := by decide +kernel
theorem subd15_0_115 : subd15_0 [0, 1, -7] = true := by decide +kernel
theorem subd15_0_116 : subd15_0 [0, 1, -6] = true := by decide +kernel
theorem subd15_0_117 : subd15_0 [0, 1, -5] = true := by decide +kernel
theorem subd15_0_118 : subd15_0 [0, 1, -4] = true := by decide +kernel
theorem subd15_0_119 : subd15_0 [0, 1, -3] = true := by decide +kernel
theorem subd15_0_120 : subd15_0 [0, 1, -2] = true := by decide +kernel
theorem subd15_0_121 : subd15_0 [0, 1, -1] = true := by decide +kernel
theorem subd15_0_122 : subd15_0 [0, 1, 0] = true := by decide +kernel
theorem subd15_0_123 : subd15_0 [0, 1, 1] = true := by decide +kernel
theorem subd15_0_124 : subd15_0 [0, 1, 2] = true := by decide +kernel
theorem subd15_0_125 : subd15_0 [0, 1, 3] = true := by decide +kernel
theorem subd15_0_126 : subd15_0 [0, 1, 4] = true := by decide +kernel
theorem subd15_0_127 : subd15_0 [0, 1, 5] = true := by decide +kernel
theorem sbd15_0_3 : ∀ q ∈ blkd15_0_3, subd15_0 q = true := by
  unfold blkd15_0_3
  exact List.forall_mem_cons.2 ⟨subd15_0_96, List.forall_mem_cons.2 ⟨subd15_0_97, List.forall_mem_cons.2 ⟨subd15_0_98, List.forall_mem_cons.2 ⟨subd15_0_99, List.forall_mem_cons.2 ⟨subd15_0_100, List.forall_mem_cons.2 ⟨subd15_0_101, List.forall_mem_cons.2 ⟨subd15_0_102, List.forall_mem_cons.2 ⟨subd15_0_103, List.forall_mem_cons.2 ⟨subd15_0_104, List.forall_mem_cons.2 ⟨subd15_0_105, List.forall_mem_cons.2 ⟨subd15_0_106, List.forall_mem_cons.2 ⟨subd15_0_107, List.forall_mem_cons.2 ⟨subd15_0_108, List.forall_mem_cons.2 ⟨subd15_0_109, List.forall_mem_cons.2 ⟨subd15_0_110, List.forall_mem_cons.2 ⟨subd15_0_111, List.forall_mem_cons.2 ⟨subd15_0_112, List.forall_mem_cons.2 ⟨subd15_0_113, List.forall_mem_cons.2 ⟨subd15_0_114, List.forall_mem_cons.2 ⟨subd15_0_115, List.forall_mem_cons.2 ⟨subd15_0_116, List.forall_mem_cons.2 ⟨subd15_0_117, List.forall_mem_cons.2 ⟨subd15_0_118, List.forall_mem_cons.2 ⟨subd15_0_119, List.forall_mem_cons.2 ⟨subd15_0_120, List.forall_mem_cons.2 ⟨subd15_0_121, List.forall_mem_cons.2 ⟨subd15_0_122, List.forall_mem_cons.2 ⟨subd15_0_123, List.forall_mem_cons.2 ⟨subd15_0_124, List.forall_mem_cons.2 ⟨subd15_0_125, List.forall_mem_cons.2 ⟨subd15_0_126, List.forall_mem_cons.2 ⟨subd15_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_128 : subd15_0 [0, 1, 6] = true := by decide +kernel
theorem subd15_0_129 : subd15_0 [0, 2] = true := by decide +kernel
theorem subd15_0_130 : subd15_0 [0, 3] = true := by decide +kernel
theorem subd15_0_131 : subd15_0 [0, 4] = true := by decide +kernel
theorem subd15_0_132 : subd15_0 [0, 5] = true := by decide +kernel
theorem subd15_0_133 : subd15_0 [1, -6] = true := by decide +kernel
theorem subd15_0_134 : subd15_0 [1, -5] = true := by decide +kernel
theorem subd15_0_135 : subd15_0 [1, -4] = true := by decide +kernel
theorem subd15_0_136 : subd15_0 [1, -3] = true := by decide +kernel
theorem subd15_0_137 : subd15_0 [1, -2] = true := by decide +kernel
theorem subd15_0_138 : subd15_0 [1, -1] = true := by decide +kernel
theorem subd15_0_139 : subd15_0 [1, 0, -7] = true := by decide +kernel
theorem subd15_0_140 : subd15_0 [1, 0, -6] = true := by decide +kernel
theorem subd15_0_141 : subd15_0 [1, 0, -5] = true := by decide +kernel
theorem subd15_0_142 : subd15_0 [1, 0, -4] = true := by decide +kernel
theorem subd15_0_143 : subd15_0 [1, 0, -3] = true := by decide +kernel
theorem subd15_0_144 : subd15_0 [1, 0, -2] = true := by decide +kernel
theorem subd15_0_145 : subd15_0 [1, 0, -1] = true := by decide +kernel
theorem subd15_0_146 : subd15_0 [1, 0, 0] = true := by decide +kernel
theorem subd15_0_147 : subd15_0 [1, 0, 1] = true := by decide +kernel
theorem subd15_0_148 : subd15_0 [1, 0, 2] = true := by decide +kernel
theorem subd15_0_149 : subd15_0 [1, 0, 3] = true := by decide +kernel
theorem subd15_0_150 : subd15_0 [1, 0, 4] = true := by decide +kernel
theorem subd15_0_151 : subd15_0 [1, 0, 5] = true := by decide +kernel
theorem subd15_0_152 : subd15_0 [1, 0, 6] = true := by decide +kernel
theorem subd15_0_153 : subd15_0 [1, 1, -7] = true := by decide +kernel
theorem subd15_0_154 : subd15_0 [1, 1, -6] = true := by decide +kernel
theorem subd15_0_155 : subd15_0 [1, 1, -5] = true := by decide +kernel
theorem subd15_0_156 : subd15_0 [1, 1, -4] = true := by decide +kernel
theorem subd15_0_157 : subd15_0 [1, 1, -3] = true := by decide +kernel
theorem subd15_0_158 : subd15_0 [1, 1, -2] = true := by decide +kernel
theorem subd15_0_159 : subd15_0 [1, 1, -1] = true := by decide +kernel
theorem sbd15_0_4 : ∀ q ∈ blkd15_0_4, subd15_0 q = true := by
  unfold blkd15_0_4
  exact List.forall_mem_cons.2 ⟨subd15_0_128, List.forall_mem_cons.2 ⟨subd15_0_129, List.forall_mem_cons.2 ⟨subd15_0_130, List.forall_mem_cons.2 ⟨subd15_0_131, List.forall_mem_cons.2 ⟨subd15_0_132, List.forall_mem_cons.2 ⟨subd15_0_133, List.forall_mem_cons.2 ⟨subd15_0_134, List.forall_mem_cons.2 ⟨subd15_0_135, List.forall_mem_cons.2 ⟨subd15_0_136, List.forall_mem_cons.2 ⟨subd15_0_137, List.forall_mem_cons.2 ⟨subd15_0_138, List.forall_mem_cons.2 ⟨subd15_0_139, List.forall_mem_cons.2 ⟨subd15_0_140, List.forall_mem_cons.2 ⟨subd15_0_141, List.forall_mem_cons.2 ⟨subd15_0_142, List.forall_mem_cons.2 ⟨subd15_0_143, List.forall_mem_cons.2 ⟨subd15_0_144, List.forall_mem_cons.2 ⟨subd15_0_145, List.forall_mem_cons.2 ⟨subd15_0_146, List.forall_mem_cons.2 ⟨subd15_0_147, List.forall_mem_cons.2 ⟨subd15_0_148, List.forall_mem_cons.2 ⟨subd15_0_149, List.forall_mem_cons.2 ⟨subd15_0_150, List.forall_mem_cons.2 ⟨subd15_0_151, List.forall_mem_cons.2 ⟨subd15_0_152, List.forall_mem_cons.2 ⟨subd15_0_153, List.forall_mem_cons.2 ⟨subd15_0_154, List.forall_mem_cons.2 ⟨subd15_0_155, List.forall_mem_cons.2 ⟨subd15_0_156, List.forall_mem_cons.2 ⟨subd15_0_157, List.forall_mem_cons.2 ⟨subd15_0_158, List.forall_mem_cons.2 ⟨subd15_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
