import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_9_0 : subd5_9 [-2] = true := by decide +kernel
theorem subd5_9_1 : subd5_9 [-1, -2] = true := by decide +kernel
theorem subd5_9_2 : subd5_9 [-1, -1, -8] = true := by decide +kernel
theorem subd5_9_3 : subd5_9 [-1, -1, -7] = true := by decide +kernel
theorem subd5_9_4 : subd5_9 [-1, -1, -6] = true := by decide +kernel
theorem subd5_9_5 : subd5_9 [-1, -1, -5] = true := by decide +kernel
theorem subd5_9_6 : subd5_9 [-1, -1, -4] = true := by decide +kernel
theorem subd5_9_7 : subd5_9 [-1, -1, -3] = true := by decide +kernel
theorem subd5_9_8 : subd5_9 [-1, -1, -2] = true := by decide +kernel
theorem subd5_9_9 : subd5_9 [-1, -1, -1] = true := by decide +kernel
theorem subd5_9_10 : subd5_9 [-1, -1, 0] = true := by decide +kernel
theorem subd5_9_11 : subd5_9 [-1, -1, 1] = true := by decide +kernel
theorem subd5_9_12 : subd5_9 [-1, -1, 2] = true := by decide +kernel
theorem subd5_9_13 : subd5_9 [-1, -1, 3] = true := by decide +kernel
theorem subd5_9_14 : subd5_9 [-1, -1, 4] = true := by decide +kernel
theorem subd5_9_15 : subd5_9 [-1, -1, 5] = true := by decide +kernel
theorem subd5_9_16 : subd5_9 [-1, -1, 6] = true := by decide +kernel
theorem subd5_9_17 : subd5_9 [-1, 0, -9] = true := by decide +kernel
theorem subd5_9_18 : subd5_9 [-1, 0, -8] = true := by decide +kernel
theorem subd5_9_19 : subd5_9 [-1, 0, -7] = true := by decide +kernel
theorem subd5_9_20 : subd5_9 [-1, 0, -6] = true := by decide +kernel
theorem subd5_9_21 : subd5_9 [-1, 0, -5] = true := by decide +kernel
theorem subd5_9_22 : subd5_9 [-1, 0, -4] = true := by decide +kernel
theorem subd5_9_23 : subd5_9 [-1, 0, -3] = true := by decide +kernel
theorem subd5_9_24 : subd5_9 [-1, 0, -2] = true := by decide +kernel
theorem subd5_9_25 : subd5_9 [-1, 0, -1] = true := by decide +kernel
theorem subd5_9_26 : subd5_9 [-1, 0, 0] = true := by decide +kernel
theorem subd5_9_27 : subd5_9 [-1, 0, 1] = true := by decide +kernel
theorem subd5_9_28 : subd5_9 [-1, 0, 2] = true := by decide +kernel
theorem subd5_9_29 : subd5_9 [-1, 0, 3] = true := by decide +kernel
theorem subd5_9_30 : subd5_9 [-1, 0, 4] = true := by decide +kernel
theorem subd5_9_31 : subd5_9 [-1, 0, 5] = true := by decide +kernel
theorem sbd5_9_0 : ∀ q ∈ blkd5_9_0, subd5_9 q = true := by
  unfold blkd5_9_0
  exact List.forall_mem_cons.2 ⟨subd5_9_0, List.forall_mem_cons.2 ⟨subd5_9_1, List.forall_mem_cons.2 ⟨subd5_9_2, List.forall_mem_cons.2 ⟨subd5_9_3, List.forall_mem_cons.2 ⟨subd5_9_4, List.forall_mem_cons.2 ⟨subd5_9_5, List.forall_mem_cons.2 ⟨subd5_9_6, List.forall_mem_cons.2 ⟨subd5_9_7, List.forall_mem_cons.2 ⟨subd5_9_8, List.forall_mem_cons.2 ⟨subd5_9_9, List.forall_mem_cons.2 ⟨subd5_9_10, List.forall_mem_cons.2 ⟨subd5_9_11, List.forall_mem_cons.2 ⟨subd5_9_12, List.forall_mem_cons.2 ⟨subd5_9_13, List.forall_mem_cons.2 ⟨subd5_9_14, List.forall_mem_cons.2 ⟨subd5_9_15, List.forall_mem_cons.2 ⟨subd5_9_16, List.forall_mem_cons.2 ⟨subd5_9_17, List.forall_mem_cons.2 ⟨subd5_9_18, List.forall_mem_cons.2 ⟨subd5_9_19, List.forall_mem_cons.2 ⟨subd5_9_20, List.forall_mem_cons.2 ⟨subd5_9_21, List.forall_mem_cons.2 ⟨subd5_9_22, List.forall_mem_cons.2 ⟨subd5_9_23, List.forall_mem_cons.2 ⟨subd5_9_24, List.forall_mem_cons.2 ⟨subd5_9_25, List.forall_mem_cons.2 ⟨subd5_9_26, List.forall_mem_cons.2 ⟨subd5_9_27, List.forall_mem_cons.2 ⟨subd5_9_28, List.forall_mem_cons.2 ⟨subd5_9_29, List.forall_mem_cons.2 ⟨subd5_9_30, List.forall_mem_cons.2 ⟨subd5_9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_9_32 : subd5_9 [-1, 0, 6] = true := by decide +kernel
theorem subd5_9_33 : subd5_9 [-1, 0, 7] = true := by decide +kernel
theorem subd5_9_34 : subd5_9 [-1, 0, 8] = true := by decide +kernel
theorem subd5_9_35 : subd5_9 [-1, 1, -8] = true := by decide +kernel
theorem subd5_9_36 : subd5_9 [-1, 1, -7] = true := by decide +kernel
theorem subd5_9_37 : subd5_9 [-1, 1, -6] = true := by decide +kernel
theorem subd5_9_38 : subd5_9 [-1, 1, -5] = true := by decide +kernel
theorem subd5_9_39 : subd5_9 [-1, 1, -4] = true := by decide +kernel
theorem subd5_9_40 : subd5_9 [-1, 1, -3] = true := by decide +kernel
theorem subd5_9_41 : subd5_9 [-1, 1, -2] = true := by decide +kernel
theorem subd5_9_42 : subd5_9 [-1, 1, -1] = true := by decide +kernel
theorem subd5_9_43 : subd5_9 [-1, 1, 0] = true := by decide +kernel
theorem subd5_9_44 : subd5_9 [-1, 1, 1] = true := by decide +kernel
theorem subd5_9_45 : subd5_9 [-1, 1, 2] = true := by decide +kernel
theorem subd5_9_46 : subd5_9 [-1, 1, 3] = true := by decide +kernel
theorem subd5_9_47 : subd5_9 [-1, 1, 4] = true := by decide +kernel
theorem subd5_9_48 : subd5_9 [-1, 1, 5] = true := by decide +kernel
theorem subd5_9_49 : subd5_9 [-1, 1, 6] = true := by decide +kernel
theorem subd5_9_50 : subd5_9 [-1, 1, 7] = true := by decide +kernel
theorem subd5_9_51 : subd5_9 [-1, 2] = true := by decide +kernel
theorem subd5_9_52 : subd5_9 [0, -3] = true := by decide +kernel
theorem subd5_9_53 : subd5_9 [0, -2] = true := by decide +kernel
theorem subd5_9_54 : subd5_9 [0, -1, -9] = true := by decide +kernel
theorem subd5_9_55 : subd5_9 [0, -1, -8] = true := by decide +kernel
theorem subd5_9_56 : subd5_9 [0, -1, -7] = true := by decide +kernel
theorem subd5_9_57 : subd5_9 [0, -1, -6] = true := by decide +kernel
theorem subd5_9_58 : subd5_9 [0, -1, -5] = true := by decide +kernel
theorem subd5_9_59 : subd5_9 [0, -1, -4] = true := by decide +kernel
theorem subd5_9_60 : subd5_9 [0, -1, -3] = true := by decide +kernel
theorem subd5_9_61 : subd5_9 [0, -1, -2] = true := by decide +kernel
theorem subd5_9_62 : subd5_9 [0, -1, -1] = true := by decide +kernel
theorem subd5_9_63 : subd5_9 [0, -1, 0] = true := by decide +kernel
theorem sbd5_9_1 : ∀ q ∈ blkd5_9_1, subd5_9 q = true := by
  unfold blkd5_9_1
  exact List.forall_mem_cons.2 ⟨subd5_9_32, List.forall_mem_cons.2 ⟨subd5_9_33, List.forall_mem_cons.2 ⟨subd5_9_34, List.forall_mem_cons.2 ⟨subd5_9_35, List.forall_mem_cons.2 ⟨subd5_9_36, List.forall_mem_cons.2 ⟨subd5_9_37, List.forall_mem_cons.2 ⟨subd5_9_38, List.forall_mem_cons.2 ⟨subd5_9_39, List.forall_mem_cons.2 ⟨subd5_9_40, List.forall_mem_cons.2 ⟨subd5_9_41, List.forall_mem_cons.2 ⟨subd5_9_42, List.forall_mem_cons.2 ⟨subd5_9_43, List.forall_mem_cons.2 ⟨subd5_9_44, List.forall_mem_cons.2 ⟨subd5_9_45, List.forall_mem_cons.2 ⟨subd5_9_46, List.forall_mem_cons.2 ⟨subd5_9_47, List.forall_mem_cons.2 ⟨subd5_9_48, List.forall_mem_cons.2 ⟨subd5_9_49, List.forall_mem_cons.2 ⟨subd5_9_50, List.forall_mem_cons.2 ⟨subd5_9_51, List.forall_mem_cons.2 ⟨subd5_9_52, List.forall_mem_cons.2 ⟨subd5_9_53, List.forall_mem_cons.2 ⟨subd5_9_54, List.forall_mem_cons.2 ⟨subd5_9_55, List.forall_mem_cons.2 ⟨subd5_9_56, List.forall_mem_cons.2 ⟨subd5_9_57, List.forall_mem_cons.2 ⟨subd5_9_58, List.forall_mem_cons.2 ⟨subd5_9_59, List.forall_mem_cons.2 ⟨subd5_9_60, List.forall_mem_cons.2 ⟨subd5_9_61, List.forall_mem_cons.2 ⟨subd5_9_62, List.forall_mem_cons.2 ⟨subd5_9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_9_64 : subd5_9 [0, -1, 1] = true := by decide +kernel
theorem subd5_9_65 : subd5_9 [0, -1, 2] = true := by decide +kernel
theorem subd5_9_66 : subd5_9 [0, -1, 3] = true := by decide +kernel
theorem subd5_9_67 : subd5_9 [0, -1, 4] = true := by decide +kernel
theorem subd5_9_68 : subd5_9 [0, -1, 5] = true := by decide +kernel
theorem subd5_9_69 : subd5_9 [0, -1, 6] = true := by decide +kernel
theorem subd5_9_70 : subd5_9 [0, -1, 7] = true := by decide +kernel
theorem subd5_9_71 : subd5_9 [0, -1, 8] = true := by decide +kernel
theorem subd5_9_72 : subd5_9 [0, 0, -10] = true := by decide +kernel
theorem subd5_9_73 : subd5_9 [0, 0, -9] = true := by decide +kernel
theorem subd5_9_74 : subd5_9 [0, 0, -8] = true := by decide +kernel
theorem subd5_9_75 : subd5_9 [0, 0, -7] = true := by decide +kernel
theorem subd5_9_76 : subd5_9 [0, 0, -6] = true := by decide +kernel
theorem subd5_9_77 : subd5_9 [0, 0, -5] = true := by decide +kernel
theorem subd5_9_78 : subd5_9 [0, 0, -4] = true := by decide +kernel
theorem subd5_9_79 : subd5_9 [0, 0, -3] = true := by decide +kernel
theorem subd5_9_80 : subd5_9 [0, 0, -2] = true := by decide +kernel
theorem subd5_9_81 : subd5_9 [0, 0, -1] = true := by decide +kernel
theorem subd5_9_82 : subd5_9 [0, 0, 0] = true := by decide +kernel
theorem subd5_9_83 : subd5_9 [0, 0, 1] = true := by decide +kernel
theorem subd5_9_84 : subd5_9 [0, 0, 2] = true := by decide +kernel
theorem subd5_9_85 : subd5_9 [0, 0, 3] = true := by decide +kernel
theorem subd5_9_86 : subd5_9 [0, 0, 4] = true := by decide +kernel
theorem subd5_9_87 : subd5_9 [0, 0, 5] = true := by decide +kernel
theorem subd5_9_88 : subd5_9 [0, 0, 6] = true := by decide +kernel
theorem subd5_9_89 : subd5_9 [0, 0, 7] = true := by decide +kernel
theorem subd5_9_90 : subd5_9 [0, 0, 8] = true := by decide +kernel
theorem subd5_9_91 : subd5_9 [0, 0, 9] = true := by decide +kernel
theorem subd5_9_92 : subd5_9 [0, 1, -9] = true := by decide +kernel
theorem subd5_9_93 : subd5_9 [0, 1, -8] = true := by decide +kernel
theorem subd5_9_94 : subd5_9 [0, 1, -7] = true := by decide +kernel
theorem subd5_9_95 : subd5_9 [0, 1, -6] = true := by decide +kernel
theorem sbd5_9_2 : ∀ q ∈ blkd5_9_2, subd5_9 q = true := by
  unfold blkd5_9_2
  exact List.forall_mem_cons.2 ⟨subd5_9_64, List.forall_mem_cons.2 ⟨subd5_9_65, List.forall_mem_cons.2 ⟨subd5_9_66, List.forall_mem_cons.2 ⟨subd5_9_67, List.forall_mem_cons.2 ⟨subd5_9_68, List.forall_mem_cons.2 ⟨subd5_9_69, List.forall_mem_cons.2 ⟨subd5_9_70, List.forall_mem_cons.2 ⟨subd5_9_71, List.forall_mem_cons.2 ⟨subd5_9_72, List.forall_mem_cons.2 ⟨subd5_9_73, List.forall_mem_cons.2 ⟨subd5_9_74, List.forall_mem_cons.2 ⟨subd5_9_75, List.forall_mem_cons.2 ⟨subd5_9_76, List.forall_mem_cons.2 ⟨subd5_9_77, List.forall_mem_cons.2 ⟨subd5_9_78, List.forall_mem_cons.2 ⟨subd5_9_79, List.forall_mem_cons.2 ⟨subd5_9_80, List.forall_mem_cons.2 ⟨subd5_9_81, List.forall_mem_cons.2 ⟨subd5_9_82, List.forall_mem_cons.2 ⟨subd5_9_83, List.forall_mem_cons.2 ⟨subd5_9_84, List.forall_mem_cons.2 ⟨subd5_9_85, List.forall_mem_cons.2 ⟨subd5_9_86, List.forall_mem_cons.2 ⟨subd5_9_87, List.forall_mem_cons.2 ⟨subd5_9_88, List.forall_mem_cons.2 ⟨subd5_9_89, List.forall_mem_cons.2 ⟨subd5_9_90, List.forall_mem_cons.2 ⟨subd5_9_91, List.forall_mem_cons.2 ⟨subd5_9_92, List.forall_mem_cons.2 ⟨subd5_9_93, List.forall_mem_cons.2 ⟨subd5_9_94, List.forall_mem_cons.2 ⟨subd5_9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_9_96 : subd5_9 [0, 1, -5] = true := by decide +kernel
theorem subd5_9_97 : subd5_9 [0, 1, -4] = true := by decide +kernel
theorem subd5_9_98 : subd5_9 [0, 1, -3] = true := by decide +kernel
theorem subd5_9_99 : subd5_9 [0, 1, -2] = true := by decide +kernel
theorem subd5_9_100 : subd5_9 [0, 1, -1] = true := by decide +kernel
theorem subd5_9_101 : subd5_9 [0, 1, 0] = true := by decide +kernel
theorem subd5_9_102 : subd5_9 [0, 1, 1] = true := by decide +kernel
theorem subd5_9_103 : subd5_9 [0, 1, 2] = true := by decide +kernel
theorem subd5_9_104 : subd5_9 [0, 1, 3] = true := by decide +kernel
theorem subd5_9_105 : subd5_9 [0, 1, 4] = true := by decide +kernel
theorem subd5_9_106 : subd5_9 [0, 1, 5] = true := by decide +kernel
theorem subd5_9_107 : subd5_9 [0, 1, 6] = true := by decide +kernel
theorem subd5_9_108 : subd5_9 [0, 1, 7] = true := by decide +kernel
theorem subd5_9_109 : subd5_9 [0, 1, 8] = true := by decide +kernel
theorem subd5_9_110 : subd5_9 [0, 2] = true := by decide +kernel
theorem subd5_9_111 : subd5_9 [1, -3] = true := by decide +kernel
theorem subd5_9_112 : subd5_9 [1, -2] = true := by decide +kernel
theorem subd5_9_113 : subd5_9 [1, -1, -8] = true := by decide +kernel
theorem subd5_9_114 : subd5_9 [1, -1, -7] = true := by decide +kernel
theorem subd5_9_115 : subd5_9 [1, -1, -6] = true := by decide +kernel
theorem subd5_9_116 : subd5_9 [1, -1, -5] = true := by decide +kernel
theorem subd5_9_117 : subd5_9 [1, -1, -4] = true := by decide +kernel
theorem subd5_9_118 : subd5_9 [1, -1, -3] = true := by decide +kernel
theorem subd5_9_119 : subd5_9 [1, -1, -2] = true := by decide +kernel
theorem subd5_9_120 : subd5_9 [1, -1, -1] = true := by decide +kernel
theorem subd5_9_121 : subd5_9 [1, -1, 0] = true := by decide +kernel
theorem subd5_9_122 : subd5_9 [1, -1, 1] = true := by decide +kernel
theorem subd5_9_123 : subd5_9 [1, -1, 2] = true := by decide +kernel
theorem subd5_9_124 : subd5_9 [1, -1, 3] = true := by decide +kernel
theorem subd5_9_125 : subd5_9 [1, -1, 4] = true := by decide +kernel
theorem subd5_9_126 : subd5_9 [1, -1, 5] = true := by decide +kernel
theorem subd5_9_127 : subd5_9 [1, -1, 6] = true := by decide +kernel
theorem sbd5_9_3 : ∀ q ∈ blkd5_9_3, subd5_9 q = true := by
  unfold blkd5_9_3
  exact List.forall_mem_cons.2 ⟨subd5_9_96, List.forall_mem_cons.2 ⟨subd5_9_97, List.forall_mem_cons.2 ⟨subd5_9_98, List.forall_mem_cons.2 ⟨subd5_9_99, List.forall_mem_cons.2 ⟨subd5_9_100, List.forall_mem_cons.2 ⟨subd5_9_101, List.forall_mem_cons.2 ⟨subd5_9_102, List.forall_mem_cons.2 ⟨subd5_9_103, List.forall_mem_cons.2 ⟨subd5_9_104, List.forall_mem_cons.2 ⟨subd5_9_105, List.forall_mem_cons.2 ⟨subd5_9_106, List.forall_mem_cons.2 ⟨subd5_9_107, List.forall_mem_cons.2 ⟨subd5_9_108, List.forall_mem_cons.2 ⟨subd5_9_109, List.forall_mem_cons.2 ⟨subd5_9_110, List.forall_mem_cons.2 ⟨subd5_9_111, List.forall_mem_cons.2 ⟨subd5_9_112, List.forall_mem_cons.2 ⟨subd5_9_113, List.forall_mem_cons.2 ⟨subd5_9_114, List.forall_mem_cons.2 ⟨subd5_9_115, List.forall_mem_cons.2 ⟨subd5_9_116, List.forall_mem_cons.2 ⟨subd5_9_117, List.forall_mem_cons.2 ⟨subd5_9_118, List.forall_mem_cons.2 ⟨subd5_9_119, List.forall_mem_cons.2 ⟨subd5_9_120, List.forall_mem_cons.2 ⟨subd5_9_121, List.forall_mem_cons.2 ⟨subd5_9_122, List.forall_mem_cons.2 ⟨subd5_9_123, List.forall_mem_cons.2 ⟨subd5_9_124, List.forall_mem_cons.2 ⟨subd5_9_125, List.forall_mem_cons.2 ⟨subd5_9_126, List.forall_mem_cons.2 ⟨subd5_9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_9_128 : subd5_9 [1, -1, 7] = true := by decide +kernel
theorem subd5_9_129 : subd5_9 [1, 0, -9] = true := by decide +kernel
theorem subd5_9_130 : subd5_9 [1, 0, -8] = true := by decide +kernel
theorem subd5_9_131 : subd5_9 [1, 0, -7] = true := by decide +kernel
theorem subd5_9_132 : subd5_9 [1, 0, -6] = true := by decide +kernel
theorem subd5_9_133 : subd5_9 [1, 0, -5] = true := by decide +kernel
theorem subd5_9_134 : subd5_9 [1, 0, -4] = true := by decide +kernel
theorem subd5_9_135 : subd5_9 [1, 0, -3] = true := by decide +kernel
theorem subd5_9_136 : subd5_9 [1, 0, -2] = true := by decide +kernel
theorem subd5_9_137 : subd5_9 [1, 0, -1] = true := by decide +kernel
theorem subd5_9_138 : subd5_9 [1, 0, 0] = true := by decide +kernel
theorem subd5_9_139 : subd5_9 [1, 0, 1] = true := by decide +kernel
theorem subd5_9_140 : subd5_9 [1, 0, 2] = true := by decide +kernel
theorem subd5_9_141 : subd5_9 [1, 0, 3] = true := by decide +kernel
theorem subd5_9_142 : subd5_9 [1, 0, 4] = true := by decide +kernel
theorem subd5_9_143 : subd5_9 [1, 0, 5] = true := by decide +kernel
theorem subd5_9_144 : subd5_9 [1, 0, 6] = true := by decide +kernel
theorem subd5_9_145 : subd5_9 [1, 0, 7] = true := by decide +kernel
theorem subd5_9_146 : subd5_9 [1, 0, 8] = true := by decide +kernel
theorem subd5_9_147 : subd5_9 [1, 1, -7] = true := by decide +kernel
theorem subd5_9_148 : subd5_9 [1, 1, -6] = true := by decide +kernel
theorem subd5_9_149 : subd5_9 [1, 1, -5] = true := by decide +kernel
theorem subd5_9_150 : subd5_9 [1, 1, -4] = true := by decide +kernel
theorem subd5_9_151 : subd5_9 [1, 1, -3] = true := by decide +kernel
theorem subd5_9_152 : subd5_9 [1, 1, -2] = true := by decide +kernel
theorem subd5_9_153 : subd5_9 [1, 1, -1] = true := by decide +kernel
theorem subd5_9_154 : subd5_9 [1, 1, 0] = true := by decide +kernel
theorem subd5_9_155 : subd5_9 [1, 1, 1] = true := by decide +kernel
theorem subd5_9_156 : subd5_9 [1, 1, 2] = true := by decide +kernel
theorem subd5_9_157 : subd5_9 [1, 1, 3] = true := by decide +kernel
theorem subd5_9_158 : subd5_9 [1, 1, 4] = true := by decide +kernel
theorem subd5_9_159 : subd5_9 [1, 1, 5] = true := by decide +kernel
theorem sbd5_9_4 : ∀ q ∈ blkd5_9_4, subd5_9 q = true := by
  unfold blkd5_9_4
  exact List.forall_mem_cons.2 ⟨subd5_9_128, List.forall_mem_cons.2 ⟨subd5_9_129, List.forall_mem_cons.2 ⟨subd5_9_130, List.forall_mem_cons.2 ⟨subd5_9_131, List.forall_mem_cons.2 ⟨subd5_9_132, List.forall_mem_cons.2 ⟨subd5_9_133, List.forall_mem_cons.2 ⟨subd5_9_134, List.forall_mem_cons.2 ⟨subd5_9_135, List.forall_mem_cons.2 ⟨subd5_9_136, List.forall_mem_cons.2 ⟨subd5_9_137, List.forall_mem_cons.2 ⟨subd5_9_138, List.forall_mem_cons.2 ⟨subd5_9_139, List.forall_mem_cons.2 ⟨subd5_9_140, List.forall_mem_cons.2 ⟨subd5_9_141, List.forall_mem_cons.2 ⟨subd5_9_142, List.forall_mem_cons.2 ⟨subd5_9_143, List.forall_mem_cons.2 ⟨subd5_9_144, List.forall_mem_cons.2 ⟨subd5_9_145, List.forall_mem_cons.2 ⟨subd5_9_146, List.forall_mem_cons.2 ⟨subd5_9_147, List.forall_mem_cons.2 ⟨subd5_9_148, List.forall_mem_cons.2 ⟨subd5_9_149, List.forall_mem_cons.2 ⟨subd5_9_150, List.forall_mem_cons.2 ⟨subd5_9_151, List.forall_mem_cons.2 ⟨subd5_9_152, List.forall_mem_cons.2 ⟨subd5_9_153, List.forall_mem_cons.2 ⟨subd5_9_154, List.forall_mem_cons.2 ⟨subd5_9_155, List.forall_mem_cons.2 ⟨subd5_9_156, List.forall_mem_cons.2 ⟨subd5_9_157, List.forall_mem_cons.2 ⟨subd5_9_158, List.forall_mem_cons.2 ⟨subd5_9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_9_160 : subd5_9 [1, 1, 6] = true := by decide +kernel
theorem subd5_9_161 : subd5_9 [1, 1, 7] = true := by decide +kernel
theorem subd5_9_162 : subd5_9 [2] = true := by decide +kernel
theorem sbd5_9_5 : ∀ q ∈ blkd5_9_5, subd5_9 q = true := by
  unfold blkd5_9_5
  exact List.forall_mem_cons.2 ⟨subd5_9_160, List.forall_mem_cons.2 ⟨subd5_9_161, List.forall_mem_cons.2 ⟨subd5_9_162, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd5_10 : ldCheck G d5_10.U d5_10.ms ldd5_10 = true := by decide +kernel
theorem pre_okd5_10 : subPre G cell5 d5_10 = true := by decide +kernel
theorem subd5_10_0 : subd5_10 [-3] = true := by decide +kernel
theorem subd5_10_1 : subd5_10 [-2, -2] = true := by decide +kernel
theorem subd5_10_2 : subd5_10 [-2, -1] = true := by decide +kernel
theorem subd5_10_3 : subd5_10 [-2, 0] = true := by decide +kernel
theorem subd5_10_4 : subd5_10 [-2, 1] = true := by decide +kernel
theorem subd5_10_5 : subd5_10 [-2, 2] = true := by decide +kernel
theorem subd5_10_6 : subd5_10 [-2, 3] = true := by decide +kernel
theorem subd5_10_7 : subd5_10 [-1, -3] = true := by decide +kernel
theorem subd5_10_8 : subd5_10 [-1, -2] = true := by decide +kernel
theorem subd5_10_9 : subd5_10 [-1, -1] = true := by decide +kernel
theorem subd5_10_10 : subd5_10 [-1, 0] = true := by decide +kernel
theorem subd5_10_11 : subd5_10 [-1, 1] = true := by decide +kernel
theorem subd5_10_12 : subd5_10 [-1, 2] = true := by decide +kernel
theorem subd5_10_13 : subd5_10 [-1, 3] = true := by decide +kernel
theorem subd5_10_14 : subd5_10 [0, -4] = true := by decide +kernel
theorem subd5_10_15 : subd5_10 [0, -3] = true := by decide +kernel
theorem subd5_10_16 : subd5_10 [0, -2] = true := by decide +kernel
theorem subd5_10_17 : subd5_10 [0, -1] = true := by decide +kernel
theorem subd5_10_18 : subd5_10 [0, 0] = true := by decide +kernel
theorem subd5_10_19 : subd5_10 [0, 1] = true := by decide +kernel
theorem subd5_10_20 : subd5_10 [0, 2] = true := by decide +kernel
theorem subd5_10_21 : subd5_10 [0, 3] = true := by decide +kernel
theorem subd5_10_22 : subd5_10 [1, -4] = true := by decide +kernel
theorem subd5_10_23 : subd5_10 [1, -3] = true := by decide +kernel
theorem subd5_10_24 : subd5_10 [1, -2] = true := by decide +kernel
theorem subd5_10_25 : subd5_10 [1, -1] = true := by decide +kernel
theorem subd5_10_26 : subd5_10 [1, 0] = true := by decide +kernel
theorem subd5_10_27 : subd5_10 [1, 1] = true := by decide +kernel
theorem subd5_10_28 : subd5_10 [1, 2] = true := by decide +kernel
theorem subd5_10_29 : subd5_10 [2, -4] = true := by decide +kernel
theorem subd5_10_30 : subd5_10 [2, -3] = true := by decide +kernel
theorem subd5_10_31 : subd5_10 [2, -2] = true := by decide +kernel
theorem sbd5_10_0 : ∀ q ∈ blkd5_10_0, subd5_10 q = true := by
  unfold blkd5_10_0
  exact List.forall_mem_cons.2 ⟨subd5_10_0, List.forall_mem_cons.2 ⟨subd5_10_1, List.forall_mem_cons.2 ⟨subd5_10_2, List.forall_mem_cons.2 ⟨subd5_10_3, List.forall_mem_cons.2 ⟨subd5_10_4, List.forall_mem_cons.2 ⟨subd5_10_5, List.forall_mem_cons.2 ⟨subd5_10_6, List.forall_mem_cons.2 ⟨subd5_10_7, List.forall_mem_cons.2 ⟨subd5_10_8, List.forall_mem_cons.2 ⟨subd5_10_9, List.forall_mem_cons.2 ⟨subd5_10_10, List.forall_mem_cons.2 ⟨subd5_10_11, List.forall_mem_cons.2 ⟨subd5_10_12, List.forall_mem_cons.2 ⟨subd5_10_13, List.forall_mem_cons.2 ⟨subd5_10_14, List.forall_mem_cons.2 ⟨subd5_10_15, List.forall_mem_cons.2 ⟨subd5_10_16, List.forall_mem_cons.2 ⟨subd5_10_17, List.forall_mem_cons.2 ⟨subd5_10_18, List.forall_mem_cons.2 ⟨subd5_10_19, List.forall_mem_cons.2 ⟨subd5_10_20, List.forall_mem_cons.2 ⟨subd5_10_21, List.forall_mem_cons.2 ⟨subd5_10_22, List.forall_mem_cons.2 ⟨subd5_10_23, List.forall_mem_cons.2 ⟨subd5_10_24, List.forall_mem_cons.2 ⟨subd5_10_25, List.forall_mem_cons.2 ⟨subd5_10_26, List.forall_mem_cons.2 ⟨subd5_10_27, List.forall_mem_cons.2 ⟨subd5_10_28, List.forall_mem_cons.2 ⟨subd5_10_29, List.forall_mem_cons.2 ⟨subd5_10_30, List.forall_mem_cons.2 ⟨subd5_10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_10_32 : subd5_10 [2, -1] = true := by decide +kernel
theorem subd5_10_33 : subd5_10 [2, 0] = true := by decide +kernel
theorem subd5_10_34 : subd5_10 [2, 1] = true := by decide +kernel
theorem subd5_10_35 : subd5_10 [3] = true := by decide +kernel
theorem sbd5_10_1 : ∀ q ∈ blkd5_10_1, subd5_10 q = true := by
  unfold blkd5_10_1
  exact List.forall_mem_cons.2 ⟨subd5_10_32, List.forall_mem_cons.2 ⟨subd5_10_33, List.forall_mem_cons.2 ⟨subd5_10_34, List.forall_mem_cons.2 ⟨subd5_10_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd5_11 : ldCheck G d5_11.U d5_11.ms ldd5_11 = true := by decide +kernel
theorem pre_okd5_11 : subPre G cell5 d5_11 = true := by decide +kernel
theorem subd5_11_0 : subd5_11 [-2, -2] = true := by decide +kernel
theorem subd5_11_1 : subd5_11 [-2, -1] = true := by decide +kernel
theorem subd5_11_2 : subd5_11 [-2, 0] = true := by decide +kernel
theorem subd5_11_3 : subd5_11 [-2, 1] = true := by decide +kernel
theorem subd5_11_4 : subd5_11 [-2, 2] = true := by decide +kernel
theorem subd5_11_5 : subd5_11 [-2, 3] = true := by decide +kernel
theorem subd5_11_6 : subd5_11 [-1, -3] = true := by decide +kernel
theorem subd5_11_7 : subd5_11 [-1, -2] = true := by decide +kernel
theorem subd5_11_8 : subd5_11 [-1, -1] = true := by decide +kernel
theorem subd5_11_9 : subd5_11 [-1, 0] = true := by decide +kernel
theorem subd5_11_10 : subd5_11 [-1, 1] = true := by decide +kernel
theorem subd5_11_11 : subd5_11 [-1, 2] = true := by decide +kernel
theorem subd5_11_12 : subd5_11 [-1, 3] = true := by decide +kernel
theorem subd5_11_13 : subd5_11 [0, -4] = true := by decide +kernel
theorem subd5_11_14 : subd5_11 [0, -3] = true := by decide +kernel
theorem subd5_11_15 : subd5_11 [0, -2] = true := by decide +kernel
theorem subd5_11_16 : subd5_11 [0, -1] = true := by decide +kernel
theorem subd5_11_17 : subd5_11 [0, 0] = true := by decide +kernel
theorem subd5_11_18 : subd5_11 [0, 1] = true := by decide +kernel
theorem subd5_11_19 : subd5_11 [0, 2] = true := by decide +kernel
theorem subd5_11_20 : subd5_11 [0, 3] = true := by decide +kernel
theorem subd5_11_21 : subd5_11 [1, -4] = true := by decide +kernel
theorem subd5_11_22 : subd5_11 [1, -3] = true := by decide +kernel
theorem subd5_11_23 : subd5_11 [1, -2] = true := by decide +kernel
theorem subd5_11_24 : subd5_11 [1, -1] = true := by decide +kernel
theorem subd5_11_25 : subd5_11 [1, 0] = true := by decide +kernel
theorem subd5_11_26 : subd5_11 [1, 1] = true := by decide +kernel
theorem subd5_11_27 : subd5_11 [1, 2] = true := by decide +kernel
theorem subd5_11_28 : subd5_11 [2, -4] = true := by decide +kernel
theorem subd5_11_29 : subd5_11 [2, -3] = true := by decide +kernel
theorem subd5_11_30 : subd5_11 [2, -2] = true := by decide +kernel
theorem subd5_11_31 : subd5_11 [2, -1] = true := by decide +kernel
theorem sbd5_11_0 : ∀ q ∈ blkd5_11_0, subd5_11 q = true := by
  unfold blkd5_11_0
  exact List.forall_mem_cons.2 ⟨subd5_11_0, List.forall_mem_cons.2 ⟨subd5_11_1, List.forall_mem_cons.2 ⟨subd5_11_2, List.forall_mem_cons.2 ⟨subd5_11_3, List.forall_mem_cons.2 ⟨subd5_11_4, List.forall_mem_cons.2 ⟨subd5_11_5, List.forall_mem_cons.2 ⟨subd5_11_6, List.forall_mem_cons.2 ⟨subd5_11_7, List.forall_mem_cons.2 ⟨subd5_11_8, List.forall_mem_cons.2 ⟨subd5_11_9, List.forall_mem_cons.2 ⟨subd5_11_10, List.forall_mem_cons.2 ⟨subd5_11_11, List.forall_mem_cons.2 ⟨subd5_11_12, List.forall_mem_cons.2 ⟨subd5_11_13, List.forall_mem_cons.2 ⟨subd5_11_14, List.forall_mem_cons.2 ⟨subd5_11_15, List.forall_mem_cons.2 ⟨subd5_11_16, List.forall_mem_cons.2 ⟨subd5_11_17, List.forall_mem_cons.2 ⟨subd5_11_18, List.forall_mem_cons.2 ⟨subd5_11_19, List.forall_mem_cons.2 ⟨subd5_11_20, List.forall_mem_cons.2 ⟨subd5_11_21, List.forall_mem_cons.2 ⟨subd5_11_22, List.forall_mem_cons.2 ⟨subd5_11_23, List.forall_mem_cons.2 ⟨subd5_11_24, List.forall_mem_cons.2 ⟨subd5_11_25, List.forall_mem_cons.2 ⟨subd5_11_26, List.forall_mem_cons.2 ⟨subd5_11_27, List.forall_mem_cons.2 ⟨subd5_11_28, List.forall_mem_cons.2 ⟨subd5_11_29, List.forall_mem_cons.2 ⟨subd5_11_30, List.forall_mem_cons.2 ⟨subd5_11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_11_32 : subd5_11 [2, 0] = true := by decide +kernel
theorem subd5_11_33 : subd5_11 [2, 1] = true := by decide +kernel
theorem sbd5_11_1 : ∀ q ∈ blkd5_11_1, subd5_11 q = true := by
  unfold blkd5_11_1
  exact List.forall_mem_cons.2 ⟨subd5_11_32, List.forall_mem_cons.2 ⟨subd5_11_33, List.forall_mem_nil _⟩⟩

end ReflectZphi.Data.Cert5.C124
