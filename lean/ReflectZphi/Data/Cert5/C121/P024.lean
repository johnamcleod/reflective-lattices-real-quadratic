import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_0 : subd9_1 [-2, -2] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-2, -1] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-2, 0] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-2, 1] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-1, -1, -7] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-1, -1, -6] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-1, -1, -5] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-1, -1, -4] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-1, -1, -3] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-1, -1, -2] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-1, -1, -1] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-1, -1, 0] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-1, -1, 1] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [-1, -1, 2] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [-1, -1, 3] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [-1, -1, 4] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [-1, -1, 5] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [-1, -1, 6] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [-1, -1, 7] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [-1, -1, 8] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [-1, 0, -9] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [-1, 0, -8] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [-1, 0, -7] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [-1, 0, -6] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [-1, 0, -5] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [-1, 0, -4] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [-1, 0, -3] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [-1, 0, -2] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [-1, 0, -1] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [-1, 0, 0] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_32 : subd9_1 [-1, 0, 1] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [-1, 0, 2] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [-1, 0, 3] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [-1, 0, 4] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [-1, 0, 5] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [-1, 0, 6] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [-1, 0, 7] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [-1, 0, 8] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [-1, 0, 9] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [-1, 1, -8] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [-1, 1, -7] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [-1, 1, -6] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [-1, 1, -5] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [-1, 1, -4] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [-1, 1, -3] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [-1, 1, -2] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [-1, 1, -1] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [-1, 1, 0] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [-1, 1, 1] = true := by decide +kernel
theorem subd9_1_51 : subd9_1 [-1, 1, 2] = true := by decide +kernel
theorem subd9_1_52 : subd9_1 [-1, 1, 3] = true := by decide +kernel
theorem subd9_1_53 : subd9_1 [-1, 1, 4] = true := by decide +kernel
theorem subd9_1_54 : subd9_1 [-1, 1, 5] = true := by decide +kernel
theorem subd9_1_55 : subd9_1 [-1, 1, 6] = true := by decide +kernel
theorem subd9_1_56 : subd9_1 [-1, 1, 7] = true := by decide +kernel
theorem subd9_1_57 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_58 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_59 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_60 : subd9_1 [0, -1, -9] = true := by decide +kernel
theorem subd9_1_61 : subd9_1 [0, -1, -8] = true := by decide +kernel
theorem subd9_1_62 : subd9_1 [0, -1, -7] = true := by decide +kernel
theorem subd9_1_63 : subd9_1 [0, -1, -6] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_cons.2 ⟨subd9_1_51, List.forall_mem_cons.2 ⟨subd9_1_52, List.forall_mem_cons.2 ⟨subd9_1_53, List.forall_mem_cons.2 ⟨subd9_1_54, List.forall_mem_cons.2 ⟨subd9_1_55, List.forall_mem_cons.2 ⟨subd9_1_56, List.forall_mem_cons.2 ⟨subd9_1_57, List.forall_mem_cons.2 ⟨subd9_1_58, List.forall_mem_cons.2 ⟨subd9_1_59, List.forall_mem_cons.2 ⟨subd9_1_60, List.forall_mem_cons.2 ⟨subd9_1_61, List.forall_mem_cons.2 ⟨subd9_1_62, List.forall_mem_cons.2 ⟨subd9_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_64 : subd9_1 [0, -1, -5] = true := by decide +kernel
theorem subd9_1_65 : subd9_1 [0, -1, -4] = true := by decide +kernel
theorem subd9_1_66 : subd9_1 [0, -1, -3] = true := by decide +kernel
theorem subd9_1_67 : subd9_1 [0, -1, -2] = true := by decide +kernel
theorem subd9_1_68 : subd9_1 [0, -1, -1] = true := by decide +kernel
theorem subd9_1_69 : subd9_1 [0, -1, 0] = true := by decide +kernel
theorem subd9_1_70 : subd9_1 [0, -1, 1] = true := by decide +kernel
theorem subd9_1_71 : subd9_1 [0, -1, 2] = true := by decide +kernel
theorem subd9_1_72 : subd9_1 [0, -1, 3] = true := by decide +kernel
theorem subd9_1_73 : subd9_1 [0, -1, 4] = true := by decide +kernel
theorem subd9_1_74 : subd9_1 [0, -1, 5] = true := by decide +kernel
theorem subd9_1_75 : subd9_1 [0, -1, 6] = true := by decide +kernel
theorem subd9_1_76 : subd9_1 [0, -1, 7] = true := by decide +kernel
theorem subd9_1_77 : subd9_1 [0, -1, 8] = true := by decide +kernel
theorem subd9_1_78 : subd9_1 [0, -1, 9] = true := by decide +kernel
theorem subd9_1_79 : subd9_1 [0, 0, -10] = true := by decide +kernel
theorem subd9_1_80 : subd9_1 [0, 0, -9] = true := by decide +kernel
theorem subd9_1_81 : subd9_1 [0, 0, -8] = true := by decide +kernel
theorem subd9_1_82 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_83 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_84 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_85 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_86 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_87 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_88 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_89 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_90 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_91 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_92 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_93 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_94 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem subd9_1_95 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem sbd9_1_2 : ∀ q ∈ blkd9_1_2, subd9_1 q = true := by
  unfold blkd9_1_2
  exact List.forall_mem_cons.2 ⟨subd9_1_64, List.forall_mem_cons.2 ⟨subd9_1_65, List.forall_mem_cons.2 ⟨subd9_1_66, List.forall_mem_cons.2 ⟨subd9_1_67, List.forall_mem_cons.2 ⟨subd9_1_68, List.forall_mem_cons.2 ⟨subd9_1_69, List.forall_mem_cons.2 ⟨subd9_1_70, List.forall_mem_cons.2 ⟨subd9_1_71, List.forall_mem_cons.2 ⟨subd9_1_72, List.forall_mem_cons.2 ⟨subd9_1_73, List.forall_mem_cons.2 ⟨subd9_1_74, List.forall_mem_cons.2 ⟨subd9_1_75, List.forall_mem_cons.2 ⟨subd9_1_76, List.forall_mem_cons.2 ⟨subd9_1_77, List.forall_mem_cons.2 ⟨subd9_1_78, List.forall_mem_cons.2 ⟨subd9_1_79, List.forall_mem_cons.2 ⟨subd9_1_80, List.forall_mem_cons.2 ⟨subd9_1_81, List.forall_mem_cons.2 ⟨subd9_1_82, List.forall_mem_cons.2 ⟨subd9_1_83, List.forall_mem_cons.2 ⟨subd9_1_84, List.forall_mem_cons.2 ⟨subd9_1_85, List.forall_mem_cons.2 ⟨subd9_1_86, List.forall_mem_cons.2 ⟨subd9_1_87, List.forall_mem_cons.2 ⟨subd9_1_88, List.forall_mem_cons.2 ⟨subd9_1_89, List.forall_mem_cons.2 ⟨subd9_1_90, List.forall_mem_cons.2 ⟨subd9_1_91, List.forall_mem_cons.2 ⟨subd9_1_92, List.forall_mem_cons.2 ⟨subd9_1_93, List.forall_mem_cons.2 ⟨subd9_1_94, List.forall_mem_cons.2 ⟨subd9_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_96 : subd9_1 [0, 0, 7] = true := by decide +kernel
theorem subd9_1_97 : subd9_1 [0, 0, 8] = true := by decide +kernel
theorem subd9_1_98 : subd9_1 [0, 0, 9] = true := by decide +kernel
theorem subd9_1_99 : subd9_1 [0, 1, -10] = true := by decide +kernel
theorem subd9_1_100 : subd9_1 [0, 1, -9] = true := by decide +kernel
theorem subd9_1_101 : subd9_1 [0, 1, -8] = true := by decide +kernel
theorem subd9_1_102 : subd9_1 [0, 1, -7] = true := by decide +kernel
theorem subd9_1_103 : subd9_1 [0, 1, -6] = true := by decide +kernel
theorem subd9_1_104 : subd9_1 [0, 1, -5] = true := by decide +kernel
theorem subd9_1_105 : subd9_1 [0, 1, -4] = true := by decide +kernel
theorem subd9_1_106 : subd9_1 [0, 1, -3] = true := by decide +kernel
theorem subd9_1_107 : subd9_1 [0, 1, -2] = true := by decide +kernel
theorem subd9_1_108 : subd9_1 [0, 1, -1] = true := by decide +kernel
theorem subd9_1_109 : subd9_1 [0, 1, 0] = true := by decide +kernel
theorem subd9_1_110 : subd9_1 [0, 1, 1] = true := by decide +kernel
theorem subd9_1_111 : subd9_1 [0, 1, 2] = true := by decide +kernel
theorem subd9_1_112 : subd9_1 [0, 1, 3] = true := by decide +kernel
theorem subd9_1_113 : subd9_1 [0, 1, 4] = true := by decide +kernel
theorem subd9_1_114 : subd9_1 [0, 1, 5] = true := by decide +kernel
theorem subd9_1_115 : subd9_1 [0, 1, 6] = true := by decide +kernel
theorem subd9_1_116 : subd9_1 [0, 1, 7] = true := by decide +kernel
theorem subd9_1_117 : subd9_1 [0, 1, 8] = true := by decide +kernel
theorem subd9_1_118 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_119 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_120 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_121 : subd9_1 [1, -1, -8] = true := by decide +kernel
theorem subd9_1_122 : subd9_1 [1, -1, -7] = true := by decide +kernel
theorem subd9_1_123 : subd9_1 [1, -1, -6] = true := by decide +kernel
theorem subd9_1_124 : subd9_1 [1, -1, -5] = true := by decide +kernel
theorem subd9_1_125 : subd9_1 [1, -1, -4] = true := by decide +kernel
theorem subd9_1_126 : subd9_1 [1, -1, -3] = true := by decide +kernel
theorem subd9_1_127 : subd9_1 [1, -1, -2] = true := by decide +kernel
theorem sbd9_1_3 : ∀ q ∈ blkd9_1_3, subd9_1 q = true := by
  unfold blkd9_1_3
  exact List.forall_mem_cons.2 ⟨subd9_1_96, List.forall_mem_cons.2 ⟨subd9_1_97, List.forall_mem_cons.2 ⟨subd9_1_98, List.forall_mem_cons.2 ⟨subd9_1_99, List.forall_mem_cons.2 ⟨subd9_1_100, List.forall_mem_cons.2 ⟨subd9_1_101, List.forall_mem_cons.2 ⟨subd9_1_102, List.forall_mem_cons.2 ⟨subd9_1_103, List.forall_mem_cons.2 ⟨subd9_1_104, List.forall_mem_cons.2 ⟨subd9_1_105, List.forall_mem_cons.2 ⟨subd9_1_106, List.forall_mem_cons.2 ⟨subd9_1_107, List.forall_mem_cons.2 ⟨subd9_1_108, List.forall_mem_cons.2 ⟨subd9_1_109, List.forall_mem_cons.2 ⟨subd9_1_110, List.forall_mem_cons.2 ⟨subd9_1_111, List.forall_mem_cons.2 ⟨subd9_1_112, List.forall_mem_cons.2 ⟨subd9_1_113, List.forall_mem_cons.2 ⟨subd9_1_114, List.forall_mem_cons.2 ⟨subd9_1_115, List.forall_mem_cons.2 ⟨subd9_1_116, List.forall_mem_cons.2 ⟨subd9_1_117, List.forall_mem_cons.2 ⟨subd9_1_118, List.forall_mem_cons.2 ⟨subd9_1_119, List.forall_mem_cons.2 ⟨subd9_1_120, List.forall_mem_cons.2 ⟨subd9_1_121, List.forall_mem_cons.2 ⟨subd9_1_122, List.forall_mem_cons.2 ⟨subd9_1_123, List.forall_mem_cons.2 ⟨subd9_1_124, List.forall_mem_cons.2 ⟨subd9_1_125, List.forall_mem_cons.2 ⟨subd9_1_126, List.forall_mem_cons.2 ⟨subd9_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_128 : subd9_1 [1, -1, -1] = true := by decide +kernel
theorem subd9_1_129 : subd9_1 [1, -1, 0] = true := by decide +kernel
theorem subd9_1_130 : subd9_1 [1, -1, 1] = true := by decide +kernel
theorem subd9_1_131 : subd9_1 [1, -1, 2] = true := by decide +kernel
theorem subd9_1_132 : subd9_1 [1, -1, 3] = true := by decide +kernel
theorem subd9_1_133 : subd9_1 [1, -1, 4] = true := by decide +kernel
theorem subd9_1_134 : subd9_1 [1, -1, 5] = true := by decide +kernel
theorem subd9_1_135 : subd9_1 [1, -1, 6] = true := by decide +kernel
theorem subd9_1_136 : subd9_1 [1, -1, 7] = true := by decide +kernel
theorem subd9_1_137 : subd9_1 [1, 0, -10] = true := by decide +kernel
theorem subd9_1_138 : subd9_1 [1, 0, -9] = true := by decide +kernel
theorem subd9_1_139 : subd9_1 [1, 0, -8] = true := by decide +kernel
theorem subd9_1_140 : subd9_1 [1, 0, -7] = true := by decide +kernel
theorem subd9_1_141 : subd9_1 [1, 0, -6] = true := by decide +kernel
theorem subd9_1_142 : subd9_1 [1, 0, -5] = true := by decide +kernel
theorem subd9_1_143 : subd9_1 [1, 0, -4] = true := by decide +kernel
theorem subd9_1_144 : subd9_1 [1, 0, -3] = true := by decide +kernel
theorem subd9_1_145 : subd9_1 [1, 0, -2] = true := by decide +kernel
theorem subd9_1_146 : subd9_1 [1, 0, -1] = true := by decide +kernel
theorem subd9_1_147 : subd9_1 [1, 0, 0] = true := by decide +kernel
theorem subd9_1_148 : subd9_1 [1, 0, 1] = true := by decide +kernel
theorem subd9_1_149 : subd9_1 [1, 0, 2] = true := by decide +kernel
theorem subd9_1_150 : subd9_1 [1, 0, 3] = true := by decide +kernel
theorem subd9_1_151 : subd9_1 [1, 0, 4] = true := by decide +kernel
theorem subd9_1_152 : subd9_1 [1, 0, 5] = true := by decide +kernel
theorem subd9_1_153 : subd9_1 [1, 0, 6] = true := by decide +kernel
theorem subd9_1_154 : subd9_1 [1, 0, 7] = true := by decide +kernel
theorem subd9_1_155 : subd9_1 [1, 0, 8] = true := by decide +kernel
theorem subd9_1_156 : subd9_1 [1, 1, -9] = true := by decide +kernel
theorem subd9_1_157 : subd9_1 [1, 1, -8] = true := by decide +kernel
theorem subd9_1_158 : subd9_1 [1, 1, -7] = true := by decide +kernel
theorem subd9_1_159 : subd9_1 [1, 1, -6] = true := by decide +kernel
theorem sbd9_1_4 : ∀ q ∈ blkd9_1_4, subd9_1 q = true := by
  unfold blkd9_1_4
  exact List.forall_mem_cons.2 ⟨subd9_1_128, List.forall_mem_cons.2 ⟨subd9_1_129, List.forall_mem_cons.2 ⟨subd9_1_130, List.forall_mem_cons.2 ⟨subd9_1_131, List.forall_mem_cons.2 ⟨subd9_1_132, List.forall_mem_cons.2 ⟨subd9_1_133, List.forall_mem_cons.2 ⟨subd9_1_134, List.forall_mem_cons.2 ⟨subd9_1_135, List.forall_mem_cons.2 ⟨subd9_1_136, List.forall_mem_cons.2 ⟨subd9_1_137, List.forall_mem_cons.2 ⟨subd9_1_138, List.forall_mem_cons.2 ⟨subd9_1_139, List.forall_mem_cons.2 ⟨subd9_1_140, List.forall_mem_cons.2 ⟨subd9_1_141, List.forall_mem_cons.2 ⟨subd9_1_142, List.forall_mem_cons.2 ⟨subd9_1_143, List.forall_mem_cons.2 ⟨subd9_1_144, List.forall_mem_cons.2 ⟨subd9_1_145, List.forall_mem_cons.2 ⟨subd9_1_146, List.forall_mem_cons.2 ⟨subd9_1_147, List.forall_mem_cons.2 ⟨subd9_1_148, List.forall_mem_cons.2 ⟨subd9_1_149, List.forall_mem_cons.2 ⟨subd9_1_150, List.forall_mem_cons.2 ⟨subd9_1_151, List.forall_mem_cons.2 ⟨subd9_1_152, List.forall_mem_cons.2 ⟨subd9_1_153, List.forall_mem_cons.2 ⟨subd9_1_154, List.forall_mem_cons.2 ⟨subd9_1_155, List.forall_mem_cons.2 ⟨subd9_1_156, List.forall_mem_cons.2 ⟨subd9_1_157, List.forall_mem_cons.2 ⟨subd9_1_158, List.forall_mem_cons.2 ⟨subd9_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_160 : subd9_1 [1, 1, -5] = true := by decide +kernel
theorem subd9_1_161 : subd9_1 [1, 1, -4] = true := by decide +kernel
theorem subd9_1_162 : subd9_1 [1, 1, -3] = true := by decide +kernel
theorem subd9_1_163 : subd9_1 [1, 1, -2] = true := by decide +kernel
theorem subd9_1_164 : subd9_1 [1, 1, -1] = true := by decide +kernel
theorem subd9_1_165 : subd9_1 [1, 1, 0] = true := by decide +kernel
theorem subd9_1_166 : subd9_1 [1, 1, 1] = true := by decide +kernel
theorem subd9_1_167 : subd9_1 [1, 1, 2] = true := by decide +kernel
theorem subd9_1_168 : subd9_1 [1, 1, 3] = true := by decide +kernel
theorem subd9_1_169 : subd9_1 [1, 1, 4] = true := by decide +kernel
theorem subd9_1_170 : subd9_1 [1, 1, 5] = true := by decide +kernel
theorem subd9_1_171 : subd9_1 [1, 1, 6] = true := by decide +kernel
theorem subd9_1_172 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_173 : subd9_1 [2, -2] = true := by decide +kernel
theorem subd9_1_174 : subd9_1 [2, -1] = true := by decide +kernel
theorem subd9_1_175 : subd9_1 [2, 0] = true := by decide +kernel
theorem subd9_1_176 : subd9_1 [2, 1] = true := by decide +kernel
theorem sbd9_1_5 : ∀ q ∈ blkd9_1_5, subd9_1 q = true := by
  unfold blkd9_1_5
  exact List.forall_mem_cons.2 ⟨subd9_1_160, List.forall_mem_cons.2 ⟨subd9_1_161, List.forall_mem_cons.2 ⟨subd9_1_162, List.forall_mem_cons.2 ⟨subd9_1_163, List.forall_mem_cons.2 ⟨subd9_1_164, List.forall_mem_cons.2 ⟨subd9_1_165, List.forall_mem_cons.2 ⟨subd9_1_166, List.forall_mem_cons.2 ⟨subd9_1_167, List.forall_mem_cons.2 ⟨subd9_1_168, List.forall_mem_cons.2 ⟨subd9_1_169, List.forall_mem_cons.2 ⟨subd9_1_170, List.forall_mem_cons.2 ⟨subd9_1_171, List.forall_mem_cons.2 ⟨subd9_1_172, List.forall_mem_cons.2 ⟨subd9_1_173, List.forall_mem_cons.2 ⟨subd9_1_174, List.forall_mem_cons.2 ⟨subd9_1_175, List.forall_mem_cons.2 ⟨subd9_1_176, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-8] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-7, -4] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-7, -3] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-7, -2] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-7, -1] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-7, 0] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-7, 1] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-7, 2] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-7, 3] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-7, 4] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-7, 5] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-6, -5] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-6, -4] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-6, -3] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [-6, -2] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [-6, -1] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [-6, 0] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [-6, 1] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [-6, 2] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [-6, 3] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [-6, 4] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [-6, 5] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [-6, 6] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [-6, 7] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [-5, -6] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [-5, -5] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [-5, -4] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [-5, -3] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [-5, -2] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [-5, -1] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [-5, 0] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [-5, 1] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_32 : subd9_2 [-5, 2] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [-5, 3] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [-5, 4] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [-5, 5] = true := by decide +kernel
theorem subd9_2_36 : subd9_2 [-5, 6] = true := by decide +kernel
theorem subd9_2_37 : subd9_2 [-5, 7] = true := by decide +kernel
theorem subd9_2_38 : subd9_2 [-4, -7] = true := by decide +kernel
theorem subd9_2_39 : subd9_2 [-4, -6] = true := by decide +kernel
theorem subd9_2_40 : subd9_2 [-4, -5] = true := by decide +kernel
theorem subd9_2_41 : subd9_2 [-4, -4] = true := by decide +kernel
theorem subd9_2_42 : subd9_2 [-4, -3] = true := by decide +kernel
theorem subd9_2_43 : subd9_2 [-4, -2] = true := by decide +kernel
theorem subd9_2_44 : subd9_2 [-4, -1] = true := by decide +kernel
theorem subd9_2_45 : subd9_2 [-4, 0, -8] = true := by decide +kernel
theorem subd9_2_46 : subd9_2 [-4, 0, -7] = true := by decide +kernel
theorem subd9_2_47 : subd9_2 [-4, 0, -6] = true := by decide +kernel
theorem subd9_2_48 : subd9_2 [-4, 0, -5] = true := by decide +kernel
theorem subd9_2_49 : subd9_2 [-4, 0, -4] = true := by decide +kernel
theorem subd9_2_50 : subd9_2 [-4, 0, -3] = true := by decide +kernel
theorem subd9_2_51 : subd9_2 [-4, 0, -2] = true := by decide +kernel
theorem subd9_2_52 : subd9_2 [-4, 0, -1] = true := by decide +kernel
theorem subd9_2_53 : subd9_2 [-4, 0, 0] = true := by decide +kernel
theorem subd9_2_54 : subd9_2 [-4, 0, 1] = true := by decide +kernel
theorem subd9_2_55 : subd9_2 [-4, 0, 2] = true := by decide +kernel
theorem subd9_2_56 : subd9_2 [-4, 0, 3] = true := by decide +kernel
theorem subd9_2_57 : subd9_2 [-4, 0, 4] = true := by decide +kernel
theorem subd9_2_58 : subd9_2 [-4, 0, 5] = true := by decide +kernel
theorem subd9_2_59 : subd9_2 [-4, 1, -8] = true := by decide +kernel
theorem subd9_2_60 : subd9_2 [-4, 1, -7] = true := by decide +kernel
theorem subd9_2_61 : subd9_2 [-4, 1, -6] = true := by decide +kernel
theorem subd9_2_62 : subd9_2 [-4, 1, -5] = true := by decide +kernel
theorem subd9_2_63 : subd9_2 [-4, 1, -4] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_cons.2 ⟨subd9_2_36, List.forall_mem_cons.2 ⟨subd9_2_37, List.forall_mem_cons.2 ⟨subd9_2_38, List.forall_mem_cons.2 ⟨subd9_2_39, List.forall_mem_cons.2 ⟨subd9_2_40, List.forall_mem_cons.2 ⟨subd9_2_41, List.forall_mem_cons.2 ⟨subd9_2_42, List.forall_mem_cons.2 ⟨subd9_2_43, List.forall_mem_cons.2 ⟨subd9_2_44, List.forall_mem_cons.2 ⟨subd9_2_45, List.forall_mem_cons.2 ⟨subd9_2_46, List.forall_mem_cons.2 ⟨subd9_2_47, List.forall_mem_cons.2 ⟨subd9_2_48, List.forall_mem_cons.2 ⟨subd9_2_49, List.forall_mem_cons.2 ⟨subd9_2_50, List.forall_mem_cons.2 ⟨subd9_2_51, List.forall_mem_cons.2 ⟨subd9_2_52, List.forall_mem_cons.2 ⟨subd9_2_53, List.forall_mem_cons.2 ⟨subd9_2_54, List.forall_mem_cons.2 ⟨subd9_2_55, List.forall_mem_cons.2 ⟨subd9_2_56, List.forall_mem_cons.2 ⟨subd9_2_57, List.forall_mem_cons.2 ⟨subd9_2_58, List.forall_mem_cons.2 ⟨subd9_2_59, List.forall_mem_cons.2 ⟨subd9_2_60, List.forall_mem_cons.2 ⟨subd9_2_61, List.forall_mem_cons.2 ⟨subd9_2_62, List.forall_mem_cons.2 ⟨subd9_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
