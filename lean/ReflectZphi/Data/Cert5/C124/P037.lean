import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_10_0 : subd7_10 [-3] = true := by decide +kernel
theorem subd7_10_1 : subd7_10 [-2, -2] = true := by decide +kernel
theorem subd7_10_2 : subd7_10 [-2, -1] = true := by decide +kernel
theorem subd7_10_3 : subd7_10 [-2, 0, -7] = true := by decide +kernel
theorem subd7_10_4 : subd7_10 [-2, 0, -6] = true := by decide +kernel
theorem subd7_10_5 : subd7_10 [-2, 0, -5] = true := by decide +kernel
theorem subd7_10_6 : subd7_10 [-2, 0, -4] = true := by decide +kernel
theorem subd7_10_7 : subd7_10 [-2, 0, -3] = true := by decide +kernel
theorem subd7_10_8 : subd7_10 [-2, 0, -2] = true := by decide +kernel
theorem subd7_10_9 : subd7_10 [-2, 0, -1] = true := by decide +kernel
theorem subd7_10_10 : subd7_10 [-2, 0, 0] = true := by decide +kernel
theorem subd7_10_11 : subd7_10 [-2, 0, 1] = true := by decide +kernel
theorem subd7_10_12 : subd7_10 [-2, 0, 2] = true := by decide +kernel
theorem subd7_10_13 : subd7_10 [-2, 0, 3] = true := by decide +kernel
theorem subd7_10_14 : subd7_10 [-2, 0, 4] = true := by decide +kernel
theorem subd7_10_15 : subd7_10 [-2, 0, 5] = true := by decide +kernel
theorem subd7_10_16 : subd7_10 [-2, 0, 6] = true := by decide +kernel
theorem subd7_10_17 : subd7_10 [-2, 0, 7] = true := by decide +kernel
theorem subd7_10_18 : subd7_10 [-2, 1, -7] = true := by decide +kernel
theorem subd7_10_19 : subd7_10 [-2, 1, -6] = true := by decide +kernel
theorem subd7_10_20 : subd7_10 [-2, 1, -5] = true := by decide +kernel
theorem subd7_10_21 : subd7_10 [-2, 1, -4] = true := by decide +kernel
theorem subd7_10_22 : subd7_10 [-2, 1, -3] = true := by decide +kernel
theorem subd7_10_23 : subd7_10 [-2, 1, -2] = true := by decide +kernel
theorem subd7_10_24 : subd7_10 [-2, 1, -1] = true := by decide +kernel
theorem subd7_10_25 : subd7_10 [-2, 1, 0] = true := by decide +kernel
theorem subd7_10_26 : subd7_10 [-2, 1, 1] = true := by decide +kernel
theorem subd7_10_27 : subd7_10 [-2, 1, 2] = true := by decide +kernel
theorem subd7_10_28 : subd7_10 [-2, 1, 3] = true := by decide +kernel
theorem subd7_10_29 : subd7_10 [-2, 1, 4] = true := by decide +kernel
theorem subd7_10_30 : subd7_10 [-2, 1, 5] = true := by decide +kernel
theorem subd7_10_31 : subd7_10 [-2, 1, 6] = true := by decide +kernel
theorem sbd7_10_0 : ∀ q ∈ blkd7_10_0, subd7_10 q = true := by
  unfold blkd7_10_0
  exact List.forall_mem_cons.2 ⟨subd7_10_0, List.forall_mem_cons.2 ⟨subd7_10_1, List.forall_mem_cons.2 ⟨subd7_10_2, List.forall_mem_cons.2 ⟨subd7_10_3, List.forall_mem_cons.2 ⟨subd7_10_4, List.forall_mem_cons.2 ⟨subd7_10_5, List.forall_mem_cons.2 ⟨subd7_10_6, List.forall_mem_cons.2 ⟨subd7_10_7, List.forall_mem_cons.2 ⟨subd7_10_8, List.forall_mem_cons.2 ⟨subd7_10_9, List.forall_mem_cons.2 ⟨subd7_10_10, List.forall_mem_cons.2 ⟨subd7_10_11, List.forall_mem_cons.2 ⟨subd7_10_12, List.forall_mem_cons.2 ⟨subd7_10_13, List.forall_mem_cons.2 ⟨subd7_10_14, List.forall_mem_cons.2 ⟨subd7_10_15, List.forall_mem_cons.2 ⟨subd7_10_16, List.forall_mem_cons.2 ⟨subd7_10_17, List.forall_mem_cons.2 ⟨subd7_10_18, List.forall_mem_cons.2 ⟨subd7_10_19, List.forall_mem_cons.2 ⟨subd7_10_20, List.forall_mem_cons.2 ⟨subd7_10_21, List.forall_mem_cons.2 ⟨subd7_10_22, List.forall_mem_cons.2 ⟨subd7_10_23, List.forall_mem_cons.2 ⟨subd7_10_24, List.forall_mem_cons.2 ⟨subd7_10_25, List.forall_mem_cons.2 ⟨subd7_10_26, List.forall_mem_cons.2 ⟨subd7_10_27, List.forall_mem_cons.2 ⟨subd7_10_28, List.forall_mem_cons.2 ⟨subd7_10_29, List.forall_mem_cons.2 ⟨subd7_10_30, List.forall_mem_cons.2 ⟨subd7_10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_32 : subd7_10 [-2, 1, 7] = true := by decide +kernel
theorem subd7_10_33 : subd7_10 [-2, 2] = true := by decide +kernel
theorem subd7_10_34 : subd7_10 [-1, -3] = true := by decide +kernel
theorem subd7_10_35 : subd7_10 [-1, -2] = true := by decide +kernel
theorem subd7_10_36 : subd7_10 [-1, -1, -9] = true := by decide +kernel
theorem subd7_10_37 : subd7_10 [-1, -1, -8] = true := by decide +kernel
theorem subd7_10_38 : subd7_10 [-1, -1, -7] = true := by decide +kernel
theorem subd7_10_39 : subd7_10 [-1, -1, -6] = true := by decide +kernel
theorem subd7_10_40 : subd7_10 [-1, -1, -5] = true := by decide +kernel
theorem subd7_10_41 : subd7_10 [-1, -1, -4] = true := by decide +kernel
theorem subd7_10_42 : subd7_10 [-1, -1, -3] = true := by decide +kernel
theorem subd7_10_43 : subd7_10 [-1, -1, -2] = true := by decide +kernel
theorem subd7_10_44 : subd7_10 [-1, -1, -1] = true := by decide +kernel
theorem subd7_10_45 : subd7_10 [-1, -1, 0] = true := by decide +kernel
theorem subd7_10_46 : subd7_10 [-1, -1, 1] = true := by decide +kernel
theorem subd7_10_47 : subd7_10 [-1, -1, 2] = true := by decide +kernel
theorem subd7_10_48 : subd7_10 [-1, -1, 3] = true := by decide +kernel
theorem subd7_10_49 : subd7_10 [-1, -1, 4] = true := by decide +kernel
theorem subd7_10_50 : subd7_10 [-1, -1, 5] = true := by decide +kernel
theorem subd7_10_51 : subd7_10 [-1, -1, 6] = true := by decide +kernel
theorem subd7_10_52 : subd7_10 [-1, -1, 7] = true := by decide +kernel
theorem subd7_10_53 : subd7_10 [-1, 0, -9] = true := by decide +kernel
theorem subd7_10_54 : subd7_10 [-1, 0, -8] = true := by decide +kernel
theorem subd7_10_55 : subd7_10 [-1, 0, -7] = true := by decide +kernel
theorem subd7_10_56 : subd7_10 [-1, 0, -6] = true := by decide +kernel
theorem subd7_10_57 : subd7_10 [-1, 0, -5] = true := by decide +kernel
theorem subd7_10_58 : subd7_10 [-1, 0, -4] = true := by decide +kernel
theorem subd7_10_59 : subd7_10 [-1, 0, -3] = true := by decide +kernel
theorem subd7_10_60 : subd7_10 [-1, 0, -2] = true := by decide +kernel
theorem subd7_10_61 : subd7_10 [-1, 0, -1] = true := by decide +kernel
theorem subd7_10_62 : subd7_10 [-1, 0, 0] = true := by decide +kernel
theorem subd7_10_63 : subd7_10 [-1, 0, 1] = true := by decide +kernel
theorem sbd7_10_1 : ∀ q ∈ blkd7_10_1, subd7_10 q = true := by
  unfold blkd7_10_1
  exact List.forall_mem_cons.2 ⟨subd7_10_32, List.forall_mem_cons.2 ⟨subd7_10_33, List.forall_mem_cons.2 ⟨subd7_10_34, List.forall_mem_cons.2 ⟨subd7_10_35, List.forall_mem_cons.2 ⟨subd7_10_36, List.forall_mem_cons.2 ⟨subd7_10_37, List.forall_mem_cons.2 ⟨subd7_10_38, List.forall_mem_cons.2 ⟨subd7_10_39, List.forall_mem_cons.2 ⟨subd7_10_40, List.forall_mem_cons.2 ⟨subd7_10_41, List.forall_mem_cons.2 ⟨subd7_10_42, List.forall_mem_cons.2 ⟨subd7_10_43, List.forall_mem_cons.2 ⟨subd7_10_44, List.forall_mem_cons.2 ⟨subd7_10_45, List.forall_mem_cons.2 ⟨subd7_10_46, List.forall_mem_cons.2 ⟨subd7_10_47, List.forall_mem_cons.2 ⟨subd7_10_48, List.forall_mem_cons.2 ⟨subd7_10_49, List.forall_mem_cons.2 ⟨subd7_10_50, List.forall_mem_cons.2 ⟨subd7_10_51, List.forall_mem_cons.2 ⟨subd7_10_52, List.forall_mem_cons.2 ⟨subd7_10_53, List.forall_mem_cons.2 ⟨subd7_10_54, List.forall_mem_cons.2 ⟨subd7_10_55, List.forall_mem_cons.2 ⟨subd7_10_56, List.forall_mem_cons.2 ⟨subd7_10_57, List.forall_mem_cons.2 ⟨subd7_10_58, List.forall_mem_cons.2 ⟨subd7_10_59, List.forall_mem_cons.2 ⟨subd7_10_60, List.forall_mem_cons.2 ⟨subd7_10_61, List.forall_mem_cons.2 ⟨subd7_10_62, List.forall_mem_cons.2 ⟨subd7_10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_64 : subd7_10 [-1, 0, 2] = true := by decide +kernel
theorem subd7_10_65 : subd7_10 [-1, 0, 3] = true := by decide +kernel
theorem subd7_10_66 : subd7_10 [-1, 0, 4] = true := by decide +kernel
theorem subd7_10_67 : subd7_10 [-1, 0, 5] = true := by decide +kernel
theorem subd7_10_68 : subd7_10 [-1, 0, 6] = true := by decide +kernel
theorem subd7_10_69 : subd7_10 [-1, 0, 7] = true := by decide +kernel
theorem subd7_10_70 : subd7_10 [-1, 0, 8] = true := by decide +kernel
theorem subd7_10_71 : subd7_10 [-1, 1, -8] = true := by decide +kernel
theorem subd7_10_72 : subd7_10 [-1, 1, -7] = true := by decide +kernel
theorem subd7_10_73 : subd7_10 [-1, 1, -6] = true := by decide +kernel
theorem subd7_10_74 : subd7_10 [-1, 1, -5] = true := by decide +kernel
theorem subd7_10_75 : subd7_10 [-1, 1, -4] = true := by decide +kernel
theorem subd7_10_76 : subd7_10 [-1, 1, -3] = true := by decide +kernel
theorem subd7_10_77 : subd7_10 [-1, 1, -2] = true := by decide +kernel
theorem subd7_10_78 : subd7_10 [-1, 1, -1] = true := by decide +kernel
theorem subd7_10_79 : subd7_10 [-1, 1, 0] = true := by decide +kernel
theorem subd7_10_80 : subd7_10 [-1, 1, 1] = true := by decide +kernel
theorem subd7_10_81 : subd7_10 [-1, 1, 2] = true := by decide +kernel
theorem subd7_10_82 : subd7_10 [-1, 1, 3] = true := by decide +kernel
theorem subd7_10_83 : subd7_10 [-1, 1, 4] = true := by decide +kernel
theorem subd7_10_84 : subd7_10 [-1, 1, 5] = true := by decide +kernel
theorem subd7_10_85 : subd7_10 [-1, 1, 6] = true := by decide +kernel
theorem subd7_10_86 : subd7_10 [-1, 1, 7] = true := by decide +kernel
theorem subd7_10_87 : subd7_10 [-1, 1, 8] = true := by decide +kernel
theorem subd7_10_88 : subd7_10 [-1, 2, -6] = true := by decide +kernel
theorem subd7_10_89 : subd7_10 [-1, 2, -5] = true := by decide +kernel
theorem subd7_10_90 : subd7_10 [-1, 2, -4] = true := by decide +kernel
theorem subd7_10_91 : subd7_10 [-1, 2, -3] = true := by decide +kernel
theorem subd7_10_92 : subd7_10 [-1, 2, -2] = true := by decide +kernel
theorem subd7_10_93 : subd7_10 [-1, 2, -1] = true := by decide +kernel
theorem subd7_10_94 : subd7_10 [-1, 2, 0] = true := by decide +kernel
theorem subd7_10_95 : subd7_10 [-1, 2, 1] = true := by decide +kernel
theorem sbd7_10_2 : ∀ q ∈ blkd7_10_2, subd7_10 q = true := by
  unfold blkd7_10_2
  exact List.forall_mem_cons.2 ⟨subd7_10_64, List.forall_mem_cons.2 ⟨subd7_10_65, List.forall_mem_cons.2 ⟨subd7_10_66, List.forall_mem_cons.2 ⟨subd7_10_67, List.forall_mem_cons.2 ⟨subd7_10_68, List.forall_mem_cons.2 ⟨subd7_10_69, List.forall_mem_cons.2 ⟨subd7_10_70, List.forall_mem_cons.2 ⟨subd7_10_71, List.forall_mem_cons.2 ⟨subd7_10_72, List.forall_mem_cons.2 ⟨subd7_10_73, List.forall_mem_cons.2 ⟨subd7_10_74, List.forall_mem_cons.2 ⟨subd7_10_75, List.forall_mem_cons.2 ⟨subd7_10_76, List.forall_mem_cons.2 ⟨subd7_10_77, List.forall_mem_cons.2 ⟨subd7_10_78, List.forall_mem_cons.2 ⟨subd7_10_79, List.forall_mem_cons.2 ⟨subd7_10_80, List.forall_mem_cons.2 ⟨subd7_10_81, List.forall_mem_cons.2 ⟨subd7_10_82, List.forall_mem_cons.2 ⟨subd7_10_83, List.forall_mem_cons.2 ⟨subd7_10_84, List.forall_mem_cons.2 ⟨subd7_10_85, List.forall_mem_cons.2 ⟨subd7_10_86, List.forall_mem_cons.2 ⟨subd7_10_87, List.forall_mem_cons.2 ⟨subd7_10_88, List.forall_mem_cons.2 ⟨subd7_10_89, List.forall_mem_cons.2 ⟨subd7_10_90, List.forall_mem_cons.2 ⟨subd7_10_91, List.forall_mem_cons.2 ⟨subd7_10_92, List.forall_mem_cons.2 ⟨subd7_10_93, List.forall_mem_cons.2 ⟨subd7_10_94, List.forall_mem_cons.2 ⟨subd7_10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_96 : subd7_10 [-1, 2, 2] = true := by decide +kernel
theorem subd7_10_97 : subd7_10 [-1, 2, 3] = true := by decide +kernel
theorem subd7_10_98 : subd7_10 [-1, 2, 4] = true := by decide +kernel
theorem subd7_10_99 : subd7_10 [-1, 2, 5] = true := by decide +kernel
theorem subd7_10_100 : subd7_10 [-1, 2, 6] = true := by decide +kernel
theorem subd7_10_101 : subd7_10 [-1, 2, 7] = true := by decide +kernel
theorem subd7_10_102 : subd7_10 [0, -3] = true := by decide +kernel
theorem subd7_10_103 : subd7_10 [0, -2, -8] = true := by decide +kernel
theorem subd7_10_104 : subd7_10 [0, -2, -7] = true := by decide +kernel
theorem subd7_10_105 : subd7_10 [0, -2, -6] = true := by decide +kernel
theorem subd7_10_106 : subd7_10 [0, -2, -5] = true := by decide +kernel
theorem subd7_10_107 : subd7_10 [0, -2, -4] = true := by decide +kernel
theorem subd7_10_108 : subd7_10 [0, -2, -3] = true := by decide +kernel
theorem subd7_10_109 : subd7_10 [0, -2, -2] = true := by decide +kernel
theorem subd7_10_110 : subd7_10 [0, -2, -1] = true := by decide +kernel
theorem subd7_10_111 : subd7_10 [0, -2, 0] = true := by decide +kernel
theorem subd7_10_112 : subd7_10 [0, -2, 1] = true := by decide +kernel
theorem subd7_10_113 : subd7_10 [0, -2, 2] = true := by decide +kernel
theorem subd7_10_114 : subd7_10 [0, -2, 3] = true := by decide +kernel
theorem subd7_10_115 : subd7_10 [0, -2, 4] = true := by decide +kernel
theorem subd7_10_116 : subd7_10 [0, -2, 5] = true := by decide +kernel
theorem subd7_10_117 : subd7_10 [0, -1, -10] = true := by decide +kernel
theorem subd7_10_118 : subd7_10 [0, -1, -9] = true := by decide +kernel
theorem subd7_10_119 : subd7_10 [0, -1, -8] = true := by decide +kernel
theorem subd7_10_120 : subd7_10 [0, -1, -7] = true := by decide +kernel
theorem subd7_10_121 : subd7_10 [0, -1, -6] = true := by decide +kernel
theorem subd7_10_122 : subd7_10 [0, -1, -5] = true := by decide +kernel
theorem subd7_10_123 : subd7_10 [0, -1, -4] = true := by decide +kernel
theorem subd7_10_124 : subd7_10 [0, -1, -3] = true := by decide +kernel
theorem subd7_10_125 : subd7_10 [0, -1, -2] = true := by decide +kernel
theorem subd7_10_126 : subd7_10 [0, -1, -1] = true := by decide +kernel
theorem subd7_10_127 : subd7_10 [0, -1, 0] = true := by decide +kernel
theorem sbd7_10_3 : ∀ q ∈ blkd7_10_3, subd7_10 q = true := by
  unfold blkd7_10_3
  exact List.forall_mem_cons.2 ⟨subd7_10_96, List.forall_mem_cons.2 ⟨subd7_10_97, List.forall_mem_cons.2 ⟨subd7_10_98, List.forall_mem_cons.2 ⟨subd7_10_99, List.forall_mem_cons.2 ⟨subd7_10_100, List.forall_mem_cons.2 ⟨subd7_10_101, List.forall_mem_cons.2 ⟨subd7_10_102, List.forall_mem_cons.2 ⟨subd7_10_103, List.forall_mem_cons.2 ⟨subd7_10_104, List.forall_mem_cons.2 ⟨subd7_10_105, List.forall_mem_cons.2 ⟨subd7_10_106, List.forall_mem_cons.2 ⟨subd7_10_107, List.forall_mem_cons.2 ⟨subd7_10_108, List.forall_mem_cons.2 ⟨subd7_10_109, List.forall_mem_cons.2 ⟨subd7_10_110, List.forall_mem_cons.2 ⟨subd7_10_111, List.forall_mem_cons.2 ⟨subd7_10_112, List.forall_mem_cons.2 ⟨subd7_10_113, List.forall_mem_cons.2 ⟨subd7_10_114, List.forall_mem_cons.2 ⟨subd7_10_115, List.forall_mem_cons.2 ⟨subd7_10_116, List.forall_mem_cons.2 ⟨subd7_10_117, List.forall_mem_cons.2 ⟨subd7_10_118, List.forall_mem_cons.2 ⟨subd7_10_119, List.forall_mem_cons.2 ⟨subd7_10_120, List.forall_mem_cons.2 ⟨subd7_10_121, List.forall_mem_cons.2 ⟨subd7_10_122, List.forall_mem_cons.2 ⟨subd7_10_123, List.forall_mem_cons.2 ⟨subd7_10_124, List.forall_mem_cons.2 ⟨subd7_10_125, List.forall_mem_cons.2 ⟨subd7_10_126, List.forall_mem_cons.2 ⟨subd7_10_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_128 : subd7_10 [0, -1, 1] = true := by decide +kernel
theorem subd7_10_129 : subd7_10 [0, -1, 2] = true := by decide +kernel
theorem subd7_10_130 : subd7_10 [0, -1, 3] = true := by decide +kernel
theorem subd7_10_131 : subd7_10 [0, -1, 4] = true := by decide +kernel
theorem subd7_10_132 : subd7_10 [0, -1, 5] = true := by decide +kernel
theorem subd7_10_133 : subd7_10 [0, -1, 6] = true := by decide +kernel
theorem subd7_10_134 : subd7_10 [0, -1, 7] = true := by decide +kernel
theorem subd7_10_135 : subd7_10 [0, -1, 8] = true := by decide +kernel
theorem subd7_10_136 : subd7_10 [0, 0, -10] = true := by decide +kernel
theorem subd7_10_137 : subd7_10 [0, 0, -9] = true := by decide +kernel
theorem subd7_10_138 : subd7_10 [0, 0, -8] = true := by decide +kernel
theorem subd7_10_139 : subd7_10 [0, 0, -7] = true := by decide +kernel
theorem subd7_10_140 : subd7_10 [0, 0, -6] = true := by decide +kernel
theorem subd7_10_141 : subd7_10 [0, 0, -5] = true := by decide +kernel
theorem subd7_10_142 : subd7_10 [0, 0, -4] = true := by decide +kernel
theorem subd7_10_143 : subd7_10 [0, 0, -3] = true := by decide +kernel
theorem subd7_10_144 : subd7_10 [0, 0, -2] = true := by decide +kernel
theorem subd7_10_145 : subd7_10 [0, 0, -1] = true := by decide +kernel
theorem subd7_10_146 : subd7_10 [0, 0, 0] = true := by decide +kernel
theorem subd7_10_147 : subd7_10 [0, 0, 1] = true := by decide +kernel
theorem subd7_10_148 : subd7_10 [0, 0, 2] = true := by decide +kernel
theorem subd7_10_149 : subd7_10 [0, 0, 3] = true := by decide +kernel
theorem subd7_10_150 : subd7_10 [0, 0, 4] = true := by decide +kernel
theorem subd7_10_151 : subd7_10 [0, 0, 5] = true := by decide +kernel
theorem subd7_10_152 : subd7_10 [0, 0, 6] = true := by decide +kernel
theorem subd7_10_153 : subd7_10 [0, 0, 7] = true := by decide +kernel
theorem subd7_10_154 : subd7_10 [0, 0, 8] = true := by decide +kernel
theorem subd7_10_155 : subd7_10 [0, 0, 9] = true := by decide +kernel
theorem subd7_10_156 : subd7_10 [0, 1, -9] = true := by decide +kernel
theorem subd7_10_157 : subd7_10 [0, 1, -8] = true := by decide +kernel
theorem subd7_10_158 : subd7_10 [0, 1, -7] = true := by decide +kernel
theorem subd7_10_159 : subd7_10 [0, 1, -6] = true := by decide +kernel
theorem sbd7_10_4 : ∀ q ∈ blkd7_10_4, subd7_10 q = true := by
  unfold blkd7_10_4
  exact List.forall_mem_cons.2 ⟨subd7_10_128, List.forall_mem_cons.2 ⟨subd7_10_129, List.forall_mem_cons.2 ⟨subd7_10_130, List.forall_mem_cons.2 ⟨subd7_10_131, List.forall_mem_cons.2 ⟨subd7_10_132, List.forall_mem_cons.2 ⟨subd7_10_133, List.forall_mem_cons.2 ⟨subd7_10_134, List.forall_mem_cons.2 ⟨subd7_10_135, List.forall_mem_cons.2 ⟨subd7_10_136, List.forall_mem_cons.2 ⟨subd7_10_137, List.forall_mem_cons.2 ⟨subd7_10_138, List.forall_mem_cons.2 ⟨subd7_10_139, List.forall_mem_cons.2 ⟨subd7_10_140, List.forall_mem_cons.2 ⟨subd7_10_141, List.forall_mem_cons.2 ⟨subd7_10_142, List.forall_mem_cons.2 ⟨subd7_10_143, List.forall_mem_cons.2 ⟨subd7_10_144, List.forall_mem_cons.2 ⟨subd7_10_145, List.forall_mem_cons.2 ⟨subd7_10_146, List.forall_mem_cons.2 ⟨subd7_10_147, List.forall_mem_cons.2 ⟨subd7_10_148, List.forall_mem_cons.2 ⟨subd7_10_149, List.forall_mem_cons.2 ⟨subd7_10_150, List.forall_mem_cons.2 ⟨subd7_10_151, List.forall_mem_cons.2 ⟨subd7_10_152, List.forall_mem_cons.2 ⟨subd7_10_153, List.forall_mem_cons.2 ⟨subd7_10_154, List.forall_mem_cons.2 ⟨subd7_10_155, List.forall_mem_cons.2 ⟨subd7_10_156, List.forall_mem_cons.2 ⟨subd7_10_157, List.forall_mem_cons.2 ⟨subd7_10_158, List.forall_mem_cons.2 ⟨subd7_10_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_160 : subd7_10 [0, 1, -5] = true := by decide +kernel
theorem subd7_10_161 : subd7_10 [0, 1, -4] = true := by decide +kernel
theorem subd7_10_162 : subd7_10 [0, 1, -3] = true := by decide +kernel
theorem subd7_10_163 : subd7_10 [0, 1, -2] = true := by decide +kernel
theorem subd7_10_164 : subd7_10 [0, 1, -1] = true := by decide +kernel
theorem subd7_10_165 : subd7_10 [0, 1, 0] = true := by decide +kernel
theorem subd7_10_166 : subd7_10 [0, 1, 1] = true := by decide +kernel
theorem subd7_10_167 : subd7_10 [0, 1, 2] = true := by decide +kernel
theorem subd7_10_168 : subd7_10 [0, 1, 3] = true := by decide +kernel
theorem subd7_10_169 : subd7_10 [0, 1, 4] = true := by decide +kernel
theorem subd7_10_170 : subd7_10 [0, 1, 5] = true := by decide +kernel
theorem subd7_10_171 : subd7_10 [0, 1, 6] = true := by decide +kernel
theorem subd7_10_172 : subd7_10 [0, 1, 7] = true := by decide +kernel
theorem subd7_10_173 : subd7_10 [0, 1, 8] = true := by decide +kernel
theorem subd7_10_174 : subd7_10 [0, 1, 9] = true := by decide +kernel
theorem subd7_10_175 : subd7_10 [0, 2, -6] = true := by decide +kernel
theorem subd7_10_176 : subd7_10 [0, 2, -5] = true := by decide +kernel
theorem subd7_10_177 : subd7_10 [0, 2, -4] = true := by decide +kernel
theorem subd7_10_178 : subd7_10 [0, 2, -3] = true := by decide +kernel
theorem subd7_10_179 : subd7_10 [0, 2, -2] = true := by decide +kernel
theorem subd7_10_180 : subd7_10 [0, 2, -1] = true := by decide +kernel
theorem subd7_10_181 : subd7_10 [0, 2, 0] = true := by decide +kernel
theorem subd7_10_182 : subd7_10 [0, 2, 1] = true := by decide +kernel
theorem subd7_10_183 : subd7_10 [0, 2, 2] = true := by decide +kernel
theorem subd7_10_184 : subd7_10 [0, 2, 3] = true := by decide +kernel
theorem subd7_10_185 : subd7_10 [0, 2, 4] = true := by decide +kernel
theorem subd7_10_186 : subd7_10 [0, 2, 5] = true := by decide +kernel
theorem subd7_10_187 : subd7_10 [0, 2, 6] = true := by decide +kernel
theorem subd7_10_188 : subd7_10 [0, 2, 7] = true := by decide +kernel
theorem subd7_10_189 : subd7_10 [1, -3] = true := by decide +kernel
theorem subd7_10_190 : subd7_10 [1, -2, -8] = true := by decide +kernel
theorem subd7_10_191 : subd7_10 [1, -2, -7] = true := by decide +kernel
theorem sbd7_10_5 : ∀ q ∈ blkd7_10_5, subd7_10 q = true := by
  unfold blkd7_10_5
  exact List.forall_mem_cons.2 ⟨subd7_10_160, List.forall_mem_cons.2 ⟨subd7_10_161, List.forall_mem_cons.2 ⟨subd7_10_162, List.forall_mem_cons.2 ⟨subd7_10_163, List.forall_mem_cons.2 ⟨subd7_10_164, List.forall_mem_cons.2 ⟨subd7_10_165, List.forall_mem_cons.2 ⟨subd7_10_166, List.forall_mem_cons.2 ⟨subd7_10_167, List.forall_mem_cons.2 ⟨subd7_10_168, List.forall_mem_cons.2 ⟨subd7_10_169, List.forall_mem_cons.2 ⟨subd7_10_170, List.forall_mem_cons.2 ⟨subd7_10_171, List.forall_mem_cons.2 ⟨subd7_10_172, List.forall_mem_cons.2 ⟨subd7_10_173, List.forall_mem_cons.2 ⟨subd7_10_174, List.forall_mem_cons.2 ⟨subd7_10_175, List.forall_mem_cons.2 ⟨subd7_10_176, List.forall_mem_cons.2 ⟨subd7_10_177, List.forall_mem_cons.2 ⟨subd7_10_178, List.forall_mem_cons.2 ⟨subd7_10_179, List.forall_mem_cons.2 ⟨subd7_10_180, List.forall_mem_cons.2 ⟨subd7_10_181, List.forall_mem_cons.2 ⟨subd7_10_182, List.forall_mem_cons.2 ⟨subd7_10_183, List.forall_mem_cons.2 ⟨subd7_10_184, List.forall_mem_cons.2 ⟨subd7_10_185, List.forall_mem_cons.2 ⟨subd7_10_186, List.forall_mem_cons.2 ⟨subd7_10_187, List.forall_mem_cons.2 ⟨subd7_10_188, List.forall_mem_cons.2 ⟨subd7_10_189, List.forall_mem_cons.2 ⟨subd7_10_190, List.forall_mem_cons.2 ⟨subd7_10_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_192 : subd7_10 [1, -2, -6] = true := by decide +kernel
theorem subd7_10_193 : subd7_10 [1, -2, -5] = true := by decide +kernel
theorem subd7_10_194 : subd7_10 [1, -2, -4] = true := by decide +kernel
theorem subd7_10_195 : subd7_10 [1, -2, -3] = true := by decide +kernel
theorem subd7_10_196 : subd7_10 [1, -2, -2] = true := by decide +kernel
theorem subd7_10_197 : subd7_10 [1, -2, -1] = true := by decide +kernel
theorem subd7_10_198 : subd7_10 [1, -2, 0] = true := by decide +kernel
theorem subd7_10_199 : subd7_10 [1, -2, 1] = true := by decide +kernel
theorem subd7_10_200 : subd7_10 [1, -2, 2] = true := by decide +kernel
theorem subd7_10_201 : subd7_10 [1, -2, 3] = true := by decide +kernel
theorem subd7_10_202 : subd7_10 [1, -2, 4] = true := by decide +kernel
theorem subd7_10_203 : subd7_10 [1, -2, 5] = true := by decide +kernel
theorem subd7_10_204 : subd7_10 [1, -1, -9] = true := by decide +kernel
theorem subd7_10_205 : subd7_10 [1, -1, -8] = true := by decide +kernel
theorem subd7_10_206 : subd7_10 [1, -1, -7] = true := by decide +kernel
theorem subd7_10_207 : subd7_10 [1, -1, -6] = true := by decide +kernel
theorem subd7_10_208 : subd7_10 [1, -1, -5] = true := by decide +kernel
theorem subd7_10_209 : subd7_10 [1, -1, -4] = true := by decide +kernel
theorem subd7_10_210 : subd7_10 [1, -1, -3] = true := by decide +kernel
theorem subd7_10_211 : subd7_10 [1, -1, -2] = true := by decide +kernel
theorem subd7_10_212 : subd7_10 [1, -1, -1] = true := by decide +kernel
theorem subd7_10_213 : subd7_10 [1, -1, 0] = true := by decide +kernel
theorem subd7_10_214 : subd7_10 [1, -1, 1] = true := by decide +kernel
theorem subd7_10_215 : subd7_10 [1, -1, 2] = true := by decide +kernel
theorem subd7_10_216 : subd7_10 [1, -1, 3] = true := by decide +kernel
theorem subd7_10_217 : subd7_10 [1, -1, 4] = true := by decide +kernel
theorem subd7_10_218 : subd7_10 [1, -1, 5] = true := by decide +kernel
theorem subd7_10_219 : subd7_10 [1, -1, 6] = true := by decide +kernel
theorem subd7_10_220 : subd7_10 [1, -1, 7] = true := by decide +kernel
theorem subd7_10_221 : subd7_10 [1, 0, -9] = true := by decide +kernel
theorem subd7_10_222 : subd7_10 [1, 0, -8] = true := by decide +kernel
theorem subd7_10_223 : subd7_10 [1, 0, -7] = true := by decide +kernel
theorem sbd7_10_6 : ∀ q ∈ blkd7_10_6, subd7_10 q = true := by
  unfold blkd7_10_6
  exact List.forall_mem_cons.2 ⟨subd7_10_192, List.forall_mem_cons.2 ⟨subd7_10_193, List.forall_mem_cons.2 ⟨subd7_10_194, List.forall_mem_cons.2 ⟨subd7_10_195, List.forall_mem_cons.2 ⟨subd7_10_196, List.forall_mem_cons.2 ⟨subd7_10_197, List.forall_mem_cons.2 ⟨subd7_10_198, List.forall_mem_cons.2 ⟨subd7_10_199, List.forall_mem_cons.2 ⟨subd7_10_200, List.forall_mem_cons.2 ⟨subd7_10_201, List.forall_mem_cons.2 ⟨subd7_10_202, List.forall_mem_cons.2 ⟨subd7_10_203, List.forall_mem_cons.2 ⟨subd7_10_204, List.forall_mem_cons.2 ⟨subd7_10_205, List.forall_mem_cons.2 ⟨subd7_10_206, List.forall_mem_cons.2 ⟨subd7_10_207, List.forall_mem_cons.2 ⟨subd7_10_208, List.forall_mem_cons.2 ⟨subd7_10_209, List.forall_mem_cons.2 ⟨subd7_10_210, List.forall_mem_cons.2 ⟨subd7_10_211, List.forall_mem_cons.2 ⟨subd7_10_212, List.forall_mem_cons.2 ⟨subd7_10_213, List.forall_mem_cons.2 ⟨subd7_10_214, List.forall_mem_cons.2 ⟨subd7_10_215, List.forall_mem_cons.2 ⟨subd7_10_216, List.forall_mem_cons.2 ⟨subd7_10_217, List.forall_mem_cons.2 ⟨subd7_10_218, List.forall_mem_cons.2 ⟨subd7_10_219, List.forall_mem_cons.2 ⟨subd7_10_220, List.forall_mem_cons.2 ⟨subd7_10_221, List.forall_mem_cons.2 ⟨subd7_10_222, List.forall_mem_cons.2 ⟨subd7_10_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_224 : subd7_10 [1, 0, -6] = true := by decide +kernel
theorem subd7_10_225 : subd7_10 [1, 0, -5] = true := by decide +kernel
theorem subd7_10_226 : subd7_10 [1, 0, -4] = true := by decide +kernel
theorem subd7_10_227 : subd7_10 [1, 0, -3] = true := by decide +kernel
theorem subd7_10_228 : subd7_10 [1, 0, -2] = true := by decide +kernel
theorem subd7_10_229 : subd7_10 [1, 0, -1] = true := by decide +kernel
theorem subd7_10_230 : subd7_10 [1, 0, 0] = true := by decide +kernel
theorem subd7_10_231 : subd7_10 [1, 0, 1] = true := by decide +kernel
theorem subd7_10_232 : subd7_10 [1, 0, 2] = true := by decide +kernel
theorem subd7_10_233 : subd7_10 [1, 0, 3] = true := by decide +kernel
theorem subd7_10_234 : subd7_10 [1, 0, 4] = true := by decide +kernel
theorem subd7_10_235 : subd7_10 [1, 0, 5] = true := by decide +kernel
theorem subd7_10_236 : subd7_10 [1, 0, 6] = true := by decide +kernel
theorem subd7_10_237 : subd7_10 [1, 0, 7] = true := by decide +kernel
theorem subd7_10_238 : subd7_10 [1, 0, 8] = true := by decide +kernel
theorem subd7_10_239 : subd7_10 [1, 1, -8] = true := by decide +kernel
theorem subd7_10_240 : subd7_10 [1, 1, -7] = true := by decide +kernel
theorem subd7_10_241 : subd7_10 [1, 1, -6] = true := by decide +kernel
theorem subd7_10_242 : subd7_10 [1, 1, -5] = true := by decide +kernel
theorem subd7_10_243 : subd7_10 [1, 1, -4] = true := by decide +kernel
theorem subd7_10_244 : subd7_10 [1, 1, -3] = true := by decide +kernel
theorem subd7_10_245 : subd7_10 [1, 1, -2] = true := by decide +kernel
theorem subd7_10_246 : subd7_10 [1, 1, -1] = true := by decide +kernel
theorem subd7_10_247 : subd7_10 [1, 1, 0] = true := by decide +kernel
theorem subd7_10_248 : subd7_10 [1, 1, 1] = true := by decide +kernel
theorem subd7_10_249 : subd7_10 [1, 1, 2] = true := by decide +kernel
theorem subd7_10_250 : subd7_10 [1, 1, 3] = true := by decide +kernel
theorem subd7_10_251 : subd7_10 [1, 1, 4] = true := by decide +kernel
theorem subd7_10_252 : subd7_10 [1, 1, 5] = true := by decide +kernel
theorem subd7_10_253 : subd7_10 [1, 1, 6] = true := by decide +kernel
theorem subd7_10_254 : subd7_10 [1, 1, 7] = true := by decide +kernel
theorem subd7_10_255 : subd7_10 [1, 1, 8] = true := by decide +kernel
theorem sbd7_10_7 : ∀ q ∈ blkd7_10_7, subd7_10 q = true := by
  unfold blkd7_10_7
  exact List.forall_mem_cons.2 ⟨subd7_10_224, List.forall_mem_cons.2 ⟨subd7_10_225, List.forall_mem_cons.2 ⟨subd7_10_226, List.forall_mem_cons.2 ⟨subd7_10_227, List.forall_mem_cons.2 ⟨subd7_10_228, List.forall_mem_cons.2 ⟨subd7_10_229, List.forall_mem_cons.2 ⟨subd7_10_230, List.forall_mem_cons.2 ⟨subd7_10_231, List.forall_mem_cons.2 ⟨subd7_10_232, List.forall_mem_cons.2 ⟨subd7_10_233, List.forall_mem_cons.2 ⟨subd7_10_234, List.forall_mem_cons.2 ⟨subd7_10_235, List.forall_mem_cons.2 ⟨subd7_10_236, List.forall_mem_cons.2 ⟨subd7_10_237, List.forall_mem_cons.2 ⟨subd7_10_238, List.forall_mem_cons.2 ⟨subd7_10_239, List.forall_mem_cons.2 ⟨subd7_10_240, List.forall_mem_cons.2 ⟨subd7_10_241, List.forall_mem_cons.2 ⟨subd7_10_242, List.forall_mem_cons.2 ⟨subd7_10_243, List.forall_mem_cons.2 ⟨subd7_10_244, List.forall_mem_cons.2 ⟨subd7_10_245, List.forall_mem_cons.2 ⟨subd7_10_246, List.forall_mem_cons.2 ⟨subd7_10_247, List.forall_mem_cons.2 ⟨subd7_10_248, List.forall_mem_cons.2 ⟨subd7_10_249, List.forall_mem_cons.2 ⟨subd7_10_250, List.forall_mem_cons.2 ⟨subd7_10_251, List.forall_mem_cons.2 ⟨subd7_10_252, List.forall_mem_cons.2 ⟨subd7_10_253, List.forall_mem_cons.2 ⟨subd7_10_254, List.forall_mem_cons.2 ⟨subd7_10_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_256 : subd7_10 [1, 2] = true := by decide +kernel
theorem subd7_10_257 : subd7_10 [2, -3] = true := by decide +kernel
theorem subd7_10_258 : subd7_10 [2, -2] = true := by decide +kernel
theorem subd7_10_259 : subd7_10 [2, -1, -8] = true := by decide +kernel
theorem subd7_10_260 : subd7_10 [2, -1, -7] = true := by decide +kernel
theorem subd7_10_261 : subd7_10 [2, -1, -6] = true := by decide +kernel
theorem subd7_10_262 : subd7_10 [2, -1, -5] = true := by decide +kernel
theorem subd7_10_263 : subd7_10 [2, -1, -4] = true := by decide +kernel
theorem subd7_10_264 : subd7_10 [2, -1, -3] = true := by decide +kernel
theorem subd7_10_265 : subd7_10 [2, -1, -2] = true := by decide +kernel
theorem subd7_10_266 : subd7_10 [2, -1, -1] = true := by decide +kernel
theorem subd7_10_267 : subd7_10 [2, -1, 0] = true := by decide +kernel
theorem subd7_10_268 : subd7_10 [2, -1, 1] = true := by decide +kernel
theorem subd7_10_269 : subd7_10 [2, -1, 2] = true := by decide +kernel
theorem subd7_10_270 : subd7_10 [2, -1, 3] = true := by decide +kernel
theorem subd7_10_271 : subd7_10 [2, -1, 4] = true := by decide +kernel
theorem subd7_10_272 : subd7_10 [2, -1, 5] = true := by decide +kernel
theorem subd7_10_273 : subd7_10 [2, -1, 6] = true := by decide +kernel
theorem subd7_10_274 : subd7_10 [2, 0, -8] = true := by decide +kernel
theorem subd7_10_275 : subd7_10 [2, 0, -7] = true := by decide +kernel
theorem subd7_10_276 : subd7_10 [2, 0, -6] = true := by decide +kernel
theorem subd7_10_277 : subd7_10 [2, 0, -5] = true := by decide +kernel
theorem subd7_10_278 : subd7_10 [2, 0, -4] = true := by decide +kernel
theorem subd7_10_279 : subd7_10 [2, 0, -3] = true := by decide +kernel
theorem subd7_10_280 : subd7_10 [2, 0, -2] = true := by decide +kernel
theorem subd7_10_281 : subd7_10 [2, 0, -1] = true := by decide +kernel
theorem subd7_10_282 : subd7_10 [2, 0, 0] = true := by decide +kernel
theorem subd7_10_283 : subd7_10 [2, 0, 1] = true := by decide +kernel
theorem subd7_10_284 : subd7_10 [2, 0, 2] = true := by decide +kernel
theorem subd7_10_285 : subd7_10 [2, 0, 3] = true := by decide +kernel
theorem subd7_10_286 : subd7_10 [2, 0, 4] = true := by decide +kernel
theorem subd7_10_287 : subd7_10 [2, 0, 5] = true := by decide +kernel
theorem sbd7_10_8 : ∀ q ∈ blkd7_10_8, subd7_10 q = true := by
  unfold blkd7_10_8
  exact List.forall_mem_cons.2 ⟨subd7_10_256, List.forall_mem_cons.2 ⟨subd7_10_257, List.forall_mem_cons.2 ⟨subd7_10_258, List.forall_mem_cons.2 ⟨subd7_10_259, List.forall_mem_cons.2 ⟨subd7_10_260, List.forall_mem_cons.2 ⟨subd7_10_261, List.forall_mem_cons.2 ⟨subd7_10_262, List.forall_mem_cons.2 ⟨subd7_10_263, List.forall_mem_cons.2 ⟨subd7_10_264, List.forall_mem_cons.2 ⟨subd7_10_265, List.forall_mem_cons.2 ⟨subd7_10_266, List.forall_mem_cons.2 ⟨subd7_10_267, List.forall_mem_cons.2 ⟨subd7_10_268, List.forall_mem_cons.2 ⟨subd7_10_269, List.forall_mem_cons.2 ⟨subd7_10_270, List.forall_mem_cons.2 ⟨subd7_10_271, List.forall_mem_cons.2 ⟨subd7_10_272, List.forall_mem_cons.2 ⟨subd7_10_273, List.forall_mem_cons.2 ⟨subd7_10_274, List.forall_mem_cons.2 ⟨subd7_10_275, List.forall_mem_cons.2 ⟨subd7_10_276, List.forall_mem_cons.2 ⟨subd7_10_277, List.forall_mem_cons.2 ⟨subd7_10_278, List.forall_mem_cons.2 ⟨subd7_10_279, List.forall_mem_cons.2 ⟨subd7_10_280, List.forall_mem_cons.2 ⟨subd7_10_281, List.forall_mem_cons.2 ⟨subd7_10_282, List.forall_mem_cons.2 ⟨subd7_10_283, List.forall_mem_cons.2 ⟨subd7_10_284, List.forall_mem_cons.2 ⟨subd7_10_285, List.forall_mem_cons.2 ⟨subd7_10_286, List.forall_mem_cons.2 ⟨subd7_10_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_10_288 : subd7_10 [2, 0, 6] = true := by decide +kernel
theorem subd7_10_289 : subd7_10 [2, 1] = true := by decide +kernel
theorem subd7_10_290 : subd7_10 [3] = true := by decide +kernel
theorem sbd7_10_9 : ∀ q ∈ blkd7_10_9, subd7_10 q = true := by
  unfold blkd7_10_9
  exact List.forall_mem_cons.2 ⟨subd7_10_288, List.forall_mem_cons.2 ⟨subd7_10_289, List.forall_mem_cons.2 ⟨subd7_10_290, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_11 : ldCheck G d7_11.U d7_11.ms ldd7_11 = true := by decide +kernel
theorem pre_okd7_11 : subPre G cell7 d7_11 = true := by decide +kernel
theorem subd7_11_0 : subd7_11 [-5] = true := by decide +kernel
theorem subd7_11_1 : subd7_11 [-4, -7] = true := by decide +kernel
theorem subd7_11_2 : subd7_11 [-4, -6] = true := by decide +kernel
theorem subd7_11_3 : subd7_11 [-4, -5] = true := by decide +kernel
theorem subd7_11_4 : subd7_11 [-4, -4] = true := by decide +kernel
theorem subd7_11_5 : subd7_11 [-4, -3] = true := by decide +kernel
theorem subd7_11_6 : subd7_11 [-4, -2] = true := by decide +kernel
theorem subd7_11_7 : subd7_11 [-4, -1] = true := by decide +kernel
theorem subd7_11_8 : subd7_11 [-4, 0] = true := by decide +kernel
theorem subd7_11_9 : subd7_11 [-4, 1] = true := by decide +kernel
theorem subd7_11_10 : subd7_11 [-4, 2] = true := by decide +kernel
theorem subd7_11_11 : subd7_11 [-4, 3] = true := by decide +kernel
theorem subd7_11_12 : subd7_11 [-3, -8] = true := by decide +kernel
theorem subd7_11_13 : subd7_11 [-3, -7] = true := by decide +kernel
theorem subd7_11_14 : subd7_11 [-3, -6] = true := by decide +kernel
theorem subd7_11_15 : subd7_11 [-3, -5] = true := by decide +kernel
theorem subd7_11_16 : subd7_11 [-3, -4] = true := by decide +kernel
theorem subd7_11_17 : subd7_11 [-3, -3] = true := by decide +kernel
theorem subd7_11_18 : subd7_11 [-3, -2] = true := by decide +kernel
theorem subd7_11_19 : subd7_11 [-3, -1] = true := by decide +kernel
theorem subd7_11_20 : subd7_11 [-3, 0] = true := by decide +kernel
theorem subd7_11_21 : subd7_11 [-3, 1] = true := by decide +kernel
theorem subd7_11_22 : subd7_11 [-3, 2] = true := by decide +kernel
theorem subd7_11_23 : subd7_11 [-3, 3] = true := by decide +kernel
theorem subd7_11_24 : subd7_11 [-3, 4] = true := by decide +kernel
theorem subd7_11_25 : subd7_11 [-2, -8] = true := by decide +kernel
theorem subd7_11_26 : subd7_11 [-2, -7] = true := by decide +kernel
theorem subd7_11_27 : subd7_11 [-2, -6] = true := by decide +kernel
theorem subd7_11_28 : subd7_11 [-2, -5] = true := by decide +kernel
theorem subd7_11_29 : subd7_11 [-2, -4] = true := by decide +kernel
theorem subd7_11_30 : subd7_11 [-2, -3] = true := by decide +kernel
theorem subd7_11_31 : subd7_11 [-2, -2] = true := by decide +kernel
theorem sbd7_11_0 : ∀ q ∈ blkd7_11_0, subd7_11 q = true := by
  unfold blkd7_11_0
  exact List.forall_mem_cons.2 ⟨subd7_11_0, List.forall_mem_cons.2 ⟨subd7_11_1, List.forall_mem_cons.2 ⟨subd7_11_2, List.forall_mem_cons.2 ⟨subd7_11_3, List.forall_mem_cons.2 ⟨subd7_11_4, List.forall_mem_cons.2 ⟨subd7_11_5, List.forall_mem_cons.2 ⟨subd7_11_6, List.forall_mem_cons.2 ⟨subd7_11_7, List.forall_mem_cons.2 ⟨subd7_11_8, List.forall_mem_cons.2 ⟨subd7_11_9, List.forall_mem_cons.2 ⟨subd7_11_10, List.forall_mem_cons.2 ⟨subd7_11_11, List.forall_mem_cons.2 ⟨subd7_11_12, List.forall_mem_cons.2 ⟨subd7_11_13, List.forall_mem_cons.2 ⟨subd7_11_14, List.forall_mem_cons.2 ⟨subd7_11_15, List.forall_mem_cons.2 ⟨subd7_11_16, List.forall_mem_cons.2 ⟨subd7_11_17, List.forall_mem_cons.2 ⟨subd7_11_18, List.forall_mem_cons.2 ⟨subd7_11_19, List.forall_mem_cons.2 ⟨subd7_11_20, List.forall_mem_cons.2 ⟨subd7_11_21, List.forall_mem_cons.2 ⟨subd7_11_22, List.forall_mem_cons.2 ⟨subd7_11_23, List.forall_mem_cons.2 ⟨subd7_11_24, List.forall_mem_cons.2 ⟨subd7_11_25, List.forall_mem_cons.2 ⟨subd7_11_26, List.forall_mem_cons.2 ⟨subd7_11_27, List.forall_mem_cons.2 ⟨subd7_11_28, List.forall_mem_cons.2 ⟨subd7_11_29, List.forall_mem_cons.2 ⟨subd7_11_30, List.forall_mem_cons.2 ⟨subd7_11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
