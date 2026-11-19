import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_3_0 : subd13_3 [-3] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2, -3] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-2, -2] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-2, -1, -10] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-2, -1, -9] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-2, -1, -8] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-2, -1, -7] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [-2, -1, -6] = true := by decide +kernel
theorem subd13_3_8 : subd13_3 [-2, -1, -5] = true := by decide +kernel
theorem subd13_3_9 : subd13_3 [-2, -1, -4] = true := by decide +kernel
theorem subd13_3_10 : subd13_3 [-2, -1, -3] = true := by decide +kernel
theorem subd13_3_11 : subd13_3 [-2, -1, -2] = true := by decide +kernel
theorem subd13_3_12 : subd13_3 [-2, -1, -1] = true := by decide +kernel
theorem subd13_3_13 : subd13_3 [-2, -1, 0] = true := by decide +kernel
theorem subd13_3_14 : subd13_3 [-2, -1, 1] = true := by decide +kernel
theorem subd13_3_15 : subd13_3 [-2, -1, 2] = true := by decide +kernel
theorem subd13_3_16 : subd13_3 [-2, -1, 3] = true := by decide +kernel
theorem subd13_3_17 : subd13_3 [-2, -1, 4] = true := by decide +kernel
theorem subd13_3_18 : subd13_3 [-2, -1, 5] = true := by decide +kernel
theorem subd13_3_19 : subd13_3 [-2, -1, 6] = true := by decide +kernel
theorem subd13_3_20 : subd13_3 [-2, -1, 7] = true := by decide +kernel
theorem subd13_3_21 : subd13_3 [-2, -1, 8] = true := by decide +kernel
theorem subd13_3_22 : subd13_3 [-2, -1, 9] = true := by decide +kernel
theorem subd13_3_23 : subd13_3 [-2, 0, -11] = true := by decide +kernel
theorem subd13_3_24 : subd13_3 [-2, 0, -10] = true := by decide +kernel
theorem subd13_3_25 : subd13_3 [-2, 0, -9] = true := by decide +kernel
theorem subd13_3_26 : subd13_3 [-2, 0, -8] = true := by decide +kernel
theorem subd13_3_27 : subd13_3 [-2, 0, -7] = true := by decide +kernel
theorem subd13_3_28 : subd13_3 [-2, 0, -6] = true := by decide +kernel
theorem subd13_3_29 : subd13_3 [-2, 0, -5] = true := by decide +kernel
theorem subd13_3_30 : subd13_3 [-2, 0, -4] = true := by decide +kernel
theorem subd13_3_31 : subd13_3 [-2, 0, -3] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_cons.2 ⟨subd13_3_7, List.forall_mem_cons.2 ⟨subd13_3_8, List.forall_mem_cons.2 ⟨subd13_3_9, List.forall_mem_cons.2 ⟨subd13_3_10, List.forall_mem_cons.2 ⟨subd13_3_11, List.forall_mem_cons.2 ⟨subd13_3_12, List.forall_mem_cons.2 ⟨subd13_3_13, List.forall_mem_cons.2 ⟨subd13_3_14, List.forall_mem_cons.2 ⟨subd13_3_15, List.forall_mem_cons.2 ⟨subd13_3_16, List.forall_mem_cons.2 ⟨subd13_3_17, List.forall_mem_cons.2 ⟨subd13_3_18, List.forall_mem_cons.2 ⟨subd13_3_19, List.forall_mem_cons.2 ⟨subd13_3_20, List.forall_mem_cons.2 ⟨subd13_3_21, List.forall_mem_cons.2 ⟨subd13_3_22, List.forall_mem_cons.2 ⟨subd13_3_23, List.forall_mem_cons.2 ⟨subd13_3_24, List.forall_mem_cons.2 ⟨subd13_3_25, List.forall_mem_cons.2 ⟨subd13_3_26, List.forall_mem_cons.2 ⟨subd13_3_27, List.forall_mem_cons.2 ⟨subd13_3_28, List.forall_mem_cons.2 ⟨subd13_3_29, List.forall_mem_cons.2 ⟨subd13_3_30, List.forall_mem_cons.2 ⟨subd13_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_32 : subd13_3 [-2, 0, -2] = true := by decide +kernel
theorem subd13_3_33 : subd13_3 [-2, 0, -1] = true := by decide +kernel
theorem subd13_3_34 : subd13_3 [-2, 0, 0] = true := by decide +kernel
theorem subd13_3_35 : subd13_3 [-2, 0, 1] = true := by decide +kernel
theorem subd13_3_36 : subd13_3 [-2, 0, 2] = true := by decide +kernel
theorem subd13_3_37 : subd13_3 [-2, 0, 3] = true := by decide +kernel
theorem subd13_3_38 : subd13_3 [-2, 0, 4] = true := by decide +kernel
theorem subd13_3_39 : subd13_3 [-2, 0, 5] = true := by decide +kernel
theorem subd13_3_40 : subd13_3 [-2, 0, 6] = true := by decide +kernel
theorem subd13_3_41 : subd13_3 [-2, 0, 7] = true := by decide +kernel
theorem subd13_3_42 : subd13_3 [-2, 0, 8] = true := by decide +kernel
theorem subd13_3_43 : subd13_3 [-2, 0, 9] = true := by decide +kernel
theorem subd13_3_44 : subd13_3 [-2, 0, 10] = true := by decide +kernel
theorem subd13_3_45 : subd13_3 [-2, 0, 11] = true := by decide +kernel
theorem subd13_3_46 : subd13_3 [-2, 1, -10] = true := by decide +kernel
theorem subd13_3_47 : subd13_3 [-2, 1, -9] = true := by decide +kernel
theorem subd13_3_48 : subd13_3 [-2, 1, -8] = true := by decide +kernel
theorem subd13_3_49 : subd13_3 [-2, 1, -7] = true := by decide +kernel
theorem subd13_3_50 : subd13_3 [-2, 1, -6] = true := by decide +kernel
theorem subd13_3_51 : subd13_3 [-2, 1, -5] = true := by decide +kernel
theorem subd13_3_52 : subd13_3 [-2, 1, -4] = true := by decide +kernel
theorem subd13_3_53 : subd13_3 [-2, 1, -3] = true := by decide +kernel
theorem subd13_3_54 : subd13_3 [-2, 1, -2] = true := by decide +kernel
theorem subd13_3_55 : subd13_3 [-2, 1, -1] = true := by decide +kernel
theorem subd13_3_56 : subd13_3 [-2, 1, 0] = true := by decide +kernel
theorem subd13_3_57 : subd13_3 [-2, 1, 1] = true := by decide +kernel
theorem subd13_3_58 : subd13_3 [-2, 1, 2] = true := by decide +kernel
theorem subd13_3_59 : subd13_3 [-2, 1, 3] = true := by decide +kernel
theorem subd13_3_60 : subd13_3 [-2, 1, 4] = true := by decide +kernel
theorem subd13_3_61 : subd13_3 [-2, 1, 5] = true := by decide +kernel
theorem subd13_3_62 : subd13_3 [-2, 1, 6] = true := by decide +kernel
theorem subd13_3_63 : subd13_3 [-2, 1, 7] = true := by decide +kernel
theorem sbd13_3_1 : ∀ q ∈ blkd13_3_1, subd13_3 q = true := by
  unfold blkd13_3_1
  exact List.forall_mem_cons.2 ⟨subd13_3_32, List.forall_mem_cons.2 ⟨subd13_3_33, List.forall_mem_cons.2 ⟨subd13_3_34, List.forall_mem_cons.2 ⟨subd13_3_35, List.forall_mem_cons.2 ⟨subd13_3_36, List.forall_mem_cons.2 ⟨subd13_3_37, List.forall_mem_cons.2 ⟨subd13_3_38, List.forall_mem_cons.2 ⟨subd13_3_39, List.forall_mem_cons.2 ⟨subd13_3_40, List.forall_mem_cons.2 ⟨subd13_3_41, List.forall_mem_cons.2 ⟨subd13_3_42, List.forall_mem_cons.2 ⟨subd13_3_43, List.forall_mem_cons.2 ⟨subd13_3_44, List.forall_mem_cons.2 ⟨subd13_3_45, List.forall_mem_cons.2 ⟨subd13_3_46, List.forall_mem_cons.2 ⟨subd13_3_47, List.forall_mem_cons.2 ⟨subd13_3_48, List.forall_mem_cons.2 ⟨subd13_3_49, List.forall_mem_cons.2 ⟨subd13_3_50, List.forall_mem_cons.2 ⟨subd13_3_51, List.forall_mem_cons.2 ⟨subd13_3_52, List.forall_mem_cons.2 ⟨subd13_3_53, List.forall_mem_cons.2 ⟨subd13_3_54, List.forall_mem_cons.2 ⟨subd13_3_55, List.forall_mem_cons.2 ⟨subd13_3_56, List.forall_mem_cons.2 ⟨subd13_3_57, List.forall_mem_cons.2 ⟨subd13_3_58, List.forall_mem_cons.2 ⟨subd13_3_59, List.forall_mem_cons.2 ⟨subd13_3_60, List.forall_mem_cons.2 ⟨subd13_3_61, List.forall_mem_cons.2 ⟨subd13_3_62, List.forall_mem_cons.2 ⟨subd13_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_64 : subd13_3 [-2, 1, 8] = true := by decide +kernel
theorem subd13_3_65 : subd13_3 [-2, 1, 9] = true := by decide +kernel
theorem subd13_3_66 : subd13_3 [-2, 1, 10] = true := by decide +kernel
theorem subd13_3_67 : subd13_3 [-2, 2, -7] = true := by decide +kernel
theorem subd13_3_68 : subd13_3 [-2, 2, -6] = true := by decide +kernel
theorem subd13_3_69 : subd13_3 [-2, 2, -5] = true := by decide +kernel
theorem subd13_3_70 : subd13_3 [-2, 2, -4] = true := by decide +kernel
theorem subd13_3_71 : subd13_3 [-2, 2, -3] = true := by decide +kernel
theorem subd13_3_72 : subd13_3 [-2, 2, -2] = true := by decide +kernel
theorem subd13_3_73 : subd13_3 [-2, 2, -1] = true := by decide +kernel
theorem subd13_3_74 : subd13_3 [-2, 2, 0] = true := by decide +kernel
theorem subd13_3_75 : subd13_3 [-2, 2, 1] = true := by decide +kernel
theorem subd13_3_76 : subd13_3 [-2, 2, 2] = true := by decide +kernel
theorem subd13_3_77 : subd13_3 [-2, 2, 3] = true := by decide +kernel
theorem subd13_3_78 : subd13_3 [-2, 2, 4] = true := by decide +kernel
theorem subd13_3_79 : subd13_3 [-2, 2, 5] = true := by decide +kernel
theorem subd13_3_80 : subd13_3 [-2, 2, 6] = true := by decide +kernel
theorem subd13_3_81 : subd13_3 [-2, 2, 7] = true := by decide +kernel
theorem subd13_3_82 : subd13_3 [-1, -3] = true := by decide +kernel
theorem subd13_3_83 : subd13_3 [-1, -2, -10] = true := by decide +kernel
theorem subd13_3_84 : subd13_3 [-1, -2, -9] = true := by decide +kernel
theorem subd13_3_85 : subd13_3 [-1, -2, -8] = true := by decide +kernel
theorem subd13_3_86 : subd13_3 [-1, -2, -7] = true := by decide +kernel
theorem subd13_3_87 : subd13_3 [-1, -2, -6] = true := by decide +kernel
theorem subd13_3_88 : subd13_3 [-1, -2, -5] = true := by decide +kernel
theorem subd13_3_89 : subd13_3 [-1, -2, -4] = true := by decide +kernel
theorem subd13_3_90 : subd13_3 [-1, -2, -3] = true := by decide +kernel
theorem subd13_3_91 : subd13_3 [-1, -2, -2] = true := by decide +kernel
theorem subd13_3_92 : subd13_3 [-1, -2, -1] = true := by decide +kernel
theorem subd13_3_93 : subd13_3 [-1, -2, 0] = true := by decide +kernel
theorem subd13_3_94 : subd13_3 [-1, -2, 1] = true := by decide +kernel
theorem subd13_3_95 : subd13_3 [-1, -2, 2] = true := by decide +kernel
theorem sbd13_3_2 : ∀ q ∈ blkd13_3_2, subd13_3 q = true := by
  unfold blkd13_3_2
  exact List.forall_mem_cons.2 ⟨subd13_3_64, List.forall_mem_cons.2 ⟨subd13_3_65, List.forall_mem_cons.2 ⟨subd13_3_66, List.forall_mem_cons.2 ⟨subd13_3_67, List.forall_mem_cons.2 ⟨subd13_3_68, List.forall_mem_cons.2 ⟨subd13_3_69, List.forall_mem_cons.2 ⟨subd13_3_70, List.forall_mem_cons.2 ⟨subd13_3_71, List.forall_mem_cons.2 ⟨subd13_3_72, List.forall_mem_cons.2 ⟨subd13_3_73, List.forall_mem_cons.2 ⟨subd13_3_74, List.forall_mem_cons.2 ⟨subd13_3_75, List.forall_mem_cons.2 ⟨subd13_3_76, List.forall_mem_cons.2 ⟨subd13_3_77, List.forall_mem_cons.2 ⟨subd13_3_78, List.forall_mem_cons.2 ⟨subd13_3_79, List.forall_mem_cons.2 ⟨subd13_3_80, List.forall_mem_cons.2 ⟨subd13_3_81, List.forall_mem_cons.2 ⟨subd13_3_82, List.forall_mem_cons.2 ⟨subd13_3_83, List.forall_mem_cons.2 ⟨subd13_3_84, List.forall_mem_cons.2 ⟨subd13_3_85, List.forall_mem_cons.2 ⟨subd13_3_86, List.forall_mem_cons.2 ⟨subd13_3_87, List.forall_mem_cons.2 ⟨subd13_3_88, List.forall_mem_cons.2 ⟨subd13_3_89, List.forall_mem_cons.2 ⟨subd13_3_90, List.forall_mem_cons.2 ⟨subd13_3_91, List.forall_mem_cons.2 ⟨subd13_3_92, List.forall_mem_cons.2 ⟨subd13_3_93, List.forall_mem_cons.2 ⟨subd13_3_94, List.forall_mem_cons.2 ⟨subd13_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_96 : subd13_3 [-1, -2, 3] = true := by decide +kernel
theorem subd13_3_97 : subd13_3 [-1, -2, 4] = true := by decide +kernel
theorem subd13_3_98 : subd13_3 [-1, -2, 5] = true := by decide +kernel
theorem subd13_3_99 : subd13_3 [-1, -2, 6] = true := by decide +kernel
theorem subd13_3_100 : subd13_3 [-1, -2, 7] = true := by decide +kernel
theorem subd13_3_101 : subd13_3 [-1, -2, 8] = true := by decide +kernel
theorem subd13_3_102 : subd13_3 [-1, -2, 9] = true := by decide +kernel
theorem subd13_3_103 : subd13_3 [-1, -1, -12] = true := by decide +kernel
theorem subd13_3_104 : subd13_3 [-1, -1, -11] = true := by decide +kernel
theorem subd13_3_105 : subd13_3 [-1, -1, -10] = true := by decide +kernel
theorem subd13_3_106 : subd13_3 [-1, -1, -9] = true := by decide +kernel
theorem subd13_3_107 : subd13_3 [-1, -1, -8] = true := by decide +kernel
theorem subd13_3_108 : subd13_3 [-1, -1, -7] = true := by decide +kernel
theorem subd13_3_109 : subd13_3 [-1, -1, -6] = true := by decide +kernel
theorem subd13_3_110 : subd13_3 [-1, -1, -5] = true := by decide +kernel
theorem subd13_3_111 : subd13_3 [-1, -1, -4] = true := by decide +kernel
theorem subd13_3_112 : subd13_3 [-1, -1, -3] = true := by decide +kernel
theorem subd13_3_113 : subd13_3 [-1, -1, -2] = true := by decide +kernel
theorem subd13_3_114 : subd13_3 [-1, -1, -1] = true := by decide +kernel
theorem subd13_3_115 : subd13_3 [-1, -1, 0] = true := by decide +kernel
theorem subd13_3_116 : subd13_3 [-1, -1, 1] = true := by decide +kernel
theorem subd13_3_117 : subd13_3 [-1, -1, 2] = true := by decide +kernel
theorem subd13_3_118 : subd13_3 [-1, -1, 3] = true := by decide +kernel
theorem subd13_3_119 : subd13_3 [-1, -1, 4] = true := by decide +kernel
theorem subd13_3_120 : subd13_3 [-1, -1, 5] = true := by decide +kernel
theorem subd13_3_121 : subd13_3 [-1, -1, 6] = true := by decide +kernel
theorem subd13_3_122 : subd13_3 [-1, -1, 7] = true := by decide +kernel
theorem subd13_3_123 : subd13_3 [-1, -1, 8] = true := by decide +kernel
theorem subd13_3_124 : subd13_3 [-1, -1, 9] = true := by decide +kernel
theorem subd13_3_125 : subd13_3 [-1, -1, 10] = true := by decide +kernel
theorem subd13_3_126 : subd13_3 [-1, -1, 11] = true := by decide +kernel
theorem subd13_3_127 : subd13_3 [-1, -1, 12] = true := by decide +kernel
theorem sbd13_3_3 : ∀ q ∈ blkd13_3_3, subd13_3 q = true := by
  unfold blkd13_3_3
  exact List.forall_mem_cons.2 ⟨subd13_3_96, List.forall_mem_cons.2 ⟨subd13_3_97, List.forall_mem_cons.2 ⟨subd13_3_98, List.forall_mem_cons.2 ⟨subd13_3_99, List.forall_mem_cons.2 ⟨subd13_3_100, List.forall_mem_cons.2 ⟨subd13_3_101, List.forall_mem_cons.2 ⟨subd13_3_102, List.forall_mem_cons.2 ⟨subd13_3_103, List.forall_mem_cons.2 ⟨subd13_3_104, List.forall_mem_cons.2 ⟨subd13_3_105, List.forall_mem_cons.2 ⟨subd13_3_106, List.forall_mem_cons.2 ⟨subd13_3_107, List.forall_mem_cons.2 ⟨subd13_3_108, List.forall_mem_cons.2 ⟨subd13_3_109, List.forall_mem_cons.2 ⟨subd13_3_110, List.forall_mem_cons.2 ⟨subd13_3_111, List.forall_mem_cons.2 ⟨subd13_3_112, List.forall_mem_cons.2 ⟨subd13_3_113, List.forall_mem_cons.2 ⟨subd13_3_114, List.forall_mem_cons.2 ⟨subd13_3_115, List.forall_mem_cons.2 ⟨subd13_3_116, List.forall_mem_cons.2 ⟨subd13_3_117, List.forall_mem_cons.2 ⟨subd13_3_118, List.forall_mem_cons.2 ⟨subd13_3_119, List.forall_mem_cons.2 ⟨subd13_3_120, List.forall_mem_cons.2 ⟨subd13_3_121, List.forall_mem_cons.2 ⟨subd13_3_122, List.forall_mem_cons.2 ⟨subd13_3_123, List.forall_mem_cons.2 ⟨subd13_3_124, List.forall_mem_cons.2 ⟨subd13_3_125, List.forall_mem_cons.2 ⟨subd13_3_126, List.forall_mem_cons.2 ⟨subd13_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_128 : subd13_3 [-1, 0, -13] = true := by decide +kernel
theorem subd13_3_129 : subd13_3 [-1, 0, -12] = true := by decide +kernel
theorem subd13_3_130 : subd13_3 [-1, 0, -11] = true := by decide +kernel
theorem subd13_3_131 : subd13_3 [-1, 0, -10] = true := by decide +kernel
theorem subd13_3_132 : subd13_3 [-1, 0, -9] = true := by decide +kernel
theorem subd13_3_133 : subd13_3 [-1, 0, -8] = true := by decide +kernel
theorem subd13_3_134 : subd13_3 [-1, 0, -7] = true := by decide +kernel
theorem subd13_3_135 : subd13_3 [-1, 0, -6] = true := by decide +kernel
theorem subd13_3_136 : subd13_3 [-1, 0, -5] = true := by decide +kernel
theorem subd13_3_137 : subd13_3 [-1, 0, -4] = true := by decide +kernel
theorem subd13_3_138 : subd13_3 [-1, 0, -3] = true := by decide +kernel
theorem subd13_3_139 : subd13_3 [-1, 0, -2] = true := by decide +kernel
theorem subd13_3_140 : subd13_3 [-1, 0, -1] = true := by decide +kernel
theorem subd13_3_141 : subd13_3 [-1, 0, 0] = true := by decide +kernel
theorem subd13_3_142 : subd13_3 [-1, 0, 1] = true := by decide +kernel
theorem subd13_3_143 : subd13_3 [-1, 0, 2] = true := by decide +kernel
theorem subd13_3_144 : subd13_3 [-1, 0, 3] = true := by decide +kernel
theorem subd13_3_145 : subd13_3 [-1, 0, 4] = true := by decide +kernel
theorem subd13_3_146 : subd13_3 [-1, 0, 5] = true := by decide +kernel
theorem subd13_3_147 : subd13_3 [-1, 0, 6] = true := by decide +kernel
theorem subd13_3_148 : subd13_3 [-1, 0, 7] = true := by decide +kernel
theorem subd13_3_149 : subd13_3 [-1, 0, 8] = true := by decide +kernel
theorem subd13_3_150 : subd13_3 [-1, 0, 9] = true := by decide +kernel
theorem subd13_3_151 : subd13_3 [-1, 0, 10] = true := by decide +kernel
theorem subd13_3_152 : subd13_3 [-1, 0, 11] = true := by decide +kernel
theorem subd13_3_153 : subd13_3 [-1, 0, 12] = true := by decide +kernel
theorem subd13_3_154 : subd13_3 [-1, 0, 13] = true := by decide +kernel
theorem subd13_3_155 : subd13_3 [-1, 1, -13] = true := by decide +kernel
theorem subd13_3_156 : subd13_3 [-1, 1, -12] = true := by decide +kernel
theorem subd13_3_157 : subd13_3 [-1, 1, -11] = true := by decide +kernel
theorem subd13_3_158 : subd13_3 [-1, 1, -10] = true := by decide +kernel
theorem subd13_3_159 : subd13_3 [-1, 1, -9] = true := by decide +kernel
theorem sbd13_3_4 : ∀ q ∈ blkd13_3_4, subd13_3 q = true := by
  unfold blkd13_3_4
  exact List.forall_mem_cons.2 ⟨subd13_3_128, List.forall_mem_cons.2 ⟨subd13_3_129, List.forall_mem_cons.2 ⟨subd13_3_130, List.forall_mem_cons.2 ⟨subd13_3_131, List.forall_mem_cons.2 ⟨subd13_3_132, List.forall_mem_cons.2 ⟨subd13_3_133, List.forall_mem_cons.2 ⟨subd13_3_134, List.forall_mem_cons.2 ⟨subd13_3_135, List.forall_mem_cons.2 ⟨subd13_3_136, List.forall_mem_cons.2 ⟨subd13_3_137, List.forall_mem_cons.2 ⟨subd13_3_138, List.forall_mem_cons.2 ⟨subd13_3_139, List.forall_mem_cons.2 ⟨subd13_3_140, List.forall_mem_cons.2 ⟨subd13_3_141, List.forall_mem_cons.2 ⟨subd13_3_142, List.forall_mem_cons.2 ⟨subd13_3_143, List.forall_mem_cons.2 ⟨subd13_3_144, List.forall_mem_cons.2 ⟨subd13_3_145, List.forall_mem_cons.2 ⟨subd13_3_146, List.forall_mem_cons.2 ⟨subd13_3_147, List.forall_mem_cons.2 ⟨subd13_3_148, List.forall_mem_cons.2 ⟨subd13_3_149, List.forall_mem_cons.2 ⟨subd13_3_150, List.forall_mem_cons.2 ⟨subd13_3_151, List.forall_mem_cons.2 ⟨subd13_3_152, List.forall_mem_cons.2 ⟨subd13_3_153, List.forall_mem_cons.2 ⟨subd13_3_154, List.forall_mem_cons.2 ⟨subd13_3_155, List.forall_mem_cons.2 ⟨subd13_3_156, List.forall_mem_cons.2 ⟨subd13_3_157, List.forall_mem_cons.2 ⟨subd13_3_158, List.forall_mem_cons.2 ⟨subd13_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_160 : subd13_3 [-1, 1, -8] = true := by decide +kernel
theorem subd13_3_161 : subd13_3 [-1, 1, -7] = true := by decide +kernel
theorem subd13_3_162 : subd13_3 [-1, 1, -6] = true := by decide +kernel
theorem subd13_3_163 : subd13_3 [-1, 1, -5] = true := by decide +kernel
theorem subd13_3_164 : subd13_3 [-1, 1, -4] = true := by decide +kernel
theorem subd13_3_165 : subd13_3 [-1, 1, -3] = true := by decide +kernel
theorem subd13_3_166 : subd13_3 [-1, 1, -2] = true := by decide +kernel
theorem subd13_3_167 : subd13_3 [-1, 1, -1] = true := by decide +kernel
theorem subd13_3_168 : subd13_3 [-1, 1, 0] = true := by decide +kernel
theorem subd13_3_169 : subd13_3 [-1, 1, 1] = true := by decide +kernel
theorem subd13_3_170 : subd13_3 [-1, 1, 2] = true := by decide +kernel
theorem subd13_3_171 : subd13_3 [-1, 1, 3] = true := by decide +kernel
theorem subd13_3_172 : subd13_3 [-1, 1, 4] = true := by decide +kernel
theorem subd13_3_173 : subd13_3 [-1, 1, 5] = true := by decide +kernel
theorem subd13_3_174 : subd13_3 [-1, 1, 6] = true := by decide +kernel
theorem subd13_3_175 : subd13_3 [-1, 1, 7] = true := by decide +kernel
theorem subd13_3_176 : subd13_3 [-1, 1, 8] = true := by decide +kernel
theorem subd13_3_177 : subd13_3 [-1, 1, 9] = true := by decide +kernel
theorem subd13_3_178 : subd13_3 [-1, 1, 10] = true := by decide +kernel
theorem subd13_3_179 : subd13_3 [-1, 1, 11] = true := by decide +kernel
theorem subd13_3_180 : subd13_3 [-1, 1, 12] = true := by decide +kernel
theorem subd13_3_181 : subd13_3 [-1, 2, -10] = true := by decide +kernel
theorem subd13_3_182 : subd13_3 [-1, 2, -9] = true := by decide +kernel
theorem subd13_3_183 : subd13_3 [-1, 2, -8] = true := by decide +kernel
theorem subd13_3_184 : subd13_3 [-1, 2, -7] = true := by decide +kernel
theorem subd13_3_185 : subd13_3 [-1, 2, -6] = true := by decide +kernel
theorem subd13_3_186 : subd13_3 [-1, 2, -5] = true := by decide +kernel
theorem subd13_3_187 : subd13_3 [-1, 2, -4] = true := by decide +kernel
theorem subd13_3_188 : subd13_3 [-1, 2, -3] = true := by decide +kernel
theorem subd13_3_189 : subd13_3 [-1, 2, -2] = true := by decide +kernel
theorem subd13_3_190 : subd13_3 [-1, 2, -1] = true := by decide +kernel
theorem subd13_3_191 : subd13_3 [-1, 2, 0] = true := by decide +kernel
theorem sbd13_3_5 : ∀ q ∈ blkd13_3_5, subd13_3 q = true := by
  unfold blkd13_3_5
  exact List.forall_mem_cons.2 ⟨subd13_3_160, List.forall_mem_cons.2 ⟨subd13_3_161, List.forall_mem_cons.2 ⟨subd13_3_162, List.forall_mem_cons.2 ⟨subd13_3_163, List.forall_mem_cons.2 ⟨subd13_3_164, List.forall_mem_cons.2 ⟨subd13_3_165, List.forall_mem_cons.2 ⟨subd13_3_166, List.forall_mem_cons.2 ⟨subd13_3_167, List.forall_mem_cons.2 ⟨subd13_3_168, List.forall_mem_cons.2 ⟨subd13_3_169, List.forall_mem_cons.2 ⟨subd13_3_170, List.forall_mem_cons.2 ⟨subd13_3_171, List.forall_mem_cons.2 ⟨subd13_3_172, List.forall_mem_cons.2 ⟨subd13_3_173, List.forall_mem_cons.2 ⟨subd13_3_174, List.forall_mem_cons.2 ⟨subd13_3_175, List.forall_mem_cons.2 ⟨subd13_3_176, List.forall_mem_cons.2 ⟨subd13_3_177, List.forall_mem_cons.2 ⟨subd13_3_178, List.forall_mem_cons.2 ⟨subd13_3_179, List.forall_mem_cons.2 ⟨subd13_3_180, List.forall_mem_cons.2 ⟨subd13_3_181, List.forall_mem_cons.2 ⟨subd13_3_182, List.forall_mem_cons.2 ⟨subd13_3_183, List.forall_mem_cons.2 ⟨subd13_3_184, List.forall_mem_cons.2 ⟨subd13_3_185, List.forall_mem_cons.2 ⟨subd13_3_186, List.forall_mem_cons.2 ⟨subd13_3_187, List.forall_mem_cons.2 ⟨subd13_3_188, List.forall_mem_cons.2 ⟨subd13_3_189, List.forall_mem_cons.2 ⟨subd13_3_190, List.forall_mem_cons.2 ⟨subd13_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_192 : subd13_3 [-1, 2, 1] = true := by decide +kernel
theorem subd13_3_193 : subd13_3 [-1, 2, 2] = true := by decide +kernel
theorem subd13_3_194 : subd13_3 [-1, 2, 3] = true := by decide +kernel
theorem subd13_3_195 : subd13_3 [-1, 2, 4] = true := by decide +kernel
theorem subd13_3_196 : subd13_3 [-1, 2, 5] = true := by decide +kernel
theorem subd13_3_197 : subd13_3 [-1, 2, 6] = true := by decide +kernel
theorem subd13_3_198 : subd13_3 [-1, 2, 7] = true := by decide +kernel
theorem subd13_3_199 : subd13_3 [-1, 2, 8] = true := by decide +kernel
theorem subd13_3_200 : subd13_3 [-1, 2, 9] = true := by decide +kernel
theorem subd13_3_201 : subd13_3 [-1, 2, 10] = true := by decide +kernel
theorem subd13_3_202 : subd13_3 [-1, 3] = true := by decide +kernel
theorem subd13_3_203 : subd13_3 [0, -4] = true := by decide +kernel
theorem subd13_3_204 : subd13_3 [0, -3] = true := by decide +kernel
theorem subd13_3_205 : subd13_3 [0, -2, -11] = true := by decide +kernel
theorem subd13_3_206 : subd13_3 [0, -2, -10] = true := by decide +kernel
theorem subd13_3_207 : subd13_3 [0, -2, -9] = true := by decide +kernel
theorem subd13_3_208 : subd13_3 [0, -2, -8] = true := by decide +kernel
theorem subd13_3_209 : subd13_3 [0, -2, -7] = true := by decide +kernel
theorem subd13_3_210 : subd13_3 [0, -2, -6] = true := by decide +kernel
theorem subd13_3_211 : subd13_3 [0, -2, -5] = true := by decide +kernel
theorem subd13_3_212 : subd13_3 [0, -2, -4] = true := by decide +kernel
theorem subd13_3_213 : subd13_3 [0, -2, -3] = true := by decide +kernel
theorem subd13_3_214 : subd13_3 [0, -2, -2] = true := by decide +kernel
theorem subd13_3_215 : subd13_3 [0, -2, -1] = true := by decide +kernel
theorem subd13_3_216 : subd13_3 [0, -2, 0] = true := by decide +kernel
theorem subd13_3_217 : subd13_3 [0, -2, 1] = true := by decide +kernel
theorem subd13_3_218 : subd13_3 [0, -2, 2] = true := by decide +kernel
theorem subd13_3_219 : subd13_3 [0, -2, 3] = true := by decide +kernel
theorem subd13_3_220 : subd13_3 [0, -2, 4] = true := by decide +kernel
theorem subd13_3_221 : subd13_3 [0, -2, 5] = true := by decide +kernel
theorem subd13_3_222 : subd13_3 [0, -2, 6] = true := by decide +kernel
theorem subd13_3_223 : subd13_3 [0, -2, 7] = true := by decide +kernel
theorem sbd13_3_6 : ∀ q ∈ blkd13_3_6, subd13_3 q = true := by
  unfold blkd13_3_6
  exact List.forall_mem_cons.2 ⟨subd13_3_192, List.forall_mem_cons.2 ⟨subd13_3_193, List.forall_mem_cons.2 ⟨subd13_3_194, List.forall_mem_cons.2 ⟨subd13_3_195, List.forall_mem_cons.2 ⟨subd13_3_196, List.forall_mem_cons.2 ⟨subd13_3_197, List.forall_mem_cons.2 ⟨subd13_3_198, List.forall_mem_cons.2 ⟨subd13_3_199, List.forall_mem_cons.2 ⟨subd13_3_200, List.forall_mem_cons.2 ⟨subd13_3_201, List.forall_mem_cons.2 ⟨subd13_3_202, List.forall_mem_cons.2 ⟨subd13_3_203, List.forall_mem_cons.2 ⟨subd13_3_204, List.forall_mem_cons.2 ⟨subd13_3_205, List.forall_mem_cons.2 ⟨subd13_3_206, List.forall_mem_cons.2 ⟨subd13_3_207, List.forall_mem_cons.2 ⟨subd13_3_208, List.forall_mem_cons.2 ⟨subd13_3_209, List.forall_mem_cons.2 ⟨subd13_3_210, List.forall_mem_cons.2 ⟨subd13_3_211, List.forall_mem_cons.2 ⟨subd13_3_212, List.forall_mem_cons.2 ⟨subd13_3_213, List.forall_mem_cons.2 ⟨subd13_3_214, List.forall_mem_cons.2 ⟨subd13_3_215, List.forall_mem_cons.2 ⟨subd13_3_216, List.forall_mem_cons.2 ⟨subd13_3_217, List.forall_mem_cons.2 ⟨subd13_3_218, List.forall_mem_cons.2 ⟨subd13_3_219, List.forall_mem_cons.2 ⟨subd13_3_220, List.forall_mem_cons.2 ⟨subd13_3_221, List.forall_mem_cons.2 ⟨subd13_3_222, List.forall_mem_cons.2 ⟨subd13_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_224 : subd13_3 [0, -2, 8] = true := by decide +kernel
theorem subd13_3_225 : subd13_3 [0, -2, 9] = true := by decide +kernel
theorem subd13_3_226 : subd13_3 [0, -2, 10] = true := by decide +kernel
theorem subd13_3_227 : subd13_3 [0, -1, -13] = true := by decide +kernel
theorem subd13_3_228 : subd13_3 [0, -1, -12] = true := by decide +kernel
theorem subd13_3_229 : subd13_3 [0, -1, -11] = true := by decide +kernel
theorem subd13_3_230 : subd13_3 [0, -1, -10] = true := by decide +kernel
theorem subd13_3_231 : subd13_3 [0, -1, -9] = true := by decide +kernel
theorem subd13_3_232 : subd13_3 [0, -1, -8] = true := by decide +kernel
theorem subd13_3_233 : subd13_3 [0, -1, -7] = true := by decide +kernel
theorem subd13_3_234 : subd13_3 [0, -1, -6] = true := by decide +kernel
theorem subd13_3_235 : subd13_3 [0, -1, -5] = true := by decide +kernel
theorem subd13_3_236 : subd13_3 [0, -1, -4] = true := by decide +kernel
theorem subd13_3_237 : subd13_3 [0, -1, -3] = true := by decide +kernel
theorem subd13_3_238 : subd13_3 [0, -1, -2] = true := by decide +kernel
theorem subd13_3_239 : subd13_3 [0, -1, -1] = true := by decide +kernel
theorem subd13_3_240 : subd13_3 [0, -1, 0] = true := by decide +kernel
theorem subd13_3_241 : subd13_3 [0, -1, 1] = true := by decide +kernel
theorem subd13_3_242 : subd13_3 [0, -1, 2] = true := by decide +kernel
theorem subd13_3_243 : subd13_3 [0, -1, 3] = true := by decide +kernel
theorem subd13_3_244 : subd13_3 [0, -1, 4] = true := by decide +kernel
theorem subd13_3_245 : subd13_3 [0, -1, 5] = true := by decide +kernel
theorem subd13_3_246 : subd13_3 [0, -1, 6] = true := by decide +kernel
theorem subd13_3_247 : subd13_3 [0, -1, 7] = true := by decide +kernel
theorem subd13_3_248 : subd13_3 [0, -1, 8] = true := by decide +kernel
theorem subd13_3_249 : subd13_3 [0, -1, 9] = true := by decide +kernel
theorem subd13_3_250 : subd13_3 [0, -1, 10] = true := by decide +kernel
theorem subd13_3_251 : subd13_3 [0, -1, 11] = true := by decide +kernel
theorem subd13_3_252 : subd13_3 [0, -1, 12] = true := by decide +kernel
theorem subd13_3_253 : subd13_3 [0, 0, -14] = true := by decide +kernel
theorem subd13_3_254 : subd13_3 [0, 0, -13] = true := by decide +kernel
theorem subd13_3_255 : subd13_3 [0, 0, -12] = true := by decide +kernel
theorem sbd13_3_7 : ∀ q ∈ blkd13_3_7, subd13_3 q = true := by
  unfold blkd13_3_7
  exact List.forall_mem_cons.2 ⟨subd13_3_224, List.forall_mem_cons.2 ⟨subd13_3_225, List.forall_mem_cons.2 ⟨subd13_3_226, List.forall_mem_cons.2 ⟨subd13_3_227, List.forall_mem_cons.2 ⟨subd13_3_228, List.forall_mem_cons.2 ⟨subd13_3_229, List.forall_mem_cons.2 ⟨subd13_3_230, List.forall_mem_cons.2 ⟨subd13_3_231, List.forall_mem_cons.2 ⟨subd13_3_232, List.forall_mem_cons.2 ⟨subd13_3_233, List.forall_mem_cons.2 ⟨subd13_3_234, List.forall_mem_cons.2 ⟨subd13_3_235, List.forall_mem_cons.2 ⟨subd13_3_236, List.forall_mem_cons.2 ⟨subd13_3_237, List.forall_mem_cons.2 ⟨subd13_3_238, List.forall_mem_cons.2 ⟨subd13_3_239, List.forall_mem_cons.2 ⟨subd13_3_240, List.forall_mem_cons.2 ⟨subd13_3_241, List.forall_mem_cons.2 ⟨subd13_3_242, List.forall_mem_cons.2 ⟨subd13_3_243, List.forall_mem_cons.2 ⟨subd13_3_244, List.forall_mem_cons.2 ⟨subd13_3_245, List.forall_mem_cons.2 ⟨subd13_3_246, List.forall_mem_cons.2 ⟨subd13_3_247, List.forall_mem_cons.2 ⟨subd13_3_248, List.forall_mem_cons.2 ⟨subd13_3_249, List.forall_mem_cons.2 ⟨subd13_3_250, List.forall_mem_cons.2 ⟨subd13_3_251, List.forall_mem_cons.2 ⟨subd13_3_252, List.forall_mem_cons.2 ⟨subd13_3_253, List.forall_mem_cons.2 ⟨subd13_3_254, List.forall_mem_cons.2 ⟨subd13_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_256 : subd13_3 [0, 0, -11] = true := by decide +kernel
theorem subd13_3_257 : subd13_3 [0, 0, -10] = true := by decide +kernel
theorem subd13_3_258 : subd13_3 [0, 0, -9] = true := by decide +kernel
theorem subd13_3_259 : subd13_3 [0, 0, -8] = true := by decide +kernel
theorem subd13_3_260 : subd13_3 [0, 0, -7] = true := by decide +kernel
theorem subd13_3_261 : subd13_3 [0, 0, -6] = true := by decide +kernel
theorem subd13_3_262 : subd13_3 [0, 0, -5] = true := by decide +kernel
theorem subd13_3_263 : subd13_3 [0, 0, -4] = true := by decide +kernel
theorem subd13_3_264 : subd13_3 [0, 0, -3] = true := by decide +kernel
theorem subd13_3_265 : subd13_3 [0, 0, -2] = true := by decide +kernel
theorem subd13_3_266 : subd13_3 [0, 0, -1] = true := by decide +kernel
theorem subd13_3_267 : subd13_3 [0, 0, 0] = true := by decide +kernel
theorem subd13_3_268 : subd13_3 [0, 0, 1] = true := by decide +kernel
theorem subd13_3_269 : subd13_3 [0, 0, 2] = true := by decide +kernel
theorem subd13_3_270 : subd13_3 [0, 0, 3] = true := by decide +kernel
theorem subd13_3_271 : subd13_3 [0, 0, 4] = true := by decide +kernel
theorem subd13_3_272 : subd13_3 [0, 0, 5] = true := by decide +kernel
theorem subd13_3_273 : subd13_3 [0, 0, 6] = true := by decide +kernel
theorem subd13_3_274 : subd13_3 [0, 0, 7] = true := by decide +kernel
theorem subd13_3_275 : subd13_3 [0, 0, 8] = true := by decide +kernel
theorem subd13_3_276 : subd13_3 [0, 0, 9] = true := by decide +kernel
theorem subd13_3_277 : subd13_3 [0, 0, 10] = true := by decide +kernel
theorem subd13_3_278 : subd13_3 [0, 0, 11] = true := by decide +kernel
theorem subd13_3_279 : subd13_3 [0, 0, 12] = true := by decide +kernel
theorem subd13_3_280 : subd13_3 [0, 0, 13] = true := by decide +kernel
theorem subd13_3_281 : subd13_3 [0, 1, -13] = true := by decide +kernel
theorem subd13_3_282 : subd13_3 [0, 1, -12] = true := by decide +kernel
theorem subd13_3_283 : subd13_3 [0, 1, -11] = true := by decide +kernel
theorem subd13_3_284 : subd13_3 [0, 1, -10] = true := by decide +kernel
theorem subd13_3_285 : subd13_3 [0, 1, -9] = true := by decide +kernel
theorem subd13_3_286 : subd13_3 [0, 1, -8] = true := by decide +kernel
theorem subd13_3_287 : subd13_3 [0, 1, -7] = true := by decide +kernel
theorem sbd13_3_8 : ∀ q ∈ blkd13_3_8, subd13_3 q = true := by
  unfold blkd13_3_8
  exact List.forall_mem_cons.2 ⟨subd13_3_256, List.forall_mem_cons.2 ⟨subd13_3_257, List.forall_mem_cons.2 ⟨subd13_3_258, List.forall_mem_cons.2 ⟨subd13_3_259, List.forall_mem_cons.2 ⟨subd13_3_260, List.forall_mem_cons.2 ⟨subd13_3_261, List.forall_mem_cons.2 ⟨subd13_3_262, List.forall_mem_cons.2 ⟨subd13_3_263, List.forall_mem_cons.2 ⟨subd13_3_264, List.forall_mem_cons.2 ⟨subd13_3_265, List.forall_mem_cons.2 ⟨subd13_3_266, List.forall_mem_cons.2 ⟨subd13_3_267, List.forall_mem_cons.2 ⟨subd13_3_268, List.forall_mem_cons.2 ⟨subd13_3_269, List.forall_mem_cons.2 ⟨subd13_3_270, List.forall_mem_cons.2 ⟨subd13_3_271, List.forall_mem_cons.2 ⟨subd13_3_272, List.forall_mem_cons.2 ⟨subd13_3_273, List.forall_mem_cons.2 ⟨subd13_3_274, List.forall_mem_cons.2 ⟨subd13_3_275, List.forall_mem_cons.2 ⟨subd13_3_276, List.forall_mem_cons.2 ⟨subd13_3_277, List.forall_mem_cons.2 ⟨subd13_3_278, List.forall_mem_cons.2 ⟨subd13_3_279, List.forall_mem_cons.2 ⟨subd13_3_280, List.forall_mem_cons.2 ⟨subd13_3_281, List.forall_mem_cons.2 ⟨subd13_3_282, List.forall_mem_cons.2 ⟨subd13_3_283, List.forall_mem_cons.2 ⟨subd13_3_284, List.forall_mem_cons.2 ⟨subd13_3_285, List.forall_mem_cons.2 ⟨subd13_3_286, List.forall_mem_cons.2 ⟨subd13_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_288 : subd13_3 [0, 1, -6] = true := by decide +kernel
theorem subd13_3_289 : subd13_3 [0, 1, -5] = true := by decide +kernel
theorem subd13_3_290 : subd13_3 [0, 1, -4] = true := by decide +kernel
theorem subd13_3_291 : subd13_3 [0, 1, -3] = true := by decide +kernel
theorem subd13_3_292 : subd13_3 [0, 1, -2] = true := by decide +kernel
theorem subd13_3_293 : subd13_3 [0, 1, -1] = true := by decide +kernel
theorem subd13_3_294 : subd13_3 [0, 1, 0] = true := by decide +kernel
theorem subd13_3_295 : subd13_3 [0, 1, 1] = true := by decide +kernel
theorem subd13_3_296 : subd13_3 [0, 1, 2] = true := by decide +kernel
theorem subd13_3_297 : subd13_3 [0, 1, 3] = true := by decide +kernel
theorem subd13_3_298 : subd13_3 [0, 1, 4] = true := by decide +kernel
theorem subd13_3_299 : subd13_3 [0, 1, 5] = true := by decide +kernel
theorem subd13_3_300 : subd13_3 [0, 1, 6] = true := by decide +kernel
theorem subd13_3_301 : subd13_3 [0, 1, 7] = true := by decide +kernel
theorem subd13_3_302 : subd13_3 [0, 1, 8] = true := by decide +kernel
theorem subd13_3_303 : subd13_3 [0, 1, 9] = true := by decide +kernel
theorem subd13_3_304 : subd13_3 [0, 1, 10] = true := by decide +kernel
theorem subd13_3_305 : subd13_3 [0, 1, 11] = true := by decide +kernel
theorem subd13_3_306 : subd13_3 [0, 1, 12] = true := by decide +kernel
theorem subd13_3_307 : subd13_3 [0, 2, -11] = true := by decide +kernel
theorem subd13_3_308 : subd13_3 [0, 2, -10] = true := by decide +kernel
theorem subd13_3_309 : subd13_3 [0, 2, -9] = true := by decide +kernel
theorem subd13_3_310 : subd13_3 [0, 2, -8] = true := by decide +kernel
theorem subd13_3_311 : subd13_3 [0, 2, -7] = true := by decide +kernel
theorem subd13_3_312 : subd13_3 [0, 2, -6] = true := by decide +kernel
theorem subd13_3_313 : subd13_3 [0, 2, -5] = true := by decide +kernel
theorem subd13_3_314 : subd13_3 [0, 2, -4] = true := by decide +kernel
theorem subd13_3_315 : subd13_3 [0, 2, -3] = true := by decide +kernel
theorem subd13_3_316 : subd13_3 [0, 2, -2] = true := by decide +kernel
theorem subd13_3_317 : subd13_3 [0, 2, -1] = true := by decide +kernel
theorem subd13_3_318 : subd13_3 [0, 2, 0] = true := by decide +kernel
theorem subd13_3_319 : subd13_3 [0, 2, 1] = true := by decide +kernel
theorem sbd13_3_9 : ∀ q ∈ blkd13_3_9, subd13_3 q = true := by
  unfold blkd13_3_9
  exact List.forall_mem_cons.2 ⟨subd13_3_288, List.forall_mem_cons.2 ⟨subd13_3_289, List.forall_mem_cons.2 ⟨subd13_3_290, List.forall_mem_cons.2 ⟨subd13_3_291, List.forall_mem_cons.2 ⟨subd13_3_292, List.forall_mem_cons.2 ⟨subd13_3_293, List.forall_mem_cons.2 ⟨subd13_3_294, List.forall_mem_cons.2 ⟨subd13_3_295, List.forall_mem_cons.2 ⟨subd13_3_296, List.forall_mem_cons.2 ⟨subd13_3_297, List.forall_mem_cons.2 ⟨subd13_3_298, List.forall_mem_cons.2 ⟨subd13_3_299, List.forall_mem_cons.2 ⟨subd13_3_300, List.forall_mem_cons.2 ⟨subd13_3_301, List.forall_mem_cons.2 ⟨subd13_3_302, List.forall_mem_cons.2 ⟨subd13_3_303, List.forall_mem_cons.2 ⟨subd13_3_304, List.forall_mem_cons.2 ⟨subd13_3_305, List.forall_mem_cons.2 ⟨subd13_3_306, List.forall_mem_cons.2 ⟨subd13_3_307, List.forall_mem_cons.2 ⟨subd13_3_308, List.forall_mem_cons.2 ⟨subd13_3_309, List.forall_mem_cons.2 ⟨subd13_3_310, List.forall_mem_cons.2 ⟨subd13_3_311, List.forall_mem_cons.2 ⟨subd13_3_312, List.forall_mem_cons.2 ⟨subd13_3_313, List.forall_mem_cons.2 ⟨subd13_3_314, List.forall_mem_cons.2 ⟨subd13_3_315, List.forall_mem_cons.2 ⟨subd13_3_316, List.forall_mem_cons.2 ⟨subd13_3_317, List.forall_mem_cons.2 ⟨subd13_3_318, List.forall_mem_cons.2 ⟨subd13_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_320 : subd13_3 [0, 2, 2] = true := by decide +kernel
theorem subd13_3_321 : subd13_3 [0, 2, 3] = true := by decide +kernel
theorem subd13_3_322 : subd13_3 [0, 2, 4] = true := by decide +kernel
theorem subd13_3_323 : subd13_3 [0, 2, 5] = true := by decide +kernel
theorem subd13_3_324 : subd13_3 [0, 2, 6] = true := by decide +kernel
theorem subd13_3_325 : subd13_3 [0, 2, 7] = true := by decide +kernel
theorem subd13_3_326 : subd13_3 [0, 2, 8] = true := by decide +kernel
theorem subd13_3_327 : subd13_3 [0, 2, 9] = true := by decide +kernel
theorem subd13_3_328 : subd13_3 [0, 2, 10] = true := by decide +kernel
theorem subd13_3_329 : subd13_3 [0, 3] = true := by decide +kernel
theorem subd13_3_330 : subd13_3 [1, -4] = true := by decide +kernel
theorem subd13_3_331 : subd13_3 [1, -3] = true := by decide +kernel
theorem subd13_3_332 : subd13_3 [1, -2, -11] = true := by decide +kernel
theorem subd13_3_333 : subd13_3 [1, -2, -10] = true := by decide +kernel
theorem subd13_3_334 : subd13_3 [1, -2, -9] = true := by decide +kernel
theorem subd13_3_335 : subd13_3 [1, -2, -8] = true := by decide +kernel
theorem subd13_3_336 : subd13_3 [1, -2, -7] = true := by decide +kernel
theorem subd13_3_337 : subd13_3 [1, -2, -6] = true := by decide +kernel
theorem subd13_3_338 : subd13_3 [1, -2, -5] = true := by decide +kernel
theorem subd13_3_339 : subd13_3 [1, -2, -4] = true := by decide +kernel
theorem subd13_3_340 : subd13_3 [1, -2, -3] = true := by decide +kernel
theorem subd13_3_341 : subd13_3 [1, -2, -2] = true := by decide +kernel
theorem subd13_3_342 : subd13_3 [1, -2, -1] = true := by decide +kernel
theorem subd13_3_343 : subd13_3 [1, -2, 0] = true := by decide +kernel
theorem subd13_3_344 : subd13_3 [1, -2, 1] = true := by decide +kernel
theorem subd13_3_345 : subd13_3 [1, -2, 2] = true := by decide +kernel
theorem subd13_3_346 : subd13_3 [1, -2, 3] = true := by decide +kernel
theorem subd13_3_347 : subd13_3 [1, -2, 4] = true := by decide +kernel
theorem subd13_3_348 : subd13_3 [1, -2, 5] = true := by decide +kernel
theorem subd13_3_349 : subd13_3 [1, -2, 6] = true := by decide +kernel
theorem subd13_3_350 : subd13_3 [1, -2, 7] = true := by decide +kernel
theorem subd13_3_351 : subd13_3 [1, -2, 8] = true := by decide +kernel
theorem sbd13_3_10 : ∀ q ∈ blkd13_3_10, subd13_3 q = true := by
  unfold blkd13_3_10
  exact List.forall_mem_cons.2 ⟨subd13_3_320, List.forall_mem_cons.2 ⟨subd13_3_321, List.forall_mem_cons.2 ⟨subd13_3_322, List.forall_mem_cons.2 ⟨subd13_3_323, List.forall_mem_cons.2 ⟨subd13_3_324, List.forall_mem_cons.2 ⟨subd13_3_325, List.forall_mem_cons.2 ⟨subd13_3_326, List.forall_mem_cons.2 ⟨subd13_3_327, List.forall_mem_cons.2 ⟨subd13_3_328, List.forall_mem_cons.2 ⟨subd13_3_329, List.forall_mem_cons.2 ⟨subd13_3_330, List.forall_mem_cons.2 ⟨subd13_3_331, List.forall_mem_cons.2 ⟨subd13_3_332, List.forall_mem_cons.2 ⟨subd13_3_333, List.forall_mem_cons.2 ⟨subd13_3_334, List.forall_mem_cons.2 ⟨subd13_3_335, List.forall_mem_cons.2 ⟨subd13_3_336, List.forall_mem_cons.2 ⟨subd13_3_337, List.forall_mem_cons.2 ⟨subd13_3_338, List.forall_mem_cons.2 ⟨subd13_3_339, List.forall_mem_cons.2 ⟨subd13_3_340, List.forall_mem_cons.2 ⟨subd13_3_341, List.forall_mem_cons.2 ⟨subd13_3_342, List.forall_mem_cons.2 ⟨subd13_3_343, List.forall_mem_cons.2 ⟨subd13_3_344, List.forall_mem_cons.2 ⟨subd13_3_345, List.forall_mem_cons.2 ⟨subd13_3_346, List.forall_mem_cons.2 ⟨subd13_3_347, List.forall_mem_cons.2 ⟨subd13_3_348, List.forall_mem_cons.2 ⟨subd13_3_349, List.forall_mem_cons.2 ⟨subd13_3_350, List.forall_mem_cons.2 ⟨subd13_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_352 : subd13_3 [1, -2, 9] = true := by decide +kernel
theorem subd13_3_353 : subd13_3 [1, -1, -13] = true := by decide +kernel
theorem subd13_3_354 : subd13_3 [1, -1, -12] = true := by decide +kernel
theorem subd13_3_355 : subd13_3 [1, -1, -11] = true := by decide +kernel
theorem subd13_3_356 : subd13_3 [1, -1, -10] = true := by decide +kernel
theorem subd13_3_357 : subd13_3 [1, -1, -9] = true := by decide +kernel
theorem subd13_3_358 : subd13_3 [1, -1, -8] = true := by decide +kernel
theorem subd13_3_359 : subd13_3 [1, -1, -7] = true := by decide +kernel
theorem subd13_3_360 : subd13_3 [1, -1, -6] = true := by decide +kernel
theorem subd13_3_361 : subd13_3 [1, -1, -5] = true := by decide +kernel
theorem subd13_3_362 : subd13_3 [1, -1, -4] = true := by decide +kernel
theorem subd13_3_363 : subd13_3 [1, -1, -3] = true := by decide +kernel
theorem subd13_3_364 : subd13_3 [1, -1, -2] = true := by decide +kernel
theorem subd13_3_365 : subd13_3 [1, -1, -1] = true := by decide +kernel
theorem subd13_3_366 : subd13_3 [1, -1, 0] = true := by decide +kernel
theorem subd13_3_367 : subd13_3 [1, -1, 1] = true := by decide +kernel
theorem subd13_3_368 : subd13_3 [1, -1, 2] = true := by decide +kernel
theorem subd13_3_369 : subd13_3 [1, -1, 3] = true := by decide +kernel
theorem subd13_3_370 : subd13_3 [1, -1, 4] = true := by decide +kernel
theorem subd13_3_371 : subd13_3 [1, -1, 5] = true := by decide +kernel
theorem subd13_3_372 : subd13_3 [1, -1, 6] = true := by decide +kernel
theorem subd13_3_373 : subd13_3 [1, -1, 7] = true := by decide +kernel
theorem subd13_3_374 : subd13_3 [1, -1, 8] = true := by decide +kernel
theorem subd13_3_375 : subd13_3 [1, -1, 9] = true := by decide +kernel
theorem subd13_3_376 : subd13_3 [1, -1, 10] = true := by decide +kernel
theorem subd13_3_377 : subd13_3 [1, -1, 11] = true := by decide +kernel
theorem subd13_3_378 : subd13_3 [1, -1, 12] = true := by decide +kernel
theorem subd13_3_379 : subd13_3 [1, 0, -14] = true := by decide +kernel
theorem subd13_3_380 : subd13_3 [1, 0, -13] = true := by decide +kernel
theorem subd13_3_381 : subd13_3 [1, 0, -12] = true := by decide +kernel
theorem subd13_3_382 : subd13_3 [1, 0, -11] = true := by decide +kernel
theorem subd13_3_383 : subd13_3 [1, 0, -10] = true := by decide +kernel
theorem sbd13_3_11 : ∀ q ∈ blkd13_3_11, subd13_3 q = true := by
  unfold blkd13_3_11
  exact List.forall_mem_cons.2 ⟨subd13_3_352, List.forall_mem_cons.2 ⟨subd13_3_353, List.forall_mem_cons.2 ⟨subd13_3_354, List.forall_mem_cons.2 ⟨subd13_3_355, List.forall_mem_cons.2 ⟨subd13_3_356, List.forall_mem_cons.2 ⟨subd13_3_357, List.forall_mem_cons.2 ⟨subd13_3_358, List.forall_mem_cons.2 ⟨subd13_3_359, List.forall_mem_cons.2 ⟨subd13_3_360, List.forall_mem_cons.2 ⟨subd13_3_361, List.forall_mem_cons.2 ⟨subd13_3_362, List.forall_mem_cons.2 ⟨subd13_3_363, List.forall_mem_cons.2 ⟨subd13_3_364, List.forall_mem_cons.2 ⟨subd13_3_365, List.forall_mem_cons.2 ⟨subd13_3_366, List.forall_mem_cons.2 ⟨subd13_3_367, List.forall_mem_cons.2 ⟨subd13_3_368, List.forall_mem_cons.2 ⟨subd13_3_369, List.forall_mem_cons.2 ⟨subd13_3_370, List.forall_mem_cons.2 ⟨subd13_3_371, List.forall_mem_cons.2 ⟨subd13_3_372, List.forall_mem_cons.2 ⟨subd13_3_373, List.forall_mem_cons.2 ⟨subd13_3_374, List.forall_mem_cons.2 ⟨subd13_3_375, List.forall_mem_cons.2 ⟨subd13_3_376, List.forall_mem_cons.2 ⟨subd13_3_377, List.forall_mem_cons.2 ⟨subd13_3_378, List.forall_mem_cons.2 ⟨subd13_3_379, List.forall_mem_cons.2 ⟨subd13_3_380, List.forall_mem_cons.2 ⟨subd13_3_381, List.forall_mem_cons.2 ⟨subd13_3_382, List.forall_mem_cons.2 ⟨subd13_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
