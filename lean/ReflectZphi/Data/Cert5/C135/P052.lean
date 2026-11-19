import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_4_0 : subd9_4 [-7] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [-6, -5] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [-6, -4] = true := by decide +kernel
theorem subd9_4_3 : subd9_4 [-6, -3] = true := by decide +kernel
theorem subd9_4_4 : subd9_4 [-6, -2] = true := by decide +kernel
theorem subd9_4_5 : subd9_4 [-6, -1] = true := by decide +kernel
theorem subd9_4_6 : subd9_4 [-6, 0] = true := by decide +kernel
theorem subd9_4_7 : subd9_4 [-6, 1] = true := by decide +kernel
theorem subd9_4_8 : subd9_4 [-6, 2] = true := by decide +kernel
theorem subd9_4_9 : subd9_4 [-6, 3] = true := by decide +kernel
theorem subd9_4_10 : subd9_4 [-5, -6] = true := by decide +kernel
theorem subd9_4_11 : subd9_4 [-5, -5] = true := by decide +kernel
theorem subd9_4_12 : subd9_4 [-5, -4] = true := by decide +kernel
theorem subd9_4_13 : subd9_4 [-5, -3] = true := by decide +kernel
theorem subd9_4_14 : subd9_4 [-5, -2] = true := by decide +kernel
theorem subd9_4_15 : subd9_4 [-5, -1] = true := by decide +kernel
theorem subd9_4_16 : subd9_4 [-5, 0] = true := by decide +kernel
theorem subd9_4_17 : subd9_4 [-5, 1] = true := by decide +kernel
theorem subd9_4_18 : subd9_4 [-5, 2] = true := by decide +kernel
theorem subd9_4_19 : subd9_4 [-5, 3] = true := by decide +kernel
theorem subd9_4_20 : subd9_4 [-5, 4] = true := by decide +kernel
theorem subd9_4_21 : subd9_4 [-4, -6] = true := by decide +kernel
theorem subd9_4_22 : subd9_4 [-4, -5] = true := by decide +kernel
theorem subd9_4_23 : subd9_4 [-4, -4] = true := by decide +kernel
theorem subd9_4_24 : subd9_4 [-4, -3] = true := by decide +kernel
theorem subd9_4_25 : subd9_4 [-4, -2] = true := by decide +kernel
theorem subd9_4_26 : subd9_4 [-4, -1] = true := by decide +kernel
theorem subd9_4_27 : subd9_4 [-4, 0, -9] = true := by decide +kernel
theorem subd9_4_28 : subd9_4 [-4, 0, -8] = true := by decide +kernel
theorem subd9_4_29 : subd9_4 [-4, 0, -7] = true := by decide +kernel
theorem subd9_4_30 : subd9_4 [-4, 0, -6] = true := by decide +kernel
theorem subd9_4_31 : subd9_4 [-4, 0, -5] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_cons.2 ⟨subd9_4_3, List.forall_mem_cons.2 ⟨subd9_4_4, List.forall_mem_cons.2 ⟨subd9_4_5, List.forall_mem_cons.2 ⟨subd9_4_6, List.forall_mem_cons.2 ⟨subd9_4_7, List.forall_mem_cons.2 ⟨subd9_4_8, List.forall_mem_cons.2 ⟨subd9_4_9, List.forall_mem_cons.2 ⟨subd9_4_10, List.forall_mem_cons.2 ⟨subd9_4_11, List.forall_mem_cons.2 ⟨subd9_4_12, List.forall_mem_cons.2 ⟨subd9_4_13, List.forall_mem_cons.2 ⟨subd9_4_14, List.forall_mem_cons.2 ⟨subd9_4_15, List.forall_mem_cons.2 ⟨subd9_4_16, List.forall_mem_cons.2 ⟨subd9_4_17, List.forall_mem_cons.2 ⟨subd9_4_18, List.forall_mem_cons.2 ⟨subd9_4_19, List.forall_mem_cons.2 ⟨subd9_4_20, List.forall_mem_cons.2 ⟨subd9_4_21, List.forall_mem_cons.2 ⟨subd9_4_22, List.forall_mem_cons.2 ⟨subd9_4_23, List.forall_mem_cons.2 ⟨subd9_4_24, List.forall_mem_cons.2 ⟨subd9_4_25, List.forall_mem_cons.2 ⟨subd9_4_26, List.forall_mem_cons.2 ⟨subd9_4_27, List.forall_mem_cons.2 ⟨subd9_4_28, List.forall_mem_cons.2 ⟨subd9_4_29, List.forall_mem_cons.2 ⟨subd9_4_30, List.forall_mem_cons.2 ⟨subd9_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_32 : subd9_4 [-4, 0, -4] = true := by decide +kernel
theorem subd9_4_33 : subd9_4 [-4, 0, -3] = true := by decide +kernel
theorem subd9_4_34 : subd9_4 [-4, 0, -2] = true := by decide +kernel
theorem subd9_4_35 : subd9_4 [-4, 0, -1] = true := by decide +kernel
theorem subd9_4_36 : subd9_4 [-4, 0, 0] = true := by decide +kernel
theorem subd9_4_37 : subd9_4 [-4, 0, 1] = true := by decide +kernel
theorem subd9_4_38 : subd9_4 [-4, 0, 2] = true := by decide +kernel
theorem subd9_4_39 : subd9_4 [-4, 0, 3] = true := by decide +kernel
theorem subd9_4_40 : subd9_4 [-4, 0, 4] = true := by decide +kernel
theorem subd9_4_41 : subd9_4 [-4, 0, 5] = true := by decide +kernel
theorem subd9_4_42 : subd9_4 [-4, 1] = true := by decide +kernel
theorem subd9_4_43 : subd9_4 [-4, 2] = true := by decide +kernel
theorem subd9_4_44 : subd9_4 [-4, 3] = true := by decide +kernel
theorem subd9_4_45 : subd9_4 [-4, 4] = true := by decide +kernel
theorem subd9_4_46 : subd9_4 [-4, 5] = true := by decide +kernel
theorem subd9_4_47 : subd9_4 [-3, -7] = true := by decide +kernel
theorem subd9_4_48 : subd9_4 [-3, -6] = true := by decide +kernel
theorem subd9_4_49 : subd9_4 [-3, -5] = true := by decide +kernel
theorem subd9_4_50 : subd9_4 [-3, -4] = true := by decide +kernel
theorem subd9_4_51 : subd9_4 [-3, -3] = true := by decide +kernel
theorem subd9_4_52 : subd9_4 [-3, -2, -9] = true := by decide +kernel
theorem subd9_4_53 : subd9_4 [-3, -2, -8] = true := by decide +kernel
theorem subd9_4_54 : subd9_4 [-3, -2, -7] = true := by decide +kernel
theorem subd9_4_55 : subd9_4 [-3, -2, -6] = true := by decide +kernel
theorem subd9_4_56 : subd9_4 [-3, -2, -5] = true := by decide +kernel
theorem subd9_4_57 : subd9_4 [-3, -2, -4] = true := by decide +kernel
theorem subd9_4_58 : subd9_4 [-3, -2, -3] = true := by decide +kernel
theorem subd9_4_59 : subd9_4 [-3, -2, -2] = true := by decide +kernel
theorem subd9_4_60 : subd9_4 [-3, -2, -1] = true := by decide +kernel
theorem subd9_4_61 : subd9_4 [-3, -2, 0] = true := by decide +kernel
theorem subd9_4_62 : subd9_4 [-3, -2, 1] = true := by decide +kernel
theorem subd9_4_63 : subd9_4 [-3, -2, 2] = true := by decide +kernel
theorem sbd9_4_1 : ∀ q ∈ blkd9_4_1, subd9_4 q = true := by
  unfold blkd9_4_1
  exact List.forall_mem_cons.2 ⟨subd9_4_32, List.forall_mem_cons.2 ⟨subd9_4_33, List.forall_mem_cons.2 ⟨subd9_4_34, List.forall_mem_cons.2 ⟨subd9_4_35, List.forall_mem_cons.2 ⟨subd9_4_36, List.forall_mem_cons.2 ⟨subd9_4_37, List.forall_mem_cons.2 ⟨subd9_4_38, List.forall_mem_cons.2 ⟨subd9_4_39, List.forall_mem_cons.2 ⟨subd9_4_40, List.forall_mem_cons.2 ⟨subd9_4_41, List.forall_mem_cons.2 ⟨subd9_4_42, List.forall_mem_cons.2 ⟨subd9_4_43, List.forall_mem_cons.2 ⟨subd9_4_44, List.forall_mem_cons.2 ⟨subd9_4_45, List.forall_mem_cons.2 ⟨subd9_4_46, List.forall_mem_cons.2 ⟨subd9_4_47, List.forall_mem_cons.2 ⟨subd9_4_48, List.forall_mem_cons.2 ⟨subd9_4_49, List.forall_mem_cons.2 ⟨subd9_4_50, List.forall_mem_cons.2 ⟨subd9_4_51, List.forall_mem_cons.2 ⟨subd9_4_52, List.forall_mem_cons.2 ⟨subd9_4_53, List.forall_mem_cons.2 ⟨subd9_4_54, List.forall_mem_cons.2 ⟨subd9_4_55, List.forall_mem_cons.2 ⟨subd9_4_56, List.forall_mem_cons.2 ⟨subd9_4_57, List.forall_mem_cons.2 ⟨subd9_4_58, List.forall_mem_cons.2 ⟨subd9_4_59, List.forall_mem_cons.2 ⟨subd9_4_60, List.forall_mem_cons.2 ⟨subd9_4_61, List.forall_mem_cons.2 ⟨subd9_4_62, List.forall_mem_cons.2 ⟨subd9_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_64 : subd9_4 [-3, -2, 3] = true := by decide +kernel
theorem subd9_4_65 : subd9_4 [-3, -2, 4] = true := by decide +kernel
theorem subd9_4_66 : subd9_4 [-3, -2, 5] = true := by decide +kernel
theorem subd9_4_67 : subd9_4 [-3, -1, -9] = true := by decide +kernel
theorem subd9_4_68 : subd9_4 [-3, -1, -8] = true := by decide +kernel
theorem subd9_4_69 : subd9_4 [-3, -1, -7] = true := by decide +kernel
theorem subd9_4_70 : subd9_4 [-3, -1, -6] = true := by decide +kernel
theorem subd9_4_71 : subd9_4 [-3, -1, -5] = true := by decide +kernel
theorem subd9_4_72 : subd9_4 [-3, -1, -4] = true := by decide +kernel
theorem subd9_4_73 : subd9_4 [-3, -1, -3] = true := by decide +kernel
theorem subd9_4_74 : subd9_4 [-3, -1, -2] = true := by decide +kernel
theorem subd9_4_75 : subd9_4 [-3, -1, -1] = true := by decide +kernel
theorem subd9_4_76 : subd9_4 [-3, -1, 0] = true := by decide +kernel
theorem subd9_4_77 : subd9_4 [-3, -1, 1] = true := by decide +kernel
theorem subd9_4_78 : subd9_4 [-3, -1, 2] = true := by decide +kernel
theorem subd9_4_79 : subd9_4 [-3, -1, 3] = true := by decide +kernel
theorem subd9_4_80 : subd9_4 [-3, -1, 4] = true := by decide +kernel
theorem subd9_4_81 : subd9_4 [-3, -1, 5] = true := by decide +kernel
theorem subd9_4_82 : subd9_4 [-3, -1, 6] = true := by decide +kernel
theorem subd9_4_83 : subd9_4 [-3, 0, -9] = true := by decide +kernel
theorem subd9_4_84 : subd9_4 [-3, 0, -8] = true := by decide +kernel
theorem subd9_4_85 : subd9_4 [-3, 0, -7] = true := by decide +kernel
theorem subd9_4_86 : subd9_4 [-3, 0, -6] = true := by decide +kernel
theorem subd9_4_87 : subd9_4 [-3, 0, -5] = true := by decide +kernel
theorem subd9_4_88 : subd9_4 [-3, 0, -4] = true := by decide +kernel
theorem subd9_4_89 : subd9_4 [-3, 0, -3] = true := by decide +kernel
theorem subd9_4_90 : subd9_4 [-3, 0, -2] = true := by decide +kernel
theorem subd9_4_91 : subd9_4 [-3, 0, -1] = true := by decide +kernel
theorem subd9_4_92 : subd9_4 [-3, 0, 0] = true := by decide +kernel
theorem subd9_4_93 : subd9_4 [-3, 0, 1] = true := by decide +kernel
theorem subd9_4_94 : subd9_4 [-3, 0, 2] = true := by decide +kernel
theorem subd9_4_95 : subd9_4 [-3, 0, 3] = true := by decide +kernel
theorem sbd9_4_2 : ∀ q ∈ blkd9_4_2, subd9_4 q = true := by
  unfold blkd9_4_2
  exact List.forall_mem_cons.2 ⟨subd9_4_64, List.forall_mem_cons.2 ⟨subd9_4_65, List.forall_mem_cons.2 ⟨subd9_4_66, List.forall_mem_cons.2 ⟨subd9_4_67, List.forall_mem_cons.2 ⟨subd9_4_68, List.forall_mem_cons.2 ⟨subd9_4_69, List.forall_mem_cons.2 ⟨subd9_4_70, List.forall_mem_cons.2 ⟨subd9_4_71, List.forall_mem_cons.2 ⟨subd9_4_72, List.forall_mem_cons.2 ⟨subd9_4_73, List.forall_mem_cons.2 ⟨subd9_4_74, List.forall_mem_cons.2 ⟨subd9_4_75, List.forall_mem_cons.2 ⟨subd9_4_76, List.forall_mem_cons.2 ⟨subd9_4_77, List.forall_mem_cons.2 ⟨subd9_4_78, List.forall_mem_cons.2 ⟨subd9_4_79, List.forall_mem_cons.2 ⟨subd9_4_80, List.forall_mem_cons.2 ⟨subd9_4_81, List.forall_mem_cons.2 ⟨subd9_4_82, List.forall_mem_cons.2 ⟨subd9_4_83, List.forall_mem_cons.2 ⟨subd9_4_84, List.forall_mem_cons.2 ⟨subd9_4_85, List.forall_mem_cons.2 ⟨subd9_4_86, List.forall_mem_cons.2 ⟨subd9_4_87, List.forall_mem_cons.2 ⟨subd9_4_88, List.forall_mem_cons.2 ⟨subd9_4_89, List.forall_mem_cons.2 ⟨subd9_4_90, List.forall_mem_cons.2 ⟨subd9_4_91, List.forall_mem_cons.2 ⟨subd9_4_92, List.forall_mem_cons.2 ⟨subd9_4_93, List.forall_mem_cons.2 ⟨subd9_4_94, List.forall_mem_cons.2 ⟨subd9_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_96 : subd9_4 [-3, 0, 4] = true := by decide +kernel
theorem subd9_4_97 : subd9_4 [-3, 0, 5] = true := by decide +kernel
theorem subd9_4_98 : subd9_4 [-3, 0, 6] = true := by decide +kernel
theorem subd9_4_99 : subd9_4 [-3, 1, -9] = true := by decide +kernel
theorem subd9_4_100 : subd9_4 [-3, 1, -8] = true := by decide +kernel
theorem subd9_4_101 : subd9_4 [-3, 1, -7] = true := by decide +kernel
theorem subd9_4_102 : subd9_4 [-3, 1, -6] = true := by decide +kernel
theorem subd9_4_103 : subd9_4 [-3, 1, -5] = true := by decide +kernel
theorem subd9_4_104 : subd9_4 [-3, 1, -4] = true := by decide +kernel
theorem subd9_4_105 : subd9_4 [-3, 1, -3] = true := by decide +kernel
theorem subd9_4_106 : subd9_4 [-3, 1, -2] = true := by decide +kernel
theorem subd9_4_107 : subd9_4 [-3, 1, -1] = true := by decide +kernel
theorem subd9_4_108 : subd9_4 [-3, 1, 0] = true := by decide +kernel
theorem subd9_4_109 : subd9_4 [-3, 1, 1] = true := by decide +kernel
theorem subd9_4_110 : subd9_4 [-3, 1, 2] = true := by decide +kernel
theorem subd9_4_111 : subd9_4 [-3, 1, 3] = true := by decide +kernel
theorem subd9_4_112 : subd9_4 [-3, 1, 4] = true := by decide +kernel
theorem subd9_4_113 : subd9_4 [-3, 1, 5] = true := by decide +kernel
theorem subd9_4_114 : subd9_4 [-3, 1, 6] = true := by decide +kernel
theorem subd9_4_115 : subd9_4 [-3, 2] = true := by decide +kernel
theorem subd9_4_116 : subd9_4 [-3, 3] = true := by decide +kernel
theorem subd9_4_117 : subd9_4 [-3, 4] = true := by decide +kernel
theorem subd9_4_118 : subd9_4 [-3, 5] = true := by decide +kernel
theorem subd9_4_119 : subd9_4 [-2, -7] = true := by decide +kernel
theorem subd9_4_120 : subd9_4 [-2, -6] = true := by decide +kernel
theorem subd9_4_121 : subd9_4 [-2, -5] = true := by decide +kernel
theorem subd9_4_122 : subd9_4 [-2, -4] = true := by decide +kernel
theorem subd9_4_123 : subd9_4 [-2, -3] = true := by decide +kernel
theorem subd9_4_124 : subd9_4 [-2, -2, -9] = true := by decide +kernel
theorem subd9_4_125 : subd9_4 [-2, -2, -8] = true := by decide +kernel
theorem subd9_4_126 : subd9_4 [-2, -2, -7] = true := by decide +kernel
theorem subd9_4_127 : subd9_4 [-2, -2, -6] = true := by decide +kernel
theorem sbd9_4_3 : ∀ q ∈ blkd9_4_3, subd9_4 q = true := by
  unfold blkd9_4_3
  exact List.forall_mem_cons.2 ⟨subd9_4_96, List.forall_mem_cons.2 ⟨subd9_4_97, List.forall_mem_cons.2 ⟨subd9_4_98, List.forall_mem_cons.2 ⟨subd9_4_99, List.forall_mem_cons.2 ⟨subd9_4_100, List.forall_mem_cons.2 ⟨subd9_4_101, List.forall_mem_cons.2 ⟨subd9_4_102, List.forall_mem_cons.2 ⟨subd9_4_103, List.forall_mem_cons.2 ⟨subd9_4_104, List.forall_mem_cons.2 ⟨subd9_4_105, List.forall_mem_cons.2 ⟨subd9_4_106, List.forall_mem_cons.2 ⟨subd9_4_107, List.forall_mem_cons.2 ⟨subd9_4_108, List.forall_mem_cons.2 ⟨subd9_4_109, List.forall_mem_cons.2 ⟨subd9_4_110, List.forall_mem_cons.2 ⟨subd9_4_111, List.forall_mem_cons.2 ⟨subd9_4_112, List.forall_mem_cons.2 ⟨subd9_4_113, List.forall_mem_cons.2 ⟨subd9_4_114, List.forall_mem_cons.2 ⟨subd9_4_115, List.forall_mem_cons.2 ⟨subd9_4_116, List.forall_mem_cons.2 ⟨subd9_4_117, List.forall_mem_cons.2 ⟨subd9_4_118, List.forall_mem_cons.2 ⟨subd9_4_119, List.forall_mem_cons.2 ⟨subd9_4_120, List.forall_mem_cons.2 ⟨subd9_4_121, List.forall_mem_cons.2 ⟨subd9_4_122, List.forall_mem_cons.2 ⟨subd9_4_123, List.forall_mem_cons.2 ⟨subd9_4_124, List.forall_mem_cons.2 ⟨subd9_4_125, List.forall_mem_cons.2 ⟨subd9_4_126, List.forall_mem_cons.2 ⟨subd9_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_128 : subd9_4 [-2, -2, -5] = true := by decide +kernel
theorem subd9_4_129 : subd9_4 [-2, -2, -4] = true := by decide +kernel
theorem subd9_4_130 : subd9_4 [-2, -2, -3] = true := by decide +kernel
theorem subd9_4_131 : subd9_4 [-2, -2, -2] = true := by decide +kernel
theorem subd9_4_132 : subd9_4 [-2, -2, -1] = true := by decide +kernel
theorem subd9_4_133 : subd9_4 [-2, -2, 0] = true := by decide +kernel
theorem subd9_4_134 : subd9_4 [-2, -2, 1] = true := by decide +kernel
theorem subd9_4_135 : subd9_4 [-2, -2, 2] = true := by decide +kernel
theorem subd9_4_136 : subd9_4 [-2, -2, 3] = true := by decide +kernel
theorem subd9_4_137 : subd9_4 [-2, -2, 4] = true := by decide +kernel
theorem subd9_4_138 : subd9_4 [-2, -2, 5] = true := by decide +kernel
theorem subd9_4_139 : subd9_4 [-2, -2, 6] = true := by decide +kernel
theorem subd9_4_140 : subd9_4 [-2, -1, -9] = true := by decide +kernel
theorem subd9_4_141 : subd9_4 [-2, -1, -8] = true := by decide +kernel
theorem subd9_4_142 : subd9_4 [-2, -1, -7] = true := by decide +kernel
theorem subd9_4_143 : subd9_4 [-2, -1, -6] = true := by decide +kernel
theorem subd9_4_144 : subd9_4 [-2, -1, -5] = true := by decide +kernel
theorem subd9_4_145 : subd9_4 [-2, -1, -4] = true := by decide +kernel
theorem subd9_4_146 : subd9_4 [-2, -1, -3] = true := by decide +kernel
theorem subd9_4_147 : subd9_4 [-2, -1, -2] = true := by decide +kernel
theorem subd9_4_148 : subd9_4 [-2, -1, -1] = true := by decide +kernel
theorem subd9_4_149 : subd9_4 [-2, -1, 0] = true := by decide +kernel
theorem subd9_4_150 : subd9_4 [-2, -1, 1] = true := by decide +kernel
theorem subd9_4_151 : subd9_4 [-2, -1, 2] = true := by decide +kernel
theorem subd9_4_152 : subd9_4 [-2, -1, 3] = true := by decide +kernel
theorem subd9_4_153 : subd9_4 [-2, -1, 4] = true := by decide +kernel
theorem subd9_4_154 : subd9_4 [-2, -1, 5] = true := by decide +kernel
theorem subd9_4_155 : subd9_4 [-2, -1, 6] = true := by decide +kernel
theorem subd9_4_156 : subd9_4 [-2, 0, -9] = true := by decide +kernel
theorem subd9_4_157 : subd9_4 [-2, 0, -8] = true := by decide +kernel
theorem subd9_4_158 : subd9_4 [-2, 0, -7] = true := by decide +kernel
theorem subd9_4_159 : subd9_4 [-2, 0, -6] = true := by decide +kernel
theorem sbd9_4_4 : ∀ q ∈ blkd9_4_4, subd9_4 q = true := by
  unfold blkd9_4_4
  exact List.forall_mem_cons.2 ⟨subd9_4_128, List.forall_mem_cons.2 ⟨subd9_4_129, List.forall_mem_cons.2 ⟨subd9_4_130, List.forall_mem_cons.2 ⟨subd9_4_131, List.forall_mem_cons.2 ⟨subd9_4_132, List.forall_mem_cons.2 ⟨subd9_4_133, List.forall_mem_cons.2 ⟨subd9_4_134, List.forall_mem_cons.2 ⟨subd9_4_135, List.forall_mem_cons.2 ⟨subd9_4_136, List.forall_mem_cons.2 ⟨subd9_4_137, List.forall_mem_cons.2 ⟨subd9_4_138, List.forall_mem_cons.2 ⟨subd9_4_139, List.forall_mem_cons.2 ⟨subd9_4_140, List.forall_mem_cons.2 ⟨subd9_4_141, List.forall_mem_cons.2 ⟨subd9_4_142, List.forall_mem_cons.2 ⟨subd9_4_143, List.forall_mem_cons.2 ⟨subd9_4_144, List.forall_mem_cons.2 ⟨subd9_4_145, List.forall_mem_cons.2 ⟨subd9_4_146, List.forall_mem_cons.2 ⟨subd9_4_147, List.forall_mem_cons.2 ⟨subd9_4_148, List.forall_mem_cons.2 ⟨subd9_4_149, List.forall_mem_cons.2 ⟨subd9_4_150, List.forall_mem_cons.2 ⟨subd9_4_151, List.forall_mem_cons.2 ⟨subd9_4_152, List.forall_mem_cons.2 ⟨subd9_4_153, List.forall_mem_cons.2 ⟨subd9_4_154, List.forall_mem_cons.2 ⟨subd9_4_155, List.forall_mem_cons.2 ⟨subd9_4_156, List.forall_mem_cons.2 ⟨subd9_4_157, List.forall_mem_cons.2 ⟨subd9_4_158, List.forall_mem_cons.2 ⟨subd9_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_160 : subd9_4 [-2, 0, -5] = true := by decide +kernel
theorem subd9_4_161 : subd9_4 [-2, 0, -4] = true := by decide +kernel
theorem subd9_4_162 : subd9_4 [-2, 0, -3] = true := by decide +kernel
theorem subd9_4_163 : subd9_4 [-2, 0, -2] = true := by decide +kernel
theorem subd9_4_164 : subd9_4 [-2, 0, -1] = true := by decide +kernel
theorem subd9_4_165 : subd9_4 [-2, 0, 0] = true := by decide +kernel
theorem subd9_4_166 : subd9_4 [-2, 0, 1] = true := by decide +kernel
theorem subd9_4_167 : subd9_4 [-2, 0, 2] = true := by decide +kernel
theorem subd9_4_168 : subd9_4 [-2, 0, 3] = true := by decide +kernel
theorem subd9_4_169 : subd9_4 [-2, 0, 4] = true := by decide +kernel
theorem subd9_4_170 : subd9_4 [-2, 0, 5] = true := by decide +kernel
theorem subd9_4_171 : subd9_4 [-2, 0, 6] = true := by decide +kernel
theorem subd9_4_172 : subd9_4 [-2, 1, -9] = true := by decide +kernel
theorem subd9_4_173 : subd9_4 [-2, 1, -8] = true := by decide +kernel
theorem subd9_4_174 : subd9_4 [-2, 1, -7] = true := by decide +kernel
theorem subd9_4_175 : subd9_4 [-2, 1, -6] = true := by decide +kernel
theorem subd9_4_176 : subd9_4 [-2, 1, -5] = true := by decide +kernel
theorem subd9_4_177 : subd9_4 [-2, 1, -4] = true := by decide +kernel
theorem subd9_4_178 : subd9_4 [-2, 1, -3] = true := by decide +kernel
theorem subd9_4_179 : subd9_4 [-2, 1, -2] = true := by decide +kernel
theorem subd9_4_180 : subd9_4 [-2, 1, -1] = true := by decide +kernel
theorem subd9_4_181 : subd9_4 [-2, 1, 0] = true := by decide +kernel
theorem subd9_4_182 : subd9_4 [-2, 1, 1] = true := by decide +kernel
theorem subd9_4_183 : subd9_4 [-2, 1, 2] = true := by decide +kernel
theorem subd9_4_184 : subd9_4 [-2, 1, 3] = true := by decide +kernel
theorem subd9_4_185 : subd9_4 [-2, 1, 4] = true := by decide +kernel
theorem subd9_4_186 : subd9_4 [-2, 1, 5] = true := by decide +kernel
theorem subd9_4_187 : subd9_4 [-2, 1, 6] = true := by decide +kernel
theorem subd9_4_188 : subd9_4 [-2, 2, -8] = true := by decide +kernel
theorem subd9_4_189 : subd9_4 [-2, 2, -7] = true := by decide +kernel
theorem subd9_4_190 : subd9_4 [-2, 2, -6] = true := by decide +kernel
theorem subd9_4_191 : subd9_4 [-2, 2, -5] = true := by decide +kernel
theorem sbd9_4_5 : ∀ q ∈ blkd9_4_5, subd9_4 q = true := by
  unfold blkd9_4_5
  exact List.forall_mem_cons.2 ⟨subd9_4_160, List.forall_mem_cons.2 ⟨subd9_4_161, List.forall_mem_cons.2 ⟨subd9_4_162, List.forall_mem_cons.2 ⟨subd9_4_163, List.forall_mem_cons.2 ⟨subd9_4_164, List.forall_mem_cons.2 ⟨subd9_4_165, List.forall_mem_cons.2 ⟨subd9_4_166, List.forall_mem_cons.2 ⟨subd9_4_167, List.forall_mem_cons.2 ⟨subd9_4_168, List.forall_mem_cons.2 ⟨subd9_4_169, List.forall_mem_cons.2 ⟨subd9_4_170, List.forall_mem_cons.2 ⟨subd9_4_171, List.forall_mem_cons.2 ⟨subd9_4_172, List.forall_mem_cons.2 ⟨subd9_4_173, List.forall_mem_cons.2 ⟨subd9_4_174, List.forall_mem_cons.2 ⟨subd9_4_175, List.forall_mem_cons.2 ⟨subd9_4_176, List.forall_mem_cons.2 ⟨subd9_4_177, List.forall_mem_cons.2 ⟨subd9_4_178, List.forall_mem_cons.2 ⟨subd9_4_179, List.forall_mem_cons.2 ⟨subd9_4_180, List.forall_mem_cons.2 ⟨subd9_4_181, List.forall_mem_cons.2 ⟨subd9_4_182, List.forall_mem_cons.2 ⟨subd9_4_183, List.forall_mem_cons.2 ⟨subd9_4_184, List.forall_mem_cons.2 ⟨subd9_4_185, List.forall_mem_cons.2 ⟨subd9_4_186, List.forall_mem_cons.2 ⟨subd9_4_187, List.forall_mem_cons.2 ⟨subd9_4_188, List.forall_mem_cons.2 ⟨subd9_4_189, List.forall_mem_cons.2 ⟨subd9_4_190, List.forall_mem_cons.2 ⟨subd9_4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_192 : subd9_4 [-2, 2, -4] = true := by decide +kernel
theorem subd9_4_193 : subd9_4 [-2, 2, -3] = true := by decide +kernel
theorem subd9_4_194 : subd9_4 [-2, 2, -2] = true := by decide +kernel
theorem subd9_4_195 : subd9_4 [-2, 2, -1] = true := by decide +kernel
theorem subd9_4_196 : subd9_4 [-2, 2, 0] = true := by decide +kernel
theorem subd9_4_197 : subd9_4 [-2, 2, 1] = true := by decide +kernel
theorem subd9_4_198 : subd9_4 [-2, 2, 2] = true := by decide +kernel
theorem subd9_4_199 : subd9_4 [-2, 2, 3] = true := by decide +kernel
theorem subd9_4_200 : subd9_4 [-2, 2, 4] = true := by decide +kernel
theorem subd9_4_201 : subd9_4 [-2, 2, 5] = true := by decide +kernel
theorem subd9_4_202 : subd9_4 [-2, 2, 6] = true := by decide +kernel
theorem subd9_4_203 : subd9_4 [-2, 3, -8] = true := by decide +kernel
theorem subd9_4_204 : subd9_4 [-2, 3, -7] = true := by decide +kernel
theorem subd9_4_205 : subd9_4 [-2, 3, -6] = true := by decide +kernel
theorem subd9_4_206 : subd9_4 [-2, 3, -5] = true := by decide +kernel
theorem subd9_4_207 : subd9_4 [-2, 3, -4] = true := by decide +kernel
theorem subd9_4_208 : subd9_4 [-2, 3, -3] = true := by decide +kernel
theorem subd9_4_209 : subd9_4 [-2, 3, -2] = true := by decide +kernel
theorem subd9_4_210 : subd9_4 [-2, 3, -1] = true := by decide +kernel
theorem subd9_4_211 : subd9_4 [-2, 3, 0] = true := by decide +kernel
theorem subd9_4_212 : subd9_4 [-2, 3, 1] = true := by decide +kernel
theorem subd9_4_213 : subd9_4 [-2, 3, 2] = true := by decide +kernel
theorem subd9_4_214 : subd9_4 [-2, 3, 3] = true := by decide +kernel
theorem subd9_4_215 : subd9_4 [-2, 3, 4] = true := by decide +kernel
theorem subd9_4_216 : subd9_4 [-2, 3, 5] = true := by decide +kernel
theorem subd9_4_217 : subd9_4 [-2, 3, 6] = true := by decide +kernel
theorem subd9_4_218 : subd9_4 [-2, 4] = true := by decide +kernel
theorem subd9_4_219 : subd9_4 [-2, 5] = true := by decide +kernel
theorem subd9_4_220 : subd9_4 [-2, 6] = true := by decide +kernel
theorem subd9_4_221 : subd9_4 [-1, -7] = true := by decide +kernel
theorem subd9_4_222 : subd9_4 [-1, -6] = true := by decide +kernel
theorem subd9_4_223 : subd9_4 [-1, -5] = true := by decide +kernel
theorem sbd9_4_6 : ∀ q ∈ blkd9_4_6, subd9_4 q = true := by
  unfold blkd9_4_6
  exact List.forall_mem_cons.2 ⟨subd9_4_192, List.forall_mem_cons.2 ⟨subd9_4_193, List.forall_mem_cons.2 ⟨subd9_4_194, List.forall_mem_cons.2 ⟨subd9_4_195, List.forall_mem_cons.2 ⟨subd9_4_196, List.forall_mem_cons.2 ⟨subd9_4_197, List.forall_mem_cons.2 ⟨subd9_4_198, List.forall_mem_cons.2 ⟨subd9_4_199, List.forall_mem_cons.2 ⟨subd9_4_200, List.forall_mem_cons.2 ⟨subd9_4_201, List.forall_mem_cons.2 ⟨subd9_4_202, List.forall_mem_cons.2 ⟨subd9_4_203, List.forall_mem_cons.2 ⟨subd9_4_204, List.forall_mem_cons.2 ⟨subd9_4_205, List.forall_mem_cons.2 ⟨subd9_4_206, List.forall_mem_cons.2 ⟨subd9_4_207, List.forall_mem_cons.2 ⟨subd9_4_208, List.forall_mem_cons.2 ⟨subd9_4_209, List.forall_mem_cons.2 ⟨subd9_4_210, List.forall_mem_cons.2 ⟨subd9_4_211, List.forall_mem_cons.2 ⟨subd9_4_212, List.forall_mem_cons.2 ⟨subd9_4_213, List.forall_mem_cons.2 ⟨subd9_4_214, List.forall_mem_cons.2 ⟨subd9_4_215, List.forall_mem_cons.2 ⟨subd9_4_216, List.forall_mem_cons.2 ⟨subd9_4_217, List.forall_mem_cons.2 ⟨subd9_4_218, List.forall_mem_cons.2 ⟨subd9_4_219, List.forall_mem_cons.2 ⟨subd9_4_220, List.forall_mem_cons.2 ⟨subd9_4_221, List.forall_mem_cons.2 ⟨subd9_4_222, List.forall_mem_cons.2 ⟨subd9_4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_224 : subd9_4 [-1, -4] = true := by decide +kernel
theorem subd9_4_225 : subd9_4 [-1, -3, -8] = true := by decide +kernel
theorem subd9_4_226 : subd9_4 [-1, -3, -7] = true := by decide +kernel
theorem subd9_4_227 : subd9_4 [-1, -3, -6] = true := by decide +kernel
theorem subd9_4_228 : subd9_4 [-1, -3, -5] = true := by decide +kernel
theorem subd9_4_229 : subd9_4 [-1, -3, -4] = true := by decide +kernel
theorem subd9_4_230 : subd9_4 [-1, -3, -3] = true := by decide +kernel
theorem subd9_4_231 : subd9_4 [-1, -3, -2] = true := by decide +kernel
theorem subd9_4_232 : subd9_4 [-1, -3, -1] = true := by decide +kernel
theorem subd9_4_233 : subd9_4 [-1, -3, 0] = true := by decide +kernel
theorem subd9_4_234 : subd9_4 [-1, -3, 1] = true := by decide +kernel
theorem subd9_4_235 : subd9_4 [-1, -3, 2] = true := by decide +kernel
theorem subd9_4_236 : subd9_4 [-1, -3, 3] = true := by decide +kernel
theorem subd9_4_237 : subd9_4 [-1, -3, 4] = true := by decide +kernel
theorem subd9_4_238 : subd9_4 [-1, -3, 5] = true := by decide +kernel
theorem subd9_4_239 : subd9_4 [-1, -3, 6] = true := by decide +kernel
theorem subd9_4_240 : subd9_4 [-1, -2, -9] = true := by decide +kernel
theorem subd9_4_241 : subd9_4 [-1, -2, -8] = true := by decide +kernel
theorem subd9_4_242 : subd9_4 [-1, -2, -7] = true := by decide +kernel
theorem subd9_4_243 : subd9_4 [-1, -2, -6] = true := by decide +kernel
theorem subd9_4_244 : subd9_4 [-1, -2, -5] = true := by decide +kernel
theorem subd9_4_245 : subd9_4 [-1, -2, -4] = true := by decide +kernel
theorem subd9_4_246 : subd9_4 [-1, -2, -3] = true := by decide +kernel
theorem subd9_4_247 : subd9_4 [-1, -2, -2] = true := by decide +kernel
theorem subd9_4_248 : subd9_4 [-1, -2, -1] = true := by decide +kernel
theorem subd9_4_249 : subd9_4 [-1, -2, 0] = true := by decide +kernel
theorem subd9_4_250 : subd9_4 [-1, -2, 1] = true := by decide +kernel
theorem subd9_4_251 : subd9_4 [-1, -2, 2] = true := by decide +kernel
theorem subd9_4_252 : subd9_4 [-1, -2, 3] = true := by decide +kernel
theorem subd9_4_253 : subd9_4 [-1, -2, 4] = true := by decide +kernel
theorem subd9_4_254 : subd9_4 [-1, -2, 5] = true := by decide +kernel
theorem subd9_4_255 : subd9_4 [-1, -2, 6] = true := by decide +kernel
theorem sbd9_4_7 : ∀ q ∈ blkd9_4_7, subd9_4 q = true := by
  unfold blkd9_4_7
  exact List.forall_mem_cons.2 ⟨subd9_4_224, List.forall_mem_cons.2 ⟨subd9_4_225, List.forall_mem_cons.2 ⟨subd9_4_226, List.forall_mem_cons.2 ⟨subd9_4_227, List.forall_mem_cons.2 ⟨subd9_4_228, List.forall_mem_cons.2 ⟨subd9_4_229, List.forall_mem_cons.2 ⟨subd9_4_230, List.forall_mem_cons.2 ⟨subd9_4_231, List.forall_mem_cons.2 ⟨subd9_4_232, List.forall_mem_cons.2 ⟨subd9_4_233, List.forall_mem_cons.2 ⟨subd9_4_234, List.forall_mem_cons.2 ⟨subd9_4_235, List.forall_mem_cons.2 ⟨subd9_4_236, List.forall_mem_cons.2 ⟨subd9_4_237, List.forall_mem_cons.2 ⟨subd9_4_238, List.forall_mem_cons.2 ⟨subd9_4_239, List.forall_mem_cons.2 ⟨subd9_4_240, List.forall_mem_cons.2 ⟨subd9_4_241, List.forall_mem_cons.2 ⟨subd9_4_242, List.forall_mem_cons.2 ⟨subd9_4_243, List.forall_mem_cons.2 ⟨subd9_4_244, List.forall_mem_cons.2 ⟨subd9_4_245, List.forall_mem_cons.2 ⟨subd9_4_246, List.forall_mem_cons.2 ⟨subd9_4_247, List.forall_mem_cons.2 ⟨subd9_4_248, List.forall_mem_cons.2 ⟨subd9_4_249, List.forall_mem_cons.2 ⟨subd9_4_250, List.forall_mem_cons.2 ⟨subd9_4_251, List.forall_mem_cons.2 ⟨subd9_4_252, List.forall_mem_cons.2 ⟨subd9_4_253, List.forall_mem_cons.2 ⟨subd9_4_254, List.forall_mem_cons.2 ⟨subd9_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_256 : subd9_4 [-1, -2, 7] = true := by decide +kernel
theorem subd9_4_257 : subd9_4 [-1, -1, -9] = true := by decide +kernel
theorem subd9_4_258 : subd9_4 [-1, -1, -8] = true := by decide +kernel
theorem subd9_4_259 : subd9_4 [-1, -1, -7] = true := by decide +kernel
theorem subd9_4_260 : subd9_4 [-1, -1, -6] = true := by decide +kernel
theorem subd9_4_261 : subd9_4 [-1, -1, -5] = true := by decide +kernel
theorem subd9_4_262 : subd9_4 [-1, -1, -4] = true := by decide +kernel
theorem subd9_4_263 : subd9_4 [-1, -1, -3] = true := by decide +kernel
theorem subd9_4_264 : subd9_4 [-1, -1, -2] = true := by decide +kernel
theorem subd9_4_265 : subd9_4 [-1, -1, -1] = true := by decide +kernel
theorem subd9_4_266 : subd9_4 [-1, -1, 0] = true := by decide +kernel
theorem subd9_4_267 : subd9_4 [-1, -1, 1] = true := by decide +kernel
theorem subd9_4_268 : subd9_4 [-1, -1, 2] = true := by decide +kernel
theorem subd9_4_269 : subd9_4 [-1, -1, 3] = true := by decide +kernel
theorem subd9_4_270 : subd9_4 [-1, -1, 4] = true := by decide +kernel
theorem subd9_4_271 : subd9_4 [-1, -1, 5] = true := by decide +kernel
theorem subd9_4_272 : subd9_4 [-1, -1, 6] = true := by decide +kernel
theorem subd9_4_273 : subd9_4 [-1, -1, 7] = true := by decide +kernel
theorem subd9_4_274 : subd9_4 [-1, 0, -9] = true := by decide +kernel
theorem subd9_4_275 : subd9_4 [-1, 0, -8] = true := by decide +kernel
theorem subd9_4_276 : subd9_4 [-1, 0, -7] = true := by decide +kernel
theorem subd9_4_277 : subd9_4 [-1, 0, -6] = true := by decide +kernel
theorem subd9_4_278 : subd9_4 [-1, 0, -5] = true := by decide +kernel
theorem subd9_4_279 : subd9_4 [-1, 0, -4] = true := by decide +kernel
theorem subd9_4_280 : subd9_4 [-1, 0, -3] = true := by decide +kernel
theorem subd9_4_281 : subd9_4 [-1, 0, -2] = true := by decide +kernel
theorem subd9_4_282 : subd9_4 [-1, 0, -1] = true := by decide +kernel
theorem subd9_4_283 : subd9_4 [-1, 0, 0] = true := by decide +kernel
theorem subd9_4_284 : subd9_4 [-1, 0, 1] = true := by decide +kernel
theorem subd9_4_285 : subd9_4 [-1, 0, 2] = true := by decide +kernel
theorem subd9_4_286 : subd9_4 [-1, 0, 3] = true := by decide +kernel
theorem subd9_4_287 : subd9_4 [-1, 0, 4] = true := by decide +kernel
theorem sbd9_4_8 : ∀ q ∈ blkd9_4_8, subd9_4 q = true := by
  unfold blkd9_4_8
  exact List.forall_mem_cons.2 ⟨subd9_4_256, List.forall_mem_cons.2 ⟨subd9_4_257, List.forall_mem_cons.2 ⟨subd9_4_258, List.forall_mem_cons.2 ⟨subd9_4_259, List.forall_mem_cons.2 ⟨subd9_4_260, List.forall_mem_cons.2 ⟨subd9_4_261, List.forall_mem_cons.2 ⟨subd9_4_262, List.forall_mem_cons.2 ⟨subd9_4_263, List.forall_mem_cons.2 ⟨subd9_4_264, List.forall_mem_cons.2 ⟨subd9_4_265, List.forall_mem_cons.2 ⟨subd9_4_266, List.forall_mem_cons.2 ⟨subd9_4_267, List.forall_mem_cons.2 ⟨subd9_4_268, List.forall_mem_cons.2 ⟨subd9_4_269, List.forall_mem_cons.2 ⟨subd9_4_270, List.forall_mem_cons.2 ⟨subd9_4_271, List.forall_mem_cons.2 ⟨subd9_4_272, List.forall_mem_cons.2 ⟨subd9_4_273, List.forall_mem_cons.2 ⟨subd9_4_274, List.forall_mem_cons.2 ⟨subd9_4_275, List.forall_mem_cons.2 ⟨subd9_4_276, List.forall_mem_cons.2 ⟨subd9_4_277, List.forall_mem_cons.2 ⟨subd9_4_278, List.forall_mem_cons.2 ⟨subd9_4_279, List.forall_mem_cons.2 ⟨subd9_4_280, List.forall_mem_cons.2 ⟨subd9_4_281, List.forall_mem_cons.2 ⟨subd9_4_282, List.forall_mem_cons.2 ⟨subd9_4_283, List.forall_mem_cons.2 ⟨subd9_4_284, List.forall_mem_cons.2 ⟨subd9_4_285, List.forall_mem_cons.2 ⟨subd9_4_286, List.forall_mem_cons.2 ⟨subd9_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_288 : subd9_4 [-1, 0, 5] = true := by decide +kernel
theorem subd9_4_289 : subd9_4 [-1, 0, 6] = true := by decide +kernel
theorem subd9_4_290 : subd9_4 [-1, 0, 7] = true := by decide +kernel
theorem subd9_4_291 : subd9_4 [-1, 1, -9] = true := by decide +kernel
theorem subd9_4_292 : subd9_4 [-1, 1, -8] = true := by decide +kernel
theorem subd9_4_293 : subd9_4 [-1, 1, -7] = true := by decide +kernel
theorem subd9_4_294 : subd9_4 [-1, 1, -6] = true := by decide +kernel
theorem subd9_4_295 : subd9_4 [-1, 1, -5] = true := by decide +kernel
theorem subd9_4_296 : subd9_4 [-1, 1, -4] = true := by decide +kernel
theorem subd9_4_297 : subd9_4 [-1, 1, -3] = true := by decide +kernel
theorem subd9_4_298 : subd9_4 [-1, 1, -2] = true := by decide +kernel
theorem subd9_4_299 : subd9_4 [-1, 1, -1] = true := by decide +kernel
theorem subd9_4_300 : subd9_4 [-1, 1, 0] = true := by decide +kernel
theorem subd9_4_301 : subd9_4 [-1, 1, 1] = true := by decide +kernel
theorem subd9_4_302 : subd9_4 [-1, 1, 2] = true := by decide +kernel
theorem subd9_4_303 : subd9_4 [-1, 1, 3] = true := by decide +kernel
theorem subd9_4_304 : subd9_4 [-1, 1, 4] = true := by decide +kernel
theorem subd9_4_305 : subd9_4 [-1, 1, 5] = true := by decide +kernel
theorem subd9_4_306 : subd9_4 [-1, 1, 6] = true := by decide +kernel
theorem subd9_4_307 : subd9_4 [-1, 1, 7] = true := by decide +kernel
theorem subd9_4_308 : subd9_4 [-1, 2, -8] = true := by decide +kernel
theorem subd9_4_309 : subd9_4 [-1, 2, -7] = true := by decide +kernel
theorem subd9_4_310 : subd9_4 [-1, 2, -6] = true := by decide +kernel
theorem subd9_4_311 : subd9_4 [-1, 2, -5] = true := by decide +kernel
theorem subd9_4_312 : subd9_4 [-1, 2, -4] = true := by decide +kernel
theorem subd9_4_313 : subd9_4 [-1, 2, -3] = true := by decide +kernel
theorem subd9_4_314 : subd9_4 [-1, 2, -2] = true := by decide +kernel
theorem subd9_4_315 : subd9_4 [-1, 2, -1] = true := by decide +kernel
theorem subd9_4_316 : subd9_4 [-1, 2, 0] = true := by decide +kernel
theorem subd9_4_317 : subd9_4 [-1, 2, 1] = true := by decide +kernel
theorem subd9_4_318 : subd9_4 [-1, 2, 2] = true := by decide +kernel
theorem subd9_4_319 : subd9_4 [-1, 2, 3] = true := by decide +kernel
theorem sbd9_4_9 : ∀ q ∈ blkd9_4_9, subd9_4 q = true := by
  unfold blkd9_4_9
  exact List.forall_mem_cons.2 ⟨subd9_4_288, List.forall_mem_cons.2 ⟨subd9_4_289, List.forall_mem_cons.2 ⟨subd9_4_290, List.forall_mem_cons.2 ⟨subd9_4_291, List.forall_mem_cons.2 ⟨subd9_4_292, List.forall_mem_cons.2 ⟨subd9_4_293, List.forall_mem_cons.2 ⟨subd9_4_294, List.forall_mem_cons.2 ⟨subd9_4_295, List.forall_mem_cons.2 ⟨subd9_4_296, List.forall_mem_cons.2 ⟨subd9_4_297, List.forall_mem_cons.2 ⟨subd9_4_298, List.forall_mem_cons.2 ⟨subd9_4_299, List.forall_mem_cons.2 ⟨subd9_4_300, List.forall_mem_cons.2 ⟨subd9_4_301, List.forall_mem_cons.2 ⟨subd9_4_302, List.forall_mem_cons.2 ⟨subd9_4_303, List.forall_mem_cons.2 ⟨subd9_4_304, List.forall_mem_cons.2 ⟨subd9_4_305, List.forall_mem_cons.2 ⟨subd9_4_306, List.forall_mem_cons.2 ⟨subd9_4_307, List.forall_mem_cons.2 ⟨subd9_4_308, List.forall_mem_cons.2 ⟨subd9_4_309, List.forall_mem_cons.2 ⟨subd9_4_310, List.forall_mem_cons.2 ⟨subd9_4_311, List.forall_mem_cons.2 ⟨subd9_4_312, List.forall_mem_cons.2 ⟨subd9_4_313, List.forall_mem_cons.2 ⟨subd9_4_314, List.forall_mem_cons.2 ⟨subd9_4_315, List.forall_mem_cons.2 ⟨subd9_4_316, List.forall_mem_cons.2 ⟨subd9_4_317, List.forall_mem_cons.2 ⟨subd9_4_318, List.forall_mem_cons.2 ⟨subd9_4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_320 : subd9_4 [-1, 2, 4] = true := by decide +kernel
theorem subd9_4_321 : subd9_4 [-1, 2, 5] = true := by decide +kernel
theorem subd9_4_322 : subd9_4 [-1, 2, 6] = true := by decide +kernel
theorem subd9_4_323 : subd9_4 [-1, 2, 7] = true := by decide +kernel
theorem subd9_4_324 : subd9_4 [-1, 3, -8] = true := by decide +kernel
theorem subd9_4_325 : subd9_4 [-1, 3, -7] = true := by decide +kernel
theorem subd9_4_326 : subd9_4 [-1, 3, -6] = true := by decide +kernel
theorem subd9_4_327 : subd9_4 [-1, 3, -5] = true := by decide +kernel
theorem subd9_4_328 : subd9_4 [-1, 3, -4] = true := by decide +kernel
theorem subd9_4_329 : subd9_4 [-1, 3, -3] = true := by decide +kernel
theorem subd9_4_330 : subd9_4 [-1, 3, -2] = true := by decide +kernel
theorem subd9_4_331 : subd9_4 [-1, 3, -1] = true := by decide +kernel
theorem subd9_4_332 : subd9_4 [-1, 3, 0] = true := by decide +kernel
theorem subd9_4_333 : subd9_4 [-1, 3, 1] = true := by decide +kernel
theorem subd9_4_334 : subd9_4 [-1, 3, 2] = true := by decide +kernel
theorem subd9_4_335 : subd9_4 [-1, 3, 3] = true := by decide +kernel
theorem subd9_4_336 : subd9_4 [-1, 3, 4] = true := by decide +kernel
theorem subd9_4_337 : subd9_4 [-1, 3, 5] = true := by decide +kernel
theorem subd9_4_338 : subd9_4 [-1, 3, 6] = true := by decide +kernel
theorem subd9_4_339 : subd9_4 [-1, 4] = true := by decide +kernel
theorem subd9_4_340 : subd9_4 [-1, 5] = true := by decide +kernel
theorem subd9_4_341 : subd9_4 [-1, 6] = true := by decide +kernel
theorem subd9_4_342 : subd9_4 [0, -7] = true := by decide +kernel
theorem subd9_4_343 : subd9_4 [0, -6] = true := by decide +kernel
theorem subd9_4_344 : subd9_4 [0, -5] = true := by decide +kernel
theorem subd9_4_345 : subd9_4 [0, -4] = true := by decide +kernel
theorem subd9_4_346 : subd9_4 [0, -3, -8] = true := by decide +kernel
theorem subd9_4_347 : subd9_4 [0, -3, -7] = true := by decide +kernel
theorem subd9_4_348 : subd9_4 [0, -3, -6] = true := by decide +kernel
theorem subd9_4_349 : subd9_4 [0, -3, -5] = true := by decide +kernel
theorem subd9_4_350 : subd9_4 [0, -3, -4] = true := by decide +kernel
theorem subd9_4_351 : subd9_4 [0, -3, -3] = true := by decide +kernel
theorem sbd9_4_10 : ∀ q ∈ blkd9_4_10, subd9_4 q = true := by
  unfold blkd9_4_10
  exact List.forall_mem_cons.2 ⟨subd9_4_320, List.forall_mem_cons.2 ⟨subd9_4_321, List.forall_mem_cons.2 ⟨subd9_4_322, List.forall_mem_cons.2 ⟨subd9_4_323, List.forall_mem_cons.2 ⟨subd9_4_324, List.forall_mem_cons.2 ⟨subd9_4_325, List.forall_mem_cons.2 ⟨subd9_4_326, List.forall_mem_cons.2 ⟨subd9_4_327, List.forall_mem_cons.2 ⟨subd9_4_328, List.forall_mem_cons.2 ⟨subd9_4_329, List.forall_mem_cons.2 ⟨subd9_4_330, List.forall_mem_cons.2 ⟨subd9_4_331, List.forall_mem_cons.2 ⟨subd9_4_332, List.forall_mem_cons.2 ⟨subd9_4_333, List.forall_mem_cons.2 ⟨subd9_4_334, List.forall_mem_cons.2 ⟨subd9_4_335, List.forall_mem_cons.2 ⟨subd9_4_336, List.forall_mem_cons.2 ⟨subd9_4_337, List.forall_mem_cons.2 ⟨subd9_4_338, List.forall_mem_cons.2 ⟨subd9_4_339, List.forall_mem_cons.2 ⟨subd9_4_340, List.forall_mem_cons.2 ⟨subd9_4_341, List.forall_mem_cons.2 ⟨subd9_4_342, List.forall_mem_cons.2 ⟨subd9_4_343, List.forall_mem_cons.2 ⟨subd9_4_344, List.forall_mem_cons.2 ⟨subd9_4_345, List.forall_mem_cons.2 ⟨subd9_4_346, List.forall_mem_cons.2 ⟨subd9_4_347, List.forall_mem_cons.2 ⟨subd9_4_348, List.forall_mem_cons.2 ⟨subd9_4_349, List.forall_mem_cons.2 ⟨subd9_4_350, List.forall_mem_cons.2 ⟨subd9_4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
