import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_6_0 : subd9_6 [-5, -5] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-5, -4] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [-5, -3] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [-5, -2] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [-5, -1] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [-5, 0] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [-5, 1] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [-5, 2] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [-4, -6] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [-4, -5] = true := by decide +kernel
theorem subd9_6_10 : subd9_6 [-4, -4] = true := by decide +kernel
theorem subd9_6_11 : subd9_6 [-4, -3] = true := by decide +kernel
theorem subd9_6_12 : subd9_6 [-4, -2] = true := by decide +kernel
theorem subd9_6_13 : subd9_6 [-4, -1] = true := by decide +kernel
theorem subd9_6_14 : subd9_6 [-4, 0] = true := by decide +kernel
theorem subd9_6_15 : subd9_6 [-4, 1] = true := by decide +kernel
theorem subd9_6_16 : subd9_6 [-4, 2] = true := by decide +kernel
theorem subd9_6_17 : subd9_6 [-4, 3] = true := by decide +kernel
theorem subd9_6_18 : subd9_6 [-4, 4] = true := by decide +kernel
theorem subd9_6_19 : subd9_6 [-3, -7] = true := by decide +kernel
theorem subd9_6_20 : subd9_6 [-3, -6] = true := by decide +kernel
theorem subd9_6_21 : subd9_6 [-3, -5] = true := by decide +kernel
theorem subd9_6_22 : subd9_6 [-3, -4] = true := by decide +kernel
theorem subd9_6_23 : subd9_6 [-3, -3, -7] = true := by decide +kernel
theorem subd9_6_24 : subd9_6 [-3, -3, -6] = true := by decide +kernel
theorem subd9_6_25 : subd9_6 [-3, -3, -5] = true := by decide +kernel
theorem subd9_6_26 : subd9_6 [-3, -3, -4] = true := by decide +kernel
theorem subd9_6_27 : subd9_6 [-3, -3, -3] = true := by decide +kernel
theorem subd9_6_28 : subd9_6 [-3, -3, -2] = true := by decide +kernel
theorem subd9_6_29 : subd9_6 [-3, -3, -1] = true := by decide +kernel
theorem subd9_6_30 : subd9_6 [-3, -3, 0] = true := by decide +kernel
theorem subd9_6_31 : subd9_6 [-3, -3, 1] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_cons.2 ⟨subd9_6_10, List.forall_mem_cons.2 ⟨subd9_6_11, List.forall_mem_cons.2 ⟨subd9_6_12, List.forall_mem_cons.2 ⟨subd9_6_13, List.forall_mem_cons.2 ⟨subd9_6_14, List.forall_mem_cons.2 ⟨subd9_6_15, List.forall_mem_cons.2 ⟨subd9_6_16, List.forall_mem_cons.2 ⟨subd9_6_17, List.forall_mem_cons.2 ⟨subd9_6_18, List.forall_mem_cons.2 ⟨subd9_6_19, List.forall_mem_cons.2 ⟨subd9_6_20, List.forall_mem_cons.2 ⟨subd9_6_21, List.forall_mem_cons.2 ⟨subd9_6_22, List.forall_mem_cons.2 ⟨subd9_6_23, List.forall_mem_cons.2 ⟨subd9_6_24, List.forall_mem_cons.2 ⟨subd9_6_25, List.forall_mem_cons.2 ⟨subd9_6_26, List.forall_mem_cons.2 ⟨subd9_6_27, List.forall_mem_cons.2 ⟨subd9_6_28, List.forall_mem_cons.2 ⟨subd9_6_29, List.forall_mem_cons.2 ⟨subd9_6_30, List.forall_mem_cons.2 ⟨subd9_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_32 : subd9_6 [-3, -3, 2] = true := by decide +kernel
theorem subd9_6_33 : subd9_6 [-3, -3, 3] = true := by decide +kernel
theorem subd9_6_34 : subd9_6 [-3, -3, 4] = true := by decide +kernel
theorem subd9_6_35 : subd9_6 [-3, -3, 5] = true := by decide +kernel
theorem subd9_6_36 : subd9_6 [-3, -3, 6] = true := by decide +kernel
theorem subd9_6_37 : subd9_6 [-3, -2, -8] = true := by decide +kernel
theorem subd9_6_38 : subd9_6 [-3, -2, -7] = true := by decide +kernel
theorem subd9_6_39 : subd9_6 [-3, -2, -6] = true := by decide +kernel
theorem subd9_6_40 : subd9_6 [-3, -2, -5] = true := by decide +kernel
theorem subd9_6_41 : subd9_6 [-3, -2, -4] = true := by decide +kernel
theorem subd9_6_42 : subd9_6 [-3, -2, -3] = true := by decide +kernel
theorem subd9_6_43 : subd9_6 [-3, -2, -2] = true := by decide +kernel
theorem subd9_6_44 : subd9_6 [-3, -2, -1] = true := by decide +kernel
theorem subd9_6_45 : subd9_6 [-3, -2, 0] = true := by decide +kernel
theorem subd9_6_46 : subd9_6 [-3, -2, 1] = true := by decide +kernel
theorem subd9_6_47 : subd9_6 [-3, -2, 2] = true := by decide +kernel
theorem subd9_6_48 : subd9_6 [-3, -2, 3] = true := by decide +kernel
theorem subd9_6_49 : subd9_6 [-3, -2, 4] = true := by decide +kernel
theorem subd9_6_50 : subd9_6 [-3, -2, 5] = true := by decide +kernel
theorem subd9_6_51 : subd9_6 [-3, -2, 6] = true := by decide +kernel
theorem subd9_6_52 : subd9_6 [-3, -1, -8] = true := by decide +kernel
theorem subd9_6_53 : subd9_6 [-3, -1, -7] = true := by decide +kernel
theorem subd9_6_54 : subd9_6 [-3, -1, -6] = true := by decide +kernel
theorem subd9_6_55 : subd9_6 [-3, -1, -5] = true := by decide +kernel
theorem subd9_6_56 : subd9_6 [-3, -1, -4] = true := by decide +kernel
theorem subd9_6_57 : subd9_6 [-3, -1, -3] = true := by decide +kernel
theorem subd9_6_58 : subd9_6 [-3, -1, -2] = true := by decide +kernel
theorem subd9_6_59 : subd9_6 [-3, -1, -1] = true := by decide +kernel
theorem subd9_6_60 : subd9_6 [-3, -1, 0] = true := by decide +kernel
theorem subd9_6_61 : subd9_6 [-3, -1, 1] = true := by decide +kernel
theorem subd9_6_62 : subd9_6 [-3, -1, 2] = true := by decide +kernel
theorem subd9_6_63 : subd9_6 [-3, -1, 3] = true := by decide +kernel
theorem sbd9_6_1 : ∀ q ∈ blkd9_6_1, subd9_6 q = true := by
  unfold blkd9_6_1
  exact List.forall_mem_cons.2 ⟨subd9_6_32, List.forall_mem_cons.2 ⟨subd9_6_33, List.forall_mem_cons.2 ⟨subd9_6_34, List.forall_mem_cons.2 ⟨subd9_6_35, List.forall_mem_cons.2 ⟨subd9_6_36, List.forall_mem_cons.2 ⟨subd9_6_37, List.forall_mem_cons.2 ⟨subd9_6_38, List.forall_mem_cons.2 ⟨subd9_6_39, List.forall_mem_cons.2 ⟨subd9_6_40, List.forall_mem_cons.2 ⟨subd9_6_41, List.forall_mem_cons.2 ⟨subd9_6_42, List.forall_mem_cons.2 ⟨subd9_6_43, List.forall_mem_cons.2 ⟨subd9_6_44, List.forall_mem_cons.2 ⟨subd9_6_45, List.forall_mem_cons.2 ⟨subd9_6_46, List.forall_mem_cons.2 ⟨subd9_6_47, List.forall_mem_cons.2 ⟨subd9_6_48, List.forall_mem_cons.2 ⟨subd9_6_49, List.forall_mem_cons.2 ⟨subd9_6_50, List.forall_mem_cons.2 ⟨subd9_6_51, List.forall_mem_cons.2 ⟨subd9_6_52, List.forall_mem_cons.2 ⟨subd9_6_53, List.forall_mem_cons.2 ⟨subd9_6_54, List.forall_mem_cons.2 ⟨subd9_6_55, List.forall_mem_cons.2 ⟨subd9_6_56, List.forall_mem_cons.2 ⟨subd9_6_57, List.forall_mem_cons.2 ⟨subd9_6_58, List.forall_mem_cons.2 ⟨subd9_6_59, List.forall_mem_cons.2 ⟨subd9_6_60, List.forall_mem_cons.2 ⟨subd9_6_61, List.forall_mem_cons.2 ⟨subd9_6_62, List.forall_mem_cons.2 ⟨subd9_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_64 : subd9_6 [-3, -1, 4] = true := by decide +kernel
theorem subd9_6_65 : subd9_6 [-3, -1, 5] = true := by decide +kernel
theorem subd9_6_66 : subd9_6 [-3, -1, 6] = true := by decide +kernel
theorem subd9_6_67 : subd9_6 [-3, 0, -8] = true := by decide +kernel
theorem subd9_6_68 : subd9_6 [-3, 0, -7] = true := by decide +kernel
theorem subd9_6_69 : subd9_6 [-3, 0, -6] = true := by decide +kernel
theorem subd9_6_70 : subd9_6 [-3, 0, -5] = true := by decide +kernel
theorem subd9_6_71 : subd9_6 [-3, 0, -4] = true := by decide +kernel
theorem subd9_6_72 : subd9_6 [-3, 0, -3] = true := by decide +kernel
theorem subd9_6_73 : subd9_6 [-3, 0, -2] = true := by decide +kernel
theorem subd9_6_74 : subd9_6 [-3, 0, -1] = true := by decide +kernel
theorem subd9_6_75 : subd9_6 [-3, 0, 0] = true := by decide +kernel
theorem subd9_6_76 : subd9_6 [-3, 0, 1] = true := by decide +kernel
theorem subd9_6_77 : subd9_6 [-3, 0, 2] = true := by decide +kernel
theorem subd9_6_78 : subd9_6 [-3, 0, 3] = true := by decide +kernel
theorem subd9_6_79 : subd9_6 [-3, 0, 4] = true := by decide +kernel
theorem subd9_6_80 : subd9_6 [-3, 0, 5] = true := by decide +kernel
theorem subd9_6_81 : subd9_6 [-3, 0, 6] = true := by decide +kernel
theorem subd9_6_82 : subd9_6 [-3, 1, -8] = true := by decide +kernel
theorem subd9_6_83 : subd9_6 [-3, 1, -7] = true := by decide +kernel
theorem subd9_6_84 : subd9_6 [-3, 1, -6] = true := by decide +kernel
theorem subd9_6_85 : subd9_6 [-3, 1, -5] = true := by decide +kernel
theorem subd9_6_86 : subd9_6 [-3, 1, -4] = true := by decide +kernel
theorem subd9_6_87 : subd9_6 [-3, 1, -3] = true := by decide +kernel
theorem subd9_6_88 : subd9_6 [-3, 1, -2] = true := by decide +kernel
theorem subd9_6_89 : subd9_6 [-3, 1, -1] = true := by decide +kernel
theorem subd9_6_90 : subd9_6 [-3, 1, 0] = true := by decide +kernel
theorem subd9_6_91 : subd9_6 [-3, 1, 1] = true := by decide +kernel
theorem subd9_6_92 : subd9_6 [-3, 1, 2] = true := by decide +kernel
theorem subd9_6_93 : subd9_6 [-3, 1, 3] = true := by decide +kernel
theorem subd9_6_94 : subd9_6 [-3, 1, 4] = true := by decide +kernel
theorem subd9_6_95 : subd9_6 [-3, 1, 5] = true := by decide +kernel
theorem sbd9_6_2 : ∀ q ∈ blkd9_6_2, subd9_6 q = true := by
  unfold blkd9_6_2
  exact List.forall_mem_cons.2 ⟨subd9_6_64, List.forall_mem_cons.2 ⟨subd9_6_65, List.forall_mem_cons.2 ⟨subd9_6_66, List.forall_mem_cons.2 ⟨subd9_6_67, List.forall_mem_cons.2 ⟨subd9_6_68, List.forall_mem_cons.2 ⟨subd9_6_69, List.forall_mem_cons.2 ⟨subd9_6_70, List.forall_mem_cons.2 ⟨subd9_6_71, List.forall_mem_cons.2 ⟨subd9_6_72, List.forall_mem_cons.2 ⟨subd9_6_73, List.forall_mem_cons.2 ⟨subd9_6_74, List.forall_mem_cons.2 ⟨subd9_6_75, List.forall_mem_cons.2 ⟨subd9_6_76, List.forall_mem_cons.2 ⟨subd9_6_77, List.forall_mem_cons.2 ⟨subd9_6_78, List.forall_mem_cons.2 ⟨subd9_6_79, List.forall_mem_cons.2 ⟨subd9_6_80, List.forall_mem_cons.2 ⟨subd9_6_81, List.forall_mem_cons.2 ⟨subd9_6_82, List.forall_mem_cons.2 ⟨subd9_6_83, List.forall_mem_cons.2 ⟨subd9_6_84, List.forall_mem_cons.2 ⟨subd9_6_85, List.forall_mem_cons.2 ⟨subd9_6_86, List.forall_mem_cons.2 ⟨subd9_6_87, List.forall_mem_cons.2 ⟨subd9_6_88, List.forall_mem_cons.2 ⟨subd9_6_89, List.forall_mem_cons.2 ⟨subd9_6_90, List.forall_mem_cons.2 ⟨subd9_6_91, List.forall_mem_cons.2 ⟨subd9_6_92, List.forall_mem_cons.2 ⟨subd9_6_93, List.forall_mem_cons.2 ⟨subd9_6_94, List.forall_mem_cons.2 ⟨subd9_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_96 : subd9_6 [-3, 2] = true := by decide +kernel
theorem subd9_6_97 : subd9_6 [-3, 3] = true := by decide +kernel
theorem subd9_6_98 : subd9_6 [-3, 4] = true := by decide +kernel
theorem subd9_6_99 : subd9_6 [-2, -7] = true := by decide +kernel
theorem subd9_6_100 : subd9_6 [-2, -6] = true := by decide +kernel
theorem subd9_6_101 : subd9_6 [-2, -5] = true := by decide +kernel
theorem subd9_6_102 : subd9_6 [-2, -4] = true := by decide +kernel
theorem subd9_6_103 : subd9_6 [-2, -3, -7] = true := by decide +kernel
theorem subd9_6_104 : subd9_6 [-2, -3, -6] = true := by decide +kernel
theorem subd9_6_105 : subd9_6 [-2, -3, -5] = true := by decide +kernel
theorem subd9_6_106 : subd9_6 [-2, -3, -4] = true := by decide +kernel
theorem subd9_6_107 : subd9_6 [-2, -3, -3] = true := by decide +kernel
theorem subd9_6_108 : subd9_6 [-2, -3, -2] = true := by decide +kernel
theorem subd9_6_109 : subd9_6 [-2, -3, -1] = true := by decide +kernel
theorem subd9_6_110 : subd9_6 [-2, -3, 0] = true := by decide +kernel
theorem subd9_6_111 : subd9_6 [-2, -3, 1] = true := by decide +kernel
theorem subd9_6_112 : subd9_6 [-2, -3, 2] = true := by decide +kernel
theorem subd9_6_113 : subd9_6 [-2, -3, 3] = true := by decide +kernel
theorem subd9_6_114 : subd9_6 [-2, -3, 4] = true := by decide +kernel
theorem subd9_6_115 : subd9_6 [-2, -3, 5] = true := by decide +kernel
theorem subd9_6_116 : subd9_6 [-2, -3, 6] = true := by decide +kernel
theorem subd9_6_117 : subd9_6 [-2, -3, 7] = true := by decide +kernel
theorem subd9_6_118 : subd9_6 [-2, -2, -8] = true := by decide +kernel
theorem subd9_6_119 : subd9_6 [-2, -2, -7] = true := by decide +kernel
theorem subd9_6_120 : subd9_6 [-2, -2, -6] = true := by decide +kernel
theorem subd9_6_121 : subd9_6 [-2, -2, -5] = true := by decide +kernel
theorem subd9_6_122 : subd9_6 [-2, -2, -4] = true := by decide +kernel
theorem subd9_6_123 : subd9_6 [-2, -2, -3] = true := by decide +kernel
theorem subd9_6_124 : subd9_6 [-2, -2, -2] = true := by decide +kernel
theorem subd9_6_125 : subd9_6 [-2, -2, -1] = true := by decide +kernel
theorem subd9_6_126 : subd9_6 [-2, -2, 0] = true := by decide +kernel
theorem subd9_6_127 : subd9_6 [-2, -2, 1] = true := by decide +kernel
theorem sbd9_6_3 : ∀ q ∈ blkd9_6_3, subd9_6 q = true := by
  unfold blkd9_6_3
  exact List.forall_mem_cons.2 ⟨subd9_6_96, List.forall_mem_cons.2 ⟨subd9_6_97, List.forall_mem_cons.2 ⟨subd9_6_98, List.forall_mem_cons.2 ⟨subd9_6_99, List.forall_mem_cons.2 ⟨subd9_6_100, List.forall_mem_cons.2 ⟨subd9_6_101, List.forall_mem_cons.2 ⟨subd9_6_102, List.forall_mem_cons.2 ⟨subd9_6_103, List.forall_mem_cons.2 ⟨subd9_6_104, List.forall_mem_cons.2 ⟨subd9_6_105, List.forall_mem_cons.2 ⟨subd9_6_106, List.forall_mem_cons.2 ⟨subd9_6_107, List.forall_mem_cons.2 ⟨subd9_6_108, List.forall_mem_cons.2 ⟨subd9_6_109, List.forall_mem_cons.2 ⟨subd9_6_110, List.forall_mem_cons.2 ⟨subd9_6_111, List.forall_mem_cons.2 ⟨subd9_6_112, List.forall_mem_cons.2 ⟨subd9_6_113, List.forall_mem_cons.2 ⟨subd9_6_114, List.forall_mem_cons.2 ⟨subd9_6_115, List.forall_mem_cons.2 ⟨subd9_6_116, List.forall_mem_cons.2 ⟨subd9_6_117, List.forall_mem_cons.2 ⟨subd9_6_118, List.forall_mem_cons.2 ⟨subd9_6_119, List.forall_mem_cons.2 ⟨subd9_6_120, List.forall_mem_cons.2 ⟨subd9_6_121, List.forall_mem_cons.2 ⟨subd9_6_122, List.forall_mem_cons.2 ⟨subd9_6_123, List.forall_mem_cons.2 ⟨subd9_6_124, List.forall_mem_cons.2 ⟨subd9_6_125, List.forall_mem_cons.2 ⟨subd9_6_126, List.forall_mem_cons.2 ⟨subd9_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_128 : subd9_6 [-2, -2, 2] = true := by decide +kernel
theorem subd9_6_129 : subd9_6 [-2, -2, 3] = true := by decide +kernel
theorem subd9_6_130 : subd9_6 [-2, -2, 4] = true := by decide +kernel
theorem subd9_6_131 : subd9_6 [-2, -2, 5] = true := by decide +kernel
theorem subd9_6_132 : subd9_6 [-2, -2, 6] = true := by decide +kernel
theorem subd9_6_133 : subd9_6 [-2, -2, 7] = true := by decide +kernel
theorem subd9_6_134 : subd9_6 [-2, -1, -8] = true := by decide +kernel
theorem subd9_6_135 : subd9_6 [-2, -1, -7] = true := by decide +kernel
theorem subd9_6_136 : subd9_6 [-2, -1, -6] = true := by decide +kernel
theorem subd9_6_137 : subd9_6 [-2, -1, -5] = true := by decide +kernel
theorem subd9_6_138 : subd9_6 [-2, -1, -4] = true := by decide +kernel
theorem subd9_6_139 : subd9_6 [-2, -1, -3] = true := by decide +kernel
theorem subd9_6_140 : subd9_6 [-2, -1, -2] = true := by decide +kernel
theorem subd9_6_141 : subd9_6 [-2, -1, -1] = true := by decide +kernel
theorem subd9_6_142 : subd9_6 [-2, -1, 0] = true := by decide +kernel
theorem subd9_6_143 : subd9_6 [-2, -1, 1] = true := by decide +kernel
theorem subd9_6_144 : subd9_6 [-2, -1, 2] = true := by decide +kernel
theorem subd9_6_145 : subd9_6 [-2, -1, 3] = true := by decide +kernel
theorem subd9_6_146 : subd9_6 [-2, -1, 4] = true := by decide +kernel
theorem subd9_6_147 : subd9_6 [-2, -1, 5] = true := by decide +kernel
theorem subd9_6_148 : subd9_6 [-2, -1, 6] = true := by decide +kernel
theorem subd9_6_149 : subd9_6 [-2, -1, 7] = true := by decide +kernel
theorem subd9_6_150 : subd9_6 [-2, 0, -9] = true := by decide +kernel
theorem subd9_6_151 : subd9_6 [-2, 0, -8] = true := by decide +kernel
theorem subd9_6_152 : subd9_6 [-2, 0, -7] = true := by decide +kernel
theorem subd9_6_153 : subd9_6 [-2, 0, -6] = true := by decide +kernel
theorem subd9_6_154 : subd9_6 [-2, 0, -5] = true := by decide +kernel
theorem subd9_6_155 : subd9_6 [-2, 0, -4] = true := by decide +kernel
theorem subd9_6_156 : subd9_6 [-2, 0, -3] = true := by decide +kernel
theorem subd9_6_157 : subd9_6 [-2, 0, -2] = true := by decide +kernel
theorem subd9_6_158 : subd9_6 [-2, 0, -1] = true := by decide +kernel
theorem subd9_6_159 : subd9_6 [-2, 0, 0] = true := by decide +kernel
theorem sbd9_6_4 : ∀ q ∈ blkd9_6_4, subd9_6 q = true := by
  unfold blkd9_6_4
  exact List.forall_mem_cons.2 ⟨subd9_6_128, List.forall_mem_cons.2 ⟨subd9_6_129, List.forall_mem_cons.2 ⟨subd9_6_130, List.forall_mem_cons.2 ⟨subd9_6_131, List.forall_mem_cons.2 ⟨subd9_6_132, List.forall_mem_cons.2 ⟨subd9_6_133, List.forall_mem_cons.2 ⟨subd9_6_134, List.forall_mem_cons.2 ⟨subd9_6_135, List.forall_mem_cons.2 ⟨subd9_6_136, List.forall_mem_cons.2 ⟨subd9_6_137, List.forall_mem_cons.2 ⟨subd9_6_138, List.forall_mem_cons.2 ⟨subd9_6_139, List.forall_mem_cons.2 ⟨subd9_6_140, List.forall_mem_cons.2 ⟨subd9_6_141, List.forall_mem_cons.2 ⟨subd9_6_142, List.forall_mem_cons.2 ⟨subd9_6_143, List.forall_mem_cons.2 ⟨subd9_6_144, List.forall_mem_cons.2 ⟨subd9_6_145, List.forall_mem_cons.2 ⟨subd9_6_146, List.forall_mem_cons.2 ⟨subd9_6_147, List.forall_mem_cons.2 ⟨subd9_6_148, List.forall_mem_cons.2 ⟨subd9_6_149, List.forall_mem_cons.2 ⟨subd9_6_150, List.forall_mem_cons.2 ⟨subd9_6_151, List.forall_mem_cons.2 ⟨subd9_6_152, List.forall_mem_cons.2 ⟨subd9_6_153, List.forall_mem_cons.2 ⟨subd9_6_154, List.forall_mem_cons.2 ⟨subd9_6_155, List.forall_mem_cons.2 ⟨subd9_6_156, List.forall_mem_cons.2 ⟨subd9_6_157, List.forall_mem_cons.2 ⟨subd9_6_158, List.forall_mem_cons.2 ⟨subd9_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_160 : subd9_6 [-2, 0, 1] = true := by decide +kernel
theorem subd9_6_161 : subd9_6 [-2, 0, 2] = true := by decide +kernel
theorem subd9_6_162 : subd9_6 [-2, 0, 3] = true := by decide +kernel
theorem subd9_6_163 : subd9_6 [-2, 0, 4] = true := by decide +kernel
theorem subd9_6_164 : subd9_6 [-2, 0, 5] = true := by decide +kernel
theorem subd9_6_165 : subd9_6 [-2, 0, 6] = true := by decide +kernel
theorem subd9_6_166 : subd9_6 [-2, 0, 7] = true := by decide +kernel
theorem subd9_6_167 : subd9_6 [-2, 1, -9] = true := by decide +kernel
theorem subd9_6_168 : subd9_6 [-2, 1, -8] = true := by decide +kernel
theorem subd9_6_169 : subd9_6 [-2, 1, -7] = true := by decide +kernel
theorem subd9_6_170 : subd9_6 [-2, 1, -6] = true := by decide +kernel
theorem subd9_6_171 : subd9_6 [-2, 1, -5] = true := by decide +kernel
theorem subd9_6_172 : subd9_6 [-2, 1, -4] = true := by decide +kernel
theorem subd9_6_173 : subd9_6 [-2, 1, -3] = true := by decide +kernel
theorem subd9_6_174 : subd9_6 [-2, 1, -2] = true := by decide +kernel
theorem subd9_6_175 : subd9_6 [-2, 1, -1] = true := by decide +kernel
theorem subd9_6_176 : subd9_6 [-2, 1, 0] = true := by decide +kernel
theorem subd9_6_177 : subd9_6 [-2, 1, 1] = true := by decide +kernel
theorem subd9_6_178 : subd9_6 [-2, 1, 2] = true := by decide +kernel
theorem subd9_6_179 : subd9_6 [-2, 1, 3] = true := by decide +kernel
theorem subd9_6_180 : subd9_6 [-2, 1, 4] = true := by decide +kernel
theorem subd9_6_181 : subd9_6 [-2, 1, 5] = true := by decide +kernel
theorem subd9_6_182 : subd9_6 [-2, 1, 6] = true := by decide +kernel
theorem subd9_6_183 : subd9_6 [-2, 2, -9] = true := by decide +kernel
theorem subd9_6_184 : subd9_6 [-2, 2, -8] = true := by decide +kernel
theorem subd9_6_185 : subd9_6 [-2, 2, -7] = true := by decide +kernel
theorem subd9_6_186 : subd9_6 [-2, 2, -6] = true := by decide +kernel
theorem subd9_6_187 : subd9_6 [-2, 2, -5] = true := by decide +kernel
theorem subd9_6_188 : subd9_6 [-2, 2, -4] = true := by decide +kernel
theorem subd9_6_189 : subd9_6 [-2, 2, -3] = true := by decide +kernel
theorem subd9_6_190 : subd9_6 [-2, 2, -2] = true := by decide +kernel
theorem subd9_6_191 : subd9_6 [-2, 2, -1] = true := by decide +kernel
theorem sbd9_6_5 : ∀ q ∈ blkd9_6_5, subd9_6 q = true := by
  unfold blkd9_6_5
  exact List.forall_mem_cons.2 ⟨subd9_6_160, List.forall_mem_cons.2 ⟨subd9_6_161, List.forall_mem_cons.2 ⟨subd9_6_162, List.forall_mem_cons.2 ⟨subd9_6_163, List.forall_mem_cons.2 ⟨subd9_6_164, List.forall_mem_cons.2 ⟨subd9_6_165, List.forall_mem_cons.2 ⟨subd9_6_166, List.forall_mem_cons.2 ⟨subd9_6_167, List.forall_mem_cons.2 ⟨subd9_6_168, List.forall_mem_cons.2 ⟨subd9_6_169, List.forall_mem_cons.2 ⟨subd9_6_170, List.forall_mem_cons.2 ⟨subd9_6_171, List.forall_mem_cons.2 ⟨subd9_6_172, List.forall_mem_cons.2 ⟨subd9_6_173, List.forall_mem_cons.2 ⟨subd9_6_174, List.forall_mem_cons.2 ⟨subd9_6_175, List.forall_mem_cons.2 ⟨subd9_6_176, List.forall_mem_cons.2 ⟨subd9_6_177, List.forall_mem_cons.2 ⟨subd9_6_178, List.forall_mem_cons.2 ⟨subd9_6_179, List.forall_mem_cons.2 ⟨subd9_6_180, List.forall_mem_cons.2 ⟨subd9_6_181, List.forall_mem_cons.2 ⟨subd9_6_182, List.forall_mem_cons.2 ⟨subd9_6_183, List.forall_mem_cons.2 ⟨subd9_6_184, List.forall_mem_cons.2 ⟨subd9_6_185, List.forall_mem_cons.2 ⟨subd9_6_186, List.forall_mem_cons.2 ⟨subd9_6_187, List.forall_mem_cons.2 ⟨subd9_6_188, List.forall_mem_cons.2 ⟨subd9_6_189, List.forall_mem_cons.2 ⟨subd9_6_190, List.forall_mem_cons.2 ⟨subd9_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_192 : subd9_6 [-2, 2, 0] = true := by decide +kernel
theorem subd9_6_193 : subd9_6 [-2, 2, 1] = true := by decide +kernel
theorem subd9_6_194 : subd9_6 [-2, 2, 2] = true := by decide +kernel
theorem subd9_6_195 : subd9_6 [-2, 2, 3] = true := by decide +kernel
theorem subd9_6_196 : subd9_6 [-2, 2, 4] = true := by decide +kernel
theorem subd9_6_197 : subd9_6 [-2, 2, 5] = true := by decide +kernel
theorem subd9_6_198 : subd9_6 [-2, 2, 6] = true := by decide +kernel
theorem subd9_6_199 : subd9_6 [-2, 3, -8] = true := by decide +kernel
theorem subd9_6_200 : subd9_6 [-2, 3, -7] = true := by decide +kernel
theorem subd9_6_201 : subd9_6 [-2, 3, -6] = true := by decide +kernel
theorem subd9_6_202 : subd9_6 [-2, 3, -5] = true := by decide +kernel
theorem subd9_6_203 : subd9_6 [-2, 3, -4] = true := by decide +kernel
theorem subd9_6_204 : subd9_6 [-2, 3, -3] = true := by decide +kernel
theorem subd9_6_205 : subd9_6 [-2, 3, -2] = true := by decide +kernel
theorem subd9_6_206 : subd9_6 [-2, 3, -1] = true := by decide +kernel
theorem subd9_6_207 : subd9_6 [-2, 3, 0] = true := by decide +kernel
theorem subd9_6_208 : subd9_6 [-2, 3, 1] = true := by decide +kernel
theorem subd9_6_209 : subd9_6 [-2, 3, 2] = true := by decide +kernel
theorem subd9_6_210 : subd9_6 [-2, 3, 3] = true := by decide +kernel
theorem subd9_6_211 : subd9_6 [-2, 3, 4] = true := by decide +kernel
theorem subd9_6_212 : subd9_6 [-2, 3, 5] = true := by decide +kernel
theorem subd9_6_213 : subd9_6 [-2, 4] = true := by decide +kernel
theorem subd9_6_214 : subd9_6 [-2, 5] = true := by decide +kernel
theorem subd9_6_215 : subd9_6 [-1, -7] = true := by decide +kernel
theorem subd9_6_216 : subd9_6 [-1, -6] = true := by decide +kernel
theorem subd9_6_217 : subd9_6 [-1, -5] = true := by decide +kernel
theorem subd9_6_218 : subd9_6 [-1, -4, -6] = true := by decide +kernel
theorem subd9_6_219 : subd9_6 [-1, -4, -5] = true := by decide +kernel
theorem subd9_6_220 : subd9_6 [-1, -4, -4] = true := by decide +kernel
theorem subd9_6_221 : subd9_6 [-1, -4, -3] = true := by decide +kernel
theorem subd9_6_222 : subd9_6 [-1, -4, -2] = true := by decide +kernel
theorem subd9_6_223 : subd9_6 [-1, -4, -1] = true := by decide +kernel
theorem sbd9_6_6 : ∀ q ∈ blkd9_6_6, subd9_6 q = true := by
  unfold blkd9_6_6
  exact List.forall_mem_cons.2 ⟨subd9_6_192, List.forall_mem_cons.2 ⟨subd9_6_193, List.forall_mem_cons.2 ⟨subd9_6_194, List.forall_mem_cons.2 ⟨subd9_6_195, List.forall_mem_cons.2 ⟨subd9_6_196, List.forall_mem_cons.2 ⟨subd9_6_197, List.forall_mem_cons.2 ⟨subd9_6_198, List.forall_mem_cons.2 ⟨subd9_6_199, List.forall_mem_cons.2 ⟨subd9_6_200, List.forall_mem_cons.2 ⟨subd9_6_201, List.forall_mem_cons.2 ⟨subd9_6_202, List.forall_mem_cons.2 ⟨subd9_6_203, List.forall_mem_cons.2 ⟨subd9_6_204, List.forall_mem_cons.2 ⟨subd9_6_205, List.forall_mem_cons.2 ⟨subd9_6_206, List.forall_mem_cons.2 ⟨subd9_6_207, List.forall_mem_cons.2 ⟨subd9_6_208, List.forall_mem_cons.2 ⟨subd9_6_209, List.forall_mem_cons.2 ⟨subd9_6_210, List.forall_mem_cons.2 ⟨subd9_6_211, List.forall_mem_cons.2 ⟨subd9_6_212, List.forall_mem_cons.2 ⟨subd9_6_213, List.forall_mem_cons.2 ⟨subd9_6_214, List.forall_mem_cons.2 ⟨subd9_6_215, List.forall_mem_cons.2 ⟨subd9_6_216, List.forall_mem_cons.2 ⟨subd9_6_217, List.forall_mem_cons.2 ⟨subd9_6_218, List.forall_mem_cons.2 ⟨subd9_6_219, List.forall_mem_cons.2 ⟨subd9_6_220, List.forall_mem_cons.2 ⟨subd9_6_221, List.forall_mem_cons.2 ⟨subd9_6_222, List.forall_mem_cons.2 ⟨subd9_6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_224 : subd9_6 [-1, -4, 0] = true := by decide +kernel
theorem subd9_6_225 : subd9_6 [-1, -4, 1] = true := by decide +kernel
theorem subd9_6_226 : subd9_6 [-1, -4, 2] = true := by decide +kernel
theorem subd9_6_227 : subd9_6 [-1, -4, 3] = true := by decide +kernel
theorem subd9_6_228 : subd9_6 [-1, -4, 4] = true := by decide +kernel
theorem subd9_6_229 : subd9_6 [-1, -4, 5] = true := by decide +kernel
theorem subd9_6_230 : subd9_6 [-1, -4, 6] = true := by decide +kernel
theorem subd9_6_231 : subd9_6 [-1, -4, 7] = true := by decide +kernel
theorem subd9_6_232 : subd9_6 [-1, -3, -7] = true := by decide +kernel
theorem subd9_6_233 : subd9_6 [-1, -3, -6] = true := by decide +kernel
theorem subd9_6_234 : subd9_6 [-1, -3, -5] = true := by decide +kernel
theorem subd9_6_235 : subd9_6 [-1, -3, -4] = true := by decide +kernel
theorem subd9_6_236 : subd9_6 [-1, -3, -3] = true := by decide +kernel
theorem subd9_6_237 : subd9_6 [-1, -3, -2] = true := by decide +kernel
theorem subd9_6_238 : subd9_6 [-1, -3, -1] = true := by decide +kernel
theorem subd9_6_239 : subd9_6 [-1, -3, 0] = true := by decide +kernel
theorem subd9_6_240 : subd9_6 [-1, -3, 1] = true := by decide +kernel
theorem subd9_6_241 : subd9_6 [-1, -3, 2] = true := by decide +kernel
theorem subd9_6_242 : subd9_6 [-1, -3, 3] = true := by decide +kernel
theorem subd9_6_243 : subd9_6 [-1, -3, 4] = true := by decide +kernel
theorem subd9_6_244 : subd9_6 [-1, -3, 5] = true := by decide +kernel
theorem subd9_6_245 : subd9_6 [-1, -3, 6] = true := by decide +kernel
theorem subd9_6_246 : subd9_6 [-1, -3, 7] = true := by decide +kernel
theorem subd9_6_247 : subd9_6 [-1, -2, -8] = true := by decide +kernel
theorem subd9_6_248 : subd9_6 [-1, -2, -7] = true := by decide +kernel
theorem subd9_6_249 : subd9_6 [-1, -2, -6] = true := by decide +kernel
theorem subd9_6_250 : subd9_6 [-1, -2, -5] = true := by decide +kernel
theorem subd9_6_251 : subd9_6 [-1, -2, -4] = true := by decide +kernel
theorem subd9_6_252 : subd9_6 [-1, -2, -3] = true := by decide +kernel
theorem subd9_6_253 : subd9_6 [-1, -2, -2] = true := by decide +kernel
theorem subd9_6_254 : subd9_6 [-1, -2, -1] = true := by decide +kernel
theorem subd9_6_255 : subd9_6 [-1, -2, 0] = true := by decide +kernel
theorem sbd9_6_7 : ∀ q ∈ blkd9_6_7, subd9_6 q = true := by
  unfold blkd9_6_7
  exact List.forall_mem_cons.2 ⟨subd9_6_224, List.forall_mem_cons.2 ⟨subd9_6_225, List.forall_mem_cons.2 ⟨subd9_6_226, List.forall_mem_cons.2 ⟨subd9_6_227, List.forall_mem_cons.2 ⟨subd9_6_228, List.forall_mem_cons.2 ⟨subd9_6_229, List.forall_mem_cons.2 ⟨subd9_6_230, List.forall_mem_cons.2 ⟨subd9_6_231, List.forall_mem_cons.2 ⟨subd9_6_232, List.forall_mem_cons.2 ⟨subd9_6_233, List.forall_mem_cons.2 ⟨subd9_6_234, List.forall_mem_cons.2 ⟨subd9_6_235, List.forall_mem_cons.2 ⟨subd9_6_236, List.forall_mem_cons.2 ⟨subd9_6_237, List.forall_mem_cons.2 ⟨subd9_6_238, List.forall_mem_cons.2 ⟨subd9_6_239, List.forall_mem_cons.2 ⟨subd9_6_240, List.forall_mem_cons.2 ⟨subd9_6_241, List.forall_mem_cons.2 ⟨subd9_6_242, List.forall_mem_cons.2 ⟨subd9_6_243, List.forall_mem_cons.2 ⟨subd9_6_244, List.forall_mem_cons.2 ⟨subd9_6_245, List.forall_mem_cons.2 ⟨subd9_6_246, List.forall_mem_cons.2 ⟨subd9_6_247, List.forall_mem_cons.2 ⟨subd9_6_248, List.forall_mem_cons.2 ⟨subd9_6_249, List.forall_mem_cons.2 ⟨subd9_6_250, List.forall_mem_cons.2 ⟨subd9_6_251, List.forall_mem_cons.2 ⟨subd9_6_252, List.forall_mem_cons.2 ⟨subd9_6_253, List.forall_mem_cons.2 ⟨subd9_6_254, List.forall_mem_cons.2 ⟨subd9_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_256 : subd9_6 [-1, -2, 1] = true := by decide +kernel
theorem subd9_6_257 : subd9_6 [-1, -2, 2] = true := by decide +kernel
theorem subd9_6_258 : subd9_6 [-1, -2, 3] = true := by decide +kernel
theorem subd9_6_259 : subd9_6 [-1, -2, 4] = true := by decide +kernel
theorem subd9_6_260 : subd9_6 [-1, -2, 5] = true := by decide +kernel
theorem subd9_6_261 : subd9_6 [-1, -2, 6] = true := by decide +kernel
theorem subd9_6_262 : subd9_6 [-1, -2, 7] = true := by decide +kernel
theorem subd9_6_263 : subd9_6 [-1, -1, -9] = true := by decide +kernel
theorem subd9_6_264 : subd9_6 [-1, -1, -8] = true := by decide +kernel
theorem subd9_6_265 : subd9_6 [-1, -1, -7] = true := by decide +kernel
theorem subd9_6_266 : subd9_6 [-1, -1, -6] = true := by decide +kernel
theorem subd9_6_267 : subd9_6 [-1, -1, -5] = true := by decide +kernel
theorem subd9_6_268 : subd9_6 [-1, -1, -4] = true := by decide +kernel
theorem subd9_6_269 : subd9_6 [-1, -1, -3] = true := by decide +kernel
theorem subd9_6_270 : subd9_6 [-1, -1, -2] = true := by decide +kernel
theorem subd9_6_271 : subd9_6 [-1, -1, -1] = true := by decide +kernel
theorem subd9_6_272 : subd9_6 [-1, -1, 0] = true := by decide +kernel
theorem subd9_6_273 : subd9_6 [-1, -1, 1] = true := by decide +kernel
theorem subd9_6_274 : subd9_6 [-1, -1, 2] = true := by decide +kernel
theorem subd9_6_275 : subd9_6 [-1, -1, 3] = true := by decide +kernel
theorem subd9_6_276 : subd9_6 [-1, -1, 4] = true := by decide +kernel
theorem subd9_6_277 : subd9_6 [-1, -1, 5] = true := by decide +kernel
theorem subd9_6_278 : subd9_6 [-1, -1, 6] = true := by decide +kernel
theorem subd9_6_279 : subd9_6 [-1, -1, 7] = true := by decide +kernel
theorem subd9_6_280 : subd9_6 [-1, 0, -9] = true := by decide +kernel
theorem subd9_6_281 : subd9_6 [-1, 0, -8] = true := by decide +kernel
theorem subd9_6_282 : subd9_6 [-1, 0, -7] = true := by decide +kernel
theorem subd9_6_283 : subd9_6 [-1, 0, -6] = true := by decide +kernel
theorem subd9_6_284 : subd9_6 [-1, 0, -5] = true := by decide +kernel
theorem subd9_6_285 : subd9_6 [-1, 0, -4] = true := by decide +kernel
theorem subd9_6_286 : subd9_6 [-1, 0, -3] = true := by decide +kernel
theorem subd9_6_287 : subd9_6 [-1, 0, -2] = true := by decide +kernel
theorem sbd9_6_8 : ∀ q ∈ blkd9_6_8, subd9_6 q = true := by
  unfold blkd9_6_8
  exact List.forall_mem_cons.2 ⟨subd9_6_256, List.forall_mem_cons.2 ⟨subd9_6_257, List.forall_mem_cons.2 ⟨subd9_6_258, List.forall_mem_cons.2 ⟨subd9_6_259, List.forall_mem_cons.2 ⟨subd9_6_260, List.forall_mem_cons.2 ⟨subd9_6_261, List.forall_mem_cons.2 ⟨subd9_6_262, List.forall_mem_cons.2 ⟨subd9_6_263, List.forall_mem_cons.2 ⟨subd9_6_264, List.forall_mem_cons.2 ⟨subd9_6_265, List.forall_mem_cons.2 ⟨subd9_6_266, List.forall_mem_cons.2 ⟨subd9_6_267, List.forall_mem_cons.2 ⟨subd9_6_268, List.forall_mem_cons.2 ⟨subd9_6_269, List.forall_mem_cons.2 ⟨subd9_6_270, List.forall_mem_cons.2 ⟨subd9_6_271, List.forall_mem_cons.2 ⟨subd9_6_272, List.forall_mem_cons.2 ⟨subd9_6_273, List.forall_mem_cons.2 ⟨subd9_6_274, List.forall_mem_cons.2 ⟨subd9_6_275, List.forall_mem_cons.2 ⟨subd9_6_276, List.forall_mem_cons.2 ⟨subd9_6_277, List.forall_mem_cons.2 ⟨subd9_6_278, List.forall_mem_cons.2 ⟨subd9_6_279, List.forall_mem_cons.2 ⟨subd9_6_280, List.forall_mem_cons.2 ⟨subd9_6_281, List.forall_mem_cons.2 ⟨subd9_6_282, List.forall_mem_cons.2 ⟨subd9_6_283, List.forall_mem_cons.2 ⟨subd9_6_284, List.forall_mem_cons.2 ⟨subd9_6_285, List.forall_mem_cons.2 ⟨subd9_6_286, List.forall_mem_cons.2 ⟨subd9_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_288 : subd9_6 [-1, 0, -1] = true := by decide +kernel
theorem subd9_6_289 : subd9_6 [-1, 0, 0] = true := by decide +kernel
theorem subd9_6_290 : subd9_6 [-1, 0, 1] = true := by decide +kernel
theorem subd9_6_291 : subd9_6 [-1, 0, 2] = true := by decide +kernel
theorem subd9_6_292 : subd9_6 [-1, 0, 3] = true := by decide +kernel
theorem subd9_6_293 : subd9_6 [-1, 0, 4] = true := by decide +kernel
theorem subd9_6_294 : subd9_6 [-1, 0, 5] = true := by decide +kernel
theorem subd9_6_295 : subd9_6 [-1, 0, 6] = true := by decide +kernel
theorem subd9_6_296 : subd9_6 [-1, 0, 7] = true := by decide +kernel
theorem subd9_6_297 : subd9_6 [-1, 1, -9] = true := by decide +kernel
theorem subd9_6_298 : subd9_6 [-1, 1, -8] = true := by decide +kernel
theorem subd9_6_299 : subd9_6 [-1, 1, -7] = true := by decide +kernel
theorem subd9_6_300 : subd9_6 [-1, 1, -6] = true := by decide +kernel
theorem subd9_6_301 : subd9_6 [-1, 1, -5] = true := by decide +kernel
theorem subd9_6_302 : subd9_6 [-1, 1, -4] = true := by decide +kernel
theorem subd9_6_303 : subd9_6 [-1, 1, -3] = true := by decide +kernel
theorem subd9_6_304 : subd9_6 [-1, 1, -2] = true := by decide +kernel
theorem subd9_6_305 : subd9_6 [-1, 1, -1] = true := by decide +kernel
theorem subd9_6_306 : subd9_6 [-1, 1, 0] = true := by decide +kernel
theorem subd9_6_307 : subd9_6 [-1, 1, 1] = true := by decide +kernel
theorem subd9_6_308 : subd9_6 [-1, 1, 2] = true := by decide +kernel
theorem subd9_6_309 : subd9_6 [-1, 1, 3] = true := by decide +kernel
theorem subd9_6_310 : subd9_6 [-1, 1, 4] = true := by decide +kernel
theorem subd9_6_311 : subd9_6 [-1, 1, 5] = true := by decide +kernel
theorem subd9_6_312 : subd9_6 [-1, 1, 6] = true := by decide +kernel
theorem subd9_6_313 : subd9_6 [-1, 1, 7] = true := by decide +kernel
theorem subd9_6_314 : subd9_6 [-1, 2, -9] = true := by decide +kernel
theorem subd9_6_315 : subd9_6 [-1, 2, -8] = true := by decide +kernel
theorem subd9_6_316 : subd9_6 [-1, 2, -7] = true := by decide +kernel
theorem subd9_6_317 : subd9_6 [-1, 2, -6] = true := by decide +kernel
theorem subd9_6_318 : subd9_6 [-1, 2, -5] = true := by decide +kernel
theorem subd9_6_319 : subd9_6 [-1, 2, -4] = true := by decide +kernel
theorem sbd9_6_9 : ∀ q ∈ blkd9_6_9, subd9_6 q = true := by
  unfold blkd9_6_9
  exact List.forall_mem_cons.2 ⟨subd9_6_288, List.forall_mem_cons.2 ⟨subd9_6_289, List.forall_mem_cons.2 ⟨subd9_6_290, List.forall_mem_cons.2 ⟨subd9_6_291, List.forall_mem_cons.2 ⟨subd9_6_292, List.forall_mem_cons.2 ⟨subd9_6_293, List.forall_mem_cons.2 ⟨subd9_6_294, List.forall_mem_cons.2 ⟨subd9_6_295, List.forall_mem_cons.2 ⟨subd9_6_296, List.forall_mem_cons.2 ⟨subd9_6_297, List.forall_mem_cons.2 ⟨subd9_6_298, List.forall_mem_cons.2 ⟨subd9_6_299, List.forall_mem_cons.2 ⟨subd9_6_300, List.forall_mem_cons.2 ⟨subd9_6_301, List.forall_mem_cons.2 ⟨subd9_6_302, List.forall_mem_cons.2 ⟨subd9_6_303, List.forall_mem_cons.2 ⟨subd9_6_304, List.forall_mem_cons.2 ⟨subd9_6_305, List.forall_mem_cons.2 ⟨subd9_6_306, List.forall_mem_cons.2 ⟨subd9_6_307, List.forall_mem_cons.2 ⟨subd9_6_308, List.forall_mem_cons.2 ⟨subd9_6_309, List.forall_mem_cons.2 ⟨subd9_6_310, List.forall_mem_cons.2 ⟨subd9_6_311, List.forall_mem_cons.2 ⟨subd9_6_312, List.forall_mem_cons.2 ⟨subd9_6_313, List.forall_mem_cons.2 ⟨subd9_6_314, List.forall_mem_cons.2 ⟨subd9_6_315, List.forall_mem_cons.2 ⟨subd9_6_316, List.forall_mem_cons.2 ⟨subd9_6_317, List.forall_mem_cons.2 ⟨subd9_6_318, List.forall_mem_cons.2 ⟨subd9_6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_320 : subd9_6 [-1, 2, -3] = true := by decide +kernel
theorem subd9_6_321 : subd9_6 [-1, 2, -2] = true := by decide +kernel
theorem subd9_6_322 : subd9_6 [-1, 2, -1] = true := by decide +kernel
theorem subd9_6_323 : subd9_6 [-1, 2, 0] = true := by decide +kernel
theorem subd9_6_324 : subd9_6 [-1, 2, 1] = true := by decide +kernel
theorem subd9_6_325 : subd9_6 [-1, 2, 2] = true := by decide +kernel
theorem subd9_6_326 : subd9_6 [-1, 2, 3] = true := by decide +kernel
theorem subd9_6_327 : subd9_6 [-1, 2, 4] = true := by decide +kernel
theorem subd9_6_328 : subd9_6 [-1, 2, 5] = true := by decide +kernel
theorem subd9_6_329 : subd9_6 [-1, 2, 6] = true := by decide +kernel
theorem subd9_6_330 : subd9_6 [-1, 3, -8] = true := by decide +kernel
theorem subd9_6_331 : subd9_6 [-1, 3, -7] = true := by decide +kernel
theorem subd9_6_332 : subd9_6 [-1, 3, -6] = true := by decide +kernel
theorem subd9_6_333 : subd9_6 [-1, 3, -5] = true := by decide +kernel
theorem subd9_6_334 : subd9_6 [-1, 3, -4] = true := by decide +kernel
theorem subd9_6_335 : subd9_6 [-1, 3, -3] = true := by decide +kernel
theorem subd9_6_336 : subd9_6 [-1, 3, -2] = true := by decide +kernel
theorem subd9_6_337 : subd9_6 [-1, 3, -1] = true := by decide +kernel
theorem subd9_6_338 : subd9_6 [-1, 3, 0] = true := by decide +kernel
theorem subd9_6_339 : subd9_6 [-1, 3, 1] = true := by decide +kernel
theorem subd9_6_340 : subd9_6 [-1, 3, 2] = true := by decide +kernel
theorem subd9_6_341 : subd9_6 [-1, 3, 3] = true := by decide +kernel
theorem subd9_6_342 : subd9_6 [-1, 3, 4] = true := by decide +kernel
theorem subd9_6_343 : subd9_6 [-1, 3, 5] = true := by decide +kernel
theorem subd9_6_344 : subd9_6 [-1, 4] = true := by decide +kernel
theorem subd9_6_345 : subd9_6 [-1, 5] = true := by decide +kernel
theorem subd9_6_346 : subd9_6 [-1, 6] = true := by decide +kernel
theorem subd9_6_347 : subd9_6 [0, -7] = true := by decide +kernel
theorem subd9_6_348 : subd9_6 [0, -6] = true := by decide +kernel
theorem subd9_6_349 : subd9_6 [0, -5] = true := by decide +kernel
theorem subd9_6_350 : subd9_6 [0, -4, -6] = true := by decide +kernel
theorem subd9_6_351 : subd9_6 [0, -4, -5] = true := by decide +kernel
theorem sbd9_6_10 : ∀ q ∈ blkd9_6_10, subd9_6 q = true := by
  unfold blkd9_6_10
  exact List.forall_mem_cons.2 ⟨subd9_6_320, List.forall_mem_cons.2 ⟨subd9_6_321, List.forall_mem_cons.2 ⟨subd9_6_322, List.forall_mem_cons.2 ⟨subd9_6_323, List.forall_mem_cons.2 ⟨subd9_6_324, List.forall_mem_cons.2 ⟨subd9_6_325, List.forall_mem_cons.2 ⟨subd9_6_326, List.forall_mem_cons.2 ⟨subd9_6_327, List.forall_mem_cons.2 ⟨subd9_6_328, List.forall_mem_cons.2 ⟨subd9_6_329, List.forall_mem_cons.2 ⟨subd9_6_330, List.forall_mem_cons.2 ⟨subd9_6_331, List.forall_mem_cons.2 ⟨subd9_6_332, List.forall_mem_cons.2 ⟨subd9_6_333, List.forall_mem_cons.2 ⟨subd9_6_334, List.forall_mem_cons.2 ⟨subd9_6_335, List.forall_mem_cons.2 ⟨subd9_6_336, List.forall_mem_cons.2 ⟨subd9_6_337, List.forall_mem_cons.2 ⟨subd9_6_338, List.forall_mem_cons.2 ⟨subd9_6_339, List.forall_mem_cons.2 ⟨subd9_6_340, List.forall_mem_cons.2 ⟨subd9_6_341, List.forall_mem_cons.2 ⟨subd9_6_342, List.forall_mem_cons.2 ⟨subd9_6_343, List.forall_mem_cons.2 ⟨subd9_6_344, List.forall_mem_cons.2 ⟨subd9_6_345, List.forall_mem_cons.2 ⟨subd9_6_346, List.forall_mem_cons.2 ⟨subd9_6_347, List.forall_mem_cons.2 ⟨subd9_6_348, List.forall_mem_cons.2 ⟨subd9_6_349, List.forall_mem_cons.2 ⟨subd9_6_350, List.forall_mem_cons.2 ⟨subd9_6_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_352 : subd9_6 [0, -4, -4] = true := by decide +kernel
theorem subd9_6_353 : subd9_6 [0, -4, -3] = true := by decide +kernel
theorem subd9_6_354 : subd9_6 [0, -4, -2] = true := by decide +kernel
theorem subd9_6_355 : subd9_6 [0, -4, -1] = true := by decide +kernel
theorem subd9_6_356 : subd9_6 [0, -4, 0] = true := by decide +kernel
theorem subd9_6_357 : subd9_6 [0, -4, 1] = true := by decide +kernel
theorem subd9_6_358 : subd9_6 [0, -4, 2] = true := by decide +kernel
theorem subd9_6_359 : subd9_6 [0, -4, 3] = true := by decide +kernel
theorem subd9_6_360 : subd9_6 [0, -4, 4] = true := by decide +kernel
theorem subd9_6_361 : subd9_6 [0, -4, 5] = true := by decide +kernel
theorem subd9_6_362 : subd9_6 [0, -4, 6] = true := by decide +kernel
theorem subd9_6_363 : subd9_6 [0, -4, 7] = true := by decide +kernel
theorem subd9_6_364 : subd9_6 [0, -3, -7] = true := by decide +kernel
theorem subd9_6_365 : subd9_6 [0, -3, -6] = true := by decide +kernel
theorem subd9_6_366 : subd9_6 [0, -3, -5] = true := by decide +kernel
theorem subd9_6_367 : subd9_6 [0, -3, -4] = true := by decide +kernel
theorem subd9_6_368 : subd9_6 [0, -3, -3] = true := by decide +kernel
theorem subd9_6_369 : subd9_6 [0, -3, -2] = true := by decide +kernel
theorem subd9_6_370 : subd9_6 [0, -3, -1] = true := by decide +kernel
theorem subd9_6_371 : subd9_6 [0, -3, 0] = true := by decide +kernel
theorem subd9_6_372 : subd9_6 [0, -3, 1] = true := by decide +kernel
theorem subd9_6_373 : subd9_6 [0, -3, 2] = true := by decide +kernel
theorem subd9_6_374 : subd9_6 [0, -3, 3] = true := by decide +kernel
theorem subd9_6_375 : subd9_6 [0, -3, 4] = true := by decide +kernel
theorem subd9_6_376 : subd9_6 [0, -3, 5] = true := by decide +kernel
theorem subd9_6_377 : subd9_6 [0, -3, 6] = true := by decide +kernel
theorem subd9_6_378 : subd9_6 [0, -3, 7] = true := by decide +kernel
theorem subd9_6_379 : subd9_6 [0, -2, -8] = true := by decide +kernel
theorem subd9_6_380 : subd9_6 [0, -2, -7] = true := by decide +kernel
theorem subd9_6_381 : subd9_6 [0, -2, -6] = true := by decide +kernel
theorem subd9_6_382 : subd9_6 [0, -2, -5] = true := by decide +kernel
theorem subd9_6_383 : subd9_6 [0, -2, -4] = true := by decide +kernel
theorem sbd9_6_11 : ∀ q ∈ blkd9_6_11, subd9_6 q = true := by
  unfold blkd9_6_11
  exact List.forall_mem_cons.2 ⟨subd9_6_352, List.forall_mem_cons.2 ⟨subd9_6_353, List.forall_mem_cons.2 ⟨subd9_6_354, List.forall_mem_cons.2 ⟨subd9_6_355, List.forall_mem_cons.2 ⟨subd9_6_356, List.forall_mem_cons.2 ⟨subd9_6_357, List.forall_mem_cons.2 ⟨subd9_6_358, List.forall_mem_cons.2 ⟨subd9_6_359, List.forall_mem_cons.2 ⟨subd9_6_360, List.forall_mem_cons.2 ⟨subd9_6_361, List.forall_mem_cons.2 ⟨subd9_6_362, List.forall_mem_cons.2 ⟨subd9_6_363, List.forall_mem_cons.2 ⟨subd9_6_364, List.forall_mem_cons.2 ⟨subd9_6_365, List.forall_mem_cons.2 ⟨subd9_6_366, List.forall_mem_cons.2 ⟨subd9_6_367, List.forall_mem_cons.2 ⟨subd9_6_368, List.forall_mem_cons.2 ⟨subd9_6_369, List.forall_mem_cons.2 ⟨subd9_6_370, List.forall_mem_cons.2 ⟨subd9_6_371, List.forall_mem_cons.2 ⟨subd9_6_372, List.forall_mem_cons.2 ⟨subd9_6_373, List.forall_mem_cons.2 ⟨subd9_6_374, List.forall_mem_cons.2 ⟨subd9_6_375, List.forall_mem_cons.2 ⟨subd9_6_376, List.forall_mem_cons.2 ⟨subd9_6_377, List.forall_mem_cons.2 ⟨subd9_6_378, List.forall_mem_cons.2 ⟨subd9_6_379, List.forall_mem_cons.2 ⟨subd9_6_380, List.forall_mem_cons.2 ⟨subd9_6_381, List.forall_mem_cons.2 ⟨subd9_6_382, List.forall_mem_cons.2 ⟨subd9_6_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
