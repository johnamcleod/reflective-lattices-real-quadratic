import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_0 : subd8_1 [-3, -3] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-3, -2] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-3, -1] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-3, 0] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-3, 1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-3, 2] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-2, 0, -6] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-2, 0, -5] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-2, 0, -4] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-2, 0, -3] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-2, 0, -2] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-2, 0, -1] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-2, 0, 0] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [-2, 0, 1] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [-2, 0, 2] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [-2, 0, 3] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [-2, 0, 4] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [-2, 0, 5] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [-2, 0, 6] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [-2, 3] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [-1, -1, -7] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [-1, -1, -6] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [-1, -1, -5] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [-1, -1, -4] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [-1, -1, -3] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [-1, -1, -2] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [-1, -1, -1] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [-1, -1, 0] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [-1, -1, 1] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [-1, -1, 2] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [-1, -1, 3] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [-1, -1, 4] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [-1, -1, 5] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [-1, -1, 6] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [-1, 0, -7] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [-1, 0, -6] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [-1, 0, -5] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [-1, 0, -4] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [-1, 0, -3] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [-1, 0, -2] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [-1, 0, -1] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [-1, 0, 0] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [-1, 0, 1] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [-1, 0, 2] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [-1, 0, 3] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [-1, 0, 4] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [-1, 0, 5] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [-1, 0, 6] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [-1, 0, 7] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [-1, 1, -7] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [-1, 1, -6] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [-1, 1, -5] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [-1, 1, -4] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [-1, 1, -3] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [-1, 1, -2] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [-1, 1, -1] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [-1, 1, 0] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [-1, 1, 1] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [-1, 1, 2] = true := by decide +kernel
theorem subd8_1_68 : subd8_1 [-1, 1, 3] = true := by decide +kernel
theorem subd8_1_69 : subd8_1 [-1, 1, 4] = true := by decide +kernel
theorem subd8_1_70 : subd8_1 [-1, 1, 5] = true := by decide +kernel
theorem subd8_1_71 : subd8_1 [-1, 1, 6] = true := by decide +kernel
theorem subd8_1_72 : subd8_1 [-1, 1, 7] = true := by decide +kernel
theorem subd8_1_73 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_74 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_75 : subd8_1 [-1, 4] = true := by decide +kernel
theorem subd8_1_76 : subd8_1 [0, -5] = true := by decide +kernel
theorem subd8_1_77 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_78 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_79 : subd8_1 [0, -2, -7] = true := by decide +kernel
theorem subd8_1_80 : subd8_1 [0, -2, -6] = true := by decide +kernel
theorem subd8_1_81 : subd8_1 [0, -2, -5] = true := by decide +kernel
theorem subd8_1_82 : subd8_1 [0, -2, -4] = true := by decide +kernel
theorem subd8_1_83 : subd8_1 [0, -2, -3] = true := by decide +kernel
theorem subd8_1_84 : subd8_1 [0, -2, -2] = true := by decide +kernel
theorem subd8_1_85 : subd8_1 [0, -2, -1] = true := by decide +kernel
theorem subd8_1_86 : subd8_1 [0, -2, 0] = true := by decide +kernel
theorem subd8_1_87 : subd8_1 [0, -2, 1] = true := by decide +kernel
theorem subd8_1_88 : subd8_1 [0, -2, 2] = true := by decide +kernel
theorem subd8_1_89 : subd8_1 [0, -2, 3] = true := by decide +kernel
theorem subd8_1_90 : subd8_1 [0, -2, 4] = true := by decide +kernel
theorem subd8_1_91 : subd8_1 [0, -2, 5] = true := by decide +kernel
theorem subd8_1_92 : subd8_1 [0, -2, 6] = true := by decide +kernel
theorem subd8_1_93 : subd8_1 [0, -1, -8] = true := by decide +kernel
theorem subd8_1_94 : subd8_1 [0, -1, -7] = true := by decide +kernel
theorem subd8_1_95 : subd8_1 [0, -1, -6] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_cons.2 ⟨subd8_1_68, List.forall_mem_cons.2 ⟨subd8_1_69, List.forall_mem_cons.2 ⟨subd8_1_70, List.forall_mem_cons.2 ⟨subd8_1_71, List.forall_mem_cons.2 ⟨subd8_1_72, List.forall_mem_cons.2 ⟨subd8_1_73, List.forall_mem_cons.2 ⟨subd8_1_74, List.forall_mem_cons.2 ⟨subd8_1_75, List.forall_mem_cons.2 ⟨subd8_1_76, List.forall_mem_cons.2 ⟨subd8_1_77, List.forall_mem_cons.2 ⟨subd8_1_78, List.forall_mem_cons.2 ⟨subd8_1_79, List.forall_mem_cons.2 ⟨subd8_1_80, List.forall_mem_cons.2 ⟨subd8_1_81, List.forall_mem_cons.2 ⟨subd8_1_82, List.forall_mem_cons.2 ⟨subd8_1_83, List.forall_mem_cons.2 ⟨subd8_1_84, List.forall_mem_cons.2 ⟨subd8_1_85, List.forall_mem_cons.2 ⟨subd8_1_86, List.forall_mem_cons.2 ⟨subd8_1_87, List.forall_mem_cons.2 ⟨subd8_1_88, List.forall_mem_cons.2 ⟨subd8_1_89, List.forall_mem_cons.2 ⟨subd8_1_90, List.forall_mem_cons.2 ⟨subd8_1_91, List.forall_mem_cons.2 ⟨subd8_1_92, List.forall_mem_cons.2 ⟨subd8_1_93, List.forall_mem_cons.2 ⟨subd8_1_94, List.forall_mem_cons.2 ⟨subd8_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_96 : subd8_1 [0, -1, -5] = true := by decide +kernel
theorem subd8_1_97 : subd8_1 [0, -1, -4] = true := by decide +kernel
theorem subd8_1_98 : subd8_1 [0, -1, -3] = true := by decide +kernel
theorem subd8_1_99 : subd8_1 [0, -1, -2] = true := by decide +kernel
theorem subd8_1_100 : subd8_1 [0, -1, -1] = true := by decide +kernel
theorem subd8_1_101 : subd8_1 [0, -1, 0] = true := by decide +kernel
theorem subd8_1_102 : subd8_1 [0, -1, 1] = true := by decide +kernel
theorem subd8_1_103 : subd8_1 [0, -1, 2] = true := by decide +kernel
theorem subd8_1_104 : subd8_1 [0, -1, 3] = true := by decide +kernel
theorem subd8_1_105 : subd8_1 [0, -1, 4] = true := by decide +kernel
theorem subd8_1_106 : subd8_1 [0, -1, 5] = true := by decide +kernel
theorem subd8_1_107 : subd8_1 [0, -1, 6] = true := by decide +kernel
theorem subd8_1_108 : subd8_1 [0, -1, 7] = true := by decide +kernel
theorem subd8_1_109 : subd8_1 [0, 0, -8] = true := by decide +kernel
theorem subd8_1_110 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_111 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_112 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_113 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_114 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_115 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_116 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_117 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_118 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_119 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_120 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_121 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_122 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_123 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem subd8_1_124 : subd8_1 [0, 0, 7] = true := by decide +kernel
theorem subd8_1_125 : subd8_1 [0, 1, -8] = true := by decide +kernel
theorem subd8_1_126 : subd8_1 [0, 1, -7] = true := by decide +kernel
theorem subd8_1_127 : subd8_1 [0, 1, -6] = true := by decide +kernel
theorem sbd8_1_3 : ∀ q ∈ blkd8_1_3, subd8_1 q = true := by
  unfold blkd8_1_3
  exact List.forall_mem_cons.2 ⟨subd8_1_96, List.forall_mem_cons.2 ⟨subd8_1_97, List.forall_mem_cons.2 ⟨subd8_1_98, List.forall_mem_cons.2 ⟨subd8_1_99, List.forall_mem_cons.2 ⟨subd8_1_100, List.forall_mem_cons.2 ⟨subd8_1_101, List.forall_mem_cons.2 ⟨subd8_1_102, List.forall_mem_cons.2 ⟨subd8_1_103, List.forall_mem_cons.2 ⟨subd8_1_104, List.forall_mem_cons.2 ⟨subd8_1_105, List.forall_mem_cons.2 ⟨subd8_1_106, List.forall_mem_cons.2 ⟨subd8_1_107, List.forall_mem_cons.2 ⟨subd8_1_108, List.forall_mem_cons.2 ⟨subd8_1_109, List.forall_mem_cons.2 ⟨subd8_1_110, List.forall_mem_cons.2 ⟨subd8_1_111, List.forall_mem_cons.2 ⟨subd8_1_112, List.forall_mem_cons.2 ⟨subd8_1_113, List.forall_mem_cons.2 ⟨subd8_1_114, List.forall_mem_cons.2 ⟨subd8_1_115, List.forall_mem_cons.2 ⟨subd8_1_116, List.forall_mem_cons.2 ⟨subd8_1_117, List.forall_mem_cons.2 ⟨subd8_1_118, List.forall_mem_cons.2 ⟨subd8_1_119, List.forall_mem_cons.2 ⟨subd8_1_120, List.forall_mem_cons.2 ⟨subd8_1_121, List.forall_mem_cons.2 ⟨subd8_1_122, List.forall_mem_cons.2 ⟨subd8_1_123, List.forall_mem_cons.2 ⟨subd8_1_124, List.forall_mem_cons.2 ⟨subd8_1_125, List.forall_mem_cons.2 ⟨subd8_1_126, List.forall_mem_cons.2 ⟨subd8_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_128 : subd8_1 [0, 1, -5] = true := by decide +kernel
theorem subd8_1_129 : subd8_1 [0, 1, -4] = true := by decide +kernel
theorem subd8_1_130 : subd8_1 [0, 1, -3] = true := by decide +kernel
theorem subd8_1_131 : subd8_1 [0, 1, -2] = true := by decide +kernel
theorem subd8_1_132 : subd8_1 [0, 1, -1] = true := by decide +kernel
theorem subd8_1_133 : subd8_1 [0, 1, 0] = true := by decide +kernel
theorem subd8_1_134 : subd8_1 [0, 1, 1] = true := by decide +kernel
theorem subd8_1_135 : subd8_1 [0, 1, 2] = true := by decide +kernel
theorem subd8_1_136 : subd8_1 [0, 1, 3] = true := by decide +kernel
theorem subd8_1_137 : subd8_1 [0, 1, 4] = true := by decide +kernel
theorem subd8_1_138 : subd8_1 [0, 1, 5] = true := by decide +kernel
theorem subd8_1_139 : subd8_1 [0, 1, 6] = true := by decide +kernel
theorem subd8_1_140 : subd8_1 [0, 1, 7] = true := by decide +kernel
theorem subd8_1_141 : subd8_1 [0, 2, -7] = true := by decide +kernel
theorem subd8_1_142 : subd8_1 [0, 2, -6] = true := by decide +kernel
theorem subd8_1_143 : subd8_1 [0, 2, -5] = true := by decide +kernel
theorem subd8_1_144 : subd8_1 [0, 2, -4] = true := by decide +kernel
theorem subd8_1_145 : subd8_1 [0, 2, -3] = true := by decide +kernel
theorem subd8_1_146 : subd8_1 [0, 2, -2] = true := by decide +kernel
theorem subd8_1_147 : subd8_1 [0, 2, -1] = true := by decide +kernel
theorem subd8_1_148 : subd8_1 [0, 2, 0] = true := by decide +kernel
theorem subd8_1_149 : subd8_1 [0, 2, 1] = true := by decide +kernel
theorem subd8_1_150 : subd8_1 [0, 2, 2] = true := by decide +kernel
theorem subd8_1_151 : subd8_1 [0, 2, 3] = true := by decide +kernel
theorem subd8_1_152 : subd8_1 [0, 2, 4] = true := by decide +kernel
theorem subd8_1_153 : subd8_1 [0, 2, 5] = true := by decide +kernel
theorem subd8_1_154 : subd8_1 [0, 2, 6] = true := by decide +kernel
theorem subd8_1_155 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_156 : subd8_1 [0, 4] = true := by decide +kernel
theorem subd8_1_157 : subd8_1 [1, -5] = true := by decide +kernel
theorem subd8_1_158 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_159 : subd8_1 [1, -3] = true := by decide +kernel
theorem sbd8_1_4 : ∀ q ∈ blkd8_1_4, subd8_1 q = true := by
  unfold blkd8_1_4
  exact List.forall_mem_cons.2 ⟨subd8_1_128, List.forall_mem_cons.2 ⟨subd8_1_129, List.forall_mem_cons.2 ⟨subd8_1_130, List.forall_mem_cons.2 ⟨subd8_1_131, List.forall_mem_cons.2 ⟨subd8_1_132, List.forall_mem_cons.2 ⟨subd8_1_133, List.forall_mem_cons.2 ⟨subd8_1_134, List.forall_mem_cons.2 ⟨subd8_1_135, List.forall_mem_cons.2 ⟨subd8_1_136, List.forall_mem_cons.2 ⟨subd8_1_137, List.forall_mem_cons.2 ⟨subd8_1_138, List.forall_mem_cons.2 ⟨subd8_1_139, List.forall_mem_cons.2 ⟨subd8_1_140, List.forall_mem_cons.2 ⟨subd8_1_141, List.forall_mem_cons.2 ⟨subd8_1_142, List.forall_mem_cons.2 ⟨subd8_1_143, List.forall_mem_cons.2 ⟨subd8_1_144, List.forall_mem_cons.2 ⟨subd8_1_145, List.forall_mem_cons.2 ⟨subd8_1_146, List.forall_mem_cons.2 ⟨subd8_1_147, List.forall_mem_cons.2 ⟨subd8_1_148, List.forall_mem_cons.2 ⟨subd8_1_149, List.forall_mem_cons.2 ⟨subd8_1_150, List.forall_mem_cons.2 ⟨subd8_1_151, List.forall_mem_cons.2 ⟨subd8_1_152, List.forall_mem_cons.2 ⟨subd8_1_153, List.forall_mem_cons.2 ⟨subd8_1_154, List.forall_mem_cons.2 ⟨subd8_1_155, List.forall_mem_cons.2 ⟨subd8_1_156, List.forall_mem_cons.2 ⟨subd8_1_157, List.forall_mem_cons.2 ⟨subd8_1_158, List.forall_mem_cons.2 ⟨subd8_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_160 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_161 : subd8_1 [1, -1, -8] = true := by decide +kernel
theorem subd8_1_162 : subd8_1 [1, -1, -7] = true := by decide +kernel
theorem subd8_1_163 : subd8_1 [1, -1, -6] = true := by decide +kernel
theorem subd8_1_164 : subd8_1 [1, -1, -5] = true := by decide +kernel
theorem subd8_1_165 : subd8_1 [1, -1, -4] = true := by decide +kernel
theorem subd8_1_166 : subd8_1 [1, -1, -3] = true := by decide +kernel
theorem subd8_1_167 : subd8_1 [1, -1, -2] = true := by decide +kernel
theorem subd8_1_168 : subd8_1 [1, -1, -1] = true := by decide +kernel
theorem subd8_1_169 : subd8_1 [1, -1, 0] = true := by decide +kernel
theorem subd8_1_170 : subd8_1 [1, -1, 1] = true := by decide +kernel
theorem subd8_1_171 : subd8_1 [1, -1, 2] = true := by decide +kernel
theorem subd8_1_172 : subd8_1 [1, -1, 3] = true := by decide +kernel
theorem subd8_1_173 : subd8_1 [1, -1, 4] = true := by decide +kernel
theorem subd8_1_174 : subd8_1 [1, -1, 5] = true := by decide +kernel
theorem subd8_1_175 : subd8_1 [1, -1, 6] = true := by decide +kernel
theorem subd8_1_176 : subd8_1 [1, 0, -8] = true := by decide +kernel
theorem subd8_1_177 : subd8_1 [1, 0, -7] = true := by decide +kernel
theorem subd8_1_178 : subd8_1 [1, 0, -6] = true := by decide +kernel
theorem subd8_1_179 : subd8_1 [1, 0, -5] = true := by decide +kernel
theorem subd8_1_180 : subd8_1 [1, 0, -4] = true := by decide +kernel
theorem subd8_1_181 : subd8_1 [1, 0, -3] = true := by decide +kernel
theorem subd8_1_182 : subd8_1 [1, 0, -2] = true := by decide +kernel
theorem subd8_1_183 : subd8_1 [1, 0, -1] = true := by decide +kernel
theorem subd8_1_184 : subd8_1 [1, 0, 0] = true := by decide +kernel
theorem subd8_1_185 : subd8_1 [1, 0, 1] = true := by decide +kernel
theorem subd8_1_186 : subd8_1 [1, 0, 2] = true := by decide +kernel
theorem subd8_1_187 : subd8_1 [1, 0, 3] = true := by decide +kernel
theorem subd8_1_188 : subd8_1 [1, 0, 4] = true := by decide +kernel
theorem subd8_1_189 : subd8_1 [1, 0, 5] = true := by decide +kernel
theorem subd8_1_190 : subd8_1 [1, 0, 6] = true := by decide +kernel
theorem subd8_1_191 : subd8_1 [1, 1, -7] = true := by decide +kernel
theorem sbd8_1_5 : ∀ q ∈ blkd8_1_5, subd8_1 q = true := by
  unfold blkd8_1_5
  exact List.forall_mem_cons.2 ⟨subd8_1_160, List.forall_mem_cons.2 ⟨subd8_1_161, List.forall_mem_cons.2 ⟨subd8_1_162, List.forall_mem_cons.2 ⟨subd8_1_163, List.forall_mem_cons.2 ⟨subd8_1_164, List.forall_mem_cons.2 ⟨subd8_1_165, List.forall_mem_cons.2 ⟨subd8_1_166, List.forall_mem_cons.2 ⟨subd8_1_167, List.forall_mem_cons.2 ⟨subd8_1_168, List.forall_mem_cons.2 ⟨subd8_1_169, List.forall_mem_cons.2 ⟨subd8_1_170, List.forall_mem_cons.2 ⟨subd8_1_171, List.forall_mem_cons.2 ⟨subd8_1_172, List.forall_mem_cons.2 ⟨subd8_1_173, List.forall_mem_cons.2 ⟨subd8_1_174, List.forall_mem_cons.2 ⟨subd8_1_175, List.forall_mem_cons.2 ⟨subd8_1_176, List.forall_mem_cons.2 ⟨subd8_1_177, List.forall_mem_cons.2 ⟨subd8_1_178, List.forall_mem_cons.2 ⟨subd8_1_179, List.forall_mem_cons.2 ⟨subd8_1_180, List.forall_mem_cons.2 ⟨subd8_1_181, List.forall_mem_cons.2 ⟨subd8_1_182, List.forall_mem_cons.2 ⟨subd8_1_183, List.forall_mem_cons.2 ⟨subd8_1_184, List.forall_mem_cons.2 ⟨subd8_1_185, List.forall_mem_cons.2 ⟨subd8_1_186, List.forall_mem_cons.2 ⟨subd8_1_187, List.forall_mem_cons.2 ⟨subd8_1_188, List.forall_mem_cons.2 ⟨subd8_1_189, List.forall_mem_cons.2 ⟨subd8_1_190, List.forall_mem_cons.2 ⟨subd8_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_192 : subd8_1 [1, 1, -6] = true := by decide +kernel
theorem subd8_1_193 : subd8_1 [1, 1, -5] = true := by decide +kernel
theorem subd8_1_194 : subd8_1 [1, 1, -4] = true := by decide +kernel
theorem subd8_1_195 : subd8_1 [1, 1, -3] = true := by decide +kernel
theorem subd8_1_196 : subd8_1 [1, 1, -2] = true := by decide +kernel
theorem subd8_1_197 : subd8_1 [1, 1, -1] = true := by decide +kernel
theorem subd8_1_198 : subd8_1 [1, 1, 0] = true := by decide +kernel
theorem subd8_1_199 : subd8_1 [1, 1, 1] = true := by decide +kernel
theorem subd8_1_200 : subd8_1 [1, 1, 2] = true := by decide +kernel
theorem subd8_1_201 : subd8_1 [1, 1, 3] = true := by decide +kernel
theorem subd8_1_202 : subd8_1 [1, 1, 4] = true := by decide +kernel
theorem subd8_1_203 : subd8_1 [1, 1, 5] = true := by decide +kernel
theorem subd8_1_204 : subd8_1 [1, 1, 6] = true := by decide +kernel
theorem subd8_1_205 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_206 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_207 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_208 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_209 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_210 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_211 : subd8_1 [2, 0, -7] = true := by decide +kernel
theorem subd8_1_212 : subd8_1 [2, 0, -6] = true := by decide +kernel
theorem subd8_1_213 : subd8_1 [2, 0, -5] = true := by decide +kernel
theorem subd8_1_214 : subd8_1 [2, 0, -4] = true := by decide +kernel
theorem subd8_1_215 : subd8_1 [2, 0, -3] = true := by decide +kernel
theorem subd8_1_216 : subd8_1 [2, 0, -2] = true := by decide +kernel
theorem subd8_1_217 : subd8_1 [2, 0, -1] = true := by decide +kernel
theorem subd8_1_218 : subd8_1 [2, 0, 0] = true := by decide +kernel
theorem subd8_1_219 : subd8_1 [2, 0, 1] = true := by decide +kernel
theorem subd8_1_220 : subd8_1 [2, 0, 2] = true := by decide +kernel
theorem subd8_1_221 : subd8_1 [2, 0, 3] = true := by decide +kernel
theorem subd8_1_222 : subd8_1 [2, 0, 4] = true := by decide +kernel
theorem subd8_1_223 : subd8_1 [2, 0, 5] = true := by decide +kernel
theorem sbd8_1_6 : ∀ q ∈ blkd8_1_6, subd8_1 q = true := by
  unfold blkd8_1_6
  exact List.forall_mem_cons.2 ⟨subd8_1_192, List.forall_mem_cons.2 ⟨subd8_1_193, List.forall_mem_cons.2 ⟨subd8_1_194, List.forall_mem_cons.2 ⟨subd8_1_195, List.forall_mem_cons.2 ⟨subd8_1_196, List.forall_mem_cons.2 ⟨subd8_1_197, List.forall_mem_cons.2 ⟨subd8_1_198, List.forall_mem_cons.2 ⟨subd8_1_199, List.forall_mem_cons.2 ⟨subd8_1_200, List.forall_mem_cons.2 ⟨subd8_1_201, List.forall_mem_cons.2 ⟨subd8_1_202, List.forall_mem_cons.2 ⟨subd8_1_203, List.forall_mem_cons.2 ⟨subd8_1_204, List.forall_mem_cons.2 ⟨subd8_1_205, List.forall_mem_cons.2 ⟨subd8_1_206, List.forall_mem_cons.2 ⟨subd8_1_207, List.forall_mem_cons.2 ⟨subd8_1_208, List.forall_mem_cons.2 ⟨subd8_1_209, List.forall_mem_cons.2 ⟨subd8_1_210, List.forall_mem_cons.2 ⟨subd8_1_211, List.forall_mem_cons.2 ⟨subd8_1_212, List.forall_mem_cons.2 ⟨subd8_1_213, List.forall_mem_cons.2 ⟨subd8_1_214, List.forall_mem_cons.2 ⟨subd8_1_215, List.forall_mem_cons.2 ⟨subd8_1_216, List.forall_mem_cons.2 ⟨subd8_1_217, List.forall_mem_cons.2 ⟨subd8_1_218, List.forall_mem_cons.2 ⟨subd8_1_219, List.forall_mem_cons.2 ⟨subd8_1_220, List.forall_mem_cons.2 ⟨subd8_1_221, List.forall_mem_cons.2 ⟨subd8_1_222, List.forall_mem_cons.2 ⟨subd8_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_224 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_225 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_226 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_227 : subd8_1 [3, -3] = true := by decide +kernel
theorem subd8_1_228 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_229 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_230 : subd8_1 [3, 0] = true := by decide +kernel
theorem subd8_1_231 : subd8_1 [3, 1] = true := by decide +kernel
theorem subd8_1_232 : subd8_1 [3, 2] = true := by decide +kernel
theorem sbd8_1_7 : ∀ q ∈ blkd8_1_7, subd8_1 q = true := by
  unfold blkd8_1_7
  exact List.forall_mem_cons.2 ⟨subd8_1_224, List.forall_mem_cons.2 ⟨subd8_1_225, List.forall_mem_cons.2 ⟨subd8_1_226, List.forall_mem_cons.2 ⟨subd8_1_227, List.forall_mem_cons.2 ⟨subd8_1_228, List.forall_mem_cons.2 ⟨subd8_1_229, List.forall_mem_cons.2 ⟨subd8_1_230, List.forall_mem_cons.2 ⟨subd8_1_231, List.forall_mem_cons.2 ⟨subd8_1_232, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-4] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-3, -2] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-3, -1] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-3, 0] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-3, 1, -6] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-3, 1, -5] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-3, 1, -4] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-3, 1, -3] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-3, 1, -2] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-3, 1, -1] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-3, 1, 0] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-3, 1, 1] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-3, 1, 2] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-3, 1, 3] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-3, 1, 4] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-3, 1, 5] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-3, 1, 6] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-3, 2, -6] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-3, 2, -5] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-3, 2, -4] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-3, 2, -3] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-3, 2, -2] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-3, 2, -1] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-3, 2, 0] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-3, 2, 1] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-3, 2, 2] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-3, 2, 3] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-3, 2, 4] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-3, 2, 5] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-3, 2, 6] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-3, 3] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-3, 4] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-2, -4] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-2, -3] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-2, -1, -7] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-2, -1, -6] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-2, -1, -5] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-2, -1, -4] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-2, -1, -3] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-2, -1, -2] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-2, -1, -1] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-2, -1, 0] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-2, -1, 1] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-2, -1, 2] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-2, -1, 3] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-2, -1, 4] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-2, -1, 5] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-2, -1, 6] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-2, -1, 7] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-2, 0, -8] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-2, 0, -7] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-2, 0, -6] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-2, 0, -5] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-2, 0, -4] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-2, 0, -3] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [-2, 0, -2] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [-2, 0, -1] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [-2, 0, 0] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [-2, 0, 1] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [-2, 0, 2] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [-2, 0, 3] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [-2, 0, 4] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [-2, 0, 5] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
