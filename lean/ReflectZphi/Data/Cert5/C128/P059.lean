import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_7_0 : subd8_7 [-4, -5] = true := by decide +kernel
theorem subd8_7_1 : subd8_7 [-4, -4] = true := by decide +kernel
theorem subd8_7_2 : subd8_7 [-4, -3] = true := by decide +kernel
theorem subd8_7_3 : subd8_7 [-4, -2] = true := by decide +kernel
theorem subd8_7_4 : subd8_7 [-4, -1] = true := by decide +kernel
theorem subd8_7_5 : subd8_7 [-4, 0] = true := by decide +kernel
theorem subd8_7_6 : subd8_7 [-4, 1] = true := by decide +kernel
theorem subd8_7_7 : subd8_7 [-3, -6] = true := by decide +kernel
theorem subd8_7_8 : subd8_7 [-3, -5] = true := by decide +kernel
theorem subd8_7_9 : subd8_7 [-3, -4] = true := by decide +kernel
theorem subd8_7_10 : subd8_7 [-3, -3] = true := by decide +kernel
theorem subd8_7_11 : subd8_7 [-3, -2] = true := by decide +kernel
theorem subd8_7_12 : subd8_7 [-3, -1] = true := by decide +kernel
theorem subd8_7_13 : subd8_7 [-3, 0] = true := by decide +kernel
theorem subd8_7_14 : subd8_7 [-3, 1] = true := by decide +kernel
theorem subd8_7_15 : subd8_7 [-3, 2] = true := by decide +kernel
theorem subd8_7_16 : subd8_7 [-3, 3] = true := by decide +kernel
theorem subd8_7_17 : subd8_7 [-2, -6] = true := by decide +kernel
theorem subd8_7_18 : subd8_7 [-2, -5] = true := by decide +kernel
theorem subd8_7_19 : subd8_7 [-2, -4] = true := by decide +kernel
theorem subd8_7_20 : subd8_7 [-2, -3] = true := by decide +kernel
theorem subd8_7_21 : subd8_7 [-2, -2] = true := by decide +kernel
theorem subd8_7_22 : subd8_7 [-2, -1, -7] = true := by decide +kernel
theorem subd8_7_23 : subd8_7 [-2, -1, -6] = true := by decide +kernel
theorem subd8_7_24 : subd8_7 [-2, -1, -5] = true := by decide +kernel
theorem subd8_7_25 : subd8_7 [-2, -1, -4] = true := by decide +kernel
theorem subd8_7_26 : subd8_7 [-2, -1, -3] = true := by decide +kernel
theorem subd8_7_27 : subd8_7 [-2, -1, -2] = true := by decide +kernel
theorem subd8_7_28 : subd8_7 [-2, -1, -1] = true := by decide +kernel
theorem subd8_7_29 : subd8_7 [-2, -1, 0] = true := by decide +kernel
theorem subd8_7_30 : subd8_7 [-2, -1, 1] = true := by decide +kernel
theorem subd8_7_31 : subd8_7 [-2, -1, 2] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_cons.2 ⟨subd8_7_1, List.forall_mem_cons.2 ⟨subd8_7_2, List.forall_mem_cons.2 ⟨subd8_7_3, List.forall_mem_cons.2 ⟨subd8_7_4, List.forall_mem_cons.2 ⟨subd8_7_5, List.forall_mem_cons.2 ⟨subd8_7_6, List.forall_mem_cons.2 ⟨subd8_7_7, List.forall_mem_cons.2 ⟨subd8_7_8, List.forall_mem_cons.2 ⟨subd8_7_9, List.forall_mem_cons.2 ⟨subd8_7_10, List.forall_mem_cons.2 ⟨subd8_7_11, List.forall_mem_cons.2 ⟨subd8_7_12, List.forall_mem_cons.2 ⟨subd8_7_13, List.forall_mem_cons.2 ⟨subd8_7_14, List.forall_mem_cons.2 ⟨subd8_7_15, List.forall_mem_cons.2 ⟨subd8_7_16, List.forall_mem_cons.2 ⟨subd8_7_17, List.forall_mem_cons.2 ⟨subd8_7_18, List.forall_mem_cons.2 ⟨subd8_7_19, List.forall_mem_cons.2 ⟨subd8_7_20, List.forall_mem_cons.2 ⟨subd8_7_21, List.forall_mem_cons.2 ⟨subd8_7_22, List.forall_mem_cons.2 ⟨subd8_7_23, List.forall_mem_cons.2 ⟨subd8_7_24, List.forall_mem_cons.2 ⟨subd8_7_25, List.forall_mem_cons.2 ⟨subd8_7_26, List.forall_mem_cons.2 ⟨subd8_7_27, List.forall_mem_cons.2 ⟨subd8_7_28, List.forall_mem_cons.2 ⟨subd8_7_29, List.forall_mem_cons.2 ⟨subd8_7_30, List.forall_mem_cons.2 ⟨subd8_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_32 : subd8_7 [-2, -1, 3] = true := by decide +kernel
theorem subd8_7_33 : subd8_7 [-2, -1, 4] = true := by decide +kernel
theorem subd8_7_34 : subd8_7 [-2, -1, 5] = true := by decide +kernel
theorem subd8_7_35 : subd8_7 [-2, -1, 6] = true := by decide +kernel
theorem subd8_7_36 : subd8_7 [-2, 0] = true := by decide +kernel
theorem subd8_7_37 : subd8_7 [-2, 1] = true := by decide +kernel
theorem subd8_7_38 : subd8_7 [-2, 2] = true := by decide +kernel
theorem subd8_7_39 : subd8_7 [-2, 3] = true := by decide +kernel
theorem subd8_7_40 : subd8_7 [-2, 4] = true := by decide +kernel
theorem subd8_7_41 : subd8_7 [-1, -6] = true := by decide +kernel
theorem subd8_7_42 : subd8_7 [-1, -5] = true := by decide +kernel
theorem subd8_7_43 : subd8_7 [-1, -4] = true := by decide +kernel
theorem subd8_7_44 : subd8_7 [-1, -3] = true := by decide +kernel
theorem subd8_7_45 : subd8_7 [-1, -2, -8] = true := by decide +kernel
theorem subd8_7_46 : subd8_7 [-1, -2, -7] = true := by decide +kernel
theorem subd8_7_47 : subd8_7 [-1, -2, -6] = true := by decide +kernel
theorem subd8_7_48 : subd8_7 [-1, -2, -5] = true := by decide +kernel
theorem subd8_7_49 : subd8_7 [-1, -2, -4] = true := by decide +kernel
theorem subd8_7_50 : subd8_7 [-1, -2, -3] = true := by decide +kernel
theorem subd8_7_51 : subd8_7 [-1, -2, -2] = true := by decide +kernel
theorem subd8_7_52 : subd8_7 [-1, -2, -1] = true := by decide +kernel
theorem subd8_7_53 : subd8_7 [-1, -2, 0] = true := by decide +kernel
theorem subd8_7_54 : subd8_7 [-1, -2, 1] = true := by decide +kernel
theorem subd8_7_55 : subd8_7 [-1, -2, 2] = true := by decide +kernel
theorem subd8_7_56 : subd8_7 [-1, -2, 3] = true := by decide +kernel
theorem subd8_7_57 : subd8_7 [-1, -2, 4] = true := by decide +kernel
theorem subd8_7_58 : subd8_7 [-1, -2, 5] = true := by decide +kernel
theorem subd8_7_59 : subd8_7 [-1, -1, -7] = true := by decide +kernel
theorem subd8_7_60 : subd8_7 [-1, -1, -6] = true := by decide +kernel
theorem subd8_7_61 : subd8_7 [-1, -1, -5] = true := by decide +kernel
theorem subd8_7_62 : subd8_7 [-1, -1, -4] = true := by decide +kernel
theorem subd8_7_63 : subd8_7 [-1, -1, -3] = true := by decide +kernel
theorem sbd8_7_1 : ∀ q ∈ blkd8_7_1, subd8_7 q = true := by
  unfold blkd8_7_1
  exact List.forall_mem_cons.2 ⟨subd8_7_32, List.forall_mem_cons.2 ⟨subd8_7_33, List.forall_mem_cons.2 ⟨subd8_7_34, List.forall_mem_cons.2 ⟨subd8_7_35, List.forall_mem_cons.2 ⟨subd8_7_36, List.forall_mem_cons.2 ⟨subd8_7_37, List.forall_mem_cons.2 ⟨subd8_7_38, List.forall_mem_cons.2 ⟨subd8_7_39, List.forall_mem_cons.2 ⟨subd8_7_40, List.forall_mem_cons.2 ⟨subd8_7_41, List.forall_mem_cons.2 ⟨subd8_7_42, List.forall_mem_cons.2 ⟨subd8_7_43, List.forall_mem_cons.2 ⟨subd8_7_44, List.forall_mem_cons.2 ⟨subd8_7_45, List.forall_mem_cons.2 ⟨subd8_7_46, List.forall_mem_cons.2 ⟨subd8_7_47, List.forall_mem_cons.2 ⟨subd8_7_48, List.forall_mem_cons.2 ⟨subd8_7_49, List.forall_mem_cons.2 ⟨subd8_7_50, List.forall_mem_cons.2 ⟨subd8_7_51, List.forall_mem_cons.2 ⟨subd8_7_52, List.forall_mem_cons.2 ⟨subd8_7_53, List.forall_mem_cons.2 ⟨subd8_7_54, List.forall_mem_cons.2 ⟨subd8_7_55, List.forall_mem_cons.2 ⟨subd8_7_56, List.forall_mem_cons.2 ⟨subd8_7_57, List.forall_mem_cons.2 ⟨subd8_7_58, List.forall_mem_cons.2 ⟨subd8_7_59, List.forall_mem_cons.2 ⟨subd8_7_60, List.forall_mem_cons.2 ⟨subd8_7_61, List.forall_mem_cons.2 ⟨subd8_7_62, List.forall_mem_cons.2 ⟨subd8_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_64 : subd8_7 [-1, -1, -2] = true := by decide +kernel
theorem subd8_7_65 : subd8_7 [-1, -1, -1] = true := by decide +kernel
theorem subd8_7_66 : subd8_7 [-1, -1, 0] = true := by decide +kernel
theorem subd8_7_67 : subd8_7 [-1, -1, 1] = true := by decide +kernel
theorem subd8_7_68 : subd8_7 [-1, -1, 2] = true := by decide +kernel
theorem subd8_7_69 : subd8_7 [-1, -1, 3] = true := by decide +kernel
theorem subd8_7_70 : subd8_7 [-1, -1, 4] = true := by decide +kernel
theorem subd8_7_71 : subd8_7 [-1, -1, 5] = true := by decide +kernel
theorem subd8_7_72 : subd8_7 [-1, -1, 6] = true := by decide +kernel
theorem subd8_7_73 : subd8_7 [-1, 0, -7] = true := by decide +kernel
theorem subd8_7_74 : subd8_7 [-1, 0, -6] = true := by decide +kernel
theorem subd8_7_75 : subd8_7 [-1, 0, -5] = true := by decide +kernel
theorem subd8_7_76 : subd8_7 [-1, 0, -4] = true := by decide +kernel
theorem subd8_7_77 : subd8_7 [-1, 0, -3] = true := by decide +kernel
theorem subd8_7_78 : subd8_7 [-1, 0, -2] = true := by decide +kernel
theorem subd8_7_79 : subd8_7 [-1, 0, -1] = true := by decide +kernel
theorem subd8_7_80 : subd8_7 [-1, 0, 0] = true := by decide +kernel
theorem subd8_7_81 : subd8_7 [-1, 0, 1] = true := by decide +kernel
theorem subd8_7_82 : subd8_7 [-1, 0, 2] = true := by decide +kernel
theorem subd8_7_83 : subd8_7 [-1, 0, 3] = true := by decide +kernel
theorem subd8_7_84 : subd8_7 [-1, 0, 4] = true := by decide +kernel
theorem subd8_7_85 : subd8_7 [-1, 0, 5] = true := by decide +kernel
theorem subd8_7_86 : subd8_7 [-1, 0, 6] = true := by decide +kernel
theorem subd8_7_87 : subd8_7 [-1, 0, 7] = true := by decide +kernel
theorem subd8_7_88 : subd8_7 [-1, 1, -6] = true := by decide +kernel
theorem subd8_7_89 : subd8_7 [-1, 1, -5] = true := by decide +kernel
theorem subd8_7_90 : subd8_7 [-1, 1, -4] = true := by decide +kernel
theorem subd8_7_91 : subd8_7 [-1, 1, -3] = true := by decide +kernel
theorem subd8_7_92 : subd8_7 [-1, 1, -2] = true := by decide +kernel
theorem subd8_7_93 : subd8_7 [-1, 1, -1] = true := by decide +kernel
theorem subd8_7_94 : subd8_7 [-1, 1, 0] = true := by decide +kernel
theorem subd8_7_95 : subd8_7 [-1, 1, 1] = true := by decide +kernel
theorem sbd8_7_2 : ∀ q ∈ blkd8_7_2, subd8_7 q = true := by
  unfold blkd8_7_2
  exact List.forall_mem_cons.2 ⟨subd8_7_64, List.forall_mem_cons.2 ⟨subd8_7_65, List.forall_mem_cons.2 ⟨subd8_7_66, List.forall_mem_cons.2 ⟨subd8_7_67, List.forall_mem_cons.2 ⟨subd8_7_68, List.forall_mem_cons.2 ⟨subd8_7_69, List.forall_mem_cons.2 ⟨subd8_7_70, List.forall_mem_cons.2 ⟨subd8_7_71, List.forall_mem_cons.2 ⟨subd8_7_72, List.forall_mem_cons.2 ⟨subd8_7_73, List.forall_mem_cons.2 ⟨subd8_7_74, List.forall_mem_cons.2 ⟨subd8_7_75, List.forall_mem_cons.2 ⟨subd8_7_76, List.forall_mem_cons.2 ⟨subd8_7_77, List.forall_mem_cons.2 ⟨subd8_7_78, List.forall_mem_cons.2 ⟨subd8_7_79, List.forall_mem_cons.2 ⟨subd8_7_80, List.forall_mem_cons.2 ⟨subd8_7_81, List.forall_mem_cons.2 ⟨subd8_7_82, List.forall_mem_cons.2 ⟨subd8_7_83, List.forall_mem_cons.2 ⟨subd8_7_84, List.forall_mem_cons.2 ⟨subd8_7_85, List.forall_mem_cons.2 ⟨subd8_7_86, List.forall_mem_cons.2 ⟨subd8_7_87, List.forall_mem_cons.2 ⟨subd8_7_88, List.forall_mem_cons.2 ⟨subd8_7_89, List.forall_mem_cons.2 ⟨subd8_7_90, List.forall_mem_cons.2 ⟨subd8_7_91, List.forall_mem_cons.2 ⟨subd8_7_92, List.forall_mem_cons.2 ⟨subd8_7_93, List.forall_mem_cons.2 ⟨subd8_7_94, List.forall_mem_cons.2 ⟨subd8_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_96 : subd8_7 [-1, 1, 2] = true := by decide +kernel
theorem subd8_7_97 : subd8_7 [-1, 1, 3] = true := by decide +kernel
theorem subd8_7_98 : subd8_7 [-1, 1, 4] = true := by decide +kernel
theorem subd8_7_99 : subd8_7 [-1, 1, 5] = true := by decide +kernel
theorem subd8_7_100 : subd8_7 [-1, 1, 6] = true := by decide +kernel
theorem subd8_7_101 : subd8_7 [-1, 1, 7] = true := by decide +kernel
theorem subd8_7_102 : subd8_7 [-1, 2] = true := by decide +kernel
theorem subd8_7_103 : subd8_7 [-1, 3] = true := by decide +kernel
theorem subd8_7_104 : subd8_7 [-1, 4] = true := by decide +kernel
theorem subd8_7_105 : subd8_7 [0, -6] = true := by decide +kernel
theorem subd8_7_106 : subd8_7 [0, -5] = true := by decide +kernel
theorem subd8_7_107 : subd8_7 [0, -4] = true := by decide +kernel
theorem subd8_7_108 : subd8_7 [0, -3] = true := by decide +kernel
theorem subd8_7_109 : subd8_7 [0, -2, -8] = true := by decide +kernel
theorem subd8_7_110 : subd8_7 [0, -2, -7] = true := by decide +kernel
theorem subd8_7_111 : subd8_7 [0, -2, -6] = true := by decide +kernel
theorem subd8_7_112 : subd8_7 [0, -2, -5] = true := by decide +kernel
theorem subd8_7_113 : subd8_7 [0, -2, -4] = true := by decide +kernel
theorem subd8_7_114 : subd8_7 [0, -2, -3] = true := by decide +kernel
theorem subd8_7_115 : subd8_7 [0, -2, -2] = true := by decide +kernel
theorem subd8_7_116 : subd8_7 [0, -2, -1] = true := by decide +kernel
theorem subd8_7_117 : subd8_7 [0, -2, 0] = true := by decide +kernel
theorem subd8_7_118 : subd8_7 [0, -2, 1] = true := by decide +kernel
theorem subd8_7_119 : subd8_7 [0, -2, 2] = true := by decide +kernel
theorem subd8_7_120 : subd8_7 [0, -2, 3] = true := by decide +kernel
theorem subd8_7_121 : subd8_7 [0, -2, 4] = true := by decide +kernel
theorem subd8_7_122 : subd8_7 [0, -2, 5] = true := by decide +kernel
theorem subd8_7_123 : subd8_7 [0, -1, -8] = true := by decide +kernel
theorem subd8_7_124 : subd8_7 [0, -1, -7] = true := by decide +kernel
theorem subd8_7_125 : subd8_7 [0, -1, -6] = true := by decide +kernel
theorem subd8_7_126 : subd8_7 [0, -1, -5] = true := by decide +kernel
theorem subd8_7_127 : subd8_7 [0, -1, -4] = true := by decide +kernel
theorem sbd8_7_3 : ∀ q ∈ blkd8_7_3, subd8_7 q = true := by
  unfold blkd8_7_3
  exact List.forall_mem_cons.2 ⟨subd8_7_96, List.forall_mem_cons.2 ⟨subd8_7_97, List.forall_mem_cons.2 ⟨subd8_7_98, List.forall_mem_cons.2 ⟨subd8_7_99, List.forall_mem_cons.2 ⟨subd8_7_100, List.forall_mem_cons.2 ⟨subd8_7_101, List.forall_mem_cons.2 ⟨subd8_7_102, List.forall_mem_cons.2 ⟨subd8_7_103, List.forall_mem_cons.2 ⟨subd8_7_104, List.forall_mem_cons.2 ⟨subd8_7_105, List.forall_mem_cons.2 ⟨subd8_7_106, List.forall_mem_cons.2 ⟨subd8_7_107, List.forall_mem_cons.2 ⟨subd8_7_108, List.forall_mem_cons.2 ⟨subd8_7_109, List.forall_mem_cons.2 ⟨subd8_7_110, List.forall_mem_cons.2 ⟨subd8_7_111, List.forall_mem_cons.2 ⟨subd8_7_112, List.forall_mem_cons.2 ⟨subd8_7_113, List.forall_mem_cons.2 ⟨subd8_7_114, List.forall_mem_cons.2 ⟨subd8_7_115, List.forall_mem_cons.2 ⟨subd8_7_116, List.forall_mem_cons.2 ⟨subd8_7_117, List.forall_mem_cons.2 ⟨subd8_7_118, List.forall_mem_cons.2 ⟨subd8_7_119, List.forall_mem_cons.2 ⟨subd8_7_120, List.forall_mem_cons.2 ⟨subd8_7_121, List.forall_mem_cons.2 ⟨subd8_7_122, List.forall_mem_cons.2 ⟨subd8_7_123, List.forall_mem_cons.2 ⟨subd8_7_124, List.forall_mem_cons.2 ⟨subd8_7_125, List.forall_mem_cons.2 ⟨subd8_7_126, List.forall_mem_cons.2 ⟨subd8_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_128 : subd8_7 [0, -1, -3] = true := by decide +kernel
theorem subd8_7_129 : subd8_7 [0, -1, -2] = true := by decide +kernel
theorem subd8_7_130 : subd8_7 [0, -1, -1] = true := by decide +kernel
theorem subd8_7_131 : subd8_7 [0, -1, 0] = true := by decide +kernel
theorem subd8_7_132 : subd8_7 [0, -1, 1] = true := by decide +kernel
theorem subd8_7_133 : subd8_7 [0, -1, 2] = true := by decide +kernel
theorem subd8_7_134 : subd8_7 [0, -1, 3] = true := by decide +kernel
theorem subd8_7_135 : subd8_7 [0, -1, 4] = true := by decide +kernel
theorem subd8_7_136 : subd8_7 [0, -1, 5] = true := by decide +kernel
theorem subd8_7_137 : subd8_7 [0, -1, 6] = true := by decide +kernel
theorem subd8_7_138 : subd8_7 [0, 0, -7] = true := by decide +kernel
theorem subd8_7_139 : subd8_7 [0, 0, -6] = true := by decide +kernel
theorem subd8_7_140 : subd8_7 [0, 0, -5] = true := by decide +kernel
theorem subd8_7_141 : subd8_7 [0, 0, -4] = true := by decide +kernel
theorem subd8_7_142 : subd8_7 [0, 0, -3] = true := by decide +kernel
theorem subd8_7_143 : subd8_7 [0, 0, -2] = true := by decide +kernel
theorem subd8_7_144 : subd8_7 [0, 0, -1] = true := by decide +kernel
theorem subd8_7_145 : subd8_7 [0, 0, 0] = true := by decide +kernel
theorem subd8_7_146 : subd8_7 [0, 0, 1] = true := by decide +kernel
theorem subd8_7_147 : subd8_7 [0, 0, 2] = true := by decide +kernel
theorem subd8_7_148 : subd8_7 [0, 0, 3] = true := by decide +kernel
theorem subd8_7_149 : subd8_7 [0, 0, 4] = true := by decide +kernel
theorem subd8_7_150 : subd8_7 [0, 0, 5] = true := by decide +kernel
theorem subd8_7_151 : subd8_7 [0, 0, 6] = true := by decide +kernel
theorem subd8_7_152 : subd8_7 [0, 1, -7] = true := by decide +kernel
theorem subd8_7_153 : subd8_7 [0, 1, -6] = true := by decide +kernel
theorem subd8_7_154 : subd8_7 [0, 1, -5] = true := by decide +kernel
theorem subd8_7_155 : subd8_7 [0, 1, -4] = true := by decide +kernel
theorem subd8_7_156 : subd8_7 [0, 1, -3] = true := by decide +kernel
theorem subd8_7_157 : subd8_7 [0, 1, -2] = true := by decide +kernel
theorem subd8_7_158 : subd8_7 [0, 1, -1] = true := by decide +kernel
theorem subd8_7_159 : subd8_7 [0, 1, 0] = true := by decide +kernel
theorem sbd8_7_4 : ∀ q ∈ blkd8_7_4, subd8_7 q = true := by
  unfold blkd8_7_4
  exact List.forall_mem_cons.2 ⟨subd8_7_128, List.forall_mem_cons.2 ⟨subd8_7_129, List.forall_mem_cons.2 ⟨subd8_7_130, List.forall_mem_cons.2 ⟨subd8_7_131, List.forall_mem_cons.2 ⟨subd8_7_132, List.forall_mem_cons.2 ⟨subd8_7_133, List.forall_mem_cons.2 ⟨subd8_7_134, List.forall_mem_cons.2 ⟨subd8_7_135, List.forall_mem_cons.2 ⟨subd8_7_136, List.forall_mem_cons.2 ⟨subd8_7_137, List.forall_mem_cons.2 ⟨subd8_7_138, List.forall_mem_cons.2 ⟨subd8_7_139, List.forall_mem_cons.2 ⟨subd8_7_140, List.forall_mem_cons.2 ⟨subd8_7_141, List.forall_mem_cons.2 ⟨subd8_7_142, List.forall_mem_cons.2 ⟨subd8_7_143, List.forall_mem_cons.2 ⟨subd8_7_144, List.forall_mem_cons.2 ⟨subd8_7_145, List.forall_mem_cons.2 ⟨subd8_7_146, List.forall_mem_cons.2 ⟨subd8_7_147, List.forall_mem_cons.2 ⟨subd8_7_148, List.forall_mem_cons.2 ⟨subd8_7_149, List.forall_mem_cons.2 ⟨subd8_7_150, List.forall_mem_cons.2 ⟨subd8_7_151, List.forall_mem_cons.2 ⟨subd8_7_152, List.forall_mem_cons.2 ⟨subd8_7_153, List.forall_mem_cons.2 ⟨subd8_7_154, List.forall_mem_cons.2 ⟨subd8_7_155, List.forall_mem_cons.2 ⟨subd8_7_156, List.forall_mem_cons.2 ⟨subd8_7_157, List.forall_mem_cons.2 ⟨subd8_7_158, List.forall_mem_cons.2 ⟨subd8_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_160 : subd8_7 [0, 1, 1] = true := by decide +kernel
theorem subd8_7_161 : subd8_7 [0, 1, 2] = true := by decide +kernel
theorem subd8_7_162 : subd8_7 [0, 1, 3] = true := by decide +kernel
theorem subd8_7_163 : subd8_7 [0, 1, 4] = true := by decide +kernel
theorem subd8_7_164 : subd8_7 [0, 1, 5] = true := by decide +kernel
theorem subd8_7_165 : subd8_7 [0, 1, 6] = true := by decide +kernel
theorem subd8_7_166 : subd8_7 [0, 1, 7] = true := by decide +kernel
theorem subd8_7_167 : subd8_7 [0, 2, -6] = true := by decide +kernel
theorem subd8_7_168 : subd8_7 [0, 2, -5] = true := by decide +kernel
theorem subd8_7_169 : subd8_7 [0, 2, -4] = true := by decide +kernel
theorem subd8_7_170 : subd8_7 [0, 2, -3] = true := by decide +kernel
theorem subd8_7_171 : subd8_7 [0, 2, -2] = true := by decide +kernel
theorem subd8_7_172 : subd8_7 [0, 2, -1] = true := by decide +kernel
theorem subd8_7_173 : subd8_7 [0, 2, 0] = true := by decide +kernel
theorem subd8_7_174 : subd8_7 [0, 2, 1] = true := by decide +kernel
theorem subd8_7_175 : subd8_7 [0, 2, 2] = true := by decide +kernel
theorem subd8_7_176 : subd8_7 [0, 2, 3] = true := by decide +kernel
theorem subd8_7_177 : subd8_7 [0, 2, 4] = true := by decide +kernel
theorem subd8_7_178 : subd8_7 [0, 2, 5] = true := by decide +kernel
theorem subd8_7_179 : subd8_7 [0, 2, 6] = true := by decide +kernel
theorem subd8_7_180 : subd8_7 [0, 2, 7] = true := by decide +kernel
theorem subd8_7_181 : subd8_7 [0, 3] = true := by decide +kernel
theorem subd8_7_182 : subd8_7 [0, 4] = true := by decide +kernel
theorem subd8_7_183 : subd8_7 [0, 5] = true := by decide +kernel
theorem subd8_7_184 : subd8_7 [1, -5] = true := by decide +kernel
theorem subd8_7_185 : subd8_7 [1, -4] = true := by decide +kernel
theorem subd8_7_186 : subd8_7 [1, -3] = true := by decide +kernel
theorem subd8_7_187 : subd8_7 [1, -2] = true := by decide +kernel
theorem subd8_7_188 : subd8_7 [1, -1, -8] = true := by decide +kernel
theorem subd8_7_189 : subd8_7 [1, -1, -7] = true := by decide +kernel
theorem subd8_7_190 : subd8_7 [1, -1, -6] = true := by decide +kernel
theorem subd8_7_191 : subd8_7 [1, -1, -5] = true := by decide +kernel
theorem sbd8_7_5 : ∀ q ∈ blkd8_7_5, subd8_7 q = true := by
  unfold blkd8_7_5
  exact List.forall_mem_cons.2 ⟨subd8_7_160, List.forall_mem_cons.2 ⟨subd8_7_161, List.forall_mem_cons.2 ⟨subd8_7_162, List.forall_mem_cons.2 ⟨subd8_7_163, List.forall_mem_cons.2 ⟨subd8_7_164, List.forall_mem_cons.2 ⟨subd8_7_165, List.forall_mem_cons.2 ⟨subd8_7_166, List.forall_mem_cons.2 ⟨subd8_7_167, List.forall_mem_cons.2 ⟨subd8_7_168, List.forall_mem_cons.2 ⟨subd8_7_169, List.forall_mem_cons.2 ⟨subd8_7_170, List.forall_mem_cons.2 ⟨subd8_7_171, List.forall_mem_cons.2 ⟨subd8_7_172, List.forall_mem_cons.2 ⟨subd8_7_173, List.forall_mem_cons.2 ⟨subd8_7_174, List.forall_mem_cons.2 ⟨subd8_7_175, List.forall_mem_cons.2 ⟨subd8_7_176, List.forall_mem_cons.2 ⟨subd8_7_177, List.forall_mem_cons.2 ⟨subd8_7_178, List.forall_mem_cons.2 ⟨subd8_7_179, List.forall_mem_cons.2 ⟨subd8_7_180, List.forall_mem_cons.2 ⟨subd8_7_181, List.forall_mem_cons.2 ⟨subd8_7_182, List.forall_mem_cons.2 ⟨subd8_7_183, List.forall_mem_cons.2 ⟨subd8_7_184, List.forall_mem_cons.2 ⟨subd8_7_185, List.forall_mem_cons.2 ⟨subd8_7_186, List.forall_mem_cons.2 ⟨subd8_7_187, List.forall_mem_cons.2 ⟨subd8_7_188, List.forall_mem_cons.2 ⟨subd8_7_189, List.forall_mem_cons.2 ⟨subd8_7_190, List.forall_mem_cons.2 ⟨subd8_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_192 : subd8_7 [1, -1, -4] = true := by decide +kernel
theorem subd8_7_193 : subd8_7 [1, -1, -3] = true := by decide +kernel
theorem subd8_7_194 : subd8_7 [1, -1, -2] = true := by decide +kernel
theorem subd8_7_195 : subd8_7 [1, -1, -1] = true := by decide +kernel
theorem subd8_7_196 : subd8_7 [1, -1, 0] = true := by decide +kernel
theorem subd8_7_197 : subd8_7 [1, -1, 1] = true := by decide +kernel
theorem subd8_7_198 : subd8_7 [1, -1, 2] = true := by decide +kernel
theorem subd8_7_199 : subd8_7 [1, -1, 3] = true := by decide +kernel
theorem subd8_7_200 : subd8_7 [1, -1, 4] = true := by decide +kernel
theorem subd8_7_201 : subd8_7 [1, -1, 5] = true := by decide +kernel
theorem subd8_7_202 : subd8_7 [1, 0, -8] = true := by decide +kernel
theorem subd8_7_203 : subd8_7 [1, 0, -7] = true := by decide +kernel
theorem subd8_7_204 : subd8_7 [1, 0, -6] = true := by decide +kernel
theorem subd8_7_205 : subd8_7 [1, 0, -5] = true := by decide +kernel
theorem subd8_7_206 : subd8_7 [1, 0, -4] = true := by decide +kernel
theorem subd8_7_207 : subd8_7 [1, 0, -3] = true := by decide +kernel
theorem subd8_7_208 : subd8_7 [1, 0, -2] = true := by decide +kernel
theorem subd8_7_209 : subd8_7 [1, 0, -1] = true := by decide +kernel
theorem subd8_7_210 : subd8_7 [1, 0, 0] = true := by decide +kernel
theorem subd8_7_211 : subd8_7 [1, 0, 1] = true := by decide +kernel
theorem subd8_7_212 : subd8_7 [1, 0, 2] = true := by decide +kernel
theorem subd8_7_213 : subd8_7 [1, 0, 3] = true := by decide +kernel
theorem subd8_7_214 : subd8_7 [1, 0, 4] = true := by decide +kernel
theorem subd8_7_215 : subd8_7 [1, 0, 5] = true := by decide +kernel
theorem subd8_7_216 : subd8_7 [1, 0, 6] = true := by decide +kernel
theorem subd8_7_217 : subd8_7 [1, 1, -7] = true := by decide +kernel
theorem subd8_7_218 : subd8_7 [1, 1, -6] = true := by decide +kernel
theorem subd8_7_219 : subd8_7 [1, 1, -5] = true := by decide +kernel
theorem subd8_7_220 : subd8_7 [1, 1, -4] = true := by decide +kernel
theorem subd8_7_221 : subd8_7 [1, 1, -3] = true := by decide +kernel
theorem subd8_7_222 : subd8_7 [1, 1, -2] = true := by decide +kernel
theorem subd8_7_223 : subd8_7 [1, 1, -1] = true := by decide +kernel
theorem sbd8_7_6 : ∀ q ∈ blkd8_7_6, subd8_7 q = true := by
  unfold blkd8_7_6
  exact List.forall_mem_cons.2 ⟨subd8_7_192, List.forall_mem_cons.2 ⟨subd8_7_193, List.forall_mem_cons.2 ⟨subd8_7_194, List.forall_mem_cons.2 ⟨subd8_7_195, List.forall_mem_cons.2 ⟨subd8_7_196, List.forall_mem_cons.2 ⟨subd8_7_197, List.forall_mem_cons.2 ⟨subd8_7_198, List.forall_mem_cons.2 ⟨subd8_7_199, List.forall_mem_cons.2 ⟨subd8_7_200, List.forall_mem_cons.2 ⟨subd8_7_201, List.forall_mem_cons.2 ⟨subd8_7_202, List.forall_mem_cons.2 ⟨subd8_7_203, List.forall_mem_cons.2 ⟨subd8_7_204, List.forall_mem_cons.2 ⟨subd8_7_205, List.forall_mem_cons.2 ⟨subd8_7_206, List.forall_mem_cons.2 ⟨subd8_7_207, List.forall_mem_cons.2 ⟨subd8_7_208, List.forall_mem_cons.2 ⟨subd8_7_209, List.forall_mem_cons.2 ⟨subd8_7_210, List.forall_mem_cons.2 ⟨subd8_7_211, List.forall_mem_cons.2 ⟨subd8_7_212, List.forall_mem_cons.2 ⟨subd8_7_213, List.forall_mem_cons.2 ⟨subd8_7_214, List.forall_mem_cons.2 ⟨subd8_7_215, List.forall_mem_cons.2 ⟨subd8_7_216, List.forall_mem_cons.2 ⟨subd8_7_217, List.forall_mem_cons.2 ⟨subd8_7_218, List.forall_mem_cons.2 ⟨subd8_7_219, List.forall_mem_cons.2 ⟨subd8_7_220, List.forall_mem_cons.2 ⟨subd8_7_221, List.forall_mem_cons.2 ⟨subd8_7_222, List.forall_mem_cons.2 ⟨subd8_7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_224 : subd8_7 [1, 1, 0] = true := by decide +kernel
theorem subd8_7_225 : subd8_7 [1, 1, 1] = true := by decide +kernel
theorem subd8_7_226 : subd8_7 [1, 1, 2] = true := by decide +kernel
theorem subd8_7_227 : subd8_7 [1, 1, 3] = true := by decide +kernel
theorem subd8_7_228 : subd8_7 [1, 1, 4] = true := by decide +kernel
theorem subd8_7_229 : subd8_7 [1, 1, 5] = true := by decide +kernel
theorem subd8_7_230 : subd8_7 [1, 1, 6] = true := by decide +kernel
theorem subd8_7_231 : subd8_7 [1, 2, -6] = true := by decide +kernel
theorem subd8_7_232 : subd8_7 [1, 2, -5] = true := by decide +kernel
theorem subd8_7_233 : subd8_7 [1, 2, -4] = true := by decide +kernel
theorem subd8_7_234 : subd8_7 [1, 2, -3] = true := by decide +kernel
theorem subd8_7_235 : subd8_7 [1, 2, -2] = true := by decide +kernel
theorem subd8_7_236 : subd8_7 [1, 2, -1] = true := by decide +kernel
theorem subd8_7_237 : subd8_7 [1, 2, 0] = true := by decide +kernel
theorem subd8_7_238 : subd8_7 [1, 2, 1] = true := by decide +kernel
theorem subd8_7_239 : subd8_7 [1, 2, 2] = true := by decide +kernel
theorem subd8_7_240 : subd8_7 [1, 2, 3] = true := by decide +kernel
theorem subd8_7_241 : subd8_7 [1, 2, 4] = true := by decide +kernel
theorem subd8_7_242 : subd8_7 [1, 2, 5] = true := by decide +kernel
theorem subd8_7_243 : subd8_7 [1, 2, 6] = true := by decide +kernel
theorem subd8_7_244 : subd8_7 [1, 2, 7] = true := by decide +kernel
theorem subd8_7_245 : subd8_7 [1, 3] = true := by decide +kernel
theorem subd8_7_246 : subd8_7 [1, 4] = true := by decide +kernel
theorem subd8_7_247 : subd8_7 [1, 5] = true := by decide +kernel
theorem subd8_7_248 : subd8_7 [2, -5] = true := by decide +kernel
theorem subd8_7_249 : subd8_7 [2, -4] = true := by decide +kernel
theorem subd8_7_250 : subd8_7 [2, -3] = true := by decide +kernel
theorem subd8_7_251 : subd8_7 [2, -2] = true := by decide +kernel
theorem subd8_7_252 : subd8_7 [2, -1] = true := by decide +kernel
theorem subd8_7_253 : subd8_7 [2, 0] = true := by decide +kernel
theorem subd8_7_254 : subd8_7 [2, 1, -7] = true := by decide +kernel
theorem subd8_7_255 : subd8_7 [2, 1, -6] = true := by decide +kernel
theorem sbd8_7_7 : ∀ q ∈ blkd8_7_7, subd8_7 q = true := by
  unfold blkd8_7_7
  exact List.forall_mem_cons.2 ⟨subd8_7_224, List.forall_mem_cons.2 ⟨subd8_7_225, List.forall_mem_cons.2 ⟨subd8_7_226, List.forall_mem_cons.2 ⟨subd8_7_227, List.forall_mem_cons.2 ⟨subd8_7_228, List.forall_mem_cons.2 ⟨subd8_7_229, List.forall_mem_cons.2 ⟨subd8_7_230, List.forall_mem_cons.2 ⟨subd8_7_231, List.forall_mem_cons.2 ⟨subd8_7_232, List.forall_mem_cons.2 ⟨subd8_7_233, List.forall_mem_cons.2 ⟨subd8_7_234, List.forall_mem_cons.2 ⟨subd8_7_235, List.forall_mem_cons.2 ⟨subd8_7_236, List.forall_mem_cons.2 ⟨subd8_7_237, List.forall_mem_cons.2 ⟨subd8_7_238, List.forall_mem_cons.2 ⟨subd8_7_239, List.forall_mem_cons.2 ⟨subd8_7_240, List.forall_mem_cons.2 ⟨subd8_7_241, List.forall_mem_cons.2 ⟨subd8_7_242, List.forall_mem_cons.2 ⟨subd8_7_243, List.forall_mem_cons.2 ⟨subd8_7_244, List.forall_mem_cons.2 ⟨subd8_7_245, List.forall_mem_cons.2 ⟨subd8_7_246, List.forall_mem_cons.2 ⟨subd8_7_247, List.forall_mem_cons.2 ⟨subd8_7_248, List.forall_mem_cons.2 ⟨subd8_7_249, List.forall_mem_cons.2 ⟨subd8_7_250, List.forall_mem_cons.2 ⟨subd8_7_251, List.forall_mem_cons.2 ⟨subd8_7_252, List.forall_mem_cons.2 ⟨subd8_7_253, List.forall_mem_cons.2 ⟨subd8_7_254, List.forall_mem_cons.2 ⟨subd8_7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
