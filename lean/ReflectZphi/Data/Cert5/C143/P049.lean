import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_2_0 : subd17_2 [-5, -5] = true := by decide +kernel
theorem subd17_2_1 : subd17_2 [-5, -4] = true := by decide +kernel
theorem subd17_2_2 : subd17_2 [-5, -3] = true := by decide +kernel
theorem subd17_2_3 : subd17_2 [-5, -2] = true := by decide +kernel
theorem subd17_2_4 : subd17_2 [-5, -1] = true := by decide +kernel
theorem subd17_2_5 : subd17_2 [-5, 0] = true := by decide +kernel
theorem subd17_2_6 : subd17_2 [-4, -6] = true := by decide +kernel
theorem subd17_2_7 : subd17_2 [-4, -5] = true := by decide +kernel
theorem subd17_2_8 : subd17_2 [-4, -4] = true := by decide +kernel
theorem subd17_2_9 : subd17_2 [-4, -3] = true := by decide +kernel
theorem subd17_2_10 : subd17_2 [-4, -2] = true := by decide +kernel
theorem subd17_2_11 : subd17_2 [-4, -1] = true := by decide +kernel
theorem subd17_2_12 : subd17_2 [-4, 0] = true := by decide +kernel
theorem subd17_2_13 : subd17_2 [-4, 1] = true := by decide +kernel
theorem subd17_2_14 : subd17_2 [-4, 2] = true := by decide +kernel
theorem subd17_2_15 : subd17_2 [-3, -7] = true := by decide +kernel
theorem subd17_2_16 : subd17_2 [-3, -6] = true := by decide +kernel
theorem subd17_2_17 : subd17_2 [-3, -5] = true := by decide +kernel
theorem subd17_2_18 : subd17_2 [-3, -4] = true := by decide +kernel
theorem subd17_2_19 : subd17_2 [-3, -3, -9] = true := by decide +kernel
theorem subd17_2_20 : subd17_2 [-3, -3, -8] = true := by decide +kernel
theorem subd17_2_21 : subd17_2 [-3, -3, -7] = true := by decide +kernel
theorem subd17_2_22 : subd17_2 [-3, -3, -6] = true := by decide +kernel
theorem subd17_2_23 : subd17_2 [-3, -3, -5] = true := by decide +kernel
theorem subd17_2_24 : subd17_2 [-3, -3, -4] = true := by decide +kernel
theorem subd17_2_25 : subd17_2 [-3, -3, -3] = true := by decide +kernel
theorem subd17_2_26 : subd17_2 [-3, -3, -2] = true := by decide +kernel
theorem subd17_2_27 : subd17_2 [-3, -3, -1] = true := by decide +kernel
theorem subd17_2_28 : subd17_2 [-3, -3, 0] = true := by decide +kernel
theorem subd17_2_29 : subd17_2 [-3, -3, 1] = true := by decide +kernel
theorem subd17_2_30 : subd17_2 [-3, -3, 2] = true := by decide +kernel
theorem subd17_2_31 : subd17_2 [-3, -3, 3] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_cons.2 ⟨subd17_2_1, List.forall_mem_cons.2 ⟨subd17_2_2, List.forall_mem_cons.2 ⟨subd17_2_3, List.forall_mem_cons.2 ⟨subd17_2_4, List.forall_mem_cons.2 ⟨subd17_2_5, List.forall_mem_cons.2 ⟨subd17_2_6, List.forall_mem_cons.2 ⟨subd17_2_7, List.forall_mem_cons.2 ⟨subd17_2_8, List.forall_mem_cons.2 ⟨subd17_2_9, List.forall_mem_cons.2 ⟨subd17_2_10, List.forall_mem_cons.2 ⟨subd17_2_11, List.forall_mem_cons.2 ⟨subd17_2_12, List.forall_mem_cons.2 ⟨subd17_2_13, List.forall_mem_cons.2 ⟨subd17_2_14, List.forall_mem_cons.2 ⟨subd17_2_15, List.forall_mem_cons.2 ⟨subd17_2_16, List.forall_mem_cons.2 ⟨subd17_2_17, List.forall_mem_cons.2 ⟨subd17_2_18, List.forall_mem_cons.2 ⟨subd17_2_19, List.forall_mem_cons.2 ⟨subd17_2_20, List.forall_mem_cons.2 ⟨subd17_2_21, List.forall_mem_cons.2 ⟨subd17_2_22, List.forall_mem_cons.2 ⟨subd17_2_23, List.forall_mem_cons.2 ⟨subd17_2_24, List.forall_mem_cons.2 ⟨subd17_2_25, List.forall_mem_cons.2 ⟨subd17_2_26, List.forall_mem_cons.2 ⟨subd17_2_27, List.forall_mem_cons.2 ⟨subd17_2_28, List.forall_mem_cons.2 ⟨subd17_2_29, List.forall_mem_cons.2 ⟨subd17_2_30, List.forall_mem_cons.2 ⟨subd17_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_32 : subd17_2 [-3, -3, 4] = true := by decide +kernel
theorem subd17_2_33 : subd17_2 [-3, -3, 5] = true := by decide +kernel
theorem subd17_2_34 : subd17_2 [-3, -2, -9] = true := by decide +kernel
theorem subd17_2_35 : subd17_2 [-3, -2, -8] = true := by decide +kernel
theorem subd17_2_36 : subd17_2 [-3, -2, -7] = true := by decide +kernel
theorem subd17_2_37 : subd17_2 [-3, -2, -6] = true := by decide +kernel
theorem subd17_2_38 : subd17_2 [-3, -2, -5] = true := by decide +kernel
theorem subd17_2_39 : subd17_2 [-3, -2, -4] = true := by decide +kernel
theorem subd17_2_40 : subd17_2 [-3, -2, -3] = true := by decide +kernel
theorem subd17_2_41 : subd17_2 [-3, -2, -2] = true := by decide +kernel
theorem subd17_2_42 : subd17_2 [-3, -2, -1] = true := by decide +kernel
theorem subd17_2_43 : subd17_2 [-3, -2, 0] = true := by decide +kernel
theorem subd17_2_44 : subd17_2 [-3, -2, 1] = true := by decide +kernel
theorem subd17_2_45 : subd17_2 [-3, -2, 2] = true := by decide +kernel
theorem subd17_2_46 : subd17_2 [-3, -2, 3] = true := by decide +kernel
theorem subd17_2_47 : subd17_2 [-3, -2, 4] = true := by decide +kernel
theorem subd17_2_48 : subd17_2 [-3, -2, 5] = true := by decide +kernel
theorem subd17_2_49 : subd17_2 [-3, -1, -8] = true := by decide +kernel
theorem subd17_2_50 : subd17_2 [-3, -1, -7] = true := by decide +kernel
theorem subd17_2_51 : subd17_2 [-3, -1, -6] = true := by decide +kernel
theorem subd17_2_52 : subd17_2 [-3, -1, -5] = true := by decide +kernel
theorem subd17_2_53 : subd17_2 [-3, -1, -4] = true := by decide +kernel
theorem subd17_2_54 : subd17_2 [-3, -1, -3] = true := by decide +kernel
theorem subd17_2_55 : subd17_2 [-3, -1, -2] = true := by decide +kernel
theorem subd17_2_56 : subd17_2 [-3, -1, -1] = true := by decide +kernel
theorem subd17_2_57 : subd17_2 [-3, -1, 0] = true := by decide +kernel
theorem subd17_2_58 : subd17_2 [-3, -1, 1] = true := by decide +kernel
theorem subd17_2_59 : subd17_2 [-3, -1, 2] = true := by decide +kernel
theorem subd17_2_60 : subd17_2 [-3, -1, 3] = true := by decide +kernel
theorem subd17_2_61 : subd17_2 [-3, -1, 4] = true := by decide +kernel
theorem subd17_2_62 : subd17_2 [-3, -1, 5] = true := by decide +kernel
theorem subd17_2_63 : subd17_2 [-3, -1, 6] = true := by decide +kernel
theorem sbd17_2_1 : ∀ q ∈ blkd17_2_1, subd17_2 q = true := by
  unfold blkd17_2_1
  exact List.forall_mem_cons.2 ⟨subd17_2_32, List.forall_mem_cons.2 ⟨subd17_2_33, List.forall_mem_cons.2 ⟨subd17_2_34, List.forall_mem_cons.2 ⟨subd17_2_35, List.forall_mem_cons.2 ⟨subd17_2_36, List.forall_mem_cons.2 ⟨subd17_2_37, List.forall_mem_cons.2 ⟨subd17_2_38, List.forall_mem_cons.2 ⟨subd17_2_39, List.forall_mem_cons.2 ⟨subd17_2_40, List.forall_mem_cons.2 ⟨subd17_2_41, List.forall_mem_cons.2 ⟨subd17_2_42, List.forall_mem_cons.2 ⟨subd17_2_43, List.forall_mem_cons.2 ⟨subd17_2_44, List.forall_mem_cons.2 ⟨subd17_2_45, List.forall_mem_cons.2 ⟨subd17_2_46, List.forall_mem_cons.2 ⟨subd17_2_47, List.forall_mem_cons.2 ⟨subd17_2_48, List.forall_mem_cons.2 ⟨subd17_2_49, List.forall_mem_cons.2 ⟨subd17_2_50, List.forall_mem_cons.2 ⟨subd17_2_51, List.forall_mem_cons.2 ⟨subd17_2_52, List.forall_mem_cons.2 ⟨subd17_2_53, List.forall_mem_cons.2 ⟨subd17_2_54, List.forall_mem_cons.2 ⟨subd17_2_55, List.forall_mem_cons.2 ⟨subd17_2_56, List.forall_mem_cons.2 ⟨subd17_2_57, List.forall_mem_cons.2 ⟨subd17_2_58, List.forall_mem_cons.2 ⟨subd17_2_59, List.forall_mem_cons.2 ⟨subd17_2_60, List.forall_mem_cons.2 ⟨subd17_2_61, List.forall_mem_cons.2 ⟨subd17_2_62, List.forall_mem_cons.2 ⟨subd17_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_64 : subd17_2 [-3, 0, -8] = true := by decide +kernel
theorem subd17_2_65 : subd17_2 [-3, 0, -7] = true := by decide +kernel
theorem subd17_2_66 : subd17_2 [-3, 0, -6] = true := by decide +kernel
theorem subd17_2_67 : subd17_2 [-3, 0, -5] = true := by decide +kernel
theorem subd17_2_68 : subd17_2 [-3, 0, -4] = true := by decide +kernel
theorem subd17_2_69 : subd17_2 [-3, 0, -3] = true := by decide +kernel
theorem subd17_2_70 : subd17_2 [-3, 0, -2] = true := by decide +kernel
theorem subd17_2_71 : subd17_2 [-3, 0, -1] = true := by decide +kernel
theorem subd17_2_72 : subd17_2 [-3, 0, 0] = true := by decide +kernel
theorem subd17_2_73 : subd17_2 [-3, 0, 1] = true := by decide +kernel
theorem subd17_2_74 : subd17_2 [-3, 0, 2] = true := by decide +kernel
theorem subd17_2_75 : subd17_2 [-3, 0, 3] = true := by decide +kernel
theorem subd17_2_76 : subd17_2 [-3, 0, 4] = true := by decide +kernel
theorem subd17_2_77 : subd17_2 [-3, 0, 5] = true := by decide +kernel
theorem subd17_2_78 : subd17_2 [-3, 0, 6] = true := by decide +kernel
theorem subd17_2_79 : subd17_2 [-3, 1, -7] = true := by decide +kernel
theorem subd17_2_80 : subd17_2 [-3, 1, -6] = true := by decide +kernel
theorem subd17_2_81 : subd17_2 [-3, 1, -5] = true := by decide +kernel
theorem subd17_2_82 : subd17_2 [-3, 1, -4] = true := by decide +kernel
theorem subd17_2_83 : subd17_2 [-3, 1, -3] = true := by decide +kernel
theorem subd17_2_84 : subd17_2 [-3, 1, -2] = true := by decide +kernel
theorem subd17_2_85 : subd17_2 [-3, 1, -1] = true := by decide +kernel
theorem subd17_2_86 : subd17_2 [-3, 1, 0] = true := by decide +kernel
theorem subd17_2_87 : subd17_2 [-3, 1, 1] = true := by decide +kernel
theorem subd17_2_88 : subd17_2 [-3, 1, 2] = true := by decide +kernel
theorem subd17_2_89 : subd17_2 [-3, 1, 3] = true := by decide +kernel
theorem subd17_2_90 : subd17_2 [-3, 1, 4] = true := by decide +kernel
theorem subd17_2_91 : subd17_2 [-3, 1, 5] = true := by decide +kernel
theorem subd17_2_92 : subd17_2 [-3, 1, 6] = true := by decide +kernel
theorem subd17_2_93 : subd17_2 [-3, 2] = true := by decide +kernel
theorem subd17_2_94 : subd17_2 [-3, 3] = true := by decide +kernel
theorem subd17_2_95 : subd17_2 [-2, -7] = true := by decide +kernel
theorem sbd17_2_2 : ∀ q ∈ blkd17_2_2, subd17_2 q = true := by
  unfold blkd17_2_2
  exact List.forall_mem_cons.2 ⟨subd17_2_64, List.forall_mem_cons.2 ⟨subd17_2_65, List.forall_mem_cons.2 ⟨subd17_2_66, List.forall_mem_cons.2 ⟨subd17_2_67, List.forall_mem_cons.2 ⟨subd17_2_68, List.forall_mem_cons.2 ⟨subd17_2_69, List.forall_mem_cons.2 ⟨subd17_2_70, List.forall_mem_cons.2 ⟨subd17_2_71, List.forall_mem_cons.2 ⟨subd17_2_72, List.forall_mem_cons.2 ⟨subd17_2_73, List.forall_mem_cons.2 ⟨subd17_2_74, List.forall_mem_cons.2 ⟨subd17_2_75, List.forall_mem_cons.2 ⟨subd17_2_76, List.forall_mem_cons.2 ⟨subd17_2_77, List.forall_mem_cons.2 ⟨subd17_2_78, List.forall_mem_cons.2 ⟨subd17_2_79, List.forall_mem_cons.2 ⟨subd17_2_80, List.forall_mem_cons.2 ⟨subd17_2_81, List.forall_mem_cons.2 ⟨subd17_2_82, List.forall_mem_cons.2 ⟨subd17_2_83, List.forall_mem_cons.2 ⟨subd17_2_84, List.forall_mem_cons.2 ⟨subd17_2_85, List.forall_mem_cons.2 ⟨subd17_2_86, List.forall_mem_cons.2 ⟨subd17_2_87, List.forall_mem_cons.2 ⟨subd17_2_88, List.forall_mem_cons.2 ⟨subd17_2_89, List.forall_mem_cons.2 ⟨subd17_2_90, List.forall_mem_cons.2 ⟨subd17_2_91, List.forall_mem_cons.2 ⟨subd17_2_92, List.forall_mem_cons.2 ⟨subd17_2_93, List.forall_mem_cons.2 ⟨subd17_2_94, List.forall_mem_cons.2 ⟨subd17_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_96 : subd17_2 [-2, -6] = true := by decide +kernel
theorem subd17_2_97 : subd17_2 [-2, -5] = true := by decide +kernel
theorem subd17_2_98 : subd17_2 [-2, -4, -9] = true := by decide +kernel
theorem subd17_2_99 : subd17_2 [-2, -4, -8] = true := by decide +kernel
theorem subd17_2_100 : subd17_2 [-2, -4, -7] = true := by decide +kernel
theorem subd17_2_101 : subd17_2 [-2, -4, -6] = true := by decide +kernel
theorem subd17_2_102 : subd17_2 [-2, -4, -5] = true := by decide +kernel
theorem subd17_2_103 : subd17_2 [-2, -4, -4] = true := by decide +kernel
theorem subd17_2_104 : subd17_2 [-2, -4, -3] = true := by decide +kernel
theorem subd17_2_105 : subd17_2 [-2, -4, -2] = true := by decide +kernel
theorem subd17_2_106 : subd17_2 [-2, -4, -1] = true := by decide +kernel
theorem subd17_2_107 : subd17_2 [-2, -4, 0] = true := by decide +kernel
theorem subd17_2_108 : subd17_2 [-2, -4, 1] = true := by decide +kernel
theorem subd17_2_109 : subd17_2 [-2, -4, 2] = true := by decide +kernel
theorem subd17_2_110 : subd17_2 [-2, -4, 3] = true := by decide +kernel
theorem subd17_2_111 : subd17_2 [-2, -4, 4] = true := by decide +kernel
theorem subd17_2_112 : subd17_2 [-2, -3, -9] = true := by decide +kernel
theorem subd17_2_113 : subd17_2 [-2, -3, -8] = true := by decide +kernel
theorem subd17_2_114 : subd17_2 [-2, -3, -7] = true := by decide +kernel
theorem subd17_2_115 : subd17_2 [-2, -3, -6] = true := by decide +kernel
theorem subd17_2_116 : subd17_2 [-2, -3, -5] = true := by decide +kernel
theorem subd17_2_117 : subd17_2 [-2, -3, -4] = true := by decide +kernel
theorem subd17_2_118 : subd17_2 [-2, -3, -3] = true := by decide +kernel
theorem subd17_2_119 : subd17_2 [-2, -3, -2] = true := by decide +kernel
theorem subd17_2_120 : subd17_2 [-2, -3, -1] = true := by decide +kernel
theorem subd17_2_121 : subd17_2 [-2, -3, 0] = true := by decide +kernel
theorem subd17_2_122 : subd17_2 [-2, -3, 1] = true := by decide +kernel
theorem subd17_2_123 : subd17_2 [-2, -3, 2] = true := by decide +kernel
theorem subd17_2_124 : subd17_2 [-2, -3, 3] = true := by decide +kernel
theorem subd17_2_125 : subd17_2 [-2, -3, 4] = true := by decide +kernel
theorem subd17_2_126 : subd17_2 [-2, -3, 5] = true := by decide +kernel
theorem subd17_2_127 : subd17_2 [-2, -2, -9] = true := by decide +kernel
theorem sbd17_2_3 : ∀ q ∈ blkd17_2_3, subd17_2 q = true := by
  unfold blkd17_2_3
  exact List.forall_mem_cons.2 ⟨subd17_2_96, List.forall_mem_cons.2 ⟨subd17_2_97, List.forall_mem_cons.2 ⟨subd17_2_98, List.forall_mem_cons.2 ⟨subd17_2_99, List.forall_mem_cons.2 ⟨subd17_2_100, List.forall_mem_cons.2 ⟨subd17_2_101, List.forall_mem_cons.2 ⟨subd17_2_102, List.forall_mem_cons.2 ⟨subd17_2_103, List.forall_mem_cons.2 ⟨subd17_2_104, List.forall_mem_cons.2 ⟨subd17_2_105, List.forall_mem_cons.2 ⟨subd17_2_106, List.forall_mem_cons.2 ⟨subd17_2_107, List.forall_mem_cons.2 ⟨subd17_2_108, List.forall_mem_cons.2 ⟨subd17_2_109, List.forall_mem_cons.2 ⟨subd17_2_110, List.forall_mem_cons.2 ⟨subd17_2_111, List.forall_mem_cons.2 ⟨subd17_2_112, List.forall_mem_cons.2 ⟨subd17_2_113, List.forall_mem_cons.2 ⟨subd17_2_114, List.forall_mem_cons.2 ⟨subd17_2_115, List.forall_mem_cons.2 ⟨subd17_2_116, List.forall_mem_cons.2 ⟨subd17_2_117, List.forall_mem_cons.2 ⟨subd17_2_118, List.forall_mem_cons.2 ⟨subd17_2_119, List.forall_mem_cons.2 ⟨subd17_2_120, List.forall_mem_cons.2 ⟨subd17_2_121, List.forall_mem_cons.2 ⟨subd17_2_122, List.forall_mem_cons.2 ⟨subd17_2_123, List.forall_mem_cons.2 ⟨subd17_2_124, List.forall_mem_cons.2 ⟨subd17_2_125, List.forall_mem_cons.2 ⟨subd17_2_126, List.forall_mem_cons.2 ⟨subd17_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_128 : subd17_2 [-2, -2, -8] = true := by decide +kernel
theorem subd17_2_129 : subd17_2 [-2, -2, -7] = true := by decide +kernel
theorem subd17_2_130 : subd17_2 [-2, -2, -6] = true := by decide +kernel
theorem subd17_2_131 : subd17_2 [-2, -2, -5] = true := by decide +kernel
theorem subd17_2_132 : subd17_2 [-2, -2, -4] = true := by decide +kernel
theorem subd17_2_133 : subd17_2 [-2, -2, -3] = true := by decide +kernel
theorem subd17_2_134 : subd17_2 [-2, -2, -2] = true := by decide +kernel
theorem subd17_2_135 : subd17_2 [-2, -2, -1] = true := by decide +kernel
theorem subd17_2_136 : subd17_2 [-2, -2, 0] = true := by decide +kernel
theorem subd17_2_137 : subd17_2 [-2, -2, 1] = true := by decide +kernel
theorem subd17_2_138 : subd17_2 [-2, -2, 2] = true := by decide +kernel
theorem subd17_2_139 : subd17_2 [-2, -2, 3] = true := by decide +kernel
theorem subd17_2_140 : subd17_2 [-2, -2, 4] = true := by decide +kernel
theorem subd17_2_141 : subd17_2 [-2, -2, 5] = true := by decide +kernel
theorem subd17_2_142 : subd17_2 [-2, -2, 6] = true := by decide +kernel
theorem subd17_2_143 : subd17_2 [-2, -1, -9] = true := by decide +kernel
theorem subd17_2_144 : subd17_2 [-2, -1, -8] = true := by decide +kernel
theorem subd17_2_145 : subd17_2 [-2, -1, -7] = true := by decide +kernel
theorem subd17_2_146 : subd17_2 [-2, -1, -6] = true := by decide +kernel
theorem subd17_2_147 : subd17_2 [-2, -1, -5] = true := by decide +kernel
theorem subd17_2_148 : subd17_2 [-2, -1, -4] = true := by decide +kernel
theorem subd17_2_149 : subd17_2 [-2, -1, -3] = true := by decide +kernel
theorem subd17_2_150 : subd17_2 [-2, -1, -2] = true := by decide +kernel
theorem subd17_2_151 : subd17_2 [-2, -1, -1] = true := by decide +kernel
theorem subd17_2_152 : subd17_2 [-2, -1, 0] = true := by decide +kernel
theorem subd17_2_153 : subd17_2 [-2, -1, 1] = true := by decide +kernel
theorem subd17_2_154 : subd17_2 [-2, -1, 2] = true := by decide +kernel
theorem subd17_2_155 : subd17_2 [-2, -1, 3] = true := by decide +kernel
theorem subd17_2_156 : subd17_2 [-2, -1, 4] = true := by decide +kernel
theorem subd17_2_157 : subd17_2 [-2, -1, 5] = true := by decide +kernel
theorem subd17_2_158 : subd17_2 [-2, -1, 6] = true := by decide +kernel
theorem subd17_2_159 : subd17_2 [-2, -1, 7] = true := by decide +kernel
theorem sbd17_2_4 : ∀ q ∈ blkd17_2_4, subd17_2 q = true := by
  unfold blkd17_2_4
  exact List.forall_mem_cons.2 ⟨subd17_2_128, List.forall_mem_cons.2 ⟨subd17_2_129, List.forall_mem_cons.2 ⟨subd17_2_130, List.forall_mem_cons.2 ⟨subd17_2_131, List.forall_mem_cons.2 ⟨subd17_2_132, List.forall_mem_cons.2 ⟨subd17_2_133, List.forall_mem_cons.2 ⟨subd17_2_134, List.forall_mem_cons.2 ⟨subd17_2_135, List.forall_mem_cons.2 ⟨subd17_2_136, List.forall_mem_cons.2 ⟨subd17_2_137, List.forall_mem_cons.2 ⟨subd17_2_138, List.forall_mem_cons.2 ⟨subd17_2_139, List.forall_mem_cons.2 ⟨subd17_2_140, List.forall_mem_cons.2 ⟨subd17_2_141, List.forall_mem_cons.2 ⟨subd17_2_142, List.forall_mem_cons.2 ⟨subd17_2_143, List.forall_mem_cons.2 ⟨subd17_2_144, List.forall_mem_cons.2 ⟨subd17_2_145, List.forall_mem_cons.2 ⟨subd17_2_146, List.forall_mem_cons.2 ⟨subd17_2_147, List.forall_mem_cons.2 ⟨subd17_2_148, List.forall_mem_cons.2 ⟨subd17_2_149, List.forall_mem_cons.2 ⟨subd17_2_150, List.forall_mem_cons.2 ⟨subd17_2_151, List.forall_mem_cons.2 ⟨subd17_2_152, List.forall_mem_cons.2 ⟨subd17_2_153, List.forall_mem_cons.2 ⟨subd17_2_154, List.forall_mem_cons.2 ⟨subd17_2_155, List.forall_mem_cons.2 ⟨subd17_2_156, List.forall_mem_cons.2 ⟨subd17_2_157, List.forall_mem_cons.2 ⟨subd17_2_158, List.forall_mem_cons.2 ⟨subd17_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_160 : subd17_2 [-2, 0, -9] = true := by decide +kernel
theorem subd17_2_161 : subd17_2 [-2, 0, -8] = true := by decide +kernel
theorem subd17_2_162 : subd17_2 [-2, 0, -7] = true := by decide +kernel
theorem subd17_2_163 : subd17_2 [-2, 0, -6] = true := by decide +kernel
theorem subd17_2_164 : subd17_2 [-2, 0, -5] = true := by decide +kernel
theorem subd17_2_165 : subd17_2 [-2, 0, -4] = true := by decide +kernel
theorem subd17_2_166 : subd17_2 [-2, 0, -3] = true := by decide +kernel
theorem subd17_2_167 : subd17_2 [-2, 0, -2] = true := by decide +kernel
theorem subd17_2_168 : subd17_2 [-2, 0, -1] = true := by decide +kernel
theorem subd17_2_169 : subd17_2 [-2, 0, 0] = true := by decide +kernel
theorem subd17_2_170 : subd17_2 [-2, 0, 1] = true := by decide +kernel
theorem subd17_2_171 : subd17_2 [-2, 0, 2] = true := by decide +kernel
theorem subd17_2_172 : subd17_2 [-2, 0, 3] = true := by decide +kernel
theorem subd17_2_173 : subd17_2 [-2, 0, 4] = true := by decide +kernel
theorem subd17_2_174 : subd17_2 [-2, 0, 5] = true := by decide +kernel
theorem subd17_2_175 : subd17_2 [-2, 0, 6] = true := by decide +kernel
theorem subd17_2_176 : subd17_2 [-2, 0, 7] = true := by decide +kernel
theorem subd17_2_177 : subd17_2 [-2, 1, -8] = true := by decide +kernel
theorem subd17_2_178 : subd17_2 [-2, 1, -7] = true := by decide +kernel
theorem subd17_2_179 : subd17_2 [-2, 1, -6] = true := by decide +kernel
theorem subd17_2_180 : subd17_2 [-2, 1, -5] = true := by decide +kernel
theorem subd17_2_181 : subd17_2 [-2, 1, -4] = true := by decide +kernel
theorem subd17_2_182 : subd17_2 [-2, 1, -3] = true := by decide +kernel
theorem subd17_2_183 : subd17_2 [-2, 1, -2] = true := by decide +kernel
theorem subd17_2_184 : subd17_2 [-2, 1, -1] = true := by decide +kernel
theorem subd17_2_185 : subd17_2 [-2, 1, 0] = true := by decide +kernel
theorem subd17_2_186 : subd17_2 [-2, 1, 1] = true := by decide +kernel
theorem subd17_2_187 : subd17_2 [-2, 1, 2] = true := by decide +kernel
theorem subd17_2_188 : subd17_2 [-2, 1, 3] = true := by decide +kernel
theorem subd17_2_189 : subd17_2 [-2, 1, 4] = true := by decide +kernel
theorem subd17_2_190 : subd17_2 [-2, 1, 5] = true := by decide +kernel
theorem subd17_2_191 : subd17_2 [-2, 1, 6] = true := by decide +kernel
theorem sbd17_2_5 : ∀ q ∈ blkd17_2_5, subd17_2 q = true := by
  unfold blkd17_2_5
  exact List.forall_mem_cons.2 ⟨subd17_2_160, List.forall_mem_cons.2 ⟨subd17_2_161, List.forall_mem_cons.2 ⟨subd17_2_162, List.forall_mem_cons.2 ⟨subd17_2_163, List.forall_mem_cons.2 ⟨subd17_2_164, List.forall_mem_cons.2 ⟨subd17_2_165, List.forall_mem_cons.2 ⟨subd17_2_166, List.forall_mem_cons.2 ⟨subd17_2_167, List.forall_mem_cons.2 ⟨subd17_2_168, List.forall_mem_cons.2 ⟨subd17_2_169, List.forall_mem_cons.2 ⟨subd17_2_170, List.forall_mem_cons.2 ⟨subd17_2_171, List.forall_mem_cons.2 ⟨subd17_2_172, List.forall_mem_cons.2 ⟨subd17_2_173, List.forall_mem_cons.2 ⟨subd17_2_174, List.forall_mem_cons.2 ⟨subd17_2_175, List.forall_mem_cons.2 ⟨subd17_2_176, List.forall_mem_cons.2 ⟨subd17_2_177, List.forall_mem_cons.2 ⟨subd17_2_178, List.forall_mem_cons.2 ⟨subd17_2_179, List.forall_mem_cons.2 ⟨subd17_2_180, List.forall_mem_cons.2 ⟨subd17_2_181, List.forall_mem_cons.2 ⟨subd17_2_182, List.forall_mem_cons.2 ⟨subd17_2_183, List.forall_mem_cons.2 ⟨subd17_2_184, List.forall_mem_cons.2 ⟨subd17_2_185, List.forall_mem_cons.2 ⟨subd17_2_186, List.forall_mem_cons.2 ⟨subd17_2_187, List.forall_mem_cons.2 ⟨subd17_2_188, List.forall_mem_cons.2 ⟨subd17_2_189, List.forall_mem_cons.2 ⟨subd17_2_190, List.forall_mem_cons.2 ⟨subd17_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_192 : subd17_2 [-2, 1, 7] = true := by decide +kernel
theorem subd17_2_193 : subd17_2 [-2, 2, -7] = true := by decide +kernel
theorem subd17_2_194 : subd17_2 [-2, 2, -6] = true := by decide +kernel
theorem subd17_2_195 : subd17_2 [-2, 2, -5] = true := by decide +kernel
theorem subd17_2_196 : subd17_2 [-2, 2, -4] = true := by decide +kernel
theorem subd17_2_197 : subd17_2 [-2, 2, -3] = true := by decide +kernel
theorem subd17_2_198 : subd17_2 [-2, 2, -2] = true := by decide +kernel
theorem subd17_2_199 : subd17_2 [-2, 2, -1] = true := by decide +kernel
theorem subd17_2_200 : subd17_2 [-2, 2, 0] = true := by decide +kernel
theorem subd17_2_201 : subd17_2 [-2, 2, 1] = true := by decide +kernel
theorem subd17_2_202 : subd17_2 [-2, 2, 2] = true := by decide +kernel
theorem subd17_2_203 : subd17_2 [-2, 2, 3] = true := by decide +kernel
theorem subd17_2_204 : subd17_2 [-2, 2, 4] = true := by decide +kernel
theorem subd17_2_205 : subd17_2 [-2, 2, 5] = true := by decide +kernel
theorem subd17_2_206 : subd17_2 [-2, 2, 6] = true := by decide +kernel
theorem subd17_2_207 : subd17_2 [-2, 2, 7] = true := by decide +kernel
theorem subd17_2_208 : subd17_2 [-2, 3] = true := by decide +kernel
theorem subd17_2_209 : subd17_2 [-2, 4] = true := by decide +kernel
theorem subd17_2_210 : subd17_2 [-1, -7] = true := by decide +kernel
theorem subd17_2_211 : subd17_2 [-1, -6] = true := by decide +kernel
theorem subd17_2_212 : subd17_2 [-1, -5] = true := by decide +kernel
theorem subd17_2_213 : subd17_2 [-1, -4, -9] = true := by decide +kernel
theorem subd17_2_214 : subd17_2 [-1, -4, -8] = true := by decide +kernel
theorem subd17_2_215 : subd17_2 [-1, -4, -7] = true := by decide +kernel
theorem subd17_2_216 : subd17_2 [-1, -4, -6] = true := by decide +kernel
theorem subd17_2_217 : subd17_2 [-1, -4, -5] = true := by decide +kernel
theorem subd17_2_218 : subd17_2 [-1, -4, -4] = true := by decide +kernel
theorem subd17_2_219 : subd17_2 [-1, -4, -3] = true := by decide +kernel
theorem subd17_2_220 : subd17_2 [-1, -4, -2] = true := by decide +kernel
theorem subd17_2_221 : subd17_2 [-1, -4, -1] = true := by decide +kernel
theorem subd17_2_222 : subd17_2 [-1, -4, 0] = true := by decide +kernel
theorem subd17_2_223 : subd17_2 [-1, -4, 1] = true := by decide +kernel
theorem sbd17_2_6 : ∀ q ∈ blkd17_2_6, subd17_2 q = true := by
  unfold blkd17_2_6
  exact List.forall_mem_cons.2 ⟨subd17_2_192, List.forall_mem_cons.2 ⟨subd17_2_193, List.forall_mem_cons.2 ⟨subd17_2_194, List.forall_mem_cons.2 ⟨subd17_2_195, List.forall_mem_cons.2 ⟨subd17_2_196, List.forall_mem_cons.2 ⟨subd17_2_197, List.forall_mem_cons.2 ⟨subd17_2_198, List.forall_mem_cons.2 ⟨subd17_2_199, List.forall_mem_cons.2 ⟨subd17_2_200, List.forall_mem_cons.2 ⟨subd17_2_201, List.forall_mem_cons.2 ⟨subd17_2_202, List.forall_mem_cons.2 ⟨subd17_2_203, List.forall_mem_cons.2 ⟨subd17_2_204, List.forall_mem_cons.2 ⟨subd17_2_205, List.forall_mem_cons.2 ⟨subd17_2_206, List.forall_mem_cons.2 ⟨subd17_2_207, List.forall_mem_cons.2 ⟨subd17_2_208, List.forall_mem_cons.2 ⟨subd17_2_209, List.forall_mem_cons.2 ⟨subd17_2_210, List.forall_mem_cons.2 ⟨subd17_2_211, List.forall_mem_cons.2 ⟨subd17_2_212, List.forall_mem_cons.2 ⟨subd17_2_213, List.forall_mem_cons.2 ⟨subd17_2_214, List.forall_mem_cons.2 ⟨subd17_2_215, List.forall_mem_cons.2 ⟨subd17_2_216, List.forall_mem_cons.2 ⟨subd17_2_217, List.forall_mem_cons.2 ⟨subd17_2_218, List.forall_mem_cons.2 ⟨subd17_2_219, List.forall_mem_cons.2 ⟨subd17_2_220, List.forall_mem_cons.2 ⟨subd17_2_221, List.forall_mem_cons.2 ⟨subd17_2_222, List.forall_mem_cons.2 ⟨subd17_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_224 : subd17_2 [-1, -4, 2] = true := by decide +kernel
theorem subd17_2_225 : subd17_2 [-1, -4, 3] = true := by decide +kernel
theorem subd17_2_226 : subd17_2 [-1, -4, 4] = true := by decide +kernel
theorem subd17_2_227 : subd17_2 [-1, -4, 5] = true := by decide +kernel
theorem subd17_2_228 : subd17_2 [-1, -3, -9] = true := by decide +kernel
theorem subd17_2_229 : subd17_2 [-1, -3, -8] = true := by decide +kernel
theorem subd17_2_230 : subd17_2 [-1, -3, -7] = true := by decide +kernel
theorem subd17_2_231 : subd17_2 [-1, -3, -6] = true := by decide +kernel
theorem subd17_2_232 : subd17_2 [-1, -3, -5] = true := by decide +kernel
theorem subd17_2_233 : subd17_2 [-1, -3, -4] = true := by decide +kernel
theorem subd17_2_234 : subd17_2 [-1, -3, -3] = true := by decide +kernel
theorem subd17_2_235 : subd17_2 [-1, -3, -2] = true := by decide +kernel
theorem subd17_2_236 : subd17_2 [-1, -3, -1] = true := by decide +kernel
theorem subd17_2_237 : subd17_2 [-1, -3, 0] = true := by decide +kernel
theorem subd17_2_238 : subd17_2 [-1, -3, 1] = true := by decide +kernel
theorem subd17_2_239 : subd17_2 [-1, -3, 2] = true := by decide +kernel
theorem subd17_2_240 : subd17_2 [-1, -3, 3] = true := by decide +kernel
theorem subd17_2_241 : subd17_2 [-1, -3, 4] = true := by decide +kernel
theorem subd17_2_242 : subd17_2 [-1, -3, 5] = true := by decide +kernel
theorem subd17_2_243 : subd17_2 [-1, -3, 6] = true := by decide +kernel
theorem subd17_2_244 : subd17_2 [-1, -2, -9] = true := by decide +kernel
theorem subd17_2_245 : subd17_2 [-1, -2, -8] = true := by decide +kernel
theorem subd17_2_246 : subd17_2 [-1, -2, -7] = true := by decide +kernel
theorem subd17_2_247 : subd17_2 [-1, -2, -6] = true := by decide +kernel
theorem subd17_2_248 : subd17_2 [-1, -2, -5] = true := by decide +kernel
theorem subd17_2_249 : subd17_2 [-1, -2, -4] = true := by decide +kernel
theorem subd17_2_250 : subd17_2 [-1, -2, -3] = true := by decide +kernel
theorem subd17_2_251 : subd17_2 [-1, -2, -2] = true := by decide +kernel
theorem subd17_2_252 : subd17_2 [-1, -2, -1] = true := by decide +kernel
theorem subd17_2_253 : subd17_2 [-1, -2, 0] = true := by decide +kernel
theorem subd17_2_254 : subd17_2 [-1, -2, 1] = true := by decide +kernel
theorem subd17_2_255 : subd17_2 [-1, -2, 2] = true := by decide +kernel
theorem sbd17_2_7 : ∀ q ∈ blkd17_2_7, subd17_2 q = true := by
  unfold blkd17_2_7
  exact List.forall_mem_cons.2 ⟨subd17_2_224, List.forall_mem_cons.2 ⟨subd17_2_225, List.forall_mem_cons.2 ⟨subd17_2_226, List.forall_mem_cons.2 ⟨subd17_2_227, List.forall_mem_cons.2 ⟨subd17_2_228, List.forall_mem_cons.2 ⟨subd17_2_229, List.forall_mem_cons.2 ⟨subd17_2_230, List.forall_mem_cons.2 ⟨subd17_2_231, List.forall_mem_cons.2 ⟨subd17_2_232, List.forall_mem_cons.2 ⟨subd17_2_233, List.forall_mem_cons.2 ⟨subd17_2_234, List.forall_mem_cons.2 ⟨subd17_2_235, List.forall_mem_cons.2 ⟨subd17_2_236, List.forall_mem_cons.2 ⟨subd17_2_237, List.forall_mem_cons.2 ⟨subd17_2_238, List.forall_mem_cons.2 ⟨subd17_2_239, List.forall_mem_cons.2 ⟨subd17_2_240, List.forall_mem_cons.2 ⟨subd17_2_241, List.forall_mem_cons.2 ⟨subd17_2_242, List.forall_mem_cons.2 ⟨subd17_2_243, List.forall_mem_cons.2 ⟨subd17_2_244, List.forall_mem_cons.2 ⟨subd17_2_245, List.forall_mem_cons.2 ⟨subd17_2_246, List.forall_mem_cons.2 ⟨subd17_2_247, List.forall_mem_cons.2 ⟨subd17_2_248, List.forall_mem_cons.2 ⟨subd17_2_249, List.forall_mem_cons.2 ⟨subd17_2_250, List.forall_mem_cons.2 ⟨subd17_2_251, List.forall_mem_cons.2 ⟨subd17_2_252, List.forall_mem_cons.2 ⟨subd17_2_253, List.forall_mem_cons.2 ⟨subd17_2_254, List.forall_mem_cons.2 ⟨subd17_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_256 : subd17_2 [-1, -2, 3] = true := by decide +kernel
theorem subd17_2_257 : subd17_2 [-1, -2, 4] = true := by decide +kernel
theorem subd17_2_258 : subd17_2 [-1, -2, 5] = true := by decide +kernel
theorem subd17_2_259 : subd17_2 [-1, -2, 6] = true := by decide +kernel
theorem subd17_2_260 : subd17_2 [-1, -2, 7] = true := by decide +kernel
theorem subd17_2_261 : subd17_2 [-1, -1, -9] = true := by decide +kernel
theorem subd17_2_262 : subd17_2 [-1, -1, -8] = true := by decide +kernel
theorem subd17_2_263 : subd17_2 [-1, -1, -7] = true := by decide +kernel
theorem subd17_2_264 : subd17_2 [-1, -1, -6] = true := by decide +kernel
theorem subd17_2_265 : subd17_2 [-1, -1, -5] = true := by decide +kernel
theorem subd17_2_266 : subd17_2 [-1, -1, -4] = true := by decide +kernel
theorem subd17_2_267 : subd17_2 [-1, -1, -3] = true := by decide +kernel
theorem subd17_2_268 : subd17_2 [-1, -1, -2] = true := by decide +kernel
theorem subd17_2_269 : subd17_2 [-1, -1, -1] = true := by decide +kernel
theorem subd17_2_270 : subd17_2 [-1, -1, 0] = true := by decide +kernel
theorem subd17_2_271 : subd17_2 [-1, -1, 1] = true := by decide +kernel
theorem subd17_2_272 : subd17_2 [-1, -1, 2] = true := by decide +kernel
theorem subd17_2_273 : subd17_2 [-1, -1, 3] = true := by decide +kernel
theorem subd17_2_274 : subd17_2 [-1, -1, 4] = true := by decide +kernel
theorem subd17_2_275 : subd17_2 [-1, -1, 5] = true := by decide +kernel
theorem subd17_2_276 : subd17_2 [-1, -1, 6] = true := by decide +kernel
theorem subd17_2_277 : subd17_2 [-1, -1, 7] = true := by decide +kernel
theorem subd17_2_278 : subd17_2 [-1, 0, -9] = true := by decide +kernel
theorem subd17_2_279 : subd17_2 [-1, 0, -8] = true := by decide +kernel
theorem subd17_2_280 : subd17_2 [-1, 0, -7] = true := by decide +kernel
theorem subd17_2_281 : subd17_2 [-1, 0, -6] = true := by decide +kernel
theorem subd17_2_282 : subd17_2 [-1, 0, -5] = true := by decide +kernel
theorem subd17_2_283 : subd17_2 [-1, 0, -4] = true := by decide +kernel
theorem subd17_2_284 : subd17_2 [-1, 0, -3] = true := by decide +kernel
theorem subd17_2_285 : subd17_2 [-1, 0, -2] = true := by decide +kernel
theorem subd17_2_286 : subd17_2 [-1, 0, -1] = true := by decide +kernel
theorem subd17_2_287 : subd17_2 [-1, 0, 0] = true := by decide +kernel
theorem sbd17_2_8 : ∀ q ∈ blkd17_2_8, subd17_2 q = true := by
  unfold blkd17_2_8
  exact List.forall_mem_cons.2 ⟨subd17_2_256, List.forall_mem_cons.2 ⟨subd17_2_257, List.forall_mem_cons.2 ⟨subd17_2_258, List.forall_mem_cons.2 ⟨subd17_2_259, List.forall_mem_cons.2 ⟨subd17_2_260, List.forall_mem_cons.2 ⟨subd17_2_261, List.forall_mem_cons.2 ⟨subd17_2_262, List.forall_mem_cons.2 ⟨subd17_2_263, List.forall_mem_cons.2 ⟨subd17_2_264, List.forall_mem_cons.2 ⟨subd17_2_265, List.forall_mem_cons.2 ⟨subd17_2_266, List.forall_mem_cons.2 ⟨subd17_2_267, List.forall_mem_cons.2 ⟨subd17_2_268, List.forall_mem_cons.2 ⟨subd17_2_269, List.forall_mem_cons.2 ⟨subd17_2_270, List.forall_mem_cons.2 ⟨subd17_2_271, List.forall_mem_cons.2 ⟨subd17_2_272, List.forall_mem_cons.2 ⟨subd17_2_273, List.forall_mem_cons.2 ⟨subd17_2_274, List.forall_mem_cons.2 ⟨subd17_2_275, List.forall_mem_cons.2 ⟨subd17_2_276, List.forall_mem_cons.2 ⟨subd17_2_277, List.forall_mem_cons.2 ⟨subd17_2_278, List.forall_mem_cons.2 ⟨subd17_2_279, List.forall_mem_cons.2 ⟨subd17_2_280, List.forall_mem_cons.2 ⟨subd17_2_281, List.forall_mem_cons.2 ⟨subd17_2_282, List.forall_mem_cons.2 ⟨subd17_2_283, List.forall_mem_cons.2 ⟨subd17_2_284, List.forall_mem_cons.2 ⟨subd17_2_285, List.forall_mem_cons.2 ⟨subd17_2_286, List.forall_mem_cons.2 ⟨subd17_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_288 : subd17_2 [-1, 0, 1] = true := by decide +kernel
theorem subd17_2_289 : subd17_2 [-1, 0, 2] = true := by decide +kernel
theorem subd17_2_290 : subd17_2 [-1, 0, 3] = true := by decide +kernel
theorem subd17_2_291 : subd17_2 [-1, 0, 4] = true := by decide +kernel
theorem subd17_2_292 : subd17_2 [-1, 0, 5] = true := by decide +kernel
theorem subd17_2_293 : subd17_2 [-1, 0, 6] = true := by decide +kernel
theorem subd17_2_294 : subd17_2 [-1, 0, 7] = true := by decide +kernel
theorem subd17_2_295 : subd17_2 [-1, 0, 8] = true := by decide +kernel
theorem subd17_2_296 : subd17_2 [-1, 1, -8] = true := by decide +kernel
theorem subd17_2_297 : subd17_2 [-1, 1, -7] = true := by decide +kernel
theorem subd17_2_298 : subd17_2 [-1, 1, -6] = true := by decide +kernel
theorem subd17_2_299 : subd17_2 [-1, 1, -5] = true := by decide +kernel
theorem subd17_2_300 : subd17_2 [-1, 1, -4] = true := by decide +kernel
theorem subd17_2_301 : subd17_2 [-1, 1, -3] = true := by decide +kernel
theorem subd17_2_302 : subd17_2 [-1, 1, -2] = true := by decide +kernel
theorem subd17_2_303 : subd17_2 [-1, 1, -1] = true := by decide +kernel
theorem subd17_2_304 : subd17_2 [-1, 1, 0] = true := by decide +kernel
theorem subd17_2_305 : subd17_2 [-1, 1, 1] = true := by decide +kernel
theorem subd17_2_306 : subd17_2 [-1, 1, 2] = true := by decide +kernel
theorem subd17_2_307 : subd17_2 [-1, 1, 3] = true := by decide +kernel
theorem subd17_2_308 : subd17_2 [-1, 1, 4] = true := by decide +kernel
theorem subd17_2_309 : subd17_2 [-1, 1, 5] = true := by decide +kernel
theorem subd17_2_310 : subd17_2 [-1, 1, 6] = true := by decide +kernel
theorem subd17_2_311 : subd17_2 [-1, 1, 7] = true := by decide +kernel
theorem subd17_2_312 : subd17_2 [-1, 1, 8] = true := by decide +kernel
theorem subd17_2_313 : subd17_2 [-1, 2, -8] = true := by decide +kernel
theorem subd17_2_314 : subd17_2 [-1, 2, -7] = true := by decide +kernel
theorem subd17_2_315 : subd17_2 [-1, 2, -6] = true := by decide +kernel
theorem subd17_2_316 : subd17_2 [-1, 2, -5] = true := by decide +kernel
theorem subd17_2_317 : subd17_2 [-1, 2, -4] = true := by decide +kernel
theorem subd17_2_318 : subd17_2 [-1, 2, -3] = true := by decide +kernel
theorem subd17_2_319 : subd17_2 [-1, 2, -2] = true := by decide +kernel
theorem sbd17_2_9 : ∀ q ∈ blkd17_2_9, subd17_2 q = true := by
  unfold blkd17_2_9
  exact List.forall_mem_cons.2 ⟨subd17_2_288, List.forall_mem_cons.2 ⟨subd17_2_289, List.forall_mem_cons.2 ⟨subd17_2_290, List.forall_mem_cons.2 ⟨subd17_2_291, List.forall_mem_cons.2 ⟨subd17_2_292, List.forall_mem_cons.2 ⟨subd17_2_293, List.forall_mem_cons.2 ⟨subd17_2_294, List.forall_mem_cons.2 ⟨subd17_2_295, List.forall_mem_cons.2 ⟨subd17_2_296, List.forall_mem_cons.2 ⟨subd17_2_297, List.forall_mem_cons.2 ⟨subd17_2_298, List.forall_mem_cons.2 ⟨subd17_2_299, List.forall_mem_cons.2 ⟨subd17_2_300, List.forall_mem_cons.2 ⟨subd17_2_301, List.forall_mem_cons.2 ⟨subd17_2_302, List.forall_mem_cons.2 ⟨subd17_2_303, List.forall_mem_cons.2 ⟨subd17_2_304, List.forall_mem_cons.2 ⟨subd17_2_305, List.forall_mem_cons.2 ⟨subd17_2_306, List.forall_mem_cons.2 ⟨subd17_2_307, List.forall_mem_cons.2 ⟨subd17_2_308, List.forall_mem_cons.2 ⟨subd17_2_309, List.forall_mem_cons.2 ⟨subd17_2_310, List.forall_mem_cons.2 ⟨subd17_2_311, List.forall_mem_cons.2 ⟨subd17_2_312, List.forall_mem_cons.2 ⟨subd17_2_313, List.forall_mem_cons.2 ⟨subd17_2_314, List.forall_mem_cons.2 ⟨subd17_2_315, List.forall_mem_cons.2 ⟨subd17_2_316, List.forall_mem_cons.2 ⟨subd17_2_317, List.forall_mem_cons.2 ⟨subd17_2_318, List.forall_mem_cons.2 ⟨subd17_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_320 : subd17_2 [-1, 2, -1] = true := by decide +kernel
theorem subd17_2_321 : subd17_2 [-1, 2, 0] = true := by decide +kernel
theorem subd17_2_322 : subd17_2 [-1, 2, 1] = true := by decide +kernel
theorem subd17_2_323 : subd17_2 [-1, 2, 2] = true := by decide +kernel
theorem subd17_2_324 : subd17_2 [-1, 2, 3] = true := by decide +kernel
theorem subd17_2_325 : subd17_2 [-1, 2, 4] = true := by decide +kernel
theorem subd17_2_326 : subd17_2 [-1, 2, 5] = true := by decide +kernel
theorem subd17_2_327 : subd17_2 [-1, 2, 6] = true := by decide +kernel
theorem subd17_2_328 : subd17_2 [-1, 2, 7] = true := by decide +kernel
theorem subd17_2_329 : subd17_2 [-1, 2, 8] = true := by decide +kernel
theorem subd17_2_330 : subd17_2 [-1, 3, -6] = true := by decide +kernel
theorem subd17_2_331 : subd17_2 [-1, 3, -5] = true := by decide +kernel
theorem subd17_2_332 : subd17_2 [-1, 3, -4] = true := by decide +kernel
theorem subd17_2_333 : subd17_2 [-1, 3, -3] = true := by decide +kernel
theorem subd17_2_334 : subd17_2 [-1, 3, -2] = true := by decide +kernel
theorem subd17_2_335 : subd17_2 [-1, 3, -1] = true := by decide +kernel
theorem subd17_2_336 : subd17_2 [-1, 3, 0] = true := by decide +kernel
theorem subd17_2_337 : subd17_2 [-1, 3, 1] = true := by decide +kernel
theorem subd17_2_338 : subd17_2 [-1, 3, 2] = true := by decide +kernel
theorem subd17_2_339 : subd17_2 [-1, 3, 3] = true := by decide +kernel
theorem subd17_2_340 : subd17_2 [-1, 3, 4] = true := by decide +kernel
theorem subd17_2_341 : subd17_2 [-1, 3, 5] = true := by decide +kernel
theorem subd17_2_342 : subd17_2 [-1, 3, 6] = true := by decide +kernel
theorem subd17_2_343 : subd17_2 [-1, 3, 7] = true := by decide +kernel
theorem subd17_2_344 : subd17_2 [-1, 4] = true := by decide +kernel
theorem subd17_2_345 : subd17_2 [-1, 5] = true := by decide +kernel
theorem subd17_2_346 : subd17_2 [0, -7] = true := by decide +kernel
theorem subd17_2_347 : subd17_2 [0, -6] = true := by decide +kernel
theorem subd17_2_348 : subd17_2 [0, -5] = true := by decide +kernel
theorem subd17_2_349 : subd17_2 [0, -4, -8] = true := by decide +kernel
theorem subd17_2_350 : subd17_2 [0, -4, -7] = true := by decide +kernel
theorem subd17_2_351 : subd17_2 [0, -4, -6] = true := by decide +kernel
theorem sbd17_2_10 : ∀ q ∈ blkd17_2_10, subd17_2 q = true := by
  unfold blkd17_2_10
  exact List.forall_mem_cons.2 ⟨subd17_2_320, List.forall_mem_cons.2 ⟨subd17_2_321, List.forall_mem_cons.2 ⟨subd17_2_322, List.forall_mem_cons.2 ⟨subd17_2_323, List.forall_mem_cons.2 ⟨subd17_2_324, List.forall_mem_cons.2 ⟨subd17_2_325, List.forall_mem_cons.2 ⟨subd17_2_326, List.forall_mem_cons.2 ⟨subd17_2_327, List.forall_mem_cons.2 ⟨subd17_2_328, List.forall_mem_cons.2 ⟨subd17_2_329, List.forall_mem_cons.2 ⟨subd17_2_330, List.forall_mem_cons.2 ⟨subd17_2_331, List.forall_mem_cons.2 ⟨subd17_2_332, List.forall_mem_cons.2 ⟨subd17_2_333, List.forall_mem_cons.2 ⟨subd17_2_334, List.forall_mem_cons.2 ⟨subd17_2_335, List.forall_mem_cons.2 ⟨subd17_2_336, List.forall_mem_cons.2 ⟨subd17_2_337, List.forall_mem_cons.2 ⟨subd17_2_338, List.forall_mem_cons.2 ⟨subd17_2_339, List.forall_mem_cons.2 ⟨subd17_2_340, List.forall_mem_cons.2 ⟨subd17_2_341, List.forall_mem_cons.2 ⟨subd17_2_342, List.forall_mem_cons.2 ⟨subd17_2_343, List.forall_mem_cons.2 ⟨subd17_2_344, List.forall_mem_cons.2 ⟨subd17_2_345, List.forall_mem_cons.2 ⟨subd17_2_346, List.forall_mem_cons.2 ⟨subd17_2_347, List.forall_mem_cons.2 ⟨subd17_2_348, List.forall_mem_cons.2 ⟨subd17_2_349, List.forall_mem_cons.2 ⟨subd17_2_350, List.forall_mem_cons.2 ⟨subd17_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_352 : subd17_2 [0, -4, -5] = true := by decide +kernel
theorem subd17_2_353 : subd17_2 [0, -4, -4] = true := by decide +kernel
theorem subd17_2_354 : subd17_2 [0, -4, -3] = true := by decide +kernel
theorem subd17_2_355 : subd17_2 [0, -4, -2] = true := by decide +kernel
theorem subd17_2_356 : subd17_2 [0, -4, -1] = true := by decide +kernel
theorem subd17_2_357 : subd17_2 [0, -4, 0] = true := by decide +kernel
theorem subd17_2_358 : subd17_2 [0, -4, 1] = true := by decide +kernel
theorem subd17_2_359 : subd17_2 [0, -4, 2] = true := by decide +kernel
theorem subd17_2_360 : subd17_2 [0, -4, 3] = true := by decide +kernel
theorem subd17_2_361 : subd17_2 [0, -4, 4] = true := by decide +kernel
theorem subd17_2_362 : subd17_2 [0, -3, -9] = true := by decide +kernel
theorem subd17_2_363 : subd17_2 [0, -3, -8] = true := by decide +kernel
theorem subd17_2_364 : subd17_2 [0, -3, -7] = true := by decide +kernel
theorem subd17_2_365 : subd17_2 [0, -3, -6] = true := by decide +kernel
theorem subd17_2_366 : subd17_2 [0, -3, -5] = true := by decide +kernel
theorem subd17_2_367 : subd17_2 [0, -3, -4] = true := by decide +kernel
theorem subd17_2_368 : subd17_2 [0, -3, -3] = true := by decide +kernel
theorem subd17_2_369 : subd17_2 [0, -3, -2] = true := by decide +kernel
theorem subd17_2_370 : subd17_2 [0, -3, -1] = true := by decide +kernel
theorem subd17_2_371 : subd17_2 [0, -3, 0] = true := by decide +kernel
theorem subd17_2_372 : subd17_2 [0, -3, 1] = true := by decide +kernel
theorem subd17_2_373 : subd17_2 [0, -3, 2] = true := by decide +kernel
theorem subd17_2_374 : subd17_2 [0, -3, 3] = true := by decide +kernel
theorem subd17_2_375 : subd17_2 [0, -3, 4] = true := by decide +kernel
theorem subd17_2_376 : subd17_2 [0, -3, 5] = true := by decide +kernel
theorem subd17_2_377 : subd17_2 [0, -3, 6] = true := by decide +kernel
theorem subd17_2_378 : subd17_2 [0, -2, -9] = true := by decide +kernel
theorem subd17_2_379 : subd17_2 [0, -2, -8] = true := by decide +kernel
theorem subd17_2_380 : subd17_2 [0, -2, -7] = true := by decide +kernel
theorem subd17_2_381 : subd17_2 [0, -2, -6] = true := by decide +kernel
theorem subd17_2_382 : subd17_2 [0, -2, -5] = true := by decide +kernel
theorem subd17_2_383 : subd17_2 [0, -2, -4] = true := by decide +kernel
theorem sbd17_2_11 : ∀ q ∈ blkd17_2_11, subd17_2 q = true := by
  unfold blkd17_2_11
  exact List.forall_mem_cons.2 ⟨subd17_2_352, List.forall_mem_cons.2 ⟨subd17_2_353, List.forall_mem_cons.2 ⟨subd17_2_354, List.forall_mem_cons.2 ⟨subd17_2_355, List.forall_mem_cons.2 ⟨subd17_2_356, List.forall_mem_cons.2 ⟨subd17_2_357, List.forall_mem_cons.2 ⟨subd17_2_358, List.forall_mem_cons.2 ⟨subd17_2_359, List.forall_mem_cons.2 ⟨subd17_2_360, List.forall_mem_cons.2 ⟨subd17_2_361, List.forall_mem_cons.2 ⟨subd17_2_362, List.forall_mem_cons.2 ⟨subd17_2_363, List.forall_mem_cons.2 ⟨subd17_2_364, List.forall_mem_cons.2 ⟨subd17_2_365, List.forall_mem_cons.2 ⟨subd17_2_366, List.forall_mem_cons.2 ⟨subd17_2_367, List.forall_mem_cons.2 ⟨subd17_2_368, List.forall_mem_cons.2 ⟨subd17_2_369, List.forall_mem_cons.2 ⟨subd17_2_370, List.forall_mem_cons.2 ⟨subd17_2_371, List.forall_mem_cons.2 ⟨subd17_2_372, List.forall_mem_cons.2 ⟨subd17_2_373, List.forall_mem_cons.2 ⟨subd17_2_374, List.forall_mem_cons.2 ⟨subd17_2_375, List.forall_mem_cons.2 ⟨subd17_2_376, List.forall_mem_cons.2 ⟨subd17_2_377, List.forall_mem_cons.2 ⟨subd17_2_378, List.forall_mem_cons.2 ⟨subd17_2_379, List.forall_mem_cons.2 ⟨subd17_2_380, List.forall_mem_cons.2 ⟨subd17_2_381, List.forall_mem_cons.2 ⟨subd17_2_382, List.forall_mem_cons.2 ⟨subd17_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_384 : subd17_2 [0, -2, -3] = true := by decide +kernel
theorem subd17_2_385 : subd17_2 [0, -2, -2] = true := by decide +kernel
theorem subd17_2_386 : subd17_2 [0, -2, -1] = true := by decide +kernel
theorem subd17_2_387 : subd17_2 [0, -2, 0] = true := by decide +kernel
theorem subd17_2_388 : subd17_2 [0, -2, 1] = true := by decide +kernel
theorem subd17_2_389 : subd17_2 [0, -2, 2] = true := by decide +kernel
theorem subd17_2_390 : subd17_2 [0, -2, 3] = true := by decide +kernel
theorem subd17_2_391 : subd17_2 [0, -2, 4] = true := by decide +kernel
theorem subd17_2_392 : subd17_2 [0, -2, 5] = true := by decide +kernel
theorem subd17_2_393 : subd17_2 [0, -2, 6] = true := by decide +kernel
theorem subd17_2_394 : subd17_2 [0, -2, 7] = true := by decide +kernel
theorem subd17_2_395 : subd17_2 [0, -1, -9] = true := by decide +kernel
theorem subd17_2_396 : subd17_2 [0, -1, -8] = true := by decide +kernel
theorem subd17_2_397 : subd17_2 [0, -1, -7] = true := by decide +kernel
theorem subd17_2_398 : subd17_2 [0, -1, -6] = true := by decide +kernel
theorem subd17_2_399 : subd17_2 [0, -1, -5] = true := by decide +kernel
theorem subd17_2_400 : subd17_2 [0, -1, -4] = true := by decide +kernel
theorem subd17_2_401 : subd17_2 [0, -1, -3] = true := by decide +kernel
theorem subd17_2_402 : subd17_2 [0, -1, -2] = true := by decide +kernel
theorem subd17_2_403 : subd17_2 [0, -1, -1] = true := by decide +kernel
theorem subd17_2_404 : subd17_2 [0, -1, 0] = true := by decide +kernel
theorem subd17_2_405 : subd17_2 [0, -1, 1] = true := by decide +kernel
theorem subd17_2_406 : subd17_2 [0, -1, 2] = true := by decide +kernel
theorem subd17_2_407 : subd17_2 [0, -1, 3] = true := by decide +kernel
theorem subd17_2_408 : subd17_2 [0, -1, 4] = true := by decide +kernel
theorem subd17_2_409 : subd17_2 [0, -1, 5] = true := by decide +kernel
theorem subd17_2_410 : subd17_2 [0, -1, 6] = true := by decide +kernel
theorem subd17_2_411 : subd17_2 [0, -1, 7] = true := by decide +kernel
theorem subd17_2_412 : subd17_2 [0, -1, 8] = true := by decide +kernel
theorem subd17_2_413 : subd17_2 [0, 0, -9] = true := by decide +kernel
theorem subd17_2_414 : subd17_2 [0, 0, -8] = true := by decide +kernel
theorem subd17_2_415 : subd17_2 [0, 0, -7] = true := by decide +kernel
theorem sbd17_2_12 : ∀ q ∈ blkd17_2_12, subd17_2 q = true := by
  unfold blkd17_2_12
  exact List.forall_mem_cons.2 ⟨subd17_2_384, List.forall_mem_cons.2 ⟨subd17_2_385, List.forall_mem_cons.2 ⟨subd17_2_386, List.forall_mem_cons.2 ⟨subd17_2_387, List.forall_mem_cons.2 ⟨subd17_2_388, List.forall_mem_cons.2 ⟨subd17_2_389, List.forall_mem_cons.2 ⟨subd17_2_390, List.forall_mem_cons.2 ⟨subd17_2_391, List.forall_mem_cons.2 ⟨subd17_2_392, List.forall_mem_cons.2 ⟨subd17_2_393, List.forall_mem_cons.2 ⟨subd17_2_394, List.forall_mem_cons.2 ⟨subd17_2_395, List.forall_mem_cons.2 ⟨subd17_2_396, List.forall_mem_cons.2 ⟨subd17_2_397, List.forall_mem_cons.2 ⟨subd17_2_398, List.forall_mem_cons.2 ⟨subd17_2_399, List.forall_mem_cons.2 ⟨subd17_2_400, List.forall_mem_cons.2 ⟨subd17_2_401, List.forall_mem_cons.2 ⟨subd17_2_402, List.forall_mem_cons.2 ⟨subd17_2_403, List.forall_mem_cons.2 ⟨subd17_2_404, List.forall_mem_cons.2 ⟨subd17_2_405, List.forall_mem_cons.2 ⟨subd17_2_406, List.forall_mem_cons.2 ⟨subd17_2_407, List.forall_mem_cons.2 ⟨subd17_2_408, List.forall_mem_cons.2 ⟨subd17_2_409, List.forall_mem_cons.2 ⟨subd17_2_410, List.forall_mem_cons.2 ⟨subd17_2_411, List.forall_mem_cons.2 ⟨subd17_2_412, List.forall_mem_cons.2 ⟨subd17_2_413, List.forall_mem_cons.2 ⟨subd17_2_414, List.forall_mem_cons.2 ⟨subd17_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
