import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_1_0 : subd17_1 [-6] = true := by decide +kernel
theorem subd17_1_1 : subd17_1 [-5, -3] = true := by decide +kernel
theorem subd17_1_2 : subd17_1 [-5, -2] = true := by decide +kernel
theorem subd17_1_3 : subd17_1 [-5, -1] = true := by decide +kernel
theorem subd17_1_4 : subd17_1 [-5, 0] = true := by decide +kernel
theorem subd17_1_5 : subd17_1 [-5, 1] = true := by decide +kernel
theorem subd17_1_6 : subd17_1 [-5, 2] = true := by decide +kernel
theorem subd17_1_7 : subd17_1 [-5, 3] = true := by decide +kernel
theorem subd17_1_8 : subd17_1 [-5, 4] = true := by decide +kernel
theorem subd17_1_9 : subd17_1 [-5, 5] = true := by decide +kernel
theorem subd17_1_10 : subd17_1 [-4, -5] = true := by decide +kernel
theorem subd17_1_11 : subd17_1 [-4, -4] = true := by decide +kernel
theorem subd17_1_12 : subd17_1 [-4, -3] = true := by decide +kernel
theorem subd17_1_13 : subd17_1 [-4, -2] = true := by decide +kernel
theorem subd17_1_14 : subd17_1 [-4, -1, -8] = true := by decide +kernel
theorem subd17_1_15 : subd17_1 [-4, -1, -7] = true := by decide +kernel
theorem subd17_1_16 : subd17_1 [-4, -1, -6] = true := by decide +kernel
theorem subd17_1_17 : subd17_1 [-4, -1, -5] = true := by decide +kernel
theorem subd17_1_18 : subd17_1 [-4, -1, -4] = true := by decide +kernel
theorem subd17_1_19 : subd17_1 [-4, -1, -3] = true := by decide +kernel
theorem subd17_1_20 : subd17_1 [-4, -1, -2] = true := by decide +kernel
theorem subd17_1_21 : subd17_1 [-4, -1, -1] = true := by decide +kernel
theorem subd17_1_22 : subd17_1 [-4, -1, 0] = true := by decide +kernel
theorem subd17_1_23 : subd17_1 [-4, -1, 1] = true := by decide +kernel
theorem subd17_1_24 : subd17_1 [-4, -1, 2] = true := by decide +kernel
theorem subd17_1_25 : subd17_1 [-4, -1, 3] = true := by decide +kernel
theorem subd17_1_26 : subd17_1 [-4, -1, 4] = true := by decide +kernel
theorem subd17_1_27 : subd17_1 [-4, 0, -8] = true := by decide +kernel
theorem subd17_1_28 : subd17_1 [-4, 0, -7] = true := by decide +kernel
theorem subd17_1_29 : subd17_1 [-4, 0, -6] = true := by decide +kernel
theorem subd17_1_30 : subd17_1 [-4, 0, -5] = true := by decide +kernel
theorem subd17_1_31 : subd17_1 [-4, 0, -4] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_cons.2 ⟨subd17_1_1, List.forall_mem_cons.2 ⟨subd17_1_2, List.forall_mem_cons.2 ⟨subd17_1_3, List.forall_mem_cons.2 ⟨subd17_1_4, List.forall_mem_cons.2 ⟨subd17_1_5, List.forall_mem_cons.2 ⟨subd17_1_6, List.forall_mem_cons.2 ⟨subd17_1_7, List.forall_mem_cons.2 ⟨subd17_1_8, List.forall_mem_cons.2 ⟨subd17_1_9, List.forall_mem_cons.2 ⟨subd17_1_10, List.forall_mem_cons.2 ⟨subd17_1_11, List.forall_mem_cons.2 ⟨subd17_1_12, List.forall_mem_cons.2 ⟨subd17_1_13, List.forall_mem_cons.2 ⟨subd17_1_14, List.forall_mem_cons.2 ⟨subd17_1_15, List.forall_mem_cons.2 ⟨subd17_1_16, List.forall_mem_cons.2 ⟨subd17_1_17, List.forall_mem_cons.2 ⟨subd17_1_18, List.forall_mem_cons.2 ⟨subd17_1_19, List.forall_mem_cons.2 ⟨subd17_1_20, List.forall_mem_cons.2 ⟨subd17_1_21, List.forall_mem_cons.2 ⟨subd17_1_22, List.forall_mem_cons.2 ⟨subd17_1_23, List.forall_mem_cons.2 ⟨subd17_1_24, List.forall_mem_cons.2 ⟨subd17_1_25, List.forall_mem_cons.2 ⟨subd17_1_26, List.forall_mem_cons.2 ⟨subd17_1_27, List.forall_mem_cons.2 ⟨subd17_1_28, List.forall_mem_cons.2 ⟨subd17_1_29, List.forall_mem_cons.2 ⟨subd17_1_30, List.forall_mem_cons.2 ⟨subd17_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_32 : subd17_1 [-4, 0, -3] = true := by decide +kernel
theorem subd17_1_33 : subd17_1 [-4, 0, -2] = true := by decide +kernel
theorem subd17_1_34 : subd17_1 [-4, 0, -1] = true := by decide +kernel
theorem subd17_1_35 : subd17_1 [-4, 0, 0] = true := by decide +kernel
theorem subd17_1_36 : subd17_1 [-4, 0, 1] = true := by decide +kernel
theorem subd17_1_37 : subd17_1 [-4, 0, 2] = true := by decide +kernel
theorem subd17_1_38 : subd17_1 [-4, 0, 3] = true := by decide +kernel
theorem subd17_1_39 : subd17_1 [-4, 0, 4] = true := by decide +kernel
theorem subd17_1_40 : subd17_1 [-4, 0, 5] = true := by decide +kernel
theorem subd17_1_41 : subd17_1 [-4, 1, -9] = true := by decide +kernel
theorem subd17_1_42 : subd17_1 [-4, 1, -8] = true := by decide +kernel
theorem subd17_1_43 : subd17_1 [-4, 1, -7] = true := by decide +kernel
theorem subd17_1_44 : subd17_1 [-4, 1, -6] = true := by decide +kernel
theorem subd17_1_45 : subd17_1 [-4, 1, -5] = true := by decide +kernel
theorem subd17_1_46 : subd17_1 [-4, 1, -4] = true := by decide +kernel
theorem subd17_1_47 : subd17_1 [-4, 1, -3] = true := by decide +kernel
theorem subd17_1_48 : subd17_1 [-4, 1, -2] = true := by decide +kernel
theorem subd17_1_49 : subd17_1 [-4, 1, -1] = true := by decide +kernel
theorem subd17_1_50 : subd17_1 [-4, 1, 0] = true := by decide +kernel
theorem subd17_1_51 : subd17_1 [-4, 1, 1] = true := by decide +kernel
theorem subd17_1_52 : subd17_1 [-4, 1, 2] = true := by decide +kernel
theorem subd17_1_53 : subd17_1 [-4, 1, 3] = true := by decide +kernel
theorem subd17_1_54 : subd17_1 [-4, 1, 4] = true := by decide +kernel
theorem subd17_1_55 : subd17_1 [-4, 1, 5] = true := by decide +kernel
theorem subd17_1_56 : subd17_1 [-4, 2, -8] = true := by decide +kernel
theorem subd17_1_57 : subd17_1 [-4, 2, -7] = true := by decide +kernel
theorem subd17_1_58 : subd17_1 [-4, 2, -6] = true := by decide +kernel
theorem subd17_1_59 : subd17_1 [-4, 2, -5] = true := by decide +kernel
theorem subd17_1_60 : subd17_1 [-4, 2, -4] = true := by decide +kernel
theorem subd17_1_61 : subd17_1 [-4, 2, -3] = true := by decide +kernel
theorem subd17_1_62 : subd17_1 [-4, 2, -2] = true := by decide +kernel
theorem subd17_1_63 : subd17_1 [-4, 2, -1] = true := by decide +kernel
theorem sbd17_1_1 : ∀ q ∈ blkd17_1_1, subd17_1 q = true := by
  unfold blkd17_1_1
  exact List.forall_mem_cons.2 ⟨subd17_1_32, List.forall_mem_cons.2 ⟨subd17_1_33, List.forall_mem_cons.2 ⟨subd17_1_34, List.forall_mem_cons.2 ⟨subd17_1_35, List.forall_mem_cons.2 ⟨subd17_1_36, List.forall_mem_cons.2 ⟨subd17_1_37, List.forall_mem_cons.2 ⟨subd17_1_38, List.forall_mem_cons.2 ⟨subd17_1_39, List.forall_mem_cons.2 ⟨subd17_1_40, List.forall_mem_cons.2 ⟨subd17_1_41, List.forall_mem_cons.2 ⟨subd17_1_42, List.forall_mem_cons.2 ⟨subd17_1_43, List.forall_mem_cons.2 ⟨subd17_1_44, List.forall_mem_cons.2 ⟨subd17_1_45, List.forall_mem_cons.2 ⟨subd17_1_46, List.forall_mem_cons.2 ⟨subd17_1_47, List.forall_mem_cons.2 ⟨subd17_1_48, List.forall_mem_cons.2 ⟨subd17_1_49, List.forall_mem_cons.2 ⟨subd17_1_50, List.forall_mem_cons.2 ⟨subd17_1_51, List.forall_mem_cons.2 ⟨subd17_1_52, List.forall_mem_cons.2 ⟨subd17_1_53, List.forall_mem_cons.2 ⟨subd17_1_54, List.forall_mem_cons.2 ⟨subd17_1_55, List.forall_mem_cons.2 ⟨subd17_1_56, List.forall_mem_cons.2 ⟨subd17_1_57, List.forall_mem_cons.2 ⟨subd17_1_58, List.forall_mem_cons.2 ⟨subd17_1_59, List.forall_mem_cons.2 ⟨subd17_1_60, List.forall_mem_cons.2 ⟨subd17_1_61, List.forall_mem_cons.2 ⟨subd17_1_62, List.forall_mem_cons.2 ⟨subd17_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_64 : subd17_1 [-4, 2, 0] = true := by decide +kernel
theorem subd17_1_65 : subd17_1 [-4, 2, 1] = true := by decide +kernel
theorem subd17_1_66 : subd17_1 [-4, 2, 2] = true := by decide +kernel
theorem subd17_1_67 : subd17_1 [-4, 2, 3] = true := by decide +kernel
theorem subd17_1_68 : subd17_1 [-4, 2, 4] = true := by decide +kernel
theorem subd17_1_69 : subd17_1 [-4, 2, 5] = true := by decide +kernel
theorem subd17_1_70 : subd17_1 [-4, 3, -8] = true := by decide +kernel
theorem subd17_1_71 : subd17_1 [-4, 3, -7] = true := by decide +kernel
theorem subd17_1_72 : subd17_1 [-4, 3, -6] = true := by decide +kernel
theorem subd17_1_73 : subd17_1 [-4, 3, -5] = true := by decide +kernel
theorem subd17_1_74 : subd17_1 [-4, 3, -4] = true := by decide +kernel
theorem subd17_1_75 : subd17_1 [-4, 3, -3] = true := by decide +kernel
theorem subd17_1_76 : subd17_1 [-4, 3, -2] = true := by decide +kernel
theorem subd17_1_77 : subd17_1 [-4, 3, -1] = true := by decide +kernel
theorem subd17_1_78 : subd17_1 [-4, 3, 0] = true := by decide +kernel
theorem subd17_1_79 : subd17_1 [-4, 3, 1] = true := by decide +kernel
theorem subd17_1_80 : subd17_1 [-4, 3, 2] = true := by decide +kernel
theorem subd17_1_81 : subd17_1 [-4, 3, 3] = true := by decide +kernel
theorem subd17_1_82 : subd17_1 [-4, 3, 4] = true := by decide +kernel
theorem subd17_1_83 : subd17_1 [-4, 3, 5] = true := by decide +kernel
theorem subd17_1_84 : subd17_1 [-4, 4] = true := by decide +kernel
theorem subd17_1_85 : subd17_1 [-4, 5] = true := by decide +kernel
theorem subd17_1_86 : subd17_1 [-4, 6] = true := by decide +kernel
theorem subd17_1_87 : subd17_1 [-3, -6] = true := by decide +kernel
theorem subd17_1_88 : subd17_1 [-3, -5] = true := by decide +kernel
theorem subd17_1_89 : subd17_1 [-3, -4] = true := by decide +kernel
theorem subd17_1_90 : subd17_1 [-3, -3] = true := by decide +kernel
theorem subd17_1_91 : subd17_1 [-3, -2, -8] = true := by decide +kernel
theorem subd17_1_92 : subd17_1 [-3, -2, -7] = true := by decide +kernel
theorem subd17_1_93 : subd17_1 [-3, -2, -6] = true := by decide +kernel
theorem subd17_1_94 : subd17_1 [-3, -2, -5] = true := by decide +kernel
theorem subd17_1_95 : subd17_1 [-3, -2, -4] = true := by decide +kernel
theorem sbd17_1_2 : ∀ q ∈ blkd17_1_2, subd17_1 q = true := by
  unfold blkd17_1_2
  exact List.forall_mem_cons.2 ⟨subd17_1_64, List.forall_mem_cons.2 ⟨subd17_1_65, List.forall_mem_cons.2 ⟨subd17_1_66, List.forall_mem_cons.2 ⟨subd17_1_67, List.forall_mem_cons.2 ⟨subd17_1_68, List.forall_mem_cons.2 ⟨subd17_1_69, List.forall_mem_cons.2 ⟨subd17_1_70, List.forall_mem_cons.2 ⟨subd17_1_71, List.forall_mem_cons.2 ⟨subd17_1_72, List.forall_mem_cons.2 ⟨subd17_1_73, List.forall_mem_cons.2 ⟨subd17_1_74, List.forall_mem_cons.2 ⟨subd17_1_75, List.forall_mem_cons.2 ⟨subd17_1_76, List.forall_mem_cons.2 ⟨subd17_1_77, List.forall_mem_cons.2 ⟨subd17_1_78, List.forall_mem_cons.2 ⟨subd17_1_79, List.forall_mem_cons.2 ⟨subd17_1_80, List.forall_mem_cons.2 ⟨subd17_1_81, List.forall_mem_cons.2 ⟨subd17_1_82, List.forall_mem_cons.2 ⟨subd17_1_83, List.forall_mem_cons.2 ⟨subd17_1_84, List.forall_mem_cons.2 ⟨subd17_1_85, List.forall_mem_cons.2 ⟨subd17_1_86, List.forall_mem_cons.2 ⟨subd17_1_87, List.forall_mem_cons.2 ⟨subd17_1_88, List.forall_mem_cons.2 ⟨subd17_1_89, List.forall_mem_cons.2 ⟨subd17_1_90, List.forall_mem_cons.2 ⟨subd17_1_91, List.forall_mem_cons.2 ⟨subd17_1_92, List.forall_mem_cons.2 ⟨subd17_1_93, List.forall_mem_cons.2 ⟨subd17_1_94, List.forall_mem_cons.2 ⟨subd17_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_96 : subd17_1 [-3, -2, -3] = true := by decide +kernel
theorem subd17_1_97 : subd17_1 [-3, -2, -2] = true := by decide +kernel
theorem subd17_1_98 : subd17_1 [-3, -2, -1] = true := by decide +kernel
theorem subd17_1_99 : subd17_1 [-3, -2, 0] = true := by decide +kernel
theorem subd17_1_100 : subd17_1 [-3, -2, 1] = true := by decide +kernel
theorem subd17_1_101 : subd17_1 [-3, -2, 2] = true := by decide +kernel
theorem subd17_1_102 : subd17_1 [-3, -2, 3] = true := by decide +kernel
theorem subd17_1_103 : subd17_1 [-3, -2, 4] = true := by decide +kernel
theorem subd17_1_104 : subd17_1 [-3, -2, 5] = true := by decide +kernel
theorem subd17_1_105 : subd17_1 [-3, -1, -9] = true := by decide +kernel
theorem subd17_1_106 : subd17_1 [-3, -1, -8] = true := by decide +kernel
theorem subd17_1_107 : subd17_1 [-3, -1, -7] = true := by decide +kernel
theorem subd17_1_108 : subd17_1 [-3, -1, -6] = true := by decide +kernel
theorem subd17_1_109 : subd17_1 [-3, -1, -5] = true := by decide +kernel
theorem subd17_1_110 : subd17_1 [-3, -1, -4] = true := by decide +kernel
theorem subd17_1_111 : subd17_1 [-3, -1, -3] = true := by decide +kernel
theorem subd17_1_112 : subd17_1 [-3, -1, -2] = true := by decide +kernel
theorem subd17_1_113 : subd17_1 [-3, -1, -1] = true := by decide +kernel
theorem subd17_1_114 : subd17_1 [-3, -1, 0] = true := by decide +kernel
theorem subd17_1_115 : subd17_1 [-3, -1, 1] = true := by decide +kernel
theorem subd17_1_116 : subd17_1 [-3, -1, 2] = true := by decide +kernel
theorem subd17_1_117 : subd17_1 [-3, -1, 3] = true := by decide +kernel
theorem subd17_1_118 : subd17_1 [-3, -1, 4] = true := by decide +kernel
theorem subd17_1_119 : subd17_1 [-3, -1, 5] = true := by decide +kernel
theorem subd17_1_120 : subd17_1 [-3, -1, 6] = true := by decide +kernel
theorem subd17_1_121 : subd17_1 [-3, 0, -9] = true := by decide +kernel
theorem subd17_1_122 : subd17_1 [-3, 0, -8] = true := by decide +kernel
theorem subd17_1_123 : subd17_1 [-3, 0, -7] = true := by decide +kernel
theorem subd17_1_124 : subd17_1 [-3, 0, -6] = true := by decide +kernel
theorem subd17_1_125 : subd17_1 [-3, 0, -5] = true := by decide +kernel
theorem subd17_1_126 : subd17_1 [-3, 0, -4] = true := by decide +kernel
theorem subd17_1_127 : subd17_1 [-3, 0, -3] = true := by decide +kernel
theorem sbd17_1_3 : ∀ q ∈ blkd17_1_3, subd17_1 q = true := by
  unfold blkd17_1_3
  exact List.forall_mem_cons.2 ⟨subd17_1_96, List.forall_mem_cons.2 ⟨subd17_1_97, List.forall_mem_cons.2 ⟨subd17_1_98, List.forall_mem_cons.2 ⟨subd17_1_99, List.forall_mem_cons.2 ⟨subd17_1_100, List.forall_mem_cons.2 ⟨subd17_1_101, List.forall_mem_cons.2 ⟨subd17_1_102, List.forall_mem_cons.2 ⟨subd17_1_103, List.forall_mem_cons.2 ⟨subd17_1_104, List.forall_mem_cons.2 ⟨subd17_1_105, List.forall_mem_cons.2 ⟨subd17_1_106, List.forall_mem_cons.2 ⟨subd17_1_107, List.forall_mem_cons.2 ⟨subd17_1_108, List.forall_mem_cons.2 ⟨subd17_1_109, List.forall_mem_cons.2 ⟨subd17_1_110, List.forall_mem_cons.2 ⟨subd17_1_111, List.forall_mem_cons.2 ⟨subd17_1_112, List.forall_mem_cons.2 ⟨subd17_1_113, List.forall_mem_cons.2 ⟨subd17_1_114, List.forall_mem_cons.2 ⟨subd17_1_115, List.forall_mem_cons.2 ⟨subd17_1_116, List.forall_mem_cons.2 ⟨subd17_1_117, List.forall_mem_cons.2 ⟨subd17_1_118, List.forall_mem_cons.2 ⟨subd17_1_119, List.forall_mem_cons.2 ⟨subd17_1_120, List.forall_mem_cons.2 ⟨subd17_1_121, List.forall_mem_cons.2 ⟨subd17_1_122, List.forall_mem_cons.2 ⟨subd17_1_123, List.forall_mem_cons.2 ⟨subd17_1_124, List.forall_mem_cons.2 ⟨subd17_1_125, List.forall_mem_cons.2 ⟨subd17_1_126, List.forall_mem_cons.2 ⟨subd17_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_128 : subd17_1 [-3, 0, -2] = true := by decide +kernel
theorem subd17_1_129 : subd17_1 [-3, 0, -1] = true := by decide +kernel
theorem subd17_1_130 : subd17_1 [-3, 0, 0] = true := by decide +kernel
theorem subd17_1_131 : subd17_1 [-3, 0, 1] = true := by decide +kernel
theorem subd17_1_132 : subd17_1 [-3, 0, 2] = true := by decide +kernel
theorem subd17_1_133 : subd17_1 [-3, 0, 3] = true := by decide +kernel
theorem subd17_1_134 : subd17_1 [-3, 0, 4] = true := by decide +kernel
theorem subd17_1_135 : subd17_1 [-3, 0, 5] = true := by decide +kernel
theorem subd17_1_136 : subd17_1 [-3, 0, 6] = true := by decide +kernel
theorem subd17_1_137 : subd17_1 [-3, 1, -9] = true := by decide +kernel
theorem subd17_1_138 : subd17_1 [-3, 1, -8] = true := by decide +kernel
theorem subd17_1_139 : subd17_1 [-3, 1, -7] = true := by decide +kernel
theorem subd17_1_140 : subd17_1 [-3, 1, -6] = true := by decide +kernel
theorem subd17_1_141 : subd17_1 [-3, 1, -5] = true := by decide +kernel
theorem subd17_1_142 : subd17_1 [-3, 1, -4] = true := by decide +kernel
theorem subd17_1_143 : subd17_1 [-3, 1, -3] = true := by decide +kernel
theorem subd17_1_144 : subd17_1 [-3, 1, -2] = true := by decide +kernel
theorem subd17_1_145 : subd17_1 [-3, 1, -1] = true := by decide +kernel
theorem subd17_1_146 : subd17_1 [-3, 1, 0] = true := by decide +kernel
theorem subd17_1_147 : subd17_1 [-3, 1, 1] = true := by decide +kernel
theorem subd17_1_148 : subd17_1 [-3, 1, 2] = true := by decide +kernel
theorem subd17_1_149 : subd17_1 [-3, 1, 3] = true := by decide +kernel
theorem subd17_1_150 : subd17_1 [-3, 1, 4] = true := by decide +kernel
theorem subd17_1_151 : subd17_1 [-3, 1, 5] = true := by decide +kernel
theorem subd17_1_152 : subd17_1 [-3, 1, 6] = true := by decide +kernel
theorem subd17_1_153 : subd17_1 [-3, 2, -9] = true := by decide +kernel
theorem subd17_1_154 : subd17_1 [-3, 2, -8] = true := by decide +kernel
theorem subd17_1_155 : subd17_1 [-3, 2, -7] = true := by decide +kernel
theorem subd17_1_156 : subd17_1 [-3, 2, -6] = true := by decide +kernel
theorem subd17_1_157 : subd17_1 [-3, 2, -5] = true := by decide +kernel
theorem subd17_1_158 : subd17_1 [-3, 2, -4] = true := by decide +kernel
theorem subd17_1_159 : subd17_1 [-3, 2, -3] = true := by decide +kernel
theorem sbd17_1_4 : ∀ q ∈ blkd17_1_4, subd17_1 q = true := by
  unfold blkd17_1_4
  exact List.forall_mem_cons.2 ⟨subd17_1_128, List.forall_mem_cons.2 ⟨subd17_1_129, List.forall_mem_cons.2 ⟨subd17_1_130, List.forall_mem_cons.2 ⟨subd17_1_131, List.forall_mem_cons.2 ⟨subd17_1_132, List.forall_mem_cons.2 ⟨subd17_1_133, List.forall_mem_cons.2 ⟨subd17_1_134, List.forall_mem_cons.2 ⟨subd17_1_135, List.forall_mem_cons.2 ⟨subd17_1_136, List.forall_mem_cons.2 ⟨subd17_1_137, List.forall_mem_cons.2 ⟨subd17_1_138, List.forall_mem_cons.2 ⟨subd17_1_139, List.forall_mem_cons.2 ⟨subd17_1_140, List.forall_mem_cons.2 ⟨subd17_1_141, List.forall_mem_cons.2 ⟨subd17_1_142, List.forall_mem_cons.2 ⟨subd17_1_143, List.forall_mem_cons.2 ⟨subd17_1_144, List.forall_mem_cons.2 ⟨subd17_1_145, List.forall_mem_cons.2 ⟨subd17_1_146, List.forall_mem_cons.2 ⟨subd17_1_147, List.forall_mem_cons.2 ⟨subd17_1_148, List.forall_mem_cons.2 ⟨subd17_1_149, List.forall_mem_cons.2 ⟨subd17_1_150, List.forall_mem_cons.2 ⟨subd17_1_151, List.forall_mem_cons.2 ⟨subd17_1_152, List.forall_mem_cons.2 ⟨subd17_1_153, List.forall_mem_cons.2 ⟨subd17_1_154, List.forall_mem_cons.2 ⟨subd17_1_155, List.forall_mem_cons.2 ⟨subd17_1_156, List.forall_mem_cons.2 ⟨subd17_1_157, List.forall_mem_cons.2 ⟨subd17_1_158, List.forall_mem_cons.2 ⟨subd17_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_160 : subd17_1 [-3, 2, -2] = true := by decide +kernel
theorem subd17_1_161 : subd17_1 [-3, 2, -1] = true := by decide +kernel
theorem subd17_1_162 : subd17_1 [-3, 2, 0] = true := by decide +kernel
theorem subd17_1_163 : subd17_1 [-3, 2, 1] = true := by decide +kernel
theorem subd17_1_164 : subd17_1 [-3, 2, 2] = true := by decide +kernel
theorem subd17_1_165 : subd17_1 [-3, 2, 3] = true := by decide +kernel
theorem subd17_1_166 : subd17_1 [-3, 2, 4] = true := by decide +kernel
theorem subd17_1_167 : subd17_1 [-3, 2, 5] = true := by decide +kernel
theorem subd17_1_168 : subd17_1 [-3, 2, 6] = true := by decide +kernel
theorem subd17_1_169 : subd17_1 [-3, 3, -9] = true := by decide +kernel
theorem subd17_1_170 : subd17_1 [-3, 3, -8] = true := by decide +kernel
theorem subd17_1_171 : subd17_1 [-3, 3, -7] = true := by decide +kernel
theorem subd17_1_172 : subd17_1 [-3, 3, -6] = true := by decide +kernel
theorem subd17_1_173 : subd17_1 [-3, 3, -5] = true := by decide +kernel
theorem subd17_1_174 : subd17_1 [-3, 3, -4] = true := by decide +kernel
theorem subd17_1_175 : subd17_1 [-3, 3, -3] = true := by decide +kernel
theorem subd17_1_176 : subd17_1 [-3, 3, -2] = true := by decide +kernel
theorem subd17_1_177 : subd17_1 [-3, 3, -1] = true := by decide +kernel
theorem subd17_1_178 : subd17_1 [-3, 3, 0] = true := by decide +kernel
theorem subd17_1_179 : subd17_1 [-3, 3, 1] = true := by decide +kernel
theorem subd17_1_180 : subd17_1 [-3, 3, 2] = true := by decide +kernel
theorem subd17_1_181 : subd17_1 [-3, 3, 3] = true := by decide +kernel
theorem subd17_1_182 : subd17_1 [-3, 3, 4] = true := by decide +kernel
theorem subd17_1_183 : subd17_1 [-3, 3, 5] = true := by decide +kernel
theorem subd17_1_184 : subd17_1 [-3, 3, 6] = true := by decide +kernel
theorem subd17_1_185 : subd17_1 [-3, 4, -8] = true := by decide +kernel
theorem subd17_1_186 : subd17_1 [-3, 4, -7] = true := by decide +kernel
theorem subd17_1_187 : subd17_1 [-3, 4, -6] = true := by decide +kernel
theorem subd17_1_188 : subd17_1 [-3, 4, -5] = true := by decide +kernel
theorem subd17_1_189 : subd17_1 [-3, 4, -4] = true := by decide +kernel
theorem subd17_1_190 : subd17_1 [-3, 4, -3] = true := by decide +kernel
theorem subd17_1_191 : subd17_1 [-3, 4, -2] = true := by decide +kernel
theorem sbd17_1_5 : ∀ q ∈ blkd17_1_5, subd17_1 q = true := by
  unfold blkd17_1_5
  exact List.forall_mem_cons.2 ⟨subd17_1_160, List.forall_mem_cons.2 ⟨subd17_1_161, List.forall_mem_cons.2 ⟨subd17_1_162, List.forall_mem_cons.2 ⟨subd17_1_163, List.forall_mem_cons.2 ⟨subd17_1_164, List.forall_mem_cons.2 ⟨subd17_1_165, List.forall_mem_cons.2 ⟨subd17_1_166, List.forall_mem_cons.2 ⟨subd17_1_167, List.forall_mem_cons.2 ⟨subd17_1_168, List.forall_mem_cons.2 ⟨subd17_1_169, List.forall_mem_cons.2 ⟨subd17_1_170, List.forall_mem_cons.2 ⟨subd17_1_171, List.forall_mem_cons.2 ⟨subd17_1_172, List.forall_mem_cons.2 ⟨subd17_1_173, List.forall_mem_cons.2 ⟨subd17_1_174, List.forall_mem_cons.2 ⟨subd17_1_175, List.forall_mem_cons.2 ⟨subd17_1_176, List.forall_mem_cons.2 ⟨subd17_1_177, List.forall_mem_cons.2 ⟨subd17_1_178, List.forall_mem_cons.2 ⟨subd17_1_179, List.forall_mem_cons.2 ⟨subd17_1_180, List.forall_mem_cons.2 ⟨subd17_1_181, List.forall_mem_cons.2 ⟨subd17_1_182, List.forall_mem_cons.2 ⟨subd17_1_183, List.forall_mem_cons.2 ⟨subd17_1_184, List.forall_mem_cons.2 ⟨subd17_1_185, List.forall_mem_cons.2 ⟨subd17_1_186, List.forall_mem_cons.2 ⟨subd17_1_187, List.forall_mem_cons.2 ⟨subd17_1_188, List.forall_mem_cons.2 ⟨subd17_1_189, List.forall_mem_cons.2 ⟨subd17_1_190, List.forall_mem_cons.2 ⟨subd17_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_192 : subd17_1 [-3, 4, -1] = true := by decide +kernel
theorem subd17_1_193 : subd17_1 [-3, 4, 0] = true := by decide +kernel
theorem subd17_1_194 : subd17_1 [-3, 4, 1] = true := by decide +kernel
theorem subd17_1_195 : subd17_1 [-3, 4, 2] = true := by decide +kernel
theorem subd17_1_196 : subd17_1 [-3, 4, 3] = true := by decide +kernel
theorem subd17_1_197 : subd17_1 [-3, 4, 4] = true := by decide +kernel
theorem subd17_1_198 : subd17_1 [-3, 4, 5] = true := by decide +kernel
theorem subd17_1_199 : subd17_1 [-3, 5] = true := by decide +kernel
theorem subd17_1_200 : subd17_1 [-3, 6] = true := by decide +kernel
theorem subd17_1_201 : subd17_1 [-2, -6] = true := by decide +kernel
theorem subd17_1_202 : subd17_1 [-2, -5] = true := by decide +kernel
theorem subd17_1_203 : subd17_1 [-2, -4] = true := by decide +kernel
theorem subd17_1_204 : subd17_1 [-2, -3, -8] = true := by decide +kernel
theorem subd17_1_205 : subd17_1 [-2, -3, -7] = true := by decide +kernel
theorem subd17_1_206 : subd17_1 [-2, -3, -6] = true := by decide +kernel
theorem subd17_1_207 : subd17_1 [-2, -3, -5] = true := by decide +kernel
theorem subd17_1_208 : subd17_1 [-2, -3, -4] = true := by decide +kernel
theorem subd17_1_209 : subd17_1 [-2, -3, -3] = true := by decide +kernel
theorem subd17_1_210 : subd17_1 [-2, -3, -2] = true := by decide +kernel
theorem subd17_1_211 : subd17_1 [-2, -3, -1] = true := by decide +kernel
theorem subd17_1_212 : subd17_1 [-2, -3, 0] = true := by decide +kernel
theorem subd17_1_213 : subd17_1 [-2, -3, 1] = true := by decide +kernel
theorem subd17_1_214 : subd17_1 [-2, -3, 2] = true := by decide +kernel
theorem subd17_1_215 : subd17_1 [-2, -3, 3] = true := by decide +kernel
theorem subd17_1_216 : subd17_1 [-2, -3, 4] = true := by decide +kernel
theorem subd17_1_217 : subd17_1 [-2, -3, 5] = true := by decide +kernel
theorem subd17_1_218 : subd17_1 [-2, -3, 6] = true := by decide +kernel
theorem subd17_1_219 : subd17_1 [-2, -2, -9] = true := by decide +kernel
theorem subd17_1_220 : subd17_1 [-2, -2, -8] = true := by decide +kernel
theorem subd17_1_221 : subd17_1 [-2, -2, -7] = true := by decide +kernel
theorem subd17_1_222 : subd17_1 [-2, -2, -6] = true := by decide +kernel
theorem subd17_1_223 : subd17_1 [-2, -2, -5] = true := by decide +kernel
theorem sbd17_1_6 : ∀ q ∈ blkd17_1_6, subd17_1 q = true := by
  unfold blkd17_1_6
  exact List.forall_mem_cons.2 ⟨subd17_1_192, List.forall_mem_cons.2 ⟨subd17_1_193, List.forall_mem_cons.2 ⟨subd17_1_194, List.forall_mem_cons.2 ⟨subd17_1_195, List.forall_mem_cons.2 ⟨subd17_1_196, List.forall_mem_cons.2 ⟨subd17_1_197, List.forall_mem_cons.2 ⟨subd17_1_198, List.forall_mem_cons.2 ⟨subd17_1_199, List.forall_mem_cons.2 ⟨subd17_1_200, List.forall_mem_cons.2 ⟨subd17_1_201, List.forall_mem_cons.2 ⟨subd17_1_202, List.forall_mem_cons.2 ⟨subd17_1_203, List.forall_mem_cons.2 ⟨subd17_1_204, List.forall_mem_cons.2 ⟨subd17_1_205, List.forall_mem_cons.2 ⟨subd17_1_206, List.forall_mem_cons.2 ⟨subd17_1_207, List.forall_mem_cons.2 ⟨subd17_1_208, List.forall_mem_cons.2 ⟨subd17_1_209, List.forall_mem_cons.2 ⟨subd17_1_210, List.forall_mem_cons.2 ⟨subd17_1_211, List.forall_mem_cons.2 ⟨subd17_1_212, List.forall_mem_cons.2 ⟨subd17_1_213, List.forall_mem_cons.2 ⟨subd17_1_214, List.forall_mem_cons.2 ⟨subd17_1_215, List.forall_mem_cons.2 ⟨subd17_1_216, List.forall_mem_cons.2 ⟨subd17_1_217, List.forall_mem_cons.2 ⟨subd17_1_218, List.forall_mem_cons.2 ⟨subd17_1_219, List.forall_mem_cons.2 ⟨subd17_1_220, List.forall_mem_cons.2 ⟨subd17_1_221, List.forall_mem_cons.2 ⟨subd17_1_222, List.forall_mem_cons.2 ⟨subd17_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_224 : subd17_1 [-2, -2, -4] = true := by decide +kernel
theorem subd17_1_225 : subd17_1 [-2, -2, -3] = true := by decide +kernel
theorem subd17_1_226 : subd17_1 [-2, -2, -2] = true := by decide +kernel
theorem subd17_1_227 : subd17_1 [-2, -2, -1] = true := by decide +kernel
theorem subd17_1_228 : subd17_1 [-2, -2, 0] = true := by decide +kernel
theorem subd17_1_229 : subd17_1 [-2, -2, 1] = true := by decide +kernel
theorem subd17_1_230 : subd17_1 [-2, -2, 2] = true := by decide +kernel
theorem subd17_1_231 : subd17_1 [-2, -2, 3] = true := by decide +kernel
theorem subd17_1_232 : subd17_1 [-2, -2, 4] = true := by decide +kernel
theorem subd17_1_233 : subd17_1 [-2, -2, 5] = true := by decide +kernel
theorem subd17_1_234 : subd17_1 [-2, -2, 6] = true := by decide +kernel
theorem subd17_1_235 : subd17_1 [-2, -2, 7] = true := by decide +kernel
theorem subd17_1_236 : subd17_1 [-2, -1, -9] = true := by decide +kernel
theorem subd17_1_237 : subd17_1 [-2, -1, -8] = true := by decide +kernel
theorem subd17_1_238 : subd17_1 [-2, -1, -7] = true := by decide +kernel
theorem subd17_1_239 : subd17_1 [-2, -1, -6] = true := by decide +kernel
theorem subd17_1_240 : subd17_1 [-2, -1, -5] = true := by decide +kernel
theorem subd17_1_241 : subd17_1 [-2, -1, -4] = true := by decide +kernel
theorem subd17_1_242 : subd17_1 [-2, -1, -3] = true := by decide +kernel
theorem subd17_1_243 : subd17_1 [-2, -1, -2] = true := by decide +kernel
theorem subd17_1_244 : subd17_1 [-2, -1, -1] = true := by decide +kernel
theorem subd17_1_245 : subd17_1 [-2, -1, 0] = true := by decide +kernel
theorem subd17_1_246 : subd17_1 [-2, -1, 1] = true := by decide +kernel
theorem subd17_1_247 : subd17_1 [-2, -1, 2] = true := by decide +kernel
theorem subd17_1_248 : subd17_1 [-2, -1, 3] = true := by decide +kernel
theorem subd17_1_249 : subd17_1 [-2, -1, 4] = true := by decide +kernel
theorem subd17_1_250 : subd17_1 [-2, -1, 5] = true := by decide +kernel
theorem subd17_1_251 : subd17_1 [-2, -1, 6] = true := by decide +kernel
theorem subd17_1_252 : subd17_1 [-2, -1, 7] = true := by decide +kernel
theorem subd17_1_253 : subd17_1 [-2, 0, -9] = true := by decide +kernel
theorem subd17_1_254 : subd17_1 [-2, 0, -8] = true := by decide +kernel
theorem subd17_1_255 : subd17_1 [-2, 0, -7] = true := by decide +kernel
theorem sbd17_1_7 : ∀ q ∈ blkd17_1_7, subd17_1 q = true := by
  unfold blkd17_1_7
  exact List.forall_mem_cons.2 ⟨subd17_1_224, List.forall_mem_cons.2 ⟨subd17_1_225, List.forall_mem_cons.2 ⟨subd17_1_226, List.forall_mem_cons.2 ⟨subd17_1_227, List.forall_mem_cons.2 ⟨subd17_1_228, List.forall_mem_cons.2 ⟨subd17_1_229, List.forall_mem_cons.2 ⟨subd17_1_230, List.forall_mem_cons.2 ⟨subd17_1_231, List.forall_mem_cons.2 ⟨subd17_1_232, List.forall_mem_cons.2 ⟨subd17_1_233, List.forall_mem_cons.2 ⟨subd17_1_234, List.forall_mem_cons.2 ⟨subd17_1_235, List.forall_mem_cons.2 ⟨subd17_1_236, List.forall_mem_cons.2 ⟨subd17_1_237, List.forall_mem_cons.2 ⟨subd17_1_238, List.forall_mem_cons.2 ⟨subd17_1_239, List.forall_mem_cons.2 ⟨subd17_1_240, List.forall_mem_cons.2 ⟨subd17_1_241, List.forall_mem_cons.2 ⟨subd17_1_242, List.forall_mem_cons.2 ⟨subd17_1_243, List.forall_mem_cons.2 ⟨subd17_1_244, List.forall_mem_cons.2 ⟨subd17_1_245, List.forall_mem_cons.2 ⟨subd17_1_246, List.forall_mem_cons.2 ⟨subd17_1_247, List.forall_mem_cons.2 ⟨subd17_1_248, List.forall_mem_cons.2 ⟨subd17_1_249, List.forall_mem_cons.2 ⟨subd17_1_250, List.forall_mem_cons.2 ⟨subd17_1_251, List.forall_mem_cons.2 ⟨subd17_1_252, List.forall_mem_cons.2 ⟨subd17_1_253, List.forall_mem_cons.2 ⟨subd17_1_254, List.forall_mem_cons.2 ⟨subd17_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_256 : subd17_1 [-2, 0, -6] = true := by decide +kernel
theorem subd17_1_257 : subd17_1 [-2, 0, -5] = true := by decide +kernel
theorem subd17_1_258 : subd17_1 [-2, 0, -4] = true := by decide +kernel
theorem subd17_1_259 : subd17_1 [-2, 0, -3] = true := by decide +kernel
theorem subd17_1_260 : subd17_1 [-2, 0, -2] = true := by decide +kernel
theorem subd17_1_261 : subd17_1 [-2, 0, -1] = true := by decide +kernel
theorem subd17_1_262 : subd17_1 [-2, 0, 0] = true := by decide +kernel
theorem subd17_1_263 : subd17_1 [-2, 0, 1] = true := by decide +kernel
theorem subd17_1_264 : subd17_1 [-2, 0, 2] = true := by decide +kernel
theorem subd17_1_265 : subd17_1 [-2, 0, 3] = true := by decide +kernel
theorem subd17_1_266 : subd17_1 [-2, 0, 4] = true := by decide +kernel
theorem subd17_1_267 : subd17_1 [-2, 0, 5] = true := by decide +kernel
theorem subd17_1_268 : subd17_1 [-2, 0, 6] = true := by decide +kernel
theorem subd17_1_269 : subd17_1 [-2, 0, 7] = true := by decide +kernel
theorem subd17_1_270 : subd17_1 [-2, 1, -10] = true := by decide +kernel
theorem subd17_1_271 : subd17_1 [-2, 1, -9] = true := by decide +kernel
theorem subd17_1_272 : subd17_1 [-2, 1, -8] = true := by decide +kernel
theorem subd17_1_273 : subd17_1 [-2, 1, -7] = true := by decide +kernel
theorem subd17_1_274 : subd17_1 [-2, 1, -6] = true := by decide +kernel
theorem subd17_1_275 : subd17_1 [-2, 1, -5] = true := by decide +kernel
theorem subd17_1_276 : subd17_1 [-2, 1, -4] = true := by decide +kernel
theorem subd17_1_277 : subd17_1 [-2, 1, -3] = true := by decide +kernel
theorem subd17_1_278 : subd17_1 [-2, 1, -2] = true := by decide +kernel
theorem subd17_1_279 : subd17_1 [-2, 1, -1] = true := by decide +kernel
theorem subd17_1_280 : subd17_1 [-2, 1, 0] = true := by decide +kernel
theorem subd17_1_281 : subd17_1 [-2, 1, 1] = true := by decide +kernel
theorem subd17_1_282 : subd17_1 [-2, 1, 2] = true := by decide +kernel
theorem subd17_1_283 : subd17_1 [-2, 1, 3] = true := by decide +kernel
theorem subd17_1_284 : subd17_1 [-2, 1, 4] = true := by decide +kernel
theorem subd17_1_285 : subd17_1 [-2, 1, 5] = true := by decide +kernel
theorem subd17_1_286 : subd17_1 [-2, 1, 6] = true := by decide +kernel
theorem subd17_1_287 : subd17_1 [-2, 1, 7] = true := by decide +kernel
theorem sbd17_1_8 : ∀ q ∈ blkd17_1_8, subd17_1 q = true := by
  unfold blkd17_1_8
  exact List.forall_mem_cons.2 ⟨subd17_1_256, List.forall_mem_cons.2 ⟨subd17_1_257, List.forall_mem_cons.2 ⟨subd17_1_258, List.forall_mem_cons.2 ⟨subd17_1_259, List.forall_mem_cons.2 ⟨subd17_1_260, List.forall_mem_cons.2 ⟨subd17_1_261, List.forall_mem_cons.2 ⟨subd17_1_262, List.forall_mem_cons.2 ⟨subd17_1_263, List.forall_mem_cons.2 ⟨subd17_1_264, List.forall_mem_cons.2 ⟨subd17_1_265, List.forall_mem_cons.2 ⟨subd17_1_266, List.forall_mem_cons.2 ⟨subd17_1_267, List.forall_mem_cons.2 ⟨subd17_1_268, List.forall_mem_cons.2 ⟨subd17_1_269, List.forall_mem_cons.2 ⟨subd17_1_270, List.forall_mem_cons.2 ⟨subd17_1_271, List.forall_mem_cons.2 ⟨subd17_1_272, List.forall_mem_cons.2 ⟨subd17_1_273, List.forall_mem_cons.2 ⟨subd17_1_274, List.forall_mem_cons.2 ⟨subd17_1_275, List.forall_mem_cons.2 ⟨subd17_1_276, List.forall_mem_cons.2 ⟨subd17_1_277, List.forall_mem_cons.2 ⟨subd17_1_278, List.forall_mem_cons.2 ⟨subd17_1_279, List.forall_mem_cons.2 ⟨subd17_1_280, List.forall_mem_cons.2 ⟨subd17_1_281, List.forall_mem_cons.2 ⟨subd17_1_282, List.forall_mem_cons.2 ⟨subd17_1_283, List.forall_mem_cons.2 ⟨subd17_1_284, List.forall_mem_cons.2 ⟨subd17_1_285, List.forall_mem_cons.2 ⟨subd17_1_286, List.forall_mem_cons.2 ⟨subd17_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_288 : subd17_1 [-2, 2, -9] = true := by decide +kernel
theorem subd17_1_289 : subd17_1 [-2, 2, -8] = true := by decide +kernel
theorem subd17_1_290 : subd17_1 [-2, 2, -7] = true := by decide +kernel
theorem subd17_1_291 : subd17_1 [-2, 2, -6] = true := by decide +kernel
theorem subd17_1_292 : subd17_1 [-2, 2, -5] = true := by decide +kernel
theorem subd17_1_293 : subd17_1 [-2, 2, -4] = true := by decide +kernel
theorem subd17_1_294 : subd17_1 [-2, 2, -3] = true := by decide +kernel
theorem subd17_1_295 : subd17_1 [-2, 2, -2] = true := by decide +kernel
theorem subd17_1_296 : subd17_1 [-2, 2, -1] = true := by decide +kernel
theorem subd17_1_297 : subd17_1 [-2, 2, 0] = true := by decide +kernel
theorem subd17_1_298 : subd17_1 [-2, 2, 1] = true := by decide +kernel
theorem subd17_1_299 : subd17_1 [-2, 2, 2] = true := by decide +kernel
theorem subd17_1_300 : subd17_1 [-2, 2, 3] = true := by decide +kernel
theorem subd17_1_301 : subd17_1 [-2, 2, 4] = true := by decide +kernel
theorem subd17_1_302 : subd17_1 [-2, 2, 5] = true := by decide +kernel
theorem subd17_1_303 : subd17_1 [-2, 2, 6] = true := by decide +kernel
theorem subd17_1_304 : subd17_1 [-2, 2, 7] = true := by decide +kernel
theorem subd17_1_305 : subd17_1 [-2, 3, -9] = true := by decide +kernel
theorem subd17_1_306 : subd17_1 [-2, 3, -8] = true := by decide +kernel
theorem subd17_1_307 : subd17_1 [-2, 3, -7] = true := by decide +kernel
theorem subd17_1_308 : subd17_1 [-2, 3, -6] = true := by decide +kernel
theorem subd17_1_309 : subd17_1 [-2, 3, -5] = true := by decide +kernel
theorem subd17_1_310 : subd17_1 [-2, 3, -4] = true := by decide +kernel
theorem subd17_1_311 : subd17_1 [-2, 3, -3] = true := by decide +kernel
theorem subd17_1_312 : subd17_1 [-2, 3, -2] = true := by decide +kernel
theorem subd17_1_313 : subd17_1 [-2, 3, -1] = true := by decide +kernel
theorem subd17_1_314 : subd17_1 [-2, 3, 0] = true := by decide +kernel
theorem subd17_1_315 : subd17_1 [-2, 3, 1] = true := by decide +kernel
theorem subd17_1_316 : subd17_1 [-2, 3, 2] = true := by decide +kernel
theorem subd17_1_317 : subd17_1 [-2, 3, 3] = true := by decide +kernel
theorem subd17_1_318 : subd17_1 [-2, 3, 4] = true := by decide +kernel
theorem subd17_1_319 : subd17_1 [-2, 3, 5] = true := by decide +kernel
theorem sbd17_1_9 : ∀ q ∈ blkd17_1_9, subd17_1 q = true := by
  unfold blkd17_1_9
  exact List.forall_mem_cons.2 ⟨subd17_1_288, List.forall_mem_cons.2 ⟨subd17_1_289, List.forall_mem_cons.2 ⟨subd17_1_290, List.forall_mem_cons.2 ⟨subd17_1_291, List.forall_mem_cons.2 ⟨subd17_1_292, List.forall_mem_cons.2 ⟨subd17_1_293, List.forall_mem_cons.2 ⟨subd17_1_294, List.forall_mem_cons.2 ⟨subd17_1_295, List.forall_mem_cons.2 ⟨subd17_1_296, List.forall_mem_cons.2 ⟨subd17_1_297, List.forall_mem_cons.2 ⟨subd17_1_298, List.forall_mem_cons.2 ⟨subd17_1_299, List.forall_mem_cons.2 ⟨subd17_1_300, List.forall_mem_cons.2 ⟨subd17_1_301, List.forall_mem_cons.2 ⟨subd17_1_302, List.forall_mem_cons.2 ⟨subd17_1_303, List.forall_mem_cons.2 ⟨subd17_1_304, List.forall_mem_cons.2 ⟨subd17_1_305, List.forall_mem_cons.2 ⟨subd17_1_306, List.forall_mem_cons.2 ⟨subd17_1_307, List.forall_mem_cons.2 ⟨subd17_1_308, List.forall_mem_cons.2 ⟨subd17_1_309, List.forall_mem_cons.2 ⟨subd17_1_310, List.forall_mem_cons.2 ⟨subd17_1_311, List.forall_mem_cons.2 ⟨subd17_1_312, List.forall_mem_cons.2 ⟨subd17_1_313, List.forall_mem_cons.2 ⟨subd17_1_314, List.forall_mem_cons.2 ⟨subd17_1_315, List.forall_mem_cons.2 ⟨subd17_1_316, List.forall_mem_cons.2 ⟨subd17_1_317, List.forall_mem_cons.2 ⟨subd17_1_318, List.forall_mem_cons.2 ⟨subd17_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_320 : subd17_1 [-2, 3, 6] = true := by decide +kernel
theorem subd17_1_321 : subd17_1 [-2, 3, 7] = true := by decide +kernel
theorem subd17_1_322 : subd17_1 [-2, 4, -8] = true := by decide +kernel
theorem subd17_1_323 : subd17_1 [-2, 4, -7] = true := by decide +kernel
theorem subd17_1_324 : subd17_1 [-2, 4, -6] = true := by decide +kernel
theorem subd17_1_325 : subd17_1 [-2, 4, -5] = true := by decide +kernel
theorem subd17_1_326 : subd17_1 [-2, 4, -4] = true := by decide +kernel
theorem subd17_1_327 : subd17_1 [-2, 4, -3] = true := by decide +kernel
theorem subd17_1_328 : subd17_1 [-2, 4, -2] = true := by decide +kernel
theorem subd17_1_329 : subd17_1 [-2, 4, -1] = true := by decide +kernel
theorem subd17_1_330 : subd17_1 [-2, 4, 0] = true := by decide +kernel
theorem subd17_1_331 : subd17_1 [-2, 4, 1] = true := by decide +kernel
theorem subd17_1_332 : subd17_1 [-2, 4, 2] = true := by decide +kernel
theorem subd17_1_333 : subd17_1 [-2, 4, 3] = true := by decide +kernel
theorem subd17_1_334 : subd17_1 [-2, 4, 4] = true := by decide +kernel
theorem subd17_1_335 : subd17_1 [-2, 4, 5] = true := by decide +kernel
theorem subd17_1_336 : subd17_1 [-2, 4, 6] = true := by decide +kernel
theorem subd17_1_337 : subd17_1 [-2, 5, -7] = true := by decide +kernel
theorem subd17_1_338 : subd17_1 [-2, 5, -6] = true := by decide +kernel
theorem subd17_1_339 : subd17_1 [-2, 5, -5] = true := by decide +kernel
theorem subd17_1_340 : subd17_1 [-2, 5, -4] = true := by decide +kernel
theorem subd17_1_341 : subd17_1 [-2, 5, -3] = true := by decide +kernel
theorem subd17_1_342 : subd17_1 [-2, 5, -2] = true := by decide +kernel
theorem subd17_1_343 : subd17_1 [-2, 5, -1] = true := by decide +kernel
theorem subd17_1_344 : subd17_1 [-2, 5, 0] = true := by decide +kernel
theorem subd17_1_345 : subd17_1 [-2, 5, 1] = true := by decide +kernel
theorem subd17_1_346 : subd17_1 [-2, 5, 2] = true := by decide +kernel
theorem subd17_1_347 : subd17_1 [-2, 5, 3] = true := by decide +kernel
theorem subd17_1_348 : subd17_1 [-2, 5, 4] = true := by decide +kernel
theorem subd17_1_349 : subd17_1 [-2, 5, 5] = true := by decide +kernel
theorem subd17_1_350 : subd17_1 [-2, 6] = true := by decide +kernel
theorem subd17_1_351 : subd17_1 [-2, 7] = true := by decide +kernel
theorem sbd17_1_10 : ∀ q ∈ blkd17_1_10, subd17_1 q = true := by
  unfold blkd17_1_10
  exact List.forall_mem_cons.2 ⟨subd17_1_320, List.forall_mem_cons.2 ⟨subd17_1_321, List.forall_mem_cons.2 ⟨subd17_1_322, List.forall_mem_cons.2 ⟨subd17_1_323, List.forall_mem_cons.2 ⟨subd17_1_324, List.forall_mem_cons.2 ⟨subd17_1_325, List.forall_mem_cons.2 ⟨subd17_1_326, List.forall_mem_cons.2 ⟨subd17_1_327, List.forall_mem_cons.2 ⟨subd17_1_328, List.forall_mem_cons.2 ⟨subd17_1_329, List.forall_mem_cons.2 ⟨subd17_1_330, List.forall_mem_cons.2 ⟨subd17_1_331, List.forall_mem_cons.2 ⟨subd17_1_332, List.forall_mem_cons.2 ⟨subd17_1_333, List.forall_mem_cons.2 ⟨subd17_1_334, List.forall_mem_cons.2 ⟨subd17_1_335, List.forall_mem_cons.2 ⟨subd17_1_336, List.forall_mem_cons.2 ⟨subd17_1_337, List.forall_mem_cons.2 ⟨subd17_1_338, List.forall_mem_cons.2 ⟨subd17_1_339, List.forall_mem_cons.2 ⟨subd17_1_340, List.forall_mem_cons.2 ⟨subd17_1_341, List.forall_mem_cons.2 ⟨subd17_1_342, List.forall_mem_cons.2 ⟨subd17_1_343, List.forall_mem_cons.2 ⟨subd17_1_344, List.forall_mem_cons.2 ⟨subd17_1_345, List.forall_mem_cons.2 ⟨subd17_1_346, List.forall_mem_cons.2 ⟨subd17_1_347, List.forall_mem_cons.2 ⟨subd17_1_348, List.forall_mem_cons.2 ⟨subd17_1_349, List.forall_mem_cons.2 ⟨subd17_1_350, List.forall_mem_cons.2 ⟨subd17_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_352 : subd17_1 [-1, -7] = true := by decide +kernel
theorem subd17_1_353 : subd17_1 [-1, -6] = true := by decide +kernel
theorem subd17_1_354 : subd17_1 [-1, -5] = true := by decide +kernel
theorem subd17_1_355 : subd17_1 [-1, -4, -8] = true := by decide +kernel
theorem subd17_1_356 : subd17_1 [-1, -4, -7] = true := by decide +kernel
theorem subd17_1_357 : subd17_1 [-1, -4, -6] = true := by decide +kernel
theorem subd17_1_358 : subd17_1 [-1, -4, -5] = true := by decide +kernel
theorem subd17_1_359 : subd17_1 [-1, -4, -4] = true := by decide +kernel
theorem subd17_1_360 : subd17_1 [-1, -4, -3] = true := by decide +kernel
theorem subd17_1_361 : subd17_1 [-1, -4, -2] = true := by decide +kernel
theorem subd17_1_362 : subd17_1 [-1, -4, -1] = true := by decide +kernel
theorem subd17_1_363 : subd17_1 [-1, -4, 0] = true := by decide +kernel
theorem subd17_1_364 : subd17_1 [-1, -4, 1] = true := by decide +kernel
theorem subd17_1_365 : subd17_1 [-1, -4, 2] = true := by decide +kernel
theorem subd17_1_366 : subd17_1 [-1, -4, 3] = true := by decide +kernel
theorem subd17_1_367 : subd17_1 [-1, -4, 4] = true := by decide +kernel
theorem subd17_1_368 : subd17_1 [-1, -4, 5] = true := by decide +kernel
theorem subd17_1_369 : subd17_1 [-1, -4, 6] = true := by decide +kernel
theorem subd17_1_370 : subd17_1 [-1, -3, -8] = true := by decide +kernel
theorem subd17_1_371 : subd17_1 [-1, -3, -7] = true := by decide +kernel
theorem subd17_1_372 : subd17_1 [-1, -3, -6] = true := by decide +kernel
theorem subd17_1_373 : subd17_1 [-1, -3, -5] = true := by decide +kernel
theorem subd17_1_374 : subd17_1 [-1, -3, -4] = true := by decide +kernel
theorem subd17_1_375 : subd17_1 [-1, -3, -3] = true := by decide +kernel
theorem subd17_1_376 : subd17_1 [-1, -3, -2] = true := by decide +kernel
theorem subd17_1_377 : subd17_1 [-1, -3, -1] = true := by decide +kernel
theorem subd17_1_378 : subd17_1 [-1, -3, 0] = true := by decide +kernel
theorem subd17_1_379 : subd17_1 [-1, -3, 1] = true := by decide +kernel
theorem subd17_1_380 : subd17_1 [-1, -3, 2] = true := by decide +kernel
theorem subd17_1_381 : subd17_1 [-1, -3, 3] = true := by decide +kernel
theorem subd17_1_382 : subd17_1 [-1, -3, 4] = true := by decide +kernel
theorem subd17_1_383 : subd17_1 [-1, -3, 5] = true := by decide +kernel
theorem sbd17_1_11 : ∀ q ∈ blkd17_1_11, subd17_1 q = true := by
  unfold blkd17_1_11
  exact List.forall_mem_cons.2 ⟨subd17_1_352, List.forall_mem_cons.2 ⟨subd17_1_353, List.forall_mem_cons.2 ⟨subd17_1_354, List.forall_mem_cons.2 ⟨subd17_1_355, List.forall_mem_cons.2 ⟨subd17_1_356, List.forall_mem_cons.2 ⟨subd17_1_357, List.forall_mem_cons.2 ⟨subd17_1_358, List.forall_mem_cons.2 ⟨subd17_1_359, List.forall_mem_cons.2 ⟨subd17_1_360, List.forall_mem_cons.2 ⟨subd17_1_361, List.forall_mem_cons.2 ⟨subd17_1_362, List.forall_mem_cons.2 ⟨subd17_1_363, List.forall_mem_cons.2 ⟨subd17_1_364, List.forall_mem_cons.2 ⟨subd17_1_365, List.forall_mem_cons.2 ⟨subd17_1_366, List.forall_mem_cons.2 ⟨subd17_1_367, List.forall_mem_cons.2 ⟨subd17_1_368, List.forall_mem_cons.2 ⟨subd17_1_369, List.forall_mem_cons.2 ⟨subd17_1_370, List.forall_mem_cons.2 ⟨subd17_1_371, List.forall_mem_cons.2 ⟨subd17_1_372, List.forall_mem_cons.2 ⟨subd17_1_373, List.forall_mem_cons.2 ⟨subd17_1_374, List.forall_mem_cons.2 ⟨subd17_1_375, List.forall_mem_cons.2 ⟨subd17_1_376, List.forall_mem_cons.2 ⟨subd17_1_377, List.forall_mem_cons.2 ⟨subd17_1_378, List.forall_mem_cons.2 ⟨subd17_1_379, List.forall_mem_cons.2 ⟨subd17_1_380, List.forall_mem_cons.2 ⟨subd17_1_381, List.forall_mem_cons.2 ⟨subd17_1_382, List.forall_mem_cons.2 ⟨subd17_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_384 : subd17_1 [-1, -3, 6] = true := by decide +kernel
theorem subd17_1_385 : subd17_1 [-1, -3, 7] = true := by decide +kernel
theorem subd17_1_386 : subd17_1 [-1, -2, -9] = true := by decide +kernel
theorem subd17_1_387 : subd17_1 [-1, -2, -8] = true := by decide +kernel
theorem subd17_1_388 : subd17_1 [-1, -2, -7] = true := by decide +kernel
theorem subd17_1_389 : subd17_1 [-1, -2, -6] = true := by decide +kernel
theorem subd17_1_390 : subd17_1 [-1, -2, -5] = true := by decide +kernel
theorem subd17_1_391 : subd17_1 [-1, -2, -4] = true := by decide +kernel
theorem subd17_1_392 : subd17_1 [-1, -2, -3] = true := by decide +kernel
theorem subd17_1_393 : subd17_1 [-1, -2, -2] = true := by decide +kernel
theorem subd17_1_394 : subd17_1 [-1, -2, -1] = true := by decide +kernel
theorem subd17_1_395 : subd17_1 [-1, -2, 0] = true := by decide +kernel
theorem subd17_1_396 : subd17_1 [-1, -2, 1] = true := by decide +kernel
theorem subd17_1_397 : subd17_1 [-1, -2, 2] = true := by decide +kernel
theorem subd17_1_398 : subd17_1 [-1, -2, 3] = true := by decide +kernel
theorem subd17_1_399 : subd17_1 [-1, -2, 4] = true := by decide +kernel
theorem subd17_1_400 : subd17_1 [-1, -2, 5] = true := by decide +kernel
theorem subd17_1_401 : subd17_1 [-1, -2, 6] = true := by decide +kernel
theorem subd17_1_402 : subd17_1 [-1, -2, 7] = true := by decide +kernel
theorem subd17_1_403 : subd17_1 [-1, -1, -9] = true := by decide +kernel
theorem subd17_1_404 : subd17_1 [-1, -1, -8] = true := by decide +kernel
theorem subd17_1_405 : subd17_1 [-1, -1, -7] = true := by decide +kernel
theorem subd17_1_406 : subd17_1 [-1, -1, -6] = true := by decide +kernel
theorem subd17_1_407 : subd17_1 [-1, -1, -5] = true := by decide +kernel
theorem subd17_1_408 : subd17_1 [-1, -1, -4] = true := by decide +kernel
theorem subd17_1_409 : subd17_1 [-1, -1, -3] = true := by decide +kernel
theorem subd17_1_410 : subd17_1 [-1, -1, -2] = true := by decide +kernel
theorem subd17_1_411 : subd17_1 [-1, -1, -1] = true := by decide +kernel
theorem subd17_1_412 : subd17_1 [-1, -1, 0] = true := by decide +kernel
theorem subd17_1_413 : subd17_1 [-1, -1, 1] = true := by decide +kernel
theorem subd17_1_414 : subd17_1 [-1, -1, 2] = true := by decide +kernel
theorem subd17_1_415 : subd17_1 [-1, -1, 3] = true := by decide +kernel
theorem sbd17_1_12 : ∀ q ∈ blkd17_1_12, subd17_1 q = true := by
  unfold blkd17_1_12
  exact List.forall_mem_cons.2 ⟨subd17_1_384, List.forall_mem_cons.2 ⟨subd17_1_385, List.forall_mem_cons.2 ⟨subd17_1_386, List.forall_mem_cons.2 ⟨subd17_1_387, List.forall_mem_cons.2 ⟨subd17_1_388, List.forall_mem_cons.2 ⟨subd17_1_389, List.forall_mem_cons.2 ⟨subd17_1_390, List.forall_mem_cons.2 ⟨subd17_1_391, List.forall_mem_cons.2 ⟨subd17_1_392, List.forall_mem_cons.2 ⟨subd17_1_393, List.forall_mem_cons.2 ⟨subd17_1_394, List.forall_mem_cons.2 ⟨subd17_1_395, List.forall_mem_cons.2 ⟨subd17_1_396, List.forall_mem_cons.2 ⟨subd17_1_397, List.forall_mem_cons.2 ⟨subd17_1_398, List.forall_mem_cons.2 ⟨subd17_1_399, List.forall_mem_cons.2 ⟨subd17_1_400, List.forall_mem_cons.2 ⟨subd17_1_401, List.forall_mem_cons.2 ⟨subd17_1_402, List.forall_mem_cons.2 ⟨subd17_1_403, List.forall_mem_cons.2 ⟨subd17_1_404, List.forall_mem_cons.2 ⟨subd17_1_405, List.forall_mem_cons.2 ⟨subd17_1_406, List.forall_mem_cons.2 ⟨subd17_1_407, List.forall_mem_cons.2 ⟨subd17_1_408, List.forall_mem_cons.2 ⟨subd17_1_409, List.forall_mem_cons.2 ⟨subd17_1_410, List.forall_mem_cons.2 ⟨subd17_1_411, List.forall_mem_cons.2 ⟨subd17_1_412, List.forall_mem_cons.2 ⟨subd17_1_413, List.forall_mem_cons.2 ⟨subd17_1_414, List.forall_mem_cons.2 ⟨subd17_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
