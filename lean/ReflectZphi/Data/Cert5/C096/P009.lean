import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_1_0 : subd7_1 [-6] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-5, -4] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-5, -3] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-5, -2] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-5, -1] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-5, 0] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-5, 1] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-5, 2] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-5, 3] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-5, 4] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [-4, -5] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [-4, -4] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [-4, -3] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [-4, -2] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [-4, -1] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [-4, 0] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [-4, 1] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [-4, 2] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [-4, 3] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [-4, 4] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [-4, 5] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [-3, -5] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [-3, -4] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [-3, -3] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [-3, -2] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [-3, -1, -6] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [-3, -1, -5] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [-3, -1, -4] = true := by decide +kernel
theorem subd7_1_28 : subd7_1 [-3, -1, -3] = true := by decide +kernel
theorem subd7_1_29 : subd7_1 [-3, -1, -2] = true := by decide +kernel
theorem subd7_1_30 : subd7_1 [-3, -1, -1] = true := by decide +kernel
theorem subd7_1_31 : subd7_1 [-3, -1, 0] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_cons.2 ⟨subd7_1_28, List.forall_mem_cons.2 ⟨subd7_1_29, List.forall_mem_cons.2 ⟨subd7_1_30, List.forall_mem_cons.2 ⟨subd7_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_32 : subd7_1 [-3, -1, 1] = true := by decide +kernel
theorem subd7_1_33 : subd7_1 [-3, -1, 2] = true := by decide +kernel
theorem subd7_1_34 : subd7_1 [-3, -1, 3] = true := by decide +kernel
theorem subd7_1_35 : subd7_1 [-3, -1, 4] = true := by decide +kernel
theorem subd7_1_36 : subd7_1 [-3, -1, 5] = true := by decide +kernel
theorem subd7_1_37 : subd7_1 [-3, -1, 6] = true := by decide +kernel
theorem subd7_1_38 : subd7_1 [-3, -1, 7] = true := by decide +kernel
theorem subd7_1_39 : subd7_1 [-3, 0, -7] = true := by decide +kernel
theorem subd7_1_40 : subd7_1 [-3, 0, -6] = true := by decide +kernel
theorem subd7_1_41 : subd7_1 [-3, 0, -5] = true := by decide +kernel
theorem subd7_1_42 : subd7_1 [-3, 0, -4] = true := by decide +kernel
theorem subd7_1_43 : subd7_1 [-3, 0, -3] = true := by decide +kernel
theorem subd7_1_44 : subd7_1 [-3, 0, -2] = true := by decide +kernel
theorem subd7_1_45 : subd7_1 [-3, 0, -1] = true := by decide +kernel
theorem subd7_1_46 : subd7_1 [-3, 0, 0] = true := by decide +kernel
theorem subd7_1_47 : subd7_1 [-3, 0, 1] = true := by decide +kernel
theorem subd7_1_48 : subd7_1 [-3, 0, 2] = true := by decide +kernel
theorem subd7_1_49 : subd7_1 [-3, 0, 3] = true := by decide +kernel
theorem subd7_1_50 : subd7_1 [-3, 0, 4] = true := by decide +kernel
theorem subd7_1_51 : subd7_1 [-3, 0, 5] = true := by decide +kernel
theorem subd7_1_52 : subd7_1 [-3, 0, 6] = true := by decide +kernel
theorem subd7_1_53 : subd7_1 [-3, 1, -7] = true := by decide +kernel
theorem subd7_1_54 : subd7_1 [-3, 1, -6] = true := by decide +kernel
theorem subd7_1_55 : subd7_1 [-3, 1, -5] = true := by decide +kernel
theorem subd7_1_56 : subd7_1 [-3, 1, -4] = true := by decide +kernel
theorem subd7_1_57 : subd7_1 [-3, 1, -3] = true := by decide +kernel
theorem subd7_1_58 : subd7_1 [-3, 1, -2] = true := by decide +kernel
theorem subd7_1_59 : subd7_1 [-3, 1, -1] = true := by decide +kernel
theorem subd7_1_60 : subd7_1 [-3, 1, 0] = true := by decide +kernel
theorem subd7_1_61 : subd7_1 [-3, 1, 1] = true := by decide +kernel
theorem subd7_1_62 : subd7_1 [-3, 1, 2] = true := by decide +kernel
theorem subd7_1_63 : subd7_1 [-3, 1, 3] = true := by decide +kernel
theorem sbd7_1_1 : ∀ q ∈ blkd7_1_1, subd7_1 q = true := by
  unfold blkd7_1_1
  exact List.forall_mem_cons.2 ⟨subd7_1_32, List.forall_mem_cons.2 ⟨subd7_1_33, List.forall_mem_cons.2 ⟨subd7_1_34, List.forall_mem_cons.2 ⟨subd7_1_35, List.forall_mem_cons.2 ⟨subd7_1_36, List.forall_mem_cons.2 ⟨subd7_1_37, List.forall_mem_cons.2 ⟨subd7_1_38, List.forall_mem_cons.2 ⟨subd7_1_39, List.forall_mem_cons.2 ⟨subd7_1_40, List.forall_mem_cons.2 ⟨subd7_1_41, List.forall_mem_cons.2 ⟨subd7_1_42, List.forall_mem_cons.2 ⟨subd7_1_43, List.forall_mem_cons.2 ⟨subd7_1_44, List.forall_mem_cons.2 ⟨subd7_1_45, List.forall_mem_cons.2 ⟨subd7_1_46, List.forall_mem_cons.2 ⟨subd7_1_47, List.forall_mem_cons.2 ⟨subd7_1_48, List.forall_mem_cons.2 ⟨subd7_1_49, List.forall_mem_cons.2 ⟨subd7_1_50, List.forall_mem_cons.2 ⟨subd7_1_51, List.forall_mem_cons.2 ⟨subd7_1_52, List.forall_mem_cons.2 ⟨subd7_1_53, List.forall_mem_cons.2 ⟨subd7_1_54, List.forall_mem_cons.2 ⟨subd7_1_55, List.forall_mem_cons.2 ⟨subd7_1_56, List.forall_mem_cons.2 ⟨subd7_1_57, List.forall_mem_cons.2 ⟨subd7_1_58, List.forall_mem_cons.2 ⟨subd7_1_59, List.forall_mem_cons.2 ⟨subd7_1_60, List.forall_mem_cons.2 ⟨subd7_1_61, List.forall_mem_cons.2 ⟨subd7_1_62, List.forall_mem_cons.2 ⟨subd7_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_64 : subd7_1 [-3, 1, 4] = true := by decide +kernel
theorem subd7_1_65 : subd7_1 [-3, 1, 5] = true := by decide +kernel
theorem subd7_1_66 : subd7_1 [-3, 1, 6] = true := by decide +kernel
theorem subd7_1_67 : subd7_1 [-3, 2, -7] = true := by decide +kernel
theorem subd7_1_68 : subd7_1 [-3, 2, -6] = true := by decide +kernel
theorem subd7_1_69 : subd7_1 [-3, 2, -5] = true := by decide +kernel
theorem subd7_1_70 : subd7_1 [-3, 2, -4] = true := by decide +kernel
theorem subd7_1_71 : subd7_1 [-3, 2, -3] = true := by decide +kernel
theorem subd7_1_72 : subd7_1 [-3, 2, -2] = true := by decide +kernel
theorem subd7_1_73 : subd7_1 [-3, 2, -1] = true := by decide +kernel
theorem subd7_1_74 : subd7_1 [-3, 2, 0] = true := by decide +kernel
theorem subd7_1_75 : subd7_1 [-3, 2, 1] = true := by decide +kernel
theorem subd7_1_76 : subd7_1 [-3, 2, 2] = true := by decide +kernel
theorem subd7_1_77 : subd7_1 [-3, 2, 3] = true := by decide +kernel
theorem subd7_1_78 : subd7_1 [-3, 2, 4] = true := by decide +kernel
theorem subd7_1_79 : subd7_1 [-3, 2, 5] = true := by decide +kernel
theorem subd7_1_80 : subd7_1 [-3, 3] = true := by decide +kernel
theorem subd7_1_81 : subd7_1 [-3, 4] = true := by decide +kernel
theorem subd7_1_82 : subd7_1 [-3, 5] = true := by decide +kernel
theorem subd7_1_83 : subd7_1 [-2, -6] = true := by decide +kernel
theorem subd7_1_84 : subd7_1 [-2, -5] = true := by decide +kernel
theorem subd7_1_85 : subd7_1 [-2, -4] = true := by decide +kernel
theorem subd7_1_86 : subd7_1 [-2, -3] = true := by decide +kernel
theorem subd7_1_87 : subd7_1 [-2, -2, -6] = true := by decide +kernel
theorem subd7_1_88 : subd7_1 [-2, -2, -5] = true := by decide +kernel
theorem subd7_1_89 : subd7_1 [-2, -2, -4] = true := by decide +kernel
theorem subd7_1_90 : subd7_1 [-2, -2, -3] = true := by decide +kernel
theorem subd7_1_91 : subd7_1 [-2, -2, -2] = true := by decide +kernel
theorem subd7_1_92 : subd7_1 [-2, -2, -1] = true := by decide +kernel
theorem subd7_1_93 : subd7_1 [-2, -2, 0] = true := by decide +kernel
theorem subd7_1_94 : subd7_1 [-2, -2, 1] = true := by decide +kernel
theorem subd7_1_95 : subd7_1 [-2, -2, 2] = true := by decide +kernel
theorem sbd7_1_2 : ∀ q ∈ blkd7_1_2, subd7_1 q = true := by
  unfold blkd7_1_2
  exact List.forall_mem_cons.2 ⟨subd7_1_64, List.forall_mem_cons.2 ⟨subd7_1_65, List.forall_mem_cons.2 ⟨subd7_1_66, List.forall_mem_cons.2 ⟨subd7_1_67, List.forall_mem_cons.2 ⟨subd7_1_68, List.forall_mem_cons.2 ⟨subd7_1_69, List.forall_mem_cons.2 ⟨subd7_1_70, List.forall_mem_cons.2 ⟨subd7_1_71, List.forall_mem_cons.2 ⟨subd7_1_72, List.forall_mem_cons.2 ⟨subd7_1_73, List.forall_mem_cons.2 ⟨subd7_1_74, List.forall_mem_cons.2 ⟨subd7_1_75, List.forall_mem_cons.2 ⟨subd7_1_76, List.forall_mem_cons.2 ⟨subd7_1_77, List.forall_mem_cons.2 ⟨subd7_1_78, List.forall_mem_cons.2 ⟨subd7_1_79, List.forall_mem_cons.2 ⟨subd7_1_80, List.forall_mem_cons.2 ⟨subd7_1_81, List.forall_mem_cons.2 ⟨subd7_1_82, List.forall_mem_cons.2 ⟨subd7_1_83, List.forall_mem_cons.2 ⟨subd7_1_84, List.forall_mem_cons.2 ⟨subd7_1_85, List.forall_mem_cons.2 ⟨subd7_1_86, List.forall_mem_cons.2 ⟨subd7_1_87, List.forall_mem_cons.2 ⟨subd7_1_88, List.forall_mem_cons.2 ⟨subd7_1_89, List.forall_mem_cons.2 ⟨subd7_1_90, List.forall_mem_cons.2 ⟨subd7_1_91, List.forall_mem_cons.2 ⟨subd7_1_92, List.forall_mem_cons.2 ⟨subd7_1_93, List.forall_mem_cons.2 ⟨subd7_1_94, List.forall_mem_cons.2 ⟨subd7_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_96 : subd7_1 [-2, -2, 3] = true := by decide +kernel
theorem subd7_1_97 : subd7_1 [-2, -2, 4] = true := by decide +kernel
theorem subd7_1_98 : subd7_1 [-2, -2, 5] = true := by decide +kernel
theorem subd7_1_99 : subd7_1 [-2, -2, 6] = true := by decide +kernel
theorem subd7_1_100 : subd7_1 [-2, -2, 7] = true := by decide +kernel
theorem subd7_1_101 : subd7_1 [-2, -1, -7] = true := by decide +kernel
theorem subd7_1_102 : subd7_1 [-2, -1, -6] = true := by decide +kernel
theorem subd7_1_103 : subd7_1 [-2, -1, -5] = true := by decide +kernel
theorem subd7_1_104 : subd7_1 [-2, -1, -4] = true := by decide +kernel
theorem subd7_1_105 : subd7_1 [-2, -1, -3] = true := by decide +kernel
theorem subd7_1_106 : subd7_1 [-2, -1, -2] = true := by decide +kernel
theorem subd7_1_107 : subd7_1 [-2, -1, -1] = true := by decide +kernel
theorem subd7_1_108 : subd7_1 [-2, -1, 0] = true := by decide +kernel
theorem subd7_1_109 : subd7_1 [-2, -1, 1] = true := by decide +kernel
theorem subd7_1_110 : subd7_1 [-2, -1, 2] = true := by decide +kernel
theorem subd7_1_111 : subd7_1 [-2, -1, 3] = true := by decide +kernel
theorem subd7_1_112 : subd7_1 [-2, -1, 4] = true := by decide +kernel
theorem subd7_1_113 : subd7_1 [-2, -1, 5] = true := by decide +kernel
theorem subd7_1_114 : subd7_1 [-2, -1, 6] = true := by decide +kernel
theorem subd7_1_115 : subd7_1 [-2, -1, 7] = true := by decide +kernel
theorem subd7_1_116 : subd7_1 [-2, 0, -7] = true := by decide +kernel
theorem subd7_1_117 : subd7_1 [-2, 0, -6] = true := by decide +kernel
theorem subd7_1_118 : subd7_1 [-2, 0, -5] = true := by decide +kernel
theorem subd7_1_119 : subd7_1 [-2, 0, -4] = true := by decide +kernel
theorem subd7_1_120 : subd7_1 [-2, 0, -3] = true := by decide +kernel
theorem subd7_1_121 : subd7_1 [-2, 0, -2] = true := by decide +kernel
theorem subd7_1_122 : subd7_1 [-2, 0, -1] = true := by decide +kernel
theorem subd7_1_123 : subd7_1 [-2, 0, 0] = true := by decide +kernel
theorem subd7_1_124 : subd7_1 [-2, 0, 1] = true := by decide +kernel
theorem subd7_1_125 : subd7_1 [-2, 0, 2] = true := by decide +kernel
theorem subd7_1_126 : subd7_1 [-2, 0, 3] = true := by decide +kernel
theorem subd7_1_127 : subd7_1 [-2, 0, 4] = true := by decide +kernel
theorem sbd7_1_3 : ∀ q ∈ blkd7_1_3, subd7_1 q = true := by
  unfold blkd7_1_3
  exact List.forall_mem_cons.2 ⟨subd7_1_96, List.forall_mem_cons.2 ⟨subd7_1_97, List.forall_mem_cons.2 ⟨subd7_1_98, List.forall_mem_cons.2 ⟨subd7_1_99, List.forall_mem_cons.2 ⟨subd7_1_100, List.forall_mem_cons.2 ⟨subd7_1_101, List.forall_mem_cons.2 ⟨subd7_1_102, List.forall_mem_cons.2 ⟨subd7_1_103, List.forall_mem_cons.2 ⟨subd7_1_104, List.forall_mem_cons.2 ⟨subd7_1_105, List.forall_mem_cons.2 ⟨subd7_1_106, List.forall_mem_cons.2 ⟨subd7_1_107, List.forall_mem_cons.2 ⟨subd7_1_108, List.forall_mem_cons.2 ⟨subd7_1_109, List.forall_mem_cons.2 ⟨subd7_1_110, List.forall_mem_cons.2 ⟨subd7_1_111, List.forall_mem_cons.2 ⟨subd7_1_112, List.forall_mem_cons.2 ⟨subd7_1_113, List.forall_mem_cons.2 ⟨subd7_1_114, List.forall_mem_cons.2 ⟨subd7_1_115, List.forall_mem_cons.2 ⟨subd7_1_116, List.forall_mem_cons.2 ⟨subd7_1_117, List.forall_mem_cons.2 ⟨subd7_1_118, List.forall_mem_cons.2 ⟨subd7_1_119, List.forall_mem_cons.2 ⟨subd7_1_120, List.forall_mem_cons.2 ⟨subd7_1_121, List.forall_mem_cons.2 ⟨subd7_1_122, List.forall_mem_cons.2 ⟨subd7_1_123, List.forall_mem_cons.2 ⟨subd7_1_124, List.forall_mem_cons.2 ⟨subd7_1_125, List.forall_mem_cons.2 ⟨subd7_1_126, List.forall_mem_cons.2 ⟨subd7_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_128 : subd7_1 [-2, 0, 5] = true := by decide +kernel
theorem subd7_1_129 : subd7_1 [-2, 0, 6] = true := by decide +kernel
theorem subd7_1_130 : subd7_1 [-2, 0, 7] = true := by decide +kernel
theorem subd7_1_131 : subd7_1 [-2, 1, -8] = true := by decide +kernel
theorem subd7_1_132 : subd7_1 [-2, 1, -7] = true := by decide +kernel
theorem subd7_1_133 : subd7_1 [-2, 1, -6] = true := by decide +kernel
theorem subd7_1_134 : subd7_1 [-2, 1, -5] = true := by decide +kernel
theorem subd7_1_135 : subd7_1 [-2, 1, -4] = true := by decide +kernel
theorem subd7_1_136 : subd7_1 [-2, 1, -3] = true := by decide +kernel
theorem subd7_1_137 : subd7_1 [-2, 1, -2] = true := by decide +kernel
theorem subd7_1_138 : subd7_1 [-2, 1, -1] = true := by decide +kernel
theorem subd7_1_139 : subd7_1 [-2, 1, 0] = true := by decide +kernel
theorem subd7_1_140 : subd7_1 [-2, 1, 1] = true := by decide +kernel
theorem subd7_1_141 : subd7_1 [-2, 1, 2] = true := by decide +kernel
theorem subd7_1_142 : subd7_1 [-2, 1, 3] = true := by decide +kernel
theorem subd7_1_143 : subd7_1 [-2, 1, 4] = true := by decide +kernel
theorem subd7_1_144 : subd7_1 [-2, 1, 5] = true := by decide +kernel
theorem subd7_1_145 : subd7_1 [-2, 1, 6] = true := by decide +kernel
theorem subd7_1_146 : subd7_1 [-2, 2, -8] = true := by decide +kernel
theorem subd7_1_147 : subd7_1 [-2, 2, -7] = true := by decide +kernel
theorem subd7_1_148 : subd7_1 [-2, 2, -6] = true := by decide +kernel
theorem subd7_1_149 : subd7_1 [-2, 2, -5] = true := by decide +kernel
theorem subd7_1_150 : subd7_1 [-2, 2, -4] = true := by decide +kernel
theorem subd7_1_151 : subd7_1 [-2, 2, -3] = true := by decide +kernel
theorem subd7_1_152 : subd7_1 [-2, 2, -2] = true := by decide +kernel
theorem subd7_1_153 : subd7_1 [-2, 2, -1] = true := by decide +kernel
theorem subd7_1_154 : subd7_1 [-2, 2, 0] = true := by decide +kernel
theorem subd7_1_155 : subd7_1 [-2, 2, 1] = true := by decide +kernel
theorem subd7_1_156 : subd7_1 [-2, 2, 2] = true := by decide +kernel
theorem subd7_1_157 : subd7_1 [-2, 2, 3] = true := by decide +kernel
theorem subd7_1_158 : subd7_1 [-2, 2, 4] = true := by decide +kernel
theorem subd7_1_159 : subd7_1 [-2, 2, 5] = true := by decide +kernel
theorem sbd7_1_4 : ∀ q ∈ blkd7_1_4, subd7_1 q = true := by
  unfold blkd7_1_4
  exact List.forall_mem_cons.2 ⟨subd7_1_128, List.forall_mem_cons.2 ⟨subd7_1_129, List.forall_mem_cons.2 ⟨subd7_1_130, List.forall_mem_cons.2 ⟨subd7_1_131, List.forall_mem_cons.2 ⟨subd7_1_132, List.forall_mem_cons.2 ⟨subd7_1_133, List.forall_mem_cons.2 ⟨subd7_1_134, List.forall_mem_cons.2 ⟨subd7_1_135, List.forall_mem_cons.2 ⟨subd7_1_136, List.forall_mem_cons.2 ⟨subd7_1_137, List.forall_mem_cons.2 ⟨subd7_1_138, List.forall_mem_cons.2 ⟨subd7_1_139, List.forall_mem_cons.2 ⟨subd7_1_140, List.forall_mem_cons.2 ⟨subd7_1_141, List.forall_mem_cons.2 ⟨subd7_1_142, List.forall_mem_cons.2 ⟨subd7_1_143, List.forall_mem_cons.2 ⟨subd7_1_144, List.forall_mem_cons.2 ⟨subd7_1_145, List.forall_mem_cons.2 ⟨subd7_1_146, List.forall_mem_cons.2 ⟨subd7_1_147, List.forall_mem_cons.2 ⟨subd7_1_148, List.forall_mem_cons.2 ⟨subd7_1_149, List.forall_mem_cons.2 ⟨subd7_1_150, List.forall_mem_cons.2 ⟨subd7_1_151, List.forall_mem_cons.2 ⟨subd7_1_152, List.forall_mem_cons.2 ⟨subd7_1_153, List.forall_mem_cons.2 ⟨subd7_1_154, List.forall_mem_cons.2 ⟨subd7_1_155, List.forall_mem_cons.2 ⟨subd7_1_156, List.forall_mem_cons.2 ⟨subd7_1_157, List.forall_mem_cons.2 ⟨subd7_1_158, List.forall_mem_cons.2 ⟨subd7_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_160 : subd7_1 [-2, 2, 6] = true := by decide +kernel
theorem subd7_1_161 : subd7_1 [-2, 3, -8] = true := by decide +kernel
theorem subd7_1_162 : subd7_1 [-2, 3, -7] = true := by decide +kernel
theorem subd7_1_163 : subd7_1 [-2, 3, -6] = true := by decide +kernel
theorem subd7_1_164 : subd7_1 [-2, 3, -5] = true := by decide +kernel
theorem subd7_1_165 : subd7_1 [-2, 3, -4] = true := by decide +kernel
theorem subd7_1_166 : subd7_1 [-2, 3, -3] = true := by decide +kernel
theorem subd7_1_167 : subd7_1 [-2, 3, -2] = true := by decide +kernel
theorem subd7_1_168 : subd7_1 [-2, 3, -1] = true := by decide +kernel
theorem subd7_1_169 : subd7_1 [-2, 3, 0] = true := by decide +kernel
theorem subd7_1_170 : subd7_1 [-2, 3, 1] = true := by decide +kernel
theorem subd7_1_171 : subd7_1 [-2, 3, 2] = true := by decide +kernel
theorem subd7_1_172 : subd7_1 [-2, 3, 3] = true := by decide +kernel
theorem subd7_1_173 : subd7_1 [-2, 3, 4] = true := by decide +kernel
theorem subd7_1_174 : subd7_1 [-2, 3, 5] = true := by decide +kernel
theorem subd7_1_175 : subd7_1 [-2, 4] = true := by decide +kernel
theorem subd7_1_176 : subd7_1 [-2, 5] = true := by decide +kernel
theorem subd7_1_177 : subd7_1 [-1, -6] = true := by decide +kernel
theorem subd7_1_178 : subd7_1 [-1, -5] = true := by decide +kernel
theorem subd7_1_179 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_180 : subd7_1 [-1, -3, -5] = true := by decide +kernel
theorem subd7_1_181 : subd7_1 [-1, -3, -4] = true := by decide +kernel
theorem subd7_1_182 : subd7_1 [-1, -3, -3] = true := by decide +kernel
theorem subd7_1_183 : subd7_1 [-1, -3, -2] = true := by decide +kernel
theorem subd7_1_184 : subd7_1 [-1, -3, -1] = true := by decide +kernel
theorem subd7_1_185 : subd7_1 [-1, -3, 0] = true := by decide +kernel
theorem subd7_1_186 : subd7_1 [-1, -3, 1] = true := by decide +kernel
theorem subd7_1_187 : subd7_1 [-1, -3, 2] = true := by decide +kernel
theorem subd7_1_188 : subd7_1 [-1, -3, 3] = true := by decide +kernel
theorem subd7_1_189 : subd7_1 [-1, -3, 4] = true := by decide +kernel
theorem subd7_1_190 : subd7_1 [-1, -3, 5] = true := by decide +kernel
theorem subd7_1_191 : subd7_1 [-1, -3, 6] = true := by decide +kernel
theorem sbd7_1_5 : ∀ q ∈ blkd7_1_5, subd7_1 q = true := by
  unfold blkd7_1_5
  exact List.forall_mem_cons.2 ⟨subd7_1_160, List.forall_mem_cons.2 ⟨subd7_1_161, List.forall_mem_cons.2 ⟨subd7_1_162, List.forall_mem_cons.2 ⟨subd7_1_163, List.forall_mem_cons.2 ⟨subd7_1_164, List.forall_mem_cons.2 ⟨subd7_1_165, List.forall_mem_cons.2 ⟨subd7_1_166, List.forall_mem_cons.2 ⟨subd7_1_167, List.forall_mem_cons.2 ⟨subd7_1_168, List.forall_mem_cons.2 ⟨subd7_1_169, List.forall_mem_cons.2 ⟨subd7_1_170, List.forall_mem_cons.2 ⟨subd7_1_171, List.forall_mem_cons.2 ⟨subd7_1_172, List.forall_mem_cons.2 ⟨subd7_1_173, List.forall_mem_cons.2 ⟨subd7_1_174, List.forall_mem_cons.2 ⟨subd7_1_175, List.forall_mem_cons.2 ⟨subd7_1_176, List.forall_mem_cons.2 ⟨subd7_1_177, List.forall_mem_cons.2 ⟨subd7_1_178, List.forall_mem_cons.2 ⟨subd7_1_179, List.forall_mem_cons.2 ⟨subd7_1_180, List.forall_mem_cons.2 ⟨subd7_1_181, List.forall_mem_cons.2 ⟨subd7_1_182, List.forall_mem_cons.2 ⟨subd7_1_183, List.forall_mem_cons.2 ⟨subd7_1_184, List.forall_mem_cons.2 ⟨subd7_1_185, List.forall_mem_cons.2 ⟨subd7_1_186, List.forall_mem_cons.2 ⟨subd7_1_187, List.forall_mem_cons.2 ⟨subd7_1_188, List.forall_mem_cons.2 ⟨subd7_1_189, List.forall_mem_cons.2 ⟨subd7_1_190, List.forall_mem_cons.2 ⟨subd7_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_192 : subd7_1 [-1, -3, 7] = true := by decide +kernel
theorem subd7_1_193 : subd7_1 [-1, -2, -7] = true := by decide +kernel
theorem subd7_1_194 : subd7_1 [-1, -2, -6] = true := by decide +kernel
theorem subd7_1_195 : subd7_1 [-1, -2, -5] = true := by decide +kernel
theorem subd7_1_196 : subd7_1 [-1, -2, -4] = true := by decide +kernel
theorem subd7_1_197 : subd7_1 [-1, -2, -3] = true := by decide +kernel
theorem subd7_1_198 : subd7_1 [-1, -2, -2] = true := by decide +kernel
theorem subd7_1_199 : subd7_1 [-1, -2, -1] = true := by decide +kernel
theorem subd7_1_200 : subd7_1 [-1, -2, 0] = true := by decide +kernel
theorem subd7_1_201 : subd7_1 [-1, -2, 1] = true := by decide +kernel
theorem subd7_1_202 : subd7_1 [-1, -2, 2] = true := by decide +kernel
theorem subd7_1_203 : subd7_1 [-1, -2, 3] = true := by decide +kernel
theorem subd7_1_204 : subd7_1 [-1, -2, 4] = true := by decide +kernel
theorem subd7_1_205 : subd7_1 [-1, -2, 5] = true := by decide +kernel
theorem subd7_1_206 : subd7_1 [-1, -2, 6] = true := by decide +kernel
theorem subd7_1_207 : subd7_1 [-1, -2, 7] = true := by decide +kernel
theorem subd7_1_208 : subd7_1 [-1, -1, -7] = true := by decide +kernel
theorem subd7_1_209 : subd7_1 [-1, -1, -6] = true := by decide +kernel
theorem subd7_1_210 : subd7_1 [-1, -1, -5] = true := by decide +kernel
theorem subd7_1_211 : subd7_1 [-1, -1, -4] = true := by decide +kernel
theorem subd7_1_212 : subd7_1 [-1, -1, -3] = true := by decide +kernel
theorem subd7_1_213 : subd7_1 [-1, -1, -2] = true := by decide +kernel
theorem subd7_1_214 : subd7_1 [-1, -1, -1] = true := by decide +kernel
theorem subd7_1_215 : subd7_1 [-1, -1, 0] = true := by decide +kernel
theorem subd7_1_216 : subd7_1 [-1, -1, 1] = true := by decide +kernel
theorem subd7_1_217 : subd7_1 [-1, -1, 2] = true := by decide +kernel
theorem subd7_1_218 : subd7_1 [-1, -1, 3] = true := by decide +kernel
theorem subd7_1_219 : subd7_1 [-1, -1, 4] = true := by decide +kernel
theorem subd7_1_220 : subd7_1 [-1, -1, 5] = true := by decide +kernel
theorem subd7_1_221 : subd7_1 [-1, -1, 6] = true := by decide +kernel
theorem subd7_1_222 : subd7_1 [-1, -1, 7] = true := by decide +kernel
theorem subd7_1_223 : subd7_1 [-1, 0, -8] = true := by decide +kernel
theorem sbd7_1_6 : ∀ q ∈ blkd7_1_6, subd7_1 q = true := by
  unfold blkd7_1_6
  exact List.forall_mem_cons.2 ⟨subd7_1_192, List.forall_mem_cons.2 ⟨subd7_1_193, List.forall_mem_cons.2 ⟨subd7_1_194, List.forall_mem_cons.2 ⟨subd7_1_195, List.forall_mem_cons.2 ⟨subd7_1_196, List.forall_mem_cons.2 ⟨subd7_1_197, List.forall_mem_cons.2 ⟨subd7_1_198, List.forall_mem_cons.2 ⟨subd7_1_199, List.forall_mem_cons.2 ⟨subd7_1_200, List.forall_mem_cons.2 ⟨subd7_1_201, List.forall_mem_cons.2 ⟨subd7_1_202, List.forall_mem_cons.2 ⟨subd7_1_203, List.forall_mem_cons.2 ⟨subd7_1_204, List.forall_mem_cons.2 ⟨subd7_1_205, List.forall_mem_cons.2 ⟨subd7_1_206, List.forall_mem_cons.2 ⟨subd7_1_207, List.forall_mem_cons.2 ⟨subd7_1_208, List.forall_mem_cons.2 ⟨subd7_1_209, List.forall_mem_cons.2 ⟨subd7_1_210, List.forall_mem_cons.2 ⟨subd7_1_211, List.forall_mem_cons.2 ⟨subd7_1_212, List.forall_mem_cons.2 ⟨subd7_1_213, List.forall_mem_cons.2 ⟨subd7_1_214, List.forall_mem_cons.2 ⟨subd7_1_215, List.forall_mem_cons.2 ⟨subd7_1_216, List.forall_mem_cons.2 ⟨subd7_1_217, List.forall_mem_cons.2 ⟨subd7_1_218, List.forall_mem_cons.2 ⟨subd7_1_219, List.forall_mem_cons.2 ⟨subd7_1_220, List.forall_mem_cons.2 ⟨subd7_1_221, List.forall_mem_cons.2 ⟨subd7_1_222, List.forall_mem_cons.2 ⟨subd7_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_224 : subd7_1 [-1, 0, -7] = true := by decide +kernel
theorem subd7_1_225 : subd7_1 [-1, 0, -6] = true := by decide +kernel
theorem subd7_1_226 : subd7_1 [-1, 0, -5] = true := by decide +kernel
theorem subd7_1_227 : subd7_1 [-1, 0, -4] = true := by decide +kernel
theorem subd7_1_228 : subd7_1 [-1, 0, -3] = true := by decide +kernel
theorem subd7_1_229 : subd7_1 [-1, 0, -2] = true := by decide +kernel
theorem subd7_1_230 : subd7_1 [-1, 0, -1] = true := by decide +kernel
theorem subd7_1_231 : subd7_1 [-1, 0, 0] = true := by decide +kernel
theorem subd7_1_232 : subd7_1 [-1, 0, 1] = true := by decide +kernel
theorem subd7_1_233 : subd7_1 [-1, 0, 2] = true := by decide +kernel
theorem subd7_1_234 : subd7_1 [-1, 0, 3] = true := by decide +kernel
theorem subd7_1_235 : subd7_1 [-1, 0, 4] = true := by decide +kernel
theorem subd7_1_236 : subd7_1 [-1, 0, 5] = true := by decide +kernel
theorem subd7_1_237 : subd7_1 [-1, 0, 6] = true := by decide +kernel
theorem subd7_1_238 : subd7_1 [-1, 0, 7] = true := by decide +kernel
theorem subd7_1_239 : subd7_1 [-1, 1, -8] = true := by decide +kernel
theorem subd7_1_240 : subd7_1 [-1, 1, -7] = true := by decide +kernel
theorem subd7_1_241 : subd7_1 [-1, 1, -6] = true := by decide +kernel
theorem subd7_1_242 : subd7_1 [-1, 1, -5] = true := by decide +kernel
theorem subd7_1_243 : subd7_1 [-1, 1, -4] = true := by decide +kernel
theorem subd7_1_244 : subd7_1 [-1, 1, -3] = true := by decide +kernel
theorem subd7_1_245 : subd7_1 [-1, 1, -2] = true := by decide +kernel
theorem subd7_1_246 : subd7_1 [-1, 1, -1] = true := by decide +kernel
theorem subd7_1_247 : subd7_1 [-1, 1, 0] = true := by decide +kernel
theorem subd7_1_248 : subd7_1 [-1, 1, 1] = true := by decide +kernel
theorem subd7_1_249 : subd7_1 [-1, 1, 2] = true := by decide +kernel
theorem subd7_1_250 : subd7_1 [-1, 1, 3] = true := by decide +kernel
theorem subd7_1_251 : subd7_1 [-1, 1, 4] = true := by decide +kernel
theorem subd7_1_252 : subd7_1 [-1, 1, 5] = true := by decide +kernel
theorem subd7_1_253 : subd7_1 [-1, 1, 6] = true := by decide +kernel
theorem subd7_1_254 : subd7_1 [-1, 1, 7] = true := by decide +kernel
theorem subd7_1_255 : subd7_1 [-1, 2, -8] = true := by decide +kernel
theorem sbd7_1_7 : ∀ q ∈ blkd7_1_7, subd7_1 q = true := by
  unfold blkd7_1_7
  exact List.forall_mem_cons.2 ⟨subd7_1_224, List.forall_mem_cons.2 ⟨subd7_1_225, List.forall_mem_cons.2 ⟨subd7_1_226, List.forall_mem_cons.2 ⟨subd7_1_227, List.forall_mem_cons.2 ⟨subd7_1_228, List.forall_mem_cons.2 ⟨subd7_1_229, List.forall_mem_cons.2 ⟨subd7_1_230, List.forall_mem_cons.2 ⟨subd7_1_231, List.forall_mem_cons.2 ⟨subd7_1_232, List.forall_mem_cons.2 ⟨subd7_1_233, List.forall_mem_cons.2 ⟨subd7_1_234, List.forall_mem_cons.2 ⟨subd7_1_235, List.forall_mem_cons.2 ⟨subd7_1_236, List.forall_mem_cons.2 ⟨subd7_1_237, List.forall_mem_cons.2 ⟨subd7_1_238, List.forall_mem_cons.2 ⟨subd7_1_239, List.forall_mem_cons.2 ⟨subd7_1_240, List.forall_mem_cons.2 ⟨subd7_1_241, List.forall_mem_cons.2 ⟨subd7_1_242, List.forall_mem_cons.2 ⟨subd7_1_243, List.forall_mem_cons.2 ⟨subd7_1_244, List.forall_mem_cons.2 ⟨subd7_1_245, List.forall_mem_cons.2 ⟨subd7_1_246, List.forall_mem_cons.2 ⟨subd7_1_247, List.forall_mem_cons.2 ⟨subd7_1_248, List.forall_mem_cons.2 ⟨subd7_1_249, List.forall_mem_cons.2 ⟨subd7_1_250, List.forall_mem_cons.2 ⟨subd7_1_251, List.forall_mem_cons.2 ⟨subd7_1_252, List.forall_mem_cons.2 ⟨subd7_1_253, List.forall_mem_cons.2 ⟨subd7_1_254, List.forall_mem_cons.2 ⟨subd7_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_256 : subd7_1 [-1, 2, -7] = true := by decide +kernel
theorem subd7_1_257 : subd7_1 [-1, 2, -6] = true := by decide +kernel
theorem subd7_1_258 : subd7_1 [-1, 2, -5] = true := by decide +kernel
theorem subd7_1_259 : subd7_1 [-1, 2, -4] = true := by decide +kernel
theorem subd7_1_260 : subd7_1 [-1, 2, -3] = true := by decide +kernel
theorem subd7_1_261 : subd7_1 [-1, 2, -2] = true := by decide +kernel
theorem subd7_1_262 : subd7_1 [-1, 2, -1] = true := by decide +kernel
theorem subd7_1_263 : subd7_1 [-1, 2, 0] = true := by decide +kernel
theorem subd7_1_264 : subd7_1 [-1, 2, 1] = true := by decide +kernel
theorem subd7_1_265 : subd7_1 [-1, 2, 2] = true := by decide +kernel
theorem subd7_1_266 : subd7_1 [-1, 2, 3] = true := by decide +kernel
theorem subd7_1_267 : subd7_1 [-1, 2, 4] = true := by decide +kernel
theorem subd7_1_268 : subd7_1 [-1, 2, 5] = true := by decide +kernel
theorem subd7_1_269 : subd7_1 [-1, 2, 6] = true := by decide +kernel
theorem subd7_1_270 : subd7_1 [-1, 3, -8] = true := by decide +kernel
theorem subd7_1_271 : subd7_1 [-1, 3, -7] = true := by decide +kernel
theorem subd7_1_272 : subd7_1 [-1, 3, -6] = true := by decide +kernel
theorem subd7_1_273 : subd7_1 [-1, 3, -5] = true := by decide +kernel
theorem subd7_1_274 : subd7_1 [-1, 3, -4] = true := by decide +kernel
theorem subd7_1_275 : subd7_1 [-1, 3, -3] = true := by decide +kernel
theorem subd7_1_276 : subd7_1 [-1, 3, -2] = true := by decide +kernel
theorem subd7_1_277 : subd7_1 [-1, 3, -1] = true := by decide +kernel
theorem subd7_1_278 : subd7_1 [-1, 3, 0] = true := by decide +kernel
theorem subd7_1_279 : subd7_1 [-1, 3, 1] = true := by decide +kernel
theorem subd7_1_280 : subd7_1 [-1, 3, 2] = true := by decide +kernel
theorem subd7_1_281 : subd7_1 [-1, 3, 3] = true := by decide +kernel
theorem subd7_1_282 : subd7_1 [-1, 3, 4] = true := by decide +kernel
theorem subd7_1_283 : subd7_1 [-1, 3, 5] = true := by decide +kernel
theorem subd7_1_284 : subd7_1 [-1, 4] = true := by decide +kernel
theorem subd7_1_285 : subd7_1 [-1, 5] = true := by decide +kernel
theorem subd7_1_286 : subd7_1 [-1, 6] = true := by decide +kernel
theorem subd7_1_287 : subd7_1 [0, -6] = true := by decide +kernel
theorem sbd7_1_8 : ∀ q ∈ blkd7_1_8, subd7_1 q = true := by
  unfold blkd7_1_8
  exact List.forall_mem_cons.2 ⟨subd7_1_256, List.forall_mem_cons.2 ⟨subd7_1_257, List.forall_mem_cons.2 ⟨subd7_1_258, List.forall_mem_cons.2 ⟨subd7_1_259, List.forall_mem_cons.2 ⟨subd7_1_260, List.forall_mem_cons.2 ⟨subd7_1_261, List.forall_mem_cons.2 ⟨subd7_1_262, List.forall_mem_cons.2 ⟨subd7_1_263, List.forall_mem_cons.2 ⟨subd7_1_264, List.forall_mem_cons.2 ⟨subd7_1_265, List.forall_mem_cons.2 ⟨subd7_1_266, List.forall_mem_cons.2 ⟨subd7_1_267, List.forall_mem_cons.2 ⟨subd7_1_268, List.forall_mem_cons.2 ⟨subd7_1_269, List.forall_mem_cons.2 ⟨subd7_1_270, List.forall_mem_cons.2 ⟨subd7_1_271, List.forall_mem_cons.2 ⟨subd7_1_272, List.forall_mem_cons.2 ⟨subd7_1_273, List.forall_mem_cons.2 ⟨subd7_1_274, List.forall_mem_cons.2 ⟨subd7_1_275, List.forall_mem_cons.2 ⟨subd7_1_276, List.forall_mem_cons.2 ⟨subd7_1_277, List.forall_mem_cons.2 ⟨subd7_1_278, List.forall_mem_cons.2 ⟨subd7_1_279, List.forall_mem_cons.2 ⟨subd7_1_280, List.forall_mem_cons.2 ⟨subd7_1_281, List.forall_mem_cons.2 ⟨subd7_1_282, List.forall_mem_cons.2 ⟨subd7_1_283, List.forall_mem_cons.2 ⟨subd7_1_284, List.forall_mem_cons.2 ⟨subd7_1_285, List.forall_mem_cons.2 ⟨subd7_1_286, List.forall_mem_cons.2 ⟨subd7_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_288 : subd7_1 [0, -5] = true := by decide +kernel
theorem subd7_1_289 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_290 : subd7_1 [0, -3, -6] = true := by decide +kernel
theorem subd7_1_291 : subd7_1 [0, -3, -5] = true := by decide +kernel
theorem subd7_1_292 : subd7_1 [0, -3, -4] = true := by decide +kernel
theorem subd7_1_293 : subd7_1 [0, -3, -3] = true := by decide +kernel
theorem subd7_1_294 : subd7_1 [0, -3, -2] = true := by decide +kernel
theorem subd7_1_295 : subd7_1 [0, -3, -1] = true := by decide +kernel
theorem subd7_1_296 : subd7_1 [0, -3, 0] = true := by decide +kernel
theorem subd7_1_297 : subd7_1 [0, -3, 1] = true := by decide +kernel
theorem subd7_1_298 : subd7_1 [0, -3, 2] = true := by decide +kernel
theorem subd7_1_299 : subd7_1 [0, -3, 3] = true := by decide +kernel
theorem subd7_1_300 : subd7_1 [0, -3, 4] = true := by decide +kernel
theorem subd7_1_301 : subd7_1 [0, -3, 5] = true := by decide +kernel
theorem subd7_1_302 : subd7_1 [0, -3, 6] = true := by decide +kernel
theorem subd7_1_303 : subd7_1 [0, -3, 7] = true := by decide +kernel
theorem subd7_1_304 : subd7_1 [0, -2, -7] = true := by decide +kernel
theorem subd7_1_305 : subd7_1 [0, -2, -6] = true := by decide +kernel
theorem subd7_1_306 : subd7_1 [0, -2, -5] = true := by decide +kernel
theorem subd7_1_307 : subd7_1 [0, -2, -4] = true := by decide +kernel
theorem subd7_1_308 : subd7_1 [0, -2, -3] = true := by decide +kernel
theorem subd7_1_309 : subd7_1 [0, -2, -2] = true := by decide +kernel
theorem subd7_1_310 : subd7_1 [0, -2, -1] = true := by decide +kernel
theorem subd7_1_311 : subd7_1 [0, -2, 0] = true := by decide +kernel
theorem subd7_1_312 : subd7_1 [0, -2, 1] = true := by decide +kernel
theorem subd7_1_313 : subd7_1 [0, -2, 2] = true := by decide +kernel
theorem subd7_1_314 : subd7_1 [0, -2, 3] = true := by decide +kernel
theorem subd7_1_315 : subd7_1 [0, -2, 4] = true := by decide +kernel
theorem subd7_1_316 : subd7_1 [0, -2, 5] = true := by decide +kernel
theorem subd7_1_317 : subd7_1 [0, -2, 6] = true := by decide +kernel
theorem subd7_1_318 : subd7_1 [0, -2, 7] = true := by decide +kernel
theorem subd7_1_319 : subd7_1 [0, -1, -8] = true := by decide +kernel
theorem sbd7_1_9 : ∀ q ∈ blkd7_1_9, subd7_1 q = true := by
  unfold blkd7_1_9
  exact List.forall_mem_cons.2 ⟨subd7_1_288, List.forall_mem_cons.2 ⟨subd7_1_289, List.forall_mem_cons.2 ⟨subd7_1_290, List.forall_mem_cons.2 ⟨subd7_1_291, List.forall_mem_cons.2 ⟨subd7_1_292, List.forall_mem_cons.2 ⟨subd7_1_293, List.forall_mem_cons.2 ⟨subd7_1_294, List.forall_mem_cons.2 ⟨subd7_1_295, List.forall_mem_cons.2 ⟨subd7_1_296, List.forall_mem_cons.2 ⟨subd7_1_297, List.forall_mem_cons.2 ⟨subd7_1_298, List.forall_mem_cons.2 ⟨subd7_1_299, List.forall_mem_cons.2 ⟨subd7_1_300, List.forall_mem_cons.2 ⟨subd7_1_301, List.forall_mem_cons.2 ⟨subd7_1_302, List.forall_mem_cons.2 ⟨subd7_1_303, List.forall_mem_cons.2 ⟨subd7_1_304, List.forall_mem_cons.2 ⟨subd7_1_305, List.forall_mem_cons.2 ⟨subd7_1_306, List.forall_mem_cons.2 ⟨subd7_1_307, List.forall_mem_cons.2 ⟨subd7_1_308, List.forall_mem_cons.2 ⟨subd7_1_309, List.forall_mem_cons.2 ⟨subd7_1_310, List.forall_mem_cons.2 ⟨subd7_1_311, List.forall_mem_cons.2 ⟨subd7_1_312, List.forall_mem_cons.2 ⟨subd7_1_313, List.forall_mem_cons.2 ⟨subd7_1_314, List.forall_mem_cons.2 ⟨subd7_1_315, List.forall_mem_cons.2 ⟨subd7_1_316, List.forall_mem_cons.2 ⟨subd7_1_317, List.forall_mem_cons.2 ⟨subd7_1_318, List.forall_mem_cons.2 ⟨subd7_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_320 : subd7_1 [0, -1, -7] = true := by decide +kernel
theorem subd7_1_321 : subd7_1 [0, -1, -6] = true := by decide +kernel
theorem subd7_1_322 : subd7_1 [0, -1, -5] = true := by decide +kernel
theorem subd7_1_323 : subd7_1 [0, -1, -4] = true := by decide +kernel
theorem subd7_1_324 : subd7_1 [0, -1, -3] = true := by decide +kernel
theorem subd7_1_325 : subd7_1 [0, -1, -2] = true := by decide +kernel
theorem subd7_1_326 : subd7_1 [0, -1, -1] = true := by decide +kernel
theorem subd7_1_327 : subd7_1 [0, -1, 0] = true := by decide +kernel
theorem subd7_1_328 : subd7_1 [0, -1, 1] = true := by decide +kernel
theorem subd7_1_329 : subd7_1 [0, -1, 2] = true := by decide +kernel
theorem subd7_1_330 : subd7_1 [0, -1, 3] = true := by decide +kernel
theorem subd7_1_331 : subd7_1 [0, -1, 4] = true := by decide +kernel
theorem subd7_1_332 : subd7_1 [0, -1, 5] = true := by decide +kernel
theorem subd7_1_333 : subd7_1 [0, -1, 6] = true := by decide +kernel
theorem subd7_1_334 : subd7_1 [0, -1, 7] = true := by decide +kernel
theorem subd7_1_335 : subd7_1 [0, 0, -8] = true := by decide +kernel
theorem subd7_1_336 : subd7_1 [0, 0, -7] = true := by decide +kernel
theorem subd7_1_337 : subd7_1 [0, 0, -6] = true := by decide +kernel
theorem subd7_1_338 : subd7_1 [0, 0, -5] = true := by decide +kernel
theorem subd7_1_339 : subd7_1 [0, 0, -4] = true := by decide +kernel
theorem subd7_1_340 : subd7_1 [0, 0, -3] = true := by decide +kernel
theorem subd7_1_341 : subd7_1 [0, 0, -2] = true := by decide +kernel
theorem subd7_1_342 : subd7_1 [0, 0, -1] = true := by decide +kernel
theorem subd7_1_343 : subd7_1 [0, 0, 0] = true := by decide +kernel
theorem subd7_1_344 : subd7_1 [0, 0, 1] = true := by decide +kernel
theorem subd7_1_345 : subd7_1 [0, 0, 2] = true := by decide +kernel
theorem subd7_1_346 : subd7_1 [0, 0, 3] = true := by decide +kernel
theorem subd7_1_347 : subd7_1 [0, 0, 4] = true := by decide +kernel
theorem subd7_1_348 : subd7_1 [0, 0, 5] = true := by decide +kernel
theorem subd7_1_349 : subd7_1 [0, 0, 6] = true := by decide +kernel
theorem subd7_1_350 : subd7_1 [0, 0, 7] = true := by decide +kernel
theorem subd7_1_351 : subd7_1 [0, 1, -8] = true := by decide +kernel
theorem sbd7_1_10 : ∀ q ∈ blkd7_1_10, subd7_1 q = true := by
  unfold blkd7_1_10
  exact List.forall_mem_cons.2 ⟨subd7_1_320, List.forall_mem_cons.2 ⟨subd7_1_321, List.forall_mem_cons.2 ⟨subd7_1_322, List.forall_mem_cons.2 ⟨subd7_1_323, List.forall_mem_cons.2 ⟨subd7_1_324, List.forall_mem_cons.2 ⟨subd7_1_325, List.forall_mem_cons.2 ⟨subd7_1_326, List.forall_mem_cons.2 ⟨subd7_1_327, List.forall_mem_cons.2 ⟨subd7_1_328, List.forall_mem_cons.2 ⟨subd7_1_329, List.forall_mem_cons.2 ⟨subd7_1_330, List.forall_mem_cons.2 ⟨subd7_1_331, List.forall_mem_cons.2 ⟨subd7_1_332, List.forall_mem_cons.2 ⟨subd7_1_333, List.forall_mem_cons.2 ⟨subd7_1_334, List.forall_mem_cons.2 ⟨subd7_1_335, List.forall_mem_cons.2 ⟨subd7_1_336, List.forall_mem_cons.2 ⟨subd7_1_337, List.forall_mem_cons.2 ⟨subd7_1_338, List.forall_mem_cons.2 ⟨subd7_1_339, List.forall_mem_cons.2 ⟨subd7_1_340, List.forall_mem_cons.2 ⟨subd7_1_341, List.forall_mem_cons.2 ⟨subd7_1_342, List.forall_mem_cons.2 ⟨subd7_1_343, List.forall_mem_cons.2 ⟨subd7_1_344, List.forall_mem_cons.2 ⟨subd7_1_345, List.forall_mem_cons.2 ⟨subd7_1_346, List.forall_mem_cons.2 ⟨subd7_1_347, List.forall_mem_cons.2 ⟨subd7_1_348, List.forall_mem_cons.2 ⟨subd7_1_349, List.forall_mem_cons.2 ⟨subd7_1_350, List.forall_mem_cons.2 ⟨subd7_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_352 : subd7_1 [0, 1, -7] = true := by decide +kernel
theorem subd7_1_353 : subd7_1 [0, 1, -6] = true := by decide +kernel
theorem subd7_1_354 : subd7_1 [0, 1, -5] = true := by decide +kernel
theorem subd7_1_355 : subd7_1 [0, 1, -4] = true := by decide +kernel
theorem subd7_1_356 : subd7_1 [0, 1, -3] = true := by decide +kernel
theorem subd7_1_357 : subd7_1 [0, 1, -2] = true := by decide +kernel
theorem subd7_1_358 : subd7_1 [0, 1, -1] = true := by decide +kernel
theorem subd7_1_359 : subd7_1 [0, 1, 0] = true := by decide +kernel
theorem subd7_1_360 : subd7_1 [0, 1, 1] = true := by decide +kernel
theorem subd7_1_361 : subd7_1 [0, 1, 2] = true := by decide +kernel
theorem subd7_1_362 : subd7_1 [0, 1, 3] = true := by decide +kernel
theorem subd7_1_363 : subd7_1 [0, 1, 4] = true := by decide +kernel
theorem subd7_1_364 : subd7_1 [0, 1, 5] = true := by decide +kernel
theorem subd7_1_365 : subd7_1 [0, 1, 6] = true := by decide +kernel
theorem subd7_1_366 : subd7_1 [0, 1, 7] = true := by decide +kernel
theorem subd7_1_367 : subd7_1 [0, 2, -8] = true := by decide +kernel
theorem subd7_1_368 : subd7_1 [0, 2, -7] = true := by decide +kernel
theorem subd7_1_369 : subd7_1 [0, 2, -6] = true := by decide +kernel
theorem subd7_1_370 : subd7_1 [0, 2, -5] = true := by decide +kernel
theorem subd7_1_371 : subd7_1 [0, 2, -4] = true := by decide +kernel
theorem subd7_1_372 : subd7_1 [0, 2, -3] = true := by decide +kernel
theorem subd7_1_373 : subd7_1 [0, 2, -2] = true := by decide +kernel
theorem subd7_1_374 : subd7_1 [0, 2, -1] = true := by decide +kernel
theorem subd7_1_375 : subd7_1 [0, 2, 0] = true := by decide +kernel
theorem subd7_1_376 : subd7_1 [0, 2, 1] = true := by decide +kernel
theorem subd7_1_377 : subd7_1 [0, 2, 2] = true := by decide +kernel
theorem subd7_1_378 : subd7_1 [0, 2, 3] = true := by decide +kernel
theorem subd7_1_379 : subd7_1 [0, 2, 4] = true := by decide +kernel
theorem subd7_1_380 : subd7_1 [0, 2, 5] = true := by decide +kernel
theorem subd7_1_381 : subd7_1 [0, 2, 6] = true := by decide +kernel
theorem subd7_1_382 : subd7_1 [0, 3, -8] = true := by decide +kernel
theorem subd7_1_383 : subd7_1 [0, 3, -7] = true := by decide +kernel
theorem sbd7_1_11 : ∀ q ∈ blkd7_1_11, subd7_1 q = true := by
  unfold blkd7_1_11
  exact List.forall_mem_cons.2 ⟨subd7_1_352, List.forall_mem_cons.2 ⟨subd7_1_353, List.forall_mem_cons.2 ⟨subd7_1_354, List.forall_mem_cons.2 ⟨subd7_1_355, List.forall_mem_cons.2 ⟨subd7_1_356, List.forall_mem_cons.2 ⟨subd7_1_357, List.forall_mem_cons.2 ⟨subd7_1_358, List.forall_mem_cons.2 ⟨subd7_1_359, List.forall_mem_cons.2 ⟨subd7_1_360, List.forall_mem_cons.2 ⟨subd7_1_361, List.forall_mem_cons.2 ⟨subd7_1_362, List.forall_mem_cons.2 ⟨subd7_1_363, List.forall_mem_cons.2 ⟨subd7_1_364, List.forall_mem_cons.2 ⟨subd7_1_365, List.forall_mem_cons.2 ⟨subd7_1_366, List.forall_mem_cons.2 ⟨subd7_1_367, List.forall_mem_cons.2 ⟨subd7_1_368, List.forall_mem_cons.2 ⟨subd7_1_369, List.forall_mem_cons.2 ⟨subd7_1_370, List.forall_mem_cons.2 ⟨subd7_1_371, List.forall_mem_cons.2 ⟨subd7_1_372, List.forall_mem_cons.2 ⟨subd7_1_373, List.forall_mem_cons.2 ⟨subd7_1_374, List.forall_mem_cons.2 ⟨subd7_1_375, List.forall_mem_cons.2 ⟨subd7_1_376, List.forall_mem_cons.2 ⟨subd7_1_377, List.forall_mem_cons.2 ⟨subd7_1_378, List.forall_mem_cons.2 ⟨subd7_1_379, List.forall_mem_cons.2 ⟨subd7_1_380, List.forall_mem_cons.2 ⟨subd7_1_381, List.forall_mem_cons.2 ⟨subd7_1_382, List.forall_mem_cons.2 ⟨subd7_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
