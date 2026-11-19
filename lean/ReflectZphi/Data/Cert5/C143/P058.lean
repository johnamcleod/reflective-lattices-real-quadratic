import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_2_0 : subd18_2 [-6] = true := by decide +kernel
theorem subd18_2_1 : subd18_2 [-5, -5] = true := by decide +kernel
theorem subd18_2_2 : subd18_2 [-5, -4] = true := by decide +kernel
theorem subd18_2_3 : subd18_2 [-5, -3] = true := by decide +kernel
theorem subd18_2_4 : subd18_2 [-5, -2] = true := by decide +kernel
theorem subd18_2_5 : subd18_2 [-5, -1] = true := by decide +kernel
theorem subd18_2_6 : subd18_2 [-5, 0] = true := by decide +kernel
theorem subd18_2_7 : subd18_2 [-5, 1] = true := by decide +kernel
theorem subd18_2_8 : subd18_2 [-5, 2] = true := by decide +kernel
theorem subd18_2_9 : subd18_2 [-4, -6] = true := by decide +kernel
theorem subd18_2_10 : subd18_2 [-4, -5] = true := by decide +kernel
theorem subd18_2_11 : subd18_2 [-4, -4] = true := by decide +kernel
theorem subd18_2_12 : subd18_2 [-4, -3] = true := by decide +kernel
theorem subd18_2_13 : subd18_2 [-4, -2] = true := by decide +kernel
theorem subd18_2_14 : subd18_2 [-4, -1] = true := by decide +kernel
theorem subd18_2_15 : subd18_2 [-4, 0] = true := by decide +kernel
theorem subd18_2_16 : subd18_2 [-4, 1] = true := by decide +kernel
theorem subd18_2_17 : subd18_2 [-4, 2] = true := by decide +kernel
theorem subd18_2_18 : subd18_2 [-4, 3] = true := by decide +kernel
theorem subd18_2_19 : subd18_2 [-3, -6] = true := by decide +kernel
theorem subd18_2_20 : subd18_2 [-3, -5] = true := by decide +kernel
theorem subd18_2_21 : subd18_2 [-3, -4] = true := by decide +kernel
theorem subd18_2_22 : subd18_2 [-3, -3] = true := by decide +kernel
theorem subd18_2_23 : subd18_2 [-3, -2] = true := by decide +kernel
theorem subd18_2_24 : subd18_2 [-3, -1, -8] = true := by decide +kernel
theorem subd18_2_25 : subd18_2 [-3, -1, -7] = true := by decide +kernel
theorem subd18_2_26 : subd18_2 [-3, -1, -6] = true := by decide +kernel
theorem subd18_2_27 : subd18_2 [-3, -1, -5] = true := by decide +kernel
theorem subd18_2_28 : subd18_2 [-3, -1, -4] = true := by decide +kernel
theorem subd18_2_29 : subd18_2 [-3, -1, -3] = true := by decide +kernel
theorem subd18_2_30 : subd18_2 [-3, -1, -2] = true := by decide +kernel
theorem subd18_2_31 : subd18_2 [-3, -1, -1] = true := by decide +kernel
theorem sbd18_2_0 : ∀ q ∈ blkd18_2_0, subd18_2 q = true := by
  unfold blkd18_2_0
  exact List.forall_mem_cons.2 ⟨subd18_2_0, List.forall_mem_cons.2 ⟨subd18_2_1, List.forall_mem_cons.2 ⟨subd18_2_2, List.forall_mem_cons.2 ⟨subd18_2_3, List.forall_mem_cons.2 ⟨subd18_2_4, List.forall_mem_cons.2 ⟨subd18_2_5, List.forall_mem_cons.2 ⟨subd18_2_6, List.forall_mem_cons.2 ⟨subd18_2_7, List.forall_mem_cons.2 ⟨subd18_2_8, List.forall_mem_cons.2 ⟨subd18_2_9, List.forall_mem_cons.2 ⟨subd18_2_10, List.forall_mem_cons.2 ⟨subd18_2_11, List.forall_mem_cons.2 ⟨subd18_2_12, List.forall_mem_cons.2 ⟨subd18_2_13, List.forall_mem_cons.2 ⟨subd18_2_14, List.forall_mem_cons.2 ⟨subd18_2_15, List.forall_mem_cons.2 ⟨subd18_2_16, List.forall_mem_cons.2 ⟨subd18_2_17, List.forall_mem_cons.2 ⟨subd18_2_18, List.forall_mem_cons.2 ⟨subd18_2_19, List.forall_mem_cons.2 ⟨subd18_2_20, List.forall_mem_cons.2 ⟨subd18_2_21, List.forall_mem_cons.2 ⟨subd18_2_22, List.forall_mem_cons.2 ⟨subd18_2_23, List.forall_mem_cons.2 ⟨subd18_2_24, List.forall_mem_cons.2 ⟨subd18_2_25, List.forall_mem_cons.2 ⟨subd18_2_26, List.forall_mem_cons.2 ⟨subd18_2_27, List.forall_mem_cons.2 ⟨subd18_2_28, List.forall_mem_cons.2 ⟨subd18_2_29, List.forall_mem_cons.2 ⟨subd18_2_30, List.forall_mem_cons.2 ⟨subd18_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_32 : subd18_2 [-3, -1, 0] = true := by decide +kernel
theorem subd18_2_33 : subd18_2 [-3, -1, 1] = true := by decide +kernel
theorem subd18_2_34 : subd18_2 [-3, -1, 2] = true := by decide +kernel
theorem subd18_2_35 : subd18_2 [-3, -1, 3] = true := by decide +kernel
theorem subd18_2_36 : subd18_2 [-3, -1, 4] = true := by decide +kernel
theorem subd18_2_37 : subd18_2 [-3, -1, 5] = true := by decide +kernel
theorem subd18_2_38 : subd18_2 [-3, -1, 6] = true := by decide +kernel
theorem subd18_2_39 : subd18_2 [-3, 0, -7] = true := by decide +kernel
theorem subd18_2_40 : subd18_2 [-3, 0, -6] = true := by decide +kernel
theorem subd18_2_41 : subd18_2 [-3, 0, -5] = true := by decide +kernel
theorem subd18_2_42 : subd18_2 [-3, 0, -4] = true := by decide +kernel
theorem subd18_2_43 : subd18_2 [-3, 0, -3] = true := by decide +kernel
theorem subd18_2_44 : subd18_2 [-3, 0, -2] = true := by decide +kernel
theorem subd18_2_45 : subd18_2 [-3, 0, -1] = true := by decide +kernel
theorem subd18_2_46 : subd18_2 [-3, 0, 0] = true := by decide +kernel
theorem subd18_2_47 : subd18_2 [-3, 0, 1] = true := by decide +kernel
theorem subd18_2_48 : subd18_2 [-3, 0, 2] = true := by decide +kernel
theorem subd18_2_49 : subd18_2 [-3, 0, 3] = true := by decide +kernel
theorem subd18_2_50 : subd18_2 [-3, 0, 4] = true := by decide +kernel
theorem subd18_2_51 : subd18_2 [-3, 0, 5] = true := by decide +kernel
theorem subd18_2_52 : subd18_2 [-3, 0, 6] = true := by decide +kernel
theorem subd18_2_53 : subd18_2 [-3, 1] = true := by decide +kernel
theorem subd18_2_54 : subd18_2 [-3, 2] = true := by decide +kernel
theorem subd18_2_55 : subd18_2 [-3, 3] = true := by decide +kernel
theorem subd18_2_56 : subd18_2 [-3, 4] = true := by decide +kernel
theorem subd18_2_57 : subd18_2 [-2, -6] = true := by decide +kernel
theorem subd18_2_58 : subd18_2 [-2, -5] = true := by decide +kernel
theorem subd18_2_59 : subd18_2 [-2, -4] = true := by decide +kernel
theorem subd18_2_60 : subd18_2 [-2, -3] = true := by decide +kernel
theorem subd18_2_61 : subd18_2 [-2, -2, -8] = true := by decide +kernel
theorem subd18_2_62 : subd18_2 [-2, -2, -7] = true := by decide +kernel
theorem subd18_2_63 : subd18_2 [-2, -2, -6] = true := by decide +kernel
theorem sbd18_2_1 : ∀ q ∈ blkd18_2_1, subd18_2 q = true := by
  unfold blkd18_2_1
  exact List.forall_mem_cons.2 ⟨subd18_2_32, List.forall_mem_cons.2 ⟨subd18_2_33, List.forall_mem_cons.2 ⟨subd18_2_34, List.forall_mem_cons.2 ⟨subd18_2_35, List.forall_mem_cons.2 ⟨subd18_2_36, List.forall_mem_cons.2 ⟨subd18_2_37, List.forall_mem_cons.2 ⟨subd18_2_38, List.forall_mem_cons.2 ⟨subd18_2_39, List.forall_mem_cons.2 ⟨subd18_2_40, List.forall_mem_cons.2 ⟨subd18_2_41, List.forall_mem_cons.2 ⟨subd18_2_42, List.forall_mem_cons.2 ⟨subd18_2_43, List.forall_mem_cons.2 ⟨subd18_2_44, List.forall_mem_cons.2 ⟨subd18_2_45, List.forall_mem_cons.2 ⟨subd18_2_46, List.forall_mem_cons.2 ⟨subd18_2_47, List.forall_mem_cons.2 ⟨subd18_2_48, List.forall_mem_cons.2 ⟨subd18_2_49, List.forall_mem_cons.2 ⟨subd18_2_50, List.forall_mem_cons.2 ⟨subd18_2_51, List.forall_mem_cons.2 ⟨subd18_2_52, List.forall_mem_cons.2 ⟨subd18_2_53, List.forall_mem_cons.2 ⟨subd18_2_54, List.forall_mem_cons.2 ⟨subd18_2_55, List.forall_mem_cons.2 ⟨subd18_2_56, List.forall_mem_cons.2 ⟨subd18_2_57, List.forall_mem_cons.2 ⟨subd18_2_58, List.forall_mem_cons.2 ⟨subd18_2_59, List.forall_mem_cons.2 ⟨subd18_2_60, List.forall_mem_cons.2 ⟨subd18_2_61, List.forall_mem_cons.2 ⟨subd18_2_62, List.forall_mem_cons.2 ⟨subd18_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_64 : subd18_2 [-2, -2, -5] = true := by decide +kernel
theorem subd18_2_65 : subd18_2 [-2, -2, -4] = true := by decide +kernel
theorem subd18_2_66 : subd18_2 [-2, -2, -3] = true := by decide +kernel
theorem subd18_2_67 : subd18_2 [-2, -2, -2] = true := by decide +kernel
theorem subd18_2_68 : subd18_2 [-2, -2, -1] = true := by decide +kernel
theorem subd18_2_69 : subd18_2 [-2, -2, 0] = true := by decide +kernel
theorem subd18_2_70 : subd18_2 [-2, -2, 1] = true := by decide +kernel
theorem subd18_2_71 : subd18_2 [-2, -2, 2] = true := by decide +kernel
theorem subd18_2_72 : subd18_2 [-2, -2, 3] = true := by decide +kernel
theorem subd18_2_73 : subd18_2 [-2, -2, 4] = true := by decide +kernel
theorem subd18_2_74 : subd18_2 [-2, -2, 5] = true := by decide +kernel
theorem subd18_2_75 : subd18_2 [-2, -2, 6] = true := by decide +kernel
theorem subd18_2_76 : subd18_2 [-2, -1, -8] = true := by decide +kernel
theorem subd18_2_77 : subd18_2 [-2, -1, -7] = true := by decide +kernel
theorem subd18_2_78 : subd18_2 [-2, -1, -6] = true := by decide +kernel
theorem subd18_2_79 : subd18_2 [-2, -1, -5] = true := by decide +kernel
theorem subd18_2_80 : subd18_2 [-2, -1, -4] = true := by decide +kernel
theorem subd18_2_81 : subd18_2 [-2, -1, -3] = true := by decide +kernel
theorem subd18_2_82 : subd18_2 [-2, -1, -2] = true := by decide +kernel
theorem subd18_2_83 : subd18_2 [-2, -1, -1] = true := by decide +kernel
theorem subd18_2_84 : subd18_2 [-2, -1, 0] = true := by decide +kernel
theorem subd18_2_85 : subd18_2 [-2, -1, 1] = true := by decide +kernel
theorem subd18_2_86 : subd18_2 [-2, -1, 2] = true := by decide +kernel
theorem subd18_2_87 : subd18_2 [-2, -1, 3] = true := by decide +kernel
theorem subd18_2_88 : subd18_2 [-2, -1, 4] = true := by decide +kernel
theorem subd18_2_89 : subd18_2 [-2, -1, 5] = true := by decide +kernel
theorem subd18_2_90 : subd18_2 [-2, -1, 6] = true := by decide +kernel
theorem subd18_2_91 : subd18_2 [-2, 0, -8] = true := by decide +kernel
theorem subd18_2_92 : subd18_2 [-2, 0, -7] = true := by decide +kernel
theorem subd18_2_93 : subd18_2 [-2, 0, -6] = true := by decide +kernel
theorem subd18_2_94 : subd18_2 [-2, 0, -5] = true := by decide +kernel
theorem subd18_2_95 : subd18_2 [-2, 0, -4] = true := by decide +kernel
theorem sbd18_2_2 : ∀ q ∈ blkd18_2_2, subd18_2 q = true := by
  unfold blkd18_2_2
  exact List.forall_mem_cons.2 ⟨subd18_2_64, List.forall_mem_cons.2 ⟨subd18_2_65, List.forall_mem_cons.2 ⟨subd18_2_66, List.forall_mem_cons.2 ⟨subd18_2_67, List.forall_mem_cons.2 ⟨subd18_2_68, List.forall_mem_cons.2 ⟨subd18_2_69, List.forall_mem_cons.2 ⟨subd18_2_70, List.forall_mem_cons.2 ⟨subd18_2_71, List.forall_mem_cons.2 ⟨subd18_2_72, List.forall_mem_cons.2 ⟨subd18_2_73, List.forall_mem_cons.2 ⟨subd18_2_74, List.forall_mem_cons.2 ⟨subd18_2_75, List.forall_mem_cons.2 ⟨subd18_2_76, List.forall_mem_cons.2 ⟨subd18_2_77, List.forall_mem_cons.2 ⟨subd18_2_78, List.forall_mem_cons.2 ⟨subd18_2_79, List.forall_mem_cons.2 ⟨subd18_2_80, List.forall_mem_cons.2 ⟨subd18_2_81, List.forall_mem_cons.2 ⟨subd18_2_82, List.forall_mem_cons.2 ⟨subd18_2_83, List.forall_mem_cons.2 ⟨subd18_2_84, List.forall_mem_cons.2 ⟨subd18_2_85, List.forall_mem_cons.2 ⟨subd18_2_86, List.forall_mem_cons.2 ⟨subd18_2_87, List.forall_mem_cons.2 ⟨subd18_2_88, List.forall_mem_cons.2 ⟨subd18_2_89, List.forall_mem_cons.2 ⟨subd18_2_90, List.forall_mem_cons.2 ⟨subd18_2_91, List.forall_mem_cons.2 ⟨subd18_2_92, List.forall_mem_cons.2 ⟨subd18_2_93, List.forall_mem_cons.2 ⟨subd18_2_94, List.forall_mem_cons.2 ⟨subd18_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_96 : subd18_2 [-2, 0, -3] = true := by decide +kernel
theorem subd18_2_97 : subd18_2 [-2, 0, -2] = true := by decide +kernel
theorem subd18_2_98 : subd18_2 [-2, 0, -1] = true := by decide +kernel
theorem subd18_2_99 : subd18_2 [-2, 0, 0] = true := by decide +kernel
theorem subd18_2_100 : subd18_2 [-2, 0, 1] = true := by decide +kernel
theorem subd18_2_101 : subd18_2 [-2, 0, 2] = true := by decide +kernel
theorem subd18_2_102 : subd18_2 [-2, 0, 3] = true := by decide +kernel
theorem subd18_2_103 : subd18_2 [-2, 0, 4] = true := by decide +kernel
theorem subd18_2_104 : subd18_2 [-2, 0, 5] = true := by decide +kernel
theorem subd18_2_105 : subd18_2 [-2, 0, 6] = true := by decide +kernel
theorem subd18_2_106 : subd18_2 [-2, 0, 7] = true := by decide +kernel
theorem subd18_2_107 : subd18_2 [-2, 1, -7] = true := by decide +kernel
theorem subd18_2_108 : subd18_2 [-2, 1, -6] = true := by decide +kernel
theorem subd18_2_109 : subd18_2 [-2, 1, -5] = true := by decide +kernel
theorem subd18_2_110 : subd18_2 [-2, 1, -4] = true := by decide +kernel
theorem subd18_2_111 : subd18_2 [-2, 1, -3] = true := by decide +kernel
theorem subd18_2_112 : subd18_2 [-2, 1, -2] = true := by decide +kernel
theorem subd18_2_113 : subd18_2 [-2, 1, -1] = true := by decide +kernel
theorem subd18_2_114 : subd18_2 [-2, 1, 0] = true := by decide +kernel
theorem subd18_2_115 : subd18_2 [-2, 1, 1] = true := by decide +kernel
theorem subd18_2_116 : subd18_2 [-2, 1, 2] = true := by decide +kernel
theorem subd18_2_117 : subd18_2 [-2, 1, 3] = true := by decide +kernel
theorem subd18_2_118 : subd18_2 [-2, 1, 4] = true := by decide +kernel
theorem subd18_2_119 : subd18_2 [-2, 1, 5] = true := by decide +kernel
theorem subd18_2_120 : subd18_2 [-2, 1, 6] = true := by decide +kernel
theorem subd18_2_121 : subd18_2 [-2, 2] = true := by decide +kernel
theorem subd18_2_122 : subd18_2 [-2, 3] = true := by decide +kernel
theorem subd18_2_123 : subd18_2 [-2, 4] = true := by decide +kernel
theorem subd18_2_124 : subd18_2 [-1, -6] = true := by decide +kernel
theorem subd18_2_125 : subd18_2 [-1, -5] = true := by decide +kernel
theorem subd18_2_126 : subd18_2 [-1, -4] = true := by decide +kernel
theorem subd18_2_127 : subd18_2 [-1, -3, -8] = true := by decide +kernel
theorem sbd18_2_3 : ∀ q ∈ blkd18_2_3, subd18_2 q = true := by
  unfold blkd18_2_3
  exact List.forall_mem_cons.2 ⟨subd18_2_96, List.forall_mem_cons.2 ⟨subd18_2_97, List.forall_mem_cons.2 ⟨subd18_2_98, List.forall_mem_cons.2 ⟨subd18_2_99, List.forall_mem_cons.2 ⟨subd18_2_100, List.forall_mem_cons.2 ⟨subd18_2_101, List.forall_mem_cons.2 ⟨subd18_2_102, List.forall_mem_cons.2 ⟨subd18_2_103, List.forall_mem_cons.2 ⟨subd18_2_104, List.forall_mem_cons.2 ⟨subd18_2_105, List.forall_mem_cons.2 ⟨subd18_2_106, List.forall_mem_cons.2 ⟨subd18_2_107, List.forall_mem_cons.2 ⟨subd18_2_108, List.forall_mem_cons.2 ⟨subd18_2_109, List.forall_mem_cons.2 ⟨subd18_2_110, List.forall_mem_cons.2 ⟨subd18_2_111, List.forall_mem_cons.2 ⟨subd18_2_112, List.forall_mem_cons.2 ⟨subd18_2_113, List.forall_mem_cons.2 ⟨subd18_2_114, List.forall_mem_cons.2 ⟨subd18_2_115, List.forall_mem_cons.2 ⟨subd18_2_116, List.forall_mem_cons.2 ⟨subd18_2_117, List.forall_mem_cons.2 ⟨subd18_2_118, List.forall_mem_cons.2 ⟨subd18_2_119, List.forall_mem_cons.2 ⟨subd18_2_120, List.forall_mem_cons.2 ⟨subd18_2_121, List.forall_mem_cons.2 ⟨subd18_2_122, List.forall_mem_cons.2 ⟨subd18_2_123, List.forall_mem_cons.2 ⟨subd18_2_124, List.forall_mem_cons.2 ⟨subd18_2_125, List.forall_mem_cons.2 ⟨subd18_2_126, List.forall_mem_cons.2 ⟨subd18_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_128 : subd18_2 [-1, -3, -7] = true := by decide +kernel
theorem subd18_2_129 : subd18_2 [-1, -3, -6] = true := by decide +kernel
theorem subd18_2_130 : subd18_2 [-1, -3, -5] = true := by decide +kernel
theorem subd18_2_131 : subd18_2 [-1, -3, -4] = true := by decide +kernel
theorem subd18_2_132 : subd18_2 [-1, -3, -3] = true := by decide +kernel
theorem subd18_2_133 : subd18_2 [-1, -3, -2] = true := by decide +kernel
theorem subd18_2_134 : subd18_2 [-1, -3, -1] = true := by decide +kernel
theorem subd18_2_135 : subd18_2 [-1, -3, 0] = true := by decide +kernel
theorem subd18_2_136 : subd18_2 [-1, -3, 1] = true := by decide +kernel
theorem subd18_2_137 : subd18_2 [-1, -3, 2] = true := by decide +kernel
theorem subd18_2_138 : subd18_2 [-1, -3, 3] = true := by decide +kernel
theorem subd18_2_139 : subd18_2 [-1, -3, 4] = true := by decide +kernel
theorem subd18_2_140 : subd18_2 [-1, -3, 5] = true := by decide +kernel
theorem subd18_2_141 : subd18_2 [-1, -2, -8] = true := by decide +kernel
theorem subd18_2_142 : subd18_2 [-1, -2, -7] = true := by decide +kernel
theorem subd18_2_143 : subd18_2 [-1, -2, -6] = true := by decide +kernel
theorem subd18_2_144 : subd18_2 [-1, -2, -5] = true := by decide +kernel
theorem subd18_2_145 : subd18_2 [-1, -2, -4] = true := by decide +kernel
theorem subd18_2_146 : subd18_2 [-1, -2, -3] = true := by decide +kernel
theorem subd18_2_147 : subd18_2 [-1, -2, -2] = true := by decide +kernel
theorem subd18_2_148 : subd18_2 [-1, -2, -1] = true := by decide +kernel
theorem subd18_2_149 : subd18_2 [-1, -2, 0] = true := by decide +kernel
theorem subd18_2_150 : subd18_2 [-1, -2, 1] = true := by decide +kernel
theorem subd18_2_151 : subd18_2 [-1, -2, 2] = true := by decide +kernel
theorem subd18_2_152 : subd18_2 [-1, -2, 3] = true := by decide +kernel
theorem subd18_2_153 : subd18_2 [-1, -2, 4] = true := by decide +kernel
theorem subd18_2_154 : subd18_2 [-1, -2, 5] = true := by decide +kernel
theorem subd18_2_155 : subd18_2 [-1, -2, 6] = true := by decide +kernel
theorem subd18_2_156 : subd18_2 [-1, -1, -8] = true := by decide +kernel
theorem subd18_2_157 : subd18_2 [-1, -1, -7] = true := by decide +kernel
theorem subd18_2_158 : subd18_2 [-1, -1, -6] = true := by decide +kernel
theorem subd18_2_159 : subd18_2 [-1, -1, -5] = true := by decide +kernel
theorem sbd18_2_4 : ∀ q ∈ blkd18_2_4, subd18_2 q = true := by
  unfold blkd18_2_4
  exact List.forall_mem_cons.2 ⟨subd18_2_128, List.forall_mem_cons.2 ⟨subd18_2_129, List.forall_mem_cons.2 ⟨subd18_2_130, List.forall_mem_cons.2 ⟨subd18_2_131, List.forall_mem_cons.2 ⟨subd18_2_132, List.forall_mem_cons.2 ⟨subd18_2_133, List.forall_mem_cons.2 ⟨subd18_2_134, List.forall_mem_cons.2 ⟨subd18_2_135, List.forall_mem_cons.2 ⟨subd18_2_136, List.forall_mem_cons.2 ⟨subd18_2_137, List.forall_mem_cons.2 ⟨subd18_2_138, List.forall_mem_cons.2 ⟨subd18_2_139, List.forall_mem_cons.2 ⟨subd18_2_140, List.forall_mem_cons.2 ⟨subd18_2_141, List.forall_mem_cons.2 ⟨subd18_2_142, List.forall_mem_cons.2 ⟨subd18_2_143, List.forall_mem_cons.2 ⟨subd18_2_144, List.forall_mem_cons.2 ⟨subd18_2_145, List.forall_mem_cons.2 ⟨subd18_2_146, List.forall_mem_cons.2 ⟨subd18_2_147, List.forall_mem_cons.2 ⟨subd18_2_148, List.forall_mem_cons.2 ⟨subd18_2_149, List.forall_mem_cons.2 ⟨subd18_2_150, List.forall_mem_cons.2 ⟨subd18_2_151, List.forall_mem_cons.2 ⟨subd18_2_152, List.forall_mem_cons.2 ⟨subd18_2_153, List.forall_mem_cons.2 ⟨subd18_2_154, List.forall_mem_cons.2 ⟨subd18_2_155, List.forall_mem_cons.2 ⟨subd18_2_156, List.forall_mem_cons.2 ⟨subd18_2_157, List.forall_mem_cons.2 ⟨subd18_2_158, List.forall_mem_cons.2 ⟨subd18_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_160 : subd18_2 [-1, -1, -4] = true := by decide +kernel
theorem subd18_2_161 : subd18_2 [-1, -1, -3] = true := by decide +kernel
theorem subd18_2_162 : subd18_2 [-1, -1, -2] = true := by decide +kernel
theorem subd18_2_163 : subd18_2 [-1, -1, -1] = true := by decide +kernel
theorem subd18_2_164 : subd18_2 [-1, -1, 0] = true := by decide +kernel
theorem subd18_2_165 : subd18_2 [-1, -1, 1] = true := by decide +kernel
theorem subd18_2_166 : subd18_2 [-1, -1, 2] = true := by decide +kernel
theorem subd18_2_167 : subd18_2 [-1, -1, 3] = true := by decide +kernel
theorem subd18_2_168 : subd18_2 [-1, -1, 4] = true := by decide +kernel
theorem subd18_2_169 : subd18_2 [-1, -1, 5] = true := by decide +kernel
theorem subd18_2_170 : subd18_2 [-1, -1, 6] = true := by decide +kernel
theorem subd18_2_171 : subd18_2 [-1, -1, 7] = true := by decide +kernel
theorem subd18_2_172 : subd18_2 [-1, 0, -8] = true := by decide +kernel
theorem subd18_2_173 : subd18_2 [-1, 0, -7] = true := by decide +kernel
theorem subd18_2_174 : subd18_2 [-1, 0, -6] = true := by decide +kernel
theorem subd18_2_175 : subd18_2 [-1, 0, -5] = true := by decide +kernel
theorem subd18_2_176 : subd18_2 [-1, 0, -4] = true := by decide +kernel
theorem subd18_2_177 : subd18_2 [-1, 0, -3] = true := by decide +kernel
theorem subd18_2_178 : subd18_2 [-1, 0, -2] = true := by decide +kernel
theorem subd18_2_179 : subd18_2 [-1, 0, -1] = true := by decide +kernel
theorem subd18_2_180 : subd18_2 [-1, 0, 0] = true := by decide +kernel
theorem subd18_2_181 : subd18_2 [-1, 0, 1] = true := by decide +kernel
theorem subd18_2_182 : subd18_2 [-1, 0, 2] = true := by decide +kernel
theorem subd18_2_183 : subd18_2 [-1, 0, 3] = true := by decide +kernel
theorem subd18_2_184 : subd18_2 [-1, 0, 4] = true := by decide +kernel
theorem subd18_2_185 : subd18_2 [-1, 0, 5] = true := by decide +kernel
theorem subd18_2_186 : subd18_2 [-1, 0, 6] = true := by decide +kernel
theorem subd18_2_187 : subd18_2 [-1, 0, 7] = true := by decide +kernel
theorem subd18_2_188 : subd18_2 [-1, 1, -8] = true := by decide +kernel
theorem subd18_2_189 : subd18_2 [-1, 1, -7] = true := by decide +kernel
theorem subd18_2_190 : subd18_2 [-1, 1, -6] = true := by decide +kernel
theorem subd18_2_191 : subd18_2 [-1, 1, -5] = true := by decide +kernel
theorem sbd18_2_5 : ∀ q ∈ blkd18_2_5, subd18_2 q = true := by
  unfold blkd18_2_5
  exact List.forall_mem_cons.2 ⟨subd18_2_160, List.forall_mem_cons.2 ⟨subd18_2_161, List.forall_mem_cons.2 ⟨subd18_2_162, List.forall_mem_cons.2 ⟨subd18_2_163, List.forall_mem_cons.2 ⟨subd18_2_164, List.forall_mem_cons.2 ⟨subd18_2_165, List.forall_mem_cons.2 ⟨subd18_2_166, List.forall_mem_cons.2 ⟨subd18_2_167, List.forall_mem_cons.2 ⟨subd18_2_168, List.forall_mem_cons.2 ⟨subd18_2_169, List.forall_mem_cons.2 ⟨subd18_2_170, List.forall_mem_cons.2 ⟨subd18_2_171, List.forall_mem_cons.2 ⟨subd18_2_172, List.forall_mem_cons.2 ⟨subd18_2_173, List.forall_mem_cons.2 ⟨subd18_2_174, List.forall_mem_cons.2 ⟨subd18_2_175, List.forall_mem_cons.2 ⟨subd18_2_176, List.forall_mem_cons.2 ⟨subd18_2_177, List.forall_mem_cons.2 ⟨subd18_2_178, List.forall_mem_cons.2 ⟨subd18_2_179, List.forall_mem_cons.2 ⟨subd18_2_180, List.forall_mem_cons.2 ⟨subd18_2_181, List.forall_mem_cons.2 ⟨subd18_2_182, List.forall_mem_cons.2 ⟨subd18_2_183, List.forall_mem_cons.2 ⟨subd18_2_184, List.forall_mem_cons.2 ⟨subd18_2_185, List.forall_mem_cons.2 ⟨subd18_2_186, List.forall_mem_cons.2 ⟨subd18_2_187, List.forall_mem_cons.2 ⟨subd18_2_188, List.forall_mem_cons.2 ⟨subd18_2_189, List.forall_mem_cons.2 ⟨subd18_2_190, List.forall_mem_cons.2 ⟨subd18_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_192 : subd18_2 [-1, 1, -4] = true := by decide +kernel
theorem subd18_2_193 : subd18_2 [-1, 1, -3] = true := by decide +kernel
theorem subd18_2_194 : subd18_2 [-1, 1, -2] = true := by decide +kernel
theorem subd18_2_195 : subd18_2 [-1, 1, -1] = true := by decide +kernel
theorem subd18_2_196 : subd18_2 [-1, 1, 0] = true := by decide +kernel
theorem subd18_2_197 : subd18_2 [-1, 1, 1] = true := by decide +kernel
theorem subd18_2_198 : subd18_2 [-1, 1, 2] = true := by decide +kernel
theorem subd18_2_199 : subd18_2 [-1, 1, 3] = true := by decide +kernel
theorem subd18_2_200 : subd18_2 [-1, 1, 4] = true := by decide +kernel
theorem subd18_2_201 : subd18_2 [-1, 1, 5] = true := by decide +kernel
theorem subd18_2_202 : subd18_2 [-1, 1, 6] = true := by decide +kernel
theorem subd18_2_203 : subd18_2 [-1, 1, 7] = true := by decide +kernel
theorem subd18_2_204 : subd18_2 [-1, 2, -7] = true := by decide +kernel
theorem subd18_2_205 : subd18_2 [-1, 2, -6] = true := by decide +kernel
theorem subd18_2_206 : subd18_2 [-1, 2, -5] = true := by decide +kernel
theorem subd18_2_207 : subd18_2 [-1, 2, -4] = true := by decide +kernel
theorem subd18_2_208 : subd18_2 [-1, 2, -3] = true := by decide +kernel
theorem subd18_2_209 : subd18_2 [-1, 2, -2] = true := by decide +kernel
theorem subd18_2_210 : subd18_2 [-1, 2, -1] = true := by decide +kernel
theorem subd18_2_211 : subd18_2 [-1, 2, 0] = true := by decide +kernel
theorem subd18_2_212 : subd18_2 [-1, 2, 1] = true := by decide +kernel
theorem subd18_2_213 : subd18_2 [-1, 2, 2] = true := by decide +kernel
theorem subd18_2_214 : subd18_2 [-1, 2, 3] = true := by decide +kernel
theorem subd18_2_215 : subd18_2 [-1, 2, 4] = true := by decide +kernel
theorem subd18_2_216 : subd18_2 [-1, 2, 5] = true := by decide +kernel
theorem subd18_2_217 : subd18_2 [-1, 2, 6] = true := by decide +kernel
theorem subd18_2_218 : subd18_2 [-1, 2, 7] = true := by decide +kernel
theorem subd18_2_219 : subd18_2 [-1, 3] = true := by decide +kernel
theorem subd18_2_220 : subd18_2 [-1, 4] = true := by decide +kernel
theorem subd18_2_221 : subd18_2 [-1, 5] = true := by decide +kernel
theorem subd18_2_222 : subd18_2 [0, -6] = true := by decide +kernel
theorem subd18_2_223 : subd18_2 [0, -5] = true := by decide +kernel
theorem sbd18_2_6 : ∀ q ∈ blkd18_2_6, subd18_2 q = true := by
  unfold blkd18_2_6
  exact List.forall_mem_cons.2 ⟨subd18_2_192, List.forall_mem_cons.2 ⟨subd18_2_193, List.forall_mem_cons.2 ⟨subd18_2_194, List.forall_mem_cons.2 ⟨subd18_2_195, List.forall_mem_cons.2 ⟨subd18_2_196, List.forall_mem_cons.2 ⟨subd18_2_197, List.forall_mem_cons.2 ⟨subd18_2_198, List.forall_mem_cons.2 ⟨subd18_2_199, List.forall_mem_cons.2 ⟨subd18_2_200, List.forall_mem_cons.2 ⟨subd18_2_201, List.forall_mem_cons.2 ⟨subd18_2_202, List.forall_mem_cons.2 ⟨subd18_2_203, List.forall_mem_cons.2 ⟨subd18_2_204, List.forall_mem_cons.2 ⟨subd18_2_205, List.forall_mem_cons.2 ⟨subd18_2_206, List.forall_mem_cons.2 ⟨subd18_2_207, List.forall_mem_cons.2 ⟨subd18_2_208, List.forall_mem_cons.2 ⟨subd18_2_209, List.forall_mem_cons.2 ⟨subd18_2_210, List.forall_mem_cons.2 ⟨subd18_2_211, List.forall_mem_cons.2 ⟨subd18_2_212, List.forall_mem_cons.2 ⟨subd18_2_213, List.forall_mem_cons.2 ⟨subd18_2_214, List.forall_mem_cons.2 ⟨subd18_2_215, List.forall_mem_cons.2 ⟨subd18_2_216, List.forall_mem_cons.2 ⟨subd18_2_217, List.forall_mem_cons.2 ⟨subd18_2_218, List.forall_mem_cons.2 ⟨subd18_2_219, List.forall_mem_cons.2 ⟨subd18_2_220, List.forall_mem_cons.2 ⟨subd18_2_221, List.forall_mem_cons.2 ⟨subd18_2_222, List.forall_mem_cons.2 ⟨subd18_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_224 : subd18_2 [0, -4] = true := by decide +kernel
theorem subd18_2_225 : subd18_2 [0, -3] = true := by decide +kernel
theorem subd18_2_226 : subd18_2 [0, -2, -8] = true := by decide +kernel
theorem subd18_2_227 : subd18_2 [0, -2, -7] = true := by decide +kernel
theorem subd18_2_228 : subd18_2 [0, -2, -6] = true := by decide +kernel
theorem subd18_2_229 : subd18_2 [0, -2, -5] = true := by decide +kernel
theorem subd18_2_230 : subd18_2 [0, -2, -4] = true := by decide +kernel
theorem subd18_2_231 : subd18_2 [0, -2, -3] = true := by decide +kernel
theorem subd18_2_232 : subd18_2 [0, -2, -2] = true := by decide +kernel
theorem subd18_2_233 : subd18_2 [0, -2, -1] = true := by decide +kernel
theorem subd18_2_234 : subd18_2 [0, -2, 0] = true := by decide +kernel
theorem subd18_2_235 : subd18_2 [0, -2, 1] = true := by decide +kernel
theorem subd18_2_236 : subd18_2 [0, -2, 2] = true := by decide +kernel
theorem subd18_2_237 : subd18_2 [0, -2, 3] = true := by decide +kernel
theorem subd18_2_238 : subd18_2 [0, -2, 4] = true := by decide +kernel
theorem subd18_2_239 : subd18_2 [0, -2, 5] = true := by decide +kernel
theorem subd18_2_240 : subd18_2 [0, -2, 6] = true := by decide +kernel
theorem subd18_2_241 : subd18_2 [0, -1, -8] = true := by decide +kernel
theorem subd18_2_242 : subd18_2 [0, -1, -7] = true := by decide +kernel
theorem subd18_2_243 : subd18_2 [0, -1, -6] = true := by decide +kernel
theorem subd18_2_244 : subd18_2 [0, -1, -5] = true := by decide +kernel
theorem subd18_2_245 : subd18_2 [0, -1, -4] = true := by decide +kernel
theorem subd18_2_246 : subd18_2 [0, -1, -3] = true := by decide +kernel
theorem subd18_2_247 : subd18_2 [0, -1, -2] = true := by decide +kernel
theorem subd18_2_248 : subd18_2 [0, -1, -1] = true := by decide +kernel
theorem subd18_2_249 : subd18_2 [0, -1, 0] = true := by decide +kernel
theorem subd18_2_250 : subd18_2 [0, -1, 1] = true := by decide +kernel
theorem subd18_2_251 : subd18_2 [0, -1, 2] = true := by decide +kernel
theorem subd18_2_252 : subd18_2 [0, -1, 3] = true := by decide +kernel
theorem subd18_2_253 : subd18_2 [0, -1, 4] = true := by decide +kernel
theorem subd18_2_254 : subd18_2 [0, -1, 5] = true := by decide +kernel
theorem subd18_2_255 : subd18_2 [0, -1, 6] = true := by decide +kernel
theorem sbd18_2_7 : ∀ q ∈ blkd18_2_7, subd18_2 q = true := by
  unfold blkd18_2_7
  exact List.forall_mem_cons.2 ⟨subd18_2_224, List.forall_mem_cons.2 ⟨subd18_2_225, List.forall_mem_cons.2 ⟨subd18_2_226, List.forall_mem_cons.2 ⟨subd18_2_227, List.forall_mem_cons.2 ⟨subd18_2_228, List.forall_mem_cons.2 ⟨subd18_2_229, List.forall_mem_cons.2 ⟨subd18_2_230, List.forall_mem_cons.2 ⟨subd18_2_231, List.forall_mem_cons.2 ⟨subd18_2_232, List.forall_mem_cons.2 ⟨subd18_2_233, List.forall_mem_cons.2 ⟨subd18_2_234, List.forall_mem_cons.2 ⟨subd18_2_235, List.forall_mem_cons.2 ⟨subd18_2_236, List.forall_mem_cons.2 ⟨subd18_2_237, List.forall_mem_cons.2 ⟨subd18_2_238, List.forall_mem_cons.2 ⟨subd18_2_239, List.forall_mem_cons.2 ⟨subd18_2_240, List.forall_mem_cons.2 ⟨subd18_2_241, List.forall_mem_cons.2 ⟨subd18_2_242, List.forall_mem_cons.2 ⟨subd18_2_243, List.forall_mem_cons.2 ⟨subd18_2_244, List.forall_mem_cons.2 ⟨subd18_2_245, List.forall_mem_cons.2 ⟨subd18_2_246, List.forall_mem_cons.2 ⟨subd18_2_247, List.forall_mem_cons.2 ⟨subd18_2_248, List.forall_mem_cons.2 ⟨subd18_2_249, List.forall_mem_cons.2 ⟨subd18_2_250, List.forall_mem_cons.2 ⟨subd18_2_251, List.forall_mem_cons.2 ⟨subd18_2_252, List.forall_mem_cons.2 ⟨subd18_2_253, List.forall_mem_cons.2 ⟨subd18_2_254, List.forall_mem_cons.2 ⟨subd18_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_256 : subd18_2 [0, -1, 7] = true := by decide +kernel
theorem subd18_2_257 : subd18_2 [0, 0, -8] = true := by decide +kernel
theorem subd18_2_258 : subd18_2 [0, 0, -7] = true := by decide +kernel
theorem subd18_2_259 : subd18_2 [0, 0, -6] = true := by decide +kernel
theorem subd18_2_260 : subd18_2 [0, 0, -5] = true := by decide +kernel
theorem subd18_2_261 : subd18_2 [0, 0, -4] = true := by decide +kernel
theorem subd18_2_262 : subd18_2 [0, 0, -3] = true := by decide +kernel
theorem subd18_2_263 : subd18_2 [0, 0, -2] = true := by decide +kernel
theorem subd18_2_264 : subd18_2 [0, 0, -1] = true := by decide +kernel
theorem subd18_2_265 : subd18_2 [0, 0, 0] = true := by decide +kernel
theorem subd18_2_266 : subd18_2 [0, 0, 1] = true := by decide +kernel
theorem subd18_2_267 : subd18_2 [0, 0, 2] = true := by decide +kernel
theorem subd18_2_268 : subd18_2 [0, 0, 3] = true := by decide +kernel
theorem subd18_2_269 : subd18_2 [0, 0, 4] = true := by decide +kernel
theorem subd18_2_270 : subd18_2 [0, 0, 5] = true := by decide +kernel
theorem subd18_2_271 : subd18_2 [0, 0, 6] = true := by decide +kernel
theorem subd18_2_272 : subd18_2 [0, 0, 7] = true := by decide +kernel
theorem subd18_2_273 : subd18_2 [0, 1, -8] = true := by decide +kernel
theorem subd18_2_274 : subd18_2 [0, 1, -7] = true := by decide +kernel
theorem subd18_2_275 : subd18_2 [0, 1, -6] = true := by decide +kernel
theorem subd18_2_276 : subd18_2 [0, 1, -5] = true := by decide +kernel
theorem subd18_2_277 : subd18_2 [0, 1, -4] = true := by decide +kernel
theorem subd18_2_278 : subd18_2 [0, 1, -3] = true := by decide +kernel
theorem subd18_2_279 : subd18_2 [0, 1, -2] = true := by decide +kernel
theorem subd18_2_280 : subd18_2 [0, 1, -1] = true := by decide +kernel
theorem subd18_2_281 : subd18_2 [0, 1, 0] = true := by decide +kernel
theorem subd18_2_282 : subd18_2 [0, 1, 1] = true := by decide +kernel
theorem subd18_2_283 : subd18_2 [0, 1, 2] = true := by decide +kernel
theorem subd18_2_284 : subd18_2 [0, 1, 3] = true := by decide +kernel
theorem subd18_2_285 : subd18_2 [0, 1, 4] = true := by decide +kernel
theorem subd18_2_286 : subd18_2 [0, 1, 5] = true := by decide +kernel
theorem subd18_2_287 : subd18_2 [0, 1, 6] = true := by decide +kernel
theorem sbd18_2_8 : ∀ q ∈ blkd18_2_8, subd18_2 q = true := by
  unfold blkd18_2_8
  exact List.forall_mem_cons.2 ⟨subd18_2_256, List.forall_mem_cons.2 ⟨subd18_2_257, List.forall_mem_cons.2 ⟨subd18_2_258, List.forall_mem_cons.2 ⟨subd18_2_259, List.forall_mem_cons.2 ⟨subd18_2_260, List.forall_mem_cons.2 ⟨subd18_2_261, List.forall_mem_cons.2 ⟨subd18_2_262, List.forall_mem_cons.2 ⟨subd18_2_263, List.forall_mem_cons.2 ⟨subd18_2_264, List.forall_mem_cons.2 ⟨subd18_2_265, List.forall_mem_cons.2 ⟨subd18_2_266, List.forall_mem_cons.2 ⟨subd18_2_267, List.forall_mem_cons.2 ⟨subd18_2_268, List.forall_mem_cons.2 ⟨subd18_2_269, List.forall_mem_cons.2 ⟨subd18_2_270, List.forall_mem_cons.2 ⟨subd18_2_271, List.forall_mem_cons.2 ⟨subd18_2_272, List.forall_mem_cons.2 ⟨subd18_2_273, List.forall_mem_cons.2 ⟨subd18_2_274, List.forall_mem_cons.2 ⟨subd18_2_275, List.forall_mem_cons.2 ⟨subd18_2_276, List.forall_mem_cons.2 ⟨subd18_2_277, List.forall_mem_cons.2 ⟨subd18_2_278, List.forall_mem_cons.2 ⟨subd18_2_279, List.forall_mem_cons.2 ⟨subd18_2_280, List.forall_mem_cons.2 ⟨subd18_2_281, List.forall_mem_cons.2 ⟨subd18_2_282, List.forall_mem_cons.2 ⟨subd18_2_283, List.forall_mem_cons.2 ⟨subd18_2_284, List.forall_mem_cons.2 ⟨subd18_2_285, List.forall_mem_cons.2 ⟨subd18_2_286, List.forall_mem_cons.2 ⟨subd18_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_288 : subd18_2 [0, 1, 7] = true := by decide +kernel
theorem subd18_2_289 : subd18_2 [0, 2, -7] = true := by decide +kernel
theorem subd18_2_290 : subd18_2 [0, 2, -6] = true := by decide +kernel
theorem subd18_2_291 : subd18_2 [0, 2, -5] = true := by decide +kernel
theorem subd18_2_292 : subd18_2 [0, 2, -4] = true := by decide +kernel
theorem subd18_2_293 : subd18_2 [0, 2, -3] = true := by decide +kernel
theorem subd18_2_294 : subd18_2 [0, 2, -2] = true := by decide +kernel
theorem subd18_2_295 : subd18_2 [0, 2, -1] = true := by decide +kernel
theorem subd18_2_296 : subd18_2 [0, 2, 0] = true := by decide +kernel
theorem subd18_2_297 : subd18_2 [0, 2, 1] = true := by decide +kernel
theorem subd18_2_298 : subd18_2 [0, 2, 2] = true := by decide +kernel
theorem subd18_2_299 : subd18_2 [0, 2, 3] = true := by decide +kernel
theorem subd18_2_300 : subd18_2 [0, 2, 4] = true := by decide +kernel
theorem subd18_2_301 : subd18_2 [0, 2, 5] = true := by decide +kernel
theorem subd18_2_302 : subd18_2 [0, 2, 6] = true := by decide +kernel
theorem subd18_2_303 : subd18_2 [0, 2, 7] = true := by decide +kernel
theorem subd18_2_304 : subd18_2 [0, 3] = true := by decide +kernel
theorem subd18_2_305 : subd18_2 [0, 4] = true := by decide +kernel
theorem subd18_2_306 : subd18_2 [0, 5] = true := by decide +kernel
theorem subd18_2_307 : subd18_2 [1, -6] = true := by decide +kernel
theorem subd18_2_308 : subd18_2 [1, -5] = true := by decide +kernel
theorem subd18_2_309 : subd18_2 [1, -4] = true := by decide +kernel
theorem subd18_2_310 : subd18_2 [1, -3] = true := by decide +kernel
theorem subd18_2_311 : subd18_2 [1, -2, -8] = true := by decide +kernel
theorem subd18_2_312 : subd18_2 [1, -2, -7] = true := by decide +kernel
theorem subd18_2_313 : subd18_2 [1, -2, -6] = true := by decide +kernel
theorem subd18_2_314 : subd18_2 [1, -2, -5] = true := by decide +kernel
theorem subd18_2_315 : subd18_2 [1, -2, -4] = true := by decide +kernel
theorem subd18_2_316 : subd18_2 [1, -2, -3] = true := by decide +kernel
theorem subd18_2_317 : subd18_2 [1, -2, -2] = true := by decide +kernel
theorem subd18_2_318 : subd18_2 [1, -2, -1] = true := by decide +kernel
theorem subd18_2_319 : subd18_2 [1, -2, 0] = true := by decide +kernel
theorem sbd18_2_9 : ∀ q ∈ blkd18_2_9, subd18_2 q = true := by
  unfold blkd18_2_9
  exact List.forall_mem_cons.2 ⟨subd18_2_288, List.forall_mem_cons.2 ⟨subd18_2_289, List.forall_mem_cons.2 ⟨subd18_2_290, List.forall_mem_cons.2 ⟨subd18_2_291, List.forall_mem_cons.2 ⟨subd18_2_292, List.forall_mem_cons.2 ⟨subd18_2_293, List.forall_mem_cons.2 ⟨subd18_2_294, List.forall_mem_cons.2 ⟨subd18_2_295, List.forall_mem_cons.2 ⟨subd18_2_296, List.forall_mem_cons.2 ⟨subd18_2_297, List.forall_mem_cons.2 ⟨subd18_2_298, List.forall_mem_cons.2 ⟨subd18_2_299, List.forall_mem_cons.2 ⟨subd18_2_300, List.forall_mem_cons.2 ⟨subd18_2_301, List.forall_mem_cons.2 ⟨subd18_2_302, List.forall_mem_cons.2 ⟨subd18_2_303, List.forall_mem_cons.2 ⟨subd18_2_304, List.forall_mem_cons.2 ⟨subd18_2_305, List.forall_mem_cons.2 ⟨subd18_2_306, List.forall_mem_cons.2 ⟨subd18_2_307, List.forall_mem_cons.2 ⟨subd18_2_308, List.forall_mem_cons.2 ⟨subd18_2_309, List.forall_mem_cons.2 ⟨subd18_2_310, List.forall_mem_cons.2 ⟨subd18_2_311, List.forall_mem_cons.2 ⟨subd18_2_312, List.forall_mem_cons.2 ⟨subd18_2_313, List.forall_mem_cons.2 ⟨subd18_2_314, List.forall_mem_cons.2 ⟨subd18_2_315, List.forall_mem_cons.2 ⟨subd18_2_316, List.forall_mem_cons.2 ⟨subd18_2_317, List.forall_mem_cons.2 ⟨subd18_2_318, List.forall_mem_cons.2 ⟨subd18_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_320 : subd18_2 [1, -2, 1] = true := by decide +kernel
theorem subd18_2_321 : subd18_2 [1, -2, 2] = true := by decide +kernel
theorem subd18_2_322 : subd18_2 [1, -2, 3] = true := by decide +kernel
theorem subd18_2_323 : subd18_2 [1, -2, 4] = true := by decide +kernel
theorem subd18_2_324 : subd18_2 [1, -2, 5] = true := by decide +kernel
theorem subd18_2_325 : subd18_2 [1, -2, 6] = true := by decide +kernel
theorem subd18_2_326 : subd18_2 [1, -1, -8] = true := by decide +kernel
theorem subd18_2_327 : subd18_2 [1, -1, -7] = true := by decide +kernel
theorem subd18_2_328 : subd18_2 [1, -1, -6] = true := by decide +kernel
theorem subd18_2_329 : subd18_2 [1, -1, -5] = true := by decide +kernel
theorem subd18_2_330 : subd18_2 [1, -1, -4] = true := by decide +kernel
theorem subd18_2_331 : subd18_2 [1, -1, -3] = true := by decide +kernel
theorem subd18_2_332 : subd18_2 [1, -1, -2] = true := by decide +kernel
theorem subd18_2_333 : subd18_2 [1, -1, -1] = true := by decide +kernel
theorem subd18_2_334 : subd18_2 [1, -1, 0] = true := by decide +kernel
theorem subd18_2_335 : subd18_2 [1, -1, 1] = true := by decide +kernel
theorem subd18_2_336 : subd18_2 [1, -1, 2] = true := by decide +kernel
theorem subd18_2_337 : subd18_2 [1, -1, 3] = true := by decide +kernel
theorem subd18_2_338 : subd18_2 [1, -1, 4] = true := by decide +kernel
theorem subd18_2_339 : subd18_2 [1, -1, 5] = true := by decide +kernel
theorem subd18_2_340 : subd18_2 [1, -1, 6] = true := by decide +kernel
theorem subd18_2_341 : subd18_2 [1, -1, 7] = true := by decide +kernel
theorem subd18_2_342 : subd18_2 [1, 0, -8] = true := by decide +kernel
theorem subd18_2_343 : subd18_2 [1, 0, -7] = true := by decide +kernel
theorem subd18_2_344 : subd18_2 [1, 0, -6] = true := by decide +kernel
theorem subd18_2_345 : subd18_2 [1, 0, -5] = true := by decide +kernel
theorem subd18_2_346 : subd18_2 [1, 0, -4] = true := by decide +kernel
theorem subd18_2_347 : subd18_2 [1, 0, -3] = true := by decide +kernel
theorem subd18_2_348 : subd18_2 [1, 0, -2] = true := by decide +kernel
theorem subd18_2_349 : subd18_2 [1, 0, -1] = true := by decide +kernel
theorem subd18_2_350 : subd18_2 [1, 0, 0] = true := by decide +kernel
theorem subd18_2_351 : subd18_2 [1, 0, 1] = true := by decide +kernel
theorem sbd18_2_10 : ∀ q ∈ blkd18_2_10, subd18_2 q = true := by
  unfold blkd18_2_10
  exact List.forall_mem_cons.2 ⟨subd18_2_320, List.forall_mem_cons.2 ⟨subd18_2_321, List.forall_mem_cons.2 ⟨subd18_2_322, List.forall_mem_cons.2 ⟨subd18_2_323, List.forall_mem_cons.2 ⟨subd18_2_324, List.forall_mem_cons.2 ⟨subd18_2_325, List.forall_mem_cons.2 ⟨subd18_2_326, List.forall_mem_cons.2 ⟨subd18_2_327, List.forall_mem_cons.2 ⟨subd18_2_328, List.forall_mem_cons.2 ⟨subd18_2_329, List.forall_mem_cons.2 ⟨subd18_2_330, List.forall_mem_cons.2 ⟨subd18_2_331, List.forall_mem_cons.2 ⟨subd18_2_332, List.forall_mem_cons.2 ⟨subd18_2_333, List.forall_mem_cons.2 ⟨subd18_2_334, List.forall_mem_cons.2 ⟨subd18_2_335, List.forall_mem_cons.2 ⟨subd18_2_336, List.forall_mem_cons.2 ⟨subd18_2_337, List.forall_mem_cons.2 ⟨subd18_2_338, List.forall_mem_cons.2 ⟨subd18_2_339, List.forall_mem_cons.2 ⟨subd18_2_340, List.forall_mem_cons.2 ⟨subd18_2_341, List.forall_mem_cons.2 ⟨subd18_2_342, List.forall_mem_cons.2 ⟨subd18_2_343, List.forall_mem_cons.2 ⟨subd18_2_344, List.forall_mem_cons.2 ⟨subd18_2_345, List.forall_mem_cons.2 ⟨subd18_2_346, List.forall_mem_cons.2 ⟨subd18_2_347, List.forall_mem_cons.2 ⟨subd18_2_348, List.forall_mem_cons.2 ⟨subd18_2_349, List.forall_mem_cons.2 ⟨subd18_2_350, List.forall_mem_cons.2 ⟨subd18_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_352 : subd18_2 [1, 0, 2] = true := by decide +kernel
theorem subd18_2_353 : subd18_2 [1, 0, 3] = true := by decide +kernel
theorem subd18_2_354 : subd18_2 [1, 0, 4] = true := by decide +kernel
theorem subd18_2_355 : subd18_2 [1, 0, 5] = true := by decide +kernel
theorem subd18_2_356 : subd18_2 [1, 0, 6] = true := by decide +kernel
theorem subd18_2_357 : subd18_2 [1, 0, 7] = true := by decide +kernel
theorem subd18_2_358 : subd18_2 [1, 1, -8] = true := by decide +kernel
theorem subd18_2_359 : subd18_2 [1, 1, -7] = true := by decide +kernel
theorem subd18_2_360 : subd18_2 [1, 1, -6] = true := by decide +kernel
theorem subd18_2_361 : subd18_2 [1, 1, -5] = true := by decide +kernel
theorem subd18_2_362 : subd18_2 [1, 1, -4] = true := by decide +kernel
theorem subd18_2_363 : subd18_2 [1, 1, -3] = true := by decide +kernel
theorem subd18_2_364 : subd18_2 [1, 1, -2] = true := by decide +kernel
theorem subd18_2_365 : subd18_2 [1, 1, -1] = true := by decide +kernel
theorem subd18_2_366 : subd18_2 [1, 1, 0] = true := by decide +kernel
theorem subd18_2_367 : subd18_2 [1, 1, 1] = true := by decide +kernel
theorem subd18_2_368 : subd18_2 [1, 1, 2] = true := by decide +kernel
theorem subd18_2_369 : subd18_2 [1, 1, 3] = true := by decide +kernel
theorem subd18_2_370 : subd18_2 [1, 1, 4] = true := by decide +kernel
theorem subd18_2_371 : subd18_2 [1, 1, 5] = true := by decide +kernel
theorem subd18_2_372 : subd18_2 [1, 1, 6] = true := by decide +kernel
theorem subd18_2_373 : subd18_2 [1, 1, 7] = true := by decide +kernel
theorem subd18_2_374 : subd18_2 [1, 2, -7] = true := by decide +kernel
theorem subd18_2_375 : subd18_2 [1, 2, -6] = true := by decide +kernel
theorem subd18_2_376 : subd18_2 [1, 2, -5] = true := by decide +kernel
theorem subd18_2_377 : subd18_2 [1, 2, -4] = true := by decide +kernel
theorem subd18_2_378 : subd18_2 [1, 2, -3] = true := by decide +kernel
theorem subd18_2_379 : subd18_2 [1, 2, -2] = true := by decide +kernel
theorem subd18_2_380 : subd18_2 [1, 2, -1] = true := by decide +kernel
theorem subd18_2_381 : subd18_2 [1, 2, 0] = true := by decide +kernel
theorem subd18_2_382 : subd18_2 [1, 2, 1] = true := by decide +kernel
theorem subd18_2_383 : subd18_2 [1, 2, 2] = true := by decide +kernel
theorem sbd18_2_11 : ∀ q ∈ blkd18_2_11, subd18_2 q = true := by
  unfold blkd18_2_11
  exact List.forall_mem_cons.2 ⟨subd18_2_352, List.forall_mem_cons.2 ⟨subd18_2_353, List.forall_mem_cons.2 ⟨subd18_2_354, List.forall_mem_cons.2 ⟨subd18_2_355, List.forall_mem_cons.2 ⟨subd18_2_356, List.forall_mem_cons.2 ⟨subd18_2_357, List.forall_mem_cons.2 ⟨subd18_2_358, List.forall_mem_cons.2 ⟨subd18_2_359, List.forall_mem_cons.2 ⟨subd18_2_360, List.forall_mem_cons.2 ⟨subd18_2_361, List.forall_mem_cons.2 ⟨subd18_2_362, List.forall_mem_cons.2 ⟨subd18_2_363, List.forall_mem_cons.2 ⟨subd18_2_364, List.forall_mem_cons.2 ⟨subd18_2_365, List.forall_mem_cons.2 ⟨subd18_2_366, List.forall_mem_cons.2 ⟨subd18_2_367, List.forall_mem_cons.2 ⟨subd18_2_368, List.forall_mem_cons.2 ⟨subd18_2_369, List.forall_mem_cons.2 ⟨subd18_2_370, List.forall_mem_cons.2 ⟨subd18_2_371, List.forall_mem_cons.2 ⟨subd18_2_372, List.forall_mem_cons.2 ⟨subd18_2_373, List.forall_mem_cons.2 ⟨subd18_2_374, List.forall_mem_cons.2 ⟨subd18_2_375, List.forall_mem_cons.2 ⟨subd18_2_376, List.forall_mem_cons.2 ⟨subd18_2_377, List.forall_mem_cons.2 ⟨subd18_2_378, List.forall_mem_cons.2 ⟨subd18_2_379, List.forall_mem_cons.2 ⟨subd18_2_380, List.forall_mem_cons.2 ⟨subd18_2_381, List.forall_mem_cons.2 ⟨subd18_2_382, List.forall_mem_cons.2 ⟨subd18_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
