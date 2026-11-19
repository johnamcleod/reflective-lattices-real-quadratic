import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_3_0 : subd5_3 [-5] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-4, -3] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-4, -2] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-4, -1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-4, 0] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-4, 1] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-4, 2] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-4, 3] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-4, 4] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-4, 5] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-3, -4] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-3, -3] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-3, -2] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-3, -1] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-3, 0] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-3, 1] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [-3, 2] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [-3, 3] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [-3, 4] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [-3, 5] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [-2, -5] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [-2, -4] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [-2, 3] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [-2, 4] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [-2, 5] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [-2, 6] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [-1, -6] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [-1, -5] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [-1, -1, -6] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [-1, -1, -5] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [-1, -1, -4] = true := by decide +kernel
theorem subd5_3_40 : subd5_3 [-1, -1, -3] = true := by decide +kernel
theorem subd5_3_41 : subd5_3 [-1, -1, -2] = true := by decide +kernel
theorem subd5_3_42 : subd5_3 [-1, -1, -1] = true := by decide +kernel
theorem subd5_3_43 : subd5_3 [-1, -1, 0] = true := by decide +kernel
theorem subd5_3_44 : subd5_3 [-1, -1, 1] = true := by decide +kernel
theorem subd5_3_45 : subd5_3 [-1, -1, 2] = true := by decide +kernel
theorem subd5_3_46 : subd5_3 [-1, -1, 3] = true := by decide +kernel
theorem subd5_3_47 : subd5_3 [-1, -1, 4] = true := by decide +kernel
theorem subd5_3_48 : subd5_3 [-1, -1, 5] = true := by decide +kernel
theorem subd5_3_49 : subd5_3 [-1, -1, 6] = true := by decide +kernel
theorem subd5_3_50 : subd5_3 [-1, 0, -7] = true := by decide +kernel
theorem subd5_3_51 : subd5_3 [-1, 0, -6] = true := by decide +kernel
theorem subd5_3_52 : subd5_3 [-1, 0, -5] = true := by decide +kernel
theorem subd5_3_53 : subd5_3 [-1, 0, -4] = true := by decide +kernel
theorem subd5_3_54 : subd5_3 [-1, 0, -3] = true := by decide +kernel
theorem subd5_3_55 : subd5_3 [-1, 0, -2] = true := by decide +kernel
theorem subd5_3_56 : subd5_3 [-1, 0, -1] = true := by decide +kernel
theorem subd5_3_57 : subd5_3 [-1, 0, 0] = true := by decide +kernel
theorem subd5_3_58 : subd5_3 [-1, 0, 1] = true := by decide +kernel
theorem subd5_3_59 : subd5_3 [-1, 0, 2] = true := by decide +kernel
theorem subd5_3_60 : subd5_3 [-1, 0, 3] = true := by decide +kernel
theorem subd5_3_61 : subd5_3 [-1, 0, 4] = true := by decide +kernel
theorem subd5_3_62 : subd5_3 [-1, 0, 5] = true := by decide +kernel
theorem subd5_3_63 : subd5_3 [-1, 0, 6] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_cons.2 ⟨subd5_3_40, List.forall_mem_cons.2 ⟨subd5_3_41, List.forall_mem_cons.2 ⟨subd5_3_42, List.forall_mem_cons.2 ⟨subd5_3_43, List.forall_mem_cons.2 ⟨subd5_3_44, List.forall_mem_cons.2 ⟨subd5_3_45, List.forall_mem_cons.2 ⟨subd5_3_46, List.forall_mem_cons.2 ⟨subd5_3_47, List.forall_mem_cons.2 ⟨subd5_3_48, List.forall_mem_cons.2 ⟨subd5_3_49, List.forall_mem_cons.2 ⟨subd5_3_50, List.forall_mem_cons.2 ⟨subd5_3_51, List.forall_mem_cons.2 ⟨subd5_3_52, List.forall_mem_cons.2 ⟨subd5_3_53, List.forall_mem_cons.2 ⟨subd5_3_54, List.forall_mem_cons.2 ⟨subd5_3_55, List.forall_mem_cons.2 ⟨subd5_3_56, List.forall_mem_cons.2 ⟨subd5_3_57, List.forall_mem_cons.2 ⟨subd5_3_58, List.forall_mem_cons.2 ⟨subd5_3_59, List.forall_mem_cons.2 ⟨subd5_3_60, List.forall_mem_cons.2 ⟨subd5_3_61, List.forall_mem_cons.2 ⟨subd5_3_62, List.forall_mem_cons.2 ⟨subd5_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_64 : subd5_3 [-1, 1, -7] = true := by decide +kernel
theorem subd5_3_65 : subd5_3 [-1, 1, -6] = true := by decide +kernel
theorem subd5_3_66 : subd5_3 [-1, 1, -5] = true := by decide +kernel
theorem subd5_3_67 : subd5_3 [-1, 1, -4] = true := by decide +kernel
theorem subd5_3_68 : subd5_3 [-1, 1, -3] = true := by decide +kernel
theorem subd5_3_69 : subd5_3 [-1, 1, -2] = true := by decide +kernel
theorem subd5_3_70 : subd5_3 [-1, 1, -1] = true := by decide +kernel
theorem subd5_3_71 : subd5_3 [-1, 1, 0] = true := by decide +kernel
theorem subd5_3_72 : subd5_3 [-1, 1, 1] = true := by decide +kernel
theorem subd5_3_73 : subd5_3 [-1, 1, 2] = true := by decide +kernel
theorem subd5_3_74 : subd5_3 [-1, 1, 3] = true := by decide +kernel
theorem subd5_3_75 : subd5_3 [-1, 1, 4] = true := by decide +kernel
theorem subd5_3_76 : subd5_3 [-1, 1, 5] = true := by decide +kernel
theorem subd5_3_77 : subd5_3 [-1, 2, -8] = true := by decide +kernel
theorem subd5_3_78 : subd5_3 [-1, 2, -7] = true := by decide +kernel
theorem subd5_3_79 : subd5_3 [-1, 2, -6] = true := by decide +kernel
theorem subd5_3_80 : subd5_3 [-1, 2, -5] = true := by decide +kernel
theorem subd5_3_81 : subd5_3 [-1, 2, -4] = true := by decide +kernel
theorem subd5_3_82 : subd5_3 [-1, 2, -3] = true := by decide +kernel
theorem subd5_3_83 : subd5_3 [-1, 2, -2] = true := by decide +kernel
theorem subd5_3_84 : subd5_3 [-1, 2, -1] = true := by decide +kernel
theorem subd5_3_85 : subd5_3 [-1, 2, 0] = true := by decide +kernel
theorem subd5_3_86 : subd5_3 [-1, 2, 1] = true := by decide +kernel
theorem subd5_3_87 : subd5_3 [-1, 2, 2] = true := by decide +kernel
theorem subd5_3_88 : subd5_3 [-1, 2, 3] = true := by decide +kernel
theorem subd5_3_89 : subd5_3 [-1, 2, 4] = true := by decide +kernel
theorem subd5_3_90 : subd5_3 [-1, 2, 5] = true := by decide +kernel
theorem subd5_3_91 : subd5_3 [-1, 3] = true := by decide +kernel
theorem subd5_3_92 : subd5_3 [-1, 4] = true := by decide +kernel
theorem subd5_3_93 : subd5_3 [-1, 5] = true := by decide +kernel
theorem subd5_3_94 : subd5_3 [-1, 6] = true := by decide +kernel
theorem subd5_3_95 : subd5_3 [0, -6] = true := by decide +kernel
theorem sbd5_3_2 : ∀ q ∈ blkd5_3_2, subd5_3 q = true := by
  unfold blkd5_3_2
  exact List.forall_mem_cons.2 ⟨subd5_3_64, List.forall_mem_cons.2 ⟨subd5_3_65, List.forall_mem_cons.2 ⟨subd5_3_66, List.forall_mem_cons.2 ⟨subd5_3_67, List.forall_mem_cons.2 ⟨subd5_3_68, List.forall_mem_cons.2 ⟨subd5_3_69, List.forall_mem_cons.2 ⟨subd5_3_70, List.forall_mem_cons.2 ⟨subd5_3_71, List.forall_mem_cons.2 ⟨subd5_3_72, List.forall_mem_cons.2 ⟨subd5_3_73, List.forall_mem_cons.2 ⟨subd5_3_74, List.forall_mem_cons.2 ⟨subd5_3_75, List.forall_mem_cons.2 ⟨subd5_3_76, List.forall_mem_cons.2 ⟨subd5_3_77, List.forall_mem_cons.2 ⟨subd5_3_78, List.forall_mem_cons.2 ⟨subd5_3_79, List.forall_mem_cons.2 ⟨subd5_3_80, List.forall_mem_cons.2 ⟨subd5_3_81, List.forall_mem_cons.2 ⟨subd5_3_82, List.forall_mem_cons.2 ⟨subd5_3_83, List.forall_mem_cons.2 ⟨subd5_3_84, List.forall_mem_cons.2 ⟨subd5_3_85, List.forall_mem_cons.2 ⟨subd5_3_86, List.forall_mem_cons.2 ⟨subd5_3_87, List.forall_mem_cons.2 ⟨subd5_3_88, List.forall_mem_cons.2 ⟨subd5_3_89, List.forall_mem_cons.2 ⟨subd5_3_90, List.forall_mem_cons.2 ⟨subd5_3_91, List.forall_mem_cons.2 ⟨subd5_3_92, List.forall_mem_cons.2 ⟨subd5_3_93, List.forall_mem_cons.2 ⟨subd5_3_94, List.forall_mem_cons.2 ⟨subd5_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_96 : subd5_3 [0, -5] = true := by decide +kernel
theorem subd5_3_97 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_98 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_99 : subd5_3 [0, -2, -6] = true := by decide +kernel
theorem subd5_3_100 : subd5_3 [0, -2, -5] = true := by decide +kernel
theorem subd5_3_101 : subd5_3 [0, -2, -4] = true := by decide +kernel
theorem subd5_3_102 : subd5_3 [0, -2, -3] = true := by decide +kernel
theorem subd5_3_103 : subd5_3 [0, -2, -2] = true := by decide +kernel
theorem subd5_3_104 : subd5_3 [0, -2, -1] = true := by decide +kernel
theorem subd5_3_105 : subd5_3 [0, -2, 0] = true := by decide +kernel
theorem subd5_3_106 : subd5_3 [0, -2, 1] = true := by decide +kernel
theorem subd5_3_107 : subd5_3 [0, -2, 2] = true := by decide +kernel
theorem subd5_3_108 : subd5_3 [0, -2, 3] = true := by decide +kernel
theorem subd5_3_109 : subd5_3 [0, -2, 4] = true := by decide +kernel
theorem subd5_3_110 : subd5_3 [0, -2, 5] = true := by decide +kernel
theorem subd5_3_111 : subd5_3 [0, -2, 6] = true := by decide +kernel
theorem subd5_3_112 : subd5_3 [0, -1, -7] = true := by decide +kernel
theorem subd5_3_113 : subd5_3 [0, -1, -6] = true := by decide +kernel
theorem subd5_3_114 : subd5_3 [0, -1, -5] = true := by decide +kernel
theorem subd5_3_115 : subd5_3 [0, -1, -4] = true := by decide +kernel
theorem subd5_3_116 : subd5_3 [0, -1, -3] = true := by decide +kernel
theorem subd5_3_117 : subd5_3 [0, -1, -2] = true := by decide +kernel
theorem subd5_3_118 : subd5_3 [0, -1, -1] = true := by decide +kernel
theorem subd5_3_119 : subd5_3 [0, -1, 0] = true := by decide +kernel
theorem subd5_3_120 : subd5_3 [0, -1, 1] = true := by decide +kernel
theorem subd5_3_121 : subd5_3 [0, -1, 2] = true := by decide +kernel
theorem subd5_3_122 : subd5_3 [0, -1, 3] = true := by decide +kernel
theorem subd5_3_123 : subd5_3 [0, -1, 4] = true := by decide +kernel
theorem subd5_3_124 : subd5_3 [0, -1, 5] = true := by decide +kernel
theorem subd5_3_125 : subd5_3 [0, -1, 6] = true := by decide +kernel
theorem subd5_3_126 : subd5_3 [0, 0, -7] = true := by decide +kernel
theorem subd5_3_127 : subd5_3 [0, 0, -6] = true := by decide +kernel
theorem sbd5_3_3 : ∀ q ∈ blkd5_3_3, subd5_3 q = true := by
  unfold blkd5_3_3
  exact List.forall_mem_cons.2 ⟨subd5_3_96, List.forall_mem_cons.2 ⟨subd5_3_97, List.forall_mem_cons.2 ⟨subd5_3_98, List.forall_mem_cons.2 ⟨subd5_3_99, List.forall_mem_cons.2 ⟨subd5_3_100, List.forall_mem_cons.2 ⟨subd5_3_101, List.forall_mem_cons.2 ⟨subd5_3_102, List.forall_mem_cons.2 ⟨subd5_3_103, List.forall_mem_cons.2 ⟨subd5_3_104, List.forall_mem_cons.2 ⟨subd5_3_105, List.forall_mem_cons.2 ⟨subd5_3_106, List.forall_mem_cons.2 ⟨subd5_3_107, List.forall_mem_cons.2 ⟨subd5_3_108, List.forall_mem_cons.2 ⟨subd5_3_109, List.forall_mem_cons.2 ⟨subd5_3_110, List.forall_mem_cons.2 ⟨subd5_3_111, List.forall_mem_cons.2 ⟨subd5_3_112, List.forall_mem_cons.2 ⟨subd5_3_113, List.forall_mem_cons.2 ⟨subd5_3_114, List.forall_mem_cons.2 ⟨subd5_3_115, List.forall_mem_cons.2 ⟨subd5_3_116, List.forall_mem_cons.2 ⟨subd5_3_117, List.forall_mem_cons.2 ⟨subd5_3_118, List.forall_mem_cons.2 ⟨subd5_3_119, List.forall_mem_cons.2 ⟨subd5_3_120, List.forall_mem_cons.2 ⟨subd5_3_121, List.forall_mem_cons.2 ⟨subd5_3_122, List.forall_mem_cons.2 ⟨subd5_3_123, List.forall_mem_cons.2 ⟨subd5_3_124, List.forall_mem_cons.2 ⟨subd5_3_125, List.forall_mem_cons.2 ⟨subd5_3_126, List.forall_mem_cons.2 ⟨subd5_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_128 : subd5_3 [0, 0, -5] = true := by decide +kernel
theorem subd5_3_129 : subd5_3 [0, 0, -4] = true := by decide +kernel
theorem subd5_3_130 : subd5_3 [0, 0, -3] = true := by decide +kernel
theorem subd5_3_131 : subd5_3 [0, 0, -2] = true := by decide +kernel
theorem subd5_3_132 : subd5_3 [0, 0, -1] = true := by decide +kernel
theorem subd5_3_133 : subd5_3 [0, 0, 0] = true := by decide +kernel
theorem subd5_3_134 : subd5_3 [0, 0, 1] = true := by decide +kernel
theorem subd5_3_135 : subd5_3 [0, 0, 2] = true := by decide +kernel
theorem subd5_3_136 : subd5_3 [0, 0, 3] = true := by decide +kernel
theorem subd5_3_137 : subd5_3 [0, 0, 4] = true := by decide +kernel
theorem subd5_3_138 : subd5_3 [0, 0, 5] = true := by decide +kernel
theorem subd5_3_139 : subd5_3 [0, 0, 6] = true := by decide +kernel
theorem subd5_3_140 : subd5_3 [0, 1, -7] = true := by decide +kernel
theorem subd5_3_141 : subd5_3 [0, 1, -6] = true := by decide +kernel
theorem subd5_3_142 : subd5_3 [0, 1, -5] = true := by decide +kernel
theorem subd5_3_143 : subd5_3 [0, 1, -4] = true := by decide +kernel
theorem subd5_3_144 : subd5_3 [0, 1, -3] = true := by decide +kernel
theorem subd5_3_145 : subd5_3 [0, 1, -2] = true := by decide +kernel
theorem subd5_3_146 : subd5_3 [0, 1, -1] = true := by decide +kernel
theorem subd5_3_147 : subd5_3 [0, 1, 0] = true := by decide +kernel
theorem subd5_3_148 : subd5_3 [0, 1, 1] = true := by decide +kernel
theorem subd5_3_149 : subd5_3 [0, 1, 2] = true := by decide +kernel
theorem subd5_3_150 : subd5_3 [0, 1, 3] = true := by decide +kernel
theorem subd5_3_151 : subd5_3 [0, 1, 4] = true := by decide +kernel
theorem subd5_3_152 : subd5_3 [0, 1, 5] = true := by decide +kernel
theorem subd5_3_153 : subd5_3 [0, 1, 6] = true := by decide +kernel
theorem subd5_3_154 : subd5_3 [0, 2, -7] = true := by decide +kernel
theorem subd5_3_155 : subd5_3 [0, 2, -6] = true := by decide +kernel
theorem subd5_3_156 : subd5_3 [0, 2, -5] = true := by decide +kernel
theorem subd5_3_157 : subd5_3 [0, 2, -4] = true := by decide +kernel
theorem subd5_3_158 : subd5_3 [0, 2, -3] = true := by decide +kernel
theorem subd5_3_159 : subd5_3 [0, 2, -2] = true := by decide +kernel
theorem sbd5_3_4 : ∀ q ∈ blkd5_3_4, subd5_3 q = true := by
  unfold blkd5_3_4
  exact List.forall_mem_cons.2 ⟨subd5_3_128, List.forall_mem_cons.2 ⟨subd5_3_129, List.forall_mem_cons.2 ⟨subd5_3_130, List.forall_mem_cons.2 ⟨subd5_3_131, List.forall_mem_cons.2 ⟨subd5_3_132, List.forall_mem_cons.2 ⟨subd5_3_133, List.forall_mem_cons.2 ⟨subd5_3_134, List.forall_mem_cons.2 ⟨subd5_3_135, List.forall_mem_cons.2 ⟨subd5_3_136, List.forall_mem_cons.2 ⟨subd5_3_137, List.forall_mem_cons.2 ⟨subd5_3_138, List.forall_mem_cons.2 ⟨subd5_3_139, List.forall_mem_cons.2 ⟨subd5_3_140, List.forall_mem_cons.2 ⟨subd5_3_141, List.forall_mem_cons.2 ⟨subd5_3_142, List.forall_mem_cons.2 ⟨subd5_3_143, List.forall_mem_cons.2 ⟨subd5_3_144, List.forall_mem_cons.2 ⟨subd5_3_145, List.forall_mem_cons.2 ⟨subd5_3_146, List.forall_mem_cons.2 ⟨subd5_3_147, List.forall_mem_cons.2 ⟨subd5_3_148, List.forall_mem_cons.2 ⟨subd5_3_149, List.forall_mem_cons.2 ⟨subd5_3_150, List.forall_mem_cons.2 ⟨subd5_3_151, List.forall_mem_cons.2 ⟨subd5_3_152, List.forall_mem_cons.2 ⟨subd5_3_153, List.forall_mem_cons.2 ⟨subd5_3_154, List.forall_mem_cons.2 ⟨subd5_3_155, List.forall_mem_cons.2 ⟨subd5_3_156, List.forall_mem_cons.2 ⟨subd5_3_157, List.forall_mem_cons.2 ⟨subd5_3_158, List.forall_mem_cons.2 ⟨subd5_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_160 : subd5_3 [0, 2, -1] = true := by decide +kernel
theorem subd5_3_161 : subd5_3 [0, 2, 0] = true := by decide +kernel
theorem subd5_3_162 : subd5_3 [0, 2, 1] = true := by decide +kernel
theorem subd5_3_163 : subd5_3 [0, 2, 2] = true := by decide +kernel
theorem subd5_3_164 : subd5_3 [0, 2, 3] = true := by decide +kernel
theorem subd5_3_165 : subd5_3 [0, 2, 4] = true := by decide +kernel
theorem subd5_3_166 : subd5_3 [0, 2, 5] = true := by decide +kernel
theorem subd5_3_167 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_168 : subd5_3 [0, 4] = true := by decide +kernel
theorem subd5_3_169 : subd5_3 [0, 5] = true := by decide +kernel
theorem subd5_3_170 : subd5_3 [1, -7] = true := by decide +kernel
theorem subd5_3_171 : subd5_3 [1, -6] = true := by decide +kernel
theorem subd5_3_172 : subd5_3 [1, -5] = true := by decide +kernel
theorem subd5_3_173 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_174 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_175 : subd5_3 [1, -2, -6] = true := by decide +kernel
theorem subd5_3_176 : subd5_3 [1, -2, -5] = true := by decide +kernel
theorem subd5_3_177 : subd5_3 [1, -2, -4] = true := by decide +kernel
theorem subd5_3_178 : subd5_3 [1, -2, -3] = true := by decide +kernel
theorem subd5_3_179 : subd5_3 [1, -2, -2] = true := by decide +kernel
theorem subd5_3_180 : subd5_3 [1, -2, -1] = true := by decide +kernel
theorem subd5_3_181 : subd5_3 [1, -2, 0] = true := by decide +kernel
theorem subd5_3_182 : subd5_3 [1, -2, 1] = true := by decide +kernel
theorem subd5_3_183 : subd5_3 [1, -2, 2] = true := by decide +kernel
theorem subd5_3_184 : subd5_3 [1, -2, 3] = true := by decide +kernel
theorem subd5_3_185 : subd5_3 [1, -2, 4] = true := by decide +kernel
theorem subd5_3_186 : subd5_3 [1, -2, 5] = true := by decide +kernel
theorem subd5_3_187 : subd5_3 [1, -2, 6] = true := by decide +kernel
theorem subd5_3_188 : subd5_3 [1, -2, 7] = true := by decide +kernel
theorem subd5_3_189 : subd5_3 [1, -1, -6] = true := by decide +kernel
theorem subd5_3_190 : subd5_3 [1, -1, -5] = true := by decide +kernel
theorem subd5_3_191 : subd5_3 [1, -1, -4] = true := by decide +kernel
theorem sbd5_3_5 : ∀ q ∈ blkd5_3_5, subd5_3 q = true := by
  unfold blkd5_3_5
  exact List.forall_mem_cons.2 ⟨subd5_3_160, List.forall_mem_cons.2 ⟨subd5_3_161, List.forall_mem_cons.2 ⟨subd5_3_162, List.forall_mem_cons.2 ⟨subd5_3_163, List.forall_mem_cons.2 ⟨subd5_3_164, List.forall_mem_cons.2 ⟨subd5_3_165, List.forall_mem_cons.2 ⟨subd5_3_166, List.forall_mem_cons.2 ⟨subd5_3_167, List.forall_mem_cons.2 ⟨subd5_3_168, List.forall_mem_cons.2 ⟨subd5_3_169, List.forall_mem_cons.2 ⟨subd5_3_170, List.forall_mem_cons.2 ⟨subd5_3_171, List.forall_mem_cons.2 ⟨subd5_3_172, List.forall_mem_cons.2 ⟨subd5_3_173, List.forall_mem_cons.2 ⟨subd5_3_174, List.forall_mem_cons.2 ⟨subd5_3_175, List.forall_mem_cons.2 ⟨subd5_3_176, List.forall_mem_cons.2 ⟨subd5_3_177, List.forall_mem_cons.2 ⟨subd5_3_178, List.forall_mem_cons.2 ⟨subd5_3_179, List.forall_mem_cons.2 ⟨subd5_3_180, List.forall_mem_cons.2 ⟨subd5_3_181, List.forall_mem_cons.2 ⟨subd5_3_182, List.forall_mem_cons.2 ⟨subd5_3_183, List.forall_mem_cons.2 ⟨subd5_3_184, List.forall_mem_cons.2 ⟨subd5_3_185, List.forall_mem_cons.2 ⟨subd5_3_186, List.forall_mem_cons.2 ⟨subd5_3_187, List.forall_mem_cons.2 ⟨subd5_3_188, List.forall_mem_cons.2 ⟨subd5_3_189, List.forall_mem_cons.2 ⟨subd5_3_190, List.forall_mem_cons.2 ⟨subd5_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_192 : subd5_3 [1, -1, -3] = true := by decide +kernel
theorem subd5_3_193 : subd5_3 [1, -1, -2] = true := by decide +kernel
theorem subd5_3_194 : subd5_3 [1, -1, -1] = true := by decide +kernel
theorem subd5_3_195 : subd5_3 [1, -1, 0] = true := by decide +kernel
theorem subd5_3_196 : subd5_3 [1, -1, 1] = true := by decide +kernel
theorem subd5_3_197 : subd5_3 [1, -1, 2] = true := by decide +kernel
theorem subd5_3_198 : subd5_3 [1, -1, 3] = true := by decide +kernel
theorem subd5_3_199 : subd5_3 [1, -1, 4] = true := by decide +kernel
theorem subd5_3_200 : subd5_3 [1, -1, 5] = true := by decide +kernel
theorem subd5_3_201 : subd5_3 [1, -1, 6] = true := by decide +kernel
theorem subd5_3_202 : subd5_3 [1, 0, -7] = true := by decide +kernel
theorem subd5_3_203 : subd5_3 [1, 0, -6] = true := by decide +kernel
theorem subd5_3_204 : subd5_3 [1, 0, -5] = true := by decide +kernel
theorem subd5_3_205 : subd5_3 [1, 0, -4] = true := by decide +kernel
theorem subd5_3_206 : subd5_3 [1, 0, -3] = true := by decide +kernel
theorem subd5_3_207 : subd5_3 [1, 0, -2] = true := by decide +kernel
theorem subd5_3_208 : subd5_3 [1, 0, -1] = true := by decide +kernel
theorem subd5_3_209 : subd5_3 [1, 0, 0] = true := by decide +kernel
theorem subd5_3_210 : subd5_3 [1, 0, 1] = true := by decide +kernel
theorem subd5_3_211 : subd5_3 [1, 0, 2] = true := by decide +kernel
theorem subd5_3_212 : subd5_3 [1, 0, 3] = true := by decide +kernel
theorem subd5_3_213 : subd5_3 [1, 0, 4] = true := by decide +kernel
theorem subd5_3_214 : subd5_3 [1, 0, 5] = true := by decide +kernel
theorem subd5_3_215 : subd5_3 [1, 0, 6] = true := by decide +kernel
theorem subd5_3_216 : subd5_3 [1, 1, -7] = true := by decide +kernel
theorem subd5_3_217 : subd5_3 [1, 1, -6] = true := by decide +kernel
theorem subd5_3_218 : subd5_3 [1, 1, -5] = true := by decide +kernel
theorem subd5_3_219 : subd5_3 [1, 1, -4] = true := by decide +kernel
theorem subd5_3_220 : subd5_3 [1, 1, -3] = true := by decide +kernel
theorem subd5_3_221 : subd5_3 [1, 1, -2] = true := by decide +kernel
theorem subd5_3_222 : subd5_3 [1, 1, -1] = true := by decide +kernel
theorem subd5_3_223 : subd5_3 [1, 1, 0] = true := by decide +kernel
theorem sbd5_3_6 : ∀ q ∈ blkd5_3_6, subd5_3 q = true := by
  unfold blkd5_3_6
  exact List.forall_mem_cons.2 ⟨subd5_3_192, List.forall_mem_cons.2 ⟨subd5_3_193, List.forall_mem_cons.2 ⟨subd5_3_194, List.forall_mem_cons.2 ⟨subd5_3_195, List.forall_mem_cons.2 ⟨subd5_3_196, List.forall_mem_cons.2 ⟨subd5_3_197, List.forall_mem_cons.2 ⟨subd5_3_198, List.forall_mem_cons.2 ⟨subd5_3_199, List.forall_mem_cons.2 ⟨subd5_3_200, List.forall_mem_cons.2 ⟨subd5_3_201, List.forall_mem_cons.2 ⟨subd5_3_202, List.forall_mem_cons.2 ⟨subd5_3_203, List.forall_mem_cons.2 ⟨subd5_3_204, List.forall_mem_cons.2 ⟨subd5_3_205, List.forall_mem_cons.2 ⟨subd5_3_206, List.forall_mem_cons.2 ⟨subd5_3_207, List.forall_mem_cons.2 ⟨subd5_3_208, List.forall_mem_cons.2 ⟨subd5_3_209, List.forall_mem_cons.2 ⟨subd5_3_210, List.forall_mem_cons.2 ⟨subd5_3_211, List.forall_mem_cons.2 ⟨subd5_3_212, List.forall_mem_cons.2 ⟨subd5_3_213, List.forall_mem_cons.2 ⟨subd5_3_214, List.forall_mem_cons.2 ⟨subd5_3_215, List.forall_mem_cons.2 ⟨subd5_3_216, List.forall_mem_cons.2 ⟨subd5_3_217, List.forall_mem_cons.2 ⟨subd5_3_218, List.forall_mem_cons.2 ⟨subd5_3_219, List.forall_mem_cons.2 ⟨subd5_3_220, List.forall_mem_cons.2 ⟨subd5_3_221, List.forall_mem_cons.2 ⟨subd5_3_222, List.forall_mem_cons.2 ⟨subd5_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
