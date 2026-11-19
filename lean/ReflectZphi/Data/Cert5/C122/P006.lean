import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_4_0 : subd4_4 [-4, -5] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-4, -4] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [-4, -3] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [-4, -2] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [-4, -1] = true := by decide +kernel
theorem subd4_4_5 : subd4_4 [-4, 0] = true := by decide +kernel
theorem subd4_4_6 : subd4_4 [-4, 1] = true := by decide +kernel
theorem subd4_4_7 : subd4_4 [-3, -6] = true := by decide +kernel
theorem subd4_4_8 : subd4_4 [-3, -5] = true := by decide +kernel
theorem subd4_4_9 : subd4_4 [-3, -4] = true := by decide +kernel
theorem subd4_4_10 : subd4_4 [-3, -3] = true := by decide +kernel
theorem subd4_4_11 : subd4_4 [-3, -2] = true := by decide +kernel
theorem subd4_4_12 : subd4_4 [-3, -1] = true := by decide +kernel
theorem subd4_4_13 : subd4_4 [-3, 0] = true := by decide +kernel
theorem subd4_4_14 : subd4_4 [-3, 1] = true := by decide +kernel
theorem subd4_4_15 : subd4_4 [-3, 2] = true := by decide +kernel
theorem subd4_4_16 : subd4_4 [-3, 3] = true := by decide +kernel
theorem subd4_4_17 : subd4_4 [-2, -6] = true := by decide +kernel
theorem subd4_4_18 : subd4_4 [-2, -5] = true := by decide +kernel
theorem subd4_4_19 : subd4_4 [-2, -4] = true := by decide +kernel
theorem subd4_4_20 : subd4_4 [-2, -3] = true := by decide +kernel
theorem subd4_4_21 : subd4_4 [-2, -2] = true := by decide +kernel
theorem subd4_4_22 : subd4_4 [-2, -1] = true := by decide +kernel
theorem subd4_4_23 : subd4_4 [-2, 0] = true := by decide +kernel
theorem subd4_4_24 : subd4_4 [-2, 1] = true := by decide +kernel
theorem subd4_4_25 : subd4_4 [-2, 2] = true := by decide +kernel
theorem subd4_4_26 : subd4_4 [-2, 3] = true := by decide +kernel
theorem subd4_4_27 : subd4_4 [-2, 4] = true := by decide +kernel
theorem subd4_4_28 : subd4_4 [-1, -6] = true := by decide +kernel
theorem subd4_4_29 : subd4_4 [-1, -5] = true := by decide +kernel
theorem subd4_4_30 : subd4_4 [-1, -4] = true := by decide +kernel
theorem subd4_4_31 : subd4_4 [-1, -3] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_cons.2 ⟨subd4_4_5, List.forall_mem_cons.2 ⟨subd4_4_6, List.forall_mem_cons.2 ⟨subd4_4_7, List.forall_mem_cons.2 ⟨subd4_4_8, List.forall_mem_cons.2 ⟨subd4_4_9, List.forall_mem_cons.2 ⟨subd4_4_10, List.forall_mem_cons.2 ⟨subd4_4_11, List.forall_mem_cons.2 ⟨subd4_4_12, List.forall_mem_cons.2 ⟨subd4_4_13, List.forall_mem_cons.2 ⟨subd4_4_14, List.forall_mem_cons.2 ⟨subd4_4_15, List.forall_mem_cons.2 ⟨subd4_4_16, List.forall_mem_cons.2 ⟨subd4_4_17, List.forall_mem_cons.2 ⟨subd4_4_18, List.forall_mem_cons.2 ⟨subd4_4_19, List.forall_mem_cons.2 ⟨subd4_4_20, List.forall_mem_cons.2 ⟨subd4_4_21, List.forall_mem_cons.2 ⟨subd4_4_22, List.forall_mem_cons.2 ⟨subd4_4_23, List.forall_mem_cons.2 ⟨subd4_4_24, List.forall_mem_cons.2 ⟨subd4_4_25, List.forall_mem_cons.2 ⟨subd4_4_26, List.forall_mem_cons.2 ⟨subd4_4_27, List.forall_mem_cons.2 ⟨subd4_4_28, List.forall_mem_cons.2 ⟨subd4_4_29, List.forall_mem_cons.2 ⟨subd4_4_30, List.forall_mem_cons.2 ⟨subd4_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_32 : subd4_4 [-1, -2] = true := by decide +kernel
theorem subd4_4_33 : subd4_4 [-1, -1] = true := by decide +kernel
theorem subd4_4_34 : subd4_4 [-1, 0, -7] = true := by decide +kernel
theorem subd4_4_35 : subd4_4 [-1, 0, -6] = true := by decide +kernel
theorem subd4_4_36 : subd4_4 [-1, 0, -5] = true := by decide +kernel
theorem subd4_4_37 : subd4_4 [-1, 0, -4] = true := by decide +kernel
theorem subd4_4_38 : subd4_4 [-1, 0, -3] = true := by decide +kernel
theorem subd4_4_39 : subd4_4 [-1, 0, -2] = true := by decide +kernel
theorem subd4_4_40 : subd4_4 [-1, 0, -1] = true := by decide +kernel
theorem subd4_4_41 : subd4_4 [-1, 0, 0] = true := by decide +kernel
theorem subd4_4_42 : subd4_4 [-1, 0, 1] = true := by decide +kernel
theorem subd4_4_43 : subd4_4 [-1, 0, 2] = true := by decide +kernel
theorem subd4_4_44 : subd4_4 [-1, 0, 3] = true := by decide +kernel
theorem subd4_4_45 : subd4_4 [-1, 0, 4] = true := by decide +kernel
theorem subd4_4_46 : subd4_4 [-1, 0, 5] = true := by decide +kernel
theorem subd4_4_47 : subd4_4 [-1, 0, 6] = true := by decide +kernel
theorem subd4_4_48 : subd4_4 [-1, 1] = true := by decide +kernel
theorem subd4_4_49 : subd4_4 [-1, 2] = true := by decide +kernel
theorem subd4_4_50 : subd4_4 [-1, 3] = true := by decide +kernel
theorem subd4_4_51 : subd4_4 [-1, 4] = true := by decide +kernel
theorem subd4_4_52 : subd4_4 [0, -6] = true := by decide +kernel
theorem subd4_4_53 : subd4_4 [0, -5] = true := by decide +kernel
theorem subd4_4_54 : subd4_4 [0, -4] = true := by decide +kernel
theorem subd4_4_55 : subd4_4 [0, -3] = true := by decide +kernel
theorem subd4_4_56 : subd4_4 [0, -2] = true := by decide +kernel
theorem subd4_4_57 : subd4_4 [0, -1, -7] = true := by decide +kernel
theorem subd4_4_58 : subd4_4 [0, -1, -6] = true := by decide +kernel
theorem subd4_4_59 : subd4_4 [0, -1, -5] = true := by decide +kernel
theorem subd4_4_60 : subd4_4 [0, -1, -4] = true := by decide +kernel
theorem subd4_4_61 : subd4_4 [0, -1, -3] = true := by decide +kernel
theorem subd4_4_62 : subd4_4 [0, -1, -2] = true := by decide +kernel
theorem subd4_4_63 : subd4_4 [0, -1, -1] = true := by decide +kernel
theorem sbd4_4_1 : ∀ q ∈ blkd4_4_1, subd4_4 q = true := by
  unfold blkd4_4_1
  exact List.forall_mem_cons.2 ⟨subd4_4_32, List.forall_mem_cons.2 ⟨subd4_4_33, List.forall_mem_cons.2 ⟨subd4_4_34, List.forall_mem_cons.2 ⟨subd4_4_35, List.forall_mem_cons.2 ⟨subd4_4_36, List.forall_mem_cons.2 ⟨subd4_4_37, List.forall_mem_cons.2 ⟨subd4_4_38, List.forall_mem_cons.2 ⟨subd4_4_39, List.forall_mem_cons.2 ⟨subd4_4_40, List.forall_mem_cons.2 ⟨subd4_4_41, List.forall_mem_cons.2 ⟨subd4_4_42, List.forall_mem_cons.2 ⟨subd4_4_43, List.forall_mem_cons.2 ⟨subd4_4_44, List.forall_mem_cons.2 ⟨subd4_4_45, List.forall_mem_cons.2 ⟨subd4_4_46, List.forall_mem_cons.2 ⟨subd4_4_47, List.forall_mem_cons.2 ⟨subd4_4_48, List.forall_mem_cons.2 ⟨subd4_4_49, List.forall_mem_cons.2 ⟨subd4_4_50, List.forall_mem_cons.2 ⟨subd4_4_51, List.forall_mem_cons.2 ⟨subd4_4_52, List.forall_mem_cons.2 ⟨subd4_4_53, List.forall_mem_cons.2 ⟨subd4_4_54, List.forall_mem_cons.2 ⟨subd4_4_55, List.forall_mem_cons.2 ⟨subd4_4_56, List.forall_mem_cons.2 ⟨subd4_4_57, List.forall_mem_cons.2 ⟨subd4_4_58, List.forall_mem_cons.2 ⟨subd4_4_59, List.forall_mem_cons.2 ⟨subd4_4_60, List.forall_mem_cons.2 ⟨subd4_4_61, List.forall_mem_cons.2 ⟨subd4_4_62, List.forall_mem_cons.2 ⟨subd4_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_64 : subd4_4 [0, -1, 0] = true := by decide +kernel
theorem subd4_4_65 : subd4_4 [0, -1, 1] = true := by decide +kernel
theorem subd4_4_66 : subd4_4 [0, -1, 2] = true := by decide +kernel
theorem subd4_4_67 : subd4_4 [0, -1, 3] = true := by decide +kernel
theorem subd4_4_68 : subd4_4 [0, -1, 4] = true := by decide +kernel
theorem subd4_4_69 : subd4_4 [0, -1, 5] = true := by decide +kernel
theorem subd4_4_70 : subd4_4 [0, -1, 6] = true := by decide +kernel
theorem subd4_4_71 : subd4_4 [0, 0, -7] = true := by decide +kernel
theorem subd4_4_72 : subd4_4 [0, 0, -6] = true := by decide +kernel
theorem subd4_4_73 : subd4_4 [0, 0, -5] = true := by decide +kernel
theorem subd4_4_74 : subd4_4 [0, 0, -4] = true := by decide +kernel
theorem subd4_4_75 : subd4_4 [0, 0, -3] = true := by decide +kernel
theorem subd4_4_76 : subd4_4 [0, 0, -2] = true := by decide +kernel
theorem subd4_4_77 : subd4_4 [0, 0, -1] = true := by decide +kernel
theorem subd4_4_78 : subd4_4 [0, 0, 0] = true := by decide +kernel
theorem subd4_4_79 : subd4_4 [0, 0, 1] = true := by decide +kernel
theorem subd4_4_80 : subd4_4 [0, 0, 2] = true := by decide +kernel
theorem subd4_4_81 : subd4_4 [0, 0, 3] = true := by decide +kernel
theorem subd4_4_82 : subd4_4 [0, 0, 4] = true := by decide +kernel
theorem subd4_4_83 : subd4_4 [0, 0, 5] = true := by decide +kernel
theorem subd4_4_84 : subd4_4 [0, 0, 6] = true := by decide +kernel
theorem subd4_4_85 : subd4_4 [0, 1, -7] = true := by decide +kernel
theorem subd4_4_86 : subd4_4 [0, 1, -6] = true := by decide +kernel
theorem subd4_4_87 : subd4_4 [0, 1, -5] = true := by decide +kernel
theorem subd4_4_88 : subd4_4 [0, 1, -4] = true := by decide +kernel
theorem subd4_4_89 : subd4_4 [0, 1, -3] = true := by decide +kernel
theorem subd4_4_90 : subd4_4 [0, 1, -2] = true := by decide +kernel
theorem subd4_4_91 : subd4_4 [0, 1, -1] = true := by decide +kernel
theorem subd4_4_92 : subd4_4 [0, 1, 0] = true := by decide +kernel
theorem subd4_4_93 : subd4_4 [0, 1, 1] = true := by decide +kernel
theorem subd4_4_94 : subd4_4 [0, 1, 2] = true := by decide +kernel
theorem subd4_4_95 : subd4_4 [0, 1, 3] = true := by decide +kernel
theorem sbd4_4_2 : ∀ q ∈ blkd4_4_2, subd4_4 q = true := by
  unfold blkd4_4_2
  exact List.forall_mem_cons.2 ⟨subd4_4_64, List.forall_mem_cons.2 ⟨subd4_4_65, List.forall_mem_cons.2 ⟨subd4_4_66, List.forall_mem_cons.2 ⟨subd4_4_67, List.forall_mem_cons.2 ⟨subd4_4_68, List.forall_mem_cons.2 ⟨subd4_4_69, List.forall_mem_cons.2 ⟨subd4_4_70, List.forall_mem_cons.2 ⟨subd4_4_71, List.forall_mem_cons.2 ⟨subd4_4_72, List.forall_mem_cons.2 ⟨subd4_4_73, List.forall_mem_cons.2 ⟨subd4_4_74, List.forall_mem_cons.2 ⟨subd4_4_75, List.forall_mem_cons.2 ⟨subd4_4_76, List.forall_mem_cons.2 ⟨subd4_4_77, List.forall_mem_cons.2 ⟨subd4_4_78, List.forall_mem_cons.2 ⟨subd4_4_79, List.forall_mem_cons.2 ⟨subd4_4_80, List.forall_mem_cons.2 ⟨subd4_4_81, List.forall_mem_cons.2 ⟨subd4_4_82, List.forall_mem_cons.2 ⟨subd4_4_83, List.forall_mem_cons.2 ⟨subd4_4_84, List.forall_mem_cons.2 ⟨subd4_4_85, List.forall_mem_cons.2 ⟨subd4_4_86, List.forall_mem_cons.2 ⟨subd4_4_87, List.forall_mem_cons.2 ⟨subd4_4_88, List.forall_mem_cons.2 ⟨subd4_4_89, List.forall_mem_cons.2 ⟨subd4_4_90, List.forall_mem_cons.2 ⟨subd4_4_91, List.forall_mem_cons.2 ⟨subd4_4_92, List.forall_mem_cons.2 ⟨subd4_4_93, List.forall_mem_cons.2 ⟨subd4_4_94, List.forall_mem_cons.2 ⟨subd4_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_96 : subd4_4 [0, 1, 4] = true := by decide +kernel
theorem subd4_4_97 : subd4_4 [0, 1, 5] = true := by decide +kernel
theorem subd4_4_98 : subd4_4 [0, 1, 6] = true := by decide +kernel
theorem subd4_4_99 : subd4_4 [0, 2] = true := by decide +kernel
theorem subd4_4_100 : subd4_4 [0, 3] = true := by decide +kernel
theorem subd4_4_101 : subd4_4 [0, 4] = true := by decide +kernel
theorem subd4_4_102 : subd4_4 [0, 5] = true := by decide +kernel
theorem subd4_4_103 : subd4_4 [1, -5] = true := by decide +kernel
theorem subd4_4_104 : subd4_4 [1, -4] = true := by decide +kernel
theorem subd4_4_105 : subd4_4 [1, -3] = true := by decide +kernel
theorem subd4_4_106 : subd4_4 [1, -2] = true := by decide +kernel
theorem subd4_4_107 : subd4_4 [1, -1] = true := by decide +kernel
theorem subd4_4_108 : subd4_4 [1, 0, -7] = true := by decide +kernel
theorem subd4_4_109 : subd4_4 [1, 0, -6] = true := by decide +kernel
theorem subd4_4_110 : subd4_4 [1, 0, -5] = true := by decide +kernel
theorem subd4_4_111 : subd4_4 [1, 0, -4] = true := by decide +kernel
theorem subd4_4_112 : subd4_4 [1, 0, -3] = true := by decide +kernel
theorem subd4_4_113 : subd4_4 [1, 0, -2] = true := by decide +kernel
theorem subd4_4_114 : subd4_4 [1, 0, -1] = true := by decide +kernel
theorem subd4_4_115 : subd4_4 [1, 0, 0] = true := by decide +kernel
theorem subd4_4_116 : subd4_4 [1, 0, 1] = true := by decide +kernel
theorem subd4_4_117 : subd4_4 [1, 0, 2] = true := by decide +kernel
theorem subd4_4_118 : subd4_4 [1, 0, 3] = true := by decide +kernel
theorem subd4_4_119 : subd4_4 [1, 0, 4] = true := by decide +kernel
theorem subd4_4_120 : subd4_4 [1, 0, 5] = true := by decide +kernel
theorem subd4_4_121 : subd4_4 [1, 0, 6] = true := by decide +kernel
theorem subd4_4_122 : subd4_4 [1, 1] = true := by decide +kernel
theorem subd4_4_123 : subd4_4 [1, 2] = true := by decide +kernel
theorem subd4_4_124 : subd4_4 [1, 3] = true := by decide +kernel
theorem subd4_4_125 : subd4_4 [1, 4] = true := by decide +kernel
theorem subd4_4_126 : subd4_4 [1, 5] = true := by decide +kernel
theorem subd4_4_127 : subd4_4 [2, -5] = true := by decide +kernel
theorem sbd4_4_3 : ∀ q ∈ blkd4_4_3, subd4_4 q = true := by
  unfold blkd4_4_3
  exact List.forall_mem_cons.2 ⟨subd4_4_96, List.forall_mem_cons.2 ⟨subd4_4_97, List.forall_mem_cons.2 ⟨subd4_4_98, List.forall_mem_cons.2 ⟨subd4_4_99, List.forall_mem_cons.2 ⟨subd4_4_100, List.forall_mem_cons.2 ⟨subd4_4_101, List.forall_mem_cons.2 ⟨subd4_4_102, List.forall_mem_cons.2 ⟨subd4_4_103, List.forall_mem_cons.2 ⟨subd4_4_104, List.forall_mem_cons.2 ⟨subd4_4_105, List.forall_mem_cons.2 ⟨subd4_4_106, List.forall_mem_cons.2 ⟨subd4_4_107, List.forall_mem_cons.2 ⟨subd4_4_108, List.forall_mem_cons.2 ⟨subd4_4_109, List.forall_mem_cons.2 ⟨subd4_4_110, List.forall_mem_cons.2 ⟨subd4_4_111, List.forall_mem_cons.2 ⟨subd4_4_112, List.forall_mem_cons.2 ⟨subd4_4_113, List.forall_mem_cons.2 ⟨subd4_4_114, List.forall_mem_cons.2 ⟨subd4_4_115, List.forall_mem_cons.2 ⟨subd4_4_116, List.forall_mem_cons.2 ⟨subd4_4_117, List.forall_mem_cons.2 ⟨subd4_4_118, List.forall_mem_cons.2 ⟨subd4_4_119, List.forall_mem_cons.2 ⟨subd4_4_120, List.forall_mem_cons.2 ⟨subd4_4_121, List.forall_mem_cons.2 ⟨subd4_4_122, List.forall_mem_cons.2 ⟨subd4_4_123, List.forall_mem_cons.2 ⟨subd4_4_124, List.forall_mem_cons.2 ⟨subd4_4_125, List.forall_mem_cons.2 ⟨subd4_4_126, List.forall_mem_cons.2 ⟨subd4_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_128 : subd4_4 [2, -4] = true := by decide +kernel
theorem subd4_4_129 : subd4_4 [2, -3] = true := by decide +kernel
theorem subd4_4_130 : subd4_4 [2, -2] = true := by decide +kernel
theorem subd4_4_131 : subd4_4 [2, -1] = true := by decide +kernel
theorem subd4_4_132 : subd4_4 [2, 0] = true := by decide +kernel
theorem subd4_4_133 : subd4_4 [2, 1] = true := by decide +kernel
theorem subd4_4_134 : subd4_4 [2, 2] = true := by decide +kernel
theorem subd4_4_135 : subd4_4 [2, 3] = true := by decide +kernel
theorem subd4_4_136 : subd4_4 [2, 4] = true := by decide +kernel
theorem subd4_4_137 : subd4_4 [2, 5] = true := by decide +kernel
theorem subd4_4_138 : subd4_4 [3, -4] = true := by decide +kernel
theorem subd4_4_139 : subd4_4 [3, -3] = true := by decide +kernel
theorem subd4_4_140 : subd4_4 [3, -2] = true := by decide +kernel
theorem subd4_4_141 : subd4_4 [3, -1] = true := by decide +kernel
theorem subd4_4_142 : subd4_4 [3, 0] = true := by decide +kernel
theorem subd4_4_143 : subd4_4 [3, 1] = true := by decide +kernel
theorem subd4_4_144 : subd4_4 [3, 2] = true := by decide +kernel
theorem subd4_4_145 : subd4_4 [3, 3] = true := by decide +kernel
theorem subd4_4_146 : subd4_4 [3, 4] = true := by decide +kernel
theorem subd4_4_147 : subd4_4 [3, 5] = true := by decide +kernel
theorem subd4_4_148 : subd4_4 [4, -2] = true := by decide +kernel
theorem subd4_4_149 : subd4_4 [4, -1] = true := by decide +kernel
theorem subd4_4_150 : subd4_4 [4, 0] = true := by decide +kernel
theorem subd4_4_151 : subd4_4 [4, 1] = true := by decide +kernel
theorem subd4_4_152 : subd4_4 [4, 2] = true := by decide +kernel
theorem subd4_4_153 : subd4_4 [4, 3] = true := by decide +kernel
theorem subd4_4_154 : subd4_4 [4, 4] = true := by decide +kernel
theorem sbd4_4_4 : ∀ q ∈ blkd4_4_4, subd4_4 q = true := by
  unfold blkd4_4_4
  exact List.forall_mem_cons.2 ⟨subd4_4_128, List.forall_mem_cons.2 ⟨subd4_4_129, List.forall_mem_cons.2 ⟨subd4_4_130, List.forall_mem_cons.2 ⟨subd4_4_131, List.forall_mem_cons.2 ⟨subd4_4_132, List.forall_mem_cons.2 ⟨subd4_4_133, List.forall_mem_cons.2 ⟨subd4_4_134, List.forall_mem_cons.2 ⟨subd4_4_135, List.forall_mem_cons.2 ⟨subd4_4_136, List.forall_mem_cons.2 ⟨subd4_4_137, List.forall_mem_cons.2 ⟨subd4_4_138, List.forall_mem_cons.2 ⟨subd4_4_139, List.forall_mem_cons.2 ⟨subd4_4_140, List.forall_mem_cons.2 ⟨subd4_4_141, List.forall_mem_cons.2 ⟨subd4_4_142, List.forall_mem_cons.2 ⟨subd4_4_143, List.forall_mem_cons.2 ⟨subd4_4_144, List.forall_mem_cons.2 ⟨subd4_4_145, List.forall_mem_cons.2 ⟨subd4_4_146, List.forall_mem_cons.2 ⟨subd4_4_147, List.forall_mem_cons.2 ⟨subd4_4_148, List.forall_mem_cons.2 ⟨subd4_4_149, List.forall_mem_cons.2 ⟨subd4_4_150, List.forall_mem_cons.2 ⟨subd4_4_151, List.forall_mem_cons.2 ⟨subd4_4_152, List.forall_mem_cons.2 ⟨subd4_4_153, List.forall_mem_cons.2 ⟨subd4_4_154, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
