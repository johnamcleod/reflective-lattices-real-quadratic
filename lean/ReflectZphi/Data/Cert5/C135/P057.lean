import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [-3] = true := by decide +kernel
theorem subd9_7_1 : subd9_7 [-2, -4] = true := by decide +kernel
theorem subd9_7_2 : subd9_7 [-2, -3] = true := by decide +kernel
theorem subd9_7_3 : subd9_7 [-2, -2] = true := by decide +kernel
theorem subd9_7_4 : subd9_7 [-2, -1, -8] = true := by decide +kernel
theorem subd9_7_5 : subd9_7 [-2, -1, -7] = true := by decide +kernel
theorem subd9_7_6 : subd9_7 [-2, -1, -6] = true := by decide +kernel
theorem subd9_7_7 : subd9_7 [-2, -1, -5] = true := by decide +kernel
theorem subd9_7_8 : subd9_7 [-2, -1, -4] = true := by decide +kernel
theorem subd9_7_9 : subd9_7 [-2, -1, -3] = true := by decide +kernel
theorem subd9_7_10 : subd9_7 [-2, -1, -2] = true := by decide +kernel
theorem subd9_7_11 : subd9_7 [-2, -1, -1] = true := by decide +kernel
theorem subd9_7_12 : subd9_7 [-2, -1, 0] = true := by decide +kernel
theorem subd9_7_13 : subd9_7 [-2, -1, 1] = true := by decide +kernel
theorem subd9_7_14 : subd9_7 [-2, -1, 2] = true := by decide +kernel
theorem subd9_7_15 : subd9_7 [-2, -1, 3] = true := by decide +kernel
theorem subd9_7_16 : subd9_7 [-2, -1, 4] = true := by decide +kernel
theorem subd9_7_17 : subd9_7 [-2, -1, 5] = true := by decide +kernel
theorem subd9_7_18 : subd9_7 [-2, -1, 6] = true := by decide +kernel
theorem subd9_7_19 : subd9_7 [-2, -1, 7] = true := by decide +kernel
theorem subd9_7_20 : subd9_7 [-2, 0, -8] = true := by decide +kernel
theorem subd9_7_21 : subd9_7 [-2, 0, -7] = true := by decide +kernel
theorem subd9_7_22 : subd9_7 [-2, 0, -6] = true := by decide +kernel
theorem subd9_7_23 : subd9_7 [-2, 0, -5] = true := by decide +kernel
theorem subd9_7_24 : subd9_7 [-2, 0, -4] = true := by decide +kernel
theorem subd9_7_25 : subd9_7 [-2, 0, -3] = true := by decide +kernel
theorem subd9_7_26 : subd9_7 [-2, 0, -2] = true := by decide +kernel
theorem subd9_7_27 : subd9_7 [-2, 0, -1] = true := by decide +kernel
theorem subd9_7_28 : subd9_7 [-2, 0, 0] = true := by decide +kernel
theorem subd9_7_29 : subd9_7 [-2, 0, 1] = true := by decide +kernel
theorem subd9_7_30 : subd9_7 [-2, 0, 2] = true := by decide +kernel
theorem subd9_7_31 : subd9_7 [-2, 0, 3] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_cons.2 ⟨subd9_7_1, List.forall_mem_cons.2 ⟨subd9_7_2, List.forall_mem_cons.2 ⟨subd9_7_3, List.forall_mem_cons.2 ⟨subd9_7_4, List.forall_mem_cons.2 ⟨subd9_7_5, List.forall_mem_cons.2 ⟨subd9_7_6, List.forall_mem_cons.2 ⟨subd9_7_7, List.forall_mem_cons.2 ⟨subd9_7_8, List.forall_mem_cons.2 ⟨subd9_7_9, List.forall_mem_cons.2 ⟨subd9_7_10, List.forall_mem_cons.2 ⟨subd9_7_11, List.forall_mem_cons.2 ⟨subd9_7_12, List.forall_mem_cons.2 ⟨subd9_7_13, List.forall_mem_cons.2 ⟨subd9_7_14, List.forall_mem_cons.2 ⟨subd9_7_15, List.forall_mem_cons.2 ⟨subd9_7_16, List.forall_mem_cons.2 ⟨subd9_7_17, List.forall_mem_cons.2 ⟨subd9_7_18, List.forall_mem_cons.2 ⟨subd9_7_19, List.forall_mem_cons.2 ⟨subd9_7_20, List.forall_mem_cons.2 ⟨subd9_7_21, List.forall_mem_cons.2 ⟨subd9_7_22, List.forall_mem_cons.2 ⟨subd9_7_23, List.forall_mem_cons.2 ⟨subd9_7_24, List.forall_mem_cons.2 ⟨subd9_7_25, List.forall_mem_cons.2 ⟨subd9_7_26, List.forall_mem_cons.2 ⟨subd9_7_27, List.forall_mem_cons.2 ⟨subd9_7_28, List.forall_mem_cons.2 ⟨subd9_7_29, List.forall_mem_cons.2 ⟨subd9_7_30, List.forall_mem_cons.2 ⟨subd9_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_32 : subd9_7 [-2, 0, 4] = true := by decide +kernel
theorem subd9_7_33 : subd9_7 [-2, 0, 5] = true := by decide +kernel
theorem subd9_7_34 : subd9_7 [-2, 0, 6] = true := by decide +kernel
theorem subd9_7_35 : subd9_7 [-2, 0, 7] = true := by decide +kernel
theorem subd9_7_36 : subd9_7 [-2, 1, -6] = true := by decide +kernel
theorem subd9_7_37 : subd9_7 [-2, 1, -5] = true := by decide +kernel
theorem subd9_7_38 : subd9_7 [-2, 1, -4] = true := by decide +kernel
theorem subd9_7_39 : subd9_7 [-2, 1, -3] = true := by decide +kernel
theorem subd9_7_40 : subd9_7 [-2, 1, -2] = true := by decide +kernel
theorem subd9_7_41 : subd9_7 [-2, 1, -1] = true := by decide +kernel
theorem subd9_7_42 : subd9_7 [-2, 1, 0] = true := by decide +kernel
theorem subd9_7_43 : subd9_7 [-2, 1, 1] = true := by decide +kernel
theorem subd9_7_44 : subd9_7 [-2, 1, 2] = true := by decide +kernel
theorem subd9_7_45 : subd9_7 [-2, 1, 3] = true := by decide +kernel
theorem subd9_7_46 : subd9_7 [-2, 1, 4] = true := by decide +kernel
theorem subd9_7_47 : subd9_7 [-2, 1, 5] = true := by decide +kernel
theorem subd9_7_48 : subd9_7 [-2, 1, 6] = true := by decide +kernel
theorem subd9_7_49 : subd9_7 [-2, 1, 7] = true := by decide +kernel
theorem subd9_7_50 : subd9_7 [-2, 2] = true := by decide +kernel
theorem subd9_7_51 : subd9_7 [-1, -4] = true := by decide +kernel
theorem subd9_7_52 : subd9_7 [-1, -3] = true := by decide +kernel
theorem subd9_7_53 : subd9_7 [-1, -2, -9] = true := by decide +kernel
theorem subd9_7_54 : subd9_7 [-1, -2, -8] = true := by decide +kernel
theorem subd9_7_55 : subd9_7 [-1, -2, -7] = true := by decide +kernel
theorem subd9_7_56 : subd9_7 [-1, -2, -6] = true := by decide +kernel
theorem subd9_7_57 : subd9_7 [-1, -2, -5] = true := by decide +kernel
theorem subd9_7_58 : subd9_7 [-1, -2, -4] = true := by decide +kernel
theorem subd9_7_59 : subd9_7 [-1, -2, -3] = true := by decide +kernel
theorem subd9_7_60 : subd9_7 [-1, -2, -2] = true := by decide +kernel
theorem subd9_7_61 : subd9_7 [-1, -2, -1] = true := by decide +kernel
theorem subd9_7_62 : subd9_7 [-1, -2, 0] = true := by decide +kernel
theorem subd9_7_63 : subd9_7 [-1, -2, 1] = true := by decide +kernel
theorem sbd9_7_1 : ∀ q ∈ blkd9_7_1, subd9_7 q = true := by
  unfold blkd9_7_1
  exact List.forall_mem_cons.2 ⟨subd9_7_32, List.forall_mem_cons.2 ⟨subd9_7_33, List.forall_mem_cons.2 ⟨subd9_7_34, List.forall_mem_cons.2 ⟨subd9_7_35, List.forall_mem_cons.2 ⟨subd9_7_36, List.forall_mem_cons.2 ⟨subd9_7_37, List.forall_mem_cons.2 ⟨subd9_7_38, List.forall_mem_cons.2 ⟨subd9_7_39, List.forall_mem_cons.2 ⟨subd9_7_40, List.forall_mem_cons.2 ⟨subd9_7_41, List.forall_mem_cons.2 ⟨subd9_7_42, List.forall_mem_cons.2 ⟨subd9_7_43, List.forall_mem_cons.2 ⟨subd9_7_44, List.forall_mem_cons.2 ⟨subd9_7_45, List.forall_mem_cons.2 ⟨subd9_7_46, List.forall_mem_cons.2 ⟨subd9_7_47, List.forall_mem_cons.2 ⟨subd9_7_48, List.forall_mem_cons.2 ⟨subd9_7_49, List.forall_mem_cons.2 ⟨subd9_7_50, List.forall_mem_cons.2 ⟨subd9_7_51, List.forall_mem_cons.2 ⟨subd9_7_52, List.forall_mem_cons.2 ⟨subd9_7_53, List.forall_mem_cons.2 ⟨subd9_7_54, List.forall_mem_cons.2 ⟨subd9_7_55, List.forall_mem_cons.2 ⟨subd9_7_56, List.forall_mem_cons.2 ⟨subd9_7_57, List.forall_mem_cons.2 ⟨subd9_7_58, List.forall_mem_cons.2 ⟨subd9_7_59, List.forall_mem_cons.2 ⟨subd9_7_60, List.forall_mem_cons.2 ⟨subd9_7_61, List.forall_mem_cons.2 ⟨subd9_7_62, List.forall_mem_cons.2 ⟨subd9_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_64 : subd9_7 [-1, -2, 2] = true := by decide +kernel
theorem subd9_7_65 : subd9_7 [-1, -2, 3] = true := by decide +kernel
theorem subd9_7_66 : subd9_7 [-1, -2, 4] = true := by decide +kernel
theorem subd9_7_67 : subd9_7 [-1, -2, 5] = true := by decide +kernel
theorem subd9_7_68 : subd9_7 [-1, -2, 6] = true := by decide +kernel
theorem subd9_7_69 : subd9_7 [-1, -1, -9] = true := by decide +kernel
theorem subd9_7_70 : subd9_7 [-1, -1, -8] = true := by decide +kernel
theorem subd9_7_71 : subd9_7 [-1, -1, -7] = true := by decide +kernel
theorem subd9_7_72 : subd9_7 [-1, -1, -6] = true := by decide +kernel
theorem subd9_7_73 : subd9_7 [-1, -1, -5] = true := by decide +kernel
theorem subd9_7_74 : subd9_7 [-1, -1, -4] = true := by decide +kernel
theorem subd9_7_75 : subd9_7 [-1, -1, -3] = true := by decide +kernel
theorem subd9_7_76 : subd9_7 [-1, -1, -2] = true := by decide +kernel
theorem subd9_7_77 : subd9_7 [-1, -1, -1] = true := by decide +kernel
theorem subd9_7_78 : subd9_7 [-1, -1, 0] = true := by decide +kernel
theorem subd9_7_79 : subd9_7 [-1, -1, 1] = true := by decide +kernel
theorem subd9_7_80 : subd9_7 [-1, -1, 2] = true := by decide +kernel
theorem subd9_7_81 : subd9_7 [-1, -1, 3] = true := by decide +kernel
theorem subd9_7_82 : subd9_7 [-1, -1, 4] = true := by decide +kernel
theorem subd9_7_83 : subd9_7 [-1, -1, 5] = true := by decide +kernel
theorem subd9_7_84 : subd9_7 [-1, -1, 6] = true := by decide +kernel
theorem subd9_7_85 : subd9_7 [-1, -1, 7] = true := by decide +kernel
theorem subd9_7_86 : subd9_7 [-1, -1, 8] = true := by decide +kernel
theorem subd9_7_87 : subd9_7 [-1, 0, -9] = true := by decide +kernel
theorem subd9_7_88 : subd9_7 [-1, 0, -8] = true := by decide +kernel
theorem subd9_7_89 : subd9_7 [-1, 0, -7] = true := by decide +kernel
theorem subd9_7_90 : subd9_7 [-1, 0, -6] = true := by decide +kernel
theorem subd9_7_91 : subd9_7 [-1, 0, -5] = true := by decide +kernel
theorem subd9_7_92 : subd9_7 [-1, 0, -4] = true := by decide +kernel
theorem subd9_7_93 : subd9_7 [-1, 0, -3] = true := by decide +kernel
theorem subd9_7_94 : subd9_7 [-1, 0, -2] = true := by decide +kernel
theorem subd9_7_95 : subd9_7 [-1, 0, -1] = true := by decide +kernel
theorem sbd9_7_2 : ∀ q ∈ blkd9_7_2, subd9_7 q = true := by
  unfold blkd9_7_2
  exact List.forall_mem_cons.2 ⟨subd9_7_64, List.forall_mem_cons.2 ⟨subd9_7_65, List.forall_mem_cons.2 ⟨subd9_7_66, List.forall_mem_cons.2 ⟨subd9_7_67, List.forall_mem_cons.2 ⟨subd9_7_68, List.forall_mem_cons.2 ⟨subd9_7_69, List.forall_mem_cons.2 ⟨subd9_7_70, List.forall_mem_cons.2 ⟨subd9_7_71, List.forall_mem_cons.2 ⟨subd9_7_72, List.forall_mem_cons.2 ⟨subd9_7_73, List.forall_mem_cons.2 ⟨subd9_7_74, List.forall_mem_cons.2 ⟨subd9_7_75, List.forall_mem_cons.2 ⟨subd9_7_76, List.forall_mem_cons.2 ⟨subd9_7_77, List.forall_mem_cons.2 ⟨subd9_7_78, List.forall_mem_cons.2 ⟨subd9_7_79, List.forall_mem_cons.2 ⟨subd9_7_80, List.forall_mem_cons.2 ⟨subd9_7_81, List.forall_mem_cons.2 ⟨subd9_7_82, List.forall_mem_cons.2 ⟨subd9_7_83, List.forall_mem_cons.2 ⟨subd9_7_84, List.forall_mem_cons.2 ⟨subd9_7_85, List.forall_mem_cons.2 ⟨subd9_7_86, List.forall_mem_cons.2 ⟨subd9_7_87, List.forall_mem_cons.2 ⟨subd9_7_88, List.forall_mem_cons.2 ⟨subd9_7_89, List.forall_mem_cons.2 ⟨subd9_7_90, List.forall_mem_cons.2 ⟨subd9_7_91, List.forall_mem_cons.2 ⟨subd9_7_92, List.forall_mem_cons.2 ⟨subd9_7_93, List.forall_mem_cons.2 ⟨subd9_7_94, List.forall_mem_cons.2 ⟨subd9_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_96 : subd9_7 [-1, 0, 0] = true := by decide +kernel
theorem subd9_7_97 : subd9_7 [-1, 0, 1] = true := by decide +kernel
theorem subd9_7_98 : subd9_7 [-1, 0, 2] = true := by decide +kernel
theorem subd9_7_99 : subd9_7 [-1, 0, 3] = true := by decide +kernel
theorem subd9_7_100 : subd9_7 [-1, 0, 4] = true := by decide +kernel
theorem subd9_7_101 : subd9_7 [-1, 0, 5] = true := by decide +kernel
theorem subd9_7_102 : subd9_7 [-1, 0, 6] = true := by decide +kernel
theorem subd9_7_103 : subd9_7 [-1, 0, 7] = true := by decide +kernel
theorem subd9_7_104 : subd9_7 [-1, 0, 8] = true := by decide +kernel
theorem subd9_7_105 : subd9_7 [-1, 0, 9] = true := by decide +kernel
theorem subd9_7_106 : subd9_7 [-1, 1, -8] = true := by decide +kernel
theorem subd9_7_107 : subd9_7 [-1, 1, -7] = true := by decide +kernel
theorem subd9_7_108 : subd9_7 [-1, 1, -6] = true := by decide +kernel
theorem subd9_7_109 : subd9_7 [-1, 1, -5] = true := by decide +kernel
theorem subd9_7_110 : subd9_7 [-1, 1, -4] = true := by decide +kernel
theorem subd9_7_111 : subd9_7 [-1, 1, -3] = true := by decide +kernel
theorem subd9_7_112 : subd9_7 [-1, 1, -2] = true := by decide +kernel
theorem subd9_7_113 : subd9_7 [-1, 1, -1] = true := by decide +kernel
theorem subd9_7_114 : subd9_7 [-1, 1, 0] = true := by decide +kernel
theorem subd9_7_115 : subd9_7 [-1, 1, 1] = true := by decide +kernel
theorem subd9_7_116 : subd9_7 [-1, 1, 2] = true := by decide +kernel
theorem subd9_7_117 : subd9_7 [-1, 1, 3] = true := by decide +kernel
theorem subd9_7_118 : subd9_7 [-1, 1, 4] = true := by decide +kernel
theorem subd9_7_119 : subd9_7 [-1, 1, 5] = true := by decide +kernel
theorem subd9_7_120 : subd9_7 [-1, 1, 6] = true := by decide +kernel
theorem subd9_7_121 : subd9_7 [-1, 1, 7] = true := by decide +kernel
theorem subd9_7_122 : subd9_7 [-1, 1, 8] = true := by decide +kernel
theorem subd9_7_123 : subd9_7 [-1, 2, -6] = true := by decide +kernel
theorem subd9_7_124 : subd9_7 [-1, 2, -5] = true := by decide +kernel
theorem subd9_7_125 : subd9_7 [-1, 2, -4] = true := by decide +kernel
theorem subd9_7_126 : subd9_7 [-1, 2, -3] = true := by decide +kernel
theorem subd9_7_127 : subd9_7 [-1, 2, -2] = true := by decide +kernel
theorem sbd9_7_3 : ∀ q ∈ blkd9_7_3, subd9_7 q = true := by
  unfold blkd9_7_3
  exact List.forall_mem_cons.2 ⟨subd9_7_96, List.forall_mem_cons.2 ⟨subd9_7_97, List.forall_mem_cons.2 ⟨subd9_7_98, List.forall_mem_cons.2 ⟨subd9_7_99, List.forall_mem_cons.2 ⟨subd9_7_100, List.forall_mem_cons.2 ⟨subd9_7_101, List.forall_mem_cons.2 ⟨subd9_7_102, List.forall_mem_cons.2 ⟨subd9_7_103, List.forall_mem_cons.2 ⟨subd9_7_104, List.forall_mem_cons.2 ⟨subd9_7_105, List.forall_mem_cons.2 ⟨subd9_7_106, List.forall_mem_cons.2 ⟨subd9_7_107, List.forall_mem_cons.2 ⟨subd9_7_108, List.forall_mem_cons.2 ⟨subd9_7_109, List.forall_mem_cons.2 ⟨subd9_7_110, List.forall_mem_cons.2 ⟨subd9_7_111, List.forall_mem_cons.2 ⟨subd9_7_112, List.forall_mem_cons.2 ⟨subd9_7_113, List.forall_mem_cons.2 ⟨subd9_7_114, List.forall_mem_cons.2 ⟨subd9_7_115, List.forall_mem_cons.2 ⟨subd9_7_116, List.forall_mem_cons.2 ⟨subd9_7_117, List.forall_mem_cons.2 ⟨subd9_7_118, List.forall_mem_cons.2 ⟨subd9_7_119, List.forall_mem_cons.2 ⟨subd9_7_120, List.forall_mem_cons.2 ⟨subd9_7_121, List.forall_mem_cons.2 ⟨subd9_7_122, List.forall_mem_cons.2 ⟨subd9_7_123, List.forall_mem_cons.2 ⟨subd9_7_124, List.forall_mem_cons.2 ⟨subd9_7_125, List.forall_mem_cons.2 ⟨subd9_7_126, List.forall_mem_cons.2 ⟨subd9_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_128 : subd9_7 [-1, 2, -1] = true := by decide +kernel
theorem subd9_7_129 : subd9_7 [-1, 2, 0] = true := by decide +kernel
theorem subd9_7_130 : subd9_7 [-1, 2, 1] = true := by decide +kernel
theorem subd9_7_131 : subd9_7 [-1, 2, 2] = true := by decide +kernel
theorem subd9_7_132 : subd9_7 [-1, 2, 3] = true := by decide +kernel
theorem subd9_7_133 : subd9_7 [-1, 2, 4] = true := by decide +kernel
theorem subd9_7_134 : subd9_7 [-1, 2, 5] = true := by decide +kernel
theorem subd9_7_135 : subd9_7 [-1, 2, 6] = true := by decide +kernel
theorem subd9_7_136 : subd9_7 [-1, 2, 7] = true := by decide +kernel
theorem subd9_7_137 : subd9_7 [-1, 3] = true := by decide +kernel
theorem subd9_7_138 : subd9_7 [0, -4] = true := by decide +kernel
theorem subd9_7_139 : subd9_7 [0, -3] = true := by decide +kernel
theorem subd9_7_140 : subd9_7 [0, -2, -9] = true := by decide +kernel
theorem subd9_7_141 : subd9_7 [0, -2, -8] = true := by decide +kernel
theorem subd9_7_142 : subd9_7 [0, -2, -7] = true := by decide +kernel
theorem subd9_7_143 : subd9_7 [0, -2, -6] = true := by decide +kernel
theorem subd9_7_144 : subd9_7 [0, -2, -5] = true := by decide +kernel
theorem subd9_7_145 : subd9_7 [0, -2, -4] = true := by decide +kernel
theorem subd9_7_146 : subd9_7 [0, -2, -3] = true := by decide +kernel
theorem subd9_7_147 : subd9_7 [0, -2, -2] = true := by decide +kernel
theorem subd9_7_148 : subd9_7 [0, -2, -1] = true := by decide +kernel
theorem subd9_7_149 : subd9_7 [0, -2, 0] = true := by decide +kernel
theorem subd9_7_150 : subd9_7 [0, -2, 1] = true := by decide +kernel
theorem subd9_7_151 : subd9_7 [0, -2, 2] = true := by decide +kernel
theorem subd9_7_152 : subd9_7 [0, -2, 3] = true := by decide +kernel
theorem subd9_7_153 : subd9_7 [0, -2, 4] = true := by decide +kernel
theorem subd9_7_154 : subd9_7 [0, -2, 5] = true := by decide +kernel
theorem subd9_7_155 : subd9_7 [0, -2, 6] = true := by decide +kernel
theorem subd9_7_156 : subd9_7 [0, -1, -10] = true := by decide +kernel
theorem subd9_7_157 : subd9_7 [0, -1, -9] = true := by decide +kernel
theorem subd9_7_158 : subd9_7 [0, -1, -8] = true := by decide +kernel
theorem subd9_7_159 : subd9_7 [0, -1, -7] = true := by decide +kernel
theorem sbd9_7_4 : ∀ q ∈ blkd9_7_4, subd9_7 q = true := by
  unfold blkd9_7_4
  exact List.forall_mem_cons.2 ⟨subd9_7_128, List.forall_mem_cons.2 ⟨subd9_7_129, List.forall_mem_cons.2 ⟨subd9_7_130, List.forall_mem_cons.2 ⟨subd9_7_131, List.forall_mem_cons.2 ⟨subd9_7_132, List.forall_mem_cons.2 ⟨subd9_7_133, List.forall_mem_cons.2 ⟨subd9_7_134, List.forall_mem_cons.2 ⟨subd9_7_135, List.forall_mem_cons.2 ⟨subd9_7_136, List.forall_mem_cons.2 ⟨subd9_7_137, List.forall_mem_cons.2 ⟨subd9_7_138, List.forall_mem_cons.2 ⟨subd9_7_139, List.forall_mem_cons.2 ⟨subd9_7_140, List.forall_mem_cons.2 ⟨subd9_7_141, List.forall_mem_cons.2 ⟨subd9_7_142, List.forall_mem_cons.2 ⟨subd9_7_143, List.forall_mem_cons.2 ⟨subd9_7_144, List.forall_mem_cons.2 ⟨subd9_7_145, List.forall_mem_cons.2 ⟨subd9_7_146, List.forall_mem_cons.2 ⟨subd9_7_147, List.forall_mem_cons.2 ⟨subd9_7_148, List.forall_mem_cons.2 ⟨subd9_7_149, List.forall_mem_cons.2 ⟨subd9_7_150, List.forall_mem_cons.2 ⟨subd9_7_151, List.forall_mem_cons.2 ⟨subd9_7_152, List.forall_mem_cons.2 ⟨subd9_7_153, List.forall_mem_cons.2 ⟨subd9_7_154, List.forall_mem_cons.2 ⟨subd9_7_155, List.forall_mem_cons.2 ⟨subd9_7_156, List.forall_mem_cons.2 ⟨subd9_7_157, List.forall_mem_cons.2 ⟨subd9_7_158, List.forall_mem_cons.2 ⟨subd9_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_160 : subd9_7 [0, -1, -6] = true := by decide +kernel
theorem subd9_7_161 : subd9_7 [0, -1, -5] = true := by decide +kernel
theorem subd9_7_162 : subd9_7 [0, -1, -4] = true := by decide +kernel
theorem subd9_7_163 : subd9_7 [0, -1, -3] = true := by decide +kernel
theorem subd9_7_164 : subd9_7 [0, -1, -2] = true := by decide +kernel
theorem subd9_7_165 : subd9_7 [0, -1, -1] = true := by decide +kernel
theorem subd9_7_166 : subd9_7 [0, -1, 0] = true := by decide +kernel
theorem subd9_7_167 : subd9_7 [0, -1, 1] = true := by decide +kernel
theorem subd9_7_168 : subd9_7 [0, -1, 2] = true := by decide +kernel
theorem subd9_7_169 : subd9_7 [0, -1, 3] = true := by decide +kernel
theorem subd9_7_170 : subd9_7 [0, -1, 4] = true := by decide +kernel
theorem subd9_7_171 : subd9_7 [0, -1, 5] = true := by decide +kernel
theorem subd9_7_172 : subd9_7 [0, -1, 6] = true := by decide +kernel
theorem subd9_7_173 : subd9_7 [0, -1, 7] = true := by decide +kernel
theorem subd9_7_174 : subd9_7 [0, -1, 8] = true := by decide +kernel
theorem subd9_7_175 : subd9_7 [0, 0, -10] = true := by decide +kernel
theorem subd9_7_176 : subd9_7 [0, 0, -9] = true := by decide +kernel
theorem subd9_7_177 : subd9_7 [0, 0, -8] = true := by decide +kernel
theorem subd9_7_178 : subd9_7 [0, 0, -7] = true := by decide +kernel
theorem subd9_7_179 : subd9_7 [0, 0, -6] = true := by decide +kernel
theorem subd9_7_180 : subd9_7 [0, 0, -5] = true := by decide +kernel
theorem subd9_7_181 : subd9_7 [0, 0, -4] = true := by decide +kernel
theorem subd9_7_182 : subd9_7 [0, 0, -3] = true := by decide +kernel
theorem subd9_7_183 : subd9_7 [0, 0, -2] = true := by decide +kernel
theorem subd9_7_184 : subd9_7 [0, 0, -1] = true := by decide +kernel
theorem subd9_7_185 : subd9_7 [0, 0, 0] = true := by decide +kernel
theorem subd9_7_186 : subd9_7 [0, 0, 1] = true := by decide +kernel
theorem subd9_7_187 : subd9_7 [0, 0, 2] = true := by decide +kernel
theorem subd9_7_188 : subd9_7 [0, 0, 3] = true := by decide +kernel
theorem subd9_7_189 : subd9_7 [0, 0, 4] = true := by decide +kernel
theorem subd9_7_190 : subd9_7 [0, 0, 5] = true := by decide +kernel
theorem subd9_7_191 : subd9_7 [0, 0, 6] = true := by decide +kernel
theorem sbd9_7_5 : ∀ q ∈ blkd9_7_5, subd9_7 q = true := by
  unfold blkd9_7_5
  exact List.forall_mem_cons.2 ⟨subd9_7_160, List.forall_mem_cons.2 ⟨subd9_7_161, List.forall_mem_cons.2 ⟨subd9_7_162, List.forall_mem_cons.2 ⟨subd9_7_163, List.forall_mem_cons.2 ⟨subd9_7_164, List.forall_mem_cons.2 ⟨subd9_7_165, List.forall_mem_cons.2 ⟨subd9_7_166, List.forall_mem_cons.2 ⟨subd9_7_167, List.forall_mem_cons.2 ⟨subd9_7_168, List.forall_mem_cons.2 ⟨subd9_7_169, List.forall_mem_cons.2 ⟨subd9_7_170, List.forall_mem_cons.2 ⟨subd9_7_171, List.forall_mem_cons.2 ⟨subd9_7_172, List.forall_mem_cons.2 ⟨subd9_7_173, List.forall_mem_cons.2 ⟨subd9_7_174, List.forall_mem_cons.2 ⟨subd9_7_175, List.forall_mem_cons.2 ⟨subd9_7_176, List.forall_mem_cons.2 ⟨subd9_7_177, List.forall_mem_cons.2 ⟨subd9_7_178, List.forall_mem_cons.2 ⟨subd9_7_179, List.forall_mem_cons.2 ⟨subd9_7_180, List.forall_mem_cons.2 ⟨subd9_7_181, List.forall_mem_cons.2 ⟨subd9_7_182, List.forall_mem_cons.2 ⟨subd9_7_183, List.forall_mem_cons.2 ⟨subd9_7_184, List.forall_mem_cons.2 ⟨subd9_7_185, List.forall_mem_cons.2 ⟨subd9_7_186, List.forall_mem_cons.2 ⟨subd9_7_187, List.forall_mem_cons.2 ⟨subd9_7_188, List.forall_mem_cons.2 ⟨subd9_7_189, List.forall_mem_cons.2 ⟨subd9_7_190, List.forall_mem_cons.2 ⟨subd9_7_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_192 : subd9_7 [0, 0, 7] = true := by decide +kernel
theorem subd9_7_193 : subd9_7 [0, 0, 8] = true := by decide +kernel
theorem subd9_7_194 : subd9_7 [0, 0, 9] = true := by decide +kernel
theorem subd9_7_195 : subd9_7 [0, 1, -9] = true := by decide +kernel
theorem subd9_7_196 : subd9_7 [0, 1, -8] = true := by decide +kernel
theorem subd9_7_197 : subd9_7 [0, 1, -7] = true := by decide +kernel
theorem subd9_7_198 : subd9_7 [0, 1, -6] = true := by decide +kernel
theorem subd9_7_199 : subd9_7 [0, 1, -5] = true := by decide +kernel
theorem subd9_7_200 : subd9_7 [0, 1, -4] = true := by decide +kernel
theorem subd9_7_201 : subd9_7 [0, 1, -3] = true := by decide +kernel
theorem subd9_7_202 : subd9_7 [0, 1, -2] = true := by decide +kernel
theorem subd9_7_203 : subd9_7 [0, 1, -1] = true := by decide +kernel
theorem subd9_7_204 : subd9_7 [0, 1, 0] = true := by decide +kernel
theorem subd9_7_205 : subd9_7 [0, 1, 1] = true := by decide +kernel
theorem subd9_7_206 : subd9_7 [0, 1, 2] = true := by decide +kernel
theorem subd9_7_207 : subd9_7 [0, 1, 3] = true := by decide +kernel
theorem subd9_7_208 : subd9_7 [0, 1, 4] = true := by decide +kernel
theorem subd9_7_209 : subd9_7 [0, 1, 5] = true := by decide +kernel
theorem subd9_7_210 : subd9_7 [0, 1, 6] = true := by decide +kernel
theorem subd9_7_211 : subd9_7 [0, 1, 7] = true := by decide +kernel
theorem subd9_7_212 : subd9_7 [0, 1, 8] = true := by decide +kernel
theorem subd9_7_213 : subd9_7 [0, 1, 9] = true := by decide +kernel
theorem subd9_7_214 : subd9_7 [0, 2, -7] = true := by decide +kernel
theorem subd9_7_215 : subd9_7 [0, 2, -6] = true := by decide +kernel
theorem subd9_7_216 : subd9_7 [0, 2, -5] = true := by decide +kernel
theorem subd9_7_217 : subd9_7 [0, 2, -4] = true := by decide +kernel
theorem subd9_7_218 : subd9_7 [0, 2, -3] = true := by decide +kernel
theorem subd9_7_219 : subd9_7 [0, 2, -2] = true := by decide +kernel
theorem subd9_7_220 : subd9_7 [0, 2, -1] = true := by decide +kernel
theorem subd9_7_221 : subd9_7 [0, 2, 0] = true := by decide +kernel
theorem subd9_7_222 : subd9_7 [0, 2, 1] = true := by decide +kernel
theorem subd9_7_223 : subd9_7 [0, 2, 2] = true := by decide +kernel
theorem sbd9_7_6 : ∀ q ∈ blkd9_7_6, subd9_7 q = true := by
  unfold blkd9_7_6
  exact List.forall_mem_cons.2 ⟨subd9_7_192, List.forall_mem_cons.2 ⟨subd9_7_193, List.forall_mem_cons.2 ⟨subd9_7_194, List.forall_mem_cons.2 ⟨subd9_7_195, List.forall_mem_cons.2 ⟨subd9_7_196, List.forall_mem_cons.2 ⟨subd9_7_197, List.forall_mem_cons.2 ⟨subd9_7_198, List.forall_mem_cons.2 ⟨subd9_7_199, List.forall_mem_cons.2 ⟨subd9_7_200, List.forall_mem_cons.2 ⟨subd9_7_201, List.forall_mem_cons.2 ⟨subd9_7_202, List.forall_mem_cons.2 ⟨subd9_7_203, List.forall_mem_cons.2 ⟨subd9_7_204, List.forall_mem_cons.2 ⟨subd9_7_205, List.forall_mem_cons.2 ⟨subd9_7_206, List.forall_mem_cons.2 ⟨subd9_7_207, List.forall_mem_cons.2 ⟨subd9_7_208, List.forall_mem_cons.2 ⟨subd9_7_209, List.forall_mem_cons.2 ⟨subd9_7_210, List.forall_mem_cons.2 ⟨subd9_7_211, List.forall_mem_cons.2 ⟨subd9_7_212, List.forall_mem_cons.2 ⟨subd9_7_213, List.forall_mem_cons.2 ⟨subd9_7_214, List.forall_mem_cons.2 ⟨subd9_7_215, List.forall_mem_cons.2 ⟨subd9_7_216, List.forall_mem_cons.2 ⟨subd9_7_217, List.forall_mem_cons.2 ⟨subd9_7_218, List.forall_mem_cons.2 ⟨subd9_7_219, List.forall_mem_cons.2 ⟨subd9_7_220, List.forall_mem_cons.2 ⟨subd9_7_221, List.forall_mem_cons.2 ⟨subd9_7_222, List.forall_mem_cons.2 ⟨subd9_7_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_224 : subd9_7 [0, 2, 3] = true := by decide +kernel
theorem subd9_7_225 : subd9_7 [0, 2, 4] = true := by decide +kernel
theorem subd9_7_226 : subd9_7 [0, 2, 5] = true := by decide +kernel
theorem subd9_7_227 : subd9_7 [0, 2, 6] = true := by decide +kernel
theorem subd9_7_228 : subd9_7 [0, 2, 7] = true := by decide +kernel
theorem subd9_7_229 : subd9_7 [0, 2, 8] = true := by decide +kernel
theorem subd9_7_230 : subd9_7 [0, 3] = true := by decide +kernel
theorem subd9_7_231 : subd9_7 [1, -4] = true := by decide +kernel
theorem subd9_7_232 : subd9_7 [1, -3] = true := by decide +kernel
theorem subd9_7_233 : subd9_7 [1, -2, -8] = true := by decide +kernel
theorem subd9_7_234 : subd9_7 [1, -2, -7] = true := by decide +kernel
theorem subd9_7_235 : subd9_7 [1, -2, -6] = true := by decide +kernel
theorem subd9_7_236 : subd9_7 [1, -2, -5] = true := by decide +kernel
theorem subd9_7_237 : subd9_7 [1, -2, -4] = true := by decide +kernel
theorem subd9_7_238 : subd9_7 [1, -2, -3] = true := by decide +kernel
theorem subd9_7_239 : subd9_7 [1, -2, -2] = true := by decide +kernel
theorem subd9_7_240 : subd9_7 [1, -2, -1] = true := by decide +kernel
theorem subd9_7_241 : subd9_7 [1, -2, 0] = true := by decide +kernel
theorem subd9_7_242 : subd9_7 [1, -2, 1] = true := by decide +kernel
theorem subd9_7_243 : subd9_7 [1, -2, 2] = true := by decide +kernel
theorem subd9_7_244 : subd9_7 [1, -2, 3] = true := by decide +kernel
theorem subd9_7_245 : subd9_7 [1, -2, 4] = true := by decide +kernel
theorem subd9_7_246 : subd9_7 [1, -2, 5] = true := by decide +kernel
theorem subd9_7_247 : subd9_7 [1, -1, -9] = true := by decide +kernel
theorem subd9_7_248 : subd9_7 [1, -1, -8] = true := by decide +kernel
theorem subd9_7_249 : subd9_7 [1, -1, -7] = true := by decide +kernel
theorem subd9_7_250 : subd9_7 [1, -1, -6] = true := by decide +kernel
theorem subd9_7_251 : subd9_7 [1, -1, -5] = true := by decide +kernel
theorem subd9_7_252 : subd9_7 [1, -1, -4] = true := by decide +kernel
theorem subd9_7_253 : subd9_7 [1, -1, -3] = true := by decide +kernel
theorem subd9_7_254 : subd9_7 [1, -1, -2] = true := by decide +kernel
theorem subd9_7_255 : subd9_7 [1, -1, -1] = true := by decide +kernel
theorem sbd9_7_7 : ∀ q ∈ blkd9_7_7, subd9_7 q = true := by
  unfold blkd9_7_7
  exact List.forall_mem_cons.2 ⟨subd9_7_224, List.forall_mem_cons.2 ⟨subd9_7_225, List.forall_mem_cons.2 ⟨subd9_7_226, List.forall_mem_cons.2 ⟨subd9_7_227, List.forall_mem_cons.2 ⟨subd9_7_228, List.forall_mem_cons.2 ⟨subd9_7_229, List.forall_mem_cons.2 ⟨subd9_7_230, List.forall_mem_cons.2 ⟨subd9_7_231, List.forall_mem_cons.2 ⟨subd9_7_232, List.forall_mem_cons.2 ⟨subd9_7_233, List.forall_mem_cons.2 ⟨subd9_7_234, List.forall_mem_cons.2 ⟨subd9_7_235, List.forall_mem_cons.2 ⟨subd9_7_236, List.forall_mem_cons.2 ⟨subd9_7_237, List.forall_mem_cons.2 ⟨subd9_7_238, List.forall_mem_cons.2 ⟨subd9_7_239, List.forall_mem_cons.2 ⟨subd9_7_240, List.forall_mem_cons.2 ⟨subd9_7_241, List.forall_mem_cons.2 ⟨subd9_7_242, List.forall_mem_cons.2 ⟨subd9_7_243, List.forall_mem_cons.2 ⟨subd9_7_244, List.forall_mem_cons.2 ⟨subd9_7_245, List.forall_mem_cons.2 ⟨subd9_7_246, List.forall_mem_cons.2 ⟨subd9_7_247, List.forall_mem_cons.2 ⟨subd9_7_248, List.forall_mem_cons.2 ⟨subd9_7_249, List.forall_mem_cons.2 ⟨subd9_7_250, List.forall_mem_cons.2 ⟨subd9_7_251, List.forall_mem_cons.2 ⟨subd9_7_252, List.forall_mem_cons.2 ⟨subd9_7_253, List.forall_mem_cons.2 ⟨subd9_7_254, List.forall_mem_cons.2 ⟨subd9_7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_256 : subd9_7 [1, -1, 0] = true := by decide +kernel
theorem subd9_7_257 : subd9_7 [1, -1, 1] = true := by decide +kernel
theorem subd9_7_258 : subd9_7 [1, -1, 2] = true := by decide +kernel
theorem subd9_7_259 : subd9_7 [1, -1, 3] = true := by decide +kernel
theorem subd9_7_260 : subd9_7 [1, -1, 4] = true := by decide +kernel
theorem subd9_7_261 : subd9_7 [1, -1, 5] = true := by decide +kernel
theorem subd9_7_262 : subd9_7 [1, -1, 6] = true := by decide +kernel
theorem subd9_7_263 : subd9_7 [1, -1, 7] = true := by decide +kernel
theorem subd9_7_264 : subd9_7 [1, 0, -10] = true := by decide +kernel
theorem subd9_7_265 : subd9_7 [1, 0, -9] = true := by decide +kernel
theorem subd9_7_266 : subd9_7 [1, 0, -8] = true := by decide +kernel
theorem subd9_7_267 : subd9_7 [1, 0, -7] = true := by decide +kernel
theorem subd9_7_268 : subd9_7 [1, 0, -6] = true := by decide +kernel
theorem subd9_7_269 : subd9_7 [1, 0, -5] = true := by decide +kernel
theorem subd9_7_270 : subd9_7 [1, 0, -4] = true := by decide +kernel
theorem subd9_7_271 : subd9_7 [1, 0, -3] = true := by decide +kernel
theorem subd9_7_272 : subd9_7 [1, 0, -2] = true := by decide +kernel
theorem subd9_7_273 : subd9_7 [1, 0, -1] = true := by decide +kernel
theorem subd9_7_274 : subd9_7 [1, 0, 0] = true := by decide +kernel
theorem subd9_7_275 : subd9_7 [1, 0, 1] = true := by decide +kernel
theorem subd9_7_276 : subd9_7 [1, 0, 2] = true := by decide +kernel
theorem subd9_7_277 : subd9_7 [1, 0, 3] = true := by decide +kernel
theorem subd9_7_278 : subd9_7 [1, 0, 4] = true := by decide +kernel
theorem subd9_7_279 : subd9_7 [1, 0, 5] = true := by decide +kernel
theorem subd9_7_280 : subd9_7 [1, 0, 6] = true := by decide +kernel
theorem subd9_7_281 : subd9_7 [1, 0, 7] = true := by decide +kernel
theorem subd9_7_282 : subd9_7 [1, 0, 8] = true := by decide +kernel
theorem subd9_7_283 : subd9_7 [1, 1, -9] = true := by decide +kernel
theorem subd9_7_284 : subd9_7 [1, 1, -8] = true := by decide +kernel
theorem subd9_7_285 : subd9_7 [1, 1, -7] = true := by decide +kernel
theorem subd9_7_286 : subd9_7 [1, 1, -6] = true := by decide +kernel
theorem subd9_7_287 : subd9_7 [1, 1, -5] = true := by decide +kernel
theorem sbd9_7_8 : ∀ q ∈ blkd9_7_8, subd9_7 q = true := by
  unfold blkd9_7_8
  exact List.forall_mem_cons.2 ⟨subd9_7_256, List.forall_mem_cons.2 ⟨subd9_7_257, List.forall_mem_cons.2 ⟨subd9_7_258, List.forall_mem_cons.2 ⟨subd9_7_259, List.forall_mem_cons.2 ⟨subd9_7_260, List.forall_mem_cons.2 ⟨subd9_7_261, List.forall_mem_cons.2 ⟨subd9_7_262, List.forall_mem_cons.2 ⟨subd9_7_263, List.forall_mem_cons.2 ⟨subd9_7_264, List.forall_mem_cons.2 ⟨subd9_7_265, List.forall_mem_cons.2 ⟨subd9_7_266, List.forall_mem_cons.2 ⟨subd9_7_267, List.forall_mem_cons.2 ⟨subd9_7_268, List.forall_mem_cons.2 ⟨subd9_7_269, List.forall_mem_cons.2 ⟨subd9_7_270, List.forall_mem_cons.2 ⟨subd9_7_271, List.forall_mem_cons.2 ⟨subd9_7_272, List.forall_mem_cons.2 ⟨subd9_7_273, List.forall_mem_cons.2 ⟨subd9_7_274, List.forall_mem_cons.2 ⟨subd9_7_275, List.forall_mem_cons.2 ⟨subd9_7_276, List.forall_mem_cons.2 ⟨subd9_7_277, List.forall_mem_cons.2 ⟨subd9_7_278, List.forall_mem_cons.2 ⟨subd9_7_279, List.forall_mem_cons.2 ⟨subd9_7_280, List.forall_mem_cons.2 ⟨subd9_7_281, List.forall_mem_cons.2 ⟨subd9_7_282, List.forall_mem_cons.2 ⟨subd9_7_283, List.forall_mem_cons.2 ⟨subd9_7_284, List.forall_mem_cons.2 ⟨subd9_7_285, List.forall_mem_cons.2 ⟨subd9_7_286, List.forall_mem_cons.2 ⟨subd9_7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_288 : subd9_7 [1, 1, -4] = true := by decide +kernel
theorem subd9_7_289 : subd9_7 [1, 1, -3] = true := by decide +kernel
theorem subd9_7_290 : subd9_7 [1, 1, -2] = true := by decide +kernel
theorem subd9_7_291 : subd9_7 [1, 1, -1] = true := by decide +kernel
theorem subd9_7_292 : subd9_7 [1, 1, 0] = true := by decide +kernel
theorem subd9_7_293 : subd9_7 [1, 1, 1] = true := by decide +kernel
theorem subd9_7_294 : subd9_7 [1, 1, 2] = true := by decide +kernel
theorem subd9_7_295 : subd9_7 [1, 1, 3] = true := by decide +kernel
theorem subd9_7_296 : subd9_7 [1, 1, 4] = true := by decide +kernel
theorem subd9_7_297 : subd9_7 [1, 1, 5] = true := by decide +kernel
theorem subd9_7_298 : subd9_7 [1, 1, 6] = true := by decide +kernel
theorem subd9_7_299 : subd9_7 [1, 1, 7] = true := by decide +kernel
theorem subd9_7_300 : subd9_7 [1, 1, 8] = true := by decide +kernel
theorem subd9_7_301 : subd9_7 [1, 2, -7] = true := by decide +kernel
theorem subd9_7_302 : subd9_7 [1, 2, -6] = true := by decide +kernel
theorem subd9_7_303 : subd9_7 [1, 2, -5] = true := by decide +kernel
theorem subd9_7_304 : subd9_7 [1, 2, -4] = true := by decide +kernel
theorem subd9_7_305 : subd9_7 [1, 2, -3] = true := by decide +kernel
theorem subd9_7_306 : subd9_7 [1, 2, -2] = true := by decide +kernel
theorem subd9_7_307 : subd9_7 [1, 2, -1] = true := by decide +kernel
theorem subd9_7_308 : subd9_7 [1, 2, 0] = true := by decide +kernel
theorem subd9_7_309 : subd9_7 [1, 2, 1] = true := by decide +kernel
theorem subd9_7_310 : subd9_7 [1, 2, 2] = true := by decide +kernel
theorem subd9_7_311 : subd9_7 [1, 2, 3] = true := by decide +kernel
theorem subd9_7_312 : subd9_7 [1, 2, 4] = true := by decide +kernel
theorem subd9_7_313 : subd9_7 [1, 2, 5] = true := by decide +kernel
theorem subd9_7_314 : subd9_7 [1, 2, 6] = true := by decide +kernel
theorem subd9_7_315 : subd9_7 [1, 2, 7] = true := by decide +kernel
theorem subd9_7_316 : subd9_7 [1, 2, 8] = true := by decide +kernel
theorem subd9_7_317 : subd9_7 [1, 3] = true := by decide +kernel
theorem subd9_7_318 : subd9_7 [2, -3] = true := by decide +kernel
theorem subd9_7_319 : subd9_7 [2, -2] = true := by decide +kernel
theorem sbd9_7_9 : ∀ q ∈ blkd9_7_9, subd9_7 q = true := by
  unfold blkd9_7_9
  exact List.forall_mem_cons.2 ⟨subd9_7_288, List.forall_mem_cons.2 ⟨subd9_7_289, List.forall_mem_cons.2 ⟨subd9_7_290, List.forall_mem_cons.2 ⟨subd9_7_291, List.forall_mem_cons.2 ⟨subd9_7_292, List.forall_mem_cons.2 ⟨subd9_7_293, List.forall_mem_cons.2 ⟨subd9_7_294, List.forall_mem_cons.2 ⟨subd9_7_295, List.forall_mem_cons.2 ⟨subd9_7_296, List.forall_mem_cons.2 ⟨subd9_7_297, List.forall_mem_cons.2 ⟨subd9_7_298, List.forall_mem_cons.2 ⟨subd9_7_299, List.forall_mem_cons.2 ⟨subd9_7_300, List.forall_mem_cons.2 ⟨subd9_7_301, List.forall_mem_cons.2 ⟨subd9_7_302, List.forall_mem_cons.2 ⟨subd9_7_303, List.forall_mem_cons.2 ⟨subd9_7_304, List.forall_mem_cons.2 ⟨subd9_7_305, List.forall_mem_cons.2 ⟨subd9_7_306, List.forall_mem_cons.2 ⟨subd9_7_307, List.forall_mem_cons.2 ⟨subd9_7_308, List.forall_mem_cons.2 ⟨subd9_7_309, List.forall_mem_cons.2 ⟨subd9_7_310, List.forall_mem_cons.2 ⟨subd9_7_311, List.forall_mem_cons.2 ⟨subd9_7_312, List.forall_mem_cons.2 ⟨subd9_7_313, List.forall_mem_cons.2 ⟨subd9_7_314, List.forall_mem_cons.2 ⟨subd9_7_315, List.forall_mem_cons.2 ⟨subd9_7_316, List.forall_mem_cons.2 ⟨subd9_7_317, List.forall_mem_cons.2 ⟨subd9_7_318, List.forall_mem_cons.2 ⟨subd9_7_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_320 : subd9_7 [2, -1, -8] = true := by decide +kernel
theorem subd9_7_321 : subd9_7 [2, -1, -7] = true := by decide +kernel
theorem subd9_7_322 : subd9_7 [2, -1, -6] = true := by decide +kernel
theorem subd9_7_323 : subd9_7 [2, -1, -5] = true := by decide +kernel
theorem subd9_7_324 : subd9_7 [2, -1, -4] = true := by decide +kernel
theorem subd9_7_325 : subd9_7 [2, -1, -3] = true := by decide +kernel
theorem subd9_7_326 : subd9_7 [2, -1, -2] = true := by decide +kernel
theorem subd9_7_327 : subd9_7 [2, -1, -1] = true := by decide +kernel
theorem subd9_7_328 : subd9_7 [2, -1, 0] = true := by decide +kernel
theorem subd9_7_329 : subd9_7 [2, -1, 1] = true := by decide +kernel
theorem subd9_7_330 : subd9_7 [2, -1, 2] = true := by decide +kernel
theorem subd9_7_331 : subd9_7 [2, -1, 3] = true := by decide +kernel
theorem subd9_7_332 : subd9_7 [2, -1, 4] = true := by decide +kernel
theorem subd9_7_333 : subd9_7 [2, -1, 5] = true := by decide +kernel
theorem subd9_7_334 : subd9_7 [2, 0, -8] = true := by decide +kernel
theorem subd9_7_335 : subd9_7 [2, 0, -7] = true := by decide +kernel
theorem subd9_7_336 : subd9_7 [2, 0, -6] = true := by decide +kernel
theorem subd9_7_337 : subd9_7 [2, 0, -5] = true := by decide +kernel
theorem subd9_7_338 : subd9_7 [2, 0, -4] = true := by decide +kernel
theorem subd9_7_339 : subd9_7 [2, 0, -3] = true := by decide +kernel
theorem subd9_7_340 : subd9_7 [2, 0, -2] = true := by decide +kernel
theorem subd9_7_341 : subd9_7 [2, 0, -1] = true := by decide +kernel
theorem subd9_7_342 : subd9_7 [2, 0, 0] = true := by decide +kernel
theorem subd9_7_343 : subd9_7 [2, 0, 1] = true := by decide +kernel
theorem subd9_7_344 : subd9_7 [2, 0, 2] = true := by decide +kernel
theorem subd9_7_345 : subd9_7 [2, 0, 3] = true := by decide +kernel
theorem subd9_7_346 : subd9_7 [2, 0, 4] = true := by decide +kernel
theorem subd9_7_347 : subd9_7 [2, 0, 5] = true := by decide +kernel
theorem subd9_7_348 : subd9_7 [2, 0, 6] = true := by decide +kernel
theorem subd9_7_349 : subd9_7 [2, 0, 7] = true := by decide +kernel
theorem subd9_7_350 : subd9_7 [2, 1, -8] = true := by decide +kernel
theorem subd9_7_351 : subd9_7 [2, 1, -7] = true := by decide +kernel
theorem sbd9_7_10 : ∀ q ∈ blkd9_7_10, subd9_7 q = true := by
  unfold blkd9_7_10
  exact List.forall_mem_cons.2 ⟨subd9_7_320, List.forall_mem_cons.2 ⟨subd9_7_321, List.forall_mem_cons.2 ⟨subd9_7_322, List.forall_mem_cons.2 ⟨subd9_7_323, List.forall_mem_cons.2 ⟨subd9_7_324, List.forall_mem_cons.2 ⟨subd9_7_325, List.forall_mem_cons.2 ⟨subd9_7_326, List.forall_mem_cons.2 ⟨subd9_7_327, List.forall_mem_cons.2 ⟨subd9_7_328, List.forall_mem_cons.2 ⟨subd9_7_329, List.forall_mem_cons.2 ⟨subd9_7_330, List.forall_mem_cons.2 ⟨subd9_7_331, List.forall_mem_cons.2 ⟨subd9_7_332, List.forall_mem_cons.2 ⟨subd9_7_333, List.forall_mem_cons.2 ⟨subd9_7_334, List.forall_mem_cons.2 ⟨subd9_7_335, List.forall_mem_cons.2 ⟨subd9_7_336, List.forall_mem_cons.2 ⟨subd9_7_337, List.forall_mem_cons.2 ⟨subd9_7_338, List.forall_mem_cons.2 ⟨subd9_7_339, List.forall_mem_cons.2 ⟨subd9_7_340, List.forall_mem_cons.2 ⟨subd9_7_341, List.forall_mem_cons.2 ⟨subd9_7_342, List.forall_mem_cons.2 ⟨subd9_7_343, List.forall_mem_cons.2 ⟨subd9_7_344, List.forall_mem_cons.2 ⟨subd9_7_345, List.forall_mem_cons.2 ⟨subd9_7_346, List.forall_mem_cons.2 ⟨subd9_7_347, List.forall_mem_cons.2 ⟨subd9_7_348, List.forall_mem_cons.2 ⟨subd9_7_349, List.forall_mem_cons.2 ⟨subd9_7_350, List.forall_mem_cons.2 ⟨subd9_7_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_352 : subd9_7 [2, 1, -6] = true := by decide +kernel
theorem subd9_7_353 : subd9_7 [2, 1, -5] = true := by decide +kernel
theorem subd9_7_354 : subd9_7 [2, 1, -4] = true := by decide +kernel
theorem subd9_7_355 : subd9_7 [2, 1, -3] = true := by decide +kernel
theorem subd9_7_356 : subd9_7 [2, 1, -2] = true := by decide +kernel
theorem subd9_7_357 : subd9_7 [2, 1, -1] = true := by decide +kernel
theorem subd9_7_358 : subd9_7 [2, 1, 0] = true := by decide +kernel
theorem subd9_7_359 : subd9_7 [2, 1, 1] = true := by decide +kernel
theorem subd9_7_360 : subd9_7 [2, 1, 2] = true := by decide +kernel
theorem subd9_7_361 : subd9_7 [2, 1, 3] = true := by decide +kernel
theorem subd9_7_362 : subd9_7 [2, 1, 4] = true := by decide +kernel
theorem subd9_7_363 : subd9_7 [2, 1, 5] = true := by decide +kernel
theorem subd9_7_364 : subd9_7 [2, 1, 6] = true := by decide +kernel
theorem subd9_7_365 : subd9_7 [2, 1, 7] = true := by decide +kernel
theorem subd9_7_366 : subd9_7 [2, 2] = true := by decide +kernel
theorem subd9_7_367 : subd9_7 [2, 3] = true := by decide +kernel
theorem subd9_7_368 : subd9_7 [3] = true := by decide +kernel
theorem sbd9_7_11 : ∀ q ∈ blkd9_7_11, subd9_7 q = true := by
  unfold blkd9_7_11
  exact List.forall_mem_cons.2 ⟨subd9_7_352, List.forall_mem_cons.2 ⟨subd9_7_353, List.forall_mem_cons.2 ⟨subd9_7_354, List.forall_mem_cons.2 ⟨subd9_7_355, List.forall_mem_cons.2 ⟨subd9_7_356, List.forall_mem_cons.2 ⟨subd9_7_357, List.forall_mem_cons.2 ⟨subd9_7_358, List.forall_mem_cons.2 ⟨subd9_7_359, List.forall_mem_cons.2 ⟨subd9_7_360, List.forall_mem_cons.2 ⟨subd9_7_361, List.forall_mem_cons.2 ⟨subd9_7_362, List.forall_mem_cons.2 ⟨subd9_7_363, List.forall_mem_cons.2 ⟨subd9_7_364, List.forall_mem_cons.2 ⟨subd9_7_365, List.forall_mem_cons.2 ⟨subd9_7_366, List.forall_mem_cons.2 ⟨subd9_7_367, List.forall_mem_cons.2 ⟨subd9_7_368, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
