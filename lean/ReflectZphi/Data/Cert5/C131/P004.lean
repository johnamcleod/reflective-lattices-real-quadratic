import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_64 : subd7_0 [0, 0, -4] = true := by decide +kernel
theorem subd7_0_65 : subd7_0 [0, 0, -3] = true := by decide +kernel
theorem subd7_0_66 : subd7_0 [0, 0, -2] = true := by decide +kernel
theorem subd7_0_67 : subd7_0 [0, 0, -1] = true := by decide +kernel
theorem subd7_0_68 : subd7_0 [0, 0, 0] = true := by decide +kernel
theorem subd7_0_69 : subd7_0 [0, 0, 1] = true := by decide +kernel
theorem subd7_0_70 : subd7_0 [0, 0, 2] = true := by decide +kernel
theorem subd7_0_71 : subd7_0 [0, 0, 3] = true := by decide +kernel
theorem subd7_0_72 : subd7_0 [0, 0, 4] = true := by decide +kernel
theorem subd7_0_73 : subd7_0 [0, 0, 5] = true := by decide +kernel
theorem subd7_0_74 : subd7_0 [0, 0, 6] = true := by decide +kernel
theorem subd7_0_75 : subd7_0 [0, 0, 7] = true := by decide +kernel
theorem subd7_0_76 : subd7_0 [0, 0, 8] = true := by decide +kernel
theorem subd7_0_77 : subd7_0 [0, 0, 9] = true := by decide +kernel
theorem subd7_0_78 : subd7_0 [0, 1, -9] = true := by decide +kernel
theorem subd7_0_79 : subd7_0 [0, 1, -8] = true := by decide +kernel
theorem subd7_0_80 : subd7_0 [0, 1, -7] = true := by decide +kernel
theorem subd7_0_81 : subd7_0 [0, 1, -6] = true := by decide +kernel
theorem subd7_0_82 : subd7_0 [0, 1, -5] = true := by decide +kernel
theorem subd7_0_83 : subd7_0 [0, 1, -4] = true := by decide +kernel
theorem subd7_0_84 : subd7_0 [0, 1, -3] = true := by decide +kernel
theorem subd7_0_85 : subd7_0 [0, 1, -2] = true := by decide +kernel
theorem subd7_0_86 : subd7_0 [0, 1, -1] = true := by decide +kernel
theorem subd7_0_87 : subd7_0 [0, 1, 0] = true := by decide +kernel
theorem subd7_0_88 : subd7_0 [0, 1, 1] = true := by decide +kernel
theorem subd7_0_89 : subd7_0 [0, 1, 2] = true := by decide +kernel
theorem subd7_0_90 : subd7_0 [0, 1, 3] = true := by decide +kernel
theorem subd7_0_91 : subd7_0 [0, 1, 4] = true := by decide +kernel
theorem subd7_0_92 : subd7_0 [0, 1, 5] = true := by decide +kernel
theorem subd7_0_93 : subd7_0 [0, 1, 6] = true := by decide +kernel
theorem subd7_0_94 : subd7_0 [0, 1, 7] = true := by decide +kernel
theorem subd7_0_95 : subd7_0 [0, 1, 8] = true := by decide +kernel
theorem sbd7_0_2 : ∀ q ∈ blkd7_0_2, subd7_0 q = true := by
  unfold blkd7_0_2
  exact List.forall_mem_cons.2 ⟨subd7_0_64, List.forall_mem_cons.2 ⟨subd7_0_65, List.forall_mem_cons.2 ⟨subd7_0_66, List.forall_mem_cons.2 ⟨subd7_0_67, List.forall_mem_cons.2 ⟨subd7_0_68, List.forall_mem_cons.2 ⟨subd7_0_69, List.forall_mem_cons.2 ⟨subd7_0_70, List.forall_mem_cons.2 ⟨subd7_0_71, List.forall_mem_cons.2 ⟨subd7_0_72, List.forall_mem_cons.2 ⟨subd7_0_73, List.forall_mem_cons.2 ⟨subd7_0_74, List.forall_mem_cons.2 ⟨subd7_0_75, List.forall_mem_cons.2 ⟨subd7_0_76, List.forall_mem_cons.2 ⟨subd7_0_77, List.forall_mem_cons.2 ⟨subd7_0_78, List.forall_mem_cons.2 ⟨subd7_0_79, List.forall_mem_cons.2 ⟨subd7_0_80, List.forall_mem_cons.2 ⟨subd7_0_81, List.forall_mem_cons.2 ⟨subd7_0_82, List.forall_mem_cons.2 ⟨subd7_0_83, List.forall_mem_cons.2 ⟨subd7_0_84, List.forall_mem_cons.2 ⟨subd7_0_85, List.forall_mem_cons.2 ⟨subd7_0_86, List.forall_mem_cons.2 ⟨subd7_0_87, List.forall_mem_cons.2 ⟨subd7_0_88, List.forall_mem_cons.2 ⟨subd7_0_89, List.forall_mem_cons.2 ⟨subd7_0_90, List.forall_mem_cons.2 ⟨subd7_0_91, List.forall_mem_cons.2 ⟨subd7_0_92, List.forall_mem_cons.2 ⟨subd7_0_93, List.forall_mem_cons.2 ⟨subd7_0_94, List.forall_mem_cons.2 ⟨subd7_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_96 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_97 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_98 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_99 : subd7_0 [1, 0, -8] = true := by decide +kernel
theorem subd7_0_100 : subd7_0 [1, 0, -7] = true := by decide +kernel
theorem subd7_0_101 : subd7_0 [1, 0, -6] = true := by decide +kernel
theorem subd7_0_102 : subd7_0 [1, 0, -5] = true := by decide +kernel
theorem subd7_0_103 : subd7_0 [1, 0, -4] = true := by decide +kernel
theorem subd7_0_104 : subd7_0 [1, 0, -3] = true := by decide +kernel
theorem subd7_0_105 : subd7_0 [1, 0, -2] = true := by decide +kernel
theorem subd7_0_106 : subd7_0 [1, 0, -1] = true := by decide +kernel
theorem subd7_0_107 : subd7_0 [1, 0, 0] = true := by decide +kernel
theorem subd7_0_108 : subd7_0 [1, 0, 1] = true := by decide +kernel
theorem subd7_0_109 : subd7_0 [1, 0, 2] = true := by decide +kernel
theorem subd7_0_110 : subd7_0 [1, 0, 3] = true := by decide +kernel
theorem subd7_0_111 : subd7_0 [1, 0, 4] = true := by decide +kernel
theorem subd7_0_112 : subd7_0 [1, 0, 5] = true := by decide +kernel
theorem subd7_0_113 : subd7_0 [1, 0, 6] = true := by decide +kernel
theorem subd7_0_114 : subd7_0 [1, 0, 7] = true := by decide +kernel
theorem subd7_0_115 : subd7_0 [1, 0, 8] = true := by decide +kernel
theorem subd7_0_116 : subd7_0 [1, 1, -8] = true := by decide +kernel
theorem subd7_0_117 : subd7_0 [1, 1, -7] = true := by decide +kernel
theorem subd7_0_118 : subd7_0 [1, 1, -6] = true := by decide +kernel
theorem subd7_0_119 : subd7_0 [1, 1, -5] = true := by decide +kernel
theorem subd7_0_120 : subd7_0 [1, 1, -4] = true := by decide +kernel
theorem subd7_0_121 : subd7_0 [1, 1, -3] = true := by decide +kernel
theorem subd7_0_122 : subd7_0 [1, 1, -2] = true := by decide +kernel
theorem subd7_0_123 : subd7_0 [1, 1, -1] = true := by decide +kernel
theorem subd7_0_124 : subd7_0 [1, 1, 0] = true := by decide +kernel
theorem subd7_0_125 : subd7_0 [1, 1, 1] = true := by decide +kernel
theorem subd7_0_126 : subd7_0 [1, 1, 2] = true := by decide +kernel
theorem subd7_0_127 : subd7_0 [1, 1, 3] = true := by decide +kernel
theorem sbd7_0_3 : ∀ q ∈ blkd7_0_3, subd7_0 q = true := by
  unfold blkd7_0_3
  exact List.forall_mem_cons.2 ⟨subd7_0_96, List.forall_mem_cons.2 ⟨subd7_0_97, List.forall_mem_cons.2 ⟨subd7_0_98, List.forall_mem_cons.2 ⟨subd7_0_99, List.forall_mem_cons.2 ⟨subd7_0_100, List.forall_mem_cons.2 ⟨subd7_0_101, List.forall_mem_cons.2 ⟨subd7_0_102, List.forall_mem_cons.2 ⟨subd7_0_103, List.forall_mem_cons.2 ⟨subd7_0_104, List.forall_mem_cons.2 ⟨subd7_0_105, List.forall_mem_cons.2 ⟨subd7_0_106, List.forall_mem_cons.2 ⟨subd7_0_107, List.forall_mem_cons.2 ⟨subd7_0_108, List.forall_mem_cons.2 ⟨subd7_0_109, List.forall_mem_cons.2 ⟨subd7_0_110, List.forall_mem_cons.2 ⟨subd7_0_111, List.forall_mem_cons.2 ⟨subd7_0_112, List.forall_mem_cons.2 ⟨subd7_0_113, List.forall_mem_cons.2 ⟨subd7_0_114, List.forall_mem_cons.2 ⟨subd7_0_115, List.forall_mem_cons.2 ⟨subd7_0_116, List.forall_mem_cons.2 ⟨subd7_0_117, List.forall_mem_cons.2 ⟨subd7_0_118, List.forall_mem_cons.2 ⟨subd7_0_119, List.forall_mem_cons.2 ⟨subd7_0_120, List.forall_mem_cons.2 ⟨subd7_0_121, List.forall_mem_cons.2 ⟨subd7_0_122, List.forall_mem_cons.2 ⟨subd7_0_123, List.forall_mem_cons.2 ⟨subd7_0_124, List.forall_mem_cons.2 ⟨subd7_0_125, List.forall_mem_cons.2 ⟨subd7_0_126, List.forall_mem_cons.2 ⟨subd7_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_128 : subd7_0 [1, 1, 4] = true := by decide +kernel
theorem subd7_0_129 : subd7_0 [1, 1, 5] = true := by decide +kernel
theorem subd7_0_130 : subd7_0 [1, 1, 6] = true := by decide +kernel
theorem subd7_0_131 : subd7_0 [1, 1, 7] = true := by decide +kernel
theorem subd7_0_132 : subd7_0 [1, 1, 8] = true := by decide +kernel
theorem subd7_0_133 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_134 : subd7_0 [2] = true := by decide +kernel
theorem sbd7_0_4 : ∀ q ∈ blkd7_0_4, subd7_0 q = true := by
  unfold blkd7_0_4
  exact List.forall_mem_cons.2 ⟨subd7_0_128, List.forall_mem_cons.2 ⟨subd7_0_129, List.forall_mem_cons.2 ⟨subd7_0_130, List.forall_mem_cons.2 ⟨subd7_0_131, List.forall_mem_cons.2 ⟨subd7_0_132, List.forall_mem_cons.2 ⟨subd7_0_133, List.forall_mem_cons.2 ⟨subd7_0_134, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-2] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-1, -1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [0, 2] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [0, 3] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [2] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-2, -4] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-2, -3] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-2, -2, -7] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-2, -2, -6] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-2, -2, -5] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-2, -2, -4] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-2, -2, -3] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [-2, -2, -2] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [-2, -2, -1] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [-2, -2, 0] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [-2, -2, 1] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [-2, -2, 2] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [-2, -2, 3] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [-2, -2, 4] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [-2, -2, 5] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [-2, -2, 6] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [-2, -1, -9] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [-2, -1, -8] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [-2, -1, -7] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [-2, -1, -6] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [-2, -1, -5] = true := by decide +kernel
theorem subd8_0_22 : subd8_0 [-2, -1, -4] = true := by decide +kernel
theorem subd8_0_23 : subd8_0 [-2, -1, -3] = true := by decide +kernel
theorem subd8_0_24 : subd8_0 [-2, -1, -2] = true := by decide +kernel
theorem subd8_0_25 : subd8_0 [-2, -1, -1] = true := by decide +kernel
theorem subd8_0_26 : subd8_0 [-2, -1, 0] = true := by decide +kernel
theorem subd8_0_27 : subd8_0 [-2, -1, 1] = true := by decide +kernel
theorem subd8_0_28 : subd8_0 [-2, -1, 2] = true := by decide +kernel
theorem subd8_0_29 : subd8_0 [-2, -1, 3] = true := by decide +kernel
theorem subd8_0_30 : subd8_0 [-2, -1, 4] = true := by decide +kernel
theorem subd8_0_31 : subd8_0 [-2, -1, 5] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_cons.2 ⟨subd8_0_22, List.forall_mem_cons.2 ⟨subd8_0_23, List.forall_mem_cons.2 ⟨subd8_0_24, List.forall_mem_cons.2 ⟨subd8_0_25, List.forall_mem_cons.2 ⟨subd8_0_26, List.forall_mem_cons.2 ⟨subd8_0_27, List.forall_mem_cons.2 ⟨subd8_0_28, List.forall_mem_cons.2 ⟨subd8_0_29, List.forall_mem_cons.2 ⟨subd8_0_30, List.forall_mem_cons.2 ⟨subd8_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_32 : subd8_0 [-2, -1, 6] = true := by decide +kernel
theorem subd8_0_33 : subd8_0 [-2, -1, 7] = true := by decide +kernel
theorem subd8_0_34 : subd8_0 [-2, 0, -9] = true := by decide +kernel
theorem subd8_0_35 : subd8_0 [-2, 0, -8] = true := by decide +kernel
theorem subd8_0_36 : subd8_0 [-2, 0, -7] = true := by decide +kernel
theorem subd8_0_37 : subd8_0 [-2, 0, -6] = true := by decide +kernel
theorem subd8_0_38 : subd8_0 [-2, 0, -5] = true := by decide +kernel
theorem subd8_0_39 : subd8_0 [-2, 0, -4] = true := by decide +kernel
theorem subd8_0_40 : subd8_0 [-2, 0, -3] = true := by decide +kernel
theorem subd8_0_41 : subd8_0 [-2, 0, -2] = true := by decide +kernel
theorem subd8_0_42 : subd8_0 [-2, 0, -1] = true := by decide +kernel
theorem subd8_0_43 : subd8_0 [-2, 0, 0] = true := by decide +kernel
theorem subd8_0_44 : subd8_0 [-2, 0, 1] = true := by decide +kernel
theorem subd8_0_45 : subd8_0 [-2, 0, 2] = true := by decide +kernel
theorem subd8_0_46 : subd8_0 [-2, 0, 3] = true := by decide +kernel
theorem subd8_0_47 : subd8_0 [-2, 0, 4] = true := by decide +kernel
theorem subd8_0_48 : subd8_0 [-2, 0, 5] = true := by decide +kernel
theorem subd8_0_49 : subd8_0 [-2, 0, 6] = true := by decide +kernel
theorem subd8_0_50 : subd8_0 [-2, 0, 7] = true := by decide +kernel
theorem subd8_0_51 : subd8_0 [-2, 1, -7] = true := by decide +kernel
theorem subd8_0_52 : subd8_0 [-2, 1, -6] = true := by decide +kernel
theorem subd8_0_53 : subd8_0 [-2, 1, -5] = true := by decide +kernel
theorem subd8_0_54 : subd8_0 [-2, 1, -4] = true := by decide +kernel
theorem subd8_0_55 : subd8_0 [-2, 1, -3] = true := by decide +kernel
theorem subd8_0_56 : subd8_0 [-2, 1, -2] = true := by decide +kernel
theorem subd8_0_57 : subd8_0 [-2, 1, -1] = true := by decide +kernel
theorem subd8_0_58 : subd8_0 [-2, 1, 0] = true := by decide +kernel
theorem subd8_0_59 : subd8_0 [-2, 1, 1] = true := by decide +kernel
theorem subd8_0_60 : subd8_0 [-2, 1, 2] = true := by decide +kernel
theorem subd8_0_61 : subd8_0 [-2, 1, 3] = true := by decide +kernel
theorem subd8_0_62 : subd8_0 [-2, 1, 4] = true := by decide +kernel
theorem subd8_0_63 : subd8_0 [-2, 1, 5] = true := by decide +kernel
theorem sbd8_0_1 : ∀ q ∈ blkd8_0_1, subd8_0 q = true := by
  unfold blkd8_0_1
  exact List.forall_mem_cons.2 ⟨subd8_0_32, List.forall_mem_cons.2 ⟨subd8_0_33, List.forall_mem_cons.2 ⟨subd8_0_34, List.forall_mem_cons.2 ⟨subd8_0_35, List.forall_mem_cons.2 ⟨subd8_0_36, List.forall_mem_cons.2 ⟨subd8_0_37, List.forall_mem_cons.2 ⟨subd8_0_38, List.forall_mem_cons.2 ⟨subd8_0_39, List.forall_mem_cons.2 ⟨subd8_0_40, List.forall_mem_cons.2 ⟨subd8_0_41, List.forall_mem_cons.2 ⟨subd8_0_42, List.forall_mem_cons.2 ⟨subd8_0_43, List.forall_mem_cons.2 ⟨subd8_0_44, List.forall_mem_cons.2 ⟨subd8_0_45, List.forall_mem_cons.2 ⟨subd8_0_46, List.forall_mem_cons.2 ⟨subd8_0_47, List.forall_mem_cons.2 ⟨subd8_0_48, List.forall_mem_cons.2 ⟨subd8_0_49, List.forall_mem_cons.2 ⟨subd8_0_50, List.forall_mem_cons.2 ⟨subd8_0_51, List.forall_mem_cons.2 ⟨subd8_0_52, List.forall_mem_cons.2 ⟨subd8_0_53, List.forall_mem_cons.2 ⟨subd8_0_54, List.forall_mem_cons.2 ⟨subd8_0_55, List.forall_mem_cons.2 ⟨subd8_0_56, List.forall_mem_cons.2 ⟨subd8_0_57, List.forall_mem_cons.2 ⟨subd8_0_58, List.forall_mem_cons.2 ⟨subd8_0_59, List.forall_mem_cons.2 ⟨subd8_0_60, List.forall_mem_cons.2 ⟨subd8_0_61, List.forall_mem_cons.2 ⟨subd8_0_62, List.forall_mem_cons.2 ⟨subd8_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_64 : subd8_0 [-1, -4] = true := by decide +kernel
theorem subd8_0_65 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_66 : subd8_0 [-1, -2, -9] = true := by decide +kernel
theorem subd8_0_67 : subd8_0 [-1, -2, -8] = true := by decide +kernel
theorem subd8_0_68 : subd8_0 [-1, -2, -7] = true := by decide +kernel
theorem subd8_0_69 : subd8_0 [-1, -2, -6] = true := by decide +kernel
theorem subd8_0_70 : subd8_0 [-1, -2, -5] = true := by decide +kernel
theorem subd8_0_71 : subd8_0 [-1, -2, -4] = true := by decide +kernel
theorem subd8_0_72 : subd8_0 [-1, -2, -3] = true := by decide +kernel
theorem subd8_0_73 : subd8_0 [-1, -2, -2] = true := by decide +kernel
theorem subd8_0_74 : subd8_0 [-1, -2, -1] = true := by decide +kernel
theorem subd8_0_75 : subd8_0 [-1, -2, 0] = true := by decide +kernel
theorem subd8_0_76 : subd8_0 [-1, -2, 1] = true := by decide +kernel
theorem subd8_0_77 : subd8_0 [-1, -2, 2] = true := by decide +kernel
theorem subd8_0_78 : subd8_0 [-1, -2, 3] = true := by decide +kernel
theorem subd8_0_79 : subd8_0 [-1, -2, 4] = true := by decide +kernel
theorem subd8_0_80 : subd8_0 [-1, -2, 5] = true := by decide +kernel
theorem subd8_0_81 : subd8_0 [-1, -2, 6] = true := by decide +kernel
theorem subd8_0_82 : subd8_0 [-1, -2, 7] = true := by decide +kernel
theorem subd8_0_83 : subd8_0 [-1, -2, 8] = true := by decide +kernel
theorem subd8_0_84 : subd8_0 [-1, -1, -10] = true := by decide +kernel
theorem subd8_0_85 : subd8_0 [-1, -1, -9] = true := by decide +kernel
theorem subd8_0_86 : subd8_0 [-1, -1, -8] = true := by decide +kernel
theorem subd8_0_87 : subd8_0 [-1, -1, -7] = true := by decide +kernel
theorem subd8_0_88 : subd8_0 [-1, -1, -6] = true := by decide +kernel
theorem subd8_0_89 : subd8_0 [-1, -1, -5] = true := by decide +kernel
theorem subd8_0_90 : subd8_0 [-1, -1, -4] = true := by decide +kernel
theorem subd8_0_91 : subd8_0 [-1, -1, -3] = true := by decide +kernel
theorem subd8_0_92 : subd8_0 [-1, -1, -2] = true := by decide +kernel
theorem subd8_0_93 : subd8_0 [-1, -1, -1] = true := by decide +kernel
theorem subd8_0_94 : subd8_0 [-1, -1, 0] = true := by decide +kernel
theorem subd8_0_95 : subd8_0 [-1, -1, 1] = true := by decide +kernel
theorem sbd8_0_2 : ∀ q ∈ blkd8_0_2, subd8_0 q = true := by
  unfold blkd8_0_2
  exact List.forall_mem_cons.2 ⟨subd8_0_64, List.forall_mem_cons.2 ⟨subd8_0_65, List.forall_mem_cons.2 ⟨subd8_0_66, List.forall_mem_cons.2 ⟨subd8_0_67, List.forall_mem_cons.2 ⟨subd8_0_68, List.forall_mem_cons.2 ⟨subd8_0_69, List.forall_mem_cons.2 ⟨subd8_0_70, List.forall_mem_cons.2 ⟨subd8_0_71, List.forall_mem_cons.2 ⟨subd8_0_72, List.forall_mem_cons.2 ⟨subd8_0_73, List.forall_mem_cons.2 ⟨subd8_0_74, List.forall_mem_cons.2 ⟨subd8_0_75, List.forall_mem_cons.2 ⟨subd8_0_76, List.forall_mem_cons.2 ⟨subd8_0_77, List.forall_mem_cons.2 ⟨subd8_0_78, List.forall_mem_cons.2 ⟨subd8_0_79, List.forall_mem_cons.2 ⟨subd8_0_80, List.forall_mem_cons.2 ⟨subd8_0_81, List.forall_mem_cons.2 ⟨subd8_0_82, List.forall_mem_cons.2 ⟨subd8_0_83, List.forall_mem_cons.2 ⟨subd8_0_84, List.forall_mem_cons.2 ⟨subd8_0_85, List.forall_mem_cons.2 ⟨subd8_0_86, List.forall_mem_cons.2 ⟨subd8_0_87, List.forall_mem_cons.2 ⟨subd8_0_88, List.forall_mem_cons.2 ⟨subd8_0_89, List.forall_mem_cons.2 ⟨subd8_0_90, List.forall_mem_cons.2 ⟨subd8_0_91, List.forall_mem_cons.2 ⟨subd8_0_92, List.forall_mem_cons.2 ⟨subd8_0_93, List.forall_mem_cons.2 ⟨subd8_0_94, List.forall_mem_cons.2 ⟨subd8_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_96 : subd8_0 [-1, -1, 2] = true := by decide +kernel
theorem subd8_0_97 : subd8_0 [-1, -1, 3] = true := by decide +kernel
theorem subd8_0_98 : subd8_0 [-1, -1, 4] = true := by decide +kernel
theorem subd8_0_99 : subd8_0 [-1, -1, 5] = true := by decide +kernel
theorem subd8_0_100 : subd8_0 [-1, -1, 6] = true := by decide +kernel
theorem subd8_0_101 : subd8_0 [-1, -1, 7] = true := by decide +kernel
theorem subd8_0_102 : subd8_0 [-1, -1, 8] = true := by decide +kernel
theorem subd8_0_103 : subd8_0 [-1, -1, 9] = true := by decide +kernel
theorem subd8_0_104 : subd8_0 [-1, 0, -11] = true := by decide +kernel
theorem subd8_0_105 : subd8_0 [-1, 0, -10] = true := by decide +kernel
theorem subd8_0_106 : subd8_0 [-1, 0, -9] = true := by decide +kernel
theorem subd8_0_107 : subd8_0 [-1, 0, -8] = true := by decide +kernel
theorem subd8_0_108 : subd8_0 [-1, 0, -7] = true := by decide +kernel
theorem subd8_0_109 : subd8_0 [-1, 0, -6] = true := by decide +kernel
theorem subd8_0_110 : subd8_0 [-1, 0, -5] = true := by decide +kernel
theorem subd8_0_111 : subd8_0 [-1, 0, -4] = true := by decide +kernel
theorem subd8_0_112 : subd8_0 [-1, 0, -3] = true := by decide +kernel
theorem subd8_0_113 : subd8_0 [-1, 0, -2] = true := by decide +kernel
theorem subd8_0_114 : subd8_0 [-1, 0, -1] = true := by decide +kernel
theorem subd8_0_115 : subd8_0 [-1, 0, 0] = true := by decide +kernel
theorem subd8_0_116 : subd8_0 [-1, 0, 1] = true := by decide +kernel
theorem subd8_0_117 : subd8_0 [-1, 0, 2] = true := by decide +kernel
theorem subd8_0_118 : subd8_0 [-1, 0, 3] = true := by decide +kernel
theorem subd8_0_119 : subd8_0 [-1, 0, 4] = true := by decide +kernel
theorem subd8_0_120 : subd8_0 [-1, 0, 5] = true := by decide +kernel
theorem subd8_0_121 : subd8_0 [-1, 0, 6] = true := by decide +kernel
theorem subd8_0_122 : subd8_0 [-1, 0, 7] = true := by decide +kernel
theorem subd8_0_123 : subd8_0 [-1, 0, 8] = true := by decide +kernel
theorem subd8_0_124 : subd8_0 [-1, 0, 9] = true := by decide +kernel
theorem subd8_0_125 : subd8_0 [-1, 1, -10] = true := by decide +kernel
theorem subd8_0_126 : subd8_0 [-1, 1, -9] = true := by decide +kernel
theorem subd8_0_127 : subd8_0 [-1, 1, -8] = true := by decide +kernel
theorem sbd8_0_3 : ∀ q ∈ blkd8_0_3, subd8_0 q = true := by
  unfold blkd8_0_3
  exact List.forall_mem_cons.2 ⟨subd8_0_96, List.forall_mem_cons.2 ⟨subd8_0_97, List.forall_mem_cons.2 ⟨subd8_0_98, List.forall_mem_cons.2 ⟨subd8_0_99, List.forall_mem_cons.2 ⟨subd8_0_100, List.forall_mem_cons.2 ⟨subd8_0_101, List.forall_mem_cons.2 ⟨subd8_0_102, List.forall_mem_cons.2 ⟨subd8_0_103, List.forall_mem_cons.2 ⟨subd8_0_104, List.forall_mem_cons.2 ⟨subd8_0_105, List.forall_mem_cons.2 ⟨subd8_0_106, List.forall_mem_cons.2 ⟨subd8_0_107, List.forall_mem_cons.2 ⟨subd8_0_108, List.forall_mem_cons.2 ⟨subd8_0_109, List.forall_mem_cons.2 ⟨subd8_0_110, List.forall_mem_cons.2 ⟨subd8_0_111, List.forall_mem_cons.2 ⟨subd8_0_112, List.forall_mem_cons.2 ⟨subd8_0_113, List.forall_mem_cons.2 ⟨subd8_0_114, List.forall_mem_cons.2 ⟨subd8_0_115, List.forall_mem_cons.2 ⟨subd8_0_116, List.forall_mem_cons.2 ⟨subd8_0_117, List.forall_mem_cons.2 ⟨subd8_0_118, List.forall_mem_cons.2 ⟨subd8_0_119, List.forall_mem_cons.2 ⟨subd8_0_120, List.forall_mem_cons.2 ⟨subd8_0_121, List.forall_mem_cons.2 ⟨subd8_0_122, List.forall_mem_cons.2 ⟨subd8_0_123, List.forall_mem_cons.2 ⟨subd8_0_124, List.forall_mem_cons.2 ⟨subd8_0_125, List.forall_mem_cons.2 ⟨subd8_0_126, List.forall_mem_cons.2 ⟨subd8_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_128 : subd8_0 [-1, 1, -7] = true := by decide +kernel
theorem subd8_0_129 : subd8_0 [-1, 1, -6] = true := by decide +kernel
theorem subd8_0_130 : subd8_0 [-1, 1, -5] = true := by decide +kernel
theorem subd8_0_131 : subd8_0 [-1, 1, -4] = true := by decide +kernel
theorem subd8_0_132 : subd8_0 [-1, 1, -3] = true := by decide +kernel
theorem subd8_0_133 : subd8_0 [-1, 1, -2] = true := by decide +kernel
theorem subd8_0_134 : subd8_0 [-1, 1, -1] = true := by decide +kernel
theorem subd8_0_135 : subd8_0 [-1, 1, 0] = true := by decide +kernel
theorem subd8_0_136 : subd8_0 [-1, 1, 1] = true := by decide +kernel
theorem subd8_0_137 : subd8_0 [-1, 1, 2] = true := by decide +kernel
theorem subd8_0_138 : subd8_0 [-1, 1, 3] = true := by decide +kernel
theorem subd8_0_139 : subd8_0 [-1, 1, 4] = true := by decide +kernel
theorem subd8_0_140 : subd8_0 [-1, 1, 5] = true := by decide +kernel
theorem subd8_0_141 : subd8_0 [-1, 1, 6] = true := by decide +kernel
theorem subd8_0_142 : subd8_0 [-1, 1, 7] = true := by decide +kernel
theorem subd8_0_143 : subd8_0 [-1, 1, 8] = true := by decide +kernel
theorem subd8_0_144 : subd8_0 [-1, 2, -8] = true := by decide +kernel
theorem subd8_0_145 : subd8_0 [-1, 2, -7] = true := by decide +kernel
theorem subd8_0_146 : subd8_0 [-1, 2, -6] = true := by decide +kernel
theorem subd8_0_147 : subd8_0 [-1, 2, -5] = true := by decide +kernel
theorem subd8_0_148 : subd8_0 [-1, 2, -4] = true := by decide +kernel
theorem subd8_0_149 : subd8_0 [-1, 2, -3] = true := by decide +kernel
theorem subd8_0_150 : subd8_0 [-1, 2, -2] = true := by decide +kernel
theorem subd8_0_151 : subd8_0 [-1, 2, -1] = true := by decide +kernel
theorem subd8_0_152 : subd8_0 [-1, 2, 0] = true := by decide +kernel
theorem subd8_0_153 : subd8_0 [-1, 2, 1] = true := by decide +kernel
theorem subd8_0_154 : subd8_0 [-1, 2, 2] = true := by decide +kernel
theorem subd8_0_155 : subd8_0 [-1, 2, 3] = true := by decide +kernel
theorem subd8_0_156 : subd8_0 [-1, 2, 4] = true := by decide +kernel
theorem subd8_0_157 : subd8_0 [-1, 2, 5] = true := by decide +kernel
theorem subd8_0_158 : subd8_0 [-1, 2, 6] = true := by decide +kernel
theorem subd8_0_159 : subd8_0 [0, -4] = true := by decide +kernel
theorem sbd8_0_4 : ∀ q ∈ blkd8_0_4, subd8_0 q = true := by
  unfold blkd8_0_4
  exact List.forall_mem_cons.2 ⟨subd8_0_128, List.forall_mem_cons.2 ⟨subd8_0_129, List.forall_mem_cons.2 ⟨subd8_0_130, List.forall_mem_cons.2 ⟨subd8_0_131, List.forall_mem_cons.2 ⟨subd8_0_132, List.forall_mem_cons.2 ⟨subd8_0_133, List.forall_mem_cons.2 ⟨subd8_0_134, List.forall_mem_cons.2 ⟨subd8_0_135, List.forall_mem_cons.2 ⟨subd8_0_136, List.forall_mem_cons.2 ⟨subd8_0_137, List.forall_mem_cons.2 ⟨subd8_0_138, List.forall_mem_cons.2 ⟨subd8_0_139, List.forall_mem_cons.2 ⟨subd8_0_140, List.forall_mem_cons.2 ⟨subd8_0_141, List.forall_mem_cons.2 ⟨subd8_0_142, List.forall_mem_cons.2 ⟨subd8_0_143, List.forall_mem_cons.2 ⟨subd8_0_144, List.forall_mem_cons.2 ⟨subd8_0_145, List.forall_mem_cons.2 ⟨subd8_0_146, List.forall_mem_cons.2 ⟨subd8_0_147, List.forall_mem_cons.2 ⟨subd8_0_148, List.forall_mem_cons.2 ⟨subd8_0_149, List.forall_mem_cons.2 ⟨subd8_0_150, List.forall_mem_cons.2 ⟨subd8_0_151, List.forall_mem_cons.2 ⟨subd8_0_152, List.forall_mem_cons.2 ⟨subd8_0_153, List.forall_mem_cons.2 ⟨subd8_0_154, List.forall_mem_cons.2 ⟨subd8_0_155, List.forall_mem_cons.2 ⟨subd8_0_156, List.forall_mem_cons.2 ⟨subd8_0_157, List.forall_mem_cons.2 ⟨subd8_0_158, List.forall_mem_cons.2 ⟨subd8_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_160 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_161 : subd8_0 [0, -2, -9] = true := by decide +kernel
theorem subd8_0_162 : subd8_0 [0, -2, -8] = true := by decide +kernel
theorem subd8_0_163 : subd8_0 [0, -2, -7] = true := by decide +kernel
theorem subd8_0_164 : subd8_0 [0, -2, -6] = true := by decide +kernel
theorem subd8_0_165 : subd8_0 [0, -2, -5] = true := by decide +kernel
theorem subd8_0_166 : subd8_0 [0, -2, -4] = true := by decide +kernel
theorem subd8_0_167 : subd8_0 [0, -2, -3] = true := by decide +kernel
theorem subd8_0_168 : subd8_0 [0, -2, -2] = true := by decide +kernel
theorem subd8_0_169 : subd8_0 [0, -2, -1] = true := by decide +kernel
theorem subd8_0_170 : subd8_0 [0, -2, 0] = true := by decide +kernel
theorem subd8_0_171 : subd8_0 [0, -2, 1] = true := by decide +kernel
theorem subd8_0_172 : subd8_0 [0, -2, 2] = true := by decide +kernel
theorem subd8_0_173 : subd8_0 [0, -2, 3] = true := by decide +kernel
theorem subd8_0_174 : subd8_0 [0, -2, 4] = true := by decide +kernel
theorem subd8_0_175 : subd8_0 [0, -2, 5] = true := by decide +kernel
theorem subd8_0_176 : subd8_0 [0, -2, 6] = true := by decide +kernel
theorem subd8_0_177 : subd8_0 [0, -2, 7] = true := by decide +kernel
theorem subd8_0_178 : subd8_0 [0, -2, 8] = true := by decide +kernel
theorem subd8_0_179 : subd8_0 [0, -1, -10] = true := by decide +kernel
theorem subd8_0_180 : subd8_0 [0, -1, -9] = true := by decide +kernel
theorem subd8_0_181 : subd8_0 [0, -1, -8] = true := by decide +kernel
theorem subd8_0_182 : subd8_0 [0, -1, -7] = true := by decide +kernel
theorem subd8_0_183 : subd8_0 [0, -1, -6] = true := by decide +kernel
theorem subd8_0_184 : subd8_0 [0, -1, -5] = true := by decide +kernel
theorem subd8_0_185 : subd8_0 [0, -1, -4] = true := by decide +kernel
theorem subd8_0_186 : subd8_0 [0, -1, -3] = true := by decide +kernel
theorem subd8_0_187 : subd8_0 [0, -1, -2] = true := by decide +kernel
theorem subd8_0_188 : subd8_0 [0, -1, -1] = true := by decide +kernel
theorem subd8_0_189 : subd8_0 [0, -1, 0] = true := by decide +kernel
theorem subd8_0_190 : subd8_0 [0, -1, 1] = true := by decide +kernel
theorem subd8_0_191 : subd8_0 [0, -1, 2] = true := by decide +kernel
theorem sbd8_0_5 : ∀ q ∈ blkd8_0_5, subd8_0 q = true := by
  unfold blkd8_0_5
  exact List.forall_mem_cons.2 ⟨subd8_0_160, List.forall_mem_cons.2 ⟨subd8_0_161, List.forall_mem_cons.2 ⟨subd8_0_162, List.forall_mem_cons.2 ⟨subd8_0_163, List.forall_mem_cons.2 ⟨subd8_0_164, List.forall_mem_cons.2 ⟨subd8_0_165, List.forall_mem_cons.2 ⟨subd8_0_166, List.forall_mem_cons.2 ⟨subd8_0_167, List.forall_mem_cons.2 ⟨subd8_0_168, List.forall_mem_cons.2 ⟨subd8_0_169, List.forall_mem_cons.2 ⟨subd8_0_170, List.forall_mem_cons.2 ⟨subd8_0_171, List.forall_mem_cons.2 ⟨subd8_0_172, List.forall_mem_cons.2 ⟨subd8_0_173, List.forall_mem_cons.2 ⟨subd8_0_174, List.forall_mem_cons.2 ⟨subd8_0_175, List.forall_mem_cons.2 ⟨subd8_0_176, List.forall_mem_cons.2 ⟨subd8_0_177, List.forall_mem_cons.2 ⟨subd8_0_178, List.forall_mem_cons.2 ⟨subd8_0_179, List.forall_mem_cons.2 ⟨subd8_0_180, List.forall_mem_cons.2 ⟨subd8_0_181, List.forall_mem_cons.2 ⟨subd8_0_182, List.forall_mem_cons.2 ⟨subd8_0_183, List.forall_mem_cons.2 ⟨subd8_0_184, List.forall_mem_cons.2 ⟨subd8_0_185, List.forall_mem_cons.2 ⟨subd8_0_186, List.forall_mem_cons.2 ⟨subd8_0_187, List.forall_mem_cons.2 ⟨subd8_0_188, List.forall_mem_cons.2 ⟨subd8_0_189, List.forall_mem_cons.2 ⟨subd8_0_190, List.forall_mem_cons.2 ⟨subd8_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_192 : subd8_0 [0, -1, 3] = true := by decide +kernel
theorem subd8_0_193 : subd8_0 [0, -1, 4] = true := by decide +kernel
theorem subd8_0_194 : subd8_0 [0, -1, 5] = true := by decide +kernel
theorem subd8_0_195 : subd8_0 [0, -1, 6] = true := by decide +kernel
theorem subd8_0_196 : subd8_0 [0, -1, 7] = true := by decide +kernel
theorem subd8_0_197 : subd8_0 [0, -1, 8] = true := by decide +kernel
theorem subd8_0_198 : subd8_0 [0, -1, 9] = true := by decide +kernel
theorem subd8_0_199 : subd8_0 [0, -1, 10] = true := by decide +kernel
theorem subd8_0_200 : subd8_0 [0, 0, -11] = true := by decide +kernel
theorem subd8_0_201 : subd8_0 [0, 0, -10] = true := by decide +kernel
theorem subd8_0_202 : subd8_0 [0, 0, -9] = true := by decide +kernel
theorem subd8_0_203 : subd8_0 [0, 0, -8] = true := by decide +kernel
theorem subd8_0_204 : subd8_0 [0, 0, -7] = true := by decide +kernel
theorem subd8_0_205 : subd8_0 [0, 0, -6] = true := by decide +kernel
theorem subd8_0_206 : subd8_0 [0, 0, -5] = true := by decide +kernel
theorem subd8_0_207 : subd8_0 [0, 0, -4] = true := by decide +kernel
theorem subd8_0_208 : subd8_0 [0, 0, -3] = true := by decide +kernel
theorem subd8_0_209 : subd8_0 [0, 0, -2] = true := by decide +kernel
theorem subd8_0_210 : subd8_0 [0, 0, -1] = true := by decide +kernel
theorem subd8_0_211 : subd8_0 [0, 0, 0] = true := by decide +kernel
theorem subd8_0_212 : subd8_0 [0, 0, 1] = true := by decide +kernel
theorem subd8_0_213 : subd8_0 [0, 0, 2] = true := by decide +kernel
theorem subd8_0_214 : subd8_0 [0, 0, 3] = true := by decide +kernel
theorem subd8_0_215 : subd8_0 [0, 0, 4] = true := by decide +kernel
theorem subd8_0_216 : subd8_0 [0, 0, 5] = true := by decide +kernel
theorem subd8_0_217 : subd8_0 [0, 0, 6] = true := by decide +kernel
theorem subd8_0_218 : subd8_0 [0, 0, 7] = true := by decide +kernel
theorem subd8_0_219 : subd8_0 [0, 0, 8] = true := by decide +kernel
theorem subd8_0_220 : subd8_0 [0, 0, 9] = true := by decide +kernel
theorem subd8_0_221 : subd8_0 [0, 0, 10] = true := by decide +kernel
theorem subd8_0_222 : subd8_0 [0, 1, -11] = true := by decide +kernel
theorem subd8_0_223 : subd8_0 [0, 1, -10] = true := by decide +kernel
theorem sbd8_0_6 : ∀ q ∈ blkd8_0_6, subd8_0 q = true := by
  unfold blkd8_0_6
  exact List.forall_mem_cons.2 ⟨subd8_0_192, List.forall_mem_cons.2 ⟨subd8_0_193, List.forall_mem_cons.2 ⟨subd8_0_194, List.forall_mem_cons.2 ⟨subd8_0_195, List.forall_mem_cons.2 ⟨subd8_0_196, List.forall_mem_cons.2 ⟨subd8_0_197, List.forall_mem_cons.2 ⟨subd8_0_198, List.forall_mem_cons.2 ⟨subd8_0_199, List.forall_mem_cons.2 ⟨subd8_0_200, List.forall_mem_cons.2 ⟨subd8_0_201, List.forall_mem_cons.2 ⟨subd8_0_202, List.forall_mem_cons.2 ⟨subd8_0_203, List.forall_mem_cons.2 ⟨subd8_0_204, List.forall_mem_cons.2 ⟨subd8_0_205, List.forall_mem_cons.2 ⟨subd8_0_206, List.forall_mem_cons.2 ⟨subd8_0_207, List.forall_mem_cons.2 ⟨subd8_0_208, List.forall_mem_cons.2 ⟨subd8_0_209, List.forall_mem_cons.2 ⟨subd8_0_210, List.forall_mem_cons.2 ⟨subd8_0_211, List.forall_mem_cons.2 ⟨subd8_0_212, List.forall_mem_cons.2 ⟨subd8_0_213, List.forall_mem_cons.2 ⟨subd8_0_214, List.forall_mem_cons.2 ⟨subd8_0_215, List.forall_mem_cons.2 ⟨subd8_0_216, List.forall_mem_cons.2 ⟨subd8_0_217, List.forall_mem_cons.2 ⟨subd8_0_218, List.forall_mem_cons.2 ⟨subd8_0_219, List.forall_mem_cons.2 ⟨subd8_0_220, List.forall_mem_cons.2 ⟨subd8_0_221, List.forall_mem_cons.2 ⟨subd8_0_222, List.forall_mem_cons.2 ⟨subd8_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
