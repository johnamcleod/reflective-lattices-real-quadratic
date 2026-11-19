import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_0_64 : subd1_0 [0, 0, -4] = true := by decide +kernel
theorem subd1_0_65 : subd1_0 [0, 0, -3] = true := by decide +kernel
theorem subd1_0_66 : subd1_0 [0, 0, -2] = true := by decide +kernel
theorem subd1_0_67 : subd1_0 [0, 0, -1] = true := by decide +kernel
theorem subd1_0_68 : subd1_0 [0, 0, 0] = true := by decide +kernel
theorem subd1_0_69 : subd1_0 [0, 0, 1] = true := by decide +kernel
theorem subd1_0_70 : subd1_0 [0, 0, 2] = true := by decide +kernel
theorem subd1_0_71 : subd1_0 [0, 0, 3] = true := by decide +kernel
theorem subd1_0_72 : subd1_0 [0, 0, 4] = true := by decide +kernel
theorem subd1_0_73 : subd1_0 [0, 0, 5] = true := by decide +kernel
theorem subd1_0_74 : subd1_0 [0, 0, 6] = true := by decide +kernel
theorem subd1_0_75 : subd1_0 [0, 0, 7] = true := by decide +kernel
theorem subd1_0_76 : subd1_0 [0, 0, 8] = true := by decide +kernel
theorem subd1_0_77 : subd1_0 [0, 0, 9] = true := by decide +kernel
theorem subd1_0_78 : subd1_0 [0, 1, -9] = true := by decide +kernel
theorem subd1_0_79 : subd1_0 [0, 1, -8] = true := by decide +kernel
theorem subd1_0_80 : subd1_0 [0, 1, -7] = true := by decide +kernel
theorem subd1_0_81 : subd1_0 [0, 1, -6] = true := by decide +kernel
theorem subd1_0_82 : subd1_0 [0, 1, -5] = true := by decide +kernel
theorem subd1_0_83 : subd1_0 [0, 1, -4] = true := by decide +kernel
theorem subd1_0_84 : subd1_0 [0, 1, -3] = true := by decide +kernel
theorem subd1_0_85 : subd1_0 [0, 1, -2] = true := by decide +kernel
theorem subd1_0_86 : subd1_0 [0, 1, -1] = true := by decide +kernel
theorem subd1_0_87 : subd1_0 [0, 1, 0] = true := by decide +kernel
theorem subd1_0_88 : subd1_0 [0, 1, 1] = true := by decide +kernel
theorem subd1_0_89 : subd1_0 [0, 1, 2] = true := by decide +kernel
theorem subd1_0_90 : subd1_0 [0, 1, 3] = true := by decide +kernel
theorem subd1_0_91 : subd1_0 [0, 1, 4] = true := by decide +kernel
theorem subd1_0_92 : subd1_0 [0, 1, 5] = true := by decide +kernel
theorem subd1_0_93 : subd1_0 [0, 1, 6] = true := by decide +kernel
theorem subd1_0_94 : subd1_0 [0, 1, 7] = true := by decide +kernel
theorem subd1_0_95 : subd1_0 [0, 1, 8] = true := by decide +kernel
theorem sbd1_0_2 : ∀ q ∈ blkd1_0_2, subd1_0 q = true := by
  unfold blkd1_0_2
  exact List.forall_mem_cons.2 ⟨subd1_0_64, List.forall_mem_cons.2 ⟨subd1_0_65, List.forall_mem_cons.2 ⟨subd1_0_66, List.forall_mem_cons.2 ⟨subd1_0_67, List.forall_mem_cons.2 ⟨subd1_0_68, List.forall_mem_cons.2 ⟨subd1_0_69, List.forall_mem_cons.2 ⟨subd1_0_70, List.forall_mem_cons.2 ⟨subd1_0_71, List.forall_mem_cons.2 ⟨subd1_0_72, List.forall_mem_cons.2 ⟨subd1_0_73, List.forall_mem_cons.2 ⟨subd1_0_74, List.forall_mem_cons.2 ⟨subd1_0_75, List.forall_mem_cons.2 ⟨subd1_0_76, List.forall_mem_cons.2 ⟨subd1_0_77, List.forall_mem_cons.2 ⟨subd1_0_78, List.forall_mem_cons.2 ⟨subd1_0_79, List.forall_mem_cons.2 ⟨subd1_0_80, List.forall_mem_cons.2 ⟨subd1_0_81, List.forall_mem_cons.2 ⟨subd1_0_82, List.forall_mem_cons.2 ⟨subd1_0_83, List.forall_mem_cons.2 ⟨subd1_0_84, List.forall_mem_cons.2 ⟨subd1_0_85, List.forall_mem_cons.2 ⟨subd1_0_86, List.forall_mem_cons.2 ⟨subd1_0_87, List.forall_mem_cons.2 ⟨subd1_0_88, List.forall_mem_cons.2 ⟨subd1_0_89, List.forall_mem_cons.2 ⟨subd1_0_90, List.forall_mem_cons.2 ⟨subd1_0_91, List.forall_mem_cons.2 ⟨subd1_0_92, List.forall_mem_cons.2 ⟨subd1_0_93, List.forall_mem_cons.2 ⟨subd1_0_94, List.forall_mem_cons.2 ⟨subd1_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_0_96 : subd1_0 [0, 2] = true := by decide +kernel
theorem subd1_0_97 : subd1_0 [1, -2] = true := by decide +kernel
theorem subd1_0_98 : subd1_0 [1, -1] = true := by decide +kernel
theorem subd1_0_99 : subd1_0 [1, 0, -9] = true := by decide +kernel
theorem subd1_0_100 : subd1_0 [1, 0, -8] = true := by decide +kernel
theorem subd1_0_101 : subd1_0 [1, 0, -7] = true := by decide +kernel
theorem subd1_0_102 : subd1_0 [1, 0, -6] = true := by decide +kernel
theorem subd1_0_103 : subd1_0 [1, 0, -5] = true := by decide +kernel
theorem subd1_0_104 : subd1_0 [1, 0, -4] = true := by decide +kernel
theorem subd1_0_105 : subd1_0 [1, 0, -3] = true := by decide +kernel
theorem subd1_0_106 : subd1_0 [1, 0, -2] = true := by decide +kernel
theorem subd1_0_107 : subd1_0 [1, 0, -1] = true := by decide +kernel
theorem subd1_0_108 : subd1_0 [1, 0, 0] = true := by decide +kernel
theorem subd1_0_109 : subd1_0 [1, 0, 1] = true := by decide +kernel
theorem subd1_0_110 : subd1_0 [1, 0, 2] = true := by decide +kernel
theorem subd1_0_111 : subd1_0 [1, 0, 3] = true := by decide +kernel
theorem subd1_0_112 : subd1_0 [1, 0, 4] = true := by decide +kernel
theorem subd1_0_113 : subd1_0 [1, 0, 5] = true := by decide +kernel
theorem subd1_0_114 : subd1_0 [1, 0, 6] = true := by decide +kernel
theorem subd1_0_115 : subd1_0 [1, 0, 7] = true := by decide +kernel
theorem subd1_0_116 : subd1_0 [1, 1, -9] = true := by decide +kernel
theorem subd1_0_117 : subd1_0 [1, 1, -8] = true := by decide +kernel
theorem subd1_0_118 : subd1_0 [1, 1, -7] = true := by decide +kernel
theorem subd1_0_119 : subd1_0 [1, 1, -6] = true := by decide +kernel
theorem subd1_0_120 : subd1_0 [1, 1, -5] = true := by decide +kernel
theorem subd1_0_121 : subd1_0 [1, 1, -4] = true := by decide +kernel
theorem subd1_0_122 : subd1_0 [1, 1, -3] = true := by decide +kernel
theorem subd1_0_123 : subd1_0 [1, 1, -2] = true := by decide +kernel
theorem subd1_0_124 : subd1_0 [1, 1, -1] = true := by decide +kernel
theorem subd1_0_125 : subd1_0 [1, 1, 0] = true := by decide +kernel
theorem subd1_0_126 : subd1_0 [1, 1, 1] = true := by decide +kernel
theorem subd1_0_127 : subd1_0 [1, 1, 2] = true := by decide +kernel
theorem sbd1_0_3 : ∀ q ∈ blkd1_0_3, subd1_0 q = true := by
  unfold blkd1_0_3
  exact List.forall_mem_cons.2 ⟨subd1_0_96, List.forall_mem_cons.2 ⟨subd1_0_97, List.forall_mem_cons.2 ⟨subd1_0_98, List.forall_mem_cons.2 ⟨subd1_0_99, List.forall_mem_cons.2 ⟨subd1_0_100, List.forall_mem_cons.2 ⟨subd1_0_101, List.forall_mem_cons.2 ⟨subd1_0_102, List.forall_mem_cons.2 ⟨subd1_0_103, List.forall_mem_cons.2 ⟨subd1_0_104, List.forall_mem_cons.2 ⟨subd1_0_105, List.forall_mem_cons.2 ⟨subd1_0_106, List.forall_mem_cons.2 ⟨subd1_0_107, List.forall_mem_cons.2 ⟨subd1_0_108, List.forall_mem_cons.2 ⟨subd1_0_109, List.forall_mem_cons.2 ⟨subd1_0_110, List.forall_mem_cons.2 ⟨subd1_0_111, List.forall_mem_cons.2 ⟨subd1_0_112, List.forall_mem_cons.2 ⟨subd1_0_113, List.forall_mem_cons.2 ⟨subd1_0_114, List.forall_mem_cons.2 ⟨subd1_0_115, List.forall_mem_cons.2 ⟨subd1_0_116, List.forall_mem_cons.2 ⟨subd1_0_117, List.forall_mem_cons.2 ⟨subd1_0_118, List.forall_mem_cons.2 ⟨subd1_0_119, List.forall_mem_cons.2 ⟨subd1_0_120, List.forall_mem_cons.2 ⟨subd1_0_121, List.forall_mem_cons.2 ⟨subd1_0_122, List.forall_mem_cons.2 ⟨subd1_0_123, List.forall_mem_cons.2 ⟨subd1_0_124, List.forall_mem_cons.2 ⟨subd1_0_125, List.forall_mem_cons.2 ⟨subd1_0_126, List.forall_mem_cons.2 ⟨subd1_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_0_128 : subd1_0 [1, 1, 3] = true := by decide +kernel
theorem subd1_0_129 : subd1_0 [1, 1, 4] = true := by decide +kernel
theorem subd1_0_130 : subd1_0 [1, 1, 5] = true := by decide +kernel
theorem subd1_0_131 : subd1_0 [1, 1, 6] = true := by decide +kernel
theorem subd1_0_132 : subd1_0 [1, 1, 7] = true := by decide +kernel
theorem subd1_0_133 : subd1_0 [1, 2] = true := by decide +kernel
theorem subd1_0_134 : subd1_0 [2] = true := by decide +kernel
theorem sbd1_0_4 : ∀ q ∈ blkd1_0_4, subd1_0 q = true := by
  unfold blkd1_0_4
  exact List.forall_mem_cons.2 ⟨subd1_0_128, List.forall_mem_cons.2 ⟨subd1_0_129, List.forall_mem_cons.2 ⟨subd1_0_130, List.forall_mem_cons.2 ⟨subd1_0_131, List.forall_mem_cons.2 ⟨subd1_0_132, List.forall_mem_cons.2 ⟨subd1_0_133, List.forall_mem_cons.2 ⟨subd1_0_134, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [-1] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [0, -2] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [0, -1] = true := by decide +kernel
theorem subd1_1_3 : subd1_1 [0, 0, -7] = true := by decide +kernel
theorem subd1_1_4 : subd1_1 [0, 0, -6] = true := by decide +kernel
theorem subd1_1_5 : subd1_1 [0, 0, -5] = true := by decide +kernel
theorem subd1_1_6 : subd1_1 [0, 0, -4] = true := by decide +kernel
theorem subd1_1_7 : subd1_1 [0, 0, -3] = true := by decide +kernel
theorem subd1_1_8 : subd1_1 [0, 0, -2] = true := by decide +kernel
theorem subd1_1_9 : subd1_1 [0, 0, -1] = true := by decide +kernel
theorem subd1_1_10 : subd1_1 [0, 0, 0] = true := by decide +kernel
theorem subd1_1_11 : subd1_1 [0, 0, 1] = true := by decide +kernel
theorem subd1_1_12 : subd1_1 [0, 0, 2] = true := by decide +kernel
theorem subd1_1_13 : subd1_1 [0, 0, 3] = true := by decide +kernel
theorem subd1_1_14 : subd1_1 [0, 0, 4] = true := by decide +kernel
theorem subd1_1_15 : subd1_1 [0, 0, 5] = true := by decide +kernel
theorem subd1_1_16 : subd1_1 [0, 0, 6] = true := by decide +kernel
theorem subd1_1_17 : subd1_1 [0, 1] = true := by decide +kernel
theorem subd1_1_18 : subd1_1 [1] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_cons.2 ⟨subd1_1_3, List.forall_mem_cons.2 ⟨subd1_1_4, List.forall_mem_cons.2 ⟨subd1_1_5, List.forall_mem_cons.2 ⟨subd1_1_6, List.forall_mem_cons.2 ⟨subd1_1_7, List.forall_mem_cons.2 ⟨subd1_1_8, List.forall_mem_cons.2 ⟨subd1_1_9, List.forall_mem_cons.2 ⟨subd1_1_10, List.forall_mem_cons.2 ⟨subd1_1_11, List.forall_mem_cons.2 ⟨subd1_1_12, List.forall_mem_cons.2 ⟨subd1_1_13, List.forall_mem_cons.2 ⟨subd1_1_14, List.forall_mem_cons.2 ⟨subd1_1_15, List.forall_mem_cons.2 ⟨subd1_1_16, List.forall_mem_cons.2 ⟨subd1_1_17, List.forall_mem_cons.2 ⟨subd1_1_18, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [-3] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [-2, -3] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [-2, -2] = true := by decide +kernel
theorem subd1_2_3 : subd1_2 [-2, -1] = true := by decide +kernel
theorem subd1_2_4 : subd1_2 [-2, 0] = true := by decide +kernel
theorem subd1_2_5 : subd1_2 [-2, 1] = true := by decide +kernel
theorem subd1_2_6 : subd1_2 [-2, 2] = true := by decide +kernel
theorem subd1_2_7 : subd1_2 [-2, 3] = true := by decide +kernel
theorem subd1_2_8 : subd1_2 [-1, -4] = true := by decide +kernel
theorem subd1_2_9 : subd1_2 [-1, -3] = true := by decide +kernel
theorem subd1_2_10 : subd1_2 [-1, -2] = true := by decide +kernel
theorem subd1_2_11 : subd1_2 [-1, -1] = true := by decide +kernel
theorem subd1_2_12 : subd1_2 [-1, 0] = true := by decide +kernel
theorem subd1_2_13 : subd1_2 [-1, 1] = true := by decide +kernel
theorem subd1_2_14 : subd1_2 [-1, 2] = true := by decide +kernel
theorem subd1_2_15 : subd1_2 [-1, 3] = true := by decide +kernel
theorem subd1_2_16 : subd1_2 [0, -4] = true := by decide +kernel
theorem subd1_2_17 : subd1_2 [0, -3] = true := by decide +kernel
theorem subd1_2_18 : subd1_2 [0, -2] = true := by decide +kernel
theorem subd1_2_19 : subd1_2 [0, -1] = true := by decide +kernel
theorem subd1_2_20 : subd1_2 [0, 0] = true := by decide +kernel
theorem subd1_2_21 : subd1_2 [0, 1] = true := by decide +kernel
theorem subd1_2_22 : subd1_2 [0, 2] = true := by decide +kernel
theorem subd1_2_23 : subd1_2 [0, 3] = true := by decide +kernel
theorem subd1_2_24 : subd1_2 [1, -4] = true := by decide +kernel
theorem subd1_2_25 : subd1_2 [1, -3] = true := by decide +kernel
theorem subd1_2_26 : subd1_2 [1, -2] = true := by decide +kernel
theorem subd1_2_27 : subd1_2 [1, -1] = true := by decide +kernel
theorem subd1_2_28 : subd1_2 [1, 0] = true := by decide +kernel
theorem subd1_2_29 : subd1_2 [1, 1] = true := by decide +kernel
theorem subd1_2_30 : subd1_2 [1, 2] = true := by decide +kernel
theorem subd1_2_31 : subd1_2 [1, 3] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_cons.2 ⟨subd1_2_3, List.forall_mem_cons.2 ⟨subd1_2_4, List.forall_mem_cons.2 ⟨subd1_2_5, List.forall_mem_cons.2 ⟨subd1_2_6, List.forall_mem_cons.2 ⟨subd1_2_7, List.forall_mem_cons.2 ⟨subd1_2_8, List.forall_mem_cons.2 ⟨subd1_2_9, List.forall_mem_cons.2 ⟨subd1_2_10, List.forall_mem_cons.2 ⟨subd1_2_11, List.forall_mem_cons.2 ⟨subd1_2_12, List.forall_mem_cons.2 ⟨subd1_2_13, List.forall_mem_cons.2 ⟨subd1_2_14, List.forall_mem_cons.2 ⟨subd1_2_15, List.forall_mem_cons.2 ⟨subd1_2_16, List.forall_mem_cons.2 ⟨subd1_2_17, List.forall_mem_cons.2 ⟨subd1_2_18, List.forall_mem_cons.2 ⟨subd1_2_19, List.forall_mem_cons.2 ⟨subd1_2_20, List.forall_mem_cons.2 ⟨subd1_2_21, List.forall_mem_cons.2 ⟨subd1_2_22, List.forall_mem_cons.2 ⟨subd1_2_23, List.forall_mem_cons.2 ⟨subd1_2_24, List.forall_mem_cons.2 ⟨subd1_2_25, List.forall_mem_cons.2 ⟨subd1_2_26, List.forall_mem_cons.2 ⟨subd1_2_27, List.forall_mem_cons.2 ⟨subd1_2_28, List.forall_mem_cons.2 ⟨subd1_2_29, List.forall_mem_cons.2 ⟨subd1_2_30, List.forall_mem_cons.2 ⟨subd1_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_2_32 : subd1_2 [2, -4] = true := by decide +kernel
theorem subd1_2_33 : subd1_2 [2, -3] = true := by decide +kernel
theorem subd1_2_34 : subd1_2 [2, -2] = true := by decide +kernel
theorem subd1_2_35 : subd1_2 [2, -1] = true := by decide +kernel
theorem subd1_2_36 : subd1_2 [2, 0] = true := by decide +kernel
theorem subd1_2_37 : subd1_2 [2, 1] = true := by decide +kernel
theorem subd1_2_38 : subd1_2 [2, 2] = true := by decide +kernel
theorem subd1_2_39 : subd1_2 [3] = true := by decide +kernel
theorem sbd1_2_1 : ∀ q ∈ blkd1_2_1, subd1_2 q = true := by
  unfold blkd1_2_1
  exact List.forall_mem_cons.2 ⟨subd1_2_32, List.forall_mem_cons.2 ⟨subd1_2_33, List.forall_mem_cons.2 ⟨subd1_2_34, List.forall_mem_cons.2 ⟨subd1_2_35, List.forall_mem_cons.2 ⟨subd1_2_36, List.forall_mem_cons.2 ⟨subd1_2_37, List.forall_mem_cons.2 ⟨subd1_2_38, List.forall_mem_cons.2 ⟨subd1_2_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-2] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-1] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [0] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [1] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [2] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C141
