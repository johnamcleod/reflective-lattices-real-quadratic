import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_96 : subd9_3 [2, 5] = true := by decide +kernel
theorem subd9_3_97 : subd9_3 [2, 6] = true := by decide +kernel
theorem subd9_3_98 : subd9_3 [3, -4] = true := by decide +kernel
theorem subd9_3_99 : subd9_3 [3, -3] = true := by decide +kernel
theorem subd9_3_100 : subd9_3 [3, -2] = true := by decide +kernel
theorem subd9_3_101 : subd9_3 [3, -1] = true := by decide +kernel
theorem subd9_3_102 : subd9_3 [3, 0] = true := by decide +kernel
theorem subd9_3_103 : subd9_3 [3, 1] = true := by decide +kernel
theorem subd9_3_104 : subd9_3 [3, 2] = true := by decide +kernel
theorem subd9_3_105 : subd9_3 [3, 3] = true := by decide +kernel
theorem subd9_3_106 : subd9_3 [3, 4] = true := by decide +kernel
theorem subd9_3_107 : subd9_3 [3, 5] = true := by decide +kernel
theorem subd9_3_108 : subd9_3 [3, 6] = true := by decide +kernel
theorem subd9_3_109 : subd9_3 [4, -3] = true := by decide +kernel
theorem subd9_3_110 : subd9_3 [4, -2] = true := by decide +kernel
theorem subd9_3_111 : subd9_3 [4, -1] = true := by decide +kernel
theorem subd9_3_112 : subd9_3 [4, 0] = true := by decide +kernel
theorem subd9_3_113 : subd9_3 [4, 1] = true := by decide +kernel
theorem subd9_3_114 : subd9_3 [4, 2] = true := by decide +kernel
theorem subd9_3_115 : subd9_3 [4, 3] = true := by decide +kernel
theorem subd9_3_116 : subd9_3 [4, 4] = true := by decide +kernel
theorem subd9_3_117 : subd9_3 [4, 5] = true := by decide +kernel
theorem subd9_3_118 : subd9_3 [4, 6] = true := by decide +kernel
theorem subd9_3_119 : subd9_3 [5, -2] = true := by decide +kernel
theorem subd9_3_120 : subd9_3 [5, -1] = true := by decide +kernel
theorem subd9_3_121 : subd9_3 [5, 0] = true := by decide +kernel
theorem subd9_3_122 : subd9_3 [5, 1] = true := by decide +kernel
theorem subd9_3_123 : subd9_3 [5, 2] = true := by decide +kernel
theorem subd9_3_124 : subd9_3 [5, 3] = true := by decide +kernel
theorem subd9_3_125 : subd9_3 [5, 4] = true := by decide +kernel
theorem subd9_3_126 : subd9_3 [5, 5] = true := by decide +kernel
theorem subd9_3_127 : subd9_3 [5, 6] = true := by decide +kernel
theorem sbd9_3_3 : ∀ q ∈ blkd9_3_3, subd9_3 q = true := by
  unfold blkd9_3_3
  exact List.forall_mem_cons.2 ⟨subd9_3_96, List.forall_mem_cons.2 ⟨subd9_3_97, List.forall_mem_cons.2 ⟨subd9_3_98, List.forall_mem_cons.2 ⟨subd9_3_99, List.forall_mem_cons.2 ⟨subd9_3_100, List.forall_mem_cons.2 ⟨subd9_3_101, List.forall_mem_cons.2 ⟨subd9_3_102, List.forall_mem_cons.2 ⟨subd9_3_103, List.forall_mem_cons.2 ⟨subd9_3_104, List.forall_mem_cons.2 ⟨subd9_3_105, List.forall_mem_cons.2 ⟨subd9_3_106, List.forall_mem_cons.2 ⟨subd9_3_107, List.forall_mem_cons.2 ⟨subd9_3_108, List.forall_mem_cons.2 ⟨subd9_3_109, List.forall_mem_cons.2 ⟨subd9_3_110, List.forall_mem_cons.2 ⟨subd9_3_111, List.forall_mem_cons.2 ⟨subd9_3_112, List.forall_mem_cons.2 ⟨subd9_3_113, List.forall_mem_cons.2 ⟨subd9_3_114, List.forall_mem_cons.2 ⟨subd9_3_115, List.forall_mem_cons.2 ⟨subd9_3_116, List.forall_mem_cons.2 ⟨subd9_3_117, List.forall_mem_cons.2 ⟨subd9_3_118, List.forall_mem_cons.2 ⟨subd9_3_119, List.forall_mem_cons.2 ⟨subd9_3_120, List.forall_mem_cons.2 ⟨subd9_3_121, List.forall_mem_cons.2 ⟨subd9_3_122, List.forall_mem_cons.2 ⟨subd9_3_123, List.forall_mem_cons.2 ⟨subd9_3_124, List.forall_mem_cons.2 ⟨subd9_3_125, List.forall_mem_cons.2 ⟨subd9_3_126, List.forall_mem_cons.2 ⟨subd9_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_128 : subd9_3 [6, -1] = true := by decide +kernel
theorem subd9_3_129 : subd9_3 [6, 0] = true := by decide +kernel
theorem subd9_3_130 : subd9_3 [6, 1] = true := by decide +kernel
theorem subd9_3_131 : subd9_3 [6, 2] = true := by decide +kernel
theorem subd9_3_132 : subd9_3 [6, 3] = true := by decide +kernel
theorem subd9_3_133 : subd9_3 [6, 4] = true := by decide +kernel
theorem subd9_3_134 : subd9_3 [6, 5] = true := by decide +kernel
theorem subd9_3_135 : subd9_3 [7] = true := by decide +kernel
theorem sbd9_3_4 : ∀ q ∈ blkd9_3_4, subd9_3 q = true := by
  unfold blkd9_3_4
  exact List.forall_mem_cons.2 ⟨subd9_3_128, List.forall_mem_cons.2 ⟨subd9_3_129, List.forall_mem_cons.2 ⟨subd9_3_130, List.forall_mem_cons.2 ⟨subd9_3_131, List.forall_mem_cons.2 ⟨subd9_3_132, List.forall_mem_cons.2 ⟨subd9_3_133, List.forall_mem_cons.2 ⟨subd9_3_134, List.forall_mem_cons.2 ⟨subd9_3_135, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-4] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-3, -3] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-3, -2] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-3, -1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-3, 0] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-3, 1] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-3, 2] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-3, 3] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [-2, -4] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [-2, -3] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [-2, -2] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [-2, -1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [-2, 0] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [-2, 1] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [-2, 2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [-2, 3] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [-1, -4] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [-1, 3] = true := by decide +kernel
theorem subd10_0_24 : subd10_0 [0, -5] = true := by decide +kernel
theorem subd10_0_25 : subd10_0 [0, -4] = true := by decide +kernel
theorem subd10_0_26 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_27 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_28 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_29 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_30 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_31 : subd10_0 [0, 2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_cons.2 ⟨subd10_0_24, List.forall_mem_cons.2 ⟨subd10_0_25, List.forall_mem_cons.2 ⟨subd10_0_26, List.forall_mem_cons.2 ⟨subd10_0_27, List.forall_mem_cons.2 ⟨subd10_0_28, List.forall_mem_cons.2 ⟨subd10_0_29, List.forall_mem_cons.2 ⟨subd10_0_30, List.forall_mem_cons.2 ⟨subd10_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_32 : subd10_0 [0, 3] = true := by decide +kernel
theorem subd10_0_33 : subd10_0 [0, 4] = true := by decide +kernel
theorem subd10_0_34 : subd10_0 [1, -4] = true := by decide +kernel
theorem subd10_0_35 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_36 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_37 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_38 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_39 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_40 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_41 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_42 : subd10_0 [2, -4] = true := by decide +kernel
theorem subd10_0_43 : subd10_0 [2, -3] = true := by decide +kernel
theorem subd10_0_44 : subd10_0 [2, -2] = true := by decide +kernel
theorem subd10_0_45 : subd10_0 [2, -1] = true := by decide +kernel
theorem subd10_0_46 : subd10_0 [2, 0] = true := by decide +kernel
theorem subd10_0_47 : subd10_0 [2, 1] = true := by decide +kernel
theorem subd10_0_48 : subd10_0 [2, 2] = true := by decide +kernel
theorem subd10_0_49 : subd10_0 [2, 3] = true := by decide +kernel
theorem subd10_0_50 : subd10_0 [3, -4] = true := by decide +kernel
theorem subd10_0_51 : subd10_0 [3, -3] = true := by decide +kernel
theorem subd10_0_52 : subd10_0 [3, -2] = true := by decide +kernel
theorem subd10_0_53 : subd10_0 [3, -1] = true := by decide +kernel
theorem subd10_0_54 : subd10_0 [3, 0] = true := by decide +kernel
theorem subd10_0_55 : subd10_0 [3, 1] = true := by decide +kernel
theorem subd10_0_56 : subd10_0 [3, 2] = true := by decide +kernel
theorem subd10_0_57 : subd10_0 [4] = true := by decide +kernel
theorem sbd10_0_1 : ∀ q ∈ blkd10_0_1, subd10_0 q = true := by
  unfold blkd10_0_1
  exact List.forall_mem_cons.2 ⟨subd10_0_32, List.forall_mem_cons.2 ⟨subd10_0_33, List.forall_mem_cons.2 ⟨subd10_0_34, List.forall_mem_cons.2 ⟨subd10_0_35, List.forall_mem_cons.2 ⟨subd10_0_36, List.forall_mem_cons.2 ⟨subd10_0_37, List.forall_mem_cons.2 ⟨subd10_0_38, List.forall_mem_cons.2 ⟨subd10_0_39, List.forall_mem_cons.2 ⟨subd10_0_40, List.forall_mem_cons.2 ⟨subd10_0_41, List.forall_mem_cons.2 ⟨subd10_0_42, List.forall_mem_cons.2 ⟨subd10_0_43, List.forall_mem_cons.2 ⟨subd10_0_44, List.forall_mem_cons.2 ⟨subd10_0_45, List.forall_mem_cons.2 ⟨subd10_0_46, List.forall_mem_cons.2 ⟨subd10_0_47, List.forall_mem_cons.2 ⟨subd10_0_48, List.forall_mem_cons.2 ⟨subd10_0_49, List.forall_mem_cons.2 ⟨subd10_0_50, List.forall_mem_cons.2 ⟨subd10_0_51, List.forall_mem_cons.2 ⟨subd10_0_52, List.forall_mem_cons.2 ⟨subd10_0_53, List.forall_mem_cons.2 ⟨subd10_0_54, List.forall_mem_cons.2 ⟨subd10_0_55, List.forall_mem_cons.2 ⟨subd10_0_56, List.forall_mem_cons.2 ⟨subd10_0_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
