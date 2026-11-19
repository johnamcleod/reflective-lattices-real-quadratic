import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_11_96 : subd6_11 [2, -3] = true := by decide +kernel
theorem subd6_11_97 : subd6_11 [2, -2] = true := by decide +kernel
theorem subd6_11_98 : subd6_11 [2, -1] = true := by decide +kernel
theorem subd6_11_99 : subd6_11 [2, 0] = true := by decide +kernel
theorem subd6_11_100 : subd6_11 [2, 1] = true := by decide +kernel
theorem subd6_11_101 : subd6_11 [2, 2] = true := by decide +kernel
theorem subd6_11_102 : subd6_11 [2, 3] = true := by decide +kernel
theorem subd6_11_103 : subd6_11 [2, 4] = true := by decide +kernel
theorem subd6_11_104 : subd6_11 [2, 5] = true := by decide +kernel
theorem subd6_11_105 : subd6_11 [2, 6] = true := by decide +kernel
theorem subd6_11_106 : subd6_11 [3, -7] = true := by decide +kernel
theorem subd6_11_107 : subd6_11 [3, -6] = true := by decide +kernel
theorem subd6_11_108 : subd6_11 [3, -5] = true := by decide +kernel
theorem subd6_11_109 : subd6_11 [3, -4] = true := by decide +kernel
theorem subd6_11_110 : subd6_11 [3, -3] = true := by decide +kernel
theorem subd6_11_111 : subd6_11 [3, -2] = true := by decide +kernel
theorem subd6_11_112 : subd6_11 [3, -1] = true := by decide +kernel
theorem subd6_11_113 : subd6_11 [3, 0] = true := by decide +kernel
theorem subd6_11_114 : subd6_11 [3, 1] = true := by decide +kernel
theorem subd6_11_115 : subd6_11 [3, 2] = true := by decide +kernel
theorem subd6_11_116 : subd6_11 [3, 3] = true := by decide +kernel
theorem subd6_11_117 : subd6_11 [3, 4] = true := by decide +kernel
theorem subd6_11_118 : subd6_11 [3, 5] = true := by decide +kernel
theorem subd6_11_119 : subd6_11 [4, -7] = true := by decide +kernel
theorem subd6_11_120 : subd6_11 [4, -6] = true := by decide +kernel
theorem subd6_11_121 : subd6_11 [4, -5] = true := by decide +kernel
theorem subd6_11_122 : subd6_11 [4, -4] = true := by decide +kernel
theorem subd6_11_123 : subd6_11 [4, -3] = true := by decide +kernel
theorem subd6_11_124 : subd6_11 [4, -2] = true := by decide +kernel
theorem subd6_11_125 : subd6_11 [4, -1] = true := by decide +kernel
theorem subd6_11_126 : subd6_11 [4, 0] = true := by decide +kernel
theorem subd6_11_127 : subd6_11 [4, 1] = true := by decide +kernel
theorem sbd6_11_3 : ∀ q ∈ blkd6_11_3, subd6_11 q = true := by
  unfold blkd6_11_3
  exact List.forall_mem_cons.2 ⟨subd6_11_96, List.forall_mem_cons.2 ⟨subd6_11_97, List.forall_mem_cons.2 ⟨subd6_11_98, List.forall_mem_cons.2 ⟨subd6_11_99, List.forall_mem_cons.2 ⟨subd6_11_100, List.forall_mem_cons.2 ⟨subd6_11_101, List.forall_mem_cons.2 ⟨subd6_11_102, List.forall_mem_cons.2 ⟨subd6_11_103, List.forall_mem_cons.2 ⟨subd6_11_104, List.forall_mem_cons.2 ⟨subd6_11_105, List.forall_mem_cons.2 ⟨subd6_11_106, List.forall_mem_cons.2 ⟨subd6_11_107, List.forall_mem_cons.2 ⟨subd6_11_108, List.forall_mem_cons.2 ⟨subd6_11_109, List.forall_mem_cons.2 ⟨subd6_11_110, List.forall_mem_cons.2 ⟨subd6_11_111, List.forall_mem_cons.2 ⟨subd6_11_112, List.forall_mem_cons.2 ⟨subd6_11_113, List.forall_mem_cons.2 ⟨subd6_11_114, List.forall_mem_cons.2 ⟨subd6_11_115, List.forall_mem_cons.2 ⟨subd6_11_116, List.forall_mem_cons.2 ⟨subd6_11_117, List.forall_mem_cons.2 ⟨subd6_11_118, List.forall_mem_cons.2 ⟨subd6_11_119, List.forall_mem_cons.2 ⟨subd6_11_120, List.forall_mem_cons.2 ⟨subd6_11_121, List.forall_mem_cons.2 ⟨subd6_11_122, List.forall_mem_cons.2 ⟨subd6_11_123, List.forall_mem_cons.2 ⟨subd6_11_124, List.forall_mem_cons.2 ⟨subd6_11_125, List.forall_mem_cons.2 ⟨subd6_11_126, List.forall_mem_cons.2 ⟨subd6_11_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_11_128 : subd6_11 [4, 2] = true := by decide +kernel
theorem subd6_11_129 : subd6_11 [4, 3] = true := by decide +kernel
theorem subd6_11_130 : subd6_11 [4, 4] = true := by decide +kernel
theorem subd6_11_131 : subd6_11 [5, -6] = true := by decide +kernel
theorem subd6_11_132 : subd6_11 [5, -5] = true := by decide +kernel
theorem subd6_11_133 : subd6_11 [5, -4] = true := by decide +kernel
theorem subd6_11_134 : subd6_11 [5, -3] = true := by decide +kernel
theorem subd6_11_135 : subd6_11 [5, -2] = true := by decide +kernel
theorem subd6_11_136 : subd6_11 [5, -1] = true := by decide +kernel
theorem subd6_11_137 : subd6_11 [5, 0] = true := by decide +kernel
theorem subd6_11_138 : subd6_11 [5, 1] = true := by decide +kernel
theorem subd6_11_139 : subd6_11 [5, 2] = true := by decide +kernel
theorem subd6_11_140 : subd6_11 [5, 3] = true := by decide +kernel
theorem subd6_11_141 : subd6_11 [6] = true := by decide +kernel
theorem sbd6_11_4 : ∀ q ∈ blkd6_11_4, subd6_11 q = true := by
  unfold blkd6_11_4
  exact List.forall_mem_cons.2 ⟨subd6_11_128, List.forall_mem_cons.2 ⟨subd6_11_129, List.forall_mem_cons.2 ⟨subd6_11_130, List.forall_mem_cons.2 ⟨subd6_11_131, List.forall_mem_cons.2 ⟨subd6_11_132, List.forall_mem_cons.2 ⟨subd6_11_133, List.forall_mem_cons.2 ⟨subd6_11_134, List.forall_mem_cons.2 ⟨subd6_11_135, List.forall_mem_cons.2 ⟨subd6_11_136, List.forall_mem_cons.2 ⟨subd6_11_137, List.forall_mem_cons.2 ⟨subd6_11_138, List.forall_mem_cons.2 ⟨subd6_11_139, List.forall_mem_cons.2 ⟨subd6_11_140, List.forall_mem_cons.2 ⟨subd6_11_141, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_12 : ldCheck G d6_12.U d6_12.ms ldd6_12 = true := by decide +kernel
theorem pre_okd6_12 : subPre G cell6 d6_12 = true := by decide +kernel
theorem subd6_12_0 : subd6_12 [-5] = true := by decide +kernel
theorem subd6_12_1 : subd6_12 [-4] = true := by decide +kernel
theorem subd6_12_2 : subd6_12 [-3, -5] = true := by decide +kernel
theorem subd6_12_3 : subd6_12 [-3, -4] = true := by decide +kernel
theorem subd6_12_4 : subd6_12 [-3, -3] = true := by decide +kernel
theorem subd6_12_5 : subd6_12 [-3, -2] = true := by decide +kernel
theorem subd6_12_6 : subd6_12 [-3, -1] = true := by decide +kernel
theorem subd6_12_7 : subd6_12 [-3, 0] = true := by decide +kernel
theorem subd6_12_8 : subd6_12 [-3, 1] = true := by decide +kernel
theorem subd6_12_9 : subd6_12 [-3, 2] = true := by decide +kernel
theorem subd6_12_10 : subd6_12 [-2, -5] = true := by decide +kernel
theorem subd6_12_11 : subd6_12 [-2, -4] = true := by decide +kernel
theorem subd6_12_12 : subd6_12 [-2, -3] = true := by decide +kernel
theorem subd6_12_13 : subd6_12 [-2, -2] = true := by decide +kernel
theorem subd6_12_14 : subd6_12 [-2, -1] = true := by decide +kernel
theorem subd6_12_15 : subd6_12 [-2, 0] = true := by decide +kernel
theorem subd6_12_16 : subd6_12 [-2, 1] = true := by decide +kernel
theorem subd6_12_17 : subd6_12 [-2, 2] = true := by decide +kernel
theorem subd6_12_18 : subd6_12 [-2, 3] = true := by decide +kernel
theorem subd6_12_19 : subd6_12 [-1, -5] = true := by decide +kernel
theorem subd6_12_20 : subd6_12 [-1, -4] = true := by decide +kernel
theorem subd6_12_21 : subd6_12 [-1, -3] = true := by decide +kernel
theorem subd6_12_22 : subd6_12 [-1, -2] = true := by decide +kernel
theorem subd6_12_23 : subd6_12 [-1, -1] = true := by decide +kernel
theorem subd6_12_24 : subd6_12 [-1, 0] = true := by decide +kernel
theorem subd6_12_25 : subd6_12 [-1, 1] = true := by decide +kernel
theorem subd6_12_26 : subd6_12 [-1, 2] = true := by decide +kernel
theorem subd6_12_27 : subd6_12 [-1, 3] = true := by decide +kernel
theorem subd6_12_28 : subd6_12 [0, -5] = true := by decide +kernel
theorem subd6_12_29 : subd6_12 [0, -4] = true := by decide +kernel
theorem subd6_12_30 : subd6_12 [0, -3] = true := by decide +kernel
theorem subd6_12_31 : subd6_12 [0, -2] = true := by decide +kernel
theorem sbd6_12_0 : ∀ q ∈ blkd6_12_0, subd6_12 q = true := by
  unfold blkd6_12_0
  exact List.forall_mem_cons.2 ⟨subd6_12_0, List.forall_mem_cons.2 ⟨subd6_12_1, List.forall_mem_cons.2 ⟨subd6_12_2, List.forall_mem_cons.2 ⟨subd6_12_3, List.forall_mem_cons.2 ⟨subd6_12_4, List.forall_mem_cons.2 ⟨subd6_12_5, List.forall_mem_cons.2 ⟨subd6_12_6, List.forall_mem_cons.2 ⟨subd6_12_7, List.forall_mem_cons.2 ⟨subd6_12_8, List.forall_mem_cons.2 ⟨subd6_12_9, List.forall_mem_cons.2 ⟨subd6_12_10, List.forall_mem_cons.2 ⟨subd6_12_11, List.forall_mem_cons.2 ⟨subd6_12_12, List.forall_mem_cons.2 ⟨subd6_12_13, List.forall_mem_cons.2 ⟨subd6_12_14, List.forall_mem_cons.2 ⟨subd6_12_15, List.forall_mem_cons.2 ⟨subd6_12_16, List.forall_mem_cons.2 ⟨subd6_12_17, List.forall_mem_cons.2 ⟨subd6_12_18, List.forall_mem_cons.2 ⟨subd6_12_19, List.forall_mem_cons.2 ⟨subd6_12_20, List.forall_mem_cons.2 ⟨subd6_12_21, List.forall_mem_cons.2 ⟨subd6_12_22, List.forall_mem_cons.2 ⟨subd6_12_23, List.forall_mem_cons.2 ⟨subd6_12_24, List.forall_mem_cons.2 ⟨subd6_12_25, List.forall_mem_cons.2 ⟨subd6_12_26, List.forall_mem_cons.2 ⟨subd6_12_27, List.forall_mem_cons.2 ⟨subd6_12_28, List.forall_mem_cons.2 ⟨subd6_12_29, List.forall_mem_cons.2 ⟨subd6_12_30, List.forall_mem_cons.2 ⟨subd6_12_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_12_32 : subd6_12 [0, -1] = true := by decide +kernel
theorem subd6_12_33 : subd6_12 [0, 0] = true := by decide +kernel
theorem subd6_12_34 : subd6_12 [0, 1] = true := by decide +kernel
theorem subd6_12_35 : subd6_12 [0, 2] = true := by decide +kernel
theorem subd6_12_36 : subd6_12 [0, 3] = true := by decide +kernel
theorem subd6_12_37 : subd6_12 [0, 4] = true := by decide +kernel
theorem subd6_12_38 : subd6_12 [1, -4] = true := by decide +kernel
theorem subd6_12_39 : subd6_12 [1, -3] = true := by decide +kernel
theorem subd6_12_40 : subd6_12 [1, -2] = true := by decide +kernel
theorem subd6_12_41 : subd6_12 [1, -1] = true := by decide +kernel
theorem subd6_12_42 : subd6_12 [1, 0] = true := by decide +kernel
theorem subd6_12_43 : subd6_12 [1, 1] = true := by decide +kernel
theorem subd6_12_44 : subd6_12 [1, 2] = true := by decide +kernel
theorem subd6_12_45 : subd6_12 [1, 3] = true := by decide +kernel
theorem subd6_12_46 : subd6_12 [1, 4] = true := by decide +kernel
theorem subd6_12_47 : subd6_12 [2, -4] = true := by decide +kernel
theorem subd6_12_48 : subd6_12 [2, -3] = true := by decide +kernel
theorem subd6_12_49 : subd6_12 [2, -2] = true := by decide +kernel
theorem subd6_12_50 : subd6_12 [2, -1] = true := by decide +kernel
theorem subd6_12_51 : subd6_12 [2, 0] = true := by decide +kernel
theorem subd6_12_52 : subd6_12 [2, 1] = true := by decide +kernel
theorem subd6_12_53 : subd6_12 [2, 2] = true := by decide +kernel
theorem subd6_12_54 : subd6_12 [2, 3] = true := by decide +kernel
theorem subd6_12_55 : subd6_12 [2, 4] = true := by decide +kernel
theorem subd6_12_56 : subd6_12 [3, -3] = true := by decide +kernel
theorem subd6_12_57 : subd6_12 [3, -2] = true := by decide +kernel
theorem subd6_12_58 : subd6_12 [3, -1] = true := by decide +kernel
theorem subd6_12_59 : subd6_12 [3, 0] = true := by decide +kernel
theorem subd6_12_60 : subd6_12 [3, 1] = true := by decide +kernel
theorem subd6_12_61 : subd6_12 [3, 2] = true := by decide +kernel
theorem subd6_12_62 : subd6_12 [3, 3] = true := by decide +kernel
theorem subd6_12_63 : subd6_12 [3, 4] = true := by decide +kernel
theorem sbd6_12_1 : ∀ q ∈ blkd6_12_1, subd6_12 q = true := by
  unfold blkd6_12_1
  exact List.forall_mem_cons.2 ⟨subd6_12_32, List.forall_mem_cons.2 ⟨subd6_12_33, List.forall_mem_cons.2 ⟨subd6_12_34, List.forall_mem_cons.2 ⟨subd6_12_35, List.forall_mem_cons.2 ⟨subd6_12_36, List.forall_mem_cons.2 ⟨subd6_12_37, List.forall_mem_cons.2 ⟨subd6_12_38, List.forall_mem_cons.2 ⟨subd6_12_39, List.forall_mem_cons.2 ⟨subd6_12_40, List.forall_mem_cons.2 ⟨subd6_12_41, List.forall_mem_cons.2 ⟨subd6_12_42, List.forall_mem_cons.2 ⟨subd6_12_43, List.forall_mem_cons.2 ⟨subd6_12_44, List.forall_mem_cons.2 ⟨subd6_12_45, List.forall_mem_cons.2 ⟨subd6_12_46, List.forall_mem_cons.2 ⟨subd6_12_47, List.forall_mem_cons.2 ⟨subd6_12_48, List.forall_mem_cons.2 ⟨subd6_12_49, List.forall_mem_cons.2 ⟨subd6_12_50, List.forall_mem_cons.2 ⟨subd6_12_51, List.forall_mem_cons.2 ⟨subd6_12_52, List.forall_mem_cons.2 ⟨subd6_12_53, List.forall_mem_cons.2 ⟨subd6_12_54, List.forall_mem_cons.2 ⟨subd6_12_55, List.forall_mem_cons.2 ⟨subd6_12_56, List.forall_mem_cons.2 ⟨subd6_12_57, List.forall_mem_cons.2 ⟨subd6_12_58, List.forall_mem_cons.2 ⟨subd6_12_59, List.forall_mem_cons.2 ⟨subd6_12_60, List.forall_mem_cons.2 ⟨subd6_12_61, List.forall_mem_cons.2 ⟨subd6_12_62, List.forall_mem_cons.2 ⟨subd6_12_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_12_64 : subd6_12 [4] = true := by decide +kernel
theorem subd6_12_65 : subd6_12 [5] = true := by decide +kernel
theorem sbd6_12_2 : ∀ q ∈ blkd6_12_2, subd6_12 q = true := by
  unfold blkd6_12_2
  exact List.forall_mem_cons.2 ⟨subd6_12_64, List.forall_mem_cons.2 ⟨subd6_12_65, List.forall_mem_nil _⟩⟩

end ReflectZphi.Data.Cert5.C124
