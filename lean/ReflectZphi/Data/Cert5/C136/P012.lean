import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_96 : subd8_2 [0, 1, -2] = true := by decide +kernel
theorem subd8_2_97 : subd8_2 [0, 1, -1] = true := by decide +kernel
theorem subd8_2_98 : subd8_2 [0, 1, 0] = true := by decide +kernel
theorem subd8_2_99 : subd8_2 [0, 1, 1] = true := by decide +kernel
theorem subd8_2_100 : subd8_2 [0, 1, 2] = true := by decide +kernel
theorem subd8_2_101 : subd8_2 [0, 1, 3] = true := by decide +kernel
theorem subd8_2_102 : subd8_2 [0, 1, 4] = true := by decide +kernel
theorem subd8_2_103 : subd8_2 [0, 1, 5] = true := by decide +kernel
theorem subd8_2_104 : subd8_2 [0, 1, 6] = true := by decide +kernel
theorem subd8_2_105 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_106 : subd8_2 [0, 3] = true := by decide +kernel
theorem subd8_2_107 : subd8_2 [1, -4] = true := by decide +kernel
theorem subd8_2_108 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_109 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_110 : subd8_2 [1, -1, -7] = true := by decide +kernel
theorem subd8_2_111 : subd8_2 [1, -1, -6] = true := by decide +kernel
theorem subd8_2_112 : subd8_2 [1, -1, -5] = true := by decide +kernel
theorem subd8_2_113 : subd8_2 [1, -1, -4] = true := by decide +kernel
theorem subd8_2_114 : subd8_2 [1, -1, -3] = true := by decide +kernel
theorem subd8_2_115 : subd8_2 [1, -1, -2] = true := by decide +kernel
theorem subd8_2_116 : subd8_2 [1, -1, -1] = true := by decide +kernel
theorem subd8_2_117 : subd8_2 [1, -1, 0] = true := by decide +kernel
theorem subd8_2_118 : subd8_2 [1, -1, 1] = true := by decide +kernel
theorem subd8_2_119 : subd8_2 [1, -1, 2] = true := by decide +kernel
theorem subd8_2_120 : subd8_2 [1, -1, 3] = true := by decide +kernel
theorem subd8_2_121 : subd8_2 [1, -1, 4] = true := by decide +kernel
theorem subd8_2_122 : subd8_2 [1, -1, 5] = true := by decide +kernel
theorem subd8_2_123 : subd8_2 [1, -1, 6] = true := by decide +kernel
theorem subd8_2_124 : subd8_2 [1, 0, -8] = true := by decide +kernel
theorem subd8_2_125 : subd8_2 [1, 0, -7] = true := by decide +kernel
theorem subd8_2_126 : subd8_2 [1, 0, -6] = true := by decide +kernel
theorem subd8_2_127 : subd8_2 [1, 0, -5] = true := by decide +kernel
theorem sbd8_2_3 : ∀ q ∈ blkd8_2_3, subd8_2 q = true := by
  unfold blkd8_2_3
  exact List.forall_mem_cons.2 ⟨subd8_2_96, List.forall_mem_cons.2 ⟨subd8_2_97, List.forall_mem_cons.2 ⟨subd8_2_98, List.forall_mem_cons.2 ⟨subd8_2_99, List.forall_mem_cons.2 ⟨subd8_2_100, List.forall_mem_cons.2 ⟨subd8_2_101, List.forall_mem_cons.2 ⟨subd8_2_102, List.forall_mem_cons.2 ⟨subd8_2_103, List.forall_mem_cons.2 ⟨subd8_2_104, List.forall_mem_cons.2 ⟨subd8_2_105, List.forall_mem_cons.2 ⟨subd8_2_106, List.forall_mem_cons.2 ⟨subd8_2_107, List.forall_mem_cons.2 ⟨subd8_2_108, List.forall_mem_cons.2 ⟨subd8_2_109, List.forall_mem_cons.2 ⟨subd8_2_110, List.forall_mem_cons.2 ⟨subd8_2_111, List.forall_mem_cons.2 ⟨subd8_2_112, List.forall_mem_cons.2 ⟨subd8_2_113, List.forall_mem_cons.2 ⟨subd8_2_114, List.forall_mem_cons.2 ⟨subd8_2_115, List.forall_mem_cons.2 ⟨subd8_2_116, List.forall_mem_cons.2 ⟨subd8_2_117, List.forall_mem_cons.2 ⟨subd8_2_118, List.forall_mem_cons.2 ⟨subd8_2_119, List.forall_mem_cons.2 ⟨subd8_2_120, List.forall_mem_cons.2 ⟨subd8_2_121, List.forall_mem_cons.2 ⟨subd8_2_122, List.forall_mem_cons.2 ⟨subd8_2_123, List.forall_mem_cons.2 ⟨subd8_2_124, List.forall_mem_cons.2 ⟨subd8_2_125, List.forall_mem_cons.2 ⟨subd8_2_126, List.forall_mem_cons.2 ⟨subd8_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_128 : subd8_2 [1, 0, -4] = true := by decide +kernel
theorem subd8_2_129 : subd8_2 [1, 0, -3] = true := by decide +kernel
theorem subd8_2_130 : subd8_2 [1, 0, -2] = true := by decide +kernel
theorem subd8_2_131 : subd8_2 [1, 0, -1] = true := by decide +kernel
theorem subd8_2_132 : subd8_2 [1, 0, 0] = true := by decide +kernel
theorem subd8_2_133 : subd8_2 [1, 0, 1] = true := by decide +kernel
theorem subd8_2_134 : subd8_2 [1, 0, 2] = true := by decide +kernel
theorem subd8_2_135 : subd8_2 [1, 0, 3] = true := by decide +kernel
theorem subd8_2_136 : subd8_2 [1, 0, 4] = true := by decide +kernel
theorem subd8_2_137 : subd8_2 [1, 0, 5] = true := by decide +kernel
theorem subd8_2_138 : subd8_2 [1, 0, 6] = true := by decide +kernel
theorem subd8_2_139 : subd8_2 [1, 1, -8] = true := by decide +kernel
theorem subd8_2_140 : subd8_2 [1, 1, -7] = true := by decide +kernel
theorem subd8_2_141 : subd8_2 [1, 1, -6] = true := by decide +kernel
theorem subd8_2_142 : subd8_2 [1, 1, -5] = true := by decide +kernel
theorem subd8_2_143 : subd8_2 [1, 1, -4] = true := by decide +kernel
theorem subd8_2_144 : subd8_2 [1, 1, -3] = true := by decide +kernel
theorem subd8_2_145 : subd8_2 [1, 1, -2] = true := by decide +kernel
theorem subd8_2_146 : subd8_2 [1, 1, -1] = true := by decide +kernel
theorem subd8_2_147 : subd8_2 [1, 1, 0] = true := by decide +kernel
theorem subd8_2_148 : subd8_2 [1, 1, 1] = true := by decide +kernel
theorem subd8_2_149 : subd8_2 [1, 1, 2] = true := by decide +kernel
theorem subd8_2_150 : subd8_2 [1, 1, 3] = true := by decide +kernel
theorem subd8_2_151 : subd8_2 [1, 1, 4] = true := by decide +kernel
theorem subd8_2_152 : subd8_2 [1, 1, 5] = true := by decide +kernel
theorem subd8_2_153 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_154 : subd8_2 [1, 3] = true := by decide +kernel
theorem subd8_2_155 : subd8_2 [2, -4] = true := by decide +kernel
theorem subd8_2_156 : subd8_2 [2, -3] = true := by decide +kernel
theorem subd8_2_157 : subd8_2 [2, -2] = true := by decide +kernel
theorem subd8_2_158 : subd8_2 [2, -1] = true := by decide +kernel
theorem subd8_2_159 : subd8_2 [2, 0] = true := by decide +kernel
theorem sbd8_2_4 : ∀ q ∈ blkd8_2_4, subd8_2 q = true := by
  unfold blkd8_2_4
  exact List.forall_mem_cons.2 ⟨subd8_2_128, List.forall_mem_cons.2 ⟨subd8_2_129, List.forall_mem_cons.2 ⟨subd8_2_130, List.forall_mem_cons.2 ⟨subd8_2_131, List.forall_mem_cons.2 ⟨subd8_2_132, List.forall_mem_cons.2 ⟨subd8_2_133, List.forall_mem_cons.2 ⟨subd8_2_134, List.forall_mem_cons.2 ⟨subd8_2_135, List.forall_mem_cons.2 ⟨subd8_2_136, List.forall_mem_cons.2 ⟨subd8_2_137, List.forall_mem_cons.2 ⟨subd8_2_138, List.forall_mem_cons.2 ⟨subd8_2_139, List.forall_mem_cons.2 ⟨subd8_2_140, List.forall_mem_cons.2 ⟨subd8_2_141, List.forall_mem_cons.2 ⟨subd8_2_142, List.forall_mem_cons.2 ⟨subd8_2_143, List.forall_mem_cons.2 ⟨subd8_2_144, List.forall_mem_cons.2 ⟨subd8_2_145, List.forall_mem_cons.2 ⟨subd8_2_146, List.forall_mem_cons.2 ⟨subd8_2_147, List.forall_mem_cons.2 ⟨subd8_2_148, List.forall_mem_cons.2 ⟨subd8_2_149, List.forall_mem_cons.2 ⟨subd8_2_150, List.forall_mem_cons.2 ⟨subd8_2_151, List.forall_mem_cons.2 ⟨subd8_2_152, List.forall_mem_cons.2 ⟨subd8_2_153, List.forall_mem_cons.2 ⟨subd8_2_154, List.forall_mem_cons.2 ⟨subd8_2_155, List.forall_mem_cons.2 ⟨subd8_2_156, List.forall_mem_cons.2 ⟨subd8_2_157, List.forall_mem_cons.2 ⟨subd8_2_158, List.forall_mem_cons.2 ⟨subd8_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_160 : subd8_2 [2, 1] = true := by decide +kernel
theorem subd8_2_161 : subd8_2 [2, 2] = true := by decide +kernel
theorem subd8_2_162 : subd8_2 [3] = true := by decide +kernel
theorem sbd8_2_5 : ∀ q ∈ blkd8_2_5, subd8_2 q = true := by
  unfold blkd8_2_5
  exact List.forall_mem_cons.2 ⟨subd8_2_160, List.forall_mem_cons.2 ⟨subd8_2_161, List.forall_mem_cons.2 ⟨subd8_2_162, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-5] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-4, -6] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-4, -5] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-4, -4] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-4, -3] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-4, -2] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-4, -1] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-4, 0] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-4, 1] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-3, -6] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-3, -5] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-3, -4] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-3, -3] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-3, -2] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-3, -1] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-3, 0] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [-3, 1] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [-3, 2] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [-3, 3] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [-2, -6] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [-2, -5] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [-2, -4] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [-2, -1] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [-2, 0] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [-2, 1] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [-2, 4] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [-1, -6] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [-1, -5] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_40 : subd8_3 [-1, 4] = true := by decide +kernel
theorem subd8_3_41 : subd8_3 [0, -6] = true := by decide +kernel
theorem subd8_3_42 : subd8_3 [0, -5] = true := by decide +kernel
theorem subd8_3_43 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_44 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_45 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_46 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_47 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_48 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_49 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_50 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_51 : subd8_3 [0, 4] = true := by decide +kernel
theorem subd8_3_52 : subd8_3 [0, 5] = true := by decide +kernel
theorem subd8_3_53 : subd8_3 [1, -5] = true := by decide +kernel
theorem subd8_3_54 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_55 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_56 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_57 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_58 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_59 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_60 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_61 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_62 : subd8_3 [1, 4] = true := by decide +kernel
theorem subd8_3_63 : subd8_3 [1, 5] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_cons.2 ⟨subd8_3_40, List.forall_mem_cons.2 ⟨subd8_3_41, List.forall_mem_cons.2 ⟨subd8_3_42, List.forall_mem_cons.2 ⟨subd8_3_43, List.forall_mem_cons.2 ⟨subd8_3_44, List.forall_mem_cons.2 ⟨subd8_3_45, List.forall_mem_cons.2 ⟨subd8_3_46, List.forall_mem_cons.2 ⟨subd8_3_47, List.forall_mem_cons.2 ⟨subd8_3_48, List.forall_mem_cons.2 ⟨subd8_3_49, List.forall_mem_cons.2 ⟨subd8_3_50, List.forall_mem_cons.2 ⟨subd8_3_51, List.forall_mem_cons.2 ⟨subd8_3_52, List.forall_mem_cons.2 ⟨subd8_3_53, List.forall_mem_cons.2 ⟨subd8_3_54, List.forall_mem_cons.2 ⟨subd8_3_55, List.forall_mem_cons.2 ⟨subd8_3_56, List.forall_mem_cons.2 ⟨subd8_3_57, List.forall_mem_cons.2 ⟨subd8_3_58, List.forall_mem_cons.2 ⟨subd8_3_59, List.forall_mem_cons.2 ⟨subd8_3_60, List.forall_mem_cons.2 ⟨subd8_3_61, List.forall_mem_cons.2 ⟨subd8_3_62, List.forall_mem_cons.2 ⟨subd8_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C136
