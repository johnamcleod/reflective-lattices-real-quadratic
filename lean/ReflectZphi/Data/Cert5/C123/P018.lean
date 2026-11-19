import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_96 : subd8_4 [0, 1, -2] = true := by decide +kernel
theorem subd8_4_97 : subd8_4 [0, 1, -1] = true := by decide +kernel
theorem subd8_4_98 : subd8_4 [0, 1, 0] = true := by decide +kernel
theorem subd8_4_99 : subd8_4 [0, 1, 1] = true := by decide +kernel
theorem subd8_4_100 : subd8_4 [0, 1, 2] = true := by decide +kernel
theorem subd8_4_101 : subd8_4 [0, 1, 3] = true := by decide +kernel
theorem subd8_4_102 : subd8_4 [0, 1, 4] = true := by decide +kernel
theorem subd8_4_103 : subd8_4 [0, 1, 5] = true := by decide +kernel
theorem subd8_4_104 : subd8_4 [0, 1, 6] = true := by decide +kernel
theorem subd8_4_105 : subd8_4 [0, 1, 7] = true := by decide +kernel
theorem subd8_4_106 : subd8_4 [0, 2] = true := by decide +kernel
theorem subd8_4_107 : subd8_4 [0, 3] = true := by decide +kernel
theorem subd8_4_108 : subd8_4 [1, -4] = true := by decide +kernel
theorem subd8_4_109 : subd8_4 [1, -3] = true := by decide +kernel
theorem subd8_4_110 : subd8_4 [1, -2] = true := by decide +kernel
theorem subd8_4_111 : subd8_4 [1, -1, -8] = true := by decide +kernel
theorem subd8_4_112 : subd8_4 [1, -1, -7] = true := by decide +kernel
theorem subd8_4_113 : subd8_4 [1, -1, -6] = true := by decide +kernel
theorem subd8_4_114 : subd8_4 [1, -1, -5] = true := by decide +kernel
theorem subd8_4_115 : subd8_4 [1, -1, -4] = true := by decide +kernel
theorem subd8_4_116 : subd8_4 [1, -1, -3] = true := by decide +kernel
theorem subd8_4_117 : subd8_4 [1, -1, -2] = true := by decide +kernel
theorem subd8_4_118 : subd8_4 [1, -1, -1] = true := by decide +kernel
theorem subd8_4_119 : subd8_4 [1, -1, 0] = true := by decide +kernel
theorem subd8_4_120 : subd8_4 [1, -1, 1] = true := by decide +kernel
theorem subd8_4_121 : subd8_4 [1, -1, 2] = true := by decide +kernel
theorem subd8_4_122 : subd8_4 [1, -1, 3] = true := by decide +kernel
theorem subd8_4_123 : subd8_4 [1, -1, 4] = true := by decide +kernel
theorem subd8_4_124 : subd8_4 [1, -1, 5] = true := by decide +kernel
theorem subd8_4_125 : subd8_4 [1, -1, 6] = true := by decide +kernel
theorem subd8_4_126 : subd8_4 [1, 0, -7] = true := by decide +kernel
theorem subd8_4_127 : subd8_4 [1, 0, -6] = true := by decide +kernel
theorem sbd8_4_3 : ∀ q ∈ blkd8_4_3, subd8_4 q = true := by
  unfold blkd8_4_3
  exact List.forall_mem_cons.2 ⟨subd8_4_96, List.forall_mem_cons.2 ⟨subd8_4_97, List.forall_mem_cons.2 ⟨subd8_4_98, List.forall_mem_cons.2 ⟨subd8_4_99, List.forall_mem_cons.2 ⟨subd8_4_100, List.forall_mem_cons.2 ⟨subd8_4_101, List.forall_mem_cons.2 ⟨subd8_4_102, List.forall_mem_cons.2 ⟨subd8_4_103, List.forall_mem_cons.2 ⟨subd8_4_104, List.forall_mem_cons.2 ⟨subd8_4_105, List.forall_mem_cons.2 ⟨subd8_4_106, List.forall_mem_cons.2 ⟨subd8_4_107, List.forall_mem_cons.2 ⟨subd8_4_108, List.forall_mem_cons.2 ⟨subd8_4_109, List.forall_mem_cons.2 ⟨subd8_4_110, List.forall_mem_cons.2 ⟨subd8_4_111, List.forall_mem_cons.2 ⟨subd8_4_112, List.forall_mem_cons.2 ⟨subd8_4_113, List.forall_mem_cons.2 ⟨subd8_4_114, List.forall_mem_cons.2 ⟨subd8_4_115, List.forall_mem_cons.2 ⟨subd8_4_116, List.forall_mem_cons.2 ⟨subd8_4_117, List.forall_mem_cons.2 ⟨subd8_4_118, List.forall_mem_cons.2 ⟨subd8_4_119, List.forall_mem_cons.2 ⟨subd8_4_120, List.forall_mem_cons.2 ⟨subd8_4_121, List.forall_mem_cons.2 ⟨subd8_4_122, List.forall_mem_cons.2 ⟨subd8_4_123, List.forall_mem_cons.2 ⟨subd8_4_124, List.forall_mem_cons.2 ⟨subd8_4_125, List.forall_mem_cons.2 ⟨subd8_4_126, List.forall_mem_cons.2 ⟨subd8_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_128 : subd8_4 [1, 0, -5] = true := by decide +kernel
theorem subd8_4_129 : subd8_4 [1, 0, -4] = true := by decide +kernel
theorem subd8_4_130 : subd8_4 [1, 0, -3] = true := by decide +kernel
theorem subd8_4_131 : subd8_4 [1, 0, -2] = true := by decide +kernel
theorem subd8_4_132 : subd8_4 [1, 0, -1] = true := by decide +kernel
theorem subd8_4_133 : subd8_4 [1, 0, 0] = true := by decide +kernel
theorem subd8_4_134 : subd8_4 [1, 0, 1] = true := by decide +kernel
theorem subd8_4_135 : subd8_4 [1, 0, 2] = true := by decide +kernel
theorem subd8_4_136 : subd8_4 [1, 0, 3] = true := by decide +kernel
theorem subd8_4_137 : subd8_4 [1, 0, 4] = true := by decide +kernel
theorem subd8_4_138 : subd8_4 [1, 0, 5] = true := by decide +kernel
theorem subd8_4_139 : subd8_4 [1, 0, 6] = true := by decide +kernel
theorem subd8_4_140 : subd8_4 [1, 0, 7] = true := by decide +kernel
theorem subd8_4_141 : subd8_4 [1, 1, -6] = true := by decide +kernel
theorem subd8_4_142 : subd8_4 [1, 1, -5] = true := by decide +kernel
theorem subd8_4_143 : subd8_4 [1, 1, -4] = true := by decide +kernel
theorem subd8_4_144 : subd8_4 [1, 1, -3] = true := by decide +kernel
theorem subd8_4_145 : subd8_4 [1, 1, -2] = true := by decide +kernel
theorem subd8_4_146 : subd8_4 [1, 1, -1] = true := by decide +kernel
theorem subd8_4_147 : subd8_4 [1, 1, 0] = true := by decide +kernel
theorem subd8_4_148 : subd8_4 [1, 1, 1] = true := by decide +kernel
theorem subd8_4_149 : subd8_4 [1, 1, 2] = true := by decide +kernel
theorem subd8_4_150 : subd8_4 [1, 1, 3] = true := by decide +kernel
theorem subd8_4_151 : subd8_4 [1, 1, 4] = true := by decide +kernel
theorem subd8_4_152 : subd8_4 [1, 1, 5] = true := by decide +kernel
theorem subd8_4_153 : subd8_4 [1, 1, 6] = true := by decide +kernel
theorem subd8_4_154 : subd8_4 [1, 1, 7] = true := by decide +kernel
theorem subd8_4_155 : subd8_4 [1, 2] = true := by decide +kernel
theorem subd8_4_156 : subd8_4 [1, 3] = true := by decide +kernel
theorem subd8_4_157 : subd8_4 [2, -4] = true := by decide +kernel
theorem subd8_4_158 : subd8_4 [2, -3] = true := by decide +kernel
theorem subd8_4_159 : subd8_4 [2, -2] = true := by decide +kernel
theorem sbd8_4_4 : ∀ q ∈ blkd8_4_4, subd8_4 q = true := by
  unfold blkd8_4_4
  exact List.forall_mem_cons.2 ⟨subd8_4_128, List.forall_mem_cons.2 ⟨subd8_4_129, List.forall_mem_cons.2 ⟨subd8_4_130, List.forall_mem_cons.2 ⟨subd8_4_131, List.forall_mem_cons.2 ⟨subd8_4_132, List.forall_mem_cons.2 ⟨subd8_4_133, List.forall_mem_cons.2 ⟨subd8_4_134, List.forall_mem_cons.2 ⟨subd8_4_135, List.forall_mem_cons.2 ⟨subd8_4_136, List.forall_mem_cons.2 ⟨subd8_4_137, List.forall_mem_cons.2 ⟨subd8_4_138, List.forall_mem_cons.2 ⟨subd8_4_139, List.forall_mem_cons.2 ⟨subd8_4_140, List.forall_mem_cons.2 ⟨subd8_4_141, List.forall_mem_cons.2 ⟨subd8_4_142, List.forall_mem_cons.2 ⟨subd8_4_143, List.forall_mem_cons.2 ⟨subd8_4_144, List.forall_mem_cons.2 ⟨subd8_4_145, List.forall_mem_cons.2 ⟨subd8_4_146, List.forall_mem_cons.2 ⟨subd8_4_147, List.forall_mem_cons.2 ⟨subd8_4_148, List.forall_mem_cons.2 ⟨subd8_4_149, List.forall_mem_cons.2 ⟨subd8_4_150, List.forall_mem_cons.2 ⟨subd8_4_151, List.forall_mem_cons.2 ⟨subd8_4_152, List.forall_mem_cons.2 ⟨subd8_4_153, List.forall_mem_cons.2 ⟨subd8_4_154, List.forall_mem_cons.2 ⟨subd8_4_155, List.forall_mem_cons.2 ⟨subd8_4_156, List.forall_mem_cons.2 ⟨subd8_4_157, List.forall_mem_cons.2 ⟨subd8_4_158, List.forall_mem_cons.2 ⟨subd8_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_160 : subd8_4 [2, -1] = true := by decide +kernel
theorem subd8_4_161 : subd8_4 [2, 0] = true := by decide +kernel
theorem subd8_4_162 : subd8_4 [2, 1] = true := by decide +kernel
theorem subd8_4_163 : subd8_4 [2, 2] = true := by decide +kernel
theorem subd8_4_164 : subd8_4 [3] = true := by decide +kernel
theorem sbd8_4_5 : ∀ q ∈ blkd8_4_5, subd8_4 q = true := by
  unfold blkd8_4_5
  exact List.forall_mem_cons.2 ⟨subd8_4_160, List.forall_mem_cons.2 ⟨subd8_4_161, List.forall_mem_cons.2 ⟨subd8_4_162, List.forall_mem_cons.2 ⟨subd8_4_163, List.forall_mem_cons.2 ⟨subd8_4_164, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-4] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-3, -5] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [-3, -4] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [-3, -3] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [-3, -2] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [-3, -1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [-3, 0] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [-3, 1] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [-3, 2] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [-2, -5] = true := by decide +kernel
theorem subd8_5_10 : subd8_5 [-2, -4] = true := by decide +kernel
theorem subd8_5_11 : subd8_5 [-2, -3] = true := by decide +kernel
theorem subd8_5_12 : subd8_5 [-2, -2] = true := by decide +kernel
theorem subd8_5_13 : subd8_5 [-2, -1] = true := by decide +kernel
theorem subd8_5_14 : subd8_5 [-2, 0] = true := by decide +kernel
theorem subd8_5_15 : subd8_5 [-2, 1] = true := by decide +kernel
theorem subd8_5_16 : subd8_5 [-2, 2] = true := by decide +kernel
theorem subd8_5_17 : subd8_5 [-2, 3] = true := by decide +kernel
theorem subd8_5_18 : subd8_5 [-1, -5] = true := by decide +kernel
theorem subd8_5_19 : subd8_5 [-1, -4] = true := by decide +kernel
theorem subd8_5_20 : subd8_5 [-1, -3] = true := by decide +kernel
theorem subd8_5_21 : subd8_5 [-1, -2] = true := by decide +kernel
theorem subd8_5_22 : subd8_5 [-1, -1] = true := by decide +kernel
theorem subd8_5_23 : subd8_5 [-1, 0] = true := by decide +kernel
theorem subd8_5_24 : subd8_5 [-1, 1] = true := by decide +kernel
theorem subd8_5_25 : subd8_5 [-1, 2] = true := by decide +kernel
theorem subd8_5_26 : subd8_5 [-1, 3] = true := by decide +kernel
theorem subd8_5_27 : subd8_5 [-1, 4] = true := by decide +kernel
theorem subd8_5_28 : subd8_5 [0, -5] = true := by decide +kernel
theorem subd8_5_29 : subd8_5 [0, -4] = true := by decide +kernel
theorem subd8_5_30 : subd8_5 [0, -3] = true := by decide +kernel
theorem subd8_5_31 : subd8_5 [0, -2] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_cons.2 ⟨subd8_5_10, List.forall_mem_cons.2 ⟨subd8_5_11, List.forall_mem_cons.2 ⟨subd8_5_12, List.forall_mem_cons.2 ⟨subd8_5_13, List.forall_mem_cons.2 ⟨subd8_5_14, List.forall_mem_cons.2 ⟨subd8_5_15, List.forall_mem_cons.2 ⟨subd8_5_16, List.forall_mem_cons.2 ⟨subd8_5_17, List.forall_mem_cons.2 ⟨subd8_5_18, List.forall_mem_cons.2 ⟨subd8_5_19, List.forall_mem_cons.2 ⟨subd8_5_20, List.forall_mem_cons.2 ⟨subd8_5_21, List.forall_mem_cons.2 ⟨subd8_5_22, List.forall_mem_cons.2 ⟨subd8_5_23, List.forall_mem_cons.2 ⟨subd8_5_24, List.forall_mem_cons.2 ⟨subd8_5_25, List.forall_mem_cons.2 ⟨subd8_5_26, List.forall_mem_cons.2 ⟨subd8_5_27, List.forall_mem_cons.2 ⟨subd8_5_28, List.forall_mem_cons.2 ⟨subd8_5_29, List.forall_mem_cons.2 ⟨subd8_5_30, List.forall_mem_cons.2 ⟨subd8_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_32 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_33 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_34 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_35 : subd8_5 [0, 2] = true := by decide +kernel
theorem subd8_5_36 : subd8_5 [0, 3] = true := by decide +kernel
theorem subd8_5_37 : subd8_5 [0, 4] = true := by decide +kernel
theorem subd8_5_38 : subd8_5 [1, -5] = true := by decide +kernel
theorem subd8_5_39 : subd8_5 [1, -4] = true := by decide +kernel
theorem subd8_5_40 : subd8_5 [1, -3] = true := by decide +kernel
theorem subd8_5_41 : subd8_5 [1, -2] = true := by decide +kernel
theorem subd8_5_42 : subd8_5 [1, -1] = true := by decide +kernel
theorem subd8_5_43 : subd8_5 [1, 0] = true := by decide +kernel
theorem subd8_5_44 : subd8_5 [1, 1] = true := by decide +kernel
theorem subd8_5_45 : subd8_5 [1, 2] = true := by decide +kernel
theorem subd8_5_46 : subd8_5 [1, 3] = true := by decide +kernel
theorem subd8_5_47 : subd8_5 [1, 4] = true := by decide +kernel
theorem subd8_5_48 : subd8_5 [2, -4] = true := by decide +kernel
theorem subd8_5_49 : subd8_5 [2, -3] = true := by decide +kernel
theorem subd8_5_50 : subd8_5 [2, -2] = true := by decide +kernel
theorem subd8_5_51 : subd8_5 [2, -1] = true := by decide +kernel
theorem subd8_5_52 : subd8_5 [2, 0] = true := by decide +kernel
theorem subd8_5_53 : subd8_5 [2, 1] = true := by decide +kernel
theorem subd8_5_54 : subd8_5 [2, 2] = true := by decide +kernel
theorem subd8_5_55 : subd8_5 [2, 3] = true := by decide +kernel
theorem subd8_5_56 : subd8_5 [2, 4] = true := by decide +kernel
theorem subd8_5_57 : subd8_5 [3, -3] = true := by decide +kernel
theorem subd8_5_58 : subd8_5 [3, -2] = true := by decide +kernel
theorem subd8_5_59 : subd8_5 [3, -1] = true := by decide +kernel
theorem subd8_5_60 : subd8_5 [3, 0] = true := by decide +kernel
theorem subd8_5_61 : subd8_5 [3, 1] = true := by decide +kernel
theorem subd8_5_62 : subd8_5 [3, 2] = true := by decide +kernel
theorem subd8_5_63 : subd8_5 [3, 3] = true := by decide +kernel
theorem sbd8_5_1 : ∀ q ∈ blkd8_5_1, subd8_5 q = true := by
  unfold blkd8_5_1
  exact List.forall_mem_cons.2 ⟨subd8_5_32, List.forall_mem_cons.2 ⟨subd8_5_33, List.forall_mem_cons.2 ⟨subd8_5_34, List.forall_mem_cons.2 ⟨subd8_5_35, List.forall_mem_cons.2 ⟨subd8_5_36, List.forall_mem_cons.2 ⟨subd8_5_37, List.forall_mem_cons.2 ⟨subd8_5_38, List.forall_mem_cons.2 ⟨subd8_5_39, List.forall_mem_cons.2 ⟨subd8_5_40, List.forall_mem_cons.2 ⟨subd8_5_41, List.forall_mem_cons.2 ⟨subd8_5_42, List.forall_mem_cons.2 ⟨subd8_5_43, List.forall_mem_cons.2 ⟨subd8_5_44, List.forall_mem_cons.2 ⟨subd8_5_45, List.forall_mem_cons.2 ⟨subd8_5_46, List.forall_mem_cons.2 ⟨subd8_5_47, List.forall_mem_cons.2 ⟨subd8_5_48, List.forall_mem_cons.2 ⟨subd8_5_49, List.forall_mem_cons.2 ⟨subd8_5_50, List.forall_mem_cons.2 ⟨subd8_5_51, List.forall_mem_cons.2 ⟨subd8_5_52, List.forall_mem_cons.2 ⟨subd8_5_53, List.forall_mem_cons.2 ⟨subd8_5_54, List.forall_mem_cons.2 ⟨subd8_5_55, List.forall_mem_cons.2 ⟨subd8_5_56, List.forall_mem_cons.2 ⟨subd8_5_57, List.forall_mem_cons.2 ⟨subd8_5_58, List.forall_mem_cons.2 ⟨subd8_5_59, List.forall_mem_cons.2 ⟨subd8_5_60, List.forall_mem_cons.2 ⟨subd8_5_61, List.forall_mem_cons.2 ⟨subd8_5_62, List.forall_mem_cons.2 ⟨subd8_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_5_64 : subd8_5 [3, 4] = true := by decide +kernel
theorem subd8_5_65 : subd8_5 [4] = true := by decide +kernel
theorem sbd8_5_2 : ∀ q ∈ blkd8_5_2, subd8_5 q = true := by
  unfold blkd8_5_2
  exact List.forall_mem_cons.2 ⟨subd8_5_64, List.forall_mem_cons.2 ⟨subd8_5_65, List.forall_mem_nil _⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C123
