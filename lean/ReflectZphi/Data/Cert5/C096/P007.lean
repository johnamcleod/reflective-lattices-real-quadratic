import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_128 : subd6_2 [1, 0, 0] = true := by decide +kernel
theorem subd6_2_129 : subd6_2 [1, 0, 1] = true := by decide +kernel
theorem subd6_2_130 : subd6_2 [1, 0, 2] = true := by decide +kernel
theorem subd6_2_131 : subd6_2 [1, 0, 3] = true := by decide +kernel
theorem subd6_2_132 : subd6_2 [1, 0, 4] = true := by decide +kernel
theorem subd6_2_133 : subd6_2 [1, 0, 5] = true := by decide +kernel
theorem subd6_2_134 : subd6_2 [1, 0, 6] = true := by decide +kernel
theorem subd6_2_135 : subd6_2 [1, 1, -7] = true := by decide +kernel
theorem subd6_2_136 : subd6_2 [1, 1, -6] = true := by decide +kernel
theorem subd6_2_137 : subd6_2 [1, 1, -5] = true := by decide +kernel
theorem subd6_2_138 : subd6_2 [1, 1, -4] = true := by decide +kernel
theorem subd6_2_139 : subd6_2 [1, 1, -3] = true := by decide +kernel
theorem subd6_2_140 : subd6_2 [1, 1, -2] = true := by decide +kernel
theorem subd6_2_141 : subd6_2 [1, 1, -1] = true := by decide +kernel
theorem subd6_2_142 : subd6_2 [1, 1, 0] = true := by decide +kernel
theorem subd6_2_143 : subd6_2 [1, 1, 1] = true := by decide +kernel
theorem subd6_2_144 : subd6_2 [1, 1, 2] = true := by decide +kernel
theorem subd6_2_145 : subd6_2 [1, 1, 3] = true := by decide +kernel
theorem subd6_2_146 : subd6_2 [1, 1, 4] = true := by decide +kernel
theorem subd6_2_147 : subd6_2 [1, 1, 5] = true := by decide +kernel
theorem subd6_2_148 : subd6_2 [1, 1, 6] = true := by decide +kernel
theorem subd6_2_149 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_150 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_151 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_152 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_153 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_154 : subd6_2 [2, 0] = true := by decide +kernel
theorem subd6_2_155 : subd6_2 [2, 1] = true := by decide +kernel
theorem subd6_2_156 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_157 : subd6_2 [3, -2] = true := by decide +kernel
theorem subd6_2_158 : subd6_2 [3, -1] = true := by decide +kernel
theorem subd6_2_159 : subd6_2 [3, 0] = true := by decide +kernel
theorem sbd6_2_4 : ∀ q ∈ blkd6_2_4, subd6_2 q = true := by
  unfold blkd6_2_4
  exact List.forall_mem_cons.2 ⟨subd6_2_128, List.forall_mem_cons.2 ⟨subd6_2_129, List.forall_mem_cons.2 ⟨subd6_2_130, List.forall_mem_cons.2 ⟨subd6_2_131, List.forall_mem_cons.2 ⟨subd6_2_132, List.forall_mem_cons.2 ⟨subd6_2_133, List.forall_mem_cons.2 ⟨subd6_2_134, List.forall_mem_cons.2 ⟨subd6_2_135, List.forall_mem_cons.2 ⟨subd6_2_136, List.forall_mem_cons.2 ⟨subd6_2_137, List.forall_mem_cons.2 ⟨subd6_2_138, List.forall_mem_cons.2 ⟨subd6_2_139, List.forall_mem_cons.2 ⟨subd6_2_140, List.forall_mem_cons.2 ⟨subd6_2_141, List.forall_mem_cons.2 ⟨subd6_2_142, List.forall_mem_cons.2 ⟨subd6_2_143, List.forall_mem_cons.2 ⟨subd6_2_144, List.forall_mem_cons.2 ⟨subd6_2_145, List.forall_mem_cons.2 ⟨subd6_2_146, List.forall_mem_cons.2 ⟨subd6_2_147, List.forall_mem_cons.2 ⟨subd6_2_148, List.forall_mem_cons.2 ⟨subd6_2_149, List.forall_mem_cons.2 ⟨subd6_2_150, List.forall_mem_cons.2 ⟨subd6_2_151, List.forall_mem_cons.2 ⟨subd6_2_152, List.forall_mem_cons.2 ⟨subd6_2_153, List.forall_mem_cons.2 ⟨subd6_2_154, List.forall_mem_cons.2 ⟨subd6_2_155, List.forall_mem_cons.2 ⟨subd6_2_156, List.forall_mem_cons.2 ⟨subd6_2_157, List.forall_mem_cons.2 ⟨subd6_2_158, List.forall_mem_cons.2 ⟨subd6_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_160 : subd6_2 [3, 1] = true := by decide +kernel
theorem sbd6_2_5 : ∀ q ∈ blkd6_2_5, subd6_2 q = true := by
  unfold blkd6_2_5
  exact List.forall_mem_cons.2 ⟨subd6_2_160, List.forall_mem_nil _⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-4] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-3, -3] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-3, -2] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-3, -1] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-3, 0] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-3, 1] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-3, 2] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-3, 3] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-3, 4] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-3, 5] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-2, -5] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-2, -4] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-2, 1] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-2, 2] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [-2, 3] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [-2, 4] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [-2, 5] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [-1, -5] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [-1, -4] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [-1, 4] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [-1, 5] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [0, -6] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [0, -5] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [0, 4] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [0, 5] = true := by decide +kernel
theorem subd6_3_44 : subd6_3 [1, -6] = true := by decide +kernel
theorem subd6_3_45 : subd6_3 [1, -5] = true := by decide +kernel
theorem subd6_3_46 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_47 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_48 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_49 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_50 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_51 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_52 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_53 : subd6_3 [1, 3] = true := by decide +kernel
theorem subd6_3_54 : subd6_3 [1, 4] = true := by decide +kernel
theorem subd6_3_55 : subd6_3 [2, -6] = true := by decide +kernel
theorem subd6_3_56 : subd6_3 [2, -5] = true := by decide +kernel
theorem subd6_3_57 : subd6_3 [2, -4] = true := by decide +kernel
theorem subd6_3_58 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_59 : subd6_3 [2, -2] = true := by decide +kernel
theorem subd6_3_60 : subd6_3 [2, -1] = true := by decide +kernel
theorem subd6_3_61 : subd6_3 [2, 0] = true := by decide +kernel
theorem subd6_3_62 : subd6_3 [2, 1] = true := by decide +kernel
theorem subd6_3_63 : subd6_3 [2, 2] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_cons.2 ⟨subd6_3_44, List.forall_mem_cons.2 ⟨subd6_3_45, List.forall_mem_cons.2 ⟨subd6_3_46, List.forall_mem_cons.2 ⟨subd6_3_47, List.forall_mem_cons.2 ⟨subd6_3_48, List.forall_mem_cons.2 ⟨subd6_3_49, List.forall_mem_cons.2 ⟨subd6_3_50, List.forall_mem_cons.2 ⟨subd6_3_51, List.forall_mem_cons.2 ⟨subd6_3_52, List.forall_mem_cons.2 ⟨subd6_3_53, List.forall_mem_cons.2 ⟨subd6_3_54, List.forall_mem_cons.2 ⟨subd6_3_55, List.forall_mem_cons.2 ⟨subd6_3_56, List.forall_mem_cons.2 ⟨subd6_3_57, List.forall_mem_cons.2 ⟨subd6_3_58, List.forall_mem_cons.2 ⟨subd6_3_59, List.forall_mem_cons.2 ⟨subd6_3_60, List.forall_mem_cons.2 ⟨subd6_3_61, List.forall_mem_cons.2 ⟨subd6_3_62, List.forall_mem_cons.2 ⟨subd6_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_64 : subd6_3 [2, 3] = true := by decide +kernel
theorem subd6_3_65 : subd6_3 [2, 4] = true := by decide +kernel
theorem subd6_3_66 : subd6_3 [3, -6] = true := by decide +kernel
theorem subd6_3_67 : subd6_3 [3, -5] = true := by decide +kernel
theorem subd6_3_68 : subd6_3 [3, -4] = true := by decide +kernel
theorem subd6_3_69 : subd6_3 [3, -3] = true := by decide +kernel
theorem subd6_3_70 : subd6_3 [3, -2] = true := by decide +kernel
theorem subd6_3_71 : subd6_3 [3, -1] = true := by decide +kernel
theorem subd6_3_72 : subd6_3 [3, 0] = true := by decide +kernel
theorem subd6_3_73 : subd6_3 [3, 1] = true := by decide +kernel
theorem subd6_3_74 : subd6_3 [3, 2] = true := by decide +kernel
theorem subd6_3_75 : subd6_3 [4] = true := by decide +kernel
theorem sbd6_3_2 : ∀ q ∈ blkd6_3_2, subd6_3 q = true := by
  unfold blkd6_3_2
  exact List.forall_mem_cons.2 ⟨subd6_3_64, List.forall_mem_cons.2 ⟨subd6_3_65, List.forall_mem_cons.2 ⟨subd6_3_66, List.forall_mem_cons.2 ⟨subd6_3_67, List.forall_mem_cons.2 ⟨subd6_3_68, List.forall_mem_cons.2 ⟨subd6_3_69, List.forall_mem_cons.2 ⟨subd6_3_70, List.forall_mem_cons.2 ⟨subd6_3_71, List.forall_mem_cons.2 ⟨subd6_3_72, List.forall_mem_cons.2 ⟨subd6_3_73, List.forall_mem_cons.2 ⟨subd6_3_74, List.forall_mem_cons.2 ⟨subd6_3_75, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
