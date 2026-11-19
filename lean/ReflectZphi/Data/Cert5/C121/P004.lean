import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_2_128 : subd3_2 [4, -4] = true := by decide +kernel
theorem subd3_2_129 : subd3_2 [4, -3] = true := by decide +kernel
theorem subd3_2_130 : subd3_2 [4, -2] = true := by decide +kernel
theorem subd3_2_131 : subd3_2 [4, -1] = true := by decide +kernel
theorem subd3_2_132 : subd3_2 [4, 0] = true := by decide +kernel
theorem subd3_2_133 : subd3_2 [4, 1] = true := by decide +kernel
theorem subd3_2_134 : subd3_2 [4, 2] = true := by decide +kernel
theorem subd3_2_135 : subd3_2 [4, 3] = true := by decide +kernel
theorem subd3_2_136 : subd3_2 [4, 4] = true := by decide +kernel
theorem subd3_2_137 : subd3_2 [5, -6] = true := by decide +kernel
theorem subd3_2_138 : subd3_2 [5, -5] = true := by decide +kernel
theorem subd3_2_139 : subd3_2 [5, -4] = true := by decide +kernel
theorem subd3_2_140 : subd3_2 [5, -3] = true := by decide +kernel
theorem subd3_2_141 : subd3_2 [5, -2] = true := by decide +kernel
theorem subd3_2_142 : subd3_2 [5, -1] = true := by decide +kernel
theorem subd3_2_143 : subd3_2 [5, 0] = true := by decide +kernel
theorem subd3_2_144 : subd3_2 [5, 1] = true := by decide +kernel
theorem subd3_2_145 : subd3_2 [5, 2] = true := by decide +kernel
theorem subd3_2_146 : subd3_2 [5, 3] = true := by decide +kernel
theorem subd3_2_147 : subd3_2 [6] = true := by decide +kernel
theorem sbd3_2_4 : ∀ q ∈ blkd3_2_4, subd3_2 q = true := by
  unfold blkd3_2_4
  exact List.forall_mem_cons.2 ⟨subd3_2_128, List.forall_mem_cons.2 ⟨subd3_2_129, List.forall_mem_cons.2 ⟨subd3_2_130, List.forall_mem_cons.2 ⟨subd3_2_131, List.forall_mem_cons.2 ⟨subd3_2_132, List.forall_mem_cons.2 ⟨subd3_2_133, List.forall_mem_cons.2 ⟨subd3_2_134, List.forall_mem_cons.2 ⟨subd3_2_135, List.forall_mem_cons.2 ⟨subd3_2_136, List.forall_mem_cons.2 ⟨subd3_2_137, List.forall_mem_cons.2 ⟨subd3_2_138, List.forall_mem_cons.2 ⟨subd3_2_139, List.forall_mem_cons.2 ⟨subd3_2_140, List.forall_mem_cons.2 ⟨subd3_2_141, List.forall_mem_cons.2 ⟨subd3_2_142, List.forall_mem_cons.2 ⟨subd3_2_143, List.forall_mem_cons.2 ⟨subd3_2_144, List.forall_mem_cons.2 ⟨subd3_2_145, List.forall_mem_cons.2 ⟨subd3_2_146, List.forall_mem_cons.2 ⟨subd3_2_147, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [-3] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-2] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [-1, -4] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [-1, -3] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [-1, -2] = true := by decide +kernel
theorem subd3_3_5 : subd3_3 [-1, -1] = true := by decide +kernel
theorem subd3_3_6 : subd3_3 [-1, 0] = true := by decide +kernel
theorem subd3_3_7 : subd3_3 [-1, 1] = true := by decide +kernel
theorem subd3_3_8 : subd3_3 [-1, 2] = true := by decide +kernel
theorem subd3_3_9 : subd3_3 [-1, 3] = true := by decide +kernel
theorem subd3_3_10 : subd3_3 [0, -4] = true := by decide +kernel
theorem subd3_3_11 : subd3_3 [0, -3] = true := by decide +kernel
theorem subd3_3_12 : subd3_3 [0, -2] = true := by decide +kernel
theorem subd3_3_13 : subd3_3 [0, -1] = true := by decide +kernel
theorem subd3_3_14 : subd3_3 [0, 0] = true := by decide +kernel
theorem subd3_3_15 : subd3_3 [0, 1] = true := by decide +kernel
theorem subd3_3_16 : subd3_3 [0, 2] = true := by decide +kernel
theorem subd3_3_17 : subd3_3 [0, 3] = true := by decide +kernel
theorem subd3_3_18 : subd3_3 [1, -4] = true := by decide +kernel
theorem subd3_3_19 : subd3_3 [1, -3] = true := by decide +kernel
theorem subd3_3_20 : subd3_3 [1, -2] = true := by decide +kernel
theorem subd3_3_21 : subd3_3 [1, -1] = true := by decide +kernel
theorem subd3_3_22 : subd3_3 [1, 0] = true := by decide +kernel
theorem subd3_3_23 : subd3_3 [1, 1] = true := by decide +kernel
theorem subd3_3_24 : subd3_3 [1, 2] = true := by decide +kernel
theorem subd3_3_25 : subd3_3 [1, 3] = true := by decide +kernel
theorem subd3_3_26 : subd3_3 [2] = true := by decide +kernel
theorem subd3_3_27 : subd3_3 [3] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_cons.2 ⟨subd3_3_5, List.forall_mem_cons.2 ⟨subd3_3_6, List.forall_mem_cons.2 ⟨subd3_3_7, List.forall_mem_cons.2 ⟨subd3_3_8, List.forall_mem_cons.2 ⟨subd3_3_9, List.forall_mem_cons.2 ⟨subd3_3_10, List.forall_mem_cons.2 ⟨subd3_3_11, List.forall_mem_cons.2 ⟨subd3_3_12, List.forall_mem_cons.2 ⟨subd3_3_13, List.forall_mem_cons.2 ⟨subd3_3_14, List.forall_mem_cons.2 ⟨subd3_3_15, List.forall_mem_cons.2 ⟨subd3_3_16, List.forall_mem_cons.2 ⟨subd3_3_17, List.forall_mem_cons.2 ⟨subd3_3_18, List.forall_mem_cons.2 ⟨subd3_3_19, List.forall_mem_cons.2 ⟨subd3_3_20, List.forall_mem_cons.2 ⟨subd3_3_21, List.forall_mem_cons.2 ⟨subd3_3_22, List.forall_mem_cons.2 ⟨subd3_3_23, List.forall_mem_cons.2 ⟨subd3_3_24, List.forall_mem_cons.2 ⟨subd3_3_25, List.forall_mem_cons.2 ⟨subd3_3_26, List.forall_mem_cons.2 ⟨subd3_3_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [0] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-4] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-3, -3] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-3, -2] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-3, -1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-3, 0] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-3, 1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-3, 2] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-3, 3] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-3, 4] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-3, 5] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-2, -4] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [-2, 2] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [-2, 3] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [-2, 4] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [-2, 5] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [-1, -5] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [-1, 4] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [-1, 5] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [0, -6] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
