import ReflectZphi.Data.Cert5.C103.Base

namespace ReflectZphi.Data.Cert5.C103

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-2] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [0, -1] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [2] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [-2] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-1] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [0] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [1] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [2] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-4] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-3, -5] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-3, -4] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-3, -3] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-3, -2] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-3, -1] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-3, 0] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [-3, 1] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [-3, 2] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [-3, 3] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [-2, -5] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [-2, -4] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [-2, -3] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [-2, -2] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [-2, -1] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [-2, 0] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [-2, 1] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [-2, 2] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [-2, 3] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [-1, -5] = true := by decide +kernel
theorem subd4_0_20 : subd4_0 [-1, -4] = true := by decide +kernel
theorem subd4_0_21 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_22 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_23 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_24 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_25 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_26 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_27 : subd4_0 [-1, 3] = true := by decide +kernel
theorem subd4_0_28 : subd4_0 [-1, 4] = true := by decide +kernel
theorem subd4_0_29 : subd4_0 [0, -5] = true := by decide +kernel
theorem subd4_0_30 : subd4_0 [0, -4] = true := by decide +kernel
theorem subd4_0_31 : subd4_0 [0, -3] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_cons.2 ⟨subd4_0_20, List.forall_mem_cons.2 ⟨subd4_0_21, List.forall_mem_cons.2 ⟨subd4_0_22, List.forall_mem_cons.2 ⟨subd4_0_23, List.forall_mem_cons.2 ⟨subd4_0_24, List.forall_mem_cons.2 ⟨subd4_0_25, List.forall_mem_cons.2 ⟨subd4_0_26, List.forall_mem_cons.2 ⟨subd4_0_27, List.forall_mem_cons.2 ⟨subd4_0_28, List.forall_mem_cons.2 ⟨subd4_0_29, List.forall_mem_cons.2 ⟨subd4_0_30, List.forall_mem_cons.2 ⟨subd4_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C103
