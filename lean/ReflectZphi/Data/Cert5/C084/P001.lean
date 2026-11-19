import ReflectZphi.Data.Cert5.C084.Base

namespace ReflectZphi.Data.Cert5.C084

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_0_0 : subd3_0 [-3] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-2, -4] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-2, -3] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-2, -2] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [-2, -1] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [-2, 0] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [-2, 1] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [-2, 2] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [-1, -4] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [-1, -3] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [-1, -1] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [-1, 0] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [-1, 1] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [-1, 2] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [-1, 3] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [0, -4] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [0, -3] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [0, -2] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [0, -1] = true := by decide +kernel
theorem subd3_0_20 : subd3_0 [0, 0] = true := by decide +kernel
theorem subd3_0_21 : subd3_0 [0, 1] = true := by decide +kernel
theorem subd3_0_22 : subd3_0 [0, 2] = true := by decide +kernel
theorem subd3_0_23 : subd3_0 [0, 3] = true := by decide +kernel
theorem subd3_0_24 : subd3_0 [1, -4] = true := by decide +kernel
theorem subd3_0_25 : subd3_0 [1, -3] = true := by decide +kernel
theorem subd3_0_26 : subd3_0 [1, -2] = true := by decide +kernel
theorem subd3_0_27 : subd3_0 [1, -1] = true := by decide +kernel
theorem subd3_0_28 : subd3_0 [1, 0] = true := by decide +kernel
theorem subd3_0_29 : subd3_0 [1, 1] = true := by decide +kernel
theorem subd3_0_30 : subd3_0 [1, 2] = true := by decide +kernel
theorem subd3_0_31 : subd3_0 [1, 3] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_cons.2 ⟨subd3_0_20, List.forall_mem_cons.2 ⟨subd3_0_21, List.forall_mem_cons.2 ⟨subd3_0_22, List.forall_mem_cons.2 ⟨subd3_0_23, List.forall_mem_cons.2 ⟨subd3_0_24, List.forall_mem_cons.2 ⟨subd3_0_25, List.forall_mem_cons.2 ⟨subd3_0_26, List.forall_mem_cons.2 ⟨subd3_0_27, List.forall_mem_cons.2 ⟨subd3_0_28, List.forall_mem_cons.2 ⟨subd3_0_29, List.forall_mem_cons.2 ⟨subd3_0_30, List.forall_mem_cons.2 ⟨subd3_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_32 : subd3_0 [2, -3] = true := by decide +kernel
theorem subd3_0_33 : subd3_0 [2, -2] = true := by decide +kernel
theorem subd3_0_34 : subd3_0 [2, -1] = true := by decide +kernel
theorem subd3_0_35 : subd3_0 [2, 0] = true := by decide +kernel
theorem subd3_0_36 : subd3_0 [2, 1] = true := by decide +kernel
theorem subd3_0_37 : subd3_0 [2, 2] = true := by decide +kernel
theorem subd3_0_38 : subd3_0 [2, 3] = true := by decide +kernel
theorem subd3_0_39 : subd3_0 [3] = true := by decide +kernel
theorem sbd3_0_1 : ∀ q ∈ blkd3_0_1, subd3_0 q = true := by
  unfold blkd3_0_1
  exact List.forall_mem_cons.2 ⟨subd3_0_32, List.forall_mem_cons.2 ⟨subd3_0_33, List.forall_mem_cons.2 ⟨subd3_0_34, List.forall_mem_cons.2 ⟨subd3_0_35, List.forall_mem_cons.2 ⟨subd3_0_36, List.forall_mem_cons.2 ⟨subd3_0_37, List.forall_mem_cons.2 ⟨subd3_0_38, List.forall_mem_cons.2 ⟨subd3_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_nil _⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-4] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-3, -2] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-3, -1] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-3, 0] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-3, 1] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-3, 2] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-3, 3] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [-3, 4] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [-2, -4] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [-2, -3] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [-2, -2] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [-2, -1] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [-2, 0] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [-2, 1] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [-2, 2] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [-2, 3] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [-2, 4] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [-2, 5] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [-1, -5] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [-1, -4] = true := by decide +kernel
theorem subd4_0_20 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_21 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_22 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_23 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_24 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_25 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_26 : subd4_0 [-1, 3] = true := by decide +kernel
theorem subd4_0_27 : subd4_0 [-1, 4] = true := by decide +kernel
theorem subd4_0_28 : subd4_0 [-1, 5] = true := by decide +kernel
theorem subd4_0_29 : subd4_0 [0, -5] = true := by decide +kernel
theorem subd4_0_30 : subd4_0 [0, -4] = true := by decide +kernel
theorem subd4_0_31 : subd4_0 [0, -3] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_cons.2 ⟨subd4_0_20, List.forall_mem_cons.2 ⟨subd4_0_21, List.forall_mem_cons.2 ⟨subd4_0_22, List.forall_mem_cons.2 ⟨subd4_0_23, List.forall_mem_cons.2 ⟨subd4_0_24, List.forall_mem_cons.2 ⟨subd4_0_25, List.forall_mem_cons.2 ⟨subd4_0_26, List.forall_mem_cons.2 ⟨subd4_0_27, List.forall_mem_cons.2 ⟨subd4_0_28, List.forall_mem_cons.2 ⟨subd4_0_29, List.forall_mem_cons.2 ⟨subd4_0_30, List.forall_mem_cons.2 ⟨subd4_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C084
