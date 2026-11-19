import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-3] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-2, -4] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-2, -3] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-2, -2] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-2, -1] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-2, 0] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-2, 1] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [-2, 2] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [-1, -4] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [-1, 3] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [0, -4] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [0, -1] = true := by decide +kernel
theorem subd3_2_20 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_21 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_22 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_23 : subd3_2 [0, 3] = true := by decide +kernel
theorem subd3_2_24 : subd3_2 [1, -4] = true := by decide +kernel
theorem subd3_2_25 : subd3_2 [1, -3] = true := by decide +kernel
theorem subd3_2_26 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_27 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_28 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_29 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_30 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_31 : subd3_2 [1, 3] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_cons.2 ⟨subd3_2_20, List.forall_mem_cons.2 ⟨subd3_2_21, List.forall_mem_cons.2 ⟨subd3_2_22, List.forall_mem_cons.2 ⟨subd3_2_23, List.forall_mem_cons.2 ⟨subd3_2_24, List.forall_mem_cons.2 ⟨subd3_2_25, List.forall_mem_cons.2 ⟨subd3_2_26, List.forall_mem_cons.2 ⟨subd3_2_27, List.forall_mem_cons.2 ⟨subd3_2_28, List.forall_mem_cons.2 ⟨subd3_2_29, List.forall_mem_cons.2 ⟨subd3_2_30, List.forall_mem_cons.2 ⟨subd3_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_2_32 : subd3_2 [2, -3] = true := by decide +kernel
theorem subd3_2_33 : subd3_2 [2, -2] = true := by decide +kernel
theorem subd3_2_34 : subd3_2 [2, -1] = true := by decide +kernel
theorem subd3_2_35 : subd3_2 [2, 0] = true := by decide +kernel
theorem subd3_2_36 : subd3_2 [2, 1] = true := by decide +kernel
theorem subd3_2_37 : subd3_2 [2, 2] = true := by decide +kernel
theorem subd3_2_38 : subd3_2 [2, 3] = true := by decide +kernel
theorem subd3_2_39 : subd3_2 [3] = true := by decide +kernel
theorem sbd3_2_1 : ∀ q ∈ blkd3_2_1, subd3_2 q = true := by
  unfold blkd3_2_1
  exact List.forall_mem_cons.2 ⟨subd3_2_32, List.forall_mem_cons.2 ⟨subd3_2_33, List.forall_mem_cons.2 ⟨subd3_2_34, List.forall_mem_cons.2 ⟨subd3_2_35, List.forall_mem_cons.2 ⟨subd3_2_36, List.forall_mem_cons.2 ⟨subd3_2_37, List.forall_mem_cons.2 ⟨subd3_2_38, List.forall_mem_cons.2 ⟨subd3_2_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [-4] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-3] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [-2, -3] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [-2, -2] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [-2, -1] = true := by decide +kernel
theorem subd3_3_5 : subd3_3 [-2, 0] = true := by decide +kernel
theorem subd3_3_6 : subd3_3 [-2, 1] = true := by decide +kernel
theorem subd3_3_7 : subd3_3 [-2, 2] = true := by decide +kernel
theorem subd3_3_8 : subd3_3 [-2, 3] = true := by decide +kernel
theorem subd3_3_9 : subd3_3 [-1, -3] = true := by decide +kernel
theorem subd3_3_10 : subd3_3 [-1, -2] = true := by decide +kernel
theorem subd3_3_11 : subd3_3 [-1, -1] = true := by decide +kernel
theorem subd3_3_12 : subd3_3 [-1, 0] = true := by decide +kernel
theorem subd3_3_13 : subd3_3 [-1, 1] = true := by decide +kernel
theorem subd3_3_14 : subd3_3 [-1, 2] = true := by decide +kernel
theorem subd3_3_15 : subd3_3 [-1, 3] = true := by decide +kernel
theorem subd3_3_16 : subd3_3 [0, -4] = true := by decide +kernel
theorem subd3_3_17 : subd3_3 [0, -3] = true := by decide +kernel
theorem subd3_3_18 : subd3_3 [0, -2] = true := by decide +kernel
theorem subd3_3_19 : subd3_3 [0, -1] = true := by decide +kernel
theorem subd3_3_20 : subd3_3 [0, 0] = true := by decide +kernel
theorem subd3_3_21 : subd3_3 [0, 1] = true := by decide +kernel
theorem subd3_3_22 : subd3_3 [0, 2] = true := by decide +kernel
theorem subd3_3_23 : subd3_3 [0, 3] = true := by decide +kernel
theorem subd3_3_24 : subd3_3 [1, -4] = true := by decide +kernel
theorem subd3_3_25 : subd3_3 [1, -3] = true := by decide +kernel
theorem subd3_3_26 : subd3_3 [1, -2] = true := by decide +kernel
theorem subd3_3_27 : subd3_3 [1, -1] = true := by decide +kernel
theorem subd3_3_28 : subd3_3 [1, 0] = true := by decide +kernel
theorem subd3_3_29 : subd3_3 [1, 1] = true := by decide +kernel
theorem subd3_3_30 : subd3_3 [1, 2] = true := by decide +kernel
theorem subd3_3_31 : subd3_3 [2, -4] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_cons.2 ⟨subd3_3_5, List.forall_mem_cons.2 ⟨subd3_3_6, List.forall_mem_cons.2 ⟨subd3_3_7, List.forall_mem_cons.2 ⟨subd3_3_8, List.forall_mem_cons.2 ⟨subd3_3_9, List.forall_mem_cons.2 ⟨subd3_3_10, List.forall_mem_cons.2 ⟨subd3_3_11, List.forall_mem_cons.2 ⟨subd3_3_12, List.forall_mem_cons.2 ⟨subd3_3_13, List.forall_mem_cons.2 ⟨subd3_3_14, List.forall_mem_cons.2 ⟨subd3_3_15, List.forall_mem_cons.2 ⟨subd3_3_16, List.forall_mem_cons.2 ⟨subd3_3_17, List.forall_mem_cons.2 ⟨subd3_3_18, List.forall_mem_cons.2 ⟨subd3_3_19, List.forall_mem_cons.2 ⟨subd3_3_20, List.forall_mem_cons.2 ⟨subd3_3_21, List.forall_mem_cons.2 ⟨subd3_3_22, List.forall_mem_cons.2 ⟨subd3_3_23, List.forall_mem_cons.2 ⟨subd3_3_24, List.forall_mem_cons.2 ⟨subd3_3_25, List.forall_mem_cons.2 ⟨subd3_3_26, List.forall_mem_cons.2 ⟨subd3_3_27, List.forall_mem_cons.2 ⟨subd3_3_28, List.forall_mem_cons.2 ⟨subd3_3_29, List.forall_mem_cons.2 ⟨subd3_3_30, List.forall_mem_cons.2 ⟨subd3_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_3_32 : subd3_3 [2, -3] = true := by decide +kernel
theorem subd3_3_33 : subd3_3 [2, -2] = true := by decide +kernel
theorem subd3_3_34 : subd3_3 [2, -1] = true := by decide +kernel
theorem subd3_3_35 : subd3_3 [2, 0] = true := by decide +kernel
theorem subd3_3_36 : subd3_3 [2, 1] = true := by decide +kernel
theorem subd3_3_37 : subd3_3 [2, 2] = true := by decide +kernel
theorem subd3_3_38 : subd3_3 [3] = true := by decide +kernel
theorem subd3_3_39 : subd3_3 [4] = true := by decide +kernel
theorem sbd3_3_1 : ∀ q ∈ blkd3_3_1, subd3_3 q = true := by
  unfold blkd3_3_1
  exact List.forall_mem_cons.2 ⟨subd3_3_32, List.forall_mem_cons.2 ⟨subd3_3_33, List.forall_mem_cons.2 ⟨subd3_3_34, List.forall_mem_cons.2 ⟨subd3_3_35, List.forall_mem_cons.2 ⟨subd3_3_36, List.forall_mem_cons.2 ⟨subd3_3_37, List.forall_mem_cons.2 ⟨subd3_3_38, List.forall_mem_cons.2 ⟨subd3_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [1, 1] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C129
