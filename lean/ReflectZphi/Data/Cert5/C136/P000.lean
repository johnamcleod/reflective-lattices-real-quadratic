import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_0 : ldCheck G d0_0.U d0_0.ms ldd0_0 = true := by decide +kernel
theorem pre_okd0_0 : subPre G cell0 d0_0 = true := by decide +kernel
theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem ld_okd0_1 : ldCheck G d0_1.U d0_1.ms ldd0_1 = true := by decide +kernel
theorem pre_okd0_1 : subPre G cell0 d0_1 = true := by decide +kernel
theorem subd0_1_0 : subd0_1 [-2, -2] = true := by decide +kernel
theorem subd0_1_1 : subd0_1 [-2, -1] = true := by decide +kernel
theorem subd0_1_2 : subd0_1 [-2, 0] = true := by decide +kernel
theorem subd0_1_3 : subd0_1 [-2, 1] = true := by decide +kernel
theorem subd0_1_4 : subd0_1 [-2, 2] = true := by decide +kernel
theorem subd0_1_5 : subd0_1 [-2, 3] = true := by decide +kernel
theorem subd0_1_6 : subd0_1 [-1, -3] = true := by decide +kernel
theorem subd0_1_7 : subd0_1 [-1, -2] = true := by decide +kernel
theorem subd0_1_8 : subd0_1 [-1, -1] = true := by decide +kernel
theorem subd0_1_9 : subd0_1 [-1, 0] = true := by decide +kernel
theorem subd0_1_10 : subd0_1 [-1, 1] = true := by decide +kernel
theorem subd0_1_11 : subd0_1 [-1, 2] = true := by decide +kernel
theorem subd0_1_12 : subd0_1 [-1, 3] = true := by decide +kernel
theorem subd0_1_13 : subd0_1 [0, -4] = true := by decide +kernel
theorem subd0_1_14 : subd0_1 [0, -3] = true := by decide +kernel
theorem subd0_1_15 : subd0_1 [0, -2] = true := by decide +kernel
theorem subd0_1_16 : subd0_1 [0, -1] = true := by decide +kernel
theorem subd0_1_17 : subd0_1 [0, 0] = true := by decide +kernel
theorem subd0_1_18 : subd0_1 [0, 1] = true := by decide +kernel
theorem subd0_1_19 : subd0_1 [0, 2] = true := by decide +kernel
theorem subd0_1_20 : subd0_1 [0, 3] = true := by decide +kernel
theorem subd0_1_21 : subd0_1 [1, -4] = true := by decide +kernel
theorem subd0_1_22 : subd0_1 [1, -3] = true := by decide +kernel
theorem subd0_1_23 : subd0_1 [1, -2] = true := by decide +kernel
theorem subd0_1_24 : subd0_1 [1, -1] = true := by decide +kernel
theorem subd0_1_25 : subd0_1 [1, 0] = true := by decide +kernel
theorem subd0_1_26 : subd0_1 [1, 1] = true := by decide +kernel
theorem subd0_1_27 : subd0_1 [1, 2] = true := by decide +kernel
theorem subd0_1_28 : subd0_1 [2, -4] = true := by decide +kernel
theorem subd0_1_29 : subd0_1 [2, -3] = true := by decide +kernel
theorem subd0_1_30 : subd0_1 [2, -2] = true := by decide +kernel
theorem subd0_1_31 : subd0_1 [2, -1] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_cons.2 ⟨subd0_1_1, List.forall_mem_cons.2 ⟨subd0_1_2, List.forall_mem_cons.2 ⟨subd0_1_3, List.forall_mem_cons.2 ⟨subd0_1_4, List.forall_mem_cons.2 ⟨subd0_1_5, List.forall_mem_cons.2 ⟨subd0_1_6, List.forall_mem_cons.2 ⟨subd0_1_7, List.forall_mem_cons.2 ⟨subd0_1_8, List.forall_mem_cons.2 ⟨subd0_1_9, List.forall_mem_cons.2 ⟨subd0_1_10, List.forall_mem_cons.2 ⟨subd0_1_11, List.forall_mem_cons.2 ⟨subd0_1_12, List.forall_mem_cons.2 ⟨subd0_1_13, List.forall_mem_cons.2 ⟨subd0_1_14, List.forall_mem_cons.2 ⟨subd0_1_15, List.forall_mem_cons.2 ⟨subd0_1_16, List.forall_mem_cons.2 ⟨subd0_1_17, List.forall_mem_cons.2 ⟨subd0_1_18, List.forall_mem_cons.2 ⟨subd0_1_19, List.forall_mem_cons.2 ⟨subd0_1_20, List.forall_mem_cons.2 ⟨subd0_1_21, List.forall_mem_cons.2 ⟨subd0_1_22, List.forall_mem_cons.2 ⟨subd0_1_23, List.forall_mem_cons.2 ⟨subd0_1_24, List.forall_mem_cons.2 ⟨subd0_1_25, List.forall_mem_cons.2 ⟨subd0_1_26, List.forall_mem_cons.2 ⟨subd0_1_27, List.forall_mem_cons.2 ⟨subd0_1_28, List.forall_mem_cons.2 ⟨subd0_1_29, List.forall_mem_cons.2 ⟨subd0_1_30, List.forall_mem_cons.2 ⟨subd0_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_1_32 : subd0_1 [2, 0] = true := by decide +kernel
theorem subd0_1_33 : subd0_1 [2, 1] = true := by decide +kernel
theorem sbd0_1_1 : ∀ q ∈ blkd0_1_1, subd0_1 q = true := by
  unfold blkd0_1_1
  exact List.forall_mem_cons.2 ⟨subd0_1_32, List.forall_mem_cons.2 ⟨subd0_1_33, List.forall_mem_nil _⟩⟩
theorem ld_okd0_2 : ldCheck G d0_2.U d0_2.ms ldd0_2 = true := by decide +kernel
theorem pre_okd0_2 : subPre G cell0 d0_2 = true := by decide +kernel
theorem subd0_2_0 : subd0_2 [-4] = true := by decide +kernel
theorem subd0_2_1 : subd0_2 [-3] = true := by decide +kernel
theorem subd0_2_2 : subd0_2 [-2, -4] = true := by decide +kernel
theorem subd0_2_3 : subd0_2 [-2, -3] = true := by decide +kernel
theorem subd0_2_4 : subd0_2 [-2, -2] = true := by decide +kernel
theorem subd0_2_5 : subd0_2 [-2, -1] = true := by decide +kernel
theorem subd0_2_6 : subd0_2 [-2, 0] = true := by decide +kernel
theorem subd0_2_7 : subd0_2 [-2, 1] = true := by decide +kernel
theorem subd0_2_8 : subd0_2 [-2, 2] = true := by decide +kernel
theorem subd0_2_9 : subd0_2 [-1, -4] = true := by decide +kernel
theorem subd0_2_10 : subd0_2 [-1, -3] = true := by decide +kernel
theorem subd0_2_11 : subd0_2 [-1, -2] = true := by decide +kernel
theorem subd0_2_12 : subd0_2 [-1, -1] = true := by decide +kernel
theorem subd0_2_13 : subd0_2 [-1, 0] = true := by decide +kernel
theorem subd0_2_14 : subd0_2 [-1, 1] = true := by decide +kernel
theorem subd0_2_15 : subd0_2 [-1, 2] = true := by decide +kernel
theorem subd0_2_16 : subd0_2 [-1, 3] = true := by decide +kernel
theorem subd0_2_17 : subd0_2 [0, -4] = true := by decide +kernel
theorem subd0_2_18 : subd0_2 [0, -3] = true := by decide +kernel
theorem subd0_2_19 : subd0_2 [0, -2] = true := by decide +kernel
theorem subd0_2_20 : subd0_2 [0, -1] = true := by decide +kernel
theorem subd0_2_21 : subd0_2 [0, 0] = true := by decide +kernel
theorem subd0_2_22 : subd0_2 [0, 1] = true := by decide +kernel
theorem subd0_2_23 : subd0_2 [0, 2] = true := by decide +kernel
theorem subd0_2_24 : subd0_2 [0, 3] = true := by decide +kernel
theorem subd0_2_25 : subd0_2 [1, -4] = true := by decide +kernel
theorem subd0_2_26 : subd0_2 [1, -3] = true := by decide +kernel
theorem subd0_2_27 : subd0_2 [1, -2] = true := by decide +kernel
theorem subd0_2_28 : subd0_2 [1, -1] = true := by decide +kernel
theorem subd0_2_29 : subd0_2 [1, 0] = true := by decide +kernel
theorem subd0_2_30 : subd0_2 [1, 1] = true := by decide +kernel
theorem subd0_2_31 : subd0_2 [1, 2] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_cons.2 ⟨subd0_2_1, List.forall_mem_cons.2 ⟨subd0_2_2, List.forall_mem_cons.2 ⟨subd0_2_3, List.forall_mem_cons.2 ⟨subd0_2_4, List.forall_mem_cons.2 ⟨subd0_2_5, List.forall_mem_cons.2 ⟨subd0_2_6, List.forall_mem_cons.2 ⟨subd0_2_7, List.forall_mem_cons.2 ⟨subd0_2_8, List.forall_mem_cons.2 ⟨subd0_2_9, List.forall_mem_cons.2 ⟨subd0_2_10, List.forall_mem_cons.2 ⟨subd0_2_11, List.forall_mem_cons.2 ⟨subd0_2_12, List.forall_mem_cons.2 ⟨subd0_2_13, List.forall_mem_cons.2 ⟨subd0_2_14, List.forall_mem_cons.2 ⟨subd0_2_15, List.forall_mem_cons.2 ⟨subd0_2_16, List.forall_mem_cons.2 ⟨subd0_2_17, List.forall_mem_cons.2 ⟨subd0_2_18, List.forall_mem_cons.2 ⟨subd0_2_19, List.forall_mem_cons.2 ⟨subd0_2_20, List.forall_mem_cons.2 ⟨subd0_2_21, List.forall_mem_cons.2 ⟨subd0_2_22, List.forall_mem_cons.2 ⟨subd0_2_23, List.forall_mem_cons.2 ⟨subd0_2_24, List.forall_mem_cons.2 ⟨subd0_2_25, List.forall_mem_cons.2 ⟨subd0_2_26, List.forall_mem_cons.2 ⟨subd0_2_27, List.forall_mem_cons.2 ⟨subd0_2_28, List.forall_mem_cons.2 ⟨subd0_2_29, List.forall_mem_cons.2 ⟨subd0_2_30, List.forall_mem_cons.2 ⟨subd0_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_2_32 : subd0_2 [1, 3] = true := by decide +kernel
theorem subd0_2_33 : subd0_2 [2, -3] = true := by decide +kernel
theorem subd0_2_34 : subd0_2 [2, -2] = true := by decide +kernel
theorem subd0_2_35 : subd0_2 [2, -1] = true := by decide +kernel
theorem subd0_2_36 : subd0_2 [2, 0] = true := by decide +kernel
theorem subd0_2_37 : subd0_2 [2, 1] = true := by decide +kernel
theorem subd0_2_38 : subd0_2 [2, 2] = true := by decide +kernel
theorem subd0_2_39 : subd0_2 [2, 3] = true := by decide +kernel
theorem subd0_2_40 : subd0_2 [3] = true := by decide +kernel
theorem subd0_2_41 : subd0_2 [4] = true := by decide +kernel
theorem sbd0_2_1 : ∀ q ∈ blkd0_2_1, subd0_2 q = true := by
  unfold blkd0_2_1
  exact List.forall_mem_cons.2 ⟨subd0_2_32, List.forall_mem_cons.2 ⟨subd0_2_33, List.forall_mem_cons.2 ⟨subd0_2_34, List.forall_mem_cons.2 ⟨subd0_2_35, List.forall_mem_cons.2 ⟨subd0_2_36, List.forall_mem_cons.2 ⟨subd0_2_37, List.forall_mem_cons.2 ⟨subd0_2_38, List.forall_mem_cons.2 ⟨subd0_2_39, List.forall_mem_cons.2 ⟨subd0_2_40, List.forall_mem_cons.2 ⟨subd0_2_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [-3] = true := by decide +kernel
theorem subd0_3_1 : subd0_3 [-2, -4] = true := by decide +kernel
theorem subd0_3_2 : subd0_3 [-2, -3] = true := by decide +kernel
theorem subd0_3_3 : subd0_3 [-2, -2] = true := by decide +kernel
theorem subd0_3_4 : subd0_3 [-2, -1] = true := by decide +kernel
theorem subd0_3_5 : subd0_3 [-2, 0] = true := by decide +kernel
theorem subd0_3_6 : subd0_3 [-2, 1] = true := by decide +kernel
theorem subd0_3_7 : subd0_3 [-2, 2] = true := by decide +kernel
theorem subd0_3_8 : subd0_3 [-2, 3] = true := by decide +kernel
theorem subd0_3_9 : subd0_3 [-1, -4] = true := by decide +kernel
theorem subd0_3_10 : subd0_3 [-1, -3] = true := by decide +kernel
theorem subd0_3_11 : subd0_3 [-1, -2] = true := by decide +kernel
theorem subd0_3_12 : subd0_3 [-1, -1] = true := by decide +kernel
theorem subd0_3_13 : subd0_3 [-1, 0] = true := by decide +kernel
theorem subd0_3_14 : subd0_3 [-1, 1] = true := by decide +kernel
theorem subd0_3_15 : subd0_3 [-1, 2] = true := by decide +kernel
theorem subd0_3_16 : subd0_3 [-1, 3] = true := by decide +kernel
theorem subd0_3_17 : subd0_3 [0, -4] = true := by decide +kernel
theorem subd0_3_18 : subd0_3 [0, -3] = true := by decide +kernel
theorem subd0_3_19 : subd0_3 [0, -2] = true := by decide +kernel
theorem subd0_3_20 : subd0_3 [0, -1] = true := by decide +kernel
theorem subd0_3_21 : subd0_3 [0, 0] = true := by decide +kernel
theorem subd0_3_22 : subd0_3 [0, 1] = true := by decide +kernel
theorem subd0_3_23 : subd0_3 [0, 2] = true := by decide +kernel
theorem subd0_3_24 : subd0_3 [0, 3] = true := by decide +kernel
theorem subd0_3_25 : subd0_3 [1, -4] = true := by decide +kernel
theorem subd0_3_26 : subd0_3 [1, -3] = true := by decide +kernel
theorem subd0_3_27 : subd0_3 [1, -2] = true := by decide +kernel
theorem subd0_3_28 : subd0_3 [1, -1] = true := by decide +kernel
theorem subd0_3_29 : subd0_3 [1, 0] = true := by decide +kernel
theorem subd0_3_30 : subd0_3 [1, 1] = true := by decide +kernel
theorem subd0_3_31 : subd0_3 [1, 2] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_cons.2 ⟨subd0_3_1, List.forall_mem_cons.2 ⟨subd0_3_2, List.forall_mem_cons.2 ⟨subd0_3_3, List.forall_mem_cons.2 ⟨subd0_3_4, List.forall_mem_cons.2 ⟨subd0_3_5, List.forall_mem_cons.2 ⟨subd0_3_6, List.forall_mem_cons.2 ⟨subd0_3_7, List.forall_mem_cons.2 ⟨subd0_3_8, List.forall_mem_cons.2 ⟨subd0_3_9, List.forall_mem_cons.2 ⟨subd0_3_10, List.forall_mem_cons.2 ⟨subd0_3_11, List.forall_mem_cons.2 ⟨subd0_3_12, List.forall_mem_cons.2 ⟨subd0_3_13, List.forall_mem_cons.2 ⟨subd0_3_14, List.forall_mem_cons.2 ⟨subd0_3_15, List.forall_mem_cons.2 ⟨subd0_3_16, List.forall_mem_cons.2 ⟨subd0_3_17, List.forall_mem_cons.2 ⟨subd0_3_18, List.forall_mem_cons.2 ⟨subd0_3_19, List.forall_mem_cons.2 ⟨subd0_3_20, List.forall_mem_cons.2 ⟨subd0_3_21, List.forall_mem_cons.2 ⟨subd0_3_22, List.forall_mem_cons.2 ⟨subd0_3_23, List.forall_mem_cons.2 ⟨subd0_3_24, List.forall_mem_cons.2 ⟨subd0_3_25, List.forall_mem_cons.2 ⟨subd0_3_26, List.forall_mem_cons.2 ⟨subd0_3_27, List.forall_mem_cons.2 ⟨subd0_3_28, List.forall_mem_cons.2 ⟨subd0_3_29, List.forall_mem_cons.2 ⟨subd0_3_30, List.forall_mem_cons.2 ⟨subd0_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C136
