import ReflectZphi.Data.Cert5.C138.Base

namespace ReflectZphi.Data.Cert5.C138

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_1_0 : subd15_1 [-4] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-3] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-2, -4] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-2, -3] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-2, -2] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-2, -1] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-2, 0] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [-2, 1] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [-2, 2] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [-1, -4] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [-1, -3] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [-1, -2] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [-1, -1] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [-1, 0] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [-1, 1] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [-1, 2] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [-1, 3] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [0, -4] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [0, -3] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [0, -2] = true := by decide +kernel
theorem subd15_1_20 : subd15_1 [0, -1] = true := by decide +kernel
theorem subd15_1_21 : subd15_1 [0, 0] = true := by decide +kernel
theorem subd15_1_22 : subd15_1 [0, 1] = true := by decide +kernel
theorem subd15_1_23 : subd15_1 [0, 2] = true := by decide +kernel
theorem subd15_1_24 : subd15_1 [0, 3] = true := by decide +kernel
theorem subd15_1_25 : subd15_1 [1, -4] = true := by decide +kernel
theorem subd15_1_26 : subd15_1 [1, -3] = true := by decide +kernel
theorem subd15_1_27 : subd15_1 [1, -2] = true := by decide +kernel
theorem subd15_1_28 : subd15_1 [1, -1] = true := by decide +kernel
theorem subd15_1_29 : subd15_1 [1, 0] = true := by decide +kernel
theorem subd15_1_30 : subd15_1 [1, 1] = true := by decide +kernel
theorem subd15_1_31 : subd15_1 [1, 2] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_cons.2 ⟨subd15_1_20, List.forall_mem_cons.2 ⟨subd15_1_21, List.forall_mem_cons.2 ⟨subd15_1_22, List.forall_mem_cons.2 ⟨subd15_1_23, List.forall_mem_cons.2 ⟨subd15_1_24, List.forall_mem_cons.2 ⟨subd15_1_25, List.forall_mem_cons.2 ⟨subd15_1_26, List.forall_mem_cons.2 ⟨subd15_1_27, List.forall_mem_cons.2 ⟨subd15_1_28, List.forall_mem_cons.2 ⟨subd15_1_29, List.forall_mem_cons.2 ⟨subd15_1_30, List.forall_mem_cons.2 ⟨subd15_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_32 : subd15_1 [1, 3] = true := by decide +kernel
theorem subd15_1_33 : subd15_1 [2, -3] = true := by decide +kernel
theorem subd15_1_34 : subd15_1 [2, -2] = true := by decide +kernel
theorem subd15_1_35 : subd15_1 [2, -1] = true := by decide +kernel
theorem subd15_1_36 : subd15_1 [2, 0] = true := by decide +kernel
theorem subd15_1_37 : subd15_1 [2, 1] = true := by decide +kernel
theorem subd15_1_38 : subd15_1 [2, 2] = true := by decide +kernel
theorem subd15_1_39 : subd15_1 [2, 3] = true := by decide +kernel
theorem subd15_1_40 : subd15_1 [3] = true := by decide +kernel
theorem subd15_1_41 : subd15_1 [4] = true := by decide +kernel
theorem sbd15_1_1 : ∀ q ∈ blkd15_1_1, subd15_1 q = true := by
  unfold blkd15_1_1
  exact List.forall_mem_cons.2 ⟨subd15_1_32, List.forall_mem_cons.2 ⟨subd15_1_33, List.forall_mem_cons.2 ⟨subd15_1_34, List.forall_mem_cons.2 ⟨subd15_1_35, List.forall_mem_cons.2 ⟨subd15_1_36, List.forall_mem_cons.2 ⟨subd15_1_37, List.forall_mem_cons.2 ⟨subd15_1_38, List.forall_mem_cons.2 ⟨subd15_1_39, List.forall_mem_cons.2 ⟨subd15_1_40, List.forall_mem_cons.2 ⟨subd15_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [-2] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [-1] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [0] = true := by decide +kernel
theorem subd15_2_3 : subd15_2 [1] = true := by decide +kernel
theorem subd15_2_4 : subd15_2 [2] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_cons.2 ⟨subd15_2_3, List.forall_mem_cons.2 ⟨subd15_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [-2] = true := by decide +kernel
theorem subd15_3_1 : subd15_3 [-1, -3] = true := by decide +kernel
theorem subd15_3_2 : subd15_3 [-1, -2] = true := by decide +kernel
theorem subd15_3_3 : subd15_3 [-1, -1] = true := by decide +kernel
theorem subd15_3_4 : subd15_3 [-1, 0] = true := by decide +kernel
theorem subd15_3_5 : subd15_3 [-1, 1] = true := by decide +kernel
theorem subd15_3_6 : subd15_3 [-1, 2] = true := by decide +kernel
theorem subd15_3_7 : subd15_3 [0, -3] = true := by decide +kernel
theorem subd15_3_8 : subd15_3 [0, -2] = true := by decide +kernel
theorem subd15_3_9 : subd15_3 [0, -1] = true := by decide +kernel
theorem subd15_3_10 : subd15_3 [0, 0] = true := by decide +kernel
theorem subd15_3_11 : subd15_3 [0, 1] = true := by decide +kernel
theorem subd15_3_12 : subd15_3 [0, 2] = true := by decide +kernel
theorem subd15_3_13 : subd15_3 [1, -3] = true := by decide +kernel
theorem subd15_3_14 : subd15_3 [1, -2] = true := by decide +kernel
theorem subd15_3_15 : subd15_3 [1, -1] = true := by decide +kernel
theorem subd15_3_16 : subd15_3 [1, 0] = true := by decide +kernel
theorem subd15_3_17 : subd15_3 [1, 1] = true := by decide +kernel
theorem subd15_3_18 : subd15_3 [1, 2] = true := by decide +kernel
theorem subd15_3_19 : subd15_3 [2] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_cons.2 ⟨subd15_3_1, List.forall_mem_cons.2 ⟨subd15_3_2, List.forall_mem_cons.2 ⟨subd15_3_3, List.forall_mem_cons.2 ⟨subd15_3_4, List.forall_mem_cons.2 ⟨subd15_3_5, List.forall_mem_cons.2 ⟨subd15_3_6, List.forall_mem_cons.2 ⟨subd15_3_7, List.forall_mem_cons.2 ⟨subd15_3_8, List.forall_mem_cons.2 ⟨subd15_3_9, List.forall_mem_cons.2 ⟨subd15_3_10, List.forall_mem_cons.2 ⟨subd15_3_11, List.forall_mem_cons.2 ⟨subd15_3_12, List.forall_mem_cons.2 ⟨subd15_3_13, List.forall_mem_cons.2 ⟨subd15_3_14, List.forall_mem_cons.2 ⟨subd15_3_15, List.forall_mem_cons.2 ⟨subd15_3_16, List.forall_mem_cons.2 ⟨subd15_3_17, List.forall_mem_cons.2 ⟨subd15_3_18, List.forall_mem_cons.2 ⟨subd15_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_nil _⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-3] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-2, -3] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [-2, -2] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [-2, -1] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [-2, 0] = true := by decide +kernel
theorem subd16_1_5 : subd16_1 [-2, 1] = true := by decide +kernel
theorem subd16_1_6 : subd16_1 [-2, 2] = true := by decide +kernel
theorem subd16_1_7 : subd16_1 [-1, -4] = true := by decide +kernel
theorem subd16_1_8 : subd16_1 [-1, -3] = true := by decide +kernel
theorem subd16_1_9 : subd16_1 [-1, -2] = true := by decide +kernel
theorem subd16_1_10 : subd16_1 [-1, -1] = true := by decide +kernel
theorem subd16_1_11 : subd16_1 [-1, 0] = true := by decide +kernel
theorem subd16_1_12 : subd16_1 [-1, 1] = true := by decide +kernel
theorem subd16_1_13 : subd16_1 [-1, 2] = true := by decide +kernel
theorem subd16_1_14 : subd16_1 [-1, 3] = true := by decide +kernel
theorem subd16_1_15 : subd16_1 [0, -4] = true := by decide +kernel
theorem subd16_1_16 : subd16_1 [0, -3] = true := by decide +kernel
theorem subd16_1_17 : subd16_1 [0, -2] = true := by decide +kernel
theorem subd16_1_18 : subd16_1 [0, -1] = true := by decide +kernel
theorem subd16_1_19 : subd16_1 [0, 0] = true := by decide +kernel
theorem subd16_1_20 : subd16_1 [0, 1] = true := by decide +kernel
theorem subd16_1_21 : subd16_1 [0, 2] = true := by decide +kernel
theorem subd16_1_22 : subd16_1 [0, 3] = true := by decide +kernel
theorem subd16_1_23 : subd16_1 [1, -4] = true := by decide +kernel
theorem subd16_1_24 : subd16_1 [1, -3] = true := by decide +kernel
theorem subd16_1_25 : subd16_1 [1, -2] = true := by decide +kernel
theorem subd16_1_26 : subd16_1 [1, -1] = true := by decide +kernel
theorem subd16_1_27 : subd16_1 [1, 0] = true := by decide +kernel
theorem subd16_1_28 : subd16_1 [1, 1] = true := by decide +kernel
theorem subd16_1_29 : subd16_1 [1, 2] = true := by decide +kernel
theorem subd16_1_30 : subd16_1 [1, 3] = true := by decide +kernel
theorem subd16_1_31 : subd16_1 [2, -3] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_cons.2 ⟨subd16_1_5, List.forall_mem_cons.2 ⟨subd16_1_6, List.forall_mem_cons.2 ⟨subd16_1_7, List.forall_mem_cons.2 ⟨subd16_1_8, List.forall_mem_cons.2 ⟨subd16_1_9, List.forall_mem_cons.2 ⟨subd16_1_10, List.forall_mem_cons.2 ⟨subd16_1_11, List.forall_mem_cons.2 ⟨subd16_1_12, List.forall_mem_cons.2 ⟨subd16_1_13, List.forall_mem_cons.2 ⟨subd16_1_14, List.forall_mem_cons.2 ⟨subd16_1_15, List.forall_mem_cons.2 ⟨subd16_1_16, List.forall_mem_cons.2 ⟨subd16_1_17, List.forall_mem_cons.2 ⟨subd16_1_18, List.forall_mem_cons.2 ⟨subd16_1_19, List.forall_mem_cons.2 ⟨subd16_1_20, List.forall_mem_cons.2 ⟨subd16_1_21, List.forall_mem_cons.2 ⟨subd16_1_22, List.forall_mem_cons.2 ⟨subd16_1_23, List.forall_mem_cons.2 ⟨subd16_1_24, List.forall_mem_cons.2 ⟨subd16_1_25, List.forall_mem_cons.2 ⟨subd16_1_26, List.forall_mem_cons.2 ⟨subd16_1_27, List.forall_mem_cons.2 ⟨subd16_1_28, List.forall_mem_cons.2 ⟨subd16_1_29, List.forall_mem_cons.2 ⟨subd16_1_30, List.forall_mem_cons.2 ⟨subd16_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_32 : subd16_1 [2, -2] = true := by decide +kernel
theorem subd16_1_33 : subd16_1 [2, -1] = true := by decide +kernel
theorem subd16_1_34 : subd16_1 [2, 0] = true := by decide +kernel
theorem subd16_1_35 : subd16_1 [2, 1] = true := by decide +kernel
theorem subd16_1_36 : subd16_1 [2, 2] = true := by decide +kernel
theorem subd16_1_37 : subd16_1 [3] = true := by decide +kernel
theorem sbd16_1_1 : ∀ q ∈ blkd16_1_1, subd16_1 q = true := by
  unfold blkd16_1_1
  exact List.forall_mem_cons.2 ⟨subd16_1_32, List.forall_mem_cons.2 ⟨subd16_1_33, List.forall_mem_cons.2 ⟨subd16_1_34, List.forall_mem_cons.2 ⟨subd16_1_35, List.forall_mem_cons.2 ⟨subd16_1_36, List.forall_mem_cons.2 ⟨subd16_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C138
