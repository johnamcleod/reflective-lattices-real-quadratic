import ReflectZphi.Data.Cert5.C075.Base

namespace ReflectZphi.Data.Cert5.C075

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_0 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-2, -1] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-2, 0] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-2, 1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-2, 2] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-1, 3] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [2, -3] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [2, -2] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [2, -1] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [2, 0] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [2, 1] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_0 : subd6_2 [] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_nil _⟩
theorem subd6_3_0 : subd6_3 [-1] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [0] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_nil _⟩⟩⟩
theorem subd6_4_0 : subd6_4 [] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_nil _⟩
theorem subd6_5_0 : subd6_5 [] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_nil _⟩
theorem subd6_6_0 : subd6_6 [] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_nil _⟩
theorem subd7_0_0 : subd7_0 [-2] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [2] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_0 : subd7_1 [-3] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-2] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-1, -1] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-1, 3] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [0, 2] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [0, 3] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [1, 3] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [2] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [3] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_0 : subd7_2 [] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_nil _⟩
theorem subd7_3_0 : subd7_3 [] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_nil _⟩
theorem subd7_4_0 : subd7_4 [] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_nil _⟩
theorem subd7_5_0 : subd7_5 [] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_nil _⟩
theorem subd7_6_0 : subd7_6 [] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_nil _⟩
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_0 : subd8_1 [-3] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [1, 3] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [3] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_0 : subd8_2 [] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_nil _⟩
theorem subd8_3_0 : subd8_3 [] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_nil _⟩
theorem subd8_4_0 : subd8_4 [] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_nil _⟩
theorem subd8_5_0 : subd8_5 [] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_nil _⟩
theorem subd8_6_0 : subd8_6 [] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_nil _⟩
theorem subd9_0_0 : subd9_0 [-1] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [1] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C075
