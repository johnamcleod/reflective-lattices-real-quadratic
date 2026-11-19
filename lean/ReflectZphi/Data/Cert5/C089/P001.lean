import ReflectZphi.Data.Cert5.C089.Base

namespace ReflectZphi.Data.Cert5.C089

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_1_0 : subd4_1 [-2, -4] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [2, 1] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_32 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [2, 3] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_nil _⟩⟩
theorem subd4_2_0 : subd4_2 [-1] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [0] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [1] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_nil _⟩⟩⟩
theorem subd4_3_0 : subd4_3 [-2] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-1] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [0] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [1] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [2] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd5_0_0 : subd5_0 [] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_nil _⟩
theorem subd5_1_0 : subd5_1 [-3] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-1, 3] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [1, -4] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [1, 2] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [2] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [3] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_0 : subd5_2 [] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_nil _⟩
theorem subd5_3_0 : subd5_3 [] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_nil _⟩
theorem subd6_0_0 : subd6_0 [] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_nil _⟩
theorem subd6_1_0 : subd6_1 [-2] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [2] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_0 : subd6_2 [] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_nil _⟩
theorem subd6_3_0 : subd6_3 [] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_nil _⟩
theorem subd7_0_0 : subd7_0 [] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_nil _⟩
theorem subd7_1_0 : subd7_1 [-2] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-1] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [0] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [2] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd7_2_0 : subd7_2 [] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_nil _⟩
theorem subd7_3_0 : subd7_3 [] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C089
