import ReflectZphi.Data.Cert5.C089.Base

namespace ReflectZphi.Data.Cert5.C089

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem subd0_1_0 : subd0_1 [-4] = true := by decide +kernel
theorem subd0_1_1 : subd0_1 [-3] = true := by decide +kernel
theorem subd0_1_2 : subd0_1 [-2, -2] = true := by decide +kernel
theorem subd0_1_3 : subd0_1 [-2, -1] = true := by decide +kernel
theorem subd0_1_4 : subd0_1 [-2, 0] = true := by decide +kernel
theorem subd0_1_5 : subd0_1 [-2, 1] = true := by decide +kernel
theorem subd0_1_6 : subd0_1 [-2, 2] = true := by decide +kernel
theorem subd0_1_7 : subd0_1 [-2, 3] = true := by decide +kernel
theorem subd0_1_8 : subd0_1 [-1, -3] = true := by decide +kernel
theorem subd0_1_9 : subd0_1 [-1, -2] = true := by decide +kernel
theorem subd0_1_10 : subd0_1 [-1, -1] = true := by decide +kernel
theorem subd0_1_11 : subd0_1 [-1, 0] = true := by decide +kernel
theorem subd0_1_12 : subd0_1 [-1, 1] = true := by decide +kernel
theorem subd0_1_13 : subd0_1 [-1, 2] = true := by decide +kernel
theorem subd0_1_14 : subd0_1 [-1, 3] = true := by decide +kernel
theorem subd0_1_15 : subd0_1 [0, -4] = true := by decide +kernel
theorem subd0_1_16 : subd0_1 [0, -3] = true := by decide +kernel
theorem subd0_1_17 : subd0_1 [0, -2] = true := by decide +kernel
theorem subd0_1_18 : subd0_1 [0, -1] = true := by decide +kernel
theorem subd0_1_19 : subd0_1 [0, 0] = true := by decide +kernel
theorem subd0_1_20 : subd0_1 [0, 1] = true := by decide +kernel
theorem subd0_1_21 : subd0_1 [0, 2] = true := by decide +kernel
theorem subd0_1_22 : subd0_1 [0, 3] = true := by decide +kernel
theorem subd0_1_23 : subd0_1 [1, -4] = true := by decide +kernel
theorem subd0_1_24 : subd0_1 [1, -3] = true := by decide +kernel
theorem subd0_1_25 : subd0_1 [1, -2] = true := by decide +kernel
theorem subd0_1_26 : subd0_1 [1, -1] = true := by decide +kernel
theorem subd0_1_27 : subd0_1 [1, 0] = true := by decide +kernel
theorem subd0_1_28 : subd0_1 [1, 1] = true := by decide +kernel
theorem subd0_1_29 : subd0_1 [1, 2] = true := by decide +kernel
theorem subd0_1_30 : subd0_1 [2, -4] = true := by decide +kernel
theorem subd0_1_31 : subd0_1 [2, -3] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_cons.2 ⟨subd0_1_1, List.forall_mem_cons.2 ⟨subd0_1_2, List.forall_mem_cons.2 ⟨subd0_1_3, List.forall_mem_cons.2 ⟨subd0_1_4, List.forall_mem_cons.2 ⟨subd0_1_5, List.forall_mem_cons.2 ⟨subd0_1_6, List.forall_mem_cons.2 ⟨subd0_1_7, List.forall_mem_cons.2 ⟨subd0_1_8, List.forall_mem_cons.2 ⟨subd0_1_9, List.forall_mem_cons.2 ⟨subd0_1_10, List.forall_mem_cons.2 ⟨subd0_1_11, List.forall_mem_cons.2 ⟨subd0_1_12, List.forall_mem_cons.2 ⟨subd0_1_13, List.forall_mem_cons.2 ⟨subd0_1_14, List.forall_mem_cons.2 ⟨subd0_1_15, List.forall_mem_cons.2 ⟨subd0_1_16, List.forall_mem_cons.2 ⟨subd0_1_17, List.forall_mem_cons.2 ⟨subd0_1_18, List.forall_mem_cons.2 ⟨subd0_1_19, List.forall_mem_cons.2 ⟨subd0_1_20, List.forall_mem_cons.2 ⟨subd0_1_21, List.forall_mem_cons.2 ⟨subd0_1_22, List.forall_mem_cons.2 ⟨subd0_1_23, List.forall_mem_cons.2 ⟨subd0_1_24, List.forall_mem_cons.2 ⟨subd0_1_25, List.forall_mem_cons.2 ⟨subd0_1_26, List.forall_mem_cons.2 ⟨subd0_1_27, List.forall_mem_cons.2 ⟨subd0_1_28, List.forall_mem_cons.2 ⟨subd0_1_29, List.forall_mem_cons.2 ⟨subd0_1_30, List.forall_mem_cons.2 ⟨subd0_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_1_32 : subd0_1 [2, -2] = true := by decide +kernel
theorem subd0_1_33 : subd0_1 [2, -1] = true := by decide +kernel
theorem subd0_1_34 : subd0_1 [2, 0] = true := by decide +kernel
theorem subd0_1_35 : subd0_1 [2, 1] = true := by decide +kernel
theorem subd0_1_36 : subd0_1 [3] = true := by decide +kernel
theorem subd0_1_37 : subd0_1 [4] = true := by decide +kernel
theorem sbd0_1_1 : ∀ q ∈ blkd0_1_1, subd0_1 q = true := by
  unfold blkd0_1_1
  exact List.forall_mem_cons.2 ⟨subd0_1_32, List.forall_mem_cons.2 ⟨subd0_1_33, List.forall_mem_cons.2 ⟨subd0_1_34, List.forall_mem_cons.2 ⟨subd0_1_35, List.forall_mem_cons.2 ⟨subd0_1_36, List.forall_mem_cons.2 ⟨subd0_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd0_2_0 : subd0_2 [-1] = true := by decide +kernel
theorem subd0_2_1 : subd0_2 [0] = true := by decide +kernel
theorem subd0_2_2 : subd0_2 [1] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_cons.2 ⟨subd0_2_1, List.forall_mem_cons.2 ⟨subd0_2_2, List.forall_mem_nil _⟩⟩⟩
theorem subd0_3_0 : subd0_3 [] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_nil _⟩
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩
theorem subd1_1_0 : subd1_1 [-2] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [-1] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [0] = true := by decide +kernel
theorem subd1_1_3 : subd1_1 [1] = true := by decide +kernel
theorem subd1_1_4 : subd1_1 [2] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_cons.2 ⟨subd1_1_3, List.forall_mem_cons.2 ⟨subd1_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd1_2_0 : subd1_2 [] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_nil _⟩
theorem subd1_3_0 : subd1_3 [] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_nil _⟩
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem subd2_1_0 : subd2_1 [-2] = true := by decide +kernel
theorem subd2_1_1 : subd2_1 [-1, -3] = true := by decide +kernel
theorem subd2_1_2 : subd2_1 [-1, -2] = true := by decide +kernel
theorem subd2_1_3 : subd2_1 [-1, -1] = true := by decide +kernel
theorem subd2_1_4 : subd2_1 [-1, 0] = true := by decide +kernel
theorem subd2_1_5 : subd2_1 [-1, 1] = true := by decide +kernel
theorem subd2_1_6 : subd2_1 [-1, 2] = true := by decide +kernel
theorem subd2_1_7 : subd2_1 [0, -3] = true := by decide +kernel
theorem subd2_1_8 : subd2_1 [0, -2] = true := by decide +kernel
theorem subd2_1_9 : subd2_1 [0, -1] = true := by decide +kernel
theorem subd2_1_10 : subd2_1 [0, 0] = true := by decide +kernel
theorem subd2_1_11 : subd2_1 [0, 1] = true := by decide +kernel
theorem subd2_1_12 : subd2_1 [0, 2] = true := by decide +kernel
theorem subd2_1_13 : subd2_1 [1, -3] = true := by decide +kernel
theorem subd2_1_14 : subd2_1 [1, -2] = true := by decide +kernel
theorem subd2_1_15 : subd2_1 [1, -1] = true := by decide +kernel
theorem subd2_1_16 : subd2_1 [1, 0] = true := by decide +kernel
theorem subd2_1_17 : subd2_1 [1, 1] = true := by decide +kernel
theorem subd2_1_18 : subd2_1 [1, 2] = true := by decide +kernel
theorem subd2_1_19 : subd2_1 [2] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_cons.2 ⟨subd2_1_1, List.forall_mem_cons.2 ⟨subd2_1_2, List.forall_mem_cons.2 ⟨subd2_1_3, List.forall_mem_cons.2 ⟨subd2_1_4, List.forall_mem_cons.2 ⟨subd2_1_5, List.forall_mem_cons.2 ⟨subd2_1_6, List.forall_mem_cons.2 ⟨subd2_1_7, List.forall_mem_cons.2 ⟨subd2_1_8, List.forall_mem_cons.2 ⟨subd2_1_9, List.forall_mem_cons.2 ⟨subd2_1_10, List.forall_mem_cons.2 ⟨subd2_1_11, List.forall_mem_cons.2 ⟨subd2_1_12, List.forall_mem_cons.2 ⟨subd2_1_13, List.forall_mem_cons.2 ⟨subd2_1_14, List.forall_mem_cons.2 ⟨subd2_1_15, List.forall_mem_cons.2 ⟨subd2_1_16, List.forall_mem_cons.2 ⟨subd2_1_17, List.forall_mem_cons.2 ⟨subd2_1_18, List.forall_mem_cons.2 ⟨subd2_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem subd3_0_0 : subd3_0 [] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_nil _⟩
theorem subd3_1_0 : subd3_1 [-3] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-2, -4] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-2, -3] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-2, -2] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-2, -1] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-2, 0] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [-2, 1] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [-2, 2] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [-2, 3] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [-1, -4] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [-1, -3] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [-1, 3] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [0, -4] = true := by decide +kernel
theorem subd3_1_18 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_19 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_20 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_21 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_22 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_23 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_24 : subd3_1 [0, 3] = true := by decide +kernel
theorem subd3_1_25 : subd3_1 [1, -4] = true := by decide +kernel
theorem subd3_1_26 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_27 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_28 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_29 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_30 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_31 : subd3_1 [1, 2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_cons.2 ⟨subd3_1_18, List.forall_mem_cons.2 ⟨subd3_1_19, List.forall_mem_cons.2 ⟨subd3_1_20, List.forall_mem_cons.2 ⟨subd3_1_21, List.forall_mem_cons.2 ⟨subd3_1_22, List.forall_mem_cons.2 ⟨subd3_1_23, List.forall_mem_cons.2 ⟨subd3_1_24, List.forall_mem_cons.2 ⟨subd3_1_25, List.forall_mem_cons.2 ⟨subd3_1_26, List.forall_mem_cons.2 ⟨subd3_1_27, List.forall_mem_cons.2 ⟨subd3_1_28, List.forall_mem_cons.2 ⟨subd3_1_29, List.forall_mem_cons.2 ⟨subd3_1_30, List.forall_mem_cons.2 ⟨subd3_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_1_32 : subd3_1 [1, 3] = true := by decide +kernel
theorem subd3_1_33 : subd3_1 [2, -4] = true := by decide +kernel
theorem subd3_1_34 : subd3_1 [2, -3] = true := by decide +kernel
theorem subd3_1_35 : subd3_1 [2, -2] = true := by decide +kernel
theorem subd3_1_36 : subd3_1 [2, -1] = true := by decide +kernel
theorem subd3_1_37 : subd3_1 [2, 0] = true := by decide +kernel
theorem subd3_1_38 : subd3_1 [2, 1] = true := by decide +kernel
theorem subd3_1_39 : subd3_1 [2, 2] = true := by decide +kernel
theorem subd3_1_40 : subd3_1 [2, 3] = true := by decide +kernel
theorem subd3_1_41 : subd3_1 [3] = true := by decide +kernel
theorem sbd3_1_1 : ∀ q ∈ blkd3_1_1, subd3_1 q = true := by
  unfold blkd3_1_1
  exact List.forall_mem_cons.2 ⟨subd3_1_32, List.forall_mem_cons.2 ⟨subd3_1_33, List.forall_mem_cons.2 ⟨subd3_1_34, List.forall_mem_cons.2 ⟨subd3_1_35, List.forall_mem_cons.2 ⟨subd3_1_36, List.forall_mem_cons.2 ⟨subd3_1_37, List.forall_mem_cons.2 ⟨subd3_1_38, List.forall_mem_cons.2 ⟨subd3_1_39, List.forall_mem_cons.2 ⟨subd3_1_40, List.forall_mem_cons.2 ⟨subd3_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_2_0 : subd3_2 [-1] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [0] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [1] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_nil _⟩⟩⟩
theorem subd3_3_0 : subd3_3 [-2] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-1] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [0] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [1] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [2] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd4_0_0 : subd4_0 [] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C089
