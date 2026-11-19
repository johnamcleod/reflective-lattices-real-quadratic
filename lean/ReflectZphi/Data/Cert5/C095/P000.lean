import ReflectZphi.Data.Cert5.C095.Base

namespace ReflectZphi.Data.Cert5.C095

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem subd0_1_0 : subd0_1 [] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_nil _⟩
theorem subd0_2_0 : subd0_2 [] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_nil _⟩
theorem subd0_3_0 : subd0_3 [] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_nil _⟩
theorem subd0_4_0 : subd0_4 [] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_nil _⟩
theorem subd0_5_0 : subd0_5 [] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_nil _⟩
theorem subd0_6_0 : subd0_6 [] = true := by decide +kernel
theorem sbd0_6_0 : ∀ q ∈ blkd0_6_0, subd0_6 q = true := by
  unfold blkd0_6_0
  exact List.forall_mem_cons.2 ⟨subd0_6_0, List.forall_mem_nil _⟩
theorem subd1_0_0 : subd1_0 [0, -1] = true := by decide +kernel
theorem subd1_0_1 : subd1_0 [0, 0, -8] = true := by decide +kernel
theorem subd1_0_2 : subd1_0 [0, 0, -7] = true := by decide +kernel
theorem subd1_0_3 : subd1_0 [0, 0, -6] = true := by decide +kernel
theorem subd1_0_4 : subd1_0 [0, 0, -5] = true := by decide +kernel
theorem subd1_0_5 : subd1_0 [0, 0, -4] = true := by decide +kernel
theorem subd1_0_6 : subd1_0 [0, 0, -3] = true := by decide +kernel
theorem subd1_0_7 : subd1_0 [0, 0, -2] = true := by decide +kernel
theorem subd1_0_8 : subd1_0 [0, 0, -1] = true := by decide +kernel
theorem subd1_0_9 : subd1_0 [0, 0, 0] = true := by decide +kernel
theorem subd1_0_10 : subd1_0 [0, 0, 1] = true := by decide +kernel
theorem subd1_0_11 : subd1_0 [0, 0, 2] = true := by decide +kernel
theorem subd1_0_12 : subd1_0 [0, 0, 3] = true := by decide +kernel
theorem subd1_0_13 : subd1_0 [0, 0, 4] = true := by decide +kernel
theorem subd1_0_14 : subd1_0 [0, 0, 5] = true := by decide +kernel
theorem subd1_0_15 : subd1_0 [0, 0, 6] = true := by decide +kernel
theorem subd1_0_16 : subd1_0 [0, 0, 7] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_cons.2 ⟨subd1_0_1, List.forall_mem_cons.2 ⟨subd1_0_2, List.forall_mem_cons.2 ⟨subd1_0_3, List.forall_mem_cons.2 ⟨subd1_0_4, List.forall_mem_cons.2 ⟨subd1_0_5, List.forall_mem_cons.2 ⟨subd1_0_6, List.forall_mem_cons.2 ⟨subd1_0_7, List.forall_mem_cons.2 ⟨subd1_0_8, List.forall_mem_cons.2 ⟨subd1_0_9, List.forall_mem_cons.2 ⟨subd1_0_10, List.forall_mem_cons.2 ⟨subd1_0_11, List.forall_mem_cons.2 ⟨subd1_0_12, List.forall_mem_cons.2 ⟨subd1_0_13, List.forall_mem_cons.2 ⟨subd1_0_14, List.forall_mem_cons.2 ⟨subd1_0_15, List.forall_mem_cons.2 ⟨subd1_0_16, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_1_0 : subd1_1 [-1] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [0, -2] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [0, -1] = true := by decide +kernel
theorem subd1_1_3 : subd1_1 [0, 0] = true := by decide +kernel
theorem subd1_1_4 : subd1_1 [0, 1] = true := by decide +kernel
theorem subd1_1_5 : subd1_1 [1] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_cons.2 ⟨subd1_1_3, List.forall_mem_cons.2 ⟨subd1_1_4, List.forall_mem_cons.2 ⟨subd1_1_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd1_2_0 : subd1_2 [-1] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [0] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [1] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_nil _⟩⟩⟩
theorem subd1_3_0 : subd1_3 [-2] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-1] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [0] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [1] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [2] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd1_4_0 : subd1_4 [] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_nil _⟩
theorem subd1_5_0 : subd1_5 [] = true := by decide +kernel
theorem sbd1_5_0 : ∀ q ∈ blkd1_5_0, subd1_5 q = true := by
  unfold blkd1_5_0
  exact List.forall_mem_cons.2 ⟨subd1_5_0, List.forall_mem_nil _⟩
theorem subd1_6_0 : subd1_6 [] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_nil _⟩
theorem subd2_0_0 : subd2_0 [-1] = true := by decide +kernel
theorem subd2_0_1 : subd2_0 [0, -2] = true := by decide +kernel
theorem subd2_0_2 : subd2_0 [0, -1] = true := by decide +kernel
theorem subd2_0_3 : subd2_0 [0, 0, -7] = true := by decide +kernel
theorem subd2_0_4 : subd2_0 [0, 0, -6] = true := by decide +kernel
theorem subd2_0_5 : subd2_0 [0, 0, -5] = true := by decide +kernel
theorem subd2_0_6 : subd2_0 [0, 0, -4] = true := by decide +kernel
theorem subd2_0_7 : subd2_0 [0, 0, -3] = true := by decide +kernel
theorem subd2_0_8 : subd2_0 [0, 0, -2] = true := by decide +kernel
theorem subd2_0_9 : subd2_0 [0, 0, -1] = true := by decide +kernel
theorem subd2_0_10 : subd2_0 [0, 0, 0] = true := by decide +kernel
theorem subd2_0_11 : subd2_0 [0, 0, 1] = true := by decide +kernel
theorem subd2_0_12 : subd2_0 [0, 0, 2] = true := by decide +kernel
theorem subd2_0_13 : subd2_0 [0, 0, 3] = true := by decide +kernel
theorem subd2_0_14 : subd2_0 [0, 0, 4] = true := by decide +kernel
theorem subd2_0_15 : subd2_0 [0, 0, 5] = true := by decide +kernel
theorem subd2_0_16 : subd2_0 [0, 0, 6] = true := by decide +kernel
theorem subd2_0_17 : subd2_0 [0, 1] = true := by decide +kernel
theorem subd2_0_18 : subd2_0 [1] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_cons.2 ⟨subd2_0_1, List.forall_mem_cons.2 ⟨subd2_0_2, List.forall_mem_cons.2 ⟨subd2_0_3, List.forall_mem_cons.2 ⟨subd2_0_4, List.forall_mem_cons.2 ⟨subd2_0_5, List.forall_mem_cons.2 ⟨subd2_0_6, List.forall_mem_cons.2 ⟨subd2_0_7, List.forall_mem_cons.2 ⟨subd2_0_8, List.forall_mem_cons.2 ⟨subd2_0_9, List.forall_mem_cons.2 ⟨subd2_0_10, List.forall_mem_cons.2 ⟨subd2_0_11, List.forall_mem_cons.2 ⟨subd2_0_12, List.forall_mem_cons.2 ⟨subd2_0_13, List.forall_mem_cons.2 ⟨subd2_0_14, List.forall_mem_cons.2 ⟨subd2_0_15, List.forall_mem_cons.2 ⟨subd2_0_16, List.forall_mem_cons.2 ⟨subd2_0_17, List.forall_mem_cons.2 ⟨subd2_0_18, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_1_0 : subd2_1 [-1] = true := by decide +kernel
theorem subd2_1_1 : subd2_1 [0, -2] = true := by decide +kernel
theorem subd2_1_2 : subd2_1 [0, -1] = true := by decide +kernel
theorem subd2_1_3 : subd2_1 [0, 0] = true := by decide +kernel
theorem subd2_1_4 : subd2_1 [0, 1] = true := by decide +kernel
theorem subd2_1_5 : subd2_1 [1] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_cons.2 ⟨subd2_1_1, List.forall_mem_cons.2 ⟨subd2_1_2, List.forall_mem_cons.2 ⟨subd2_1_3, List.forall_mem_cons.2 ⟨subd2_1_4, List.forall_mem_cons.2 ⟨subd2_1_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem subd2_4_0 : subd2_4 [] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_nil _⟩
theorem subd2_5_0 : subd2_5 [] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_nil _⟩
theorem subd2_6_0 : subd2_6 [] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_nil _⟩
theorem subd3_0_0 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-1, -1] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-1, 0] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-1, 1] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [0, -2] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [0, -1] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [0, 0, -7] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [0, 0, -6] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [0, 0, -5] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [0, 0, -4] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [0, 0, -3] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [0, 0, -2] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [0, 0, -1] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [0, 0, 0] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [0, 0, 1] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [0, 0, 2] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [0, 0, 3] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [0, 0, 4] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [0, 0, 5] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [0, 0, 6] = true := by decide +kernel
theorem subd3_0_20 : subd3_0 [0, 1] = true := by decide +kernel
theorem subd3_0_21 : subd3_0 [1, -2] = true := by decide +kernel
theorem subd3_0_22 : subd3_0 [1, -1] = true := by decide +kernel
theorem subd3_0_23 : subd3_0 [1, 0] = true := by decide +kernel
theorem subd3_0_24 : subd3_0 [1, 1] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_cons.2 ⟨subd3_0_20, List.forall_mem_cons.2 ⟨subd3_0_21, List.forall_mem_cons.2 ⟨subd3_0_22, List.forall_mem_cons.2 ⟨subd3_0_23, List.forall_mem_cons.2 ⟨subd3_0_24, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1, -3] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_18 : subd3_1 [1, 2] = true := by decide +kernel
theorem subd3_1_19 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_cons.2 ⟨subd3_1_18, List.forall_mem_cons.2 ⟨subd3_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem subd3_4_0 : subd3_4 [] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_nil _⟩
theorem subd3_5_0 : subd3_5 [] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_nil _⟩
theorem subd3_6_0 : subd3_6 [] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_nil _⟩
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [1, 1] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_0 : subd4_1 [-3] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-2, 2] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [2, -3] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_32 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_34 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_35 : subd4_1 [2, 1] = true := by decide +kernel
theorem subd4_1_36 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_37 : subd4_1 [3] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_cons.2 ⟨subd4_1_34, List.forall_mem_cons.2 ⟨subd4_1_35, List.forall_mem_cons.2 ⟨subd4_1_36, List.forall_mem_cons.2 ⟨subd4_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd4_2_0 : subd4_2 [-2] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-1] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [0] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [1] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [2] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C095
