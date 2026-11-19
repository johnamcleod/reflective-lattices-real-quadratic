import ReflectZphi.Data.Cert5.C119.Base

namespace ReflectZphi.Data.Cert5.C119

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_0_0 : subd0_0 [-4] = true := by decide +kernel
theorem subd0_0_1 : subd0_0 [-3, -4] = true := by decide +kernel
theorem subd0_0_2 : subd0_0 [-3, -3] = true := by decide +kernel
theorem subd0_0_3 : subd0_0 [-3, -2] = true := by decide +kernel
theorem subd0_0_4 : subd0_0 [-3, -1] = true := by decide +kernel
theorem subd0_0_5 : subd0_0 [-3, 0] = true := by decide +kernel
theorem subd0_0_6 : subd0_0 [-3, 1] = true := by decide +kernel
theorem subd0_0_7 : subd0_0 [-3, 2] = true := by decide +kernel
theorem subd0_0_8 : subd0_0 [-3, 3] = true := by decide +kernel
theorem subd0_0_9 : subd0_0 [-2, -5] = true := by decide +kernel
theorem subd0_0_10 : subd0_0 [-2, -4] = true := by decide +kernel
theorem subd0_0_11 : subd0_0 [-2, -3] = true := by decide +kernel
theorem subd0_0_12 : subd0_0 [-2, -2] = true := by decide +kernel
theorem subd0_0_13 : subd0_0 [-2, -1] = true := by decide +kernel
theorem subd0_0_14 : subd0_0 [-2, 0] = true := by decide +kernel
theorem subd0_0_15 : subd0_0 [-2, 1] = true := by decide +kernel
theorem subd0_0_16 : subd0_0 [-2, 2] = true := by decide +kernel
theorem subd0_0_17 : subd0_0 [-2, 3] = true := by decide +kernel
theorem subd0_0_18 : subd0_0 [-2, 4] = true := by decide +kernel
theorem subd0_0_19 : subd0_0 [-1, -5] = true := by decide +kernel
theorem subd0_0_20 : subd0_0 [-1, -4] = true := by decide +kernel
theorem subd0_0_21 : subd0_0 [-1, -3] = true := by decide +kernel
theorem subd0_0_22 : subd0_0 [-1, -2] = true := by decide +kernel
theorem subd0_0_23 : subd0_0 [-1, -1] = true := by decide +kernel
theorem subd0_0_24 : subd0_0 [-1, 0] = true := by decide +kernel
theorem subd0_0_25 : subd0_0 [-1, 1] = true := by decide +kernel
theorem subd0_0_26 : subd0_0 [-1, 2] = true := by decide +kernel
theorem subd0_0_27 : subd0_0 [-1, 3] = true := by decide +kernel
theorem subd0_0_28 : subd0_0 [-1, 4] = true := by decide +kernel
theorem subd0_0_29 : subd0_0 [0, -5] = true := by decide +kernel
theorem subd0_0_30 : subd0_0 [0, -4] = true := by decide +kernel
theorem subd0_0_31 : subd0_0 [0, -3] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_cons.2 ⟨subd0_0_1, List.forall_mem_cons.2 ⟨subd0_0_2, List.forall_mem_cons.2 ⟨subd0_0_3, List.forall_mem_cons.2 ⟨subd0_0_4, List.forall_mem_cons.2 ⟨subd0_0_5, List.forall_mem_cons.2 ⟨subd0_0_6, List.forall_mem_cons.2 ⟨subd0_0_7, List.forall_mem_cons.2 ⟨subd0_0_8, List.forall_mem_cons.2 ⟨subd0_0_9, List.forall_mem_cons.2 ⟨subd0_0_10, List.forall_mem_cons.2 ⟨subd0_0_11, List.forall_mem_cons.2 ⟨subd0_0_12, List.forall_mem_cons.2 ⟨subd0_0_13, List.forall_mem_cons.2 ⟨subd0_0_14, List.forall_mem_cons.2 ⟨subd0_0_15, List.forall_mem_cons.2 ⟨subd0_0_16, List.forall_mem_cons.2 ⟨subd0_0_17, List.forall_mem_cons.2 ⟨subd0_0_18, List.forall_mem_cons.2 ⟨subd0_0_19, List.forall_mem_cons.2 ⟨subd0_0_20, List.forall_mem_cons.2 ⟨subd0_0_21, List.forall_mem_cons.2 ⟨subd0_0_22, List.forall_mem_cons.2 ⟨subd0_0_23, List.forall_mem_cons.2 ⟨subd0_0_24, List.forall_mem_cons.2 ⟨subd0_0_25, List.forall_mem_cons.2 ⟨subd0_0_26, List.forall_mem_cons.2 ⟨subd0_0_27, List.forall_mem_cons.2 ⟨subd0_0_28, List.forall_mem_cons.2 ⟨subd0_0_29, List.forall_mem_cons.2 ⟨subd0_0_30, List.forall_mem_cons.2 ⟨subd0_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_0_32 : subd0_0 [0, -2] = true := by decide +kernel
theorem subd0_0_33 : subd0_0 [0, -1] = true := by decide +kernel
theorem subd0_0_34 : subd0_0 [0, 0] = true := by decide +kernel
theorem subd0_0_35 : subd0_0 [0, 1] = true := by decide +kernel
theorem subd0_0_36 : subd0_0 [0, 2] = true := by decide +kernel
theorem subd0_0_37 : subd0_0 [0, 3] = true := by decide +kernel
theorem subd0_0_38 : subd0_0 [0, 4] = true := by decide +kernel
theorem subd0_0_39 : subd0_0 [1, -5] = true := by decide +kernel
theorem subd0_0_40 : subd0_0 [1, -4] = true := by decide +kernel
theorem subd0_0_41 : subd0_0 [1, -3] = true := by decide +kernel
theorem subd0_0_42 : subd0_0 [1, -2] = true := by decide +kernel
theorem subd0_0_43 : subd0_0 [1, -1] = true := by decide +kernel
theorem subd0_0_44 : subd0_0 [1, 0] = true := by decide +kernel
theorem subd0_0_45 : subd0_0 [1, 1] = true := by decide +kernel
theorem subd0_0_46 : subd0_0 [1, 2] = true := by decide +kernel
theorem subd0_0_47 : subd0_0 [1, 3] = true := by decide +kernel
theorem subd0_0_48 : subd0_0 [1, 4] = true := by decide +kernel
theorem subd0_0_49 : subd0_0 [2, -5] = true := by decide +kernel
theorem subd0_0_50 : subd0_0 [2, -4] = true := by decide +kernel
theorem subd0_0_51 : subd0_0 [2, -3] = true := by decide +kernel
theorem subd0_0_52 : subd0_0 [2, -2] = true := by decide +kernel
theorem subd0_0_53 : subd0_0 [2, -1] = true := by decide +kernel
theorem subd0_0_54 : subd0_0 [2, 0] = true := by decide +kernel
theorem subd0_0_55 : subd0_0 [2, 1] = true := by decide +kernel
theorem subd0_0_56 : subd0_0 [2, 2] = true := by decide +kernel
theorem subd0_0_57 : subd0_0 [2, 3] = true := by decide +kernel
theorem subd0_0_58 : subd0_0 [2, 4] = true := by decide +kernel
theorem subd0_0_59 : subd0_0 [3, -4] = true := by decide +kernel
theorem subd0_0_60 : subd0_0 [3, -3] = true := by decide +kernel
theorem subd0_0_61 : subd0_0 [3, -2] = true := by decide +kernel
theorem subd0_0_62 : subd0_0 [3, -1] = true := by decide +kernel
theorem subd0_0_63 : subd0_0 [3, 0] = true := by decide +kernel
theorem sbd0_0_1 : ∀ q ∈ blkd0_0_1, subd0_0 q = true := by
  unfold blkd0_0_1
  exact List.forall_mem_cons.2 ⟨subd0_0_32, List.forall_mem_cons.2 ⟨subd0_0_33, List.forall_mem_cons.2 ⟨subd0_0_34, List.forall_mem_cons.2 ⟨subd0_0_35, List.forall_mem_cons.2 ⟨subd0_0_36, List.forall_mem_cons.2 ⟨subd0_0_37, List.forall_mem_cons.2 ⟨subd0_0_38, List.forall_mem_cons.2 ⟨subd0_0_39, List.forall_mem_cons.2 ⟨subd0_0_40, List.forall_mem_cons.2 ⟨subd0_0_41, List.forall_mem_cons.2 ⟨subd0_0_42, List.forall_mem_cons.2 ⟨subd0_0_43, List.forall_mem_cons.2 ⟨subd0_0_44, List.forall_mem_cons.2 ⟨subd0_0_45, List.forall_mem_cons.2 ⟨subd0_0_46, List.forall_mem_cons.2 ⟨subd0_0_47, List.forall_mem_cons.2 ⟨subd0_0_48, List.forall_mem_cons.2 ⟨subd0_0_49, List.forall_mem_cons.2 ⟨subd0_0_50, List.forall_mem_cons.2 ⟨subd0_0_51, List.forall_mem_cons.2 ⟨subd0_0_52, List.forall_mem_cons.2 ⟨subd0_0_53, List.forall_mem_cons.2 ⟨subd0_0_54, List.forall_mem_cons.2 ⟨subd0_0_55, List.forall_mem_cons.2 ⟨subd0_0_56, List.forall_mem_cons.2 ⟨subd0_0_57, List.forall_mem_cons.2 ⟨subd0_0_58, List.forall_mem_cons.2 ⟨subd0_0_59, List.forall_mem_cons.2 ⟨subd0_0_60, List.forall_mem_cons.2 ⟨subd0_0_61, List.forall_mem_cons.2 ⟨subd0_0_62, List.forall_mem_cons.2 ⟨subd0_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_0_64 : subd0_0 [3, 1] = true := by decide +kernel
theorem subd0_0_65 : subd0_0 [3, 2] = true := by decide +kernel
theorem subd0_0_66 : subd0_0 [3, 3] = true := by decide +kernel
theorem subd0_0_67 : subd0_0 [4] = true := by decide +kernel
theorem sbd0_0_2 : ∀ q ∈ blkd0_0_2, subd0_0 q = true := by
  unfold blkd0_0_2
  exact List.forall_mem_cons.2 ⟨subd0_0_64, List.forall_mem_cons.2 ⟨subd0_0_65, List.forall_mem_cons.2 ⟨subd0_0_66, List.forall_mem_cons.2 ⟨subd0_0_67, List.forall_mem_nil _⟩⟩⟩⟩
theorem subd0_1_0 : subd0_1 [-2] = true := by decide +kernel
theorem subd0_1_1 : subd0_1 [-1] = true := by decide +kernel
theorem subd0_1_2 : subd0_1 [0] = true := by decide +kernel
theorem subd0_1_3 : subd0_1 [1] = true := by decide +kernel
theorem subd0_1_4 : subd0_1 [2] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_cons.2 ⟨subd0_1_1, List.forall_mem_cons.2 ⟨subd0_1_2, List.forall_mem_cons.2 ⟨subd0_1_3, List.forall_mem_cons.2 ⟨subd0_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd1_0_0 : subd1_0 [-3] = true := by decide +kernel
theorem subd1_0_1 : subd1_0 [-2, -3] = true := by decide +kernel
theorem subd1_0_2 : subd1_0 [-2, -2] = true := by decide +kernel
theorem subd1_0_3 : subd1_0 [-2, -1] = true := by decide +kernel
theorem subd1_0_4 : subd1_0 [-2, 0] = true := by decide +kernel
theorem subd1_0_5 : subd1_0 [-2, 1] = true := by decide +kernel
theorem subd1_0_6 : subd1_0 [-2, 2] = true := by decide +kernel
theorem subd1_0_7 : subd1_0 [-2, 3] = true := by decide +kernel
theorem subd1_0_8 : subd1_0 [-2, 4] = true := by decide +kernel
theorem subd1_0_9 : subd1_0 [-1, -4] = true := by decide +kernel
theorem subd1_0_10 : subd1_0 [-1, -3] = true := by decide +kernel
theorem subd1_0_11 : subd1_0 [-1, -2] = true := by decide +kernel
theorem subd1_0_12 : subd1_0 [-1, -1] = true := by decide +kernel
theorem subd1_0_13 : subd1_0 [-1, 0] = true := by decide +kernel
theorem subd1_0_14 : subd1_0 [-1, 1] = true := by decide +kernel
theorem subd1_0_15 : subd1_0 [-1, 2] = true := by decide +kernel
theorem subd1_0_16 : subd1_0 [-1, 3] = true := by decide +kernel
theorem subd1_0_17 : subd1_0 [-1, 4] = true := by decide +kernel
theorem subd1_0_18 : subd1_0 [0, -4] = true := by decide +kernel
theorem subd1_0_19 : subd1_0 [0, -3] = true := by decide +kernel
theorem subd1_0_20 : subd1_0 [0, -2] = true := by decide +kernel
theorem subd1_0_21 : subd1_0 [0, -1] = true := by decide +kernel
theorem subd1_0_22 : subd1_0 [0, 0] = true := by decide +kernel
theorem subd1_0_23 : subd1_0 [0, 1] = true := by decide +kernel
theorem subd1_0_24 : subd1_0 [0, 2] = true := by decide +kernel
theorem subd1_0_25 : subd1_0 [0, 3] = true := by decide +kernel
theorem subd1_0_26 : subd1_0 [1, -5] = true := by decide +kernel
theorem subd1_0_27 : subd1_0 [1, -4] = true := by decide +kernel
theorem subd1_0_28 : subd1_0 [1, -3] = true := by decide +kernel
theorem subd1_0_29 : subd1_0 [1, -2] = true := by decide +kernel
theorem subd1_0_30 : subd1_0 [1, -1] = true := by decide +kernel
theorem subd1_0_31 : subd1_0 [1, 0] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_cons.2 ⟨subd1_0_1, List.forall_mem_cons.2 ⟨subd1_0_2, List.forall_mem_cons.2 ⟨subd1_0_3, List.forall_mem_cons.2 ⟨subd1_0_4, List.forall_mem_cons.2 ⟨subd1_0_5, List.forall_mem_cons.2 ⟨subd1_0_6, List.forall_mem_cons.2 ⟨subd1_0_7, List.forall_mem_cons.2 ⟨subd1_0_8, List.forall_mem_cons.2 ⟨subd1_0_9, List.forall_mem_cons.2 ⟨subd1_0_10, List.forall_mem_cons.2 ⟨subd1_0_11, List.forall_mem_cons.2 ⟨subd1_0_12, List.forall_mem_cons.2 ⟨subd1_0_13, List.forall_mem_cons.2 ⟨subd1_0_14, List.forall_mem_cons.2 ⟨subd1_0_15, List.forall_mem_cons.2 ⟨subd1_0_16, List.forall_mem_cons.2 ⟨subd1_0_17, List.forall_mem_cons.2 ⟨subd1_0_18, List.forall_mem_cons.2 ⟨subd1_0_19, List.forall_mem_cons.2 ⟨subd1_0_20, List.forall_mem_cons.2 ⟨subd1_0_21, List.forall_mem_cons.2 ⟨subd1_0_22, List.forall_mem_cons.2 ⟨subd1_0_23, List.forall_mem_cons.2 ⟨subd1_0_24, List.forall_mem_cons.2 ⟨subd1_0_25, List.forall_mem_cons.2 ⟨subd1_0_26, List.forall_mem_cons.2 ⟨subd1_0_27, List.forall_mem_cons.2 ⟨subd1_0_28, List.forall_mem_cons.2 ⟨subd1_0_29, List.forall_mem_cons.2 ⟨subd1_0_30, List.forall_mem_cons.2 ⟨subd1_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_0_32 : subd1_0 [1, 1] = true := by decide +kernel
theorem subd1_0_33 : subd1_0 [1, 2] = true := by decide +kernel
theorem subd1_0_34 : subd1_0 [1, 3] = true := by decide +kernel
theorem subd1_0_35 : subd1_0 [2, -5] = true := by decide +kernel
theorem subd1_0_36 : subd1_0 [2, -4] = true := by decide +kernel
theorem subd1_0_37 : subd1_0 [2, -3] = true := by decide +kernel
theorem subd1_0_38 : subd1_0 [2, -2] = true := by decide +kernel
theorem subd1_0_39 : subd1_0 [2, -1] = true := by decide +kernel
theorem subd1_0_40 : subd1_0 [2, 0] = true := by decide +kernel
theorem subd1_0_41 : subd1_0 [2, 1] = true := by decide +kernel
theorem subd1_0_42 : subd1_0 [2, 2] = true := by decide +kernel
theorem subd1_0_43 : subd1_0 [3] = true := by decide +kernel
theorem sbd1_0_1 : ∀ q ∈ blkd1_0_1, subd1_0 q = true := by
  unfold blkd1_0_1
  exact List.forall_mem_cons.2 ⟨subd1_0_32, List.forall_mem_cons.2 ⟨subd1_0_33, List.forall_mem_cons.2 ⟨subd1_0_34, List.forall_mem_cons.2 ⟨subd1_0_35, List.forall_mem_cons.2 ⟨subd1_0_36, List.forall_mem_cons.2 ⟨subd1_0_37, List.forall_mem_cons.2 ⟨subd1_0_38, List.forall_mem_cons.2 ⟨subd1_0_39, List.forall_mem_cons.2 ⟨subd1_0_40, List.forall_mem_cons.2 ⟨subd1_0_41, List.forall_mem_cons.2 ⟨subd1_0_42, List.forall_mem_cons.2 ⟨subd1_0_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_1_0 : subd1_1 [] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_nil _⟩
theorem subd2_0_0 : subd2_0 [-3] = true := by decide +kernel
theorem subd2_0_1 : subd2_0 [-2, -4] = true := by decide +kernel
theorem subd2_0_2 : subd2_0 [-2, -3] = true := by decide +kernel
theorem subd2_0_3 : subd2_0 [-2, -2] = true := by decide +kernel
theorem subd2_0_4 : subd2_0 [-2, -1] = true := by decide +kernel
theorem subd2_0_5 : subd2_0 [-2, 0] = true := by decide +kernel
theorem subd2_0_6 : subd2_0 [-2, 1] = true := by decide +kernel
theorem subd2_0_7 : subd2_0 [-2, 2] = true := by decide +kernel
theorem subd2_0_8 : subd2_0 [-2, 3] = true := by decide +kernel
theorem subd2_0_9 : subd2_0 [-1, -4] = true := by decide +kernel
theorem subd2_0_10 : subd2_0 [-1, -3] = true := by decide +kernel
theorem subd2_0_11 : subd2_0 [-1, -2] = true := by decide +kernel
theorem subd2_0_12 : subd2_0 [-1, -1] = true := by decide +kernel
theorem subd2_0_13 : subd2_0 [-1, 0] = true := by decide +kernel
theorem subd2_0_14 : subd2_0 [-1, 1] = true := by decide +kernel
theorem subd2_0_15 : subd2_0 [-1, 2] = true := by decide +kernel
theorem subd2_0_16 : subd2_0 [-1, 3] = true := by decide +kernel
theorem subd2_0_17 : subd2_0 [-1, 4] = true := by decide +kernel
theorem subd2_0_18 : subd2_0 [0, -5] = true := by decide +kernel
theorem subd2_0_19 : subd2_0 [0, -4] = true := by decide +kernel
theorem subd2_0_20 : subd2_0 [0, -3] = true := by decide +kernel
theorem subd2_0_21 : subd2_0 [0, -2] = true := by decide +kernel
theorem subd2_0_22 : subd2_0 [0, -1] = true := by decide +kernel
theorem subd2_0_23 : subd2_0 [0, 0] = true := by decide +kernel
theorem subd2_0_24 : subd2_0 [0, 1] = true := by decide +kernel
theorem subd2_0_25 : subd2_0 [0, 2] = true := by decide +kernel
theorem subd2_0_26 : subd2_0 [0, 3] = true := by decide +kernel
theorem subd2_0_27 : subd2_0 [0, 4] = true := by decide +kernel
theorem subd2_0_28 : subd2_0 [1, -5] = true := by decide +kernel
theorem subd2_0_29 : subd2_0 [1, -4] = true := by decide +kernel
theorem subd2_0_30 : subd2_0 [1, -3] = true := by decide +kernel
theorem subd2_0_31 : subd2_0 [1, -2] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_cons.2 ⟨subd2_0_1, List.forall_mem_cons.2 ⟨subd2_0_2, List.forall_mem_cons.2 ⟨subd2_0_3, List.forall_mem_cons.2 ⟨subd2_0_4, List.forall_mem_cons.2 ⟨subd2_0_5, List.forall_mem_cons.2 ⟨subd2_0_6, List.forall_mem_cons.2 ⟨subd2_0_7, List.forall_mem_cons.2 ⟨subd2_0_8, List.forall_mem_cons.2 ⟨subd2_0_9, List.forall_mem_cons.2 ⟨subd2_0_10, List.forall_mem_cons.2 ⟨subd2_0_11, List.forall_mem_cons.2 ⟨subd2_0_12, List.forall_mem_cons.2 ⟨subd2_0_13, List.forall_mem_cons.2 ⟨subd2_0_14, List.forall_mem_cons.2 ⟨subd2_0_15, List.forall_mem_cons.2 ⟨subd2_0_16, List.forall_mem_cons.2 ⟨subd2_0_17, List.forall_mem_cons.2 ⟨subd2_0_18, List.forall_mem_cons.2 ⟨subd2_0_19, List.forall_mem_cons.2 ⟨subd2_0_20, List.forall_mem_cons.2 ⟨subd2_0_21, List.forall_mem_cons.2 ⟨subd2_0_22, List.forall_mem_cons.2 ⟨subd2_0_23, List.forall_mem_cons.2 ⟨subd2_0_24, List.forall_mem_cons.2 ⟨subd2_0_25, List.forall_mem_cons.2 ⟨subd2_0_26, List.forall_mem_cons.2 ⟨subd2_0_27, List.forall_mem_cons.2 ⟨subd2_0_28, List.forall_mem_cons.2 ⟨subd2_0_29, List.forall_mem_cons.2 ⟨subd2_0_30, List.forall_mem_cons.2 ⟨subd2_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_0_32 : subd2_0 [1, -1] = true := by decide +kernel
theorem subd2_0_33 : subd2_0 [1, 0] = true := by decide +kernel
theorem subd2_0_34 : subd2_0 [1, 1] = true := by decide +kernel
theorem subd2_0_35 : subd2_0 [1, 2] = true := by decide +kernel
theorem subd2_0_36 : subd2_0 [1, 3] = true := by decide +kernel
theorem subd2_0_37 : subd2_0 [2, -4] = true := by decide +kernel
theorem subd2_0_38 : subd2_0 [2, -3] = true := by decide +kernel
theorem subd2_0_39 : subd2_0 [2, -2] = true := by decide +kernel
theorem subd2_0_40 : subd2_0 [2, -1] = true := by decide +kernel
theorem subd2_0_41 : subd2_0 [2, 0] = true := by decide +kernel
theorem subd2_0_42 : subd2_0 [2, 1] = true := by decide +kernel
theorem subd2_0_43 : subd2_0 [2, 2] = true := by decide +kernel
theorem subd2_0_44 : subd2_0 [2, 3] = true := by decide +kernel
theorem subd2_0_45 : subd2_0 [3] = true := by decide +kernel
theorem sbd2_0_1 : ∀ q ∈ blkd2_0_1, subd2_0 q = true := by
  unfold blkd2_0_1
  exact List.forall_mem_cons.2 ⟨subd2_0_32, List.forall_mem_cons.2 ⟨subd2_0_33, List.forall_mem_cons.2 ⟨subd2_0_34, List.forall_mem_cons.2 ⟨subd2_0_35, List.forall_mem_cons.2 ⟨subd2_0_36, List.forall_mem_cons.2 ⟨subd2_0_37, List.forall_mem_cons.2 ⟨subd2_0_38, List.forall_mem_cons.2 ⟨subd2_0_39, List.forall_mem_cons.2 ⟨subd2_0_40, List.forall_mem_cons.2 ⟨subd2_0_41, List.forall_mem_cons.2 ⟨subd2_0_42, List.forall_mem_cons.2 ⟨subd2_0_43, List.forall_mem_cons.2 ⟨subd2_0_44, List.forall_mem_cons.2 ⟨subd2_0_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩
theorem subd3_0_0 : subd3_0 [-4] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-3, -5] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-3, -4] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-3, -3] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [-3, -2] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [-3, -1] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [-3, 0] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [-3, 1] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [-3, 2] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [-2, -6] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [-2, -5] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [-2, -4] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [-2, -3] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [-2, -2] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [-2, -1] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [-2, 0] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [-2, 1] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [-2, 2] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [-2, 3] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [-1, -6] = true := by decide +kernel
theorem subd3_0_20 : subd3_0 [-1, -5] = true := by decide +kernel
theorem subd3_0_21 : subd3_0 [-1, -4] = true := by decide +kernel
theorem subd3_0_22 : subd3_0 [-1, -3] = true := by decide +kernel
theorem subd3_0_23 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_24 : subd3_0 [-1, -1] = true := by decide +kernel
theorem subd3_0_25 : subd3_0 [-1, 0] = true := by decide +kernel
theorem subd3_0_26 : subd3_0 [-1, 1] = true := by decide +kernel
theorem subd3_0_27 : subd3_0 [-1, 2] = true := by decide +kernel
theorem subd3_0_28 : subd3_0 [-1, 3] = true := by decide +kernel
theorem subd3_0_29 : subd3_0 [-1, 4] = true := by decide +kernel
theorem subd3_0_30 : subd3_0 [0, -5] = true := by decide +kernel
theorem subd3_0_31 : subd3_0 [0, -4] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_cons.2 ⟨subd3_0_20, List.forall_mem_cons.2 ⟨subd3_0_21, List.forall_mem_cons.2 ⟨subd3_0_22, List.forall_mem_cons.2 ⟨subd3_0_23, List.forall_mem_cons.2 ⟨subd3_0_24, List.forall_mem_cons.2 ⟨subd3_0_25, List.forall_mem_cons.2 ⟨subd3_0_26, List.forall_mem_cons.2 ⟨subd3_0_27, List.forall_mem_cons.2 ⟨subd3_0_28, List.forall_mem_cons.2 ⟨subd3_0_29, List.forall_mem_cons.2 ⟨subd3_0_30, List.forall_mem_cons.2 ⟨subd3_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C119
