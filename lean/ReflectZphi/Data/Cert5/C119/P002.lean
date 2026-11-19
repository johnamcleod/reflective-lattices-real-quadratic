import ReflectZphi.Data.Cert5.C119.Base

namespace ReflectZphi.Data.Cert5.C119

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_32 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [0, 4] = true := by decide +kernel
theorem subd5_0_40 : subd5_0 [1, -5] = true := by decide +kernel
theorem subd5_0_41 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_42 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_43 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_44 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_45 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_46 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_47 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_48 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_49 : subd5_0 [1, 4] = true := by decide +kernel
theorem subd5_0_50 : subd5_0 [2, -5] = true := by decide +kernel
theorem subd5_0_51 : subd5_0 [2, -4] = true := by decide +kernel
theorem subd5_0_52 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_53 : subd5_0 [2, -2] = true := by decide +kernel
theorem subd5_0_54 : subd5_0 [2, -1] = true := by decide +kernel
theorem subd5_0_55 : subd5_0 [2, 0] = true := by decide +kernel
theorem subd5_0_56 : subd5_0 [2, 1] = true := by decide +kernel
theorem subd5_0_57 : subd5_0 [2, 2] = true := by decide +kernel
theorem subd5_0_58 : subd5_0 [2, 3] = true := by decide +kernel
theorem subd5_0_59 : subd5_0 [2, 4] = true := by decide +kernel
theorem subd5_0_60 : subd5_0 [3, -4] = true := by decide +kernel
theorem subd5_0_61 : subd5_0 [3, -3] = true := by decide +kernel
theorem subd5_0_62 : subd5_0 [3, -2] = true := by decide +kernel
theorem subd5_0_63 : subd5_0 [3, -1] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_cons.2 ⟨subd5_0_40, List.forall_mem_cons.2 ⟨subd5_0_41, List.forall_mem_cons.2 ⟨subd5_0_42, List.forall_mem_cons.2 ⟨subd5_0_43, List.forall_mem_cons.2 ⟨subd5_0_44, List.forall_mem_cons.2 ⟨subd5_0_45, List.forall_mem_cons.2 ⟨subd5_0_46, List.forall_mem_cons.2 ⟨subd5_0_47, List.forall_mem_cons.2 ⟨subd5_0_48, List.forall_mem_cons.2 ⟨subd5_0_49, List.forall_mem_cons.2 ⟨subd5_0_50, List.forall_mem_cons.2 ⟨subd5_0_51, List.forall_mem_cons.2 ⟨subd5_0_52, List.forall_mem_cons.2 ⟨subd5_0_53, List.forall_mem_cons.2 ⟨subd5_0_54, List.forall_mem_cons.2 ⟨subd5_0_55, List.forall_mem_cons.2 ⟨subd5_0_56, List.forall_mem_cons.2 ⟨subd5_0_57, List.forall_mem_cons.2 ⟨subd5_0_58, List.forall_mem_cons.2 ⟨subd5_0_59, List.forall_mem_cons.2 ⟨subd5_0_60, List.forall_mem_cons.2 ⟨subd5_0_61, List.forall_mem_cons.2 ⟨subd5_0_62, List.forall_mem_cons.2 ⟨subd5_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_64 : subd5_0 [3, 0] = true := by decide +kernel
theorem subd5_0_65 : subd5_0 [3, 1] = true := by decide +kernel
theorem subd5_0_66 : subd5_0 [3, 2] = true := by decide +kernel
theorem subd5_0_67 : subd5_0 [3, 3] = true := by decide +kernel
theorem subd5_0_68 : subd5_0 [3, 4] = true := by decide +kernel
theorem subd5_0_69 : subd5_0 [4] = true := by decide +kernel
theorem sbd5_0_2 : ∀ q ∈ blkd5_0_2, subd5_0 q = true := by
  unfold blkd5_0_2
  exact List.forall_mem_cons.2 ⟨subd5_0_64, List.forall_mem_cons.2 ⟨subd5_0_65, List.forall_mem_cons.2 ⟨subd5_0_66, List.forall_mem_cons.2 ⟨subd5_0_67, List.forall_mem_cons.2 ⟨subd5_0_68, List.forall_mem_cons.2 ⟨subd5_0_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd5_1_0 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [1] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_nil _⟩⟩⟩
theorem subd6_0_0 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [0, 0, -8] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, 0, -7] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [0, 0, -6] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [0, 0, -5] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [0, 0, -4] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [0, 0, -3] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [0, 0, -2] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [0, 0, -1] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [0, 0, 0] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [0, 0, 1] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [0, 0, 2] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [0, 0, 3] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [0, 0, 4] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [0, 0, 5] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [0, 0, 6] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [0, 0, 7] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [1, 2] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_32 : subd6_0 [2] = true := by decide +kernel
theorem sbd6_0_1 : ∀ q ∈ blkd6_0_1, subd6_0 q = true := by
  unfold blkd6_0_1
  exact List.forall_mem_cons.2 ⟨subd6_0_32, List.forall_mem_nil _⟩
theorem subd6_1_0 : subd6_1 [-1] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [0] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [1] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_nil _⟩⟩⟩
theorem subd7_0_0 : subd7_0 [-2] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [2] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_0 : subd7_1 [-1] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [0] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [1] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_nil _⟩⟩⟩
theorem subd8_0_0 : subd8_0 [-3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-1, -4] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [-1, 3] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [0, -4] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [0, 3] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, -4] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_22 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_23 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_24 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_25 : subd8_0 [1, 3] = true := by decide +kernel
theorem subd8_0_26 : subd8_0 [2] = true := by decide +kernel
theorem subd8_0_27 : subd8_0 [3] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_cons.2 ⟨subd8_0_22, List.forall_mem_cons.2 ⟨subd8_0_23, List.forall_mem_cons.2 ⟨subd8_0_24, List.forall_mem_cons.2 ⟨subd8_0_25, List.forall_mem_cons.2 ⟨subd8_0_26, List.forall_mem_cons.2 ⟨subd8_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_0 : subd8_1 [] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_nil _⟩
theorem subd9_0_0 : subd9_0 [] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_nil _⟩
theorem subd9_1_0 : subd9_1 [] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_nil _⟩
theorem subd10_0_0 : subd10_0 [-1] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [0] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [1] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_nil _⟩⟩⟩
theorem subd10_1_0 : subd10_1 [] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C119
