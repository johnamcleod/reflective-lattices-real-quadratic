import ReflectZphi.Data.Cert5.C091.Base

namespace ReflectZphi.Data.Cert5.C091

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_5_0 : subd4_5 [-4] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [-3] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [-2, -3] = true := by decide +kernel
theorem subd4_5_3 : subd4_5 [-2, -2] = true := by decide +kernel
theorem subd4_5_4 : subd4_5 [-2, -1] = true := by decide +kernel
theorem subd4_5_5 : subd4_5 [-2, 0] = true := by decide +kernel
theorem subd4_5_6 : subd4_5 [-2, 1] = true := by decide +kernel
theorem subd4_5_7 : subd4_5 [-2, 2] = true := by decide +kernel
theorem subd4_5_8 : subd4_5 [-2, 3] = true := by decide +kernel
theorem subd4_5_9 : subd4_5 [-1, -4] = true := by decide +kernel
theorem subd4_5_10 : subd4_5 [-1, -3] = true := by decide +kernel
theorem subd4_5_11 : subd4_5 [-1, -2] = true := by decide +kernel
theorem subd4_5_12 : subd4_5 [-1, -1] = true := by decide +kernel
theorem subd4_5_13 : subd4_5 [-1, 0] = true := by decide +kernel
theorem subd4_5_14 : subd4_5 [-1, 1] = true := by decide +kernel
theorem subd4_5_15 : subd4_5 [-1, 2] = true := by decide +kernel
theorem subd4_5_16 : subd4_5 [-1, 3] = true := by decide +kernel
theorem subd4_5_17 : subd4_5 [0, -4] = true := by decide +kernel
theorem subd4_5_18 : subd4_5 [0, -3] = true := by decide +kernel
theorem subd4_5_19 : subd4_5 [0, -2] = true := by decide +kernel
theorem subd4_5_20 : subd4_5 [0, -1] = true := by decide +kernel
theorem subd4_5_21 : subd4_5 [0, 0] = true := by decide +kernel
theorem subd4_5_22 : subd4_5 [0, 1] = true := by decide +kernel
theorem subd4_5_23 : subd4_5 [0, 2] = true := by decide +kernel
theorem subd4_5_24 : subd4_5 [0, 3] = true := by decide +kernel
theorem subd4_5_25 : subd4_5 [1, -4] = true := by decide +kernel
theorem subd4_5_26 : subd4_5 [1, -3] = true := by decide +kernel
theorem subd4_5_27 : subd4_5 [1, -2] = true := by decide +kernel
theorem subd4_5_28 : subd4_5 [1, -1] = true := by decide +kernel
theorem subd4_5_29 : subd4_5 [1, 0] = true := by decide +kernel
theorem subd4_5_30 : subd4_5 [1, 1] = true := by decide +kernel
theorem subd4_5_31 : subd4_5 [1, 2] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_cons.2 ⟨subd4_5_3, List.forall_mem_cons.2 ⟨subd4_5_4, List.forall_mem_cons.2 ⟨subd4_5_5, List.forall_mem_cons.2 ⟨subd4_5_6, List.forall_mem_cons.2 ⟨subd4_5_7, List.forall_mem_cons.2 ⟨subd4_5_8, List.forall_mem_cons.2 ⟨subd4_5_9, List.forall_mem_cons.2 ⟨subd4_5_10, List.forall_mem_cons.2 ⟨subd4_5_11, List.forall_mem_cons.2 ⟨subd4_5_12, List.forall_mem_cons.2 ⟨subd4_5_13, List.forall_mem_cons.2 ⟨subd4_5_14, List.forall_mem_cons.2 ⟨subd4_5_15, List.forall_mem_cons.2 ⟨subd4_5_16, List.forall_mem_cons.2 ⟨subd4_5_17, List.forall_mem_cons.2 ⟨subd4_5_18, List.forall_mem_cons.2 ⟨subd4_5_19, List.forall_mem_cons.2 ⟨subd4_5_20, List.forall_mem_cons.2 ⟨subd4_5_21, List.forall_mem_cons.2 ⟨subd4_5_22, List.forall_mem_cons.2 ⟨subd4_5_23, List.forall_mem_cons.2 ⟨subd4_5_24, List.forall_mem_cons.2 ⟨subd4_5_25, List.forall_mem_cons.2 ⟨subd4_5_26, List.forall_mem_cons.2 ⟨subd4_5_27, List.forall_mem_cons.2 ⟨subd4_5_28, List.forall_mem_cons.2 ⟨subd4_5_29, List.forall_mem_cons.2 ⟨subd4_5_30, List.forall_mem_cons.2 ⟨subd4_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_32 : subd4_5 [1, 3] = true := by decide +kernel
theorem subd4_5_33 : subd4_5 [2, -4] = true := by decide +kernel
theorem subd4_5_34 : subd4_5 [2, -3] = true := by decide +kernel
theorem subd4_5_35 : subd4_5 [2, -2] = true := by decide +kernel
theorem subd4_5_36 : subd4_5 [2, -1] = true := by decide +kernel
theorem subd4_5_37 : subd4_5 [2, 0] = true := by decide +kernel
theorem subd4_5_38 : subd4_5 [2, 1] = true := by decide +kernel
theorem subd4_5_39 : subd4_5 [2, 2] = true := by decide +kernel
theorem subd4_5_40 : subd4_5 [3] = true := by decide +kernel
theorem subd4_5_41 : subd4_5 [4] = true := by decide +kernel
theorem sbd4_5_1 : ∀ q ∈ blkd4_5_1, subd4_5 q = true := by
  unfold blkd4_5_1
  exact List.forall_mem_cons.2 ⟨subd4_5_32, List.forall_mem_cons.2 ⟨subd4_5_33, List.forall_mem_cons.2 ⟨subd4_5_34, List.forall_mem_cons.2 ⟨subd4_5_35, List.forall_mem_cons.2 ⟨subd4_5_36, List.forall_mem_cons.2 ⟨subd4_5_37, List.forall_mem_cons.2 ⟨subd4_5_38, List.forall_mem_cons.2 ⟨subd4_5_39, List.forall_mem_cons.2 ⟨subd4_5_40, List.forall_mem_cons.2 ⟨subd4_5_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_0 : subd4_6 [-3] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-2, -3] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [-2, -2] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [-2, -1] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [-2, 0] = true := by decide +kernel
theorem subd4_6_5 : subd4_6 [-2, 1] = true := by decide +kernel
theorem subd4_6_6 : subd4_6 [-2, 2] = true := by decide +kernel
theorem subd4_6_7 : subd4_6 [-2, 3] = true := by decide +kernel
theorem subd4_6_8 : subd4_6 [-2, 4] = true := by decide +kernel
theorem subd4_6_9 : subd4_6 [-1, -4] = true := by decide +kernel
theorem subd4_6_10 : subd4_6 [-1, -3] = true := by decide +kernel
theorem subd4_6_11 : subd4_6 [-1, -2] = true := by decide +kernel
theorem subd4_6_12 : subd4_6 [-1, -1] = true := by decide +kernel
theorem subd4_6_13 : subd4_6 [-1, 0] = true := by decide +kernel
theorem subd4_6_14 : subd4_6 [-1, 1] = true := by decide +kernel
theorem subd4_6_15 : subd4_6 [-1, 2] = true := by decide +kernel
theorem subd4_6_16 : subd4_6 [-1, 3] = true := by decide +kernel
theorem subd4_6_17 : subd4_6 [-1, 4] = true := by decide +kernel
theorem subd4_6_18 : subd4_6 [0, -5] = true := by decide +kernel
theorem subd4_6_19 : subd4_6 [0, -4] = true := by decide +kernel
theorem subd4_6_20 : subd4_6 [0, -3] = true := by decide +kernel
theorem subd4_6_21 : subd4_6 [0, -2] = true := by decide +kernel
theorem subd4_6_22 : subd4_6 [0, -1] = true := by decide +kernel
theorem subd4_6_23 : subd4_6 [0, 0] = true := by decide +kernel
theorem subd4_6_24 : subd4_6 [0, 1] = true := by decide +kernel
theorem subd4_6_25 : subd4_6 [0, 2] = true := by decide +kernel
theorem subd4_6_26 : subd4_6 [0, 3] = true := by decide +kernel
theorem subd4_6_27 : subd4_6 [0, 4] = true := by decide +kernel
theorem subd4_6_28 : subd4_6 [1, -5] = true := by decide +kernel
theorem subd4_6_29 : subd4_6 [1, -4] = true := by decide +kernel
theorem subd4_6_30 : subd4_6 [1, -3] = true := by decide +kernel
theorem subd4_6_31 : subd4_6 [1, -2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_cons.2 ⟨subd4_6_5, List.forall_mem_cons.2 ⟨subd4_6_6, List.forall_mem_cons.2 ⟨subd4_6_7, List.forall_mem_cons.2 ⟨subd4_6_8, List.forall_mem_cons.2 ⟨subd4_6_9, List.forall_mem_cons.2 ⟨subd4_6_10, List.forall_mem_cons.2 ⟨subd4_6_11, List.forall_mem_cons.2 ⟨subd4_6_12, List.forall_mem_cons.2 ⟨subd4_6_13, List.forall_mem_cons.2 ⟨subd4_6_14, List.forall_mem_cons.2 ⟨subd4_6_15, List.forall_mem_cons.2 ⟨subd4_6_16, List.forall_mem_cons.2 ⟨subd4_6_17, List.forall_mem_cons.2 ⟨subd4_6_18, List.forall_mem_cons.2 ⟨subd4_6_19, List.forall_mem_cons.2 ⟨subd4_6_20, List.forall_mem_cons.2 ⟨subd4_6_21, List.forall_mem_cons.2 ⟨subd4_6_22, List.forall_mem_cons.2 ⟨subd4_6_23, List.forall_mem_cons.2 ⟨subd4_6_24, List.forall_mem_cons.2 ⟨subd4_6_25, List.forall_mem_cons.2 ⟨subd4_6_26, List.forall_mem_cons.2 ⟨subd4_6_27, List.forall_mem_cons.2 ⟨subd4_6_28, List.forall_mem_cons.2 ⟨subd4_6_29, List.forall_mem_cons.2 ⟨subd4_6_30, List.forall_mem_cons.2 ⟨subd4_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_32 : subd4_6 [1, -1] = true := by decide +kernel
theorem subd4_6_33 : subd4_6 [1, 0] = true := by decide +kernel
theorem subd4_6_34 : subd4_6 [1, 1] = true := by decide +kernel
theorem subd4_6_35 : subd4_6 [1, 2] = true := by decide +kernel
theorem subd4_6_36 : subd4_6 [1, 3] = true := by decide +kernel
theorem subd4_6_37 : subd4_6 [2, -5] = true := by decide +kernel
theorem subd4_6_38 : subd4_6 [2, -4] = true := by decide +kernel
theorem subd4_6_39 : subd4_6 [2, -3] = true := by decide +kernel
theorem subd4_6_40 : subd4_6 [2, -2] = true := by decide +kernel
theorem subd4_6_41 : subd4_6 [2, -1] = true := by decide +kernel
theorem subd4_6_42 : subd4_6 [2, 0] = true := by decide +kernel
theorem subd4_6_43 : subd4_6 [2, 1] = true := by decide +kernel
theorem subd4_6_44 : subd4_6 [2, 2] = true := by decide +kernel
theorem subd4_6_45 : subd4_6 [3] = true := by decide +kernel
theorem sbd4_6_1 : ∀ q ∈ blkd4_6_1, subd4_6 q = true := by
  unfold blkd4_6_1
  exact List.forall_mem_cons.2 ⟨subd4_6_32, List.forall_mem_cons.2 ⟨subd4_6_33, List.forall_mem_cons.2 ⟨subd4_6_34, List.forall_mem_cons.2 ⟨subd4_6_35, List.forall_mem_cons.2 ⟨subd4_6_36, List.forall_mem_cons.2 ⟨subd4_6_37, List.forall_mem_cons.2 ⟨subd4_6_38, List.forall_mem_cons.2 ⟨subd4_6_39, List.forall_mem_cons.2 ⟨subd4_6_40, List.forall_mem_cons.2 ⟨subd4_6_41, List.forall_mem_cons.2 ⟨subd4_6_42, List.forall_mem_cons.2 ⟨subd4_6_43, List.forall_mem_cons.2 ⟨subd4_6_44, List.forall_mem_cons.2 ⟨subd4_6_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_0 : subd4_7 [-1, -1] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1, 0, -14] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [-1, 0, -13] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [-1, 0, -12] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [-1, 0, -11] = true := by decide +kernel
theorem subd4_7_5 : subd4_7 [-1, 0, -10] = true := by decide +kernel
theorem subd4_7_6 : subd4_7 [-1, 0, -9] = true := by decide +kernel
theorem subd4_7_7 : subd4_7 [-1, 0, -8] = true := by decide +kernel
theorem subd4_7_8 : subd4_7 [-1, 0, -7] = true := by decide +kernel
theorem subd4_7_9 : subd4_7 [-1, 0, -6] = true := by decide +kernel
theorem subd4_7_10 : subd4_7 [-1, 0, -5] = true := by decide +kernel
theorem subd4_7_11 : subd4_7 [-1, 0, -4] = true := by decide +kernel
theorem subd4_7_12 : subd4_7 [-1, 0, -3] = true := by decide +kernel
theorem subd4_7_13 : subd4_7 [-1, 0, -2] = true := by decide +kernel
theorem subd4_7_14 : subd4_7 [-1, 0, -1] = true := by decide +kernel
theorem subd4_7_15 : subd4_7 [-1, 0, 0] = true := by decide +kernel
theorem subd4_7_16 : subd4_7 [-1, 0, 1] = true := by decide +kernel
theorem subd4_7_17 : subd4_7 [-1, 0, 2] = true := by decide +kernel
theorem subd4_7_18 : subd4_7 [-1, 0, 3] = true := by decide +kernel
theorem subd4_7_19 : subd4_7 [-1, 0, 4] = true := by decide +kernel
theorem subd4_7_20 : subd4_7 [-1, 0, 5] = true := by decide +kernel
theorem subd4_7_21 : subd4_7 [-1, 0, 6] = true := by decide +kernel
theorem subd4_7_22 : subd4_7 [-1, 0, 7] = true := by decide +kernel
theorem subd4_7_23 : subd4_7 [-1, 0, 8] = true := by decide +kernel
theorem subd4_7_24 : subd4_7 [-1, 0, 9] = true := by decide +kernel
theorem subd4_7_25 : subd4_7 [-1, 0, 10] = true := by decide +kernel
theorem subd4_7_26 : subd4_7 [-1, 0, 11] = true := by decide +kernel
theorem subd4_7_27 : subd4_7 [-1, 0, 12] = true := by decide +kernel
theorem subd4_7_28 : subd4_7 [-1, 0, 13] = true := by decide +kernel
theorem subd4_7_29 : subd4_7 [-1, 1, -13] = true := by decide +kernel
theorem subd4_7_30 : subd4_7 [-1, 1, -12] = true := by decide +kernel
theorem subd4_7_31 : subd4_7 [-1, 1, -11] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_cons.2 ⟨subd4_7_5, List.forall_mem_cons.2 ⟨subd4_7_6, List.forall_mem_cons.2 ⟨subd4_7_7, List.forall_mem_cons.2 ⟨subd4_7_8, List.forall_mem_cons.2 ⟨subd4_7_9, List.forall_mem_cons.2 ⟨subd4_7_10, List.forall_mem_cons.2 ⟨subd4_7_11, List.forall_mem_cons.2 ⟨subd4_7_12, List.forall_mem_cons.2 ⟨subd4_7_13, List.forall_mem_cons.2 ⟨subd4_7_14, List.forall_mem_cons.2 ⟨subd4_7_15, List.forall_mem_cons.2 ⟨subd4_7_16, List.forall_mem_cons.2 ⟨subd4_7_17, List.forall_mem_cons.2 ⟨subd4_7_18, List.forall_mem_cons.2 ⟨subd4_7_19, List.forall_mem_cons.2 ⟨subd4_7_20, List.forall_mem_cons.2 ⟨subd4_7_21, List.forall_mem_cons.2 ⟨subd4_7_22, List.forall_mem_cons.2 ⟨subd4_7_23, List.forall_mem_cons.2 ⟨subd4_7_24, List.forall_mem_cons.2 ⟨subd4_7_25, List.forall_mem_cons.2 ⟨subd4_7_26, List.forall_mem_cons.2 ⟨subd4_7_27, List.forall_mem_cons.2 ⟨subd4_7_28, List.forall_mem_cons.2 ⟨subd4_7_29, List.forall_mem_cons.2 ⟨subd4_7_30, List.forall_mem_cons.2 ⟨subd4_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_32 : subd4_7 [-1, 1, -10] = true := by decide +kernel
theorem subd4_7_33 : subd4_7 [-1, 1, -9] = true := by decide +kernel
theorem subd4_7_34 : subd4_7 [-1, 1, -8] = true := by decide +kernel
theorem subd4_7_35 : subd4_7 [-1, 1, -7] = true := by decide +kernel
theorem subd4_7_36 : subd4_7 [-1, 1, -6] = true := by decide +kernel
theorem subd4_7_37 : subd4_7 [-1, 1, -5] = true := by decide +kernel
theorem subd4_7_38 : subd4_7 [-1, 1, -4] = true := by decide +kernel
theorem subd4_7_39 : subd4_7 [-1, 1, -3] = true := by decide +kernel
theorem subd4_7_40 : subd4_7 [-1, 1, -2] = true := by decide +kernel
theorem subd4_7_41 : subd4_7 [-1, 1, -1] = true := by decide +kernel
theorem subd4_7_42 : subd4_7 [-1, 1, 0] = true := by decide +kernel
theorem subd4_7_43 : subd4_7 [-1, 1, 1] = true := by decide +kernel
theorem subd4_7_44 : subd4_7 [-1, 1, 2] = true := by decide +kernel
theorem subd4_7_45 : subd4_7 [-1, 1, 3] = true := by decide +kernel
theorem subd4_7_46 : subd4_7 [-1, 1, 4] = true := by decide +kernel
theorem subd4_7_47 : subd4_7 [-1, 1, 5] = true := by decide +kernel
theorem subd4_7_48 : subd4_7 [-1, 1, 6] = true := by decide +kernel
theorem subd4_7_49 : subd4_7 [-1, 1, 7] = true := by decide +kernel
theorem subd4_7_50 : subd4_7 [-1, 1, 8] = true := by decide +kernel
theorem subd4_7_51 : subd4_7 [-1, 1, 9] = true := by decide +kernel
theorem subd4_7_52 : subd4_7 [-1, 1, 10] = true := by decide +kernel
theorem subd4_7_53 : subd4_7 [-1, 1, 11] = true := by decide +kernel
theorem subd4_7_54 : subd4_7 [-1, 1, 12] = true := by decide +kernel
theorem subd4_7_55 : subd4_7 [0, -2] = true := by decide +kernel
theorem subd4_7_56 : subd4_7 [0, -1, -15] = true := by decide +kernel
theorem subd4_7_57 : subd4_7 [0, -1, -14] = true := by decide +kernel
theorem subd4_7_58 : subd4_7 [0, -1, -13] = true := by decide +kernel
theorem subd4_7_59 : subd4_7 [0, -1, -12] = true := by decide +kernel
theorem subd4_7_60 : subd4_7 [0, -1, -11] = true := by decide +kernel
theorem subd4_7_61 : subd4_7 [0, -1, -10] = true := by decide +kernel
theorem subd4_7_62 : subd4_7 [0, -1, -9] = true := by decide +kernel
theorem subd4_7_63 : subd4_7 [0, -1, -8] = true := by decide +kernel
theorem sbd4_7_1 : ∀ q ∈ blkd4_7_1, subd4_7 q = true := by
  unfold blkd4_7_1
  exact List.forall_mem_cons.2 ⟨subd4_7_32, List.forall_mem_cons.2 ⟨subd4_7_33, List.forall_mem_cons.2 ⟨subd4_7_34, List.forall_mem_cons.2 ⟨subd4_7_35, List.forall_mem_cons.2 ⟨subd4_7_36, List.forall_mem_cons.2 ⟨subd4_7_37, List.forall_mem_cons.2 ⟨subd4_7_38, List.forall_mem_cons.2 ⟨subd4_7_39, List.forall_mem_cons.2 ⟨subd4_7_40, List.forall_mem_cons.2 ⟨subd4_7_41, List.forall_mem_cons.2 ⟨subd4_7_42, List.forall_mem_cons.2 ⟨subd4_7_43, List.forall_mem_cons.2 ⟨subd4_7_44, List.forall_mem_cons.2 ⟨subd4_7_45, List.forall_mem_cons.2 ⟨subd4_7_46, List.forall_mem_cons.2 ⟨subd4_7_47, List.forall_mem_cons.2 ⟨subd4_7_48, List.forall_mem_cons.2 ⟨subd4_7_49, List.forall_mem_cons.2 ⟨subd4_7_50, List.forall_mem_cons.2 ⟨subd4_7_51, List.forall_mem_cons.2 ⟨subd4_7_52, List.forall_mem_cons.2 ⟨subd4_7_53, List.forall_mem_cons.2 ⟨subd4_7_54, List.forall_mem_cons.2 ⟨subd4_7_55, List.forall_mem_cons.2 ⟨subd4_7_56, List.forall_mem_cons.2 ⟨subd4_7_57, List.forall_mem_cons.2 ⟨subd4_7_58, List.forall_mem_cons.2 ⟨subd4_7_59, List.forall_mem_cons.2 ⟨subd4_7_60, List.forall_mem_cons.2 ⟨subd4_7_61, List.forall_mem_cons.2 ⟨subd4_7_62, List.forall_mem_cons.2 ⟨subd4_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_64 : subd4_7 [0, -1, -7] = true := by decide +kernel
theorem subd4_7_65 : subd4_7 [0, -1, -6] = true := by decide +kernel
theorem subd4_7_66 : subd4_7 [0, -1, -5] = true := by decide +kernel
theorem subd4_7_67 : subd4_7 [0, -1, -4] = true := by decide +kernel
theorem subd4_7_68 : subd4_7 [0, -1, -3] = true := by decide +kernel
theorem subd4_7_69 : subd4_7 [0, -1, -2] = true := by decide +kernel
theorem subd4_7_70 : subd4_7 [0, -1, -1] = true := by decide +kernel
theorem subd4_7_71 : subd4_7 [0, -1, 0] = true := by decide +kernel
theorem subd4_7_72 : subd4_7 [0, -1, 1] = true := by decide +kernel
theorem subd4_7_73 : subd4_7 [0, -1, 2] = true := by decide +kernel
theorem subd4_7_74 : subd4_7 [0, -1, 3] = true := by decide +kernel
theorem subd4_7_75 : subd4_7 [0, -1, 4] = true := by decide +kernel
theorem subd4_7_76 : subd4_7 [0, -1, 5] = true := by decide +kernel
theorem subd4_7_77 : subd4_7 [0, -1, 6] = true := by decide +kernel
theorem subd4_7_78 : subd4_7 [0, -1, 7] = true := by decide +kernel
theorem subd4_7_79 : subd4_7 [0, -1, 8] = true := by decide +kernel
theorem subd4_7_80 : subd4_7 [0, -1, 9] = true := by decide +kernel
theorem subd4_7_81 : subd4_7 [0, -1, 10] = true := by decide +kernel
theorem subd4_7_82 : subd4_7 [0, -1, 11] = true := by decide +kernel
theorem subd4_7_83 : subd4_7 [0, -1, 12] = true := by decide +kernel
theorem subd4_7_84 : subd4_7 [0, -1, 13] = true := by decide +kernel
theorem subd4_7_85 : subd4_7 [0, -1, 14] = true := by decide +kernel
theorem subd4_7_86 : subd4_7 [0, -1, 15] = true := by decide +kernel
theorem subd4_7_87 : subd4_7 [0, 0, -19] = true := by decide +kernel
theorem subd4_7_88 : subd4_7 [0, 0, -18] = true := by decide +kernel
theorem subd4_7_89 : subd4_7 [0, 0, -17] = true := by decide +kernel
theorem subd4_7_90 : subd4_7 [0, 0, -16] = true := by decide +kernel
theorem subd4_7_91 : subd4_7 [0, 0, -15] = true := by decide +kernel
theorem subd4_7_92 : subd4_7 [0, 0, -14] = true := by decide +kernel
theorem subd4_7_93 : subd4_7 [0, 0, -13] = true := by decide +kernel
theorem subd4_7_94 : subd4_7 [0, 0, -12] = true := by decide +kernel
theorem subd4_7_95 : subd4_7 [0, 0, -11] = true := by decide +kernel
theorem sbd4_7_2 : ∀ q ∈ blkd4_7_2, subd4_7 q = true := by
  unfold blkd4_7_2
  exact List.forall_mem_cons.2 ⟨subd4_7_64, List.forall_mem_cons.2 ⟨subd4_7_65, List.forall_mem_cons.2 ⟨subd4_7_66, List.forall_mem_cons.2 ⟨subd4_7_67, List.forall_mem_cons.2 ⟨subd4_7_68, List.forall_mem_cons.2 ⟨subd4_7_69, List.forall_mem_cons.2 ⟨subd4_7_70, List.forall_mem_cons.2 ⟨subd4_7_71, List.forall_mem_cons.2 ⟨subd4_7_72, List.forall_mem_cons.2 ⟨subd4_7_73, List.forall_mem_cons.2 ⟨subd4_7_74, List.forall_mem_cons.2 ⟨subd4_7_75, List.forall_mem_cons.2 ⟨subd4_7_76, List.forall_mem_cons.2 ⟨subd4_7_77, List.forall_mem_cons.2 ⟨subd4_7_78, List.forall_mem_cons.2 ⟨subd4_7_79, List.forall_mem_cons.2 ⟨subd4_7_80, List.forall_mem_cons.2 ⟨subd4_7_81, List.forall_mem_cons.2 ⟨subd4_7_82, List.forall_mem_cons.2 ⟨subd4_7_83, List.forall_mem_cons.2 ⟨subd4_7_84, List.forall_mem_cons.2 ⟨subd4_7_85, List.forall_mem_cons.2 ⟨subd4_7_86, List.forall_mem_cons.2 ⟨subd4_7_87, List.forall_mem_cons.2 ⟨subd4_7_88, List.forall_mem_cons.2 ⟨subd4_7_89, List.forall_mem_cons.2 ⟨subd4_7_90, List.forall_mem_cons.2 ⟨subd4_7_91, List.forall_mem_cons.2 ⟨subd4_7_92, List.forall_mem_cons.2 ⟨subd4_7_93, List.forall_mem_cons.2 ⟨subd4_7_94, List.forall_mem_cons.2 ⟨subd4_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_96 : subd4_7 [0, 0, -10] = true := by decide +kernel
theorem subd4_7_97 : subd4_7 [0, 0, -9] = true := by decide +kernel
theorem subd4_7_98 : subd4_7 [0, 0, -8] = true := by decide +kernel
theorem subd4_7_99 : subd4_7 [0, 0, -7] = true := by decide +kernel
theorem subd4_7_100 : subd4_7 [0, 0, -6] = true := by decide +kernel
theorem subd4_7_101 : subd4_7 [0, 0, -5] = true := by decide +kernel
theorem subd4_7_102 : subd4_7 [0, 0, -4] = true := by decide +kernel
theorem subd4_7_103 : subd4_7 [0, 0, -3] = true := by decide +kernel
theorem subd4_7_104 : subd4_7 [0, 0, -2] = true := by decide +kernel
theorem subd4_7_105 : subd4_7 [0, 0, -1] = true := by decide +kernel
theorem subd4_7_106 : subd4_7 [0, 0, 0] = true := by decide +kernel
theorem subd4_7_107 : subd4_7 [0, 0, 1] = true := by decide +kernel
theorem subd4_7_108 : subd4_7 [0, 0, 2] = true := by decide +kernel
theorem subd4_7_109 : subd4_7 [0, 0, 3] = true := by decide +kernel
theorem subd4_7_110 : subd4_7 [0, 0, 4] = true := by decide +kernel
theorem subd4_7_111 : subd4_7 [0, 0, 5] = true := by decide +kernel
theorem subd4_7_112 : subd4_7 [0, 0, 6] = true := by decide +kernel
theorem subd4_7_113 : subd4_7 [0, 0, 7] = true := by decide +kernel
theorem subd4_7_114 : subd4_7 [0, 0, 8] = true := by decide +kernel
theorem subd4_7_115 : subd4_7 [0, 0, 9] = true := by decide +kernel
theorem subd4_7_116 : subd4_7 [0, 0, 10] = true := by decide +kernel
theorem subd4_7_117 : subd4_7 [0, 0, 11] = true := by decide +kernel
theorem subd4_7_118 : subd4_7 [0, 0, 12] = true := by decide +kernel
theorem subd4_7_119 : subd4_7 [0, 0, 13] = true := by decide +kernel
theorem subd4_7_120 : subd4_7 [0, 0, 14] = true := by decide +kernel
theorem subd4_7_121 : subd4_7 [0, 0, 15] = true := by decide +kernel
theorem subd4_7_122 : subd4_7 [0, 0, 16] = true := by decide +kernel
theorem subd4_7_123 : subd4_7 [0, 0, 17] = true := by decide +kernel
theorem subd4_7_124 : subd4_7 [0, 0, 18] = true := by decide +kernel
theorem subd4_7_125 : subd4_7 [0, 1, -16] = true := by decide +kernel
theorem subd4_7_126 : subd4_7 [0, 1, -15] = true := by decide +kernel
theorem subd4_7_127 : subd4_7 [0, 1, -14] = true := by decide +kernel
theorem sbd4_7_3 : ∀ q ∈ blkd4_7_3, subd4_7 q = true := by
  unfold blkd4_7_3
  exact List.forall_mem_cons.2 ⟨subd4_7_96, List.forall_mem_cons.2 ⟨subd4_7_97, List.forall_mem_cons.2 ⟨subd4_7_98, List.forall_mem_cons.2 ⟨subd4_7_99, List.forall_mem_cons.2 ⟨subd4_7_100, List.forall_mem_cons.2 ⟨subd4_7_101, List.forall_mem_cons.2 ⟨subd4_7_102, List.forall_mem_cons.2 ⟨subd4_7_103, List.forall_mem_cons.2 ⟨subd4_7_104, List.forall_mem_cons.2 ⟨subd4_7_105, List.forall_mem_cons.2 ⟨subd4_7_106, List.forall_mem_cons.2 ⟨subd4_7_107, List.forall_mem_cons.2 ⟨subd4_7_108, List.forall_mem_cons.2 ⟨subd4_7_109, List.forall_mem_cons.2 ⟨subd4_7_110, List.forall_mem_cons.2 ⟨subd4_7_111, List.forall_mem_cons.2 ⟨subd4_7_112, List.forall_mem_cons.2 ⟨subd4_7_113, List.forall_mem_cons.2 ⟨subd4_7_114, List.forall_mem_cons.2 ⟨subd4_7_115, List.forall_mem_cons.2 ⟨subd4_7_116, List.forall_mem_cons.2 ⟨subd4_7_117, List.forall_mem_cons.2 ⟨subd4_7_118, List.forall_mem_cons.2 ⟨subd4_7_119, List.forall_mem_cons.2 ⟨subd4_7_120, List.forall_mem_cons.2 ⟨subd4_7_121, List.forall_mem_cons.2 ⟨subd4_7_122, List.forall_mem_cons.2 ⟨subd4_7_123, List.forall_mem_cons.2 ⟨subd4_7_124, List.forall_mem_cons.2 ⟨subd4_7_125, List.forall_mem_cons.2 ⟨subd4_7_126, List.forall_mem_cons.2 ⟨subd4_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_128 : subd4_7 [0, 1, -13] = true := by decide +kernel
theorem subd4_7_129 : subd4_7 [0, 1, -12] = true := by decide +kernel
theorem subd4_7_130 : subd4_7 [0, 1, -11] = true := by decide +kernel
theorem subd4_7_131 : subd4_7 [0, 1, -10] = true := by decide +kernel
theorem subd4_7_132 : subd4_7 [0, 1, -9] = true := by decide +kernel
theorem subd4_7_133 : subd4_7 [0, 1, -8] = true := by decide +kernel
theorem subd4_7_134 : subd4_7 [0, 1, -7] = true := by decide +kernel
theorem subd4_7_135 : subd4_7 [0, 1, -6] = true := by decide +kernel
theorem subd4_7_136 : subd4_7 [0, 1, -5] = true := by decide +kernel
theorem subd4_7_137 : subd4_7 [0, 1, -4] = true := by decide +kernel
theorem subd4_7_138 : subd4_7 [0, 1, -3] = true := by decide +kernel
theorem subd4_7_139 : subd4_7 [0, 1, -2] = true := by decide +kernel
theorem subd4_7_140 : subd4_7 [0, 1, -1] = true := by decide +kernel
theorem subd4_7_141 : subd4_7 [0, 1, 0] = true := by decide +kernel
theorem subd4_7_142 : subd4_7 [0, 1, 1] = true := by decide +kernel
theorem subd4_7_143 : subd4_7 [0, 1, 2] = true := by decide +kernel
theorem subd4_7_144 : subd4_7 [0, 1, 3] = true := by decide +kernel
theorem subd4_7_145 : subd4_7 [0, 1, 4] = true := by decide +kernel
theorem subd4_7_146 : subd4_7 [0, 1, 5] = true := by decide +kernel
theorem subd4_7_147 : subd4_7 [0, 1, 6] = true := by decide +kernel
theorem subd4_7_148 : subd4_7 [0, 1, 7] = true := by decide +kernel
theorem subd4_7_149 : subd4_7 [0, 1, 8] = true := by decide +kernel
theorem subd4_7_150 : subd4_7 [0, 1, 9] = true := by decide +kernel
theorem subd4_7_151 : subd4_7 [0, 1, 10] = true := by decide +kernel
theorem subd4_7_152 : subd4_7 [0, 1, 11] = true := by decide +kernel
theorem subd4_7_153 : subd4_7 [0, 1, 12] = true := by decide +kernel
theorem subd4_7_154 : subd4_7 [0, 1, 13] = true := by decide +kernel
theorem subd4_7_155 : subd4_7 [0, 1, 14] = true := by decide +kernel
theorem subd4_7_156 : subd4_7 [1, -2] = true := by decide +kernel
theorem subd4_7_157 : subd4_7 [1, -1, -13] = true := by decide +kernel
theorem subd4_7_158 : subd4_7 [1, -1, -12] = true := by decide +kernel
theorem subd4_7_159 : subd4_7 [1, -1, -11] = true := by decide +kernel
theorem sbd4_7_4 : ∀ q ∈ blkd4_7_4, subd4_7 q = true := by
  unfold blkd4_7_4
  exact List.forall_mem_cons.2 ⟨subd4_7_128, List.forall_mem_cons.2 ⟨subd4_7_129, List.forall_mem_cons.2 ⟨subd4_7_130, List.forall_mem_cons.2 ⟨subd4_7_131, List.forall_mem_cons.2 ⟨subd4_7_132, List.forall_mem_cons.2 ⟨subd4_7_133, List.forall_mem_cons.2 ⟨subd4_7_134, List.forall_mem_cons.2 ⟨subd4_7_135, List.forall_mem_cons.2 ⟨subd4_7_136, List.forall_mem_cons.2 ⟨subd4_7_137, List.forall_mem_cons.2 ⟨subd4_7_138, List.forall_mem_cons.2 ⟨subd4_7_139, List.forall_mem_cons.2 ⟨subd4_7_140, List.forall_mem_cons.2 ⟨subd4_7_141, List.forall_mem_cons.2 ⟨subd4_7_142, List.forall_mem_cons.2 ⟨subd4_7_143, List.forall_mem_cons.2 ⟨subd4_7_144, List.forall_mem_cons.2 ⟨subd4_7_145, List.forall_mem_cons.2 ⟨subd4_7_146, List.forall_mem_cons.2 ⟨subd4_7_147, List.forall_mem_cons.2 ⟨subd4_7_148, List.forall_mem_cons.2 ⟨subd4_7_149, List.forall_mem_cons.2 ⟨subd4_7_150, List.forall_mem_cons.2 ⟨subd4_7_151, List.forall_mem_cons.2 ⟨subd4_7_152, List.forall_mem_cons.2 ⟨subd4_7_153, List.forall_mem_cons.2 ⟨subd4_7_154, List.forall_mem_cons.2 ⟨subd4_7_155, List.forall_mem_cons.2 ⟨subd4_7_156, List.forall_mem_cons.2 ⟨subd4_7_157, List.forall_mem_cons.2 ⟨subd4_7_158, List.forall_mem_cons.2 ⟨subd4_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C091
