import ReflectZphi.Data.Cert5.C056.Base

namespace ReflectZphi.Data.Cert5.C056
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-1] = true := by decide +kernel
theorem sub0_1 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_2 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_3 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_4 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_5 : sub0 [1] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-3] = true := by decide +kernel
theorem sub1_1 : sub1 [-2] = true := by decide +kernel
theorem sub1_2 : sub1 [-1, -4] = true := by decide +kernel
theorem sub1_3 : sub1 [-1, -3] = true := by decide +kernel
theorem sub1_4 : sub1 [-1, -2] = true := by decide +kernel
theorem sub1_5 : sub1 [-1, -1] = true := by decide +kernel
theorem sub1_6 : sub1 [-1, 0] = true := by decide +kernel
theorem sub1_7 : sub1 [-1, 1] = true := by decide +kernel
theorem sub1_8 : sub1 [-1, 2] = true := by decide +kernel
theorem sub1_9 : sub1 [-1, 3] = true := by decide +kernel
theorem sub1_10 : sub1 [0, -4] = true := by decide +kernel
theorem sub1_11 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_12 : sub1 [0, -2] = true := by decide +kernel
theorem sub1_13 : sub1 [0, -1] = true := by decide +kernel
theorem sub1_14 : sub1 [0, 0] = true := by decide +kernel
theorem sub1_15 : sub1 [0, 1] = true := by decide +kernel
theorem sub1_16 : sub1 [0, 2] = true := by decide +kernel
theorem sub1_17 : sub1 [0, 3] = true := by decide +kernel
theorem sub1_18 : sub1 [1, -4] = true := by decide +kernel
theorem sub1_19 : sub1 [1, -3] = true := by decide +kernel
theorem sub1_20 : sub1 [1, -2] = true := by decide +kernel
theorem sub1_21 : sub1 [1, -1] = true := by decide +kernel
theorem sub1_22 : sub1 [1, 0] = true := by decide +kernel
theorem sub1_23 : sub1 [1, 1] = true := by decide +kernel
theorem sub1_24 : sub1 [1, 2] = true := by decide +kernel
theorem sub1_25 : sub1 [1, 3] = true := by decide +kernel
theorem sub1_26 : sub1 [2] = true := by decide +kernel
theorem sub1_27 : sub1 [3] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_cons.2 ⟨sub1_18, List.forall_mem_cons.2 ⟨sub1_19, List.forall_mem_cons.2 ⟨sub1_20, List.forall_mem_cons.2 ⟨sub1_21, List.forall_mem_cons.2 ⟨sub1_22, List.forall_mem_cons.2 ⟨sub1_23, List.forall_mem_cons.2 ⟨sub1_24, List.forall_mem_cons.2 ⟨sub1_25, List.forall_mem_cons.2 ⟨sub1_26, List.forall_mem_cons.2 ⟨sub1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_0 : sub2 [-4] = true := by decide +kernel
theorem sub2_1 : sub2 [-3, -3] = true := by decide +kernel
theorem sub2_2 : sub2 [-3, -2] = true := by decide +kernel
theorem sub2_3 : sub2 [-3, -1] = true := by decide +kernel
theorem sub2_4 : sub2 [-3, 0] = true := by decide +kernel
theorem sub2_5 : sub2 [-3, 1] = true := by decide +kernel
theorem sub2_6 : sub2 [-3, 2] = true := by decide +kernel
theorem sub2_7 : sub2 [-3, 3] = true := by decide +kernel
theorem sub2_8 : sub2 [-2, -4] = true := by decide +kernel
theorem sub2_9 : sub2 [-2, -3] = true := by decide +kernel
theorem sub2_10 : sub2 [-2, -2] = true := by decide +kernel
theorem sub2_11 : sub2 [-2, -1] = true := by decide +kernel
theorem sub2_12 : sub2 [-2, 0] = true := by decide +kernel
theorem sub2_13 : sub2 [-2, 1] = true := by decide +kernel
theorem sub2_14 : sub2 [-2, 2] = true := by decide +kernel
theorem sub2_15 : sub2 [-2, 3] = true := by decide +kernel
theorem sub2_16 : sub2 [-1, -4] = true := by decide +kernel
theorem sub2_17 : sub2 [-1, -3] = true := by decide +kernel
theorem sub2_18 : sub2 [-1, -2] = true := by decide +kernel
theorem sub2_19 : sub2 [-1, -1] = true := by decide +kernel
theorem sub2_20 : sub2 [-1, 0] = true := by decide +kernel
theorem sub2_21 : sub2 [-1, 1] = true := by decide +kernel
theorem sub2_22 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_23 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_24 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_25 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_26 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_27 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_28 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_29 : sub2 [0, -1] = true := by decide +kernel
theorem sub2_30 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_31 : sub2 [0, 1] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_cons.2 ⟨sub2_10, List.forall_mem_cons.2 ⟨sub2_11, List.forall_mem_cons.2 ⟨sub2_12, List.forall_mem_cons.2 ⟨sub2_13, List.forall_mem_cons.2 ⟨sub2_14, List.forall_mem_cons.2 ⟨sub2_15, List.forall_mem_cons.2 ⟨sub2_16, List.forall_mem_cons.2 ⟨sub2_17, List.forall_mem_cons.2 ⟨sub2_18, List.forall_mem_cons.2 ⟨sub2_19, List.forall_mem_cons.2 ⟨sub2_20, List.forall_mem_cons.2 ⟨sub2_21, List.forall_mem_cons.2 ⟨sub2_22, List.forall_mem_cons.2 ⟨sub2_23, List.forall_mem_cons.2 ⟨sub2_24, List.forall_mem_cons.2 ⟨sub2_25, List.forall_mem_cons.2 ⟨sub2_26, List.forall_mem_cons.2 ⟨sub2_27, List.forall_mem_cons.2 ⟨sub2_28, List.forall_mem_cons.2 ⟨sub2_29, List.forall_mem_cons.2 ⟨sub2_30, List.forall_mem_cons.2 ⟨sub2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_32 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_33 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_34 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_35 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_36 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_37 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_38 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_39 : sub2 [1, -1] = true := by decide +kernel
theorem sub2_40 : sub2 [1, 0] = true := by decide +kernel
theorem sub2_41 : sub2 [1, 1] = true := by decide +kernel
theorem sub2_42 : sub2 [1, 2] = true := by decide +kernel
theorem sub2_43 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_44 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_45 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_46 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_47 : sub2 [2, -1] = true := by decide +kernel
theorem sub2_48 : sub2 [2, 0] = true := by decide +kernel
theorem sub2_49 : sub2 [2, 1] = true := by decide +kernel
theorem sub2_50 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_51 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_52 : sub2 [3, -4] = true := by decide +kernel
theorem sub2_53 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_54 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_55 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_56 : sub2 [3, 0] = true := by decide +kernel
theorem sub2_57 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_58 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_59 : sub2 [4] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-3] = true := by decide +kernel
theorem sub3_1 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_2 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_3 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_4 : sub3 [-2, 0] = true := by decide +kernel
theorem sub3_5 : sub3 [-2, 1] = true := by decide +kernel
theorem sub3_6 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_7 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_8 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_9 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_10 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_11 : sub3 [-1, -2] = true := by decide +kernel
theorem sub3_12 : sub3 [-1, -1] = true := by decide +kernel
theorem sub3_13 : sub3 [-1, 0] = true := by decide +kernel
theorem sub3_14 : sub3 [-1, 1] = true := by decide +kernel
theorem sub3_15 : sub3 [-1, 2] = true := by decide +kernel
theorem sub3_16 : sub3 [-1, 3] = true := by decide +kernel
theorem sub3_17 : sub3 [-1, 4] = true := by decide +kernel
theorem sub3_18 : sub3 [0, -5] = true := by decide +kernel
theorem sub3_19 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_20 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_21 : sub3 [0, -2] = true := by decide +kernel
theorem sub3_22 : sub3 [0, -1] = true := by decide +kernel
theorem sub3_23 : sub3 [0, 0] = true := by decide +kernel
theorem sub3_24 : sub3 [0, 1] = true := by decide +kernel
theorem sub3_25 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_26 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_27 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_28 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_29 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_30 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_31 : sub3 [1, -2] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [1, -1] = true := by decide +kernel
theorem sub3_33 : sub3 [1, 0] = true := by decide +kernel
theorem sub3_34 : sub3 [1, 1] = true := by decide +kernel
theorem sub3_35 : sub3 [1, 2] = true := by decide +kernel
theorem sub3_36 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_37 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_38 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_39 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_40 : sub3 [2, -2] = true := by decide +kernel
theorem sub3_41 : sub3 [2, -1] = true := by decide +kernel
theorem sub3_42 : sub3 [2, 0] = true := by decide +kernel
theorem sub3_43 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_44 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_45 : sub3 [3] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-5] = true := by decide +kernel
theorem sub4_1 : sub4 [-4, -4] = true := by decide +kernel
theorem sub4_2 : sub4 [-4, -3] = true := by decide +kernel
theorem sub4_3 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_4 : sub4 [-4, -1] = true := by decide +kernel
theorem sub4_5 : sub4 [-4, 0] = true := by decide +kernel
theorem sub4_6 : sub4 [-4, 1] = true := by decide +kernel
theorem sub4_7 : sub4 [-4, 2] = true := by decide +kernel
theorem sub4_8 : sub4 [-3, -5] = true := by decide +kernel
theorem sub4_9 : sub4 [-3, -4] = true := by decide +kernel
theorem sub4_10 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_11 : sub4 [-3, -2] = true := by decide +kernel
theorem sub4_12 : sub4 [-3, -1] = true := by decide +kernel
theorem sub4_13 : sub4 [-3, 0] = true := by decide +kernel
theorem sub4_14 : sub4 [-3, 1] = true := by decide +kernel
theorem sub4_15 : sub4 [-3, 2] = true := by decide +kernel
theorem sub4_16 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_17 : sub4 [-2, -5] = true := by decide +kernel
theorem sub4_18 : sub4 [-2, -4] = true := by decide +kernel
theorem sub4_19 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_20 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_21 : sub4 [-2, -1, -7] = true := by decide +kernel
theorem sub4_22 : sub4 [-2, -1, -6] = true := by decide +kernel
theorem sub4_23 : sub4 [-2, -1, -5] = true := by decide +kernel
theorem sub4_24 : sub4 [-2, -1, -4] = true := by decide +kernel
theorem sub4_25 : sub4 [-2, -1, -3] = true := by decide +kernel
theorem sub4_26 : sub4 [-2, -1, -2] = true := by decide +kernel
theorem sub4_27 : sub4 [-2, -1, -1] = true := by decide +kernel
theorem sub4_28 : sub4 [-2, -1, 0] = true := by decide +kernel
theorem sub4_29 : sub4 [-2, -1, 1] = true := by decide +kernel
theorem sub4_30 : sub4 [-2, -1, 2] = true := by decide +kernel
theorem sub4_31 : sub4 [-2, -1, 3] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-2, -1, 4] = true := by decide +kernel
theorem sub4_33 : sub4 [-2, -1, 5] = true := by decide +kernel
theorem sub4_34 : sub4 [-2, 0, -7] = true := by decide +kernel
theorem sub4_35 : sub4 [-2, 0, -6] = true := by decide +kernel
theorem sub4_36 : sub4 [-2, 0, -5] = true := by decide +kernel
theorem sub4_37 : sub4 [-2, 0, -4] = true := by decide +kernel
theorem sub4_38 : sub4 [-2, 0, -3] = true := by decide +kernel
theorem sub4_39 : sub4 [-2, 0, -2] = true := by decide +kernel
theorem sub4_40 : sub4 [-2, 0, -1] = true := by decide +kernel
theorem sub4_41 : sub4 [-2, 0, 0] = true := by decide +kernel
theorem sub4_42 : sub4 [-2, 0, 1] = true := by decide +kernel
theorem sub4_43 : sub4 [-2, 0, 2] = true := by decide +kernel
theorem sub4_44 : sub4 [-2, 0, 3] = true := by decide +kernel
theorem sub4_45 : sub4 [-2, 0, 4] = true := by decide +kernel
theorem sub4_46 : sub4 [-2, 0, 5] = true := by decide +kernel
theorem sub4_47 : sub4 [-2, 0, 6] = true := by decide +kernel
theorem sub4_48 : sub4 [-2, 1, -7] = true := by decide +kernel
theorem sub4_49 : sub4 [-2, 1, -6] = true := by decide +kernel
theorem sub4_50 : sub4 [-2, 1, -5] = true := by decide +kernel
theorem sub4_51 : sub4 [-2, 1, -4] = true := by decide +kernel
theorem sub4_52 : sub4 [-2, 1, -3] = true := by decide +kernel
theorem sub4_53 : sub4 [-2, 1, -2] = true := by decide +kernel
theorem sub4_54 : sub4 [-2, 1, -1] = true := by decide +kernel
theorem sub4_55 : sub4 [-2, 1, 0] = true := by decide +kernel
theorem sub4_56 : sub4 [-2, 1, 1] = true := by decide +kernel
theorem sub4_57 : sub4 [-2, 1, 2] = true := by decide +kernel
theorem sub4_58 : sub4 [-2, 1, 3] = true := by decide +kernel
theorem sub4_59 : sub4 [-2, 1, 4] = true := by decide +kernel
theorem sub4_60 : sub4 [-2, 1, 5] = true := by decide +kernel
theorem sub4_61 : sub4 [-2, 1, 6] = true := by decide +kernel
theorem sub4_62 : sub4 [-2, 2] = true := by decide +kernel
theorem sub4_63 : sub4 [-2, 3] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C056
