import ReflectZphi.Data.Cert5.C071.Base

namespace ReflectZphi.Data.Cert5.C071
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-2] = true := by decide +kernel
theorem sub0_1 : sub0 [-1, -3] = true := by decide +kernel
theorem sub0_2 : sub0 [-1, -2] = true := by decide +kernel
theorem sub0_3 : sub0 [-1, -1] = true := by decide +kernel
theorem sub0_4 : sub0 [-1, 0] = true := by decide +kernel
theorem sub0_5 : sub0 [-1, 1] = true := by decide +kernel
theorem sub0_6 : sub0 [-1, 2] = true := by decide +kernel
theorem sub0_7 : sub0 [-1, 3] = true := by decide +kernel
theorem sub0_8 : sub0 [0, -4] = true := by decide +kernel
theorem sub0_9 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_10 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_11 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_12 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_13 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_14 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_15 : sub0 [0, 3] = true := by decide +kernel
theorem sub0_16 : sub0 [1, -4] = true := by decide +kernel
theorem sub0_17 : sub0 [1, -3] = true := by decide +kernel
theorem sub0_18 : sub0 [1, -2] = true := by decide +kernel
theorem sub0_19 : sub0 [1, -1] = true := by decide +kernel
theorem sub0_20 : sub0 [1, 0] = true := by decide +kernel
theorem sub0_21 : sub0 [1, 1] = true := by decide +kernel
theorem sub0_22 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_23 : sub0 [2] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_cons.2 ⟨sub0_12, List.forall_mem_cons.2 ⟨sub0_13, List.forall_mem_cons.2 ⟨sub0_14, List.forall_mem_cons.2 ⟨sub0_15, List.forall_mem_cons.2 ⟨sub0_16, List.forall_mem_cons.2 ⟨sub0_17, List.forall_mem_cons.2 ⟨sub0_18, List.forall_mem_cons.2 ⟨sub0_19, List.forall_mem_cons.2 ⟨sub0_20, List.forall_mem_cons.2 ⟨sub0_21, List.forall_mem_cons.2 ⟨sub0_22, List.forall_mem_cons.2 ⟨sub0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-3] = true := by decide +kernel
theorem sub1_1 : sub1 [-2, -5] = true := by decide +kernel
theorem sub1_2 : sub1 [-2, -4] = true := by decide +kernel
theorem sub1_3 : sub1 [-2, -3] = true := by decide +kernel
theorem sub1_4 : sub1 [-2, -2] = true := by decide +kernel
theorem sub1_5 : sub1 [-2, -1] = true := by decide +kernel
theorem sub1_6 : sub1 [-2, 0] = true := by decide +kernel
theorem sub1_7 : sub1 [-2, 1] = true := by decide +kernel
theorem sub1_8 : sub1 [-2, 2] = true := by decide +kernel
theorem sub1_9 : sub1 [-1, -5] = true := by decide +kernel
theorem sub1_10 : sub1 [-1, -4] = true := by decide +kernel
theorem sub1_11 : sub1 [-1, -3] = true := by decide +kernel
theorem sub1_12 : sub1 [-1, -2] = true := by decide +kernel
theorem sub1_13 : sub1 [-1, -1] = true := by decide +kernel
theorem sub1_14 : sub1 [-1, 0] = true := by decide +kernel
theorem sub1_15 : sub1 [-1, 1] = true := by decide +kernel
theorem sub1_16 : sub1 [-1, 2] = true := by decide +kernel
theorem sub1_17 : sub1 [-1, 3] = true := by decide +kernel
theorem sub1_18 : sub1 [0, -5] = true := by decide +kernel
theorem sub1_19 : sub1 [0, -4] = true := by decide +kernel
theorem sub1_20 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_21 : sub1 [0, -2] = true := by decide +kernel
theorem sub1_22 : sub1 [0, -1] = true := by decide +kernel
theorem sub1_23 : sub1 [0, 0] = true := by decide +kernel
theorem sub1_24 : sub1 [0, 1] = true := by decide +kernel
theorem sub1_25 : sub1 [0, 2] = true := by decide +kernel
theorem sub1_26 : sub1 [0, 3] = true := by decide +kernel
theorem sub1_27 : sub1 [0, 4] = true := by decide +kernel
theorem sub1_28 : sub1 [1, -4] = true := by decide +kernel
theorem sub1_29 : sub1 [1, -3] = true := by decide +kernel
theorem sub1_30 : sub1 [1, -2] = true := by decide +kernel
theorem sub1_31 : sub1 [1, -1] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_cons.2 ⟨sub1_18, List.forall_mem_cons.2 ⟨sub1_19, List.forall_mem_cons.2 ⟨sub1_20, List.forall_mem_cons.2 ⟨sub1_21, List.forall_mem_cons.2 ⟨sub1_22, List.forall_mem_cons.2 ⟨sub1_23, List.forall_mem_cons.2 ⟨sub1_24, List.forall_mem_cons.2 ⟨sub1_25, List.forall_mem_cons.2 ⟨sub1_26, List.forall_mem_cons.2 ⟨sub1_27, List.forall_mem_cons.2 ⟨sub1_28, List.forall_mem_cons.2 ⟨sub1_29, List.forall_mem_cons.2 ⟨sub1_30, List.forall_mem_cons.2 ⟨sub1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_32 : sub1 [1, 0] = true := by decide +kernel
theorem sub1_33 : sub1 [1, 1] = true := by decide +kernel
theorem sub1_34 : sub1 [1, 2] = true := by decide +kernel
theorem sub1_35 : sub1 [1, 3] = true := by decide +kernel
theorem sub1_36 : sub1 [1, 4] = true := by decide +kernel
theorem sub1_37 : sub1 [2, -3] = true := by decide +kernel
theorem sub1_38 : sub1 [2, -2] = true := by decide +kernel
theorem sub1_39 : sub1 [2, -1] = true := by decide +kernel
theorem sub1_40 : sub1 [2, 0] = true := by decide +kernel
theorem sub1_41 : sub1 [2, 1] = true := by decide +kernel
theorem sub1_42 : sub1 [2, 2] = true := by decide +kernel
theorem sub1_43 : sub1 [2, 3] = true := by decide +kernel
theorem sub1_44 : sub1 [2, 4] = true := by decide +kernel
theorem sub1_45 : sub1 [3] = true := by decide +kernel
theorem sb1_1 : ∀ q ∈ blk1_1, sub1 q = true := by
  unfold blk1_1
  exact List.forall_mem_cons.2 ⟨sub1_32, List.forall_mem_cons.2 ⟨sub1_33, List.forall_mem_cons.2 ⟨sub1_34, List.forall_mem_cons.2 ⟨sub1_35, List.forall_mem_cons.2 ⟨sub1_36, List.forall_mem_cons.2 ⟨sub1_37, List.forall_mem_cons.2 ⟨sub1_38, List.forall_mem_cons.2 ⟨sub1_39, List.forall_mem_cons.2 ⟨sub1_40, List.forall_mem_cons.2 ⟨sub1_41, List.forall_mem_cons.2 ⟨sub1_42, List.forall_mem_cons.2 ⟨sub1_43, List.forall_mem_cons.2 ⟨sub1_44, List.forall_mem_cons.2 ⟨sub1_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_0 : sub2 [-2] = true := by decide +kernel
theorem sub2_1 : sub2 [-1] = true := by decide +kernel
theorem sub2_2 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_3 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_4 : sub2 [0, -1] = true := by decide +kernel
theorem sub2_5 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_6 : sub2 [0, 1] = true := by decide +kernel
theorem sub2_7 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_8 : sub2 [1] = true := by decide +kernel
theorem sub2_9 : sub2 [2] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-5] = true := by decide +kernel
theorem sub3_1 : sub3 [-4] = true := by decide +kernel
theorem sub3_2 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_3 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_4 : sub3 [-3, -1] = true := by decide +kernel
theorem sub3_5 : sub3 [-3, 0] = true := by decide +kernel
theorem sub3_6 : sub3 [-3, 1] = true := by decide +kernel
theorem sub3_7 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_8 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_9 : sub3 [-3, 4] = true := by decide +kernel
theorem sub3_10 : sub3 [-3, 5] = true := by decide +kernel
theorem sub3_11 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_12 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_13 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_14 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_15 : sub3 [-2, 0] = true := by decide +kernel
theorem sub3_16 : sub3 [-2, 1] = true := by decide +kernel
theorem sub3_17 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_18 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_19 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_20 : sub3 [-2, 5] = true := by decide +kernel
theorem sub3_21 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_22 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_23 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_24 : sub3 [-1, -2] = true := by decide +kernel
theorem sub3_25 : sub3 [-1, -1] = true := by decide +kernel
theorem sub3_26 : sub3 [-1, 0] = true := by decide +kernel
theorem sub3_27 : sub3 [-1, 1] = true := by decide +kernel
theorem sub3_28 : sub3 [-1, 2] = true := by decide +kernel
theorem sub3_29 : sub3 [-1, 3] = true := by decide +kernel
theorem sub3_30 : sub3 [-1, 4] = true := by decide +kernel
theorem sub3_31 : sub3 [0, -5] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_33 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_34 : sub3 [0, -2] = true := by decide +kernel
theorem sub3_35 : sub3 [0, -1] = true := by decide +kernel
theorem sub3_36 : sub3 [0, 0] = true := by decide +kernel
theorem sub3_37 : sub3 [0, 1] = true := by decide +kernel
theorem sub3_38 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_39 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_40 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_41 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_42 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_43 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_44 : sub3 [1, -2] = true := by decide +kernel
theorem sub3_45 : sub3 [1, -1] = true := by decide +kernel
theorem sub3_46 : sub3 [1, 0] = true := by decide +kernel
theorem sub3_47 : sub3 [1, 1] = true := by decide +kernel
theorem sub3_48 : sub3 [1, 2] = true := by decide +kernel
theorem sub3_49 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_50 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_51 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_52 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_53 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_54 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_55 : sub3 [2, -2] = true := by decide +kernel
theorem sub3_56 : sub3 [2, -1] = true := by decide +kernel
theorem sub3_57 : sub3 [2, 0] = true := by decide +kernel
theorem sub3_58 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_59 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_60 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_61 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_62 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_63 : sub3 [3, -4] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_65 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_66 : sub3 [3, -1] = true := by decide +kernel
theorem sub3_67 : sub3 [3, 0] = true := by decide +kernel
theorem sub3_68 : sub3 [3, 1] = true := by decide +kernel
theorem sub3_69 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_70 : sub3 [4] = true := by decide +kernel
theorem sub3_71 : sub3 [5] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-3] = true := by decide +kernel
theorem sub4_1 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_2 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_3 : sub4 [-2, -1] = true := by decide +kernel
theorem sub4_4 : sub4 [-2, 0] = true := by decide +kernel
theorem sub4_5 : sub4 [-2, 1] = true := by decide +kernel
theorem sub4_6 : sub4 [-2, 2] = true := by decide +kernel
theorem sub4_7 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_8 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_9 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_10 : sub4 [-1, -2] = true := by decide +kernel
theorem sub4_11 : sub4 [-1, -1] = true := by decide +kernel
theorem sub4_12 : sub4 [-1, 0] = true := by decide +kernel
theorem sub4_13 : sub4 [-1, 1] = true := by decide +kernel
theorem sub4_14 : sub4 [-1, 2] = true := by decide +kernel
theorem sub4_15 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_16 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_17 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_18 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_19 : sub4 [0, -2] = true := by decide +kernel
theorem sub4_20 : sub4 [0, -1] = true := by decide +kernel
theorem sub4_21 : sub4 [0, 0] = true := by decide +kernel
theorem sub4_22 : sub4 [0, 1] = true := by decide +kernel
theorem sub4_23 : sub4 [0, 2] = true := by decide +kernel
theorem sub4_24 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_25 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_26 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_27 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_28 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_29 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_30 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_31 : sub4 [1, 1] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C071
