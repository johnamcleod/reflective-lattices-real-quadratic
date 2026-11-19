import ReflectZphi.Data.Cert5.C055.Base

namespace ReflectZphi.Data.Cert5.C055
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-2] = true := by decide +kernel
theorem sub0_1 : sub0 [-1, -4] = true := by decide +kernel
theorem sub0_2 : sub0 [-1, -3] = true := by decide +kernel
theorem sub0_3 : sub0 [-1, -2] = true := by decide +kernel
theorem sub0_4 : sub0 [-1, -1] = true := by decide +kernel
theorem sub0_5 : sub0 [-1, 0] = true := by decide +kernel
theorem sub0_6 : sub0 [-1, 1] = true := by decide +kernel
theorem sub0_7 : sub0 [-1, 2] = true := by decide +kernel
theorem sub0_8 : sub0 [0, -4] = true := by decide +kernel
theorem sub0_9 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_10 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_11 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_12 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_13 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_14 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_15 : sub0 [0, 3] = true := by decide +kernel
theorem sub0_16 : sub0 [1, -3] = true := by decide +kernel
theorem sub0_17 : sub0 [1, -2] = true := by decide +kernel
theorem sub0_18 : sub0 [1, -1] = true := by decide +kernel
theorem sub0_19 : sub0 [1, 0] = true := by decide +kernel
theorem sub0_20 : sub0 [1, 1] = true := by decide +kernel
theorem sub0_21 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_22 : sub0 [1, 3] = true := by decide +kernel
theorem sub0_23 : sub0 [2] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_cons.2 ⟨sub0_12, List.forall_mem_cons.2 ⟨sub0_13, List.forall_mem_cons.2 ⟨sub0_14, List.forall_mem_cons.2 ⟨sub0_15, List.forall_mem_cons.2 ⟨sub0_16, List.forall_mem_cons.2 ⟨sub0_17, List.forall_mem_cons.2 ⟨sub0_18, List.forall_mem_cons.2 ⟨sub0_19, List.forall_mem_cons.2 ⟨sub0_20, List.forall_mem_cons.2 ⟨sub0_21, List.forall_mem_cons.2 ⟨sub0_22, List.forall_mem_cons.2 ⟨sub0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem sub2_0 : sub2 [-3] = true := by decide +kernel
theorem sub2_1 : sub2 [-2, -4] = true := by decide +kernel
theorem sub2_2 : sub2 [-2, -3] = true := by decide +kernel
theorem sub2_3 : sub2 [-2, -2] = true := by decide +kernel
theorem sub2_4 : sub2 [-2, -1] = true := by decide +kernel
theorem sub2_5 : sub2 [-2, 0] = true := by decide +kernel
theorem sub2_6 : sub2 [-2, 1] = true := by decide +kernel
theorem sub2_7 : sub2 [-2, 2] = true := by decide +kernel
theorem sub2_8 : sub2 [-1, -5] = true := by decide +kernel
theorem sub2_9 : sub2 [-1, -4] = true := by decide +kernel
theorem sub2_10 : sub2 [-1, -3] = true := by decide +kernel
theorem sub2_11 : sub2 [-1, -2] = true := by decide +kernel
theorem sub2_12 : sub2 [-1, -1] = true := by decide +kernel
theorem sub2_13 : sub2 [-1, 0] = true := by decide +kernel
theorem sub2_14 : sub2 [-1, 1] = true := by decide +kernel
theorem sub2_15 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_16 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_17 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_18 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_19 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_20 : sub2 [0, -1] = true := by decide +kernel
theorem sub2_21 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_22 : sub2 [0, 1] = true := by decide +kernel
theorem sub2_23 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_24 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_25 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_26 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_27 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_28 : sub2 [1, -1] = true := by decide +kernel
theorem sub2_29 : sub2 [1, 0] = true := by decide +kernel
theorem sub2_30 : sub2 [1, 1] = true := by decide +kernel
theorem sub2_31 : sub2 [1, 2] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_cons.2 ⟨sub2_10, List.forall_mem_cons.2 ⟨sub2_11, List.forall_mem_cons.2 ⟨sub2_12, List.forall_mem_cons.2 ⟨sub2_13, List.forall_mem_cons.2 ⟨sub2_14, List.forall_mem_cons.2 ⟨sub2_15, List.forall_mem_cons.2 ⟨sub2_16, List.forall_mem_cons.2 ⟨sub2_17, List.forall_mem_cons.2 ⟨sub2_18, List.forall_mem_cons.2 ⟨sub2_19, List.forall_mem_cons.2 ⟨sub2_20, List.forall_mem_cons.2 ⟨sub2_21, List.forall_mem_cons.2 ⟨sub2_22, List.forall_mem_cons.2 ⟨sub2_23, List.forall_mem_cons.2 ⟨sub2_24, List.forall_mem_cons.2 ⟨sub2_25, List.forall_mem_cons.2 ⟨sub2_26, List.forall_mem_cons.2 ⟨sub2_27, List.forall_mem_cons.2 ⟨sub2_28, List.forall_mem_cons.2 ⟨sub2_29, List.forall_mem_cons.2 ⟨sub2_30, List.forall_mem_cons.2 ⟨sub2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_32 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_33 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_34 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_35 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_36 : sub2 [2, -1] = true := by decide +kernel
theorem sub2_37 : sub2 [2, 0] = true := by decide +kernel
theorem sub2_38 : sub2 [2, 1] = true := by decide +kernel
theorem sub2_39 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_40 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_41 : sub2 [3] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-5] = true := by decide +kernel
theorem sub3_1 : sub3 [-4, -4] = true := by decide +kernel
theorem sub3_2 : sub3 [-4, -3] = true := by decide +kernel
theorem sub3_3 : sub3 [-4, -2] = true := by decide +kernel
theorem sub3_4 : sub3 [-4, -1] = true := by decide +kernel
theorem sub3_5 : sub3 [-4, 0] = true := by decide +kernel
theorem sub3_6 : sub3 [-4, 1] = true := by decide +kernel
theorem sub3_7 : sub3 [-4, 2] = true := by decide +kernel
theorem sub3_8 : sub3 [-3, -5] = true := by decide +kernel
theorem sub3_9 : sub3 [-3, -4] = true := by decide +kernel
theorem sub3_10 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_11 : sub3 [-3, -2, -7] = true := by decide +kernel
theorem sub3_12 : sub3 [-3, -2, -6] = true := by decide +kernel
theorem sub3_13 : sub3 [-3, -2, -5] = true := by decide +kernel
theorem sub3_14 : sub3 [-3, -2, -4] = true := by decide +kernel
theorem sub3_15 : sub3 [-3, -2, -3] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, -2, -2] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, -2, -1] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, -2, 0] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, -2, 1] = true := by decide +kernel
theorem sub3_20 : sub3 [-3, -2, 2] = true := by decide +kernel
theorem sub3_21 : sub3 [-3, -2, 3] = true := by decide +kernel
theorem sub3_22 : sub3 [-3, -2, 4] = true := by decide +kernel
theorem sub3_23 : sub3 [-3, -2, 5] = true := by decide +kernel
theorem sub3_24 : sub3 [-3, -2, 6] = true := by decide +kernel
theorem sub3_25 : sub3 [-3, -1, -8] = true := by decide +kernel
theorem sub3_26 : sub3 [-3, -1, -7] = true := by decide +kernel
theorem sub3_27 : sub3 [-3, -1, -6] = true := by decide +kernel
theorem sub3_28 : sub3 [-3, -1, -5] = true := by decide +kernel
theorem sub3_29 : sub3 [-3, -1, -4] = true := by decide +kernel
theorem sub3_30 : sub3 [-3, -1, -3] = true := by decide +kernel
theorem sub3_31 : sub3 [-3, -1, -2] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-3, -1, -1] = true := by decide +kernel
theorem sub3_33 : sub3 [-3, -1, 0] = true := by decide +kernel
theorem sub3_34 : sub3 [-3, -1, 1] = true := by decide +kernel
theorem sub3_35 : sub3 [-3, -1, 2] = true := by decide +kernel
theorem sub3_36 : sub3 [-3, -1, 3] = true := by decide +kernel
theorem sub3_37 : sub3 [-3, -1, 4] = true := by decide +kernel
theorem sub3_38 : sub3 [-3, -1, 5] = true := by decide +kernel
theorem sub3_39 : sub3 [-3, -1, 6] = true := by decide +kernel
theorem sub3_40 : sub3 [-3, 0, -8] = true := by decide +kernel
theorem sub3_41 : sub3 [-3, 0, -7] = true := by decide +kernel
theorem sub3_42 : sub3 [-3, 0, -6] = true := by decide +kernel
theorem sub3_43 : sub3 [-3, 0, -5] = true := by decide +kernel
theorem sub3_44 : sub3 [-3, 0, -4] = true := by decide +kernel
theorem sub3_45 : sub3 [-3, 0, -3] = true := by decide +kernel
theorem sub3_46 : sub3 [-3, 0, -2] = true := by decide +kernel
theorem sub3_47 : sub3 [-3, 0, -1] = true := by decide +kernel
theorem sub3_48 : sub3 [-3, 0, 0] = true := by decide +kernel
theorem sub3_49 : sub3 [-3, 0, 1] = true := by decide +kernel
theorem sub3_50 : sub3 [-3, 0, 2] = true := by decide +kernel
theorem sub3_51 : sub3 [-3, 0, 3] = true := by decide +kernel
theorem sub3_52 : sub3 [-3, 0, 4] = true := by decide +kernel
theorem sub3_53 : sub3 [-3, 0, 5] = true := by decide +kernel
theorem sub3_54 : sub3 [-3, 0, 6] = true := by decide +kernel
theorem sub3_55 : sub3 [-3, 1, -8] = true := by decide +kernel
theorem sub3_56 : sub3 [-3, 1, -7] = true := by decide +kernel
theorem sub3_57 : sub3 [-3, 1, -6] = true := by decide +kernel
theorem sub3_58 : sub3 [-3, 1, -5] = true := by decide +kernel
theorem sub3_59 : sub3 [-3, 1, -4] = true := by decide +kernel
theorem sub3_60 : sub3 [-3, 1, -3] = true := by decide +kernel
theorem sub3_61 : sub3 [-3, 1, -2] = true := by decide +kernel
theorem sub3_62 : sub3 [-3, 1, -1] = true := by decide +kernel
theorem sub3_63 : sub3 [-3, 1, 0] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [-3, 1, 1] = true := by decide +kernel
theorem sub3_65 : sub3 [-3, 1, 2] = true := by decide +kernel
theorem sub3_66 : sub3 [-3, 1, 3] = true := by decide +kernel
theorem sub3_67 : sub3 [-3, 1, 4] = true := by decide +kernel
theorem sub3_68 : sub3 [-3, 1, 5] = true := by decide +kernel
theorem sub3_69 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_70 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_71 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_72 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_73 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_74 : sub3 [-2, -2, -8] = true := by decide +kernel
theorem sub3_75 : sub3 [-2, -2, -7] = true := by decide +kernel
theorem sub3_76 : sub3 [-2, -2, -6] = true := by decide +kernel
theorem sub3_77 : sub3 [-2, -2, -5] = true := by decide +kernel
theorem sub3_78 : sub3 [-2, -2, -4] = true := by decide +kernel
theorem sub3_79 : sub3 [-2, -2, -3] = true := by decide +kernel
theorem sub3_80 : sub3 [-2, -2, -2] = true := by decide +kernel
theorem sub3_81 : sub3 [-2, -2, -1] = true := by decide +kernel
theorem sub3_82 : sub3 [-2, -2, 0] = true := by decide +kernel
theorem sub3_83 : sub3 [-2, -2, 1] = true := by decide +kernel
theorem sub3_84 : sub3 [-2, -2, 2] = true := by decide +kernel
theorem sub3_85 : sub3 [-2, -2, 3] = true := by decide +kernel
theorem sub3_86 : sub3 [-2, -2, 4] = true := by decide +kernel
theorem sub3_87 : sub3 [-2, -2, 5] = true := by decide +kernel
theorem sub3_88 : sub3 [-2, -2, 6] = true := by decide +kernel
theorem sub3_89 : sub3 [-2, -2, 7] = true := by decide +kernel
theorem sub3_90 : sub3 [-2, -1, -8] = true := by decide +kernel
theorem sub3_91 : sub3 [-2, -1, -7] = true := by decide +kernel
theorem sub3_92 : sub3 [-2, -1, -6] = true := by decide +kernel
theorem sub3_93 : sub3 [-2, -1, -5] = true := by decide +kernel
theorem sub3_94 : sub3 [-2, -1, -4] = true := by decide +kernel
theorem sub3_95 : sub3 [-2, -1, -3] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [-2, -1, -2] = true := by decide +kernel
theorem sub3_97 : sub3 [-2, -1, -1] = true := by decide +kernel
theorem sub3_98 : sub3 [-2, -1, 0] = true := by decide +kernel
theorem sub3_99 : sub3 [-2, -1, 1] = true := by decide +kernel
theorem sub3_100 : sub3 [-2, -1, 2] = true := by decide +kernel
theorem sub3_101 : sub3 [-2, -1, 3] = true := by decide +kernel
theorem sub3_102 : sub3 [-2, -1, 4] = true := by decide +kernel
theorem sub3_103 : sub3 [-2, -1, 5] = true := by decide +kernel
theorem sub3_104 : sub3 [-2, -1, 6] = true := by decide +kernel
theorem sub3_105 : sub3 [-2, -1, 7] = true := by decide +kernel
theorem sub3_106 : sub3 [-2, 0, -9] = true := by decide +kernel
theorem sub3_107 : sub3 [-2, 0, -8] = true := by decide +kernel
theorem sub3_108 : sub3 [-2, 0, -7] = true := by decide +kernel
theorem sub3_109 : sub3 [-2, 0, -6] = true := by decide +kernel
theorem sub3_110 : sub3 [-2, 0, -5] = true := by decide +kernel
theorem sub3_111 : sub3 [-2, 0, -4] = true := by decide +kernel
theorem sub3_112 : sub3 [-2, 0, -3] = true := by decide +kernel
theorem sub3_113 : sub3 [-2, 0, -2] = true := by decide +kernel
theorem sub3_114 : sub3 [-2, 0, -1] = true := by decide +kernel
theorem sub3_115 : sub3 [-2, 0, 0] = true := by decide +kernel
theorem sub3_116 : sub3 [-2, 0, 1] = true := by decide +kernel
theorem sub3_117 : sub3 [-2, 0, 2] = true := by decide +kernel
theorem sub3_118 : sub3 [-2, 0, 3] = true := by decide +kernel
theorem sub3_119 : sub3 [-2, 0, 4] = true := by decide +kernel
theorem sub3_120 : sub3 [-2, 0, 5] = true := by decide +kernel
theorem sub3_121 : sub3 [-2, 0, 6] = true := by decide +kernel
theorem sub3_122 : sub3 [-2, 0, 7] = true := by decide +kernel
theorem sub3_123 : sub3 [-2, 1, -9] = true := by decide +kernel
theorem sub3_124 : sub3 [-2, 1, -8] = true := by decide +kernel
theorem sub3_125 : sub3 [-2, 1, -7] = true := by decide +kernel
theorem sub3_126 : sub3 [-2, 1, -6] = true := by decide +kernel
theorem sub3_127 : sub3 [-2, 1, -5] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_128 : sub3 [-2, 1, -4] = true := by decide +kernel
theorem sub3_129 : sub3 [-2, 1, -3] = true := by decide +kernel
theorem sub3_130 : sub3 [-2, 1, -2] = true := by decide +kernel
theorem sub3_131 : sub3 [-2, 1, -1] = true := by decide +kernel
theorem sub3_132 : sub3 [-2, 1, 0] = true := by decide +kernel
theorem sub3_133 : sub3 [-2, 1, 1] = true := by decide +kernel
theorem sub3_134 : sub3 [-2, 1, 2] = true := by decide +kernel
theorem sub3_135 : sub3 [-2, 1, 3] = true := by decide +kernel
theorem sub3_136 : sub3 [-2, 1, 4] = true := by decide +kernel
theorem sub3_137 : sub3 [-2, 1, 5] = true := by decide +kernel
theorem sub3_138 : sub3 [-2, 1, 6] = true := by decide +kernel
theorem sub3_139 : sub3 [-2, 2, -8] = true := by decide +kernel
theorem sub3_140 : sub3 [-2, 2, -7] = true := by decide +kernel
theorem sub3_141 : sub3 [-2, 2, -6] = true := by decide +kernel
theorem sub3_142 : sub3 [-2, 2, -5] = true := by decide +kernel
theorem sub3_143 : sub3 [-2, 2, -4] = true := by decide +kernel
theorem sub3_144 : sub3 [-2, 2, -3] = true := by decide +kernel
theorem sub3_145 : sub3 [-2, 2, -2] = true := by decide +kernel
theorem sub3_146 : sub3 [-2, 2, -1] = true := by decide +kernel
theorem sub3_147 : sub3 [-2, 2, 0] = true := by decide +kernel
theorem sub3_148 : sub3 [-2, 2, 1] = true := by decide +kernel
theorem sub3_149 : sub3 [-2, 2, 2] = true := by decide +kernel
theorem sub3_150 : sub3 [-2, 2, 3] = true := by decide +kernel
theorem sub3_151 : sub3 [-2, 2, 4] = true := by decide +kernel
theorem sub3_152 : sub3 [-2, 2, 5] = true := by decide +kernel
theorem sub3_153 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_154 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_155 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_156 : sub3 [-1, -3, -7] = true := by decide +kernel
theorem sub3_157 : sub3 [-1, -3, -6] = true := by decide +kernel
theorem sub3_158 : sub3 [-1, -3, -5] = true := by decide +kernel
theorem sub3_159 : sub3 [-1, -3, -4] = true := by decide +kernel
theorem sb3_4 : ∀ q ∈ blk3_4, sub3 q = true := by
  unfold blk3_4
  exact List.forall_mem_cons.2 ⟨sub3_128, List.forall_mem_cons.2 ⟨sub3_129, List.forall_mem_cons.2 ⟨sub3_130, List.forall_mem_cons.2 ⟨sub3_131, List.forall_mem_cons.2 ⟨sub3_132, List.forall_mem_cons.2 ⟨sub3_133, List.forall_mem_cons.2 ⟨sub3_134, List.forall_mem_cons.2 ⟨sub3_135, List.forall_mem_cons.2 ⟨sub3_136, List.forall_mem_cons.2 ⟨sub3_137, List.forall_mem_cons.2 ⟨sub3_138, List.forall_mem_cons.2 ⟨sub3_139, List.forall_mem_cons.2 ⟨sub3_140, List.forall_mem_cons.2 ⟨sub3_141, List.forall_mem_cons.2 ⟨sub3_142, List.forall_mem_cons.2 ⟨sub3_143, List.forall_mem_cons.2 ⟨sub3_144, List.forall_mem_cons.2 ⟨sub3_145, List.forall_mem_cons.2 ⟨sub3_146, List.forall_mem_cons.2 ⟨sub3_147, List.forall_mem_cons.2 ⟨sub3_148, List.forall_mem_cons.2 ⟨sub3_149, List.forall_mem_cons.2 ⟨sub3_150, List.forall_mem_cons.2 ⟨sub3_151, List.forall_mem_cons.2 ⟨sub3_152, List.forall_mem_cons.2 ⟨sub3_153, List.forall_mem_cons.2 ⟨sub3_154, List.forall_mem_cons.2 ⟨sub3_155, List.forall_mem_cons.2 ⟨sub3_156, List.forall_mem_cons.2 ⟨sub3_157, List.forall_mem_cons.2 ⟨sub3_158, List.forall_mem_cons.2 ⟨sub3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_160 : sub3 [-1, -3, -3] = true := by decide +kernel
theorem sub3_161 : sub3 [-1, -3, -2] = true := by decide +kernel
theorem sub3_162 : sub3 [-1, -3, -1] = true := by decide +kernel
theorem sub3_163 : sub3 [-1, -3, 0] = true := by decide +kernel
theorem sub3_164 : sub3 [-1, -3, 1] = true := by decide +kernel
theorem sub3_165 : sub3 [-1, -3, 2] = true := by decide +kernel
theorem sub3_166 : sub3 [-1, -3, 3] = true := by decide +kernel
theorem sub3_167 : sub3 [-1, -3, 4] = true := by decide +kernel
theorem sub3_168 : sub3 [-1, -3, 5] = true := by decide +kernel
theorem sub3_169 : sub3 [-1, -3, 6] = true := by decide +kernel
theorem sub3_170 : sub3 [-1, -2, -8] = true := by decide +kernel
theorem sub3_171 : sub3 [-1, -2, -7] = true := by decide +kernel
theorem sub3_172 : sub3 [-1, -2, -6] = true := by decide +kernel
theorem sub3_173 : sub3 [-1, -2, -5] = true := by decide +kernel
theorem sub3_174 : sub3 [-1, -2, -4] = true := by decide +kernel
theorem sub3_175 : sub3 [-1, -2, -3] = true := by decide +kernel
theorem sub3_176 : sub3 [-1, -2, -2] = true := by decide +kernel
theorem sub3_177 : sub3 [-1, -2, -1] = true := by decide +kernel
theorem sub3_178 : sub3 [-1, -2, 0] = true := by decide +kernel
theorem sub3_179 : sub3 [-1, -2, 1] = true := by decide +kernel
theorem sub3_180 : sub3 [-1, -2, 2] = true := by decide +kernel
theorem sub3_181 : sub3 [-1, -2, 3] = true := by decide +kernel
theorem sub3_182 : sub3 [-1, -2, 4] = true := by decide +kernel
theorem sub3_183 : sub3 [-1, -2, 5] = true := by decide +kernel
theorem sub3_184 : sub3 [-1, -2, 6] = true := by decide +kernel
theorem sub3_185 : sub3 [-1, -2, 7] = true := by decide +kernel
theorem sub3_186 : sub3 [-1, -1, -9] = true := by decide +kernel
theorem sub3_187 : sub3 [-1, -1, -8] = true := by decide +kernel
theorem sub3_188 : sub3 [-1, -1, -7] = true := by decide +kernel
theorem sub3_189 : sub3 [-1, -1, -6] = true := by decide +kernel
theorem sub3_190 : sub3 [-1, -1, -5] = true := by decide +kernel
theorem sub3_191 : sub3 [-1, -1, -4] = true := by decide +kernel
theorem sb3_5 : ∀ q ∈ blk3_5, sub3 q = true := by
  unfold blk3_5
  exact List.forall_mem_cons.2 ⟨sub3_160, List.forall_mem_cons.2 ⟨sub3_161, List.forall_mem_cons.2 ⟨sub3_162, List.forall_mem_cons.2 ⟨sub3_163, List.forall_mem_cons.2 ⟨sub3_164, List.forall_mem_cons.2 ⟨sub3_165, List.forall_mem_cons.2 ⟨sub3_166, List.forall_mem_cons.2 ⟨sub3_167, List.forall_mem_cons.2 ⟨sub3_168, List.forall_mem_cons.2 ⟨sub3_169, List.forall_mem_cons.2 ⟨sub3_170, List.forall_mem_cons.2 ⟨sub3_171, List.forall_mem_cons.2 ⟨sub3_172, List.forall_mem_cons.2 ⟨sub3_173, List.forall_mem_cons.2 ⟨sub3_174, List.forall_mem_cons.2 ⟨sub3_175, List.forall_mem_cons.2 ⟨sub3_176, List.forall_mem_cons.2 ⟨sub3_177, List.forall_mem_cons.2 ⟨sub3_178, List.forall_mem_cons.2 ⟨sub3_179, List.forall_mem_cons.2 ⟨sub3_180, List.forall_mem_cons.2 ⟨sub3_181, List.forall_mem_cons.2 ⟨sub3_182, List.forall_mem_cons.2 ⟨sub3_183, List.forall_mem_cons.2 ⟨sub3_184, List.forall_mem_cons.2 ⟨sub3_185, List.forall_mem_cons.2 ⟨sub3_186, List.forall_mem_cons.2 ⟨sub3_187, List.forall_mem_cons.2 ⟨sub3_188, List.forall_mem_cons.2 ⟨sub3_189, List.forall_mem_cons.2 ⟨sub3_190, List.forall_mem_cons.2 ⟨sub3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_192 : sub3 [-1, -1, -3] = true := by decide +kernel
theorem sub3_193 : sub3 [-1, -1, -2] = true := by decide +kernel
theorem sub3_194 : sub3 [-1, -1, -1] = true := by decide +kernel
theorem sub3_195 : sub3 [-1, -1, 0] = true := by decide +kernel
theorem sub3_196 : sub3 [-1, -1, 1] = true := by decide +kernel
theorem sub3_197 : sub3 [-1, -1, 2] = true := by decide +kernel
theorem sub3_198 : sub3 [-1, -1, 3] = true := by decide +kernel
theorem sub3_199 : sub3 [-1, -1, 4] = true := by decide +kernel
theorem sub3_200 : sub3 [-1, -1, 5] = true := by decide +kernel
theorem sub3_201 : sub3 [-1, -1, 6] = true := by decide +kernel
theorem sub3_202 : sub3 [-1, -1, 7] = true := by decide +kernel
theorem sub3_203 : sub3 [-1, -1, 8] = true := by decide +kernel
theorem sub3_204 : sub3 [-1, 0, -9] = true := by decide +kernel
theorem sub3_205 : sub3 [-1, 0, -8] = true := by decide +kernel
theorem sub3_206 : sub3 [-1, 0, -7] = true := by decide +kernel
theorem sub3_207 : sub3 [-1, 0, -6] = true := by decide +kernel
theorem sub3_208 : sub3 [-1, 0, -5] = true := by decide +kernel
theorem sub3_209 : sub3 [-1, 0, -4] = true := by decide +kernel
theorem sub3_210 : sub3 [-1, 0, -3] = true := by decide +kernel
theorem sub3_211 : sub3 [-1, 0, -2] = true := by decide +kernel
theorem sub3_212 : sub3 [-1, 0, -1] = true := by decide +kernel
theorem sub3_213 : sub3 [-1, 0, 0] = true := by decide +kernel
theorem sub3_214 : sub3 [-1, 0, 1] = true := by decide +kernel
theorem sub3_215 : sub3 [-1, 0, 2] = true := by decide +kernel
theorem sub3_216 : sub3 [-1, 0, 3] = true := by decide +kernel
theorem sub3_217 : sub3 [-1, 0, 4] = true := by decide +kernel
theorem sub3_218 : sub3 [-1, 0, 5] = true := by decide +kernel
theorem sub3_219 : sub3 [-1, 0, 6] = true := by decide +kernel
theorem sub3_220 : sub3 [-1, 0, 7] = true := by decide +kernel
theorem sub3_221 : sub3 [-1, 0, 8] = true := by decide +kernel
theorem sub3_222 : sub3 [-1, 1, -9] = true := by decide +kernel
theorem sub3_223 : sub3 [-1, 1, -8] = true := by decide +kernel
theorem sb3_6 : ∀ q ∈ blk3_6, sub3 q = true := by
  unfold blk3_6
  exact List.forall_mem_cons.2 ⟨sub3_192, List.forall_mem_cons.2 ⟨sub3_193, List.forall_mem_cons.2 ⟨sub3_194, List.forall_mem_cons.2 ⟨sub3_195, List.forall_mem_cons.2 ⟨sub3_196, List.forall_mem_cons.2 ⟨sub3_197, List.forall_mem_cons.2 ⟨sub3_198, List.forall_mem_cons.2 ⟨sub3_199, List.forall_mem_cons.2 ⟨sub3_200, List.forall_mem_cons.2 ⟨sub3_201, List.forall_mem_cons.2 ⟨sub3_202, List.forall_mem_cons.2 ⟨sub3_203, List.forall_mem_cons.2 ⟨sub3_204, List.forall_mem_cons.2 ⟨sub3_205, List.forall_mem_cons.2 ⟨sub3_206, List.forall_mem_cons.2 ⟨sub3_207, List.forall_mem_cons.2 ⟨sub3_208, List.forall_mem_cons.2 ⟨sub3_209, List.forall_mem_cons.2 ⟨sub3_210, List.forall_mem_cons.2 ⟨sub3_211, List.forall_mem_cons.2 ⟨sub3_212, List.forall_mem_cons.2 ⟨sub3_213, List.forall_mem_cons.2 ⟨sub3_214, List.forall_mem_cons.2 ⟨sub3_215, List.forall_mem_cons.2 ⟨sub3_216, List.forall_mem_cons.2 ⟨sub3_217, List.forall_mem_cons.2 ⟨sub3_218, List.forall_mem_cons.2 ⟨sub3_219, List.forall_mem_cons.2 ⟨sub3_220, List.forall_mem_cons.2 ⟨sub3_221, List.forall_mem_cons.2 ⟨sub3_222, List.forall_mem_cons.2 ⟨sub3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C055
