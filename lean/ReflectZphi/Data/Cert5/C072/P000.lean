import ReflectZphi.Data.Cert5.C072.Base

namespace ReflectZphi.Data.Cert5.C072
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-2] = true := by decide +kernel
theorem sub0_1 : sub0 [-1, -3] = true := by decide +kernel
theorem sub0_2 : sub0 [-1, -2] = true := by decide +kernel
theorem sub0_3 : sub0 [-1, -1] = true := by decide +kernel
theorem sub0_4 : sub0 [-1, 0] = true := by decide +kernel
theorem sub0_5 : sub0 [-1, 1] = true := by decide +kernel
theorem sub0_6 : sub0 [-1, 2] = true := by decide +kernel
theorem sub0_7 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_8 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_9 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_10 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_11 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_12 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_13 : sub0 [1, -3] = true := by decide +kernel
theorem sub0_14 : sub0 [1, -2] = true := by decide +kernel
theorem sub0_15 : sub0 [1, -1] = true := by decide +kernel
theorem sub0_16 : sub0 [1, 0] = true := by decide +kernel
theorem sub0_17 : sub0 [1, 1] = true := by decide +kernel
theorem sub0_18 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_19 : sub0 [2] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_cons.2 ⟨sub0_12, List.forall_mem_cons.2 ⟨sub0_13, List.forall_mem_cons.2 ⟨sub0_14, List.forall_mem_cons.2 ⟨sub0_15, List.forall_mem_cons.2 ⟨sub0_16, List.forall_mem_cons.2 ⟨sub0_17, List.forall_mem_cons.2 ⟨sub0_18, List.forall_mem_cons.2 ⟨sub0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-2] = true := by decide +kernel
theorem sub1_1 : sub1 [-1] = true := by decide +kernel
theorem sub1_2 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_3 : sub1 [0, -2] = true := by decide +kernel
theorem sub1_4 : sub1 [0, -1] = true := by decide +kernel
theorem sub1_5 : sub1 [0, 0] = true := by decide +kernel
theorem sub1_6 : sub1 [0, 1] = true := by decide +kernel
theorem sub1_7 : sub1 [0, 2] = true := by decide +kernel
theorem sub1_8 : sub1 [1] = true := by decide +kernel
theorem sub1_9 : sub1 [2] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_0 : sub2 [-4] = true := by decide +kernel
theorem sub2_1 : sub2 [-3, -3] = true := by decide +kernel
theorem sub2_2 : sub2 [-3, -2] = true := by decide +kernel
theorem sub2_3 : sub2 [-3, -1] = true := by decide +kernel
theorem sub2_4 : sub2 [-3, 0] = true := by decide +kernel
theorem sub2_5 : sub2 [-3, 1] = true := by decide +kernel
theorem sub2_6 : sub2 [-3, 2] = true := by decide +kernel
theorem sub2_7 : sub2 [-3, 3] = true := by decide +kernel
theorem sub2_8 : sub2 [-3, 4] = true := by decide +kernel
theorem sub2_9 : sub2 [-2, -4] = true := by decide +kernel
theorem sub2_10 : sub2 [-2, -3] = true := by decide +kernel
theorem sub2_11 : sub2 [-2, -2] = true := by decide +kernel
theorem sub2_12 : sub2 [-2, -1] = true := by decide +kernel
theorem sub2_13 : sub2 [-2, 0] = true := by decide +kernel
theorem sub2_14 : sub2 [-2, 1] = true := by decide +kernel
theorem sub2_15 : sub2 [-2, 2] = true := by decide +kernel
theorem sub2_16 : sub2 [-2, 3] = true := by decide +kernel
theorem sub2_17 : sub2 [-2, 4] = true := by decide +kernel
theorem sub2_18 : sub2 [-1, -4] = true := by decide +kernel
theorem sub2_19 : sub2 [-1, -3] = true := by decide +kernel
theorem sub2_20 : sub2 [-1, -2] = true := by decide +kernel
theorem sub2_21 : sub2 [-1, -1] = true := by decide +kernel
theorem sub2_22 : sub2 [-1, 0] = true := by decide +kernel
theorem sub2_23 : sub2 [-1, 1] = true := by decide +kernel
theorem sub2_24 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_25 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_26 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_27 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_28 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_29 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_30 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_31 : sub2 [0, -1] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_cons.2 ⟨sub2_10, List.forall_mem_cons.2 ⟨sub2_11, List.forall_mem_cons.2 ⟨sub2_12, List.forall_mem_cons.2 ⟨sub2_13, List.forall_mem_cons.2 ⟨sub2_14, List.forall_mem_cons.2 ⟨sub2_15, List.forall_mem_cons.2 ⟨sub2_16, List.forall_mem_cons.2 ⟨sub2_17, List.forall_mem_cons.2 ⟨sub2_18, List.forall_mem_cons.2 ⟨sub2_19, List.forall_mem_cons.2 ⟨sub2_20, List.forall_mem_cons.2 ⟨sub2_21, List.forall_mem_cons.2 ⟨sub2_22, List.forall_mem_cons.2 ⟨sub2_23, List.forall_mem_cons.2 ⟨sub2_24, List.forall_mem_cons.2 ⟨sub2_25, List.forall_mem_cons.2 ⟨sub2_26, List.forall_mem_cons.2 ⟨sub2_27, List.forall_mem_cons.2 ⟨sub2_28, List.forall_mem_cons.2 ⟨sub2_29, List.forall_mem_cons.2 ⟨sub2_30, List.forall_mem_cons.2 ⟨sub2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_32 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_33 : sub2 [0, 1] = true := by decide +kernel
theorem sub2_34 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_35 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_36 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_37 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_38 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_39 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_40 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_41 : sub2 [1, -1] = true := by decide +kernel
theorem sub2_42 : sub2 [1, 0] = true := by decide +kernel
theorem sub2_43 : sub2 [1, 1] = true := by decide +kernel
theorem sub2_44 : sub2 [1, 2] = true := by decide +kernel
theorem sub2_45 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_46 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_47 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_48 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_49 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_50 : sub2 [2, -1] = true := by decide +kernel
theorem sub2_51 : sub2 [2, 0] = true := by decide +kernel
theorem sub2_52 : sub2 [2, 1] = true := by decide +kernel
theorem sub2_53 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_54 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_55 : sub2 [3, -5] = true := by decide +kernel
theorem sub2_56 : sub2 [3, -4] = true := by decide +kernel
theorem sub2_57 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_58 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_59 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_60 : sub2 [3, 0] = true := by decide +kernel
theorem sub2_61 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_62 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_63 : sub2 [4] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_cons.2 ⟨sub2_60, List.forall_mem_cons.2 ⟨sub2_61, List.forall_mem_cons.2 ⟨sub2_62, List.forall_mem_cons.2 ⟨sub2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-5, -2] = true := by decide +kernel
theorem sub3_1 : sub3 [-5, -1] = true := by decide +kernel
theorem sub3_2 : sub3 [-5, 0] = true := by decide +kernel
theorem sub3_3 : sub3 [-5, 1] = true := by decide +kernel
theorem sub3_4 : sub3 [-5, 2] = true := by decide +kernel
theorem sub3_5 : sub3 [-5, 3] = true := by decide +kernel
theorem sub3_6 : sub3 [-4, -3] = true := by decide +kernel
theorem sub3_7 : sub3 [-4, -2] = true := by decide +kernel
theorem sub3_8 : sub3 [-4, -1] = true := by decide +kernel
theorem sub3_9 : sub3 [-4, 0] = true := by decide +kernel
theorem sub3_10 : sub3 [-4, 1] = true := by decide +kernel
theorem sub3_11 : sub3 [-4, 2] = true := by decide +kernel
theorem sub3_12 : sub3 [-4, 3] = true := by decide +kernel
theorem sub3_13 : sub3 [-4, 4] = true := by decide +kernel
theorem sub3_14 : sub3 [-3, -4] = true := by decide +kernel
theorem sub3_15 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, -1] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, 0] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, 1] = true := by decide +kernel
theorem sub3_20 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_21 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_22 : sub3 [-3, 4] = true := by decide +kernel
theorem sub3_23 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_24 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_25 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_26 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_27 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_28 : sub3 [-2, 0, -7] = true := by decide +kernel
theorem sub3_29 : sub3 [-2, 0, -6] = true := by decide +kernel
theorem sub3_30 : sub3 [-2, 0, -5] = true := by decide +kernel
theorem sub3_31 : sub3 [-2, 0, -4] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-2, 0, -3] = true := by decide +kernel
theorem sub3_33 : sub3 [-2, 0, -2] = true := by decide +kernel
theorem sub3_34 : sub3 [-2, 0, -1] = true := by decide +kernel
theorem sub3_35 : sub3 [-2, 0, 0] = true := by decide +kernel
theorem sub3_36 : sub3 [-2, 0, 1] = true := by decide +kernel
theorem sub3_37 : sub3 [-2, 0, 2] = true := by decide +kernel
theorem sub3_38 : sub3 [-2, 0, 3] = true := by decide +kernel
theorem sub3_39 : sub3 [-2, 0, 4] = true := by decide +kernel
theorem sub3_40 : sub3 [-2, 0, 5] = true := by decide +kernel
theorem sub3_41 : sub3 [-2, 0, 6] = true := by decide +kernel
theorem sub3_42 : sub3 [-2, 1, -7] = true := by decide +kernel
theorem sub3_43 : sub3 [-2, 1, -6] = true := by decide +kernel
theorem sub3_44 : sub3 [-2, 1, -5] = true := by decide +kernel
theorem sub3_45 : sub3 [-2, 1, -4] = true := by decide +kernel
theorem sub3_46 : sub3 [-2, 1, -3] = true := by decide +kernel
theorem sub3_47 : sub3 [-2, 1, -2] = true := by decide +kernel
theorem sub3_48 : sub3 [-2, 1, -1] = true := by decide +kernel
theorem sub3_49 : sub3 [-2, 1, 0] = true := by decide +kernel
theorem sub3_50 : sub3 [-2, 1, 1] = true := by decide +kernel
theorem sub3_51 : sub3 [-2, 1, 2] = true := by decide +kernel
theorem sub3_52 : sub3 [-2, 1, 3] = true := by decide +kernel
theorem sub3_53 : sub3 [-2, 1, 4] = true := by decide +kernel
theorem sub3_54 : sub3 [-2, 1, 5] = true := by decide +kernel
theorem sub3_55 : sub3 [-2, 1, 6] = true := by decide +kernel
theorem sub3_56 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_57 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_58 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_59 : sub3 [-2, 5] = true := by decide +kernel
theorem sub3_60 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_61 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_62 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_63 : sub3 [-1, -2] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [-1, -1, -7] = true := by decide +kernel
theorem sub3_65 : sub3 [-1, -1, -6] = true := by decide +kernel
theorem sub3_66 : sub3 [-1, -1, -5] = true := by decide +kernel
theorem sub3_67 : sub3 [-1, -1, -4] = true := by decide +kernel
theorem sub3_68 : sub3 [-1, -1, -3] = true := by decide +kernel
theorem sub3_69 : sub3 [-1, -1, -2] = true := by decide +kernel
theorem sub3_70 : sub3 [-1, -1, -1] = true := by decide +kernel
theorem sub3_71 : sub3 [-1, -1, 0] = true := by decide +kernel
theorem sub3_72 : sub3 [-1, -1, 1] = true := by decide +kernel
theorem sub3_73 : sub3 [-1, -1, 2] = true := by decide +kernel
theorem sub3_74 : sub3 [-1, -1, 3] = true := by decide +kernel
theorem sub3_75 : sub3 [-1, -1, 4] = true := by decide +kernel
theorem sub3_76 : sub3 [-1, -1, 5] = true := by decide +kernel
theorem sub3_77 : sub3 [-1, -1, 6] = true := by decide +kernel
theorem sub3_78 : sub3 [-1, 0, -7] = true := by decide +kernel
theorem sub3_79 : sub3 [-1, 0, -6] = true := by decide +kernel
theorem sub3_80 : sub3 [-1, 0, -5] = true := by decide +kernel
theorem sub3_81 : sub3 [-1, 0, -4] = true := by decide +kernel
theorem sub3_82 : sub3 [-1, 0, -3] = true := by decide +kernel
theorem sub3_83 : sub3 [-1, 0, -2] = true := by decide +kernel
theorem sub3_84 : sub3 [-1, 0, -1] = true := by decide +kernel
theorem sub3_85 : sub3 [-1, 0, 0] = true := by decide +kernel
theorem sub3_86 : sub3 [-1, 0, 1] = true := by decide +kernel
theorem sub3_87 : sub3 [-1, 0, 2] = true := by decide +kernel
theorem sub3_88 : sub3 [-1, 0, 3] = true := by decide +kernel
theorem sub3_89 : sub3 [-1, 0, 4] = true := by decide +kernel
theorem sub3_90 : sub3 [-1, 0, 5] = true := by decide +kernel
theorem sub3_91 : sub3 [-1, 0, 6] = true := by decide +kernel
theorem sub3_92 : sub3 [-1, 1, -7] = true := by decide +kernel
theorem sub3_93 : sub3 [-1, 1, -6] = true := by decide +kernel
theorem sub3_94 : sub3 [-1, 1, -5] = true := by decide +kernel
theorem sub3_95 : sub3 [-1, 1, -4] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [-1, 1, -3] = true := by decide +kernel
theorem sub3_97 : sub3 [-1, 1, -2] = true := by decide +kernel
theorem sub3_98 : sub3 [-1, 1, -1] = true := by decide +kernel
theorem sub3_99 : sub3 [-1, 1, 0] = true := by decide +kernel
theorem sub3_100 : sub3 [-1, 1, 1] = true := by decide +kernel
theorem sub3_101 : sub3 [-1, 1, 2] = true := by decide +kernel
theorem sub3_102 : sub3 [-1, 1, 3] = true := by decide +kernel
theorem sub3_103 : sub3 [-1, 1, 4] = true := by decide +kernel
theorem sub3_104 : sub3 [-1, 1, 5] = true := by decide +kernel
theorem sub3_105 : sub3 [-1, 1, 6] = true := by decide +kernel
theorem sub3_106 : sub3 [-1, 2, -7] = true := by decide +kernel
theorem sub3_107 : sub3 [-1, 2, -6] = true := by decide +kernel
theorem sub3_108 : sub3 [-1, 2, -5] = true := by decide +kernel
theorem sub3_109 : sub3 [-1, 2, -4] = true := by decide +kernel
theorem sub3_110 : sub3 [-1, 2, -3] = true := by decide +kernel
theorem sub3_111 : sub3 [-1, 2, -2] = true := by decide +kernel
theorem sub3_112 : sub3 [-1, 2, -1] = true := by decide +kernel
theorem sub3_113 : sub3 [-1, 2, 0] = true := by decide +kernel
theorem sub3_114 : sub3 [-1, 2, 1] = true := by decide +kernel
theorem sub3_115 : sub3 [-1, 2, 2] = true := by decide +kernel
theorem sub3_116 : sub3 [-1, 2, 3] = true := by decide +kernel
theorem sub3_117 : sub3 [-1, 2, 4] = true := by decide +kernel
theorem sub3_118 : sub3 [-1, 2, 5] = true := by decide +kernel
theorem sub3_119 : sub3 [-1, 2, 6] = true := by decide +kernel
theorem sub3_120 : sub3 [-1, 3] = true := by decide +kernel
theorem sub3_121 : sub3 [-1, 4] = true := by decide +kernel
theorem sub3_122 : sub3 [-1, 5] = true := by decide +kernel
theorem sub3_123 : sub3 [0, -5] = true := by decide +kernel
theorem sub3_124 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_125 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_126 : sub3 [0, -2, -7] = true := by decide +kernel
theorem sub3_127 : sub3 [0, -2, -6] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C072
