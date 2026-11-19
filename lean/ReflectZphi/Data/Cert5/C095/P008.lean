import ReflectZphi.Data.Cert5.C095.Base

namespace ReflectZphi.Data.Cert5.C095

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_0 : subd9_1 [-5] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-4, -5] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-4, -4] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-4, -3] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-4, -2] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-4, -1] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-4, 0] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-4, 1] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-3, -6] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-3, -5] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-3, -4] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-3, -3] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-3, -2] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-3, -1] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-3, 0] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [-3, 1] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [-3, 2] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [-2, -6] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [-2, -5] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [-2, -4] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [-2, -3] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [-2, -2] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [-2, -1] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [-2, 0] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [-2, 1] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [-2, 2] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [-2, 3] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [-1, -5] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [-1, -4] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [-1, -1] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_32 : subd9_1 [-1, 0] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [-1, 1] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [-1, 3] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [0, -5] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [0, -4] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [0, 0] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [0, 3] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [0, 4] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [1, -4] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [1, -1] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [1, 0] = true := by decide +kernel
theorem subd9_1_51 : subd9_1 [1, 1] = true := by decide +kernel
theorem subd9_1_52 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_53 : subd9_1 [1, 3] = true := by decide +kernel
theorem subd9_1_54 : subd9_1 [1, 4] = true := by decide +kernel
theorem subd9_1_55 : subd9_1 [2, -4] = true := by decide +kernel
theorem subd9_1_56 : subd9_1 [2, -3] = true := by decide +kernel
theorem subd9_1_57 : subd9_1 [2, -2] = true := by decide +kernel
theorem subd9_1_58 : subd9_1 [2, -1] = true := by decide +kernel
theorem subd9_1_59 : subd9_1 [2, 0] = true := by decide +kernel
theorem subd9_1_60 : subd9_1 [2, 1] = true := by decide +kernel
theorem subd9_1_61 : subd9_1 [2, 2] = true := by decide +kernel
theorem subd9_1_62 : subd9_1 [2, 3] = true := by decide +kernel
theorem subd9_1_63 : subd9_1 [2, 4] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_cons.2 ⟨subd9_1_51, List.forall_mem_cons.2 ⟨subd9_1_52, List.forall_mem_cons.2 ⟨subd9_1_53, List.forall_mem_cons.2 ⟨subd9_1_54, List.forall_mem_cons.2 ⟨subd9_1_55, List.forall_mem_cons.2 ⟨subd9_1_56, List.forall_mem_cons.2 ⟨subd9_1_57, List.forall_mem_cons.2 ⟨subd9_1_58, List.forall_mem_cons.2 ⟨subd9_1_59, List.forall_mem_cons.2 ⟨subd9_1_60, List.forall_mem_cons.2 ⟨subd9_1_61, List.forall_mem_cons.2 ⟨subd9_1_62, List.forall_mem_cons.2 ⟨subd9_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_64 : subd9_1 [2, 5] = true := by decide +kernel
theorem subd9_1_65 : subd9_1 [3, -3] = true := by decide +kernel
theorem subd9_1_66 : subd9_1 [3, -2] = true := by decide +kernel
theorem subd9_1_67 : subd9_1 [3, -1] = true := by decide +kernel
theorem subd9_1_68 : subd9_1 [3, 0] = true := by decide +kernel
theorem subd9_1_69 : subd9_1 [3, 1] = true := by decide +kernel
theorem subd9_1_70 : subd9_1 [3, 2] = true := by decide +kernel
theorem subd9_1_71 : subd9_1 [3, 3] = true := by decide +kernel
theorem subd9_1_72 : subd9_1 [3, 4] = true := by decide +kernel
theorem subd9_1_73 : subd9_1 [3, 5] = true := by decide +kernel
theorem subd9_1_74 : subd9_1 [4, -2] = true := by decide +kernel
theorem subd9_1_75 : subd9_1 [4, -1] = true := by decide +kernel
theorem subd9_1_76 : subd9_1 [4, 0] = true := by decide +kernel
theorem subd9_1_77 : subd9_1 [4, 1] = true := by decide +kernel
theorem subd9_1_78 : subd9_1 [4, 2] = true := by decide +kernel
theorem subd9_1_79 : subd9_1 [4, 3] = true := by decide +kernel
theorem subd9_1_80 : subd9_1 [4, 4] = true := by decide +kernel
theorem subd9_1_81 : subd9_1 [5] = true := by decide +kernel
theorem sbd9_1_2 : ∀ q ∈ blkd9_1_2, subd9_1 q = true := by
  unfold blkd9_1_2
  exact List.forall_mem_cons.2 ⟨subd9_1_64, List.forall_mem_cons.2 ⟨subd9_1_65, List.forall_mem_cons.2 ⟨subd9_1_66, List.forall_mem_cons.2 ⟨subd9_1_67, List.forall_mem_cons.2 ⟨subd9_1_68, List.forall_mem_cons.2 ⟨subd9_1_69, List.forall_mem_cons.2 ⟨subd9_1_70, List.forall_mem_cons.2 ⟨subd9_1_71, List.forall_mem_cons.2 ⟨subd9_1_72, List.forall_mem_cons.2 ⟨subd9_1_73, List.forall_mem_cons.2 ⟨subd9_1_74, List.forall_mem_cons.2 ⟨subd9_1_75, List.forall_mem_cons.2 ⟨subd9_1_76, List.forall_mem_cons.2 ⟨subd9_1_77, List.forall_mem_cons.2 ⟨subd9_1_78, List.forall_mem_cons.2 ⟨subd9_1_79, List.forall_mem_cons.2 ⟨subd9_1_80, List.forall_mem_cons.2 ⟨subd9_1_81, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_0 : subd9_2 [-3] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-2] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-1, -3] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-1, -2] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-1, -1] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-1, 0] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-1, 1] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-1, 2] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [0, -4] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [0, -1] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [0, 0] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [0, 1] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [0, 2] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [0, 3] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [1, -3] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [1, -2] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [1, -1] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [1, 0] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [1, 1] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [1, 2] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [2] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [3] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_0 : subd9_3 [-2] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [2] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_0 : subd9_4 [] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_nil _⟩
theorem subd9_5_0 : subd9_5 [] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_nil _⟩
theorem subd9_6_0 : subd9_6 [] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_nil _⟩
theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_0 : subd10_1 [-3] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-2, -3] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-2, -2] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-2, -1] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-2, 0] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-2, 1] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-2, 2] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-2, 3] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-1, -4] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-1, 0] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-1, 1] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-1, 3] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [0, 0] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [1, -4] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [1, -1] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [1, 0] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [1, 1] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [1, 2] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [1, 3] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C095
