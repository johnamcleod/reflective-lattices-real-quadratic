import ReflectZphi.Data.Cert5.C095.Base

namespace ReflectZphi.Data.Cert5.C095

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [2] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_0 : subd6_3 [-3] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-2] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [2] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [3] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_0 : subd6_4 [] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_nil _⟩
theorem subd6_5_0 : subd6_5 [] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_nil _⟩
theorem subd6_6_0 : subd6_6 [] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_nil _⟩
theorem subd7_0_0 : subd7_0 [-4, -3] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-4, -2] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-4, -1] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-4, 0] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-4, 1] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-3, -4] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-3, -3] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-3, -2] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-3, -1] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-3, 0] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-3, 1] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-3, 2] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-2, -3] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-2, -2] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-2, -1, -7] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-2, -1, -6] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [-2, -1, -5] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [-2, -1, -4] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [-2, -1, -3] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [-2, -1, -2] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [-2, -1, -1] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [-2, -1, 0] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [-2, -1, 1] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [-2, -1, 2] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [-2, -1, 3] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [-2, -1, 4] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [-2, -1, 5] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [-2, -1, 6] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [-2, 0, -7] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [-2, 0, -6] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [-2, 0, -5] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [-2, 0, -4] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [-2, 0, -3] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [-2, 0, -2] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [-2, 0, -1] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [-2, 0, 0] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [-2, 0, 1] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [-2, 0, 2] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [-2, 0, 3] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [-2, 0, 4] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [-2, 0, 5] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [-2, 0, 6] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [-2, 0, 7] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [-2, 1, -7] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [-2, 1, -6] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [-2, 1, -5] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [-2, 1, -4] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [-2, 1, -3] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [-2, 1, -2] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [-2, 1, -1] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [-2, 1, 0] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [-2, 1, 1] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [-2, 1, 2] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [-2, 1, 3] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [-2, 1, 4] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [-2, 1, 5] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [-2, 1, 6] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [-2, 2] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [-2, 3] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [-1, -5] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_62 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_63 : subd7_0 [-1, -2, -8] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_cons.2 ⟨subd7_0_62, List.forall_mem_cons.2 ⟨subd7_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_64 : subd7_0 [-1, -2, -7] = true := by decide +kernel
theorem subd7_0_65 : subd7_0 [-1, -2, -6] = true := by decide +kernel
theorem subd7_0_66 : subd7_0 [-1, -2, -5] = true := by decide +kernel
theorem subd7_0_67 : subd7_0 [-1, -2, -4] = true := by decide +kernel
theorem subd7_0_68 : subd7_0 [-1, -2, -3] = true := by decide +kernel
theorem subd7_0_69 : subd7_0 [-1, -2, -2] = true := by decide +kernel
theorem subd7_0_70 : subd7_0 [-1, -2, -1] = true := by decide +kernel
theorem subd7_0_71 : subd7_0 [-1, -2, 0] = true := by decide +kernel
theorem subd7_0_72 : subd7_0 [-1, -2, 1] = true := by decide +kernel
theorem subd7_0_73 : subd7_0 [-1, -2, 2] = true := by decide +kernel
theorem subd7_0_74 : subd7_0 [-1, -2, 3] = true := by decide +kernel
theorem subd7_0_75 : subd7_0 [-1, -2, 4] = true := by decide +kernel
theorem subd7_0_76 : subd7_0 [-1, -2, 5] = true := by decide +kernel
theorem subd7_0_77 : subd7_0 [-1, -2, 6] = true := by decide +kernel
theorem subd7_0_78 : subd7_0 [-1, -1, -8] = true := by decide +kernel
theorem subd7_0_79 : subd7_0 [-1, -1, -7] = true := by decide +kernel
theorem subd7_0_80 : subd7_0 [-1, -1, -6] = true := by decide +kernel
theorem subd7_0_81 : subd7_0 [-1, -1, -5] = true := by decide +kernel
theorem subd7_0_82 : subd7_0 [-1, -1, -4] = true := by decide +kernel
theorem subd7_0_83 : subd7_0 [-1, -1, -3] = true := by decide +kernel
theorem subd7_0_84 : subd7_0 [-1, -1, -2] = true := by decide +kernel
theorem subd7_0_85 : subd7_0 [-1, -1, -1] = true := by decide +kernel
theorem subd7_0_86 : subd7_0 [-1, -1, 0] = true := by decide +kernel
theorem subd7_0_87 : subd7_0 [-1, -1, 1] = true := by decide +kernel
theorem subd7_0_88 : subd7_0 [-1, -1, 2] = true := by decide +kernel
theorem subd7_0_89 : subd7_0 [-1, -1, 3] = true := by decide +kernel
theorem subd7_0_90 : subd7_0 [-1, -1, 4] = true := by decide +kernel
theorem subd7_0_91 : subd7_0 [-1, -1, 5] = true := by decide +kernel
theorem subd7_0_92 : subd7_0 [-1, -1, 6] = true := by decide +kernel
theorem subd7_0_93 : subd7_0 [-1, -1, 7] = true := by decide +kernel
theorem subd7_0_94 : subd7_0 [-1, 0, -8] = true := by decide +kernel
theorem subd7_0_95 : subd7_0 [-1, 0, -7] = true := by decide +kernel
theorem sbd7_0_2 : ∀ q ∈ blkd7_0_2, subd7_0 q = true := by
  unfold blkd7_0_2
  exact List.forall_mem_cons.2 ⟨subd7_0_64, List.forall_mem_cons.2 ⟨subd7_0_65, List.forall_mem_cons.2 ⟨subd7_0_66, List.forall_mem_cons.2 ⟨subd7_0_67, List.forall_mem_cons.2 ⟨subd7_0_68, List.forall_mem_cons.2 ⟨subd7_0_69, List.forall_mem_cons.2 ⟨subd7_0_70, List.forall_mem_cons.2 ⟨subd7_0_71, List.forall_mem_cons.2 ⟨subd7_0_72, List.forall_mem_cons.2 ⟨subd7_0_73, List.forall_mem_cons.2 ⟨subd7_0_74, List.forall_mem_cons.2 ⟨subd7_0_75, List.forall_mem_cons.2 ⟨subd7_0_76, List.forall_mem_cons.2 ⟨subd7_0_77, List.forall_mem_cons.2 ⟨subd7_0_78, List.forall_mem_cons.2 ⟨subd7_0_79, List.forall_mem_cons.2 ⟨subd7_0_80, List.forall_mem_cons.2 ⟨subd7_0_81, List.forall_mem_cons.2 ⟨subd7_0_82, List.forall_mem_cons.2 ⟨subd7_0_83, List.forall_mem_cons.2 ⟨subd7_0_84, List.forall_mem_cons.2 ⟨subd7_0_85, List.forall_mem_cons.2 ⟨subd7_0_86, List.forall_mem_cons.2 ⟨subd7_0_87, List.forall_mem_cons.2 ⟨subd7_0_88, List.forall_mem_cons.2 ⟨subd7_0_89, List.forall_mem_cons.2 ⟨subd7_0_90, List.forall_mem_cons.2 ⟨subd7_0_91, List.forall_mem_cons.2 ⟨subd7_0_92, List.forall_mem_cons.2 ⟨subd7_0_93, List.forall_mem_cons.2 ⟨subd7_0_94, List.forall_mem_cons.2 ⟨subd7_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_96 : subd7_0 [-1, 0, -6] = true := by decide +kernel
theorem subd7_0_97 : subd7_0 [-1, 0, -5] = true := by decide +kernel
theorem subd7_0_98 : subd7_0 [-1, 0, -4] = true := by decide +kernel
theorem subd7_0_99 : subd7_0 [-1, 0, -3] = true := by decide +kernel
theorem subd7_0_100 : subd7_0 [-1, 0, -2] = true := by decide +kernel
theorem subd7_0_101 : subd7_0 [-1, 0, -1] = true := by decide +kernel
theorem subd7_0_102 : subd7_0 [-1, 0, 0] = true := by decide +kernel
theorem subd7_0_103 : subd7_0 [-1, 0, 1] = true := by decide +kernel
theorem subd7_0_104 : subd7_0 [-1, 0, 2] = true := by decide +kernel
theorem subd7_0_105 : subd7_0 [-1, 0, 3] = true := by decide +kernel
theorem subd7_0_106 : subd7_0 [-1, 0, 4] = true := by decide +kernel
theorem subd7_0_107 : subd7_0 [-1, 0, 5] = true := by decide +kernel
theorem subd7_0_108 : subd7_0 [-1, 0, 6] = true := by decide +kernel
theorem subd7_0_109 : subd7_0 [-1, 0, 7] = true := by decide +kernel
theorem subd7_0_110 : subd7_0 [-1, 1, -7] = true := by decide +kernel
theorem subd7_0_111 : subd7_0 [-1, 1, -6] = true := by decide +kernel
theorem subd7_0_112 : subd7_0 [-1, 1, -5] = true := by decide +kernel
theorem subd7_0_113 : subd7_0 [-1, 1, -4] = true := by decide +kernel
theorem subd7_0_114 : subd7_0 [-1, 1, -3] = true := by decide +kernel
theorem subd7_0_115 : subd7_0 [-1, 1, -2] = true := by decide +kernel
theorem subd7_0_116 : subd7_0 [-1, 1, -1] = true := by decide +kernel
theorem subd7_0_117 : subd7_0 [-1, 1, 0] = true := by decide +kernel
theorem subd7_0_118 : subd7_0 [-1, 1, 1] = true := by decide +kernel
theorem subd7_0_119 : subd7_0 [-1, 1, 2] = true := by decide +kernel
theorem subd7_0_120 : subd7_0 [-1, 1, 3] = true := by decide +kernel
theorem subd7_0_121 : subd7_0 [-1, 1, 4] = true := by decide +kernel
theorem subd7_0_122 : subd7_0 [-1, 1, 5] = true := by decide +kernel
theorem subd7_0_123 : subd7_0 [-1, 1, 6] = true := by decide +kernel
theorem subd7_0_124 : subd7_0 [-1, 1, 7] = true := by decide +kernel
theorem subd7_0_125 : subd7_0 [-1, 2, -6] = true := by decide +kernel
theorem subd7_0_126 : subd7_0 [-1, 2, -5] = true := by decide +kernel
theorem subd7_0_127 : subd7_0 [-1, 2, -4] = true := by decide +kernel
theorem sbd7_0_3 : ∀ q ∈ blkd7_0_3, subd7_0 q = true := by
  unfold blkd7_0_3
  exact List.forall_mem_cons.2 ⟨subd7_0_96, List.forall_mem_cons.2 ⟨subd7_0_97, List.forall_mem_cons.2 ⟨subd7_0_98, List.forall_mem_cons.2 ⟨subd7_0_99, List.forall_mem_cons.2 ⟨subd7_0_100, List.forall_mem_cons.2 ⟨subd7_0_101, List.forall_mem_cons.2 ⟨subd7_0_102, List.forall_mem_cons.2 ⟨subd7_0_103, List.forall_mem_cons.2 ⟨subd7_0_104, List.forall_mem_cons.2 ⟨subd7_0_105, List.forall_mem_cons.2 ⟨subd7_0_106, List.forall_mem_cons.2 ⟨subd7_0_107, List.forall_mem_cons.2 ⟨subd7_0_108, List.forall_mem_cons.2 ⟨subd7_0_109, List.forall_mem_cons.2 ⟨subd7_0_110, List.forall_mem_cons.2 ⟨subd7_0_111, List.forall_mem_cons.2 ⟨subd7_0_112, List.forall_mem_cons.2 ⟨subd7_0_113, List.forall_mem_cons.2 ⟨subd7_0_114, List.forall_mem_cons.2 ⟨subd7_0_115, List.forall_mem_cons.2 ⟨subd7_0_116, List.forall_mem_cons.2 ⟨subd7_0_117, List.forall_mem_cons.2 ⟨subd7_0_118, List.forall_mem_cons.2 ⟨subd7_0_119, List.forall_mem_cons.2 ⟨subd7_0_120, List.forall_mem_cons.2 ⟨subd7_0_121, List.forall_mem_cons.2 ⟨subd7_0_122, List.forall_mem_cons.2 ⟨subd7_0_123, List.forall_mem_cons.2 ⟨subd7_0_124, List.forall_mem_cons.2 ⟨subd7_0_125, List.forall_mem_cons.2 ⟨subd7_0_126, List.forall_mem_cons.2 ⟨subd7_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_128 : subd7_0 [-1, 2, -3] = true := by decide +kernel
theorem subd7_0_129 : subd7_0 [-1, 2, -2] = true := by decide +kernel
theorem subd7_0_130 : subd7_0 [-1, 2, -1] = true := by decide +kernel
theorem subd7_0_131 : subd7_0 [-1, 2, 0] = true := by decide +kernel
theorem subd7_0_132 : subd7_0 [-1, 2, 1] = true := by decide +kernel
theorem subd7_0_133 : subd7_0 [-1, 2, 2] = true := by decide +kernel
theorem subd7_0_134 : subd7_0 [-1, 2, 3] = true := by decide +kernel
theorem subd7_0_135 : subd7_0 [-1, 2, 4] = true := by decide +kernel
theorem subd7_0_136 : subd7_0 [-1, 2, 5] = true := by decide +kernel
theorem subd7_0_137 : subd7_0 [-1, 2, 6] = true := by decide +kernel
theorem subd7_0_138 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_139 : subd7_0 [0, -5] = true := by decide +kernel
theorem subd7_0_140 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_141 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_142 : subd7_0 [0, -2, -8] = true := by decide +kernel
theorem subd7_0_143 : subd7_0 [0, -2, -7] = true := by decide +kernel
theorem subd7_0_144 : subd7_0 [0, -2, -6] = true := by decide +kernel
theorem subd7_0_145 : subd7_0 [0, -2, -5] = true := by decide +kernel
theorem subd7_0_146 : subd7_0 [0, -2, -4] = true := by decide +kernel
theorem subd7_0_147 : subd7_0 [0, -2, -3] = true := by decide +kernel
theorem subd7_0_148 : subd7_0 [0, -2, -2] = true := by decide +kernel
theorem subd7_0_149 : subd7_0 [0, -2, -1] = true := by decide +kernel
theorem subd7_0_150 : subd7_0 [0, -2, 0] = true := by decide +kernel
theorem subd7_0_151 : subd7_0 [0, -2, 1] = true := by decide +kernel
theorem subd7_0_152 : subd7_0 [0, -2, 2] = true := by decide +kernel
theorem subd7_0_153 : subd7_0 [0, -2, 3] = true := by decide +kernel
theorem subd7_0_154 : subd7_0 [0, -2, 4] = true := by decide +kernel
theorem subd7_0_155 : subd7_0 [0, -2, 5] = true := by decide +kernel
theorem subd7_0_156 : subd7_0 [0, -2, 6] = true := by decide +kernel
theorem subd7_0_157 : subd7_0 [0, -1, -8] = true := by decide +kernel
theorem subd7_0_158 : subd7_0 [0, -1, -7] = true := by decide +kernel
theorem subd7_0_159 : subd7_0 [0, -1, -6] = true := by decide +kernel
theorem sbd7_0_4 : ∀ q ∈ blkd7_0_4, subd7_0 q = true := by
  unfold blkd7_0_4
  exact List.forall_mem_cons.2 ⟨subd7_0_128, List.forall_mem_cons.2 ⟨subd7_0_129, List.forall_mem_cons.2 ⟨subd7_0_130, List.forall_mem_cons.2 ⟨subd7_0_131, List.forall_mem_cons.2 ⟨subd7_0_132, List.forall_mem_cons.2 ⟨subd7_0_133, List.forall_mem_cons.2 ⟨subd7_0_134, List.forall_mem_cons.2 ⟨subd7_0_135, List.forall_mem_cons.2 ⟨subd7_0_136, List.forall_mem_cons.2 ⟨subd7_0_137, List.forall_mem_cons.2 ⟨subd7_0_138, List.forall_mem_cons.2 ⟨subd7_0_139, List.forall_mem_cons.2 ⟨subd7_0_140, List.forall_mem_cons.2 ⟨subd7_0_141, List.forall_mem_cons.2 ⟨subd7_0_142, List.forall_mem_cons.2 ⟨subd7_0_143, List.forall_mem_cons.2 ⟨subd7_0_144, List.forall_mem_cons.2 ⟨subd7_0_145, List.forall_mem_cons.2 ⟨subd7_0_146, List.forall_mem_cons.2 ⟨subd7_0_147, List.forall_mem_cons.2 ⟨subd7_0_148, List.forall_mem_cons.2 ⟨subd7_0_149, List.forall_mem_cons.2 ⟨subd7_0_150, List.forall_mem_cons.2 ⟨subd7_0_151, List.forall_mem_cons.2 ⟨subd7_0_152, List.forall_mem_cons.2 ⟨subd7_0_153, List.forall_mem_cons.2 ⟨subd7_0_154, List.forall_mem_cons.2 ⟨subd7_0_155, List.forall_mem_cons.2 ⟨subd7_0_156, List.forall_mem_cons.2 ⟨subd7_0_157, List.forall_mem_cons.2 ⟨subd7_0_158, List.forall_mem_cons.2 ⟨subd7_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_160 : subd7_0 [0, -1, -5] = true := by decide +kernel
theorem subd7_0_161 : subd7_0 [0, -1, -4] = true := by decide +kernel
theorem subd7_0_162 : subd7_0 [0, -1, -3] = true := by decide +kernel
theorem subd7_0_163 : subd7_0 [0, -1, -2] = true := by decide +kernel
theorem subd7_0_164 : subd7_0 [0, -1, -1] = true := by decide +kernel
theorem subd7_0_165 : subd7_0 [0, -1, 0] = true := by decide +kernel
theorem subd7_0_166 : subd7_0 [0, -1, 1] = true := by decide +kernel
theorem subd7_0_167 : subd7_0 [0, -1, 2] = true := by decide +kernel
theorem subd7_0_168 : subd7_0 [0, -1, 3] = true := by decide +kernel
theorem subd7_0_169 : subd7_0 [0, -1, 4] = true := by decide +kernel
theorem subd7_0_170 : subd7_0 [0, -1, 5] = true := by decide +kernel
theorem subd7_0_171 : subd7_0 [0, -1, 6] = true := by decide +kernel
theorem subd7_0_172 : subd7_0 [0, -1, 7] = true := by decide +kernel
theorem subd7_0_173 : subd7_0 [0, 0, -8] = true := by decide +kernel
theorem subd7_0_174 : subd7_0 [0, 0, -7] = true := by decide +kernel
theorem subd7_0_175 : subd7_0 [0, 0, -6] = true := by decide +kernel
theorem subd7_0_176 : subd7_0 [0, 0, -5] = true := by decide +kernel
theorem subd7_0_177 : subd7_0 [0, 0, -4] = true := by decide +kernel
theorem subd7_0_178 : subd7_0 [0, 0, -3] = true := by decide +kernel
theorem subd7_0_179 : subd7_0 [0, 0, -2] = true := by decide +kernel
theorem subd7_0_180 : subd7_0 [0, 0, -1] = true := by decide +kernel
theorem subd7_0_181 : subd7_0 [0, 0, 0] = true := by decide +kernel
theorem subd7_0_182 : subd7_0 [0, 0, 1] = true := by decide +kernel
theorem subd7_0_183 : subd7_0 [0, 0, 2] = true := by decide +kernel
theorem subd7_0_184 : subd7_0 [0, 0, 3] = true := by decide +kernel
theorem subd7_0_185 : subd7_0 [0, 0, 4] = true := by decide +kernel
theorem subd7_0_186 : subd7_0 [0, 0, 5] = true := by decide +kernel
theorem subd7_0_187 : subd7_0 [0, 0, 6] = true := by decide +kernel
theorem subd7_0_188 : subd7_0 [0, 0, 7] = true := by decide +kernel
theorem subd7_0_189 : subd7_0 [0, 1, -8] = true := by decide +kernel
theorem subd7_0_190 : subd7_0 [0, 1, -7] = true := by decide +kernel
theorem subd7_0_191 : subd7_0 [0, 1, -6] = true := by decide +kernel
theorem sbd7_0_5 : ∀ q ∈ blkd7_0_5, subd7_0 q = true := by
  unfold blkd7_0_5
  exact List.forall_mem_cons.2 ⟨subd7_0_160, List.forall_mem_cons.2 ⟨subd7_0_161, List.forall_mem_cons.2 ⟨subd7_0_162, List.forall_mem_cons.2 ⟨subd7_0_163, List.forall_mem_cons.2 ⟨subd7_0_164, List.forall_mem_cons.2 ⟨subd7_0_165, List.forall_mem_cons.2 ⟨subd7_0_166, List.forall_mem_cons.2 ⟨subd7_0_167, List.forall_mem_cons.2 ⟨subd7_0_168, List.forall_mem_cons.2 ⟨subd7_0_169, List.forall_mem_cons.2 ⟨subd7_0_170, List.forall_mem_cons.2 ⟨subd7_0_171, List.forall_mem_cons.2 ⟨subd7_0_172, List.forall_mem_cons.2 ⟨subd7_0_173, List.forall_mem_cons.2 ⟨subd7_0_174, List.forall_mem_cons.2 ⟨subd7_0_175, List.forall_mem_cons.2 ⟨subd7_0_176, List.forall_mem_cons.2 ⟨subd7_0_177, List.forall_mem_cons.2 ⟨subd7_0_178, List.forall_mem_cons.2 ⟨subd7_0_179, List.forall_mem_cons.2 ⟨subd7_0_180, List.forall_mem_cons.2 ⟨subd7_0_181, List.forall_mem_cons.2 ⟨subd7_0_182, List.forall_mem_cons.2 ⟨subd7_0_183, List.forall_mem_cons.2 ⟨subd7_0_184, List.forall_mem_cons.2 ⟨subd7_0_185, List.forall_mem_cons.2 ⟨subd7_0_186, List.forall_mem_cons.2 ⟨subd7_0_187, List.forall_mem_cons.2 ⟨subd7_0_188, List.forall_mem_cons.2 ⟨subd7_0_189, List.forall_mem_cons.2 ⟨subd7_0_190, List.forall_mem_cons.2 ⟨subd7_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_192 : subd7_0 [0, 1, -5] = true := by decide +kernel
theorem subd7_0_193 : subd7_0 [0, 1, -4] = true := by decide +kernel
theorem subd7_0_194 : subd7_0 [0, 1, -3] = true := by decide +kernel
theorem subd7_0_195 : subd7_0 [0, 1, -2] = true := by decide +kernel
theorem subd7_0_196 : subd7_0 [0, 1, -1] = true := by decide +kernel
theorem subd7_0_197 : subd7_0 [0, 1, 0] = true := by decide +kernel
theorem subd7_0_198 : subd7_0 [0, 1, 1] = true := by decide +kernel
theorem subd7_0_199 : subd7_0 [0, 1, 2] = true := by decide +kernel
theorem subd7_0_200 : subd7_0 [0, 1, 3] = true := by decide +kernel
theorem subd7_0_201 : subd7_0 [0, 1, 4] = true := by decide +kernel
theorem subd7_0_202 : subd7_0 [0, 1, 5] = true := by decide +kernel
theorem subd7_0_203 : subd7_0 [0, 1, 6] = true := by decide +kernel
theorem subd7_0_204 : subd7_0 [0, 1, 7] = true := by decide +kernel
theorem subd7_0_205 : subd7_0 [0, 2, -7] = true := by decide +kernel
theorem subd7_0_206 : subd7_0 [0, 2, -6] = true := by decide +kernel
theorem subd7_0_207 : subd7_0 [0, 2, -5] = true := by decide +kernel
theorem subd7_0_208 : subd7_0 [0, 2, -4] = true := by decide +kernel
theorem subd7_0_209 : subd7_0 [0, 2, -3] = true := by decide +kernel
theorem subd7_0_210 : subd7_0 [0, 2, -2] = true := by decide +kernel
theorem subd7_0_211 : subd7_0 [0, 2, -1] = true := by decide +kernel
theorem subd7_0_212 : subd7_0 [0, 2, 0] = true := by decide +kernel
theorem subd7_0_213 : subd7_0 [0, 2, 1] = true := by decide +kernel
theorem subd7_0_214 : subd7_0 [0, 2, 2] = true := by decide +kernel
theorem subd7_0_215 : subd7_0 [0, 2, 3] = true := by decide +kernel
theorem subd7_0_216 : subd7_0 [0, 2, 4] = true := by decide +kernel
theorem subd7_0_217 : subd7_0 [0, 2, 5] = true := by decide +kernel
theorem subd7_0_218 : subd7_0 [0, 2, 6] = true := by decide +kernel
theorem subd7_0_219 : subd7_0 [0, 2, 7] = true := by decide +kernel
theorem subd7_0_220 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_221 : subd7_0 [0, 4] = true := by decide +kernel
theorem subd7_0_222 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_223 : subd7_0 [1, -3] = true := by decide +kernel
theorem sbd7_0_6 : ∀ q ∈ blkd7_0_6, subd7_0 q = true := by
  unfold blkd7_0_6
  exact List.forall_mem_cons.2 ⟨subd7_0_192, List.forall_mem_cons.2 ⟨subd7_0_193, List.forall_mem_cons.2 ⟨subd7_0_194, List.forall_mem_cons.2 ⟨subd7_0_195, List.forall_mem_cons.2 ⟨subd7_0_196, List.forall_mem_cons.2 ⟨subd7_0_197, List.forall_mem_cons.2 ⟨subd7_0_198, List.forall_mem_cons.2 ⟨subd7_0_199, List.forall_mem_cons.2 ⟨subd7_0_200, List.forall_mem_cons.2 ⟨subd7_0_201, List.forall_mem_cons.2 ⟨subd7_0_202, List.forall_mem_cons.2 ⟨subd7_0_203, List.forall_mem_cons.2 ⟨subd7_0_204, List.forall_mem_cons.2 ⟨subd7_0_205, List.forall_mem_cons.2 ⟨subd7_0_206, List.forall_mem_cons.2 ⟨subd7_0_207, List.forall_mem_cons.2 ⟨subd7_0_208, List.forall_mem_cons.2 ⟨subd7_0_209, List.forall_mem_cons.2 ⟨subd7_0_210, List.forall_mem_cons.2 ⟨subd7_0_211, List.forall_mem_cons.2 ⟨subd7_0_212, List.forall_mem_cons.2 ⟨subd7_0_213, List.forall_mem_cons.2 ⟨subd7_0_214, List.forall_mem_cons.2 ⟨subd7_0_215, List.forall_mem_cons.2 ⟨subd7_0_216, List.forall_mem_cons.2 ⟨subd7_0_217, List.forall_mem_cons.2 ⟨subd7_0_218, List.forall_mem_cons.2 ⟨subd7_0_219, List.forall_mem_cons.2 ⟨subd7_0_220, List.forall_mem_cons.2 ⟨subd7_0_221, List.forall_mem_cons.2 ⟨subd7_0_222, List.forall_mem_cons.2 ⟨subd7_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_224 : subd7_0 [1, -2, -7] = true := by decide +kernel
theorem subd7_0_225 : subd7_0 [1, -2, -6] = true := by decide +kernel
theorem subd7_0_226 : subd7_0 [1, -2, -5] = true := by decide +kernel
theorem subd7_0_227 : subd7_0 [1, -2, -4] = true := by decide +kernel
theorem subd7_0_228 : subd7_0 [1, -2, -3] = true := by decide +kernel
theorem subd7_0_229 : subd7_0 [1, -2, -2] = true := by decide +kernel
theorem subd7_0_230 : subd7_0 [1, -2, -1] = true := by decide +kernel
theorem subd7_0_231 : subd7_0 [1, -2, 0] = true := by decide +kernel
theorem subd7_0_232 : subd7_0 [1, -2, 1] = true := by decide +kernel
theorem subd7_0_233 : subd7_0 [1, -2, 2] = true := by decide +kernel
theorem subd7_0_234 : subd7_0 [1, -2, 3] = true := by decide +kernel
theorem subd7_0_235 : subd7_0 [1, -2, 4] = true := by decide +kernel
theorem subd7_0_236 : subd7_0 [1, -2, 5] = true := by decide +kernel
theorem subd7_0_237 : subd7_0 [1, -1, -8] = true := by decide +kernel
theorem subd7_0_238 : subd7_0 [1, -1, -7] = true := by decide +kernel
theorem subd7_0_239 : subd7_0 [1, -1, -6] = true := by decide +kernel
theorem subd7_0_240 : subd7_0 [1, -1, -5] = true := by decide +kernel
theorem subd7_0_241 : subd7_0 [1, -1, -4] = true := by decide +kernel
theorem subd7_0_242 : subd7_0 [1, -1, -3] = true := by decide +kernel
theorem subd7_0_243 : subd7_0 [1, -1, -2] = true := by decide +kernel
theorem subd7_0_244 : subd7_0 [1, -1, -1] = true := by decide +kernel
theorem subd7_0_245 : subd7_0 [1, -1, 0] = true := by decide +kernel
theorem subd7_0_246 : subd7_0 [1, -1, 1] = true := by decide +kernel
theorem subd7_0_247 : subd7_0 [1, -1, 2] = true := by decide +kernel
theorem subd7_0_248 : subd7_0 [1, -1, 3] = true := by decide +kernel
theorem subd7_0_249 : subd7_0 [1, -1, 4] = true := by decide +kernel
theorem subd7_0_250 : subd7_0 [1, -1, 5] = true := by decide +kernel
theorem subd7_0_251 : subd7_0 [1, -1, 6] = true := by decide +kernel
theorem subd7_0_252 : subd7_0 [1, 0, -8] = true := by decide +kernel
theorem subd7_0_253 : subd7_0 [1, 0, -7] = true := by decide +kernel
theorem subd7_0_254 : subd7_0 [1, 0, -6] = true := by decide +kernel
theorem subd7_0_255 : subd7_0 [1, 0, -5] = true := by decide +kernel
theorem sbd7_0_7 : ∀ q ∈ blkd7_0_7, subd7_0 q = true := by
  unfold blkd7_0_7
  exact List.forall_mem_cons.2 ⟨subd7_0_224, List.forall_mem_cons.2 ⟨subd7_0_225, List.forall_mem_cons.2 ⟨subd7_0_226, List.forall_mem_cons.2 ⟨subd7_0_227, List.forall_mem_cons.2 ⟨subd7_0_228, List.forall_mem_cons.2 ⟨subd7_0_229, List.forall_mem_cons.2 ⟨subd7_0_230, List.forall_mem_cons.2 ⟨subd7_0_231, List.forall_mem_cons.2 ⟨subd7_0_232, List.forall_mem_cons.2 ⟨subd7_0_233, List.forall_mem_cons.2 ⟨subd7_0_234, List.forall_mem_cons.2 ⟨subd7_0_235, List.forall_mem_cons.2 ⟨subd7_0_236, List.forall_mem_cons.2 ⟨subd7_0_237, List.forall_mem_cons.2 ⟨subd7_0_238, List.forall_mem_cons.2 ⟨subd7_0_239, List.forall_mem_cons.2 ⟨subd7_0_240, List.forall_mem_cons.2 ⟨subd7_0_241, List.forall_mem_cons.2 ⟨subd7_0_242, List.forall_mem_cons.2 ⟨subd7_0_243, List.forall_mem_cons.2 ⟨subd7_0_244, List.forall_mem_cons.2 ⟨subd7_0_245, List.forall_mem_cons.2 ⟨subd7_0_246, List.forall_mem_cons.2 ⟨subd7_0_247, List.forall_mem_cons.2 ⟨subd7_0_248, List.forall_mem_cons.2 ⟨subd7_0_249, List.forall_mem_cons.2 ⟨subd7_0_250, List.forall_mem_cons.2 ⟨subd7_0_251, List.forall_mem_cons.2 ⟨subd7_0_252, List.forall_mem_cons.2 ⟨subd7_0_253, List.forall_mem_cons.2 ⟨subd7_0_254, List.forall_mem_cons.2 ⟨subd7_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_256 : subd7_0 [1, 0, -4] = true := by decide +kernel
theorem subd7_0_257 : subd7_0 [1, 0, -3] = true := by decide +kernel
theorem subd7_0_258 : subd7_0 [1, 0, -2] = true := by decide +kernel
theorem subd7_0_259 : subd7_0 [1, 0, -1] = true := by decide +kernel
theorem subd7_0_260 : subd7_0 [1, 0, 0] = true := by decide +kernel
theorem subd7_0_261 : subd7_0 [1, 0, 1] = true := by decide +kernel
theorem subd7_0_262 : subd7_0 [1, 0, 2] = true := by decide +kernel
theorem subd7_0_263 : subd7_0 [1, 0, 3] = true := by decide +kernel
theorem subd7_0_264 : subd7_0 [1, 0, 4] = true := by decide +kernel
theorem subd7_0_265 : subd7_0 [1, 0, 5] = true := by decide +kernel
theorem subd7_0_266 : subd7_0 [1, 0, 6] = true := by decide +kernel
theorem subd7_0_267 : subd7_0 [1, 0, 7] = true := by decide +kernel
theorem subd7_0_268 : subd7_0 [1, 1, -8] = true := by decide +kernel
theorem subd7_0_269 : subd7_0 [1, 1, -7] = true := by decide +kernel
theorem subd7_0_270 : subd7_0 [1, 1, -6] = true := by decide +kernel
theorem subd7_0_271 : subd7_0 [1, 1, -5] = true := by decide +kernel
theorem subd7_0_272 : subd7_0 [1, 1, -4] = true := by decide +kernel
theorem subd7_0_273 : subd7_0 [1, 1, -3] = true := by decide +kernel
theorem subd7_0_274 : subd7_0 [1, 1, -2] = true := by decide +kernel
theorem subd7_0_275 : subd7_0 [1, 1, -1] = true := by decide +kernel
theorem subd7_0_276 : subd7_0 [1, 1, 0] = true := by decide +kernel
theorem subd7_0_277 : subd7_0 [1, 1, 1] = true := by decide +kernel
theorem subd7_0_278 : subd7_0 [1, 1, 2] = true := by decide +kernel
theorem subd7_0_279 : subd7_0 [1, 1, 3] = true := by decide +kernel
theorem subd7_0_280 : subd7_0 [1, 1, 4] = true := by decide +kernel
theorem subd7_0_281 : subd7_0 [1, 1, 5] = true := by decide +kernel
theorem subd7_0_282 : subd7_0 [1, 1, 6] = true := by decide +kernel
theorem subd7_0_283 : subd7_0 [1, 1, 7] = true := by decide +kernel
theorem subd7_0_284 : subd7_0 [1, 2, -7] = true := by decide +kernel
theorem subd7_0_285 : subd7_0 [1, 2, -6] = true := by decide +kernel
theorem subd7_0_286 : subd7_0 [1, 2, -5] = true := by decide +kernel
theorem subd7_0_287 : subd7_0 [1, 2, -4] = true := by decide +kernel
theorem sbd7_0_8 : ∀ q ∈ blkd7_0_8, subd7_0 q = true := by
  unfold blkd7_0_8
  exact List.forall_mem_cons.2 ⟨subd7_0_256, List.forall_mem_cons.2 ⟨subd7_0_257, List.forall_mem_cons.2 ⟨subd7_0_258, List.forall_mem_cons.2 ⟨subd7_0_259, List.forall_mem_cons.2 ⟨subd7_0_260, List.forall_mem_cons.2 ⟨subd7_0_261, List.forall_mem_cons.2 ⟨subd7_0_262, List.forall_mem_cons.2 ⟨subd7_0_263, List.forall_mem_cons.2 ⟨subd7_0_264, List.forall_mem_cons.2 ⟨subd7_0_265, List.forall_mem_cons.2 ⟨subd7_0_266, List.forall_mem_cons.2 ⟨subd7_0_267, List.forall_mem_cons.2 ⟨subd7_0_268, List.forall_mem_cons.2 ⟨subd7_0_269, List.forall_mem_cons.2 ⟨subd7_0_270, List.forall_mem_cons.2 ⟨subd7_0_271, List.forall_mem_cons.2 ⟨subd7_0_272, List.forall_mem_cons.2 ⟨subd7_0_273, List.forall_mem_cons.2 ⟨subd7_0_274, List.forall_mem_cons.2 ⟨subd7_0_275, List.forall_mem_cons.2 ⟨subd7_0_276, List.forall_mem_cons.2 ⟨subd7_0_277, List.forall_mem_cons.2 ⟨subd7_0_278, List.forall_mem_cons.2 ⟨subd7_0_279, List.forall_mem_cons.2 ⟨subd7_0_280, List.forall_mem_cons.2 ⟨subd7_0_281, List.forall_mem_cons.2 ⟨subd7_0_282, List.forall_mem_cons.2 ⟨subd7_0_283, List.forall_mem_cons.2 ⟨subd7_0_284, List.forall_mem_cons.2 ⟨subd7_0_285, List.forall_mem_cons.2 ⟨subd7_0_286, List.forall_mem_cons.2 ⟨subd7_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_288 : subd7_0 [1, 2, -3] = true := by decide +kernel
theorem subd7_0_289 : subd7_0 [1, 2, -2] = true := by decide +kernel
theorem subd7_0_290 : subd7_0 [1, 2, -1] = true := by decide +kernel
theorem subd7_0_291 : subd7_0 [1, 2, 0] = true := by decide +kernel
theorem subd7_0_292 : subd7_0 [1, 2, 1] = true := by decide +kernel
theorem subd7_0_293 : subd7_0 [1, 2, 2] = true := by decide +kernel
theorem subd7_0_294 : subd7_0 [1, 2, 3] = true := by decide +kernel
theorem subd7_0_295 : subd7_0 [1, 2, 4] = true := by decide +kernel
theorem subd7_0_296 : subd7_0 [1, 2, 5] = true := by decide +kernel
theorem subd7_0_297 : subd7_0 [1, 2, 6] = true := by decide +kernel
theorem subd7_0_298 : subd7_0 [1, 2, 7] = true := by decide +kernel
theorem subd7_0_299 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_300 : subd7_0 [1, 4] = true := by decide +kernel
theorem subd7_0_301 : subd7_0 [2, -4] = true := by decide +kernel
theorem subd7_0_302 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_303 : subd7_0 [2, -2] = true := by decide +kernel
theorem subd7_0_304 : subd7_0 [2, -1, -7] = true := by decide +kernel
theorem subd7_0_305 : subd7_0 [2, -1, -6] = true := by decide +kernel
theorem subd7_0_306 : subd7_0 [2, -1, -5] = true := by decide +kernel
theorem subd7_0_307 : subd7_0 [2, -1, -4] = true := by decide +kernel
theorem subd7_0_308 : subd7_0 [2, -1, -3] = true := by decide +kernel
theorem subd7_0_309 : subd7_0 [2, -1, -2] = true := by decide +kernel
theorem subd7_0_310 : subd7_0 [2, -1, -1] = true := by decide +kernel
theorem subd7_0_311 : subd7_0 [2, -1, 0] = true := by decide +kernel
theorem subd7_0_312 : subd7_0 [2, -1, 1] = true := by decide +kernel
theorem subd7_0_313 : subd7_0 [2, -1, 2] = true := by decide +kernel
theorem subd7_0_314 : subd7_0 [2, -1, 3] = true := by decide +kernel
theorem subd7_0_315 : subd7_0 [2, -1, 4] = true := by decide +kernel
theorem subd7_0_316 : subd7_0 [2, -1, 5] = true := by decide +kernel
theorem subd7_0_317 : subd7_0 [2, -1, 6] = true := by decide +kernel
theorem subd7_0_318 : subd7_0 [2, 0, -8] = true := by decide +kernel
theorem subd7_0_319 : subd7_0 [2, 0, -7] = true := by decide +kernel
theorem sbd7_0_9 : ∀ q ∈ blkd7_0_9, subd7_0 q = true := by
  unfold blkd7_0_9
  exact List.forall_mem_cons.2 ⟨subd7_0_288, List.forall_mem_cons.2 ⟨subd7_0_289, List.forall_mem_cons.2 ⟨subd7_0_290, List.forall_mem_cons.2 ⟨subd7_0_291, List.forall_mem_cons.2 ⟨subd7_0_292, List.forall_mem_cons.2 ⟨subd7_0_293, List.forall_mem_cons.2 ⟨subd7_0_294, List.forall_mem_cons.2 ⟨subd7_0_295, List.forall_mem_cons.2 ⟨subd7_0_296, List.forall_mem_cons.2 ⟨subd7_0_297, List.forall_mem_cons.2 ⟨subd7_0_298, List.forall_mem_cons.2 ⟨subd7_0_299, List.forall_mem_cons.2 ⟨subd7_0_300, List.forall_mem_cons.2 ⟨subd7_0_301, List.forall_mem_cons.2 ⟨subd7_0_302, List.forall_mem_cons.2 ⟨subd7_0_303, List.forall_mem_cons.2 ⟨subd7_0_304, List.forall_mem_cons.2 ⟨subd7_0_305, List.forall_mem_cons.2 ⟨subd7_0_306, List.forall_mem_cons.2 ⟨subd7_0_307, List.forall_mem_cons.2 ⟨subd7_0_308, List.forall_mem_cons.2 ⟨subd7_0_309, List.forall_mem_cons.2 ⟨subd7_0_310, List.forall_mem_cons.2 ⟨subd7_0_311, List.forall_mem_cons.2 ⟨subd7_0_312, List.forall_mem_cons.2 ⟨subd7_0_313, List.forall_mem_cons.2 ⟨subd7_0_314, List.forall_mem_cons.2 ⟨subd7_0_315, List.forall_mem_cons.2 ⟨subd7_0_316, List.forall_mem_cons.2 ⟨subd7_0_317, List.forall_mem_cons.2 ⟨subd7_0_318, List.forall_mem_cons.2 ⟨subd7_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C095
