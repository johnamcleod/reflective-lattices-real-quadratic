import ReflectZphi.Data.Cert5.C095.Base

namespace ReflectZphi.Data.Cert5.C095

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_32 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [0, 4] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [1, -5] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [1, 4] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [2, -5] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [2, 4] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [3, -4] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [3, -3] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [3, 0] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [3, 1] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [3, 2] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [3, 3] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [4] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_nil _⟩⟩⟩⟩
theorem subd8_2_0 : subd8_2 [-2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [1, 1] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [2] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_0 : subd8_3 [-2] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [2] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_0 : subd8_4 [-1] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [0] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [1] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_nil _⟩⟩⟩
theorem subd8_5_0 : subd8_5 [] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_nil _⟩
theorem subd8_6_0 : subd8_6 [] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_nil _⟩
theorem subd9_0_0 : subd9_0 [-3] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-2, -4] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-2, -3] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-2, -2] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-2, -1] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-2, 0] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-2, 1] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-1, -4] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-1, -2] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-1, -1] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-1, 0] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-1, 1] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-1, 2] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [0, -4] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [0, 0, -7] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [0, 0, -6] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [0, 0, -5] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [0, 0, -4] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [0, 0, -3] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [0, 0, -2] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [0, 0, -1] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [0, 0, 0] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [0, 0, 1] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [0, 0, 2] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [0, 0, 3] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [0, 0, 4] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [0, 0, 5] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [0, 0, 6] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_32 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_33 : subd9_0 [0, 2] = true := by decide +kernel
theorem subd9_0_34 : subd9_0 [0, 3] = true := by decide +kernel
theorem subd9_0_35 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_36 : subd9_0 [1, -2] = true := by decide +kernel
theorem subd9_0_37 : subd9_0 [1, -1] = true := by decide +kernel
theorem subd9_0_38 : subd9_0 [1, 0] = true := by decide +kernel
theorem subd9_0_39 : subd9_0 [1, 1] = true := by decide +kernel
theorem subd9_0_40 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_41 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_42 : subd9_0 [2, -2] = true := by decide +kernel
theorem subd9_0_43 : subd9_0 [2, -1] = true := by decide +kernel
theorem subd9_0_44 : subd9_0 [2, 0] = true := by decide +kernel
theorem subd9_0_45 : subd9_0 [2, 1] = true := by decide +kernel
theorem subd9_0_46 : subd9_0 [2, 2] = true := by decide +kernel
theorem subd9_0_47 : subd9_0 [2, 3] = true := by decide +kernel
theorem subd9_0_48 : subd9_0 [3] = true := by decide +kernel
theorem sbd9_0_1 : ∀ q ∈ blkd9_0_1, subd9_0 q = true := by
  unfold blkd9_0_1
  exact List.forall_mem_cons.2 ⟨subd9_0_32, List.forall_mem_cons.2 ⟨subd9_0_33, List.forall_mem_cons.2 ⟨subd9_0_34, List.forall_mem_cons.2 ⟨subd9_0_35, List.forall_mem_cons.2 ⟨subd9_0_36, List.forall_mem_cons.2 ⟨subd9_0_37, List.forall_mem_cons.2 ⟨subd9_0_38, List.forall_mem_cons.2 ⟨subd9_0_39, List.forall_mem_cons.2 ⟨subd9_0_40, List.forall_mem_cons.2 ⟨subd9_0_41, List.forall_mem_cons.2 ⟨subd9_0_42, List.forall_mem_cons.2 ⟨subd9_0_43, List.forall_mem_cons.2 ⟨subd9_0_44, List.forall_mem_cons.2 ⟨subd9_0_45, List.forall_mem_cons.2 ⟨subd9_0_46, List.forall_mem_cons.2 ⟨subd9_0_47, List.forall_mem_cons.2 ⟨subd9_0_48, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C095
