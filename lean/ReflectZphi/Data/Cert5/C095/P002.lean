import ReflectZphi.Data.Cert5.C095.Base

namespace ReflectZphi.Data.Cert5.C095

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_0 : subd6_0 [-3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-2, -4] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-2, -3] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-2, -2] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-2, -1] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-2, 0] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-2, 1] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-2, 2] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-1, -4] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [0, 0, -7] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [0, 0, -6] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [0, 0, -5] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [0, 0, -4] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [0, 0, -3] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [0, 0, -2] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [0, 0, -1] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [0, 0, 0] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [0, 0, 1] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [0, 0, 2] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [0, 0, 3] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [0, 0, 4] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_32 : subd6_0 [0, 0, 5] = true := by decide +kernel
theorem subd6_0_33 : subd6_0 [0, 0, 6] = true := by decide +kernel
theorem subd6_0_34 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_35 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_36 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_37 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_38 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_39 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_40 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_41 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_42 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_43 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_44 : subd6_0 [1, 3] = true := by decide +kernel
theorem subd6_0_45 : subd6_0 [2, -3] = true := by decide +kernel
theorem subd6_0_46 : subd6_0 [2, -2] = true := by decide +kernel
theorem subd6_0_47 : subd6_0 [2, -1] = true := by decide +kernel
theorem subd6_0_48 : subd6_0 [2, 0] = true := by decide +kernel
theorem subd6_0_49 : subd6_0 [2, 1] = true := by decide +kernel
theorem subd6_0_50 : subd6_0 [2, 2] = true := by decide +kernel
theorem subd6_0_51 : subd6_0 [2, 3] = true := by decide +kernel
theorem subd6_0_52 : subd6_0 [3] = true := by decide +kernel
theorem sbd6_0_1 : ∀ q ∈ blkd6_0_1, subd6_0 q = true := by
  unfold blkd6_0_1
  exact List.forall_mem_cons.2 ⟨subd6_0_32, List.forall_mem_cons.2 ⟨subd6_0_33, List.forall_mem_cons.2 ⟨subd6_0_34, List.forall_mem_cons.2 ⟨subd6_0_35, List.forall_mem_cons.2 ⟨subd6_0_36, List.forall_mem_cons.2 ⟨subd6_0_37, List.forall_mem_cons.2 ⟨subd6_0_38, List.forall_mem_cons.2 ⟨subd6_0_39, List.forall_mem_cons.2 ⟨subd6_0_40, List.forall_mem_cons.2 ⟨subd6_0_41, List.forall_mem_cons.2 ⟨subd6_0_42, List.forall_mem_cons.2 ⟨subd6_0_43, List.forall_mem_cons.2 ⟨subd6_0_44, List.forall_mem_cons.2 ⟨subd6_0_45, List.forall_mem_cons.2 ⟨subd6_0_46, List.forall_mem_cons.2 ⟨subd6_0_47, List.forall_mem_cons.2 ⟨subd6_0_48, List.forall_mem_cons.2 ⟨subd6_0_49, List.forall_mem_cons.2 ⟨subd6_0_50, List.forall_mem_cons.2 ⟨subd6_0_51, List.forall_mem_cons.2 ⟨subd6_0_52, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_0 : subd6_1 [-4] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-3, -5] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-3, -4] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-3, -3] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-3, -2] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-3, -1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-3, 0] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-3, 1] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-3, 2] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-3, 3] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-2, -6] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-2, -5] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [-2, -4] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [-2, -3] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [-2, -1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [-2, 0] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [-2, 1] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [-2, 2] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [-2, 3] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [-2, 4] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [-1, -6] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [-1, -5] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [-1, 3] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [-1, 4] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [-1, 5] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [0, -6] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [0, -5] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_40 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_41 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_42 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_43 : subd6_1 [0, 4] = true := by decide +kernel
theorem subd6_1_44 : subd6_1 [0, 5] = true := by decide +kernel
theorem subd6_1_45 : subd6_1 [1, -6] = true := by decide +kernel
theorem subd6_1_46 : subd6_1 [1, -5] = true := by decide +kernel
theorem subd6_1_47 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_48 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_49 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_50 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_51 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_52 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_53 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_54 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_55 : subd6_1 [1, 4] = true := by decide +kernel
theorem subd6_1_56 : subd6_1 [1, 5] = true := by decide +kernel
theorem subd6_1_57 : subd6_1 [2, -5] = true := by decide +kernel
theorem subd6_1_58 : subd6_1 [2, -4] = true := by decide +kernel
theorem subd6_1_59 : subd6_1 [2, -3] = true := by decide +kernel
theorem subd6_1_60 : subd6_1 [2, -2] = true := by decide +kernel
theorem subd6_1_61 : subd6_1 [2, -1] = true := by decide +kernel
theorem subd6_1_62 : subd6_1 [2, 0] = true := by decide +kernel
theorem subd6_1_63 : subd6_1 [2, 1] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_cons.2 ⟨subd6_1_40, List.forall_mem_cons.2 ⟨subd6_1_41, List.forall_mem_cons.2 ⟨subd6_1_42, List.forall_mem_cons.2 ⟨subd6_1_43, List.forall_mem_cons.2 ⟨subd6_1_44, List.forall_mem_cons.2 ⟨subd6_1_45, List.forall_mem_cons.2 ⟨subd6_1_46, List.forall_mem_cons.2 ⟨subd6_1_47, List.forall_mem_cons.2 ⟨subd6_1_48, List.forall_mem_cons.2 ⟨subd6_1_49, List.forall_mem_cons.2 ⟨subd6_1_50, List.forall_mem_cons.2 ⟨subd6_1_51, List.forall_mem_cons.2 ⟨subd6_1_52, List.forall_mem_cons.2 ⟨subd6_1_53, List.forall_mem_cons.2 ⟨subd6_1_54, List.forall_mem_cons.2 ⟨subd6_1_55, List.forall_mem_cons.2 ⟨subd6_1_56, List.forall_mem_cons.2 ⟨subd6_1_57, List.forall_mem_cons.2 ⟨subd6_1_58, List.forall_mem_cons.2 ⟨subd6_1_59, List.forall_mem_cons.2 ⟨subd6_1_60, List.forall_mem_cons.2 ⟨subd6_1_61, List.forall_mem_cons.2 ⟨subd6_1_62, List.forall_mem_cons.2 ⟨subd6_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_64 : subd6_1 [2, 2] = true := by decide +kernel
theorem subd6_1_65 : subd6_1 [2, 3] = true := by decide +kernel
theorem subd6_1_66 : subd6_1 [2, 4] = true := by decide +kernel
theorem subd6_1_67 : subd6_1 [2, 5] = true := by decide +kernel
theorem subd6_1_68 : subd6_1 [3, -4] = true := by decide +kernel
theorem subd6_1_69 : subd6_1 [3, -3] = true := by decide +kernel
theorem subd6_1_70 : subd6_1 [3, -2] = true := by decide +kernel
theorem subd6_1_71 : subd6_1 [3, -1] = true := by decide +kernel
theorem subd6_1_72 : subd6_1 [3, 0] = true := by decide +kernel
theorem subd6_1_73 : subd6_1 [3, 1] = true := by decide +kernel
theorem subd6_1_74 : subd6_1 [3, 2] = true := by decide +kernel
theorem subd6_1_75 : subd6_1 [3, 3] = true := by decide +kernel
theorem subd6_1_76 : subd6_1 [3, 4] = true := by decide +kernel
theorem subd6_1_77 : subd6_1 [4] = true := by decide +kernel
theorem sbd6_1_2 : ∀ q ∈ blkd6_1_2, subd6_1 q = true := by
  unfold blkd6_1_2
  exact List.forall_mem_cons.2 ⟨subd6_1_64, List.forall_mem_cons.2 ⟨subd6_1_65, List.forall_mem_cons.2 ⟨subd6_1_66, List.forall_mem_cons.2 ⟨subd6_1_67, List.forall_mem_cons.2 ⟨subd6_1_68, List.forall_mem_cons.2 ⟨subd6_1_69, List.forall_mem_cons.2 ⟨subd6_1_70, List.forall_mem_cons.2 ⟨subd6_1_71, List.forall_mem_cons.2 ⟨subd6_1_72, List.forall_mem_cons.2 ⟨subd6_1_73, List.forall_mem_cons.2 ⟨subd6_1_74, List.forall_mem_cons.2 ⟨subd6_1_75, List.forall_mem_cons.2 ⟨subd6_1_76, List.forall_mem_cons.2 ⟨subd6_1_77, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C095
