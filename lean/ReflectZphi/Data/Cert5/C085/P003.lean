import ReflectZphi.Data.Cert5.C085.Base

namespace ReflectZphi.Data.Cert5.C085
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_0 : sub7 [-5] = true := by decide +kernel
theorem sub7_1 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_2 : sub7 [-4, -1] = true := by decide +kernel
theorem sub7_3 : sub7 [-4, 0] = true := by decide +kernel
theorem sub7_4 : sub7 [-4, 1] = true := by decide +kernel
theorem sub7_5 : sub7 [-4, 2] = true := by decide +kernel
theorem sub7_6 : sub7 [-4, 3] = true := by decide +kernel
theorem sub7_7 : sub7 [-4, 4] = true := by decide +kernel
theorem sub7_8 : sub7 [-4, 5] = true := by decide +kernel
theorem sub7_9 : sub7 [-3, -3] = true := by decide +kernel
theorem sub7_10 : sub7 [-3, -2] = true := by decide +kernel
theorem sub7_11 : sub7 [-3, -1] = true := by decide +kernel
theorem sub7_12 : sub7 [-3, 0] = true := by decide +kernel
theorem sub7_13 : sub7 [-3, 1] = true := by decide +kernel
theorem sub7_14 : sub7 [-3, 2] = true := by decide +kernel
theorem sub7_15 : sub7 [-3, 3] = true := by decide +kernel
theorem sub7_16 : sub7 [-3, 4] = true := by decide +kernel
theorem sub7_17 : sub7 [-3, 5] = true := by decide +kernel
theorem sub7_18 : sub7 [-2, -4] = true := by decide +kernel
theorem sub7_19 : sub7 [-2, -3] = true := by decide +kernel
theorem sub7_20 : sub7 [-2, -2] = true := by decide +kernel
theorem sub7_21 : sub7 [-2, -1] = true := by decide +kernel
theorem sub7_22 : sub7 [-2, 0] = true := by decide +kernel
theorem sub7_23 : sub7 [-2, 1] = true := by decide +kernel
theorem sub7_24 : sub7 [-2, 2] = true := by decide +kernel
theorem sub7_25 : sub7 [-2, 3] = true := by decide +kernel
theorem sub7_26 : sub7 [-2, 4] = true := by decide +kernel
theorem sub7_27 : sub7 [-2, 5] = true := by decide +kernel
theorem sub7_28 : sub7 [-1, -5] = true := by decide +kernel
theorem sub7_29 : sub7 [-1, -4] = true := by decide +kernel
theorem sub7_30 : sub7 [-1, -3] = true := by decide +kernel
theorem sub7_31 : sub7 [-1, -2] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [-1, -1] = true := by decide +kernel
theorem sub7_33 : sub7 [-1, 0] = true := by decide +kernel
theorem sub7_34 : sub7 [-1, 1] = true := by decide +kernel
theorem sub7_35 : sub7 [-1, 2] = true := by decide +kernel
theorem sub7_36 : sub7 [-1, 3] = true := by decide +kernel
theorem sub7_37 : sub7 [-1, 4] = true := by decide +kernel
theorem sub7_38 : sub7 [-1, 5] = true := by decide +kernel
theorem sub7_39 : sub7 [0, -5] = true := by decide +kernel
theorem sub7_40 : sub7 [0, -4] = true := by decide +kernel
theorem sub7_41 : sub7 [0, -3] = true := by decide +kernel
theorem sub7_42 : sub7 [0, -2] = true := by decide +kernel
theorem sub7_43 : sub7 [0, -1] = true := by decide +kernel
theorem sub7_44 : sub7 [0, 0] = true := by decide +kernel
theorem sub7_45 : sub7 [0, 1] = true := by decide +kernel
theorem sub7_46 : sub7 [0, 2] = true := by decide +kernel
theorem sub7_47 : sub7 [0, 3] = true := by decide +kernel
theorem sub7_48 : sub7 [0, 4] = true := by decide +kernel
theorem sub7_49 : sub7 [1, -6] = true := by decide +kernel
theorem sub7_50 : sub7 [1, -5] = true := by decide +kernel
theorem sub7_51 : sub7 [1, -4] = true := by decide +kernel
theorem sub7_52 : sub7 [1, -3] = true := by decide +kernel
theorem sub7_53 : sub7 [1, -2] = true := by decide +kernel
theorem sub7_54 : sub7 [1, -1] = true := by decide +kernel
theorem sub7_55 : sub7 [1, 0] = true := by decide +kernel
theorem sub7_56 : sub7 [1, 1] = true := by decide +kernel
theorem sub7_57 : sub7 [1, 2] = true := by decide +kernel
theorem sub7_58 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_59 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_60 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_61 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_62 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_63 : sub7 [2, -3] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_cons.2 ⟨sub7_58, List.forall_mem_cons.2 ⟨sub7_59, List.forall_mem_cons.2 ⟨sub7_60, List.forall_mem_cons.2 ⟨sub7_61, List.forall_mem_cons.2 ⟨sub7_62, List.forall_mem_cons.2 ⟨sub7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_64 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_65 : sub7 [2, -1] = true := by decide +kernel
theorem sub7_66 : sub7 [2, 0] = true := by decide +kernel
theorem sub7_67 : sub7 [2, 1] = true := by decide +kernel
theorem sub7_68 : sub7 [2, 2] = true := by decide +kernel
theorem sub7_69 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_70 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_71 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_72 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_73 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_74 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_75 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_76 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_77 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_78 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_79 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_80 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_81 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_82 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_83 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_84 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_85 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_86 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_87 : sub7 [5] = true := by decide +kernel
theorem sb7_2 : ∀ q ∈ blk7_2, sub7 q = true := by
  unfold blk7_2
  exact List.forall_mem_cons.2 ⟨sub7_64, List.forall_mem_cons.2 ⟨sub7_65, List.forall_mem_cons.2 ⟨sub7_66, List.forall_mem_cons.2 ⟨sub7_67, List.forall_mem_cons.2 ⟨sub7_68, List.forall_mem_cons.2 ⟨sub7_69, List.forall_mem_cons.2 ⟨sub7_70, List.forall_mem_cons.2 ⟨sub7_71, List.forall_mem_cons.2 ⟨sub7_72, List.forall_mem_cons.2 ⟨sub7_73, List.forall_mem_cons.2 ⟨sub7_74, List.forall_mem_cons.2 ⟨sub7_75, List.forall_mem_cons.2 ⟨sub7_76, List.forall_mem_cons.2 ⟨sub7_77, List.forall_mem_cons.2 ⟨sub7_78, List.forall_mem_cons.2 ⟨sub7_79, List.forall_mem_cons.2 ⟨sub7_80, List.forall_mem_cons.2 ⟨sub7_81, List.forall_mem_cons.2 ⟨sub7_82, List.forall_mem_cons.2 ⟨sub7_83, List.forall_mem_cons.2 ⟨sub7_84, List.forall_mem_cons.2 ⟨sub7_85, List.forall_mem_cons.2 ⟨sub7_86, List.forall_mem_cons.2 ⟨sub7_87, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-4, -3] = true := by decide +kernel
theorem sub8_1 : sub8 [-4, -2] = true := by decide +kernel
theorem sub8_2 : sub8 [-4, -1] = true := by decide +kernel
theorem sub8_3 : sub8 [-4, 0] = true := by decide +kernel
theorem sub8_4 : sub8 [-4, 1] = true := by decide +kernel
theorem sub8_5 : sub8 [-4, 2] = true := by decide +kernel
theorem sub8_6 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_7 : sub8 [-4, 4] = true := by decide +kernel
theorem sub8_8 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_9 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_10 : sub8 [-3, -2] = true := by decide +kernel
theorem sub8_11 : sub8 [-3, -1] = true := by decide +kernel
theorem sub8_12 : sub8 [-3, 0] = true := by decide +kernel
theorem sub8_13 : sub8 [-3, 1] = true := by decide +kernel
theorem sub8_14 : sub8 [-3, 2] = true := by decide +kernel
theorem sub8_15 : sub8 [-3, 3] = true := by decide +kernel
theorem sub8_16 : sub8 [-3, 4] = true := by decide +kernel
theorem sub8_17 : sub8 [-3, 5] = true := by decide +kernel
theorem sub8_18 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_19 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_20 : sub8 [-2, -3] = true := by decide +kernel
theorem sub8_21 : sub8 [-2, -2] = true := by decide +kernel
theorem sub8_22 : sub8 [-2, -1] = true := by decide +kernel
theorem sub8_23 : sub8 [-2, 0] = true := by decide +kernel
theorem sub8_24 : sub8 [-2, 1] = true := by decide +kernel
theorem sub8_25 : sub8 [-2, 2] = true := by decide +kernel
theorem sub8_26 : sub8 [-2, 3] = true := by decide +kernel
theorem sub8_27 : sub8 [-2, 4] = true := by decide +kernel
theorem sub8_28 : sub8 [-2, 5] = true := by decide +kernel
theorem sub8_29 : sub8 [-1, -6] = true := by decide +kernel
theorem sub8_30 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_31 : sub8 [-1, -4] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-1, -3] = true := by decide +kernel
theorem sub8_33 : sub8 [-1, -2] = true := by decide +kernel
theorem sub8_34 : sub8 [-1, -1] = true := by decide +kernel
theorem sub8_35 : sub8 [-1, 0] = true := by decide +kernel
theorem sub8_36 : sub8 [-1, 1] = true := by decide +kernel
theorem sub8_37 : sub8 [-1, 2] = true := by decide +kernel
theorem sub8_38 : sub8 [-1, 3] = true := by decide +kernel
theorem sub8_39 : sub8 [-1, 4] = true := by decide +kernel
theorem sub8_40 : sub8 [-1, 5] = true := by decide +kernel
theorem sub8_41 : sub8 [0, -6] = true := by decide +kernel
theorem sub8_42 : sub8 [0, -5] = true := by decide +kernel
theorem sub8_43 : sub8 [0, -4] = true := by decide +kernel
theorem sub8_44 : sub8 [0, -3] = true := by decide +kernel
theorem sub8_45 : sub8 [0, -2] = true := by decide +kernel
theorem sub8_46 : sub8 [0, -1] = true := by decide +kernel
theorem sub8_47 : sub8 [0, 0] = true := by decide +kernel
theorem sub8_48 : sub8 [0, 1] = true := by decide +kernel
theorem sub8_49 : sub8 [0, 2] = true := by decide +kernel
theorem sub8_50 : sub8 [0, 3] = true := by decide +kernel
theorem sub8_51 : sub8 [0, 4] = true := by decide +kernel
theorem sub8_52 : sub8 [0, 5] = true := by decide +kernel
theorem sub8_53 : sub8 [1, -6] = true := by decide +kernel
theorem sub8_54 : sub8 [1, -5] = true := by decide +kernel
theorem sub8_55 : sub8 [1, -4] = true := by decide +kernel
theorem sub8_56 : sub8 [1, -3] = true := by decide +kernel
theorem sub8_57 : sub8 [1, -2] = true := by decide +kernel
theorem sub8_58 : sub8 [1, -1] = true := by decide +kernel
theorem sub8_59 : sub8 [1, 0] = true := by decide +kernel
theorem sub8_60 : sub8 [1, 1] = true := by decide +kernel
theorem sub8_61 : sub8 [1, 2] = true := by decide +kernel
theorem sub8_62 : sub8 [1, 3] = true := by decide +kernel
theorem sub8_63 : sub8 [1, 4] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C085
