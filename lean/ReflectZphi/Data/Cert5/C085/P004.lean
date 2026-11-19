import ReflectZphi.Data.Cert5.C085.Base

namespace ReflectZphi.Data.Cert5.C085
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_64 : sub8 [1, 5] = true := by decide +kernel
theorem sub8_65 : sub8 [2, -6] = true := by decide +kernel
theorem sub8_66 : sub8 [2, -5] = true := by decide +kernel
theorem sub8_67 : sub8 [2, -4] = true := by decide +kernel
theorem sub8_68 : sub8 [2, -3] = true := by decide +kernel
theorem sub8_69 : sub8 [2, -2] = true := by decide +kernel
theorem sub8_70 : sub8 [2, -1] = true := by decide +kernel
theorem sub8_71 : sub8 [2, 0] = true := by decide +kernel
theorem sub8_72 : sub8 [2, 1] = true := by decide +kernel
theorem sub8_73 : sub8 [2, 2] = true := by decide +kernel
theorem sub8_74 : sub8 [2, 3] = true := by decide +kernel
theorem sub8_75 : sub8 [2, 4] = true := by decide +kernel
theorem sub8_76 : sub8 [3, -6] = true := by decide +kernel
theorem sub8_77 : sub8 [3, -5] = true := by decide +kernel
theorem sub8_78 : sub8 [3, -4] = true := by decide +kernel
theorem sub8_79 : sub8 [3, -3] = true := by decide +kernel
theorem sub8_80 : sub8 [3, -2] = true := by decide +kernel
theorem sub8_81 : sub8 [3, -1] = true := by decide +kernel
theorem sub8_82 : sub8 [3, 0] = true := by decide +kernel
theorem sub8_83 : sub8 [3, 1] = true := by decide +kernel
theorem sub8_84 : sub8 [3, 2] = true := by decide +kernel
theorem sub8_85 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_86 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_87 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_88 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_89 : sub8 [4, -2] = true := by decide +kernel
theorem sub8_90 : sub8 [4, -1] = true := by decide +kernel
theorem sub8_91 : sub8 [4, 0] = true := by decide +kernel
theorem sub8_92 : sub8 [4, 1] = true := by decide +kernel
theorem sub8_93 : sub8 [4, 2] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-4] = true := by decide +kernel
theorem sub9_1 : sub9 [-3, -4] = true := by decide +kernel
theorem sub9_2 : sub9 [-3, -3] = true := by decide +kernel
theorem sub9_3 : sub9 [-3, -2] = true := by decide +kernel
theorem sub9_4 : sub9 [-3, -1] = true := by decide +kernel
theorem sub9_5 : sub9 [-3, 0] = true := by decide +kernel
theorem sub9_6 : sub9 [-3, 1] = true := by decide +kernel
theorem sub9_7 : sub9 [-3, 2] = true := by decide +kernel
theorem sub9_8 : sub9 [-3, 3] = true := by decide +kernel
theorem sub9_9 : sub9 [-2, -4] = true := by decide +kernel
theorem sub9_10 : sub9 [-2, -3] = true := by decide +kernel
theorem sub9_11 : sub9 [-2, -2] = true := by decide +kernel
theorem sub9_12 : sub9 [-2, -1] = true := by decide +kernel
theorem sub9_13 : sub9 [-2, 0] = true := by decide +kernel
theorem sub9_14 : sub9 [-2, 1] = true := by decide +kernel
theorem sub9_15 : sub9 [-2, 2] = true := by decide +kernel
theorem sub9_16 : sub9 [-2, 3] = true := by decide +kernel
theorem sub9_17 : sub9 [-1, -5] = true := by decide +kernel
theorem sub9_18 : sub9 [-1, -4] = true := by decide +kernel
theorem sub9_19 : sub9 [-1, -3] = true := by decide +kernel
theorem sub9_20 : sub9 [-1, -2] = true := by decide +kernel
theorem sub9_21 : sub9 [-1, -1] = true := by decide +kernel
theorem sub9_22 : sub9 [-1, 0] = true := by decide +kernel
theorem sub9_23 : sub9 [-1, 1] = true := by decide +kernel
theorem sub9_24 : sub9 [-1, 2] = true := by decide +kernel
theorem sub9_25 : sub9 [-1, 3] = true := by decide +kernel
theorem sub9_26 : sub9 [-1, 4] = true := by decide +kernel
theorem sub9_27 : sub9 [0, -5] = true := by decide +kernel
theorem sub9_28 : sub9 [0, -4] = true := by decide +kernel
theorem sub9_29 : sub9 [0, -3] = true := by decide +kernel
theorem sub9_30 : sub9 [0, -2] = true := by decide +kernel
theorem sub9_31 : sub9 [0, -1] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_32 : sub9 [0, 0] = true := by decide +kernel
theorem sub9_33 : sub9 [0, 1] = true := by decide +kernel
theorem sub9_34 : sub9 [0, 2] = true := by decide +kernel
theorem sub9_35 : sub9 [0, 3] = true := by decide +kernel
theorem sub9_36 : sub9 [0, 4] = true := by decide +kernel
theorem sub9_37 : sub9 [1, -5] = true := by decide +kernel
theorem sub9_38 : sub9 [1, -4] = true := by decide +kernel
theorem sub9_39 : sub9 [1, -3] = true := by decide +kernel
theorem sub9_40 : sub9 [1, -2] = true := by decide +kernel
theorem sub9_41 : sub9 [1, -1] = true := by decide +kernel
theorem sub9_42 : sub9 [1, 0] = true := by decide +kernel
theorem sub9_43 : sub9 [1, 1] = true := by decide +kernel
theorem sub9_44 : sub9 [1, 2] = true := by decide +kernel
theorem sub9_45 : sub9 [1, 3] = true := by decide +kernel
theorem sub9_46 : sub9 [1, 4] = true := by decide +kernel
theorem sub9_47 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_48 : sub9 [2, -3] = true := by decide +kernel
theorem sub9_49 : sub9 [2, -2] = true := by decide +kernel
theorem sub9_50 : sub9 [2, -1] = true := by decide +kernel
theorem sub9_51 : sub9 [2, 0] = true := by decide +kernel
theorem sub9_52 : sub9 [2, 1] = true := by decide +kernel
theorem sub9_53 : sub9 [2, 2] = true := by decide +kernel
theorem sub9_54 : sub9 [2, 3] = true := by decide +kernel
theorem sub9_55 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_56 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_57 : sub9 [3, -2] = true := by decide +kernel
theorem sub9_58 : sub9 [3, -1] = true := by decide +kernel
theorem sub9_59 : sub9 [3, 0] = true := by decide +kernel
theorem sub9_60 : sub9 [3, 1] = true := by decide +kernel
theorem sub9_61 : sub9 [3, 2] = true := by decide +kernel
theorem sub9_62 : sub9 [3, 3] = true := by decide +kernel
theorem sub9_63 : sub9 [4] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-2] = true := by decide +kernel
theorem sub10_1 : sub10 [-1, -2] = true := by decide +kernel
theorem sub10_2 : sub10 [-1, -1] = true := by decide +kernel
theorem sub10_3 : sub10 [-1, 0] = true := by decide +kernel
theorem sub10_4 : sub10 [-1, 1] = true := by decide +kernel
theorem sub10_5 : sub10 [-1, 2] = true := by decide +kernel
theorem sub10_6 : sub10 [0, -3] = true := by decide +kernel
theorem sub10_7 : sub10 [0, -2] = true := by decide +kernel
theorem sub10_8 : sub10 [0, -1] = true := by decide +kernel
theorem sub10_9 : sub10 [0, 0] = true := by decide +kernel
theorem sub10_10 : sub10 [0, 1] = true := by decide +kernel
theorem sub10_11 : sub10 [0, 2] = true := by decide +kernel
theorem sub10_12 : sub10 [1, -3] = true := by decide +kernel
theorem sub10_13 : sub10 [1, -2] = true := by decide +kernel
theorem sub10_14 : sub10 [1, -1] = true := by decide +kernel
theorem sub10_15 : sub10 [1, 0] = true := by decide +kernel
theorem sub10_16 : sub10 [1, 1] = true := by decide +kernel
theorem sub10_17 : sub10 [2] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C085
