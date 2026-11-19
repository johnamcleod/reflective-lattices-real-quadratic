import ReflectZphi.Data.Cert5.C097.Base

namespace ReflectZphi.Data.Cert5.C097
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_0 : sub5 [-6] = true := by decide +kernel
theorem sub5_1 : sub5 [-5, -7] = true := by decide +kernel
theorem sub5_2 : sub5 [-5, -6] = true := by decide +kernel
theorem sub5_3 : sub5 [-5, -5] = true := by decide +kernel
theorem sub5_4 : sub5 [-5, -4] = true := by decide +kernel
theorem sub5_5 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_6 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_7 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_8 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_9 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_10 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_11 : sub5 [-4, -7] = true := by decide +kernel
theorem sub5_12 : sub5 [-4, -6] = true := by decide +kernel
theorem sub5_13 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_14 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_15 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_16 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_17 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_18 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_19 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_20 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_21 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_22 : sub5 [-3, -8] = true := by decide +kernel
theorem sub5_23 : sub5 [-3, -7] = true := by decide +kernel
theorem sub5_24 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_25 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_26 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_27 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_28 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_29 : sub5 [-3, -1] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, 0] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, 1] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, 3] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, 4] = true := by decide +kernel
theorem sub5_35 : sub5 [-2, -8] = true := by decide +kernel
theorem sub5_36 : sub5 [-2, -7] = true := by decide +kernel
theorem sub5_37 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_38 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_39 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_40 : sub5 [-2, -3] = true := by decide +kernel
theorem sub5_41 : sub5 [-2, -2] = true := by decide +kernel
theorem sub5_42 : sub5 [-2, -1] = true := by decide +kernel
theorem sub5_43 : sub5 [-2, 0] = true := by decide +kernel
theorem sub5_44 : sub5 [-2, 1] = true := by decide +kernel
theorem sub5_45 : sub5 [-2, 2] = true := by decide +kernel
theorem sub5_46 : sub5 [-2, 3] = true := by decide +kernel
theorem sub5_47 : sub5 [-2, 4] = true := by decide +kernel
theorem sub5_48 : sub5 [-2, 5] = true := by decide +kernel
theorem sub5_49 : sub5 [-1, -7] = true := by decide +kernel
theorem sub5_50 : sub5 [-1, -6] = true := by decide +kernel
theorem sub5_51 : sub5 [-1, -5] = true := by decide +kernel
theorem sub5_52 : sub5 [-1, -4] = true := by decide +kernel
theorem sub5_53 : sub5 [-1, -3] = true := by decide +kernel
theorem sub5_54 : sub5 [-1, -2] = true := by decide +kernel
theorem sub5_55 : sub5 [-1, -1] = true := by decide +kernel
theorem sub5_56 : sub5 [-1, 0] = true := by decide +kernel
theorem sub5_57 : sub5 [-1, 1] = true := by decide +kernel
theorem sub5_58 : sub5 [-1, 2] = true := by decide +kernel
theorem sub5_59 : sub5 [-1, 3] = true := by decide +kernel
theorem sub5_60 : sub5 [-1, 4] = true := by decide +kernel
theorem sub5_61 : sub5 [-1, 5] = true := by decide +kernel
theorem sub5_62 : sub5 [-1, 6] = true := by decide +kernel
theorem sub5_63 : sub5 [0, -7] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [0, -6] = true := by decide +kernel
theorem sub5_65 : sub5 [0, -5] = true := by decide +kernel
theorem sub5_66 : sub5 [0, -4] = true := by decide +kernel
theorem sub5_67 : sub5 [0, -3] = true := by decide +kernel
theorem sub5_68 : sub5 [0, -2] = true := by decide +kernel
theorem sub5_69 : sub5 [0, -1] = true := by decide +kernel
theorem sub5_70 : sub5 [0, 0] = true := by decide +kernel
theorem sub5_71 : sub5 [0, 1] = true := by decide +kernel
theorem sub5_72 : sub5 [0, 2] = true := by decide +kernel
theorem sub5_73 : sub5 [0, 3] = true := by decide +kernel
theorem sub5_74 : sub5 [0, 4] = true := by decide +kernel
theorem sub5_75 : sub5 [0, 5] = true := by decide +kernel
theorem sub5_76 : sub5 [0, 6] = true := by decide +kernel
theorem sub5_77 : sub5 [1, -7] = true := by decide +kernel
theorem sub5_78 : sub5 [1, -6] = true := by decide +kernel
theorem sub5_79 : sub5 [1, -5] = true := by decide +kernel
theorem sub5_80 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_81 : sub5 [1, -3] = true := by decide +kernel
theorem sub5_82 : sub5 [1, -2] = true := by decide +kernel
theorem sub5_83 : sub5 [1, -1] = true := by decide +kernel
theorem sub5_84 : sub5 [1, 0] = true := by decide +kernel
theorem sub5_85 : sub5 [1, 1] = true := by decide +kernel
theorem sub5_86 : sub5 [1, 2] = true := by decide +kernel
theorem sub5_87 : sub5 [1, 3] = true := by decide +kernel
theorem sub5_88 : sub5 [1, 4] = true := by decide +kernel
theorem sub5_89 : sub5 [1, 5] = true := by decide +kernel
theorem sub5_90 : sub5 [1, 6] = true := by decide +kernel
theorem sub5_91 : sub5 [2, -6] = true := by decide +kernel
theorem sub5_92 : sub5 [2, -5] = true := by decide +kernel
theorem sub5_93 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_94 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_95 : sub5 [2, -2] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C097
