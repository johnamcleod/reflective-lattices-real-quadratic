import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_736 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_737 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_738 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_739 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_740 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_741 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_742 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_743 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_744 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_745 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_746 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_747 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_748 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_749 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_750 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_751 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_752 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_753 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_754 : sub5 [6] = true := by decide +kernel
theorem sb5_23 : ∀ q ∈ blk5_23, sub5 q = true := by
  unfold blk5_23
  exact List.forall_mem_cons.2 ⟨sub5_736, List.forall_mem_cons.2 ⟨sub5_737, List.forall_mem_cons.2 ⟨sub5_738, List.forall_mem_cons.2 ⟨sub5_739, List.forall_mem_cons.2 ⟨sub5_740, List.forall_mem_cons.2 ⟨sub5_741, List.forall_mem_cons.2 ⟨sub5_742, List.forall_mem_cons.2 ⟨sub5_743, List.forall_mem_cons.2 ⟨sub5_744, List.forall_mem_cons.2 ⟨sub5_745, List.forall_mem_cons.2 ⟨sub5_746, List.forall_mem_cons.2 ⟨sub5_747, List.forall_mem_cons.2 ⟨sub5_748, List.forall_mem_cons.2 ⟨sub5_749, List.forall_mem_cons.2 ⟨sub5_750, List.forall_mem_cons.2 ⟨sub5_751, List.forall_mem_cons.2 ⟨sub5_752, List.forall_mem_cons.2 ⟨sub5_753, List.forall_mem_cons.2 ⟨sub5_754, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-5] = true := by decide +kernel
theorem sub6_1 : sub6 [-4, -2] = true := by decide +kernel
theorem sub6_2 : sub6 [-4, -1] = true := by decide +kernel
theorem sub6_3 : sub6 [-4, 0] = true := by decide +kernel
theorem sub6_4 : sub6 [-4, 1] = true := by decide +kernel
theorem sub6_5 : sub6 [-4, 2] = true := by decide +kernel
theorem sub6_6 : sub6 [-4, 3] = true := by decide +kernel
theorem sub6_7 : sub6 [-4, 4] = true := by decide +kernel
theorem sub6_8 : sub6 [-4, 5] = true := by decide +kernel
theorem sub6_9 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_10 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_11 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_12 : sub6 [-3, -1] = true := by decide +kernel
theorem sub6_13 : sub6 [-3, 0] = true := by decide +kernel
theorem sub6_14 : sub6 [-3, 1] = true := by decide +kernel
theorem sub6_15 : sub6 [-3, 2] = true := by decide +kernel
theorem sub6_16 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_17 : sub6 [-3, 4] = true := by decide +kernel
theorem sub6_18 : sub6 [-3, 5] = true := by decide +kernel
theorem sub6_19 : sub6 [-3, 6] = true := by decide +kernel
theorem sub6_20 : sub6 [-2, -5] = true := by decide +kernel
theorem sub6_21 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_22 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_23 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_24 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_25 : sub6 [-2, 0] = true := by decide +kernel
theorem sub6_26 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_27 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_28 : sub6 [-2, 3] = true := by decide +kernel
theorem sub6_29 : sub6 [-2, 4] = true := by decide +kernel
theorem sub6_30 : sub6 [-2, 5] = true := by decide +kernel
theorem sub6_31 : sub6 [-2, 6] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-1, -6] = true := by decide +kernel
theorem sub6_33 : sub6 [-1, -5] = true := by decide +kernel
theorem sub6_34 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_35 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_36 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_37 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_38 : sub6 [-1, 0] = true := by decide +kernel
theorem sub6_39 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_40 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_41 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_42 : sub6 [-1, 4] = true := by decide +kernel
theorem sub6_43 : sub6 [-1, 5] = true := by decide +kernel
theorem sub6_44 : sub6 [-1, 6] = true := by decide +kernel
theorem sub6_45 : sub6 [0, -6] = true := by decide +kernel
theorem sub6_46 : sub6 [0, -5] = true := by decide +kernel
theorem sub6_47 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_48 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_49 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_50 : sub6 [0, -1] = true := by decide +kernel
theorem sub6_51 : sub6 [0, 0] = true := by decide +kernel
theorem sub6_52 : sub6 [0, 1] = true := by decide +kernel
theorem sub6_53 : sub6 [0, 2] = true := by decide +kernel
theorem sub6_54 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_55 : sub6 [0, 4] = true := by decide +kernel
theorem sub6_56 : sub6 [0, 5] = true := by decide +kernel
theorem sub6_57 : sub6 [1, -7] = true := by decide +kernel
theorem sub6_58 : sub6 [1, -6] = true := by decide +kernel
theorem sub6_59 : sub6 [1, -5] = true := by decide +kernel
theorem sub6_60 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_61 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_62 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_63 : sub6 [1, -1] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [1, 0] = true := by decide +kernel
theorem sub6_65 : sub6 [1, 1] = true := by decide +kernel
theorem sub6_66 : sub6 [1, 2] = true := by decide +kernel
theorem sub6_67 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_68 : sub6 [1, 4] = true := by decide +kernel
theorem sub6_69 : sub6 [1, 5] = true := by decide +kernel
theorem sub6_70 : sub6 [2, -7] = true := by decide +kernel
theorem sub6_71 : sub6 [2, -6] = true := by decide +kernel
theorem sub6_72 : sub6 [2, -5] = true := by decide +kernel
theorem sub6_73 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_74 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_75 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_76 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_77 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_78 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_79 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_80 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_81 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_82 : sub6 [3, -7] = true := by decide +kernel
theorem sub6_83 : sub6 [3, -6] = true := by decide +kernel
theorem sub6_84 : sub6 [3, -5] = true := by decide +kernel
theorem sub6_85 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_86 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_87 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_88 : sub6 [3, -1] = true := by decide +kernel
theorem sub6_89 : sub6 [3, 0] = true := by decide +kernel
theorem sub6_90 : sub6 [3, 1] = true := by decide +kernel
theorem sub6_91 : sub6 [3, 2] = true := by decide +kernel
theorem sub6_92 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_93 : sub6 [4, -6] = true := by decide +kernel
theorem sub6_94 : sub6 [4, -5] = true := by decide +kernel
theorem sub6_95 : sub6 [4, -4] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [4, -3] = true := by decide +kernel
theorem sub6_97 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_98 : sub6 [4, -1] = true := by decide +kernel
theorem sub6_99 : sub6 [4, 0] = true := by decide +kernel
theorem sub6_100 : sub6 [4, 1] = true := by decide +kernel
theorem sub6_101 : sub6 [5] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
