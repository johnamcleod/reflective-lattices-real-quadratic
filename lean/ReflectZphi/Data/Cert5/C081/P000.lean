import ReflectZphi.Data.Cert5.C081.Base

namespace ReflectZphi.Data.Cert5.C081
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-3] = true := by decide +kernel
theorem sub0_1 : sub0 [-2, -4] = true := by decide +kernel
theorem sub0_2 : sub0 [-2, -3] = true := by decide +kernel
theorem sub0_3 : sub0 [-2, -2] = true := by decide +kernel
theorem sub0_4 : sub0 [-2, -1] = true := by decide +kernel
theorem sub0_5 : sub0 [-2, 0] = true := by decide +kernel
theorem sub0_6 : sub0 [-2, 1] = true := by decide +kernel
theorem sub0_7 : sub0 [-2, 2] = true := by decide +kernel
theorem sub0_8 : sub0 [-1, -4] = true := by decide +kernel
theorem sub0_9 : sub0 [-1, -3] = true := by decide +kernel
theorem sub0_10 : sub0 [-1, -2] = true := by decide +kernel
theorem sub0_11 : sub0 [-1, -1] = true := by decide +kernel
theorem sub0_12 : sub0 [-1, 0] = true := by decide +kernel
theorem sub0_13 : sub0 [-1, 1] = true := by decide +kernel
theorem sub0_14 : sub0 [-1, 2] = true := by decide +kernel
theorem sub0_15 : sub0 [-1, 3] = true := by decide +kernel
theorem sub0_16 : sub0 [0, -4] = true := by decide +kernel
theorem sub0_17 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_18 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_19 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_20 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_21 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_22 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_23 : sub0 [0, 3] = true := by decide +kernel
theorem sub0_24 : sub0 [1, -4] = true := by decide +kernel
theorem sub0_25 : sub0 [1, -3] = true := by decide +kernel
theorem sub0_26 : sub0 [1, -2] = true := by decide +kernel
theorem sub0_27 : sub0 [1, -1] = true := by decide +kernel
theorem sub0_28 : sub0 [1, 0] = true := by decide +kernel
theorem sub0_29 : sub0 [1, 1] = true := by decide +kernel
theorem sub0_30 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_31 : sub0 [1, 3] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_cons.2 ⟨sub0_12, List.forall_mem_cons.2 ⟨sub0_13, List.forall_mem_cons.2 ⟨sub0_14, List.forall_mem_cons.2 ⟨sub0_15, List.forall_mem_cons.2 ⟨sub0_16, List.forall_mem_cons.2 ⟨sub0_17, List.forall_mem_cons.2 ⟨sub0_18, List.forall_mem_cons.2 ⟨sub0_19, List.forall_mem_cons.2 ⟨sub0_20, List.forall_mem_cons.2 ⟨sub0_21, List.forall_mem_cons.2 ⟨sub0_22, List.forall_mem_cons.2 ⟨sub0_23, List.forall_mem_cons.2 ⟨sub0_24, List.forall_mem_cons.2 ⟨sub0_25, List.forall_mem_cons.2 ⟨sub0_26, List.forall_mem_cons.2 ⟨sub0_27, List.forall_mem_cons.2 ⟨sub0_28, List.forall_mem_cons.2 ⟨sub0_29, List.forall_mem_cons.2 ⟨sub0_30, List.forall_mem_cons.2 ⟨sub0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_32 : sub0 [2, -3] = true := by decide +kernel
theorem sub0_33 : sub0 [2, -2] = true := by decide +kernel
theorem sub0_34 : sub0 [2, -1] = true := by decide +kernel
theorem sub0_35 : sub0 [2, 0] = true := by decide +kernel
theorem sub0_36 : sub0 [2, 1] = true := by decide +kernel
theorem sub0_37 : sub0 [2, 2] = true := by decide +kernel
theorem sub0_38 : sub0 [2, 3] = true := by decide +kernel
theorem sub0_39 : sub0 [3] = true := by decide +kernel
theorem sb0_1 : ∀ q ∈ blk0_1, sub0 q = true := by
  unfold blk0_1
  exact List.forall_mem_cons.2 ⟨sub0_32, List.forall_mem_cons.2 ⟨sub0_33, List.forall_mem_cons.2 ⟨sub0_34, List.forall_mem_cons.2 ⟨sub0_35, List.forall_mem_cons.2 ⟨sub0_36, List.forall_mem_cons.2 ⟨sub0_37, List.forall_mem_cons.2 ⟨sub0_38, List.forall_mem_cons.2 ⟨sub0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-4, -2] = true := by decide +kernel
theorem sub1_1 : sub1 [-4, -1] = true := by decide +kernel
theorem sub1_2 : sub1 [-4, 0] = true := by decide +kernel
theorem sub1_3 : sub1 [-4, 1] = true := by decide +kernel
theorem sub1_4 : sub1 [-4, 2] = true := by decide +kernel
theorem sub1_5 : sub1 [-4, 3] = true := by decide +kernel
theorem sub1_6 : sub1 [-4, 4] = true := by decide +kernel
theorem sub1_7 : sub1 [-3, -4] = true := by decide +kernel
theorem sub1_8 : sub1 [-3, -3] = true := by decide +kernel
theorem sub1_9 : sub1 [-3, -2] = true := by decide +kernel
theorem sub1_10 : sub1 [-3, -1] = true := by decide +kernel
theorem sub1_11 : sub1 [-3, 0] = true := by decide +kernel
theorem sub1_12 : sub1 [-3, 1] = true := by decide +kernel
theorem sub1_13 : sub1 [-3, 2] = true := by decide +kernel
theorem sub1_14 : sub1 [-3, 3] = true := by decide +kernel
theorem sub1_15 : sub1 [-3, 4] = true := by decide +kernel
theorem sub1_16 : sub1 [-3, 5] = true := by decide +kernel
theorem sub1_17 : sub1 [-2, -5] = true := by decide +kernel
theorem sub1_18 : sub1 [-2, -4] = true := by decide +kernel
theorem sub1_19 : sub1 [-2, -3] = true := by decide +kernel
theorem sub1_20 : sub1 [-2, -2] = true := by decide +kernel
theorem sub1_21 : sub1 [-2, -1] = true := by decide +kernel
theorem sub1_22 : sub1 [-2, 0, -7] = true := by decide +kernel
theorem sub1_23 : sub1 [-2, 0, -6] = true := by decide +kernel
theorem sub1_24 : sub1 [-2, 0, -5] = true := by decide +kernel
theorem sub1_25 : sub1 [-2, 0, -4] = true := by decide +kernel
theorem sub1_26 : sub1 [-2, 0, -3] = true := by decide +kernel
theorem sub1_27 : sub1 [-2, 0, -2] = true := by decide +kernel
theorem sub1_28 : sub1 [-2, 0, -1] = true := by decide +kernel
theorem sub1_29 : sub1 [-2, 0, 0] = true := by decide +kernel
theorem sub1_30 : sub1 [-2, 0, 1] = true := by decide +kernel
theorem sub1_31 : sub1 [-2, 0, 2] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_cons.2 ⟨sub1_18, List.forall_mem_cons.2 ⟨sub1_19, List.forall_mem_cons.2 ⟨sub1_20, List.forall_mem_cons.2 ⟨sub1_21, List.forall_mem_cons.2 ⟨sub1_22, List.forall_mem_cons.2 ⟨sub1_23, List.forall_mem_cons.2 ⟨sub1_24, List.forall_mem_cons.2 ⟨sub1_25, List.forall_mem_cons.2 ⟨sub1_26, List.forall_mem_cons.2 ⟨sub1_27, List.forall_mem_cons.2 ⟨sub1_28, List.forall_mem_cons.2 ⟨sub1_29, List.forall_mem_cons.2 ⟨sub1_30, List.forall_mem_cons.2 ⟨sub1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_32 : sub1 [-2, 0, 3] = true := by decide +kernel
theorem sub1_33 : sub1 [-2, 0, 4] = true := by decide +kernel
theorem sub1_34 : sub1 [-2, 0, 5] = true := by decide +kernel
theorem sub1_35 : sub1 [-2, 0, 6] = true := by decide +kernel
theorem sub1_36 : sub1 [-2, 1, -8] = true := by decide +kernel
theorem sub1_37 : sub1 [-2, 1, -7] = true := by decide +kernel
theorem sub1_38 : sub1 [-2, 1, -6] = true := by decide +kernel
theorem sub1_39 : sub1 [-2, 1, -5] = true := by decide +kernel
theorem sub1_40 : sub1 [-2, 1, -4] = true := by decide +kernel
theorem sub1_41 : sub1 [-2, 1, -3] = true := by decide +kernel
theorem sub1_42 : sub1 [-2, 1, -2] = true := by decide +kernel
theorem sub1_43 : sub1 [-2, 1, -1] = true := by decide +kernel
theorem sub1_44 : sub1 [-2, 1, 0] = true := by decide +kernel
theorem sub1_45 : sub1 [-2, 1, 1] = true := by decide +kernel
theorem sub1_46 : sub1 [-2, 1, 2] = true := by decide +kernel
theorem sub1_47 : sub1 [-2, 1, 3] = true := by decide +kernel
theorem sub1_48 : sub1 [-2, 1, 4] = true := by decide +kernel
theorem sub1_49 : sub1 [-2, 1, 5] = true := by decide +kernel
theorem sub1_50 : sub1 [-2, 2, -8] = true := by decide +kernel
theorem sub1_51 : sub1 [-2, 2, -7] = true := by decide +kernel
theorem sub1_52 : sub1 [-2, 2, -6] = true := by decide +kernel
theorem sub1_53 : sub1 [-2, 2, -5] = true := by decide +kernel
theorem sub1_54 : sub1 [-2, 2, -4] = true := by decide +kernel
theorem sub1_55 : sub1 [-2, 2, -3] = true := by decide +kernel
theorem sub1_56 : sub1 [-2, 2, -2] = true := by decide +kernel
theorem sub1_57 : sub1 [-2, 2, -1] = true := by decide +kernel
theorem sub1_58 : sub1 [-2, 2, 0] = true := by decide +kernel
theorem sub1_59 : sub1 [-2, 2, 1] = true := by decide +kernel
theorem sub1_60 : sub1 [-2, 2, 2] = true := by decide +kernel
theorem sub1_61 : sub1 [-2, 2, 3] = true := by decide +kernel
theorem sub1_62 : sub1 [-2, 2, 4] = true := by decide +kernel
theorem sub1_63 : sub1 [-2, 2, 5] = true := by decide +kernel
theorem sb1_1 : ∀ q ∈ blk1_1, sub1 q = true := by
  unfold blk1_1
  exact List.forall_mem_cons.2 ⟨sub1_32, List.forall_mem_cons.2 ⟨sub1_33, List.forall_mem_cons.2 ⟨sub1_34, List.forall_mem_cons.2 ⟨sub1_35, List.forall_mem_cons.2 ⟨sub1_36, List.forall_mem_cons.2 ⟨sub1_37, List.forall_mem_cons.2 ⟨sub1_38, List.forall_mem_cons.2 ⟨sub1_39, List.forall_mem_cons.2 ⟨sub1_40, List.forall_mem_cons.2 ⟨sub1_41, List.forall_mem_cons.2 ⟨sub1_42, List.forall_mem_cons.2 ⟨sub1_43, List.forall_mem_cons.2 ⟨sub1_44, List.forall_mem_cons.2 ⟨sub1_45, List.forall_mem_cons.2 ⟨sub1_46, List.forall_mem_cons.2 ⟨sub1_47, List.forall_mem_cons.2 ⟨sub1_48, List.forall_mem_cons.2 ⟨sub1_49, List.forall_mem_cons.2 ⟨sub1_50, List.forall_mem_cons.2 ⟨sub1_51, List.forall_mem_cons.2 ⟨sub1_52, List.forall_mem_cons.2 ⟨sub1_53, List.forall_mem_cons.2 ⟨sub1_54, List.forall_mem_cons.2 ⟨sub1_55, List.forall_mem_cons.2 ⟨sub1_56, List.forall_mem_cons.2 ⟨sub1_57, List.forall_mem_cons.2 ⟨sub1_58, List.forall_mem_cons.2 ⟨sub1_59, List.forall_mem_cons.2 ⟨sub1_60, List.forall_mem_cons.2 ⟨sub1_61, List.forall_mem_cons.2 ⟨sub1_62, List.forall_mem_cons.2 ⟨sub1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_64 : sub1 [-2, 3] = true := by decide +kernel
theorem sub1_65 : sub1 [-2, 4] = true := by decide +kernel
theorem sub1_66 : sub1 [-2, 5] = true := by decide +kernel
theorem sub1_67 : sub1 [-1, -5] = true := by decide +kernel
theorem sub1_68 : sub1 [-1, -4] = true := by decide +kernel
theorem sub1_69 : sub1 [-1, -3] = true := by decide +kernel
theorem sub1_70 : sub1 [-1, -2, -6] = true := by decide +kernel
theorem sub1_71 : sub1 [-1, -2, -5] = true := by decide +kernel
theorem sub1_72 : sub1 [-1, -2, -4] = true := by decide +kernel
theorem sub1_73 : sub1 [-1, -2, -3] = true := by decide +kernel
theorem sub1_74 : sub1 [-1, -2, -2] = true := by decide +kernel
theorem sub1_75 : sub1 [-1, -2, -1] = true := by decide +kernel
theorem sub1_76 : sub1 [-1, -2, 0] = true := by decide +kernel
theorem sub1_77 : sub1 [-1, -2, 1] = true := by decide +kernel
theorem sub1_78 : sub1 [-1, -2, 2] = true := by decide +kernel
theorem sub1_79 : sub1 [-1, -2, 3] = true := by decide +kernel
theorem sub1_80 : sub1 [-1, -2, 4] = true := by decide +kernel
theorem sub1_81 : sub1 [-1, -2, 5] = true := by decide +kernel
theorem sub1_82 : sub1 [-1, -2, 6] = true := by decide +kernel
theorem sub1_83 : sub1 [-1, -1, -7] = true := by decide +kernel
theorem sub1_84 : sub1 [-1, -1, -6] = true := by decide +kernel
theorem sub1_85 : sub1 [-1, -1, -5] = true := by decide +kernel
theorem sub1_86 : sub1 [-1, -1, -4] = true := by decide +kernel
theorem sub1_87 : sub1 [-1, -1, -3] = true := by decide +kernel
theorem sub1_88 : sub1 [-1, -1, -2] = true := by decide +kernel
theorem sub1_89 : sub1 [-1, -1, -1] = true := by decide +kernel
theorem sub1_90 : sub1 [-1, -1, 0] = true := by decide +kernel
theorem sub1_91 : sub1 [-1, -1, 1] = true := by decide +kernel
theorem sub1_92 : sub1 [-1, -1, 2] = true := by decide +kernel
theorem sub1_93 : sub1 [-1, -1, 3] = true := by decide +kernel
theorem sub1_94 : sub1 [-1, -1, 4] = true := by decide +kernel
theorem sub1_95 : sub1 [-1, -1, 5] = true := by decide +kernel
theorem sb1_2 : ∀ q ∈ blk1_2, sub1 q = true := by
  unfold blk1_2
  exact List.forall_mem_cons.2 ⟨sub1_64, List.forall_mem_cons.2 ⟨sub1_65, List.forall_mem_cons.2 ⟨sub1_66, List.forall_mem_cons.2 ⟨sub1_67, List.forall_mem_cons.2 ⟨sub1_68, List.forall_mem_cons.2 ⟨sub1_69, List.forall_mem_cons.2 ⟨sub1_70, List.forall_mem_cons.2 ⟨sub1_71, List.forall_mem_cons.2 ⟨sub1_72, List.forall_mem_cons.2 ⟨sub1_73, List.forall_mem_cons.2 ⟨sub1_74, List.forall_mem_cons.2 ⟨sub1_75, List.forall_mem_cons.2 ⟨sub1_76, List.forall_mem_cons.2 ⟨sub1_77, List.forall_mem_cons.2 ⟨sub1_78, List.forall_mem_cons.2 ⟨sub1_79, List.forall_mem_cons.2 ⟨sub1_80, List.forall_mem_cons.2 ⟨sub1_81, List.forall_mem_cons.2 ⟨sub1_82, List.forall_mem_cons.2 ⟨sub1_83, List.forall_mem_cons.2 ⟨sub1_84, List.forall_mem_cons.2 ⟨sub1_85, List.forall_mem_cons.2 ⟨sub1_86, List.forall_mem_cons.2 ⟨sub1_87, List.forall_mem_cons.2 ⟨sub1_88, List.forall_mem_cons.2 ⟨sub1_89, List.forall_mem_cons.2 ⟨sub1_90, List.forall_mem_cons.2 ⟨sub1_91, List.forall_mem_cons.2 ⟨sub1_92, List.forall_mem_cons.2 ⟨sub1_93, List.forall_mem_cons.2 ⟨sub1_94, List.forall_mem_cons.2 ⟨sub1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_96 : sub1 [-1, -1, 6] = true := by decide +kernel
theorem sub1_97 : sub1 [-1, 0, -8] = true := by decide +kernel
theorem sub1_98 : sub1 [-1, 0, -7] = true := by decide +kernel
theorem sub1_99 : sub1 [-1, 0, -6] = true := by decide +kernel
theorem sub1_100 : sub1 [-1, 0, -5] = true := by decide +kernel
theorem sub1_101 : sub1 [-1, 0, -4] = true := by decide +kernel
theorem sub1_102 : sub1 [-1, 0, -3] = true := by decide +kernel
theorem sub1_103 : sub1 [-1, 0, -2] = true := by decide +kernel
theorem sub1_104 : sub1 [-1, 0, -1] = true := by decide +kernel
theorem sub1_105 : sub1 [-1, 0, 0] = true := by decide +kernel
theorem sub1_106 : sub1 [-1, 0, 1] = true := by decide +kernel
theorem sub1_107 : sub1 [-1, 0, 2] = true := by decide +kernel
theorem sub1_108 : sub1 [-1, 0, 3] = true := by decide +kernel
theorem sub1_109 : sub1 [-1, 0, 4] = true := by decide +kernel
theorem sub1_110 : sub1 [-1, 0, 5] = true := by decide +kernel
theorem sub1_111 : sub1 [-1, 0, 6] = true := by decide +kernel
theorem sub1_112 : sub1 [-1, 1, -8] = true := by decide +kernel
theorem sub1_113 : sub1 [-1, 1, -7] = true := by decide +kernel
theorem sub1_114 : sub1 [-1, 1, -6] = true := by decide +kernel
theorem sub1_115 : sub1 [-1, 1, -5] = true := by decide +kernel
theorem sub1_116 : sub1 [-1, 1, -4] = true := by decide +kernel
theorem sub1_117 : sub1 [-1, 1, -3] = true := by decide +kernel
theorem sub1_118 : sub1 [-1, 1, -2] = true := by decide +kernel
theorem sub1_119 : sub1 [-1, 1, -1] = true := by decide +kernel
theorem sub1_120 : sub1 [-1, 1, 0] = true := by decide +kernel
theorem sub1_121 : sub1 [-1, 1, 1] = true := by decide +kernel
theorem sub1_122 : sub1 [-1, 1, 2] = true := by decide +kernel
theorem sub1_123 : sub1 [-1, 1, 3] = true := by decide +kernel
theorem sub1_124 : sub1 [-1, 1, 4] = true := by decide +kernel
theorem sub1_125 : sub1 [-1, 1, 5] = true := by decide +kernel
theorem sub1_126 : sub1 [-1, 1, 6] = true := by decide +kernel
theorem sub1_127 : sub1 [-1, 2, -8] = true := by decide +kernel
theorem sb1_3 : ∀ q ∈ blk1_3, sub1 q = true := by
  unfold blk1_3
  exact List.forall_mem_cons.2 ⟨sub1_96, List.forall_mem_cons.2 ⟨sub1_97, List.forall_mem_cons.2 ⟨sub1_98, List.forall_mem_cons.2 ⟨sub1_99, List.forall_mem_cons.2 ⟨sub1_100, List.forall_mem_cons.2 ⟨sub1_101, List.forall_mem_cons.2 ⟨sub1_102, List.forall_mem_cons.2 ⟨sub1_103, List.forall_mem_cons.2 ⟨sub1_104, List.forall_mem_cons.2 ⟨sub1_105, List.forall_mem_cons.2 ⟨sub1_106, List.forall_mem_cons.2 ⟨sub1_107, List.forall_mem_cons.2 ⟨sub1_108, List.forall_mem_cons.2 ⟨sub1_109, List.forall_mem_cons.2 ⟨sub1_110, List.forall_mem_cons.2 ⟨sub1_111, List.forall_mem_cons.2 ⟨sub1_112, List.forall_mem_cons.2 ⟨sub1_113, List.forall_mem_cons.2 ⟨sub1_114, List.forall_mem_cons.2 ⟨sub1_115, List.forall_mem_cons.2 ⟨sub1_116, List.forall_mem_cons.2 ⟨sub1_117, List.forall_mem_cons.2 ⟨sub1_118, List.forall_mem_cons.2 ⟨sub1_119, List.forall_mem_cons.2 ⟨sub1_120, List.forall_mem_cons.2 ⟨sub1_121, List.forall_mem_cons.2 ⟨sub1_122, List.forall_mem_cons.2 ⟨sub1_123, List.forall_mem_cons.2 ⟨sub1_124, List.forall_mem_cons.2 ⟨sub1_125, List.forall_mem_cons.2 ⟨sub1_126, List.forall_mem_cons.2 ⟨sub1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_128 : sub1 [-1, 2, -7] = true := by decide +kernel
theorem sub1_129 : sub1 [-1, 2, -6] = true := by decide +kernel
theorem sub1_130 : sub1 [-1, 2, -5] = true := by decide +kernel
theorem sub1_131 : sub1 [-1, 2, -4] = true := by decide +kernel
theorem sub1_132 : sub1 [-1, 2, -3] = true := by decide +kernel
theorem sub1_133 : sub1 [-1, 2, -2] = true := by decide +kernel
theorem sub1_134 : sub1 [-1, 2, -1] = true := by decide +kernel
theorem sub1_135 : sub1 [-1, 2, 0] = true := by decide +kernel
theorem sub1_136 : sub1 [-1, 2, 1] = true := by decide +kernel
theorem sub1_137 : sub1 [-1, 2, 2] = true := by decide +kernel
theorem sub1_138 : sub1 [-1, 2, 3] = true := by decide +kernel
theorem sub1_139 : sub1 [-1, 2, 4] = true := by decide +kernel
theorem sub1_140 : sub1 [-1, 2, 5] = true := by decide +kernel
theorem sub1_141 : sub1 [-1, 3] = true := by decide +kernel
theorem sub1_142 : sub1 [-1, 4] = true := by decide +kernel
theorem sub1_143 : sub1 [-1, 5] = true := by decide +kernel
theorem sub1_144 : sub1 [0, -6] = true := by decide +kernel
theorem sub1_145 : sub1 [0, -5] = true := by decide +kernel
theorem sub1_146 : sub1 [0, -4] = true := by decide +kernel
theorem sub1_147 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_148 : sub1 [0, -2, -6] = true := by decide +kernel
theorem sub1_149 : sub1 [0, -2, -5] = true := by decide +kernel
theorem sub1_150 : sub1 [0, -2, -4] = true := by decide +kernel
theorem sub1_151 : sub1 [0, -2, -3] = true := by decide +kernel
theorem sub1_152 : sub1 [0, -2, -2] = true := by decide +kernel
theorem sub1_153 : sub1 [0, -2, -1] = true := by decide +kernel
theorem sub1_154 : sub1 [0, -2, 0] = true := by decide +kernel
theorem sub1_155 : sub1 [0, -2, 1] = true := by decide +kernel
theorem sub1_156 : sub1 [0, -2, 2] = true := by decide +kernel
theorem sub1_157 : sub1 [0, -2, 3] = true := by decide +kernel
theorem sub1_158 : sub1 [0, -2, 4] = true := by decide +kernel
theorem sub1_159 : sub1 [0, -2, 5] = true := by decide +kernel
theorem sb1_4 : ∀ q ∈ blk1_4, sub1 q = true := by
  unfold blk1_4
  exact List.forall_mem_cons.2 ⟨sub1_128, List.forall_mem_cons.2 ⟨sub1_129, List.forall_mem_cons.2 ⟨sub1_130, List.forall_mem_cons.2 ⟨sub1_131, List.forall_mem_cons.2 ⟨sub1_132, List.forall_mem_cons.2 ⟨sub1_133, List.forall_mem_cons.2 ⟨sub1_134, List.forall_mem_cons.2 ⟨sub1_135, List.forall_mem_cons.2 ⟨sub1_136, List.forall_mem_cons.2 ⟨sub1_137, List.forall_mem_cons.2 ⟨sub1_138, List.forall_mem_cons.2 ⟨sub1_139, List.forall_mem_cons.2 ⟨sub1_140, List.forall_mem_cons.2 ⟨sub1_141, List.forall_mem_cons.2 ⟨sub1_142, List.forall_mem_cons.2 ⟨sub1_143, List.forall_mem_cons.2 ⟨sub1_144, List.forall_mem_cons.2 ⟨sub1_145, List.forall_mem_cons.2 ⟨sub1_146, List.forall_mem_cons.2 ⟨sub1_147, List.forall_mem_cons.2 ⟨sub1_148, List.forall_mem_cons.2 ⟨sub1_149, List.forall_mem_cons.2 ⟨sub1_150, List.forall_mem_cons.2 ⟨sub1_151, List.forall_mem_cons.2 ⟨sub1_152, List.forall_mem_cons.2 ⟨sub1_153, List.forall_mem_cons.2 ⟨sub1_154, List.forall_mem_cons.2 ⟨sub1_155, List.forall_mem_cons.2 ⟨sub1_156, List.forall_mem_cons.2 ⟨sub1_157, List.forall_mem_cons.2 ⟨sub1_158, List.forall_mem_cons.2 ⟨sub1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_160 : sub1 [0, -2, 6] = true := by decide +kernel
theorem sub1_161 : sub1 [0, -2, 7] = true := by decide +kernel
theorem sub1_162 : sub1 [0, -1, -7] = true := by decide +kernel
theorem sub1_163 : sub1 [0, -1, -6] = true := by decide +kernel
theorem sub1_164 : sub1 [0, -1, -5] = true := by decide +kernel
theorem sub1_165 : sub1 [0, -1, -4] = true := by decide +kernel
theorem sub1_166 : sub1 [0, -1, -3] = true := by decide +kernel
theorem sub1_167 : sub1 [0, -1, -2] = true := by decide +kernel
theorem sub1_168 : sub1 [0, -1, -1] = true := by decide +kernel
theorem sub1_169 : sub1 [0, -1, 0] = true := by decide +kernel
theorem sub1_170 : sub1 [0, -1, 1] = true := by decide +kernel
theorem sub1_171 : sub1 [0, -1, 2] = true := by decide +kernel
theorem sub1_172 : sub1 [0, -1, 3] = true := by decide +kernel
theorem sub1_173 : sub1 [0, -1, 4] = true := by decide +kernel
theorem sub1_174 : sub1 [0, -1, 5] = true := by decide +kernel
theorem sub1_175 : sub1 [0, -1, 6] = true := by decide +kernel
theorem sub1_176 : sub1 [0, -1, 7] = true := by decide +kernel
theorem sub1_177 : sub1 [0, 0, -8] = true := by decide +kernel
theorem sub1_178 : sub1 [0, 0, -7] = true := by decide +kernel
theorem sub1_179 : sub1 [0, 0, -6] = true := by decide +kernel
theorem sub1_180 : sub1 [0, 0, -5] = true := by decide +kernel
theorem sub1_181 : sub1 [0, 0, -4] = true := by decide +kernel
theorem sub1_182 : sub1 [0, 0, -3] = true := by decide +kernel
theorem sub1_183 : sub1 [0, 0, -2] = true := by decide +kernel
theorem sub1_184 : sub1 [0, 0, -1] = true := by decide +kernel
theorem sub1_185 : sub1 [0, 0, 0] = true := by decide +kernel
theorem sub1_186 : sub1 [0, 0, 1] = true := by decide +kernel
theorem sub1_187 : sub1 [0, 0, 2] = true := by decide +kernel
theorem sub1_188 : sub1 [0, 0, 3] = true := by decide +kernel
theorem sub1_189 : sub1 [0, 0, 4] = true := by decide +kernel
theorem sub1_190 : sub1 [0, 0, 5] = true := by decide +kernel
theorem sub1_191 : sub1 [0, 0, 6] = true := by decide +kernel
theorem sb1_5 : ∀ q ∈ blk1_5, sub1 q = true := by
  unfold blk1_5
  exact List.forall_mem_cons.2 ⟨sub1_160, List.forall_mem_cons.2 ⟨sub1_161, List.forall_mem_cons.2 ⟨sub1_162, List.forall_mem_cons.2 ⟨sub1_163, List.forall_mem_cons.2 ⟨sub1_164, List.forall_mem_cons.2 ⟨sub1_165, List.forall_mem_cons.2 ⟨sub1_166, List.forall_mem_cons.2 ⟨sub1_167, List.forall_mem_cons.2 ⟨sub1_168, List.forall_mem_cons.2 ⟨sub1_169, List.forall_mem_cons.2 ⟨sub1_170, List.forall_mem_cons.2 ⟨sub1_171, List.forall_mem_cons.2 ⟨sub1_172, List.forall_mem_cons.2 ⟨sub1_173, List.forall_mem_cons.2 ⟨sub1_174, List.forall_mem_cons.2 ⟨sub1_175, List.forall_mem_cons.2 ⟨sub1_176, List.forall_mem_cons.2 ⟨sub1_177, List.forall_mem_cons.2 ⟨sub1_178, List.forall_mem_cons.2 ⟨sub1_179, List.forall_mem_cons.2 ⟨sub1_180, List.forall_mem_cons.2 ⟨sub1_181, List.forall_mem_cons.2 ⟨sub1_182, List.forall_mem_cons.2 ⟨sub1_183, List.forall_mem_cons.2 ⟨sub1_184, List.forall_mem_cons.2 ⟨sub1_185, List.forall_mem_cons.2 ⟨sub1_186, List.forall_mem_cons.2 ⟨sub1_187, List.forall_mem_cons.2 ⟨sub1_188, List.forall_mem_cons.2 ⟨sub1_189, List.forall_mem_cons.2 ⟨sub1_190, List.forall_mem_cons.2 ⟨sub1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_192 : sub1 [0, 0, 7] = true := by decide +kernel
theorem sub1_193 : sub1 [0, 1, -8] = true := by decide +kernel
theorem sub1_194 : sub1 [0, 1, -7] = true := by decide +kernel
theorem sub1_195 : sub1 [0, 1, -6] = true := by decide +kernel
theorem sub1_196 : sub1 [0, 1, -5] = true := by decide +kernel
theorem sub1_197 : sub1 [0, 1, -4] = true := by decide +kernel
theorem sub1_198 : sub1 [0, 1, -3] = true := by decide +kernel
theorem sub1_199 : sub1 [0, 1, -2] = true := by decide +kernel
theorem sub1_200 : sub1 [0, 1, -1] = true := by decide +kernel
theorem sub1_201 : sub1 [0, 1, 0] = true := by decide +kernel
theorem sub1_202 : sub1 [0, 1, 1] = true := by decide +kernel
theorem sub1_203 : sub1 [0, 1, 2] = true := by decide +kernel
theorem sub1_204 : sub1 [0, 1, 3] = true := by decide +kernel
theorem sub1_205 : sub1 [0, 1, 4] = true := by decide +kernel
theorem sub1_206 : sub1 [0, 1, 5] = true := by decide +kernel
theorem sub1_207 : sub1 [0, 1, 6] = true := by decide +kernel
theorem sub1_208 : sub1 [0, 2, -8] = true := by decide +kernel
theorem sub1_209 : sub1 [0, 2, -7] = true := by decide +kernel
theorem sub1_210 : sub1 [0, 2, -6] = true := by decide +kernel
theorem sub1_211 : sub1 [0, 2, -5] = true := by decide +kernel
theorem sub1_212 : sub1 [0, 2, -4] = true := by decide +kernel
theorem sub1_213 : sub1 [0, 2, -3] = true := by decide +kernel
theorem sub1_214 : sub1 [0, 2, -2] = true := by decide +kernel
theorem sub1_215 : sub1 [0, 2, -1] = true := by decide +kernel
theorem sub1_216 : sub1 [0, 2, 0] = true := by decide +kernel
theorem sub1_217 : sub1 [0, 2, 1] = true := by decide +kernel
theorem sub1_218 : sub1 [0, 2, 2] = true := by decide +kernel
theorem sub1_219 : sub1 [0, 2, 3] = true := by decide +kernel
theorem sub1_220 : sub1 [0, 2, 4] = true := by decide +kernel
theorem sub1_221 : sub1 [0, 2, 5] = true := by decide +kernel
theorem sub1_222 : sub1 [0, 3] = true := by decide +kernel
theorem sub1_223 : sub1 [0, 4] = true := by decide +kernel
theorem sb1_6 : ∀ q ∈ blk1_6, sub1 q = true := by
  unfold blk1_6
  exact List.forall_mem_cons.2 ⟨sub1_192, List.forall_mem_cons.2 ⟨sub1_193, List.forall_mem_cons.2 ⟨sub1_194, List.forall_mem_cons.2 ⟨sub1_195, List.forall_mem_cons.2 ⟨sub1_196, List.forall_mem_cons.2 ⟨sub1_197, List.forall_mem_cons.2 ⟨sub1_198, List.forall_mem_cons.2 ⟨sub1_199, List.forall_mem_cons.2 ⟨sub1_200, List.forall_mem_cons.2 ⟨sub1_201, List.forall_mem_cons.2 ⟨sub1_202, List.forall_mem_cons.2 ⟨sub1_203, List.forall_mem_cons.2 ⟨sub1_204, List.forall_mem_cons.2 ⟨sub1_205, List.forall_mem_cons.2 ⟨sub1_206, List.forall_mem_cons.2 ⟨sub1_207, List.forall_mem_cons.2 ⟨sub1_208, List.forall_mem_cons.2 ⟨sub1_209, List.forall_mem_cons.2 ⟨sub1_210, List.forall_mem_cons.2 ⟨sub1_211, List.forall_mem_cons.2 ⟨sub1_212, List.forall_mem_cons.2 ⟨sub1_213, List.forall_mem_cons.2 ⟨sub1_214, List.forall_mem_cons.2 ⟨sub1_215, List.forall_mem_cons.2 ⟨sub1_216, List.forall_mem_cons.2 ⟨sub1_217, List.forall_mem_cons.2 ⟨sub1_218, List.forall_mem_cons.2 ⟨sub1_219, List.forall_mem_cons.2 ⟨sub1_220, List.forall_mem_cons.2 ⟨sub1_221, List.forall_mem_cons.2 ⟨sub1_222, List.forall_mem_cons.2 ⟨sub1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_224 : sub1 [0, 5] = true := by decide +kernel
theorem sub1_225 : sub1 [1, -6] = true := by decide +kernel
theorem sub1_226 : sub1 [1, -5] = true := by decide +kernel
theorem sub1_227 : sub1 [1, -4] = true := by decide +kernel
theorem sub1_228 : sub1 [1, -3] = true := by decide +kernel
theorem sub1_229 : sub1 [1, -2, -6] = true := by decide +kernel
theorem sub1_230 : sub1 [1, -2, -5] = true := by decide +kernel
theorem sub1_231 : sub1 [1, -2, -4] = true := by decide +kernel
theorem sub1_232 : sub1 [1, -2, -3] = true := by decide +kernel
theorem sub1_233 : sub1 [1, -2, -2] = true := by decide +kernel
theorem sub1_234 : sub1 [1, -2, -1] = true := by decide +kernel
theorem sub1_235 : sub1 [1, -2, 0] = true := by decide +kernel
theorem sub1_236 : sub1 [1, -2, 1] = true := by decide +kernel
theorem sub1_237 : sub1 [1, -2, 2] = true := by decide +kernel
theorem sub1_238 : sub1 [1, -2, 3] = true := by decide +kernel
theorem sub1_239 : sub1 [1, -2, 4] = true := by decide +kernel
theorem sub1_240 : sub1 [1, -2, 5] = true := by decide +kernel
theorem sub1_241 : sub1 [1, -2, 6] = true := by decide +kernel
theorem sub1_242 : sub1 [1, -2, 7] = true := by decide +kernel
theorem sub1_243 : sub1 [1, -1, -7] = true := by decide +kernel
theorem sub1_244 : sub1 [1, -1, -6] = true := by decide +kernel
theorem sub1_245 : sub1 [1, -1, -5] = true := by decide +kernel
theorem sub1_246 : sub1 [1, -1, -4] = true := by decide +kernel
theorem sub1_247 : sub1 [1, -1, -3] = true := by decide +kernel
theorem sub1_248 : sub1 [1, -1, -2] = true := by decide +kernel
theorem sub1_249 : sub1 [1, -1, -1] = true := by decide +kernel
theorem sub1_250 : sub1 [1, -1, 0] = true := by decide +kernel
theorem sub1_251 : sub1 [1, -1, 1] = true := by decide +kernel
theorem sub1_252 : sub1 [1, -1, 2] = true := by decide +kernel
theorem sub1_253 : sub1 [1, -1, 3] = true := by decide +kernel
theorem sub1_254 : sub1 [1, -1, 4] = true := by decide +kernel
theorem sub1_255 : sub1 [1, -1, 5] = true := by decide +kernel
theorem sb1_7 : ∀ q ∈ blk1_7, sub1 q = true := by
  unfold blk1_7
  exact List.forall_mem_cons.2 ⟨sub1_224, List.forall_mem_cons.2 ⟨sub1_225, List.forall_mem_cons.2 ⟨sub1_226, List.forall_mem_cons.2 ⟨sub1_227, List.forall_mem_cons.2 ⟨sub1_228, List.forall_mem_cons.2 ⟨sub1_229, List.forall_mem_cons.2 ⟨sub1_230, List.forall_mem_cons.2 ⟨sub1_231, List.forall_mem_cons.2 ⟨sub1_232, List.forall_mem_cons.2 ⟨sub1_233, List.forall_mem_cons.2 ⟨sub1_234, List.forall_mem_cons.2 ⟨sub1_235, List.forall_mem_cons.2 ⟨sub1_236, List.forall_mem_cons.2 ⟨sub1_237, List.forall_mem_cons.2 ⟨sub1_238, List.forall_mem_cons.2 ⟨sub1_239, List.forall_mem_cons.2 ⟨sub1_240, List.forall_mem_cons.2 ⟨sub1_241, List.forall_mem_cons.2 ⟨sub1_242, List.forall_mem_cons.2 ⟨sub1_243, List.forall_mem_cons.2 ⟨sub1_244, List.forall_mem_cons.2 ⟨sub1_245, List.forall_mem_cons.2 ⟨sub1_246, List.forall_mem_cons.2 ⟨sub1_247, List.forall_mem_cons.2 ⟨sub1_248, List.forall_mem_cons.2 ⟨sub1_249, List.forall_mem_cons.2 ⟨sub1_250, List.forall_mem_cons.2 ⟨sub1_251, List.forall_mem_cons.2 ⟨sub1_252, List.forall_mem_cons.2 ⟨sub1_253, List.forall_mem_cons.2 ⟨sub1_254, List.forall_mem_cons.2 ⟨sub1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C081
