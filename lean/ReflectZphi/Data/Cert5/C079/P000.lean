import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-2] = true := by decide +kernel
theorem sub0_1 : sub0 [-1] = true := by decide +kernel
theorem sub0_2 : sub0 [0, -4] = true := by decide +kernel
theorem sub0_3 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_4 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_5 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_6 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_7 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_8 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_9 : sub0 [0, 3] = true := by decide +kernel
theorem sub0_10 : sub0 [1] = true := by decide +kernel
theorem sub0_11 : sub0 [2] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-2] = true := by decide +kernel
theorem sub1_1 : sub1 [-1, -2] = true := by decide +kernel
theorem sub1_2 : sub1 [-1, -1] = true := by decide +kernel
theorem sub1_3 : sub1 [-1, 0] = true := by decide +kernel
theorem sub1_4 : sub1 [-1, 1] = true := by decide +kernel
theorem sub1_5 : sub1 [-1, 2] = true := by decide +kernel
theorem sub1_6 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_7 : sub1 [0, -2] = true := by decide +kernel
theorem sub1_8 : sub1 [0, -1] = true := by decide +kernel
theorem sub1_9 : sub1 [0, 0] = true := by decide +kernel
theorem sub1_10 : sub1 [0, 1] = true := by decide +kernel
theorem sub1_11 : sub1 [0, 2] = true := by decide +kernel
theorem sub1_12 : sub1 [1, -3] = true := by decide +kernel
theorem sub1_13 : sub1 [1, -2] = true := by decide +kernel
theorem sub1_14 : sub1 [1, -1] = true := by decide +kernel
theorem sub1_15 : sub1 [1, 0] = true := by decide +kernel
theorem sub1_16 : sub1 [1, 1] = true := by decide +kernel
theorem sub1_17 : sub1 [2] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_0 : sub2 [-4] = true := by decide +kernel
theorem sub2_1 : sub2 [-3, -4] = true := by decide +kernel
theorem sub2_2 : sub2 [-3, -3] = true := by decide +kernel
theorem sub2_3 : sub2 [-3, -2] = true := by decide +kernel
theorem sub2_4 : sub2 [-3, -1] = true := by decide +kernel
theorem sub2_5 : sub2 [-3, 0] = true := by decide +kernel
theorem sub2_6 : sub2 [-3, 1] = true := by decide +kernel
theorem sub2_7 : sub2 [-3, 2] = true := by decide +kernel
theorem sub2_8 : sub2 [-3, 3] = true := by decide +kernel
theorem sub2_9 : sub2 [-2, -4] = true := by decide +kernel
theorem sub2_10 : sub2 [-2, -3] = true := by decide +kernel
theorem sub2_11 : sub2 [-2, -2] = true := by decide +kernel
theorem sub2_12 : sub2 [-2, -1, -7] = true := by decide +kernel
theorem sub2_13 : sub2 [-2, -1, -6] = true := by decide +kernel
theorem sub2_14 : sub2 [-2, -1, -5] = true := by decide +kernel
theorem sub2_15 : sub2 [-2, -1, -4] = true := by decide +kernel
theorem sub2_16 : sub2 [-2, -1, -3] = true := by decide +kernel
theorem sub2_17 : sub2 [-2, -1, -2] = true := by decide +kernel
theorem sub2_18 : sub2 [-2, -1, -1] = true := by decide +kernel
theorem sub2_19 : sub2 [-2, -1, 0] = true := by decide +kernel
theorem sub2_20 : sub2 [-2, -1, 1] = true := by decide +kernel
theorem sub2_21 : sub2 [-2, -1, 2] = true := by decide +kernel
theorem sub2_22 : sub2 [-2, -1, 3] = true := by decide +kernel
theorem sub2_23 : sub2 [-2, -1, 4] = true := by decide +kernel
theorem sub2_24 : sub2 [-2, -1, 5] = true := by decide +kernel
theorem sub2_25 : sub2 [-2, -1, 6] = true := by decide +kernel
theorem sub2_26 : sub2 [-2, 0, -7] = true := by decide +kernel
theorem sub2_27 : sub2 [-2, 0, -6] = true := by decide +kernel
theorem sub2_28 : sub2 [-2, 0, -5] = true := by decide +kernel
theorem sub2_29 : sub2 [-2, 0, -4] = true := by decide +kernel
theorem sub2_30 : sub2 [-2, 0, -3] = true := by decide +kernel
theorem sub2_31 : sub2 [-2, 0, -2] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_cons.2 ⟨sub2_10, List.forall_mem_cons.2 ⟨sub2_11, List.forall_mem_cons.2 ⟨sub2_12, List.forall_mem_cons.2 ⟨sub2_13, List.forall_mem_cons.2 ⟨sub2_14, List.forall_mem_cons.2 ⟨sub2_15, List.forall_mem_cons.2 ⟨sub2_16, List.forall_mem_cons.2 ⟨sub2_17, List.forall_mem_cons.2 ⟨sub2_18, List.forall_mem_cons.2 ⟨sub2_19, List.forall_mem_cons.2 ⟨sub2_20, List.forall_mem_cons.2 ⟨sub2_21, List.forall_mem_cons.2 ⟨sub2_22, List.forall_mem_cons.2 ⟨sub2_23, List.forall_mem_cons.2 ⟨sub2_24, List.forall_mem_cons.2 ⟨sub2_25, List.forall_mem_cons.2 ⟨sub2_26, List.forall_mem_cons.2 ⟨sub2_27, List.forall_mem_cons.2 ⟨sub2_28, List.forall_mem_cons.2 ⟨sub2_29, List.forall_mem_cons.2 ⟨sub2_30, List.forall_mem_cons.2 ⟨sub2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_32 : sub2 [-2, 0, -1] = true := by decide +kernel
theorem sub2_33 : sub2 [-2, 0, 0] = true := by decide +kernel
theorem sub2_34 : sub2 [-2, 0, 1] = true := by decide +kernel
theorem sub2_35 : sub2 [-2, 0, 2] = true := by decide +kernel
theorem sub2_36 : sub2 [-2, 0, 3] = true := by decide +kernel
theorem sub2_37 : sub2 [-2, 0, 4] = true := by decide +kernel
theorem sub2_38 : sub2 [-2, 0, 5] = true := by decide +kernel
theorem sub2_39 : sub2 [-2, 0, 6] = true := by decide +kernel
theorem sub2_40 : sub2 [-2, 1, -7] = true := by decide +kernel
theorem sub2_41 : sub2 [-2, 1, -6] = true := by decide +kernel
theorem sub2_42 : sub2 [-2, 1, -5] = true := by decide +kernel
theorem sub2_43 : sub2 [-2, 1, -4] = true := by decide +kernel
theorem sub2_44 : sub2 [-2, 1, -3] = true := by decide +kernel
theorem sub2_45 : sub2 [-2, 1, -2] = true := by decide +kernel
theorem sub2_46 : sub2 [-2, 1, -1] = true := by decide +kernel
theorem sub2_47 : sub2 [-2, 1, 0] = true := by decide +kernel
theorem sub2_48 : sub2 [-2, 1, 1] = true := by decide +kernel
theorem sub2_49 : sub2 [-2, 1, 2] = true := by decide +kernel
theorem sub2_50 : sub2 [-2, 1, 3] = true := by decide +kernel
theorem sub2_51 : sub2 [-2, 1, 4] = true := by decide +kernel
theorem sub2_52 : sub2 [-2, 1, 5] = true := by decide +kernel
theorem sub2_53 : sub2 [-2, 1, 6] = true := by decide +kernel
theorem sub2_54 : sub2 [-2, 2] = true := by decide +kernel
theorem sub2_55 : sub2 [-2, 3] = true := by decide +kernel
theorem sub2_56 : sub2 [-2, 4] = true := by decide +kernel
theorem sub2_57 : sub2 [-1, -5] = true := by decide +kernel
theorem sub2_58 : sub2 [-1, -4] = true := by decide +kernel
theorem sub2_59 : sub2 [-1, -3] = true := by decide +kernel
theorem sub2_60 : sub2 [-1, -2, -7] = true := by decide +kernel
theorem sub2_61 : sub2 [-1, -2, -6] = true := by decide +kernel
theorem sub2_62 : sub2 [-1, -2, -5] = true := by decide +kernel
theorem sub2_63 : sub2 [-1, -2, -4] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_cons.2 ⟨sub2_60, List.forall_mem_cons.2 ⟨sub2_61, List.forall_mem_cons.2 ⟨sub2_62, List.forall_mem_cons.2 ⟨sub2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_64 : sub2 [-1, -2, -3] = true := by decide +kernel
theorem sub2_65 : sub2 [-1, -2, -2] = true := by decide +kernel
theorem sub2_66 : sub2 [-1, -2, -1] = true := by decide +kernel
theorem sub2_67 : sub2 [-1, -2, 0] = true := by decide +kernel
theorem sub2_68 : sub2 [-1, -2, 1] = true := by decide +kernel
theorem sub2_69 : sub2 [-1, -2, 2] = true := by decide +kernel
theorem sub2_70 : sub2 [-1, -2, 3] = true := by decide +kernel
theorem sub2_71 : sub2 [-1, -2, 4] = true := by decide +kernel
theorem sub2_72 : sub2 [-1, -2, 5] = true := by decide +kernel
theorem sub2_73 : sub2 [-1, -2, 6] = true := by decide +kernel
theorem sub2_74 : sub2 [-1, -1, -7] = true := by decide +kernel
theorem sub2_75 : sub2 [-1, -1, -6] = true := by decide +kernel
theorem sub2_76 : sub2 [-1, -1, -5] = true := by decide +kernel
theorem sub2_77 : sub2 [-1, -1, -4] = true := by decide +kernel
theorem sub2_78 : sub2 [-1, -1, -3] = true := by decide +kernel
theorem sub2_79 : sub2 [-1, -1, -2] = true := by decide +kernel
theorem sub2_80 : sub2 [-1, -1, -1] = true := by decide +kernel
theorem sub2_81 : sub2 [-1, -1, 0] = true := by decide +kernel
theorem sub2_82 : sub2 [-1, -1, 1] = true := by decide +kernel
theorem sub2_83 : sub2 [-1, -1, 2] = true := by decide +kernel
theorem sub2_84 : sub2 [-1, -1, 3] = true := by decide +kernel
theorem sub2_85 : sub2 [-1, -1, 4] = true := by decide +kernel
theorem sub2_86 : sub2 [-1, -1, 5] = true := by decide +kernel
theorem sub2_87 : sub2 [-1, -1, 6] = true := by decide +kernel
theorem sub2_88 : sub2 [-1, 0, -8] = true := by decide +kernel
theorem sub2_89 : sub2 [-1, 0, -7] = true := by decide +kernel
theorem sub2_90 : sub2 [-1, 0, -6] = true := by decide +kernel
theorem sub2_91 : sub2 [-1, 0, -5] = true := by decide +kernel
theorem sub2_92 : sub2 [-1, 0, -4] = true := by decide +kernel
theorem sub2_93 : sub2 [-1, 0, -3] = true := by decide +kernel
theorem sub2_94 : sub2 [-1, 0, -2] = true := by decide +kernel
theorem sub2_95 : sub2 [-1, 0, -1] = true := by decide +kernel
theorem sb2_2 : ∀ q ∈ blk2_2, sub2 q = true := by
  unfold blk2_2
  exact List.forall_mem_cons.2 ⟨sub2_64, List.forall_mem_cons.2 ⟨sub2_65, List.forall_mem_cons.2 ⟨sub2_66, List.forall_mem_cons.2 ⟨sub2_67, List.forall_mem_cons.2 ⟨sub2_68, List.forall_mem_cons.2 ⟨sub2_69, List.forall_mem_cons.2 ⟨sub2_70, List.forall_mem_cons.2 ⟨sub2_71, List.forall_mem_cons.2 ⟨sub2_72, List.forall_mem_cons.2 ⟨sub2_73, List.forall_mem_cons.2 ⟨sub2_74, List.forall_mem_cons.2 ⟨sub2_75, List.forall_mem_cons.2 ⟨sub2_76, List.forall_mem_cons.2 ⟨sub2_77, List.forall_mem_cons.2 ⟨sub2_78, List.forall_mem_cons.2 ⟨sub2_79, List.forall_mem_cons.2 ⟨sub2_80, List.forall_mem_cons.2 ⟨sub2_81, List.forall_mem_cons.2 ⟨sub2_82, List.forall_mem_cons.2 ⟨sub2_83, List.forall_mem_cons.2 ⟨sub2_84, List.forall_mem_cons.2 ⟨sub2_85, List.forall_mem_cons.2 ⟨sub2_86, List.forall_mem_cons.2 ⟨sub2_87, List.forall_mem_cons.2 ⟨sub2_88, List.forall_mem_cons.2 ⟨sub2_89, List.forall_mem_cons.2 ⟨sub2_90, List.forall_mem_cons.2 ⟨sub2_91, List.forall_mem_cons.2 ⟨sub2_92, List.forall_mem_cons.2 ⟨sub2_93, List.forall_mem_cons.2 ⟨sub2_94, List.forall_mem_cons.2 ⟨sub2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_96 : sub2 [-1, 0, 0] = true := by decide +kernel
theorem sub2_97 : sub2 [-1, 0, 1] = true := by decide +kernel
theorem sub2_98 : sub2 [-1, 0, 2] = true := by decide +kernel
theorem sub2_99 : sub2 [-1, 0, 3] = true := by decide +kernel
theorem sub2_100 : sub2 [-1, 0, 4] = true := by decide +kernel
theorem sub2_101 : sub2 [-1, 0, 5] = true := by decide +kernel
theorem sub2_102 : sub2 [-1, 0, 6] = true := by decide +kernel
theorem sub2_103 : sub2 [-1, 0, 7] = true := by decide +kernel
theorem sub2_104 : sub2 [-1, 1, -7] = true := by decide +kernel
theorem sub2_105 : sub2 [-1, 1, -6] = true := by decide +kernel
theorem sub2_106 : sub2 [-1, 1, -5] = true := by decide +kernel
theorem sub2_107 : sub2 [-1, 1, -4] = true := by decide +kernel
theorem sub2_108 : sub2 [-1, 1, -3] = true := by decide +kernel
theorem sub2_109 : sub2 [-1, 1, -2] = true := by decide +kernel
theorem sub2_110 : sub2 [-1, 1, -1] = true := by decide +kernel
theorem sub2_111 : sub2 [-1, 1, 0] = true := by decide +kernel
theorem sub2_112 : sub2 [-1, 1, 1] = true := by decide +kernel
theorem sub2_113 : sub2 [-1, 1, 2] = true := by decide +kernel
theorem sub2_114 : sub2 [-1, 1, 3] = true := by decide +kernel
theorem sub2_115 : sub2 [-1, 1, 4] = true := by decide +kernel
theorem sub2_116 : sub2 [-1, 1, 5] = true := by decide +kernel
theorem sub2_117 : sub2 [-1, 1, 6] = true := by decide +kernel
theorem sub2_118 : sub2 [-1, 1, 7] = true := by decide +kernel
theorem sub2_119 : sub2 [-1, 2, -7] = true := by decide +kernel
theorem sub2_120 : sub2 [-1, 2, -6] = true := by decide +kernel
theorem sub2_121 : sub2 [-1, 2, -5] = true := by decide +kernel
theorem sub2_122 : sub2 [-1, 2, -4] = true := by decide +kernel
theorem sub2_123 : sub2 [-1, 2, -3] = true := by decide +kernel
theorem sub2_124 : sub2 [-1, 2, -2] = true := by decide +kernel
theorem sub2_125 : sub2 [-1, 2, -1] = true := by decide +kernel
theorem sub2_126 : sub2 [-1, 2, 0] = true := by decide +kernel
theorem sub2_127 : sub2 [-1, 2, 1] = true := by decide +kernel
theorem sb2_3 : ∀ q ∈ blk2_3, sub2 q = true := by
  unfold blk2_3
  exact List.forall_mem_cons.2 ⟨sub2_96, List.forall_mem_cons.2 ⟨sub2_97, List.forall_mem_cons.2 ⟨sub2_98, List.forall_mem_cons.2 ⟨sub2_99, List.forall_mem_cons.2 ⟨sub2_100, List.forall_mem_cons.2 ⟨sub2_101, List.forall_mem_cons.2 ⟨sub2_102, List.forall_mem_cons.2 ⟨sub2_103, List.forall_mem_cons.2 ⟨sub2_104, List.forall_mem_cons.2 ⟨sub2_105, List.forall_mem_cons.2 ⟨sub2_106, List.forall_mem_cons.2 ⟨sub2_107, List.forall_mem_cons.2 ⟨sub2_108, List.forall_mem_cons.2 ⟨sub2_109, List.forall_mem_cons.2 ⟨sub2_110, List.forall_mem_cons.2 ⟨sub2_111, List.forall_mem_cons.2 ⟨sub2_112, List.forall_mem_cons.2 ⟨sub2_113, List.forall_mem_cons.2 ⟨sub2_114, List.forall_mem_cons.2 ⟨sub2_115, List.forall_mem_cons.2 ⟨sub2_116, List.forall_mem_cons.2 ⟨sub2_117, List.forall_mem_cons.2 ⟨sub2_118, List.forall_mem_cons.2 ⟨sub2_119, List.forall_mem_cons.2 ⟨sub2_120, List.forall_mem_cons.2 ⟨sub2_121, List.forall_mem_cons.2 ⟨sub2_122, List.forall_mem_cons.2 ⟨sub2_123, List.forall_mem_cons.2 ⟨sub2_124, List.forall_mem_cons.2 ⟨sub2_125, List.forall_mem_cons.2 ⟨sub2_126, List.forall_mem_cons.2 ⟨sub2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_128 : sub2 [-1, 2, 2] = true := by decide +kernel
theorem sub2_129 : sub2 [-1, 2, 3] = true := by decide +kernel
theorem sub2_130 : sub2 [-1, 2, 4] = true := by decide +kernel
theorem sub2_131 : sub2 [-1, 2, 5] = true := by decide +kernel
theorem sub2_132 : sub2 [-1, 2, 6] = true := by decide +kernel
theorem sub2_133 : sub2 [-1, 2, 7] = true := by decide +kernel
theorem sub2_134 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_135 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_136 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_137 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_138 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_139 : sub2 [0, -2, -7] = true := by decide +kernel
theorem sub2_140 : sub2 [0, -2, -6] = true := by decide +kernel
theorem sub2_141 : sub2 [0, -2, -5] = true := by decide +kernel
theorem sub2_142 : sub2 [0, -2, -4] = true := by decide +kernel
theorem sub2_143 : sub2 [0, -2, -3] = true := by decide +kernel
theorem sub2_144 : sub2 [0, -2, -2] = true := by decide +kernel
theorem sub2_145 : sub2 [0, -2, -1] = true := by decide +kernel
theorem sub2_146 : sub2 [0, -2, 0] = true := by decide +kernel
theorem sub2_147 : sub2 [0, -2, 1] = true := by decide +kernel
theorem sub2_148 : sub2 [0, -2, 2] = true := by decide +kernel
theorem sub2_149 : sub2 [0, -2, 3] = true := by decide +kernel
theorem sub2_150 : sub2 [0, -2, 4] = true := by decide +kernel
theorem sub2_151 : sub2 [0, -2, 5] = true := by decide +kernel
theorem sub2_152 : sub2 [0, -2, 6] = true := by decide +kernel
theorem sub2_153 : sub2 [0, -1, -8] = true := by decide +kernel
theorem sub2_154 : sub2 [0, -1, -7] = true := by decide +kernel
theorem sub2_155 : sub2 [0, -1, -6] = true := by decide +kernel
theorem sub2_156 : sub2 [0, -1, -5] = true := by decide +kernel
theorem sub2_157 : sub2 [0, -1, -4] = true := by decide +kernel
theorem sub2_158 : sub2 [0, -1, -3] = true := by decide +kernel
theorem sub2_159 : sub2 [0, -1, -2] = true := by decide +kernel
theorem sb2_4 : ∀ q ∈ blk2_4, sub2 q = true := by
  unfold blk2_4
  exact List.forall_mem_cons.2 ⟨sub2_128, List.forall_mem_cons.2 ⟨sub2_129, List.forall_mem_cons.2 ⟨sub2_130, List.forall_mem_cons.2 ⟨sub2_131, List.forall_mem_cons.2 ⟨sub2_132, List.forall_mem_cons.2 ⟨sub2_133, List.forall_mem_cons.2 ⟨sub2_134, List.forall_mem_cons.2 ⟨sub2_135, List.forall_mem_cons.2 ⟨sub2_136, List.forall_mem_cons.2 ⟨sub2_137, List.forall_mem_cons.2 ⟨sub2_138, List.forall_mem_cons.2 ⟨sub2_139, List.forall_mem_cons.2 ⟨sub2_140, List.forall_mem_cons.2 ⟨sub2_141, List.forall_mem_cons.2 ⟨sub2_142, List.forall_mem_cons.2 ⟨sub2_143, List.forall_mem_cons.2 ⟨sub2_144, List.forall_mem_cons.2 ⟨sub2_145, List.forall_mem_cons.2 ⟨sub2_146, List.forall_mem_cons.2 ⟨sub2_147, List.forall_mem_cons.2 ⟨sub2_148, List.forall_mem_cons.2 ⟨sub2_149, List.forall_mem_cons.2 ⟨sub2_150, List.forall_mem_cons.2 ⟨sub2_151, List.forall_mem_cons.2 ⟨sub2_152, List.forall_mem_cons.2 ⟨sub2_153, List.forall_mem_cons.2 ⟨sub2_154, List.forall_mem_cons.2 ⟨sub2_155, List.forall_mem_cons.2 ⟨sub2_156, List.forall_mem_cons.2 ⟨sub2_157, List.forall_mem_cons.2 ⟨sub2_158, List.forall_mem_cons.2 ⟨sub2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_160 : sub2 [0, -1, -1] = true := by decide +kernel
theorem sub2_161 : sub2 [0, -1, 0] = true := by decide +kernel
theorem sub2_162 : sub2 [0, -1, 1] = true := by decide +kernel
theorem sub2_163 : sub2 [0, -1, 2] = true := by decide +kernel
theorem sub2_164 : sub2 [0, -1, 3] = true := by decide +kernel
theorem sub2_165 : sub2 [0, -1, 4] = true := by decide +kernel
theorem sub2_166 : sub2 [0, -1, 5] = true := by decide +kernel
theorem sub2_167 : sub2 [0, -1, 6] = true := by decide +kernel
theorem sub2_168 : sub2 [0, -1, 7] = true := by decide +kernel
theorem sub2_169 : sub2 [0, 0, -8] = true := by decide +kernel
theorem sub2_170 : sub2 [0, 0, -7] = true := by decide +kernel
theorem sub2_171 : sub2 [0, 0, -6] = true := by decide +kernel
theorem sub2_172 : sub2 [0, 0, -5] = true := by decide +kernel
theorem sub2_173 : sub2 [0, 0, -4] = true := by decide +kernel
theorem sub2_174 : sub2 [0, 0, -3] = true := by decide +kernel
theorem sub2_175 : sub2 [0, 0, -2] = true := by decide +kernel
theorem sub2_176 : sub2 [0, 0, -1] = true := by decide +kernel
theorem sub2_177 : sub2 [0, 0, 0] = true := by decide +kernel
theorem sub2_178 : sub2 [0, 0, 1] = true := by decide +kernel
theorem sub2_179 : sub2 [0, 0, 2] = true := by decide +kernel
theorem sub2_180 : sub2 [0, 0, 3] = true := by decide +kernel
theorem sub2_181 : sub2 [0, 0, 4] = true := by decide +kernel
theorem sub2_182 : sub2 [0, 0, 5] = true := by decide +kernel
theorem sub2_183 : sub2 [0, 0, 6] = true := by decide +kernel
theorem sub2_184 : sub2 [0, 0, 7] = true := by decide +kernel
theorem sub2_185 : sub2 [0, 1, -8] = true := by decide +kernel
theorem sub2_186 : sub2 [0, 1, -7] = true := by decide +kernel
theorem sub2_187 : sub2 [0, 1, -6] = true := by decide +kernel
theorem sub2_188 : sub2 [0, 1, -5] = true := by decide +kernel
theorem sub2_189 : sub2 [0, 1, -4] = true := by decide +kernel
theorem sub2_190 : sub2 [0, 1, -3] = true := by decide +kernel
theorem sub2_191 : sub2 [0, 1, -2] = true := by decide +kernel
theorem sb2_5 : ∀ q ∈ blk2_5, sub2 q = true := by
  unfold blk2_5
  exact List.forall_mem_cons.2 ⟨sub2_160, List.forall_mem_cons.2 ⟨sub2_161, List.forall_mem_cons.2 ⟨sub2_162, List.forall_mem_cons.2 ⟨sub2_163, List.forall_mem_cons.2 ⟨sub2_164, List.forall_mem_cons.2 ⟨sub2_165, List.forall_mem_cons.2 ⟨sub2_166, List.forall_mem_cons.2 ⟨sub2_167, List.forall_mem_cons.2 ⟨sub2_168, List.forall_mem_cons.2 ⟨sub2_169, List.forall_mem_cons.2 ⟨sub2_170, List.forall_mem_cons.2 ⟨sub2_171, List.forall_mem_cons.2 ⟨sub2_172, List.forall_mem_cons.2 ⟨sub2_173, List.forall_mem_cons.2 ⟨sub2_174, List.forall_mem_cons.2 ⟨sub2_175, List.forall_mem_cons.2 ⟨sub2_176, List.forall_mem_cons.2 ⟨sub2_177, List.forall_mem_cons.2 ⟨sub2_178, List.forall_mem_cons.2 ⟨sub2_179, List.forall_mem_cons.2 ⟨sub2_180, List.forall_mem_cons.2 ⟨sub2_181, List.forall_mem_cons.2 ⟨sub2_182, List.forall_mem_cons.2 ⟨sub2_183, List.forall_mem_cons.2 ⟨sub2_184, List.forall_mem_cons.2 ⟨sub2_185, List.forall_mem_cons.2 ⟨sub2_186, List.forall_mem_cons.2 ⟨sub2_187, List.forall_mem_cons.2 ⟨sub2_188, List.forall_mem_cons.2 ⟨sub2_189, List.forall_mem_cons.2 ⟨sub2_190, List.forall_mem_cons.2 ⟨sub2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_192 : sub2 [0, 1, -1] = true := by decide +kernel
theorem sub2_193 : sub2 [0, 1, 0] = true := by decide +kernel
theorem sub2_194 : sub2 [0, 1, 1] = true := by decide +kernel
theorem sub2_195 : sub2 [0, 1, 2] = true := by decide +kernel
theorem sub2_196 : sub2 [0, 1, 3] = true := by decide +kernel
theorem sub2_197 : sub2 [0, 1, 4] = true := by decide +kernel
theorem sub2_198 : sub2 [0, 1, 5] = true := by decide +kernel
theorem sub2_199 : sub2 [0, 1, 6] = true := by decide +kernel
theorem sub2_200 : sub2 [0, 1, 7] = true := by decide +kernel
theorem sub2_201 : sub2 [0, 2, -7] = true := by decide +kernel
theorem sub2_202 : sub2 [0, 2, -6] = true := by decide +kernel
theorem sub2_203 : sub2 [0, 2, -5] = true := by decide +kernel
theorem sub2_204 : sub2 [0, 2, -4] = true := by decide +kernel
theorem sub2_205 : sub2 [0, 2, -3] = true := by decide +kernel
theorem sub2_206 : sub2 [0, 2, -2] = true := by decide +kernel
theorem sub2_207 : sub2 [0, 2, -1] = true := by decide +kernel
theorem sub2_208 : sub2 [0, 2, 0] = true := by decide +kernel
theorem sub2_209 : sub2 [0, 2, 1] = true := by decide +kernel
theorem sub2_210 : sub2 [0, 2, 2] = true := by decide +kernel
theorem sub2_211 : sub2 [0, 2, 3] = true := by decide +kernel
theorem sub2_212 : sub2 [0, 2, 4] = true := by decide +kernel
theorem sub2_213 : sub2 [0, 2, 5] = true := by decide +kernel
theorem sub2_214 : sub2 [0, 2, 6] = true := by decide +kernel
theorem sub2_215 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_216 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_217 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_218 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_219 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_220 : sub2 [1, -2, -8] = true := by decide +kernel
theorem sub2_221 : sub2 [1, -2, -7] = true := by decide +kernel
theorem sub2_222 : sub2 [1, -2, -6] = true := by decide +kernel
theorem sub2_223 : sub2 [1, -2, -5] = true := by decide +kernel
theorem sb2_6 : ∀ q ∈ blk2_6, sub2 q = true := by
  unfold blk2_6
  exact List.forall_mem_cons.2 ⟨sub2_192, List.forall_mem_cons.2 ⟨sub2_193, List.forall_mem_cons.2 ⟨sub2_194, List.forall_mem_cons.2 ⟨sub2_195, List.forall_mem_cons.2 ⟨sub2_196, List.forall_mem_cons.2 ⟨sub2_197, List.forall_mem_cons.2 ⟨sub2_198, List.forall_mem_cons.2 ⟨sub2_199, List.forall_mem_cons.2 ⟨sub2_200, List.forall_mem_cons.2 ⟨sub2_201, List.forall_mem_cons.2 ⟨sub2_202, List.forall_mem_cons.2 ⟨sub2_203, List.forall_mem_cons.2 ⟨sub2_204, List.forall_mem_cons.2 ⟨sub2_205, List.forall_mem_cons.2 ⟨sub2_206, List.forall_mem_cons.2 ⟨sub2_207, List.forall_mem_cons.2 ⟨sub2_208, List.forall_mem_cons.2 ⟨sub2_209, List.forall_mem_cons.2 ⟨sub2_210, List.forall_mem_cons.2 ⟨sub2_211, List.forall_mem_cons.2 ⟨sub2_212, List.forall_mem_cons.2 ⟨sub2_213, List.forall_mem_cons.2 ⟨sub2_214, List.forall_mem_cons.2 ⟨sub2_215, List.forall_mem_cons.2 ⟨sub2_216, List.forall_mem_cons.2 ⟨sub2_217, List.forall_mem_cons.2 ⟨sub2_218, List.forall_mem_cons.2 ⟨sub2_219, List.forall_mem_cons.2 ⟨sub2_220, List.forall_mem_cons.2 ⟨sub2_221, List.forall_mem_cons.2 ⟨sub2_222, List.forall_mem_cons.2 ⟨sub2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_224 : sub2 [1, -2, -4] = true := by decide +kernel
theorem sub2_225 : sub2 [1, -2, -3] = true := by decide +kernel
theorem sub2_226 : sub2 [1, -2, -2] = true := by decide +kernel
theorem sub2_227 : sub2 [1, -2, -1] = true := by decide +kernel
theorem sub2_228 : sub2 [1, -2, 0] = true := by decide +kernel
theorem sub2_229 : sub2 [1, -2, 1] = true := by decide +kernel
theorem sub2_230 : sub2 [1, -2, 2] = true := by decide +kernel
theorem sub2_231 : sub2 [1, -2, 3] = true := by decide +kernel
theorem sub2_232 : sub2 [1, -2, 4] = true := by decide +kernel
theorem sub2_233 : sub2 [1, -2, 5] = true := by decide +kernel
theorem sub2_234 : sub2 [1, -2, 6] = true := by decide +kernel
theorem sub2_235 : sub2 [1, -1, -8] = true := by decide +kernel
theorem sub2_236 : sub2 [1, -1, -7] = true := by decide +kernel
theorem sub2_237 : sub2 [1, -1, -6] = true := by decide +kernel
theorem sub2_238 : sub2 [1, -1, -5] = true := by decide +kernel
theorem sub2_239 : sub2 [1, -1, -4] = true := by decide +kernel
theorem sub2_240 : sub2 [1, -1, -3] = true := by decide +kernel
theorem sub2_241 : sub2 [1, -1, -2] = true := by decide +kernel
theorem sub2_242 : sub2 [1, -1, -1] = true := by decide +kernel
theorem sub2_243 : sub2 [1, -1, 0] = true := by decide +kernel
theorem sub2_244 : sub2 [1, -1, 1] = true := by decide +kernel
theorem sub2_245 : sub2 [1, -1, 2] = true := by decide +kernel
theorem sub2_246 : sub2 [1, -1, 3] = true := by decide +kernel
theorem sub2_247 : sub2 [1, -1, 4] = true := by decide +kernel
theorem sub2_248 : sub2 [1, -1, 5] = true := by decide +kernel
theorem sub2_249 : sub2 [1, -1, 6] = true := by decide +kernel
theorem sub2_250 : sub2 [1, 0, -8] = true := by decide +kernel
theorem sub2_251 : sub2 [1, 0, -7] = true := by decide +kernel
theorem sub2_252 : sub2 [1, 0, -6] = true := by decide +kernel
theorem sub2_253 : sub2 [1, 0, -5] = true := by decide +kernel
theorem sub2_254 : sub2 [1, 0, -4] = true := by decide +kernel
theorem sub2_255 : sub2 [1, 0, -3] = true := by decide +kernel
theorem sb2_7 : ∀ q ∈ blk2_7, sub2 q = true := by
  unfold blk2_7
  exact List.forall_mem_cons.2 ⟨sub2_224, List.forall_mem_cons.2 ⟨sub2_225, List.forall_mem_cons.2 ⟨sub2_226, List.forall_mem_cons.2 ⟨sub2_227, List.forall_mem_cons.2 ⟨sub2_228, List.forall_mem_cons.2 ⟨sub2_229, List.forall_mem_cons.2 ⟨sub2_230, List.forall_mem_cons.2 ⟨sub2_231, List.forall_mem_cons.2 ⟨sub2_232, List.forall_mem_cons.2 ⟨sub2_233, List.forall_mem_cons.2 ⟨sub2_234, List.forall_mem_cons.2 ⟨sub2_235, List.forall_mem_cons.2 ⟨sub2_236, List.forall_mem_cons.2 ⟨sub2_237, List.forall_mem_cons.2 ⟨sub2_238, List.forall_mem_cons.2 ⟨sub2_239, List.forall_mem_cons.2 ⟨sub2_240, List.forall_mem_cons.2 ⟨sub2_241, List.forall_mem_cons.2 ⟨sub2_242, List.forall_mem_cons.2 ⟨sub2_243, List.forall_mem_cons.2 ⟨sub2_244, List.forall_mem_cons.2 ⟨sub2_245, List.forall_mem_cons.2 ⟨sub2_246, List.forall_mem_cons.2 ⟨sub2_247, List.forall_mem_cons.2 ⟨sub2_248, List.forall_mem_cons.2 ⟨sub2_249, List.forall_mem_cons.2 ⟨sub2_250, List.forall_mem_cons.2 ⟨sub2_251, List.forall_mem_cons.2 ⟨sub2_252, List.forall_mem_cons.2 ⟨sub2_253, List.forall_mem_cons.2 ⟨sub2_254, List.forall_mem_cons.2 ⟨sub2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_256 : sub2 [1, 0, -2] = true := by decide +kernel
theorem sub2_257 : sub2 [1, 0, -1] = true := by decide +kernel
theorem sub2_258 : sub2 [1, 0, 0] = true := by decide +kernel
theorem sub2_259 : sub2 [1, 0, 1] = true := by decide +kernel
theorem sub2_260 : sub2 [1, 0, 2] = true := by decide +kernel
theorem sub2_261 : sub2 [1, 0, 3] = true := by decide +kernel
theorem sub2_262 : sub2 [1, 0, 4] = true := by decide +kernel
theorem sub2_263 : sub2 [1, 0, 5] = true := by decide +kernel
theorem sub2_264 : sub2 [1, 0, 6] = true := by decide +kernel
theorem sub2_265 : sub2 [1, 0, 7] = true := by decide +kernel
theorem sub2_266 : sub2 [1, 1, -7] = true := by decide +kernel
theorem sub2_267 : sub2 [1, 1, -6] = true := by decide +kernel
theorem sub2_268 : sub2 [1, 1, -5] = true := by decide +kernel
theorem sub2_269 : sub2 [1, 1, -4] = true := by decide +kernel
theorem sub2_270 : sub2 [1, 1, -3] = true := by decide +kernel
theorem sub2_271 : sub2 [1, 1, -2] = true := by decide +kernel
theorem sub2_272 : sub2 [1, 1, -1] = true := by decide +kernel
theorem sub2_273 : sub2 [1, 1, 0] = true := by decide +kernel
theorem sub2_274 : sub2 [1, 1, 1] = true := by decide +kernel
theorem sub2_275 : sub2 [1, 1, 2] = true := by decide +kernel
theorem sub2_276 : sub2 [1, 1, 3] = true := by decide +kernel
theorem sub2_277 : sub2 [1, 1, 4] = true := by decide +kernel
theorem sub2_278 : sub2 [1, 1, 5] = true := by decide +kernel
theorem sub2_279 : sub2 [1, 1, 6] = true := by decide +kernel
theorem sub2_280 : sub2 [1, 2, -7] = true := by decide +kernel
theorem sub2_281 : sub2 [1, 2, -6] = true := by decide +kernel
theorem sub2_282 : sub2 [1, 2, -5] = true := by decide +kernel
theorem sub2_283 : sub2 [1, 2, -4] = true := by decide +kernel
theorem sub2_284 : sub2 [1, 2, -3] = true := by decide +kernel
theorem sub2_285 : sub2 [1, 2, -2] = true := by decide +kernel
theorem sub2_286 : sub2 [1, 2, -1] = true := by decide +kernel
theorem sub2_287 : sub2 [1, 2, 0] = true := by decide +kernel
theorem sb2_8 : ∀ q ∈ blk2_8, sub2 q = true := by
  unfold blk2_8
  exact List.forall_mem_cons.2 ⟨sub2_256, List.forall_mem_cons.2 ⟨sub2_257, List.forall_mem_cons.2 ⟨sub2_258, List.forall_mem_cons.2 ⟨sub2_259, List.forall_mem_cons.2 ⟨sub2_260, List.forall_mem_cons.2 ⟨sub2_261, List.forall_mem_cons.2 ⟨sub2_262, List.forall_mem_cons.2 ⟨sub2_263, List.forall_mem_cons.2 ⟨sub2_264, List.forall_mem_cons.2 ⟨sub2_265, List.forall_mem_cons.2 ⟨sub2_266, List.forall_mem_cons.2 ⟨sub2_267, List.forall_mem_cons.2 ⟨sub2_268, List.forall_mem_cons.2 ⟨sub2_269, List.forall_mem_cons.2 ⟨sub2_270, List.forall_mem_cons.2 ⟨sub2_271, List.forall_mem_cons.2 ⟨sub2_272, List.forall_mem_cons.2 ⟨sub2_273, List.forall_mem_cons.2 ⟨sub2_274, List.forall_mem_cons.2 ⟨sub2_275, List.forall_mem_cons.2 ⟨sub2_276, List.forall_mem_cons.2 ⟨sub2_277, List.forall_mem_cons.2 ⟨sub2_278, List.forall_mem_cons.2 ⟨sub2_279, List.forall_mem_cons.2 ⟨sub2_280, List.forall_mem_cons.2 ⟨sub2_281, List.forall_mem_cons.2 ⟨sub2_282, List.forall_mem_cons.2 ⟨sub2_283, List.forall_mem_cons.2 ⟨sub2_284, List.forall_mem_cons.2 ⟨sub2_285, List.forall_mem_cons.2 ⟨sub2_286, List.forall_mem_cons.2 ⟨sub2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_288 : sub2 [1, 2, 1] = true := by decide +kernel
theorem sub2_289 : sub2 [1, 2, 2] = true := by decide +kernel
theorem sub2_290 : sub2 [1, 2, 3] = true := by decide +kernel
theorem sub2_291 : sub2 [1, 2, 4] = true := by decide +kernel
theorem sub2_292 : sub2 [1, 2, 5] = true := by decide +kernel
theorem sub2_293 : sub2 [1, 2, 6] = true := by decide +kernel
theorem sub2_294 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_295 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_296 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_297 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_298 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_299 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_300 : sub2 [2, -1, -7] = true := by decide +kernel
theorem sub2_301 : sub2 [2, -1, -6] = true := by decide +kernel
theorem sub2_302 : sub2 [2, -1, -5] = true := by decide +kernel
theorem sub2_303 : sub2 [2, -1, -4] = true := by decide +kernel
theorem sub2_304 : sub2 [2, -1, -3] = true := by decide +kernel
theorem sub2_305 : sub2 [2, -1, -2] = true := by decide +kernel
theorem sub2_306 : sub2 [2, -1, -1] = true := by decide +kernel
theorem sub2_307 : sub2 [2, -1, 0] = true := by decide +kernel
theorem sub2_308 : sub2 [2, -1, 1] = true := by decide +kernel
theorem sub2_309 : sub2 [2, -1, 2] = true := by decide +kernel
theorem sub2_310 : sub2 [2, -1, 3] = true := by decide +kernel
theorem sub2_311 : sub2 [2, -1, 4] = true := by decide +kernel
theorem sub2_312 : sub2 [2, -1, 5] = true := by decide +kernel
theorem sub2_313 : sub2 [2, -1, 6] = true := by decide +kernel
theorem sub2_314 : sub2 [2, 0, -7] = true := by decide +kernel
theorem sub2_315 : sub2 [2, 0, -6] = true := by decide +kernel
theorem sub2_316 : sub2 [2, 0, -5] = true := by decide +kernel
theorem sub2_317 : sub2 [2, 0, -4] = true := by decide +kernel
theorem sub2_318 : sub2 [2, 0, -3] = true := by decide +kernel
theorem sub2_319 : sub2 [2, 0, -2] = true := by decide +kernel
theorem sb2_9 : ∀ q ∈ blk2_9, sub2 q = true := by
  unfold blk2_9
  exact List.forall_mem_cons.2 ⟨sub2_288, List.forall_mem_cons.2 ⟨sub2_289, List.forall_mem_cons.2 ⟨sub2_290, List.forall_mem_cons.2 ⟨sub2_291, List.forall_mem_cons.2 ⟨sub2_292, List.forall_mem_cons.2 ⟨sub2_293, List.forall_mem_cons.2 ⟨sub2_294, List.forall_mem_cons.2 ⟨sub2_295, List.forall_mem_cons.2 ⟨sub2_296, List.forall_mem_cons.2 ⟨sub2_297, List.forall_mem_cons.2 ⟨sub2_298, List.forall_mem_cons.2 ⟨sub2_299, List.forall_mem_cons.2 ⟨sub2_300, List.forall_mem_cons.2 ⟨sub2_301, List.forall_mem_cons.2 ⟨sub2_302, List.forall_mem_cons.2 ⟨sub2_303, List.forall_mem_cons.2 ⟨sub2_304, List.forall_mem_cons.2 ⟨sub2_305, List.forall_mem_cons.2 ⟨sub2_306, List.forall_mem_cons.2 ⟨sub2_307, List.forall_mem_cons.2 ⟨sub2_308, List.forall_mem_cons.2 ⟨sub2_309, List.forall_mem_cons.2 ⟨sub2_310, List.forall_mem_cons.2 ⟨sub2_311, List.forall_mem_cons.2 ⟨sub2_312, List.forall_mem_cons.2 ⟨sub2_313, List.forall_mem_cons.2 ⟨sub2_314, List.forall_mem_cons.2 ⟨sub2_315, List.forall_mem_cons.2 ⟨sub2_316, List.forall_mem_cons.2 ⟨sub2_317, List.forall_mem_cons.2 ⟨sub2_318, List.forall_mem_cons.2 ⟨sub2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
