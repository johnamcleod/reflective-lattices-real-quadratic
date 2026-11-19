import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_32 : sub6 [-1, 1, 1] = true := by decide +kernel
theorem sub6_33 : sub6 [-1, 1, 2] = true := by decide +kernel
theorem sub6_34 : sub6 [-1, 1, 3] = true := by decide +kernel
theorem sub6_35 : sub6 [-1, 1, 4] = true := by decide +kernel
theorem sub6_36 : sub6 [-1, 1, 5] = true := by decide +kernel
theorem sub6_37 : sub6 [-1, 1, 6] = true := by decide +kernel
theorem sub6_38 : sub6 [-1, 1, 7] = true := by decide +kernel
theorem sub6_39 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_40 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_41 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_42 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_43 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_44 : sub6 [0, -1, -8] = true := by decide +kernel
theorem sub6_45 : sub6 [0, -1, -7] = true := by decide +kernel
theorem sub6_46 : sub6 [0, -1, -6] = true := by decide +kernel
theorem sub6_47 : sub6 [0, -1, -5] = true := by decide +kernel
theorem sub6_48 : sub6 [0, -1, -4] = true := by decide +kernel
theorem sub6_49 : sub6 [0, -1, -3] = true := by decide +kernel
theorem sub6_50 : sub6 [0, -1, -2] = true := by decide +kernel
theorem sub6_51 : sub6 [0, -1, -1] = true := by decide +kernel
theorem sub6_52 : sub6 [0, -1, 0] = true := by decide +kernel
theorem sub6_53 : sub6 [0, -1, 1] = true := by decide +kernel
theorem sub6_54 : sub6 [0, -1, 2] = true := by decide +kernel
theorem sub6_55 : sub6 [0, -1, 3] = true := by decide +kernel
theorem sub6_56 : sub6 [0, -1, 4] = true := by decide +kernel
theorem sub6_57 : sub6 [0, -1, 5] = true := by decide +kernel
theorem sub6_58 : sub6 [0, -1, 6] = true := by decide +kernel
theorem sub6_59 : sub6 [0, -1, 7] = true := by decide +kernel
theorem sub6_60 : sub6 [0, 0, -8] = true := by decide +kernel
theorem sub6_61 : sub6 [0, 0, -7] = true := by decide +kernel
theorem sub6_62 : sub6 [0, 0, -6] = true := by decide +kernel
theorem sub6_63 : sub6 [0, 0, -5] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [0, 0, -4] = true := by decide +kernel
theorem sub6_65 : sub6 [0, 0, -3] = true := by decide +kernel
theorem sub6_66 : sub6 [0, 0, -2] = true := by decide +kernel
theorem sub6_67 : sub6 [0, 0, -1] = true := by decide +kernel
theorem sub6_68 : sub6 [0, 0, 0] = true := by decide +kernel
theorem sub6_69 : sub6 [0, 0, 1] = true := by decide +kernel
theorem sub6_70 : sub6 [0, 0, 2] = true := by decide +kernel
theorem sub6_71 : sub6 [0, 0, 3] = true := by decide +kernel
theorem sub6_72 : sub6 [0, 0, 4] = true := by decide +kernel
theorem sub6_73 : sub6 [0, 0, 5] = true := by decide +kernel
theorem sub6_74 : sub6 [0, 0, 6] = true := by decide +kernel
theorem sub6_75 : sub6 [0, 0, 7] = true := by decide +kernel
theorem sub6_76 : sub6 [0, 1, -8] = true := by decide +kernel
theorem sub6_77 : sub6 [0, 1, -7] = true := by decide +kernel
theorem sub6_78 : sub6 [0, 1, -6] = true := by decide +kernel
theorem sub6_79 : sub6 [0, 1, -5] = true := by decide +kernel
theorem sub6_80 : sub6 [0, 1, -4] = true := by decide +kernel
theorem sub6_81 : sub6 [0, 1, -3] = true := by decide +kernel
theorem sub6_82 : sub6 [0, 1, -2] = true := by decide +kernel
theorem sub6_83 : sub6 [0, 1, -1] = true := by decide +kernel
theorem sub6_84 : sub6 [0, 1, 0] = true := by decide +kernel
theorem sub6_85 : sub6 [0, 1, 1] = true := by decide +kernel
theorem sub6_86 : sub6 [0, 1, 2] = true := by decide +kernel
theorem sub6_87 : sub6 [0, 1, 3] = true := by decide +kernel
theorem sub6_88 : sub6 [0, 1, 4] = true := by decide +kernel
theorem sub6_89 : sub6 [0, 1, 5] = true := by decide +kernel
theorem sub6_90 : sub6 [0, 1, 6] = true := by decide +kernel
theorem sub6_91 : sub6 [0, 1, 7] = true := by decide +kernel
theorem sub6_92 : sub6 [0, 2] = true := by decide +kernel
theorem sub6_93 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_94 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_95 : sub6 [1, -3] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_97 : sub6 [1, -1, -8] = true := by decide +kernel
theorem sub6_98 : sub6 [1, -1, -7] = true := by decide +kernel
theorem sub6_99 : sub6 [1, -1, -6] = true := by decide +kernel
theorem sub6_100 : sub6 [1, -1, -5] = true := by decide +kernel
theorem sub6_101 : sub6 [1, -1, -4] = true := by decide +kernel
theorem sub6_102 : sub6 [1, -1, -3] = true := by decide +kernel
theorem sub6_103 : sub6 [1, -1, -2] = true := by decide +kernel
theorem sub6_104 : sub6 [1, -1, -1] = true := by decide +kernel
theorem sub6_105 : sub6 [1, -1, 0] = true := by decide +kernel
theorem sub6_106 : sub6 [1, -1, 1] = true := by decide +kernel
theorem sub6_107 : sub6 [1, -1, 2] = true := by decide +kernel
theorem sub6_108 : sub6 [1, -1, 3] = true := by decide +kernel
theorem sub6_109 : sub6 [1, -1, 4] = true := by decide +kernel
theorem sub6_110 : sub6 [1, -1, 5] = true := by decide +kernel
theorem sub6_111 : sub6 [1, -1, 6] = true := by decide +kernel
theorem sub6_112 : sub6 [1, 0, -8] = true := by decide +kernel
theorem sub6_113 : sub6 [1, 0, -7] = true := by decide +kernel
theorem sub6_114 : sub6 [1, 0, -6] = true := by decide +kernel
theorem sub6_115 : sub6 [1, 0, -5] = true := by decide +kernel
theorem sub6_116 : sub6 [1, 0, -4] = true := by decide +kernel
theorem sub6_117 : sub6 [1, 0, -3] = true := by decide +kernel
theorem sub6_118 : sub6 [1, 0, -2] = true := by decide +kernel
theorem sub6_119 : sub6 [1, 0, -1] = true := by decide +kernel
theorem sub6_120 : sub6 [1, 0, 0] = true := by decide +kernel
theorem sub6_121 : sub6 [1, 0, 1] = true := by decide +kernel
theorem sub6_122 : sub6 [1, 0, 2] = true := by decide +kernel
theorem sub6_123 : sub6 [1, 0, 3] = true := by decide +kernel
theorem sub6_124 : sub6 [1, 0, 4] = true := by decide +kernel
theorem sub6_125 : sub6 [1, 0, 5] = true := by decide +kernel
theorem sub6_126 : sub6 [1, 0, 6] = true := by decide +kernel
theorem sub6_127 : sub6 [1, 1] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_cons.2 ⟨sub6_102, List.forall_mem_cons.2 ⟨sub6_103, List.forall_mem_cons.2 ⟨sub6_104, List.forall_mem_cons.2 ⟨sub6_105, List.forall_mem_cons.2 ⟨sub6_106, List.forall_mem_cons.2 ⟨sub6_107, List.forall_mem_cons.2 ⟨sub6_108, List.forall_mem_cons.2 ⟨sub6_109, List.forall_mem_cons.2 ⟨sub6_110, List.forall_mem_cons.2 ⟨sub6_111, List.forall_mem_cons.2 ⟨sub6_112, List.forall_mem_cons.2 ⟨sub6_113, List.forall_mem_cons.2 ⟨sub6_114, List.forall_mem_cons.2 ⟨sub6_115, List.forall_mem_cons.2 ⟨sub6_116, List.forall_mem_cons.2 ⟨sub6_117, List.forall_mem_cons.2 ⟨sub6_118, List.forall_mem_cons.2 ⟨sub6_119, List.forall_mem_cons.2 ⟨sub6_120, List.forall_mem_cons.2 ⟨sub6_121, List.forall_mem_cons.2 ⟨sub6_122, List.forall_mem_cons.2 ⟨sub6_123, List.forall_mem_cons.2 ⟨sub6_124, List.forall_mem_cons.2 ⟨sub6_125, List.forall_mem_cons.2 ⟨sub6_126, List.forall_mem_cons.2 ⟨sub6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_128 : sub6 [1, 2] = true := by decide +kernel
theorem sub6_129 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_130 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_131 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_132 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_133 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_134 : sub6 [2, 1] = true := by decide +kernel
theorem sb6_4 : ∀ q ∈ blk6_4, sub6 q = true := by
  unfold blk6_4
  exact List.forall_mem_cons.2 ⟨sub6_128, List.forall_mem_cons.2 ⟨sub6_129, List.forall_mem_cons.2 ⟨sub6_130, List.forall_mem_cons.2 ⟨sub6_131, List.forall_mem_cons.2 ⟨sub6_132, List.forall_mem_cons.2 ⟨sub6_133, List.forall_mem_cons.2 ⟨sub6_134, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-6] = true := by decide +kernel
theorem sub7_1 : sub7 [-5, -5] = true := by decide +kernel
theorem sub7_2 : sub7 [-5, -4] = true := by decide +kernel
theorem sub7_3 : sub7 [-5, -3] = true := by decide +kernel
theorem sub7_4 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_5 : sub7 [-5, -1] = true := by decide +kernel
theorem sub7_6 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_7 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_8 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_9 : sub7 [-5, 3] = true := by decide +kernel
theorem sub7_10 : sub7 [-4, -6] = true := by decide +kernel
theorem sub7_11 : sub7 [-4, -5] = true := by decide +kernel
theorem sub7_12 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_13 : sub7 [-4, -3] = true := by decide +kernel
theorem sub7_14 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_15 : sub7 [-4, -1] = true := by decide +kernel
theorem sub7_16 : sub7 [-4, 0] = true := by decide +kernel
theorem sub7_17 : sub7 [-4, 1] = true := by decide +kernel
theorem sub7_18 : sub7 [-4, 2] = true := by decide +kernel
theorem sub7_19 : sub7 [-4, 3] = true := by decide +kernel
theorem sub7_20 : sub7 [-4, 4] = true := by decide +kernel
theorem sub7_21 : sub7 [-3, -6] = true := by decide +kernel
theorem sub7_22 : sub7 [-3, -5] = true := by decide +kernel
theorem sub7_23 : sub7 [-3, -4] = true := by decide +kernel
theorem sub7_24 : sub7 [-3, -3] = true := by decide +kernel
theorem sub7_25 : sub7 [-3, -2] = true := by decide +kernel
theorem sub7_26 : sub7 [-3, -1] = true := by decide +kernel
theorem sub7_27 : sub7 [-3, 0] = true := by decide +kernel
theorem sub7_28 : sub7 [-3, 1] = true := by decide +kernel
theorem sub7_29 : sub7 [-3, 2] = true := by decide +kernel
theorem sub7_30 : sub7 [-3, 3] = true := by decide +kernel
theorem sub7_31 : sub7 [-3, 4] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [-3, 5] = true := by decide +kernel
theorem sub7_33 : sub7 [-2, -7] = true := by decide +kernel
theorem sub7_34 : sub7 [-2, -6] = true := by decide +kernel
theorem sub7_35 : sub7 [-2, -5] = true := by decide +kernel
theorem sub7_36 : sub7 [-2, -4] = true := by decide +kernel
theorem sub7_37 : sub7 [-2, -3] = true := by decide +kernel
theorem sub7_38 : sub7 [-2, -2] = true := by decide +kernel
theorem sub7_39 : sub7 [-2, -1] = true := by decide +kernel
theorem sub7_40 : sub7 [-2, 0] = true := by decide +kernel
theorem sub7_41 : sub7 [-2, 1] = true := by decide +kernel
theorem sub7_42 : sub7 [-2, 2] = true := by decide +kernel
theorem sub7_43 : sub7 [-2, 3] = true := by decide +kernel
theorem sub7_44 : sub7 [-2, 4] = true := by decide +kernel
theorem sub7_45 : sub7 [-2, 5] = true := by decide +kernel
theorem sub7_46 : sub7 [-1, -7] = true := by decide +kernel
theorem sub7_47 : sub7 [-1, -6] = true := by decide +kernel
theorem sub7_48 : sub7 [-1, -5] = true := by decide +kernel
theorem sub7_49 : sub7 [-1, -4] = true := by decide +kernel
theorem sub7_50 : sub7 [-1, -3] = true := by decide +kernel
theorem sub7_51 : sub7 [-1, -2] = true := by decide +kernel
theorem sub7_52 : sub7 [-1, -1, -7] = true := by decide +kernel
theorem sub7_53 : sub7 [-1, -1, -6] = true := by decide +kernel
theorem sub7_54 : sub7 [-1, -1, -5] = true := by decide +kernel
theorem sub7_55 : sub7 [-1, -1, -4] = true := by decide +kernel
theorem sub7_56 : sub7 [-1, -1, -3] = true := by decide +kernel
theorem sub7_57 : sub7 [-1, -1, -2] = true := by decide +kernel
theorem sub7_58 : sub7 [-1, -1, -1] = true := by decide +kernel
theorem sub7_59 : sub7 [-1, -1, 0] = true := by decide +kernel
theorem sub7_60 : sub7 [-1, -1, 1] = true := by decide +kernel
theorem sub7_61 : sub7 [-1, -1, 2] = true := by decide +kernel
theorem sub7_62 : sub7 [-1, -1, 3] = true := by decide +kernel
theorem sub7_63 : sub7 [-1, -1, 4] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_cons.2 ⟨sub7_58, List.forall_mem_cons.2 ⟨sub7_59, List.forall_mem_cons.2 ⟨sub7_60, List.forall_mem_cons.2 ⟨sub7_61, List.forall_mem_cons.2 ⟨sub7_62, List.forall_mem_cons.2 ⟨sub7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_64 : sub7 [-1, -1, 5] = true := by decide +kernel
theorem sub7_65 : sub7 [-1, -1, 6] = true := by decide +kernel
theorem sub7_66 : sub7 [-1, 0, -6] = true := by decide +kernel
theorem sub7_67 : sub7 [-1, 0, -5] = true := by decide +kernel
theorem sub7_68 : sub7 [-1, 0, -4] = true := by decide +kernel
theorem sub7_69 : sub7 [-1, 0, -3] = true := by decide +kernel
theorem sub7_70 : sub7 [-1, 0, -2] = true := by decide +kernel
theorem sub7_71 : sub7 [-1, 0, -1] = true := by decide +kernel
theorem sub7_72 : sub7 [-1, 0, 0] = true := by decide +kernel
theorem sub7_73 : sub7 [-1, 0, 1] = true := by decide +kernel
theorem sub7_74 : sub7 [-1, 0, 2] = true := by decide +kernel
theorem sub7_75 : sub7 [-1, 0, 3] = true := by decide +kernel
theorem sub7_76 : sub7 [-1, 0, 4] = true := by decide +kernel
theorem sub7_77 : sub7 [-1, 0, 5] = true := by decide +kernel
theorem sub7_78 : sub7 [-1, 0, 6] = true := by decide +kernel
theorem sub7_79 : sub7 [-1, 1, -6] = true := by decide +kernel
theorem sub7_80 : sub7 [-1, 1, -5] = true := by decide +kernel
theorem sub7_81 : sub7 [-1, 1, -4] = true := by decide +kernel
theorem sub7_82 : sub7 [-1, 1, -3] = true := by decide +kernel
theorem sub7_83 : sub7 [-1, 1, -2] = true := by decide +kernel
theorem sub7_84 : sub7 [-1, 1, -1] = true := by decide +kernel
theorem sub7_85 : sub7 [-1, 1, 0] = true := by decide +kernel
theorem sub7_86 : sub7 [-1, 1, 1] = true := by decide +kernel
theorem sub7_87 : sub7 [-1, 1, 2] = true := by decide +kernel
theorem sub7_88 : sub7 [-1, 1, 3] = true := by decide +kernel
theorem sub7_89 : sub7 [-1, 1, 4] = true := by decide +kernel
theorem sub7_90 : sub7 [-1, 1, 5] = true := by decide +kernel
theorem sub7_91 : sub7 [-1, 1, 6] = true := by decide +kernel
theorem sub7_92 : sub7 [-1, 2] = true := by decide +kernel
theorem sub7_93 : sub7 [-1, 3] = true := by decide +kernel
theorem sub7_94 : sub7 [-1, 4] = true := by decide +kernel
theorem sub7_95 : sub7 [-1, 5] = true := by decide +kernel
theorem sb7_2 : ∀ q ∈ blk7_2, sub7 q = true := by
  unfold blk7_2
  exact List.forall_mem_cons.2 ⟨sub7_64, List.forall_mem_cons.2 ⟨sub7_65, List.forall_mem_cons.2 ⟨sub7_66, List.forall_mem_cons.2 ⟨sub7_67, List.forall_mem_cons.2 ⟨sub7_68, List.forall_mem_cons.2 ⟨sub7_69, List.forall_mem_cons.2 ⟨sub7_70, List.forall_mem_cons.2 ⟨sub7_71, List.forall_mem_cons.2 ⟨sub7_72, List.forall_mem_cons.2 ⟨sub7_73, List.forall_mem_cons.2 ⟨sub7_74, List.forall_mem_cons.2 ⟨sub7_75, List.forall_mem_cons.2 ⟨sub7_76, List.forall_mem_cons.2 ⟨sub7_77, List.forall_mem_cons.2 ⟨sub7_78, List.forall_mem_cons.2 ⟨sub7_79, List.forall_mem_cons.2 ⟨sub7_80, List.forall_mem_cons.2 ⟨sub7_81, List.forall_mem_cons.2 ⟨sub7_82, List.forall_mem_cons.2 ⟨sub7_83, List.forall_mem_cons.2 ⟨sub7_84, List.forall_mem_cons.2 ⟨sub7_85, List.forall_mem_cons.2 ⟨sub7_86, List.forall_mem_cons.2 ⟨sub7_87, List.forall_mem_cons.2 ⟨sub7_88, List.forall_mem_cons.2 ⟨sub7_89, List.forall_mem_cons.2 ⟨sub7_90, List.forall_mem_cons.2 ⟨sub7_91, List.forall_mem_cons.2 ⟨sub7_92, List.forall_mem_cons.2 ⟨sub7_93, List.forall_mem_cons.2 ⟨sub7_94, List.forall_mem_cons.2 ⟨sub7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
