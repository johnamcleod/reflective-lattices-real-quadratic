import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-3] = true := by decide +kernel
theorem sub0_1 : sub0 [-2, -2] = true := by decide +kernel
theorem sub0_2 : sub0 [-2, -1] = true := by decide +kernel
theorem sub0_3 : sub0 [-2, 0] = true := by decide +kernel
theorem sub0_4 : sub0 [-2, 1] = true := by decide +kernel
theorem sub0_5 : sub0 [-2, 2] = true := by decide +kernel
theorem sub0_6 : sub0 [-2, 3] = true := by decide +kernel
theorem sub0_7 : sub0 [-1, -3] = true := by decide +kernel
theorem sub0_8 : sub0 [-1, -2] = true := by decide +kernel
theorem sub0_9 : sub0 [-1, -1, -7] = true := by decide +kernel
theorem sub0_10 : sub0 [-1, -1, -6] = true := by decide +kernel
theorem sub0_11 : sub0 [-1, -1, -5] = true := by decide +kernel
theorem sub0_12 : sub0 [-1, -1, -4] = true := by decide +kernel
theorem sub0_13 : sub0 [-1, -1, -3] = true := by decide +kernel
theorem sub0_14 : sub0 [-1, -1, -2] = true := by decide +kernel
theorem sub0_15 : sub0 [-1, -1, -1] = true := by decide +kernel
theorem sub0_16 : sub0 [-1, -1, 0] = true := by decide +kernel
theorem sub0_17 : sub0 [-1, -1, 1] = true := by decide +kernel
theorem sub0_18 : sub0 [-1, -1, 2] = true := by decide +kernel
theorem sub0_19 : sub0 [-1, -1, 3] = true := by decide +kernel
theorem sub0_20 : sub0 [-1, -1, 4] = true := by decide +kernel
theorem sub0_21 : sub0 [-1, -1, 5] = true := by decide +kernel
theorem sub0_22 : sub0 [-1, -1, 6] = true := by decide +kernel
theorem sub0_23 : sub0 [-1, 0, -7] = true := by decide +kernel
theorem sub0_24 : sub0 [-1, 0, -6] = true := by decide +kernel
theorem sub0_25 : sub0 [-1, 0, -5] = true := by decide +kernel
theorem sub0_26 : sub0 [-1, 0, -4] = true := by decide +kernel
theorem sub0_27 : sub0 [-1, 0, -3] = true := by decide +kernel
theorem sub0_28 : sub0 [-1, 0, -2] = true := by decide +kernel
theorem sub0_29 : sub0 [-1, 0, -1] = true := by decide +kernel
theorem sub0_30 : sub0 [-1, 0, 0] = true := by decide +kernel
theorem sub0_31 : sub0 [-1, 0, 1] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_cons.2 ⟨sub0_12, List.forall_mem_cons.2 ⟨sub0_13, List.forall_mem_cons.2 ⟨sub0_14, List.forall_mem_cons.2 ⟨sub0_15, List.forall_mem_cons.2 ⟨sub0_16, List.forall_mem_cons.2 ⟨sub0_17, List.forall_mem_cons.2 ⟨sub0_18, List.forall_mem_cons.2 ⟨sub0_19, List.forall_mem_cons.2 ⟨sub0_20, List.forall_mem_cons.2 ⟨sub0_21, List.forall_mem_cons.2 ⟨sub0_22, List.forall_mem_cons.2 ⟨sub0_23, List.forall_mem_cons.2 ⟨sub0_24, List.forall_mem_cons.2 ⟨sub0_25, List.forall_mem_cons.2 ⟨sub0_26, List.forall_mem_cons.2 ⟨sub0_27, List.forall_mem_cons.2 ⟨sub0_28, List.forall_mem_cons.2 ⟨sub0_29, List.forall_mem_cons.2 ⟨sub0_30, List.forall_mem_cons.2 ⟨sub0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_32 : sub0 [-1, 0, 2] = true := by decide +kernel
theorem sub0_33 : sub0 [-1, 0, 3] = true := by decide +kernel
theorem sub0_34 : sub0 [-1, 0, 4] = true := by decide +kernel
theorem sub0_35 : sub0 [-1, 0, 5] = true := by decide +kernel
theorem sub0_36 : sub0 [-1, 0, 6] = true := by decide +kernel
theorem sub0_37 : sub0 [-1, 0, 7] = true := by decide +kernel
theorem sub0_38 : sub0 [-1, 1, -6] = true := by decide +kernel
theorem sub0_39 : sub0 [-1, 1, -5] = true := by decide +kernel
theorem sub0_40 : sub0 [-1, 1, -4] = true := by decide +kernel
theorem sub0_41 : sub0 [-1, 1, -3] = true := by decide +kernel
theorem sub0_42 : sub0 [-1, 1, -2] = true := by decide +kernel
theorem sub0_43 : sub0 [-1, 1, -1] = true := by decide +kernel
theorem sub0_44 : sub0 [-1, 1, 0] = true := by decide +kernel
theorem sub0_45 : sub0 [-1, 1, 1] = true := by decide +kernel
theorem sub0_46 : sub0 [-1, 1, 2] = true := by decide +kernel
theorem sub0_47 : sub0 [-1, 1, 3] = true := by decide +kernel
theorem sub0_48 : sub0 [-1, 1, 4] = true := by decide +kernel
theorem sub0_49 : sub0 [-1, 1, 5] = true := by decide +kernel
theorem sub0_50 : sub0 [-1, 1, 6] = true := by decide +kernel
theorem sub0_51 : sub0 [-1, 1, 7] = true := by decide +kernel
theorem sub0_52 : sub0 [-1, 2] = true := by decide +kernel
theorem sub0_53 : sub0 [-1, 3] = true := by decide +kernel
theorem sub0_54 : sub0 [0, -4] = true := by decide +kernel
theorem sub0_55 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_56 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_57 : sub0 [0, -1, -8] = true := by decide +kernel
theorem sub0_58 : sub0 [0, -1, -7] = true := by decide +kernel
theorem sub0_59 : sub0 [0, -1, -6] = true := by decide +kernel
theorem sub0_60 : sub0 [0, -1, -5] = true := by decide +kernel
theorem sub0_61 : sub0 [0, -1, -4] = true := by decide +kernel
theorem sub0_62 : sub0 [0, -1, -3] = true := by decide +kernel
theorem sub0_63 : sub0 [0, -1, -2] = true := by decide +kernel
theorem sb0_1 : ∀ q ∈ blk0_1, sub0 q = true := by
  unfold blk0_1
  exact List.forall_mem_cons.2 ⟨sub0_32, List.forall_mem_cons.2 ⟨sub0_33, List.forall_mem_cons.2 ⟨sub0_34, List.forall_mem_cons.2 ⟨sub0_35, List.forall_mem_cons.2 ⟨sub0_36, List.forall_mem_cons.2 ⟨sub0_37, List.forall_mem_cons.2 ⟨sub0_38, List.forall_mem_cons.2 ⟨sub0_39, List.forall_mem_cons.2 ⟨sub0_40, List.forall_mem_cons.2 ⟨sub0_41, List.forall_mem_cons.2 ⟨sub0_42, List.forall_mem_cons.2 ⟨sub0_43, List.forall_mem_cons.2 ⟨sub0_44, List.forall_mem_cons.2 ⟨sub0_45, List.forall_mem_cons.2 ⟨sub0_46, List.forall_mem_cons.2 ⟨sub0_47, List.forall_mem_cons.2 ⟨sub0_48, List.forall_mem_cons.2 ⟨sub0_49, List.forall_mem_cons.2 ⟨sub0_50, List.forall_mem_cons.2 ⟨sub0_51, List.forall_mem_cons.2 ⟨sub0_52, List.forall_mem_cons.2 ⟨sub0_53, List.forall_mem_cons.2 ⟨sub0_54, List.forall_mem_cons.2 ⟨sub0_55, List.forall_mem_cons.2 ⟨sub0_56, List.forall_mem_cons.2 ⟨sub0_57, List.forall_mem_cons.2 ⟨sub0_58, List.forall_mem_cons.2 ⟨sub0_59, List.forall_mem_cons.2 ⟨sub0_60, List.forall_mem_cons.2 ⟨sub0_61, List.forall_mem_cons.2 ⟨sub0_62, List.forall_mem_cons.2 ⟨sub0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_64 : sub0 [0, -1, -1] = true := by decide +kernel
theorem sub0_65 : sub0 [0, -1, 0] = true := by decide +kernel
theorem sub0_66 : sub0 [0, -1, 1] = true := by decide +kernel
theorem sub0_67 : sub0 [0, -1, 2] = true := by decide +kernel
theorem sub0_68 : sub0 [0, -1, 3] = true := by decide +kernel
theorem sub0_69 : sub0 [0, -1, 4] = true := by decide +kernel
theorem sub0_70 : sub0 [0, -1, 5] = true := by decide +kernel
theorem sub0_71 : sub0 [0, -1, 6] = true := by decide +kernel
theorem sub0_72 : sub0 [0, 0, -8] = true := by decide +kernel
theorem sub0_73 : sub0 [0, 0, -7] = true := by decide +kernel
theorem sub0_74 : sub0 [0, 0, -6] = true := by decide +kernel
theorem sub0_75 : sub0 [0, 0, -5] = true := by decide +kernel
theorem sub0_76 : sub0 [0, 0, -4] = true := by decide +kernel
theorem sub0_77 : sub0 [0, 0, -3] = true := by decide +kernel
theorem sub0_78 : sub0 [0, 0, -2] = true := by decide +kernel
theorem sub0_79 : sub0 [0, 0, -1] = true := by decide +kernel
theorem sub0_80 : sub0 [0, 0, 0] = true := by decide +kernel
theorem sub0_81 : sub0 [0, 0, 1] = true := by decide +kernel
theorem sub0_82 : sub0 [0, 0, 2] = true := by decide +kernel
theorem sub0_83 : sub0 [0, 0, 3] = true := by decide +kernel
theorem sub0_84 : sub0 [0, 0, 4] = true := by decide +kernel
theorem sub0_85 : sub0 [0, 0, 5] = true := by decide +kernel
theorem sub0_86 : sub0 [0, 0, 6] = true := by decide +kernel
theorem sub0_87 : sub0 [0, 0, 7] = true := by decide +kernel
theorem sub0_88 : sub0 [0, 1, -7] = true := by decide +kernel
theorem sub0_89 : sub0 [0, 1, -6] = true := by decide +kernel
theorem sub0_90 : sub0 [0, 1, -5] = true := by decide +kernel
theorem sub0_91 : sub0 [0, 1, -4] = true := by decide +kernel
theorem sub0_92 : sub0 [0, 1, -3] = true := by decide +kernel
theorem sub0_93 : sub0 [0, 1, -2] = true := by decide +kernel
theorem sub0_94 : sub0 [0, 1, -1] = true := by decide +kernel
theorem sub0_95 : sub0 [0, 1, 0] = true := by decide +kernel
theorem sb0_2 : ∀ q ∈ blk0_2, sub0 q = true := by
  unfold blk0_2
  exact List.forall_mem_cons.2 ⟨sub0_64, List.forall_mem_cons.2 ⟨sub0_65, List.forall_mem_cons.2 ⟨sub0_66, List.forall_mem_cons.2 ⟨sub0_67, List.forall_mem_cons.2 ⟨sub0_68, List.forall_mem_cons.2 ⟨sub0_69, List.forall_mem_cons.2 ⟨sub0_70, List.forall_mem_cons.2 ⟨sub0_71, List.forall_mem_cons.2 ⟨sub0_72, List.forall_mem_cons.2 ⟨sub0_73, List.forall_mem_cons.2 ⟨sub0_74, List.forall_mem_cons.2 ⟨sub0_75, List.forall_mem_cons.2 ⟨sub0_76, List.forall_mem_cons.2 ⟨sub0_77, List.forall_mem_cons.2 ⟨sub0_78, List.forall_mem_cons.2 ⟨sub0_79, List.forall_mem_cons.2 ⟨sub0_80, List.forall_mem_cons.2 ⟨sub0_81, List.forall_mem_cons.2 ⟨sub0_82, List.forall_mem_cons.2 ⟨sub0_83, List.forall_mem_cons.2 ⟨sub0_84, List.forall_mem_cons.2 ⟨sub0_85, List.forall_mem_cons.2 ⟨sub0_86, List.forall_mem_cons.2 ⟨sub0_87, List.forall_mem_cons.2 ⟨sub0_88, List.forall_mem_cons.2 ⟨sub0_89, List.forall_mem_cons.2 ⟨sub0_90, List.forall_mem_cons.2 ⟨sub0_91, List.forall_mem_cons.2 ⟨sub0_92, List.forall_mem_cons.2 ⟨sub0_93, List.forall_mem_cons.2 ⟨sub0_94, List.forall_mem_cons.2 ⟨sub0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_96 : sub0 [0, 1, 1] = true := by decide +kernel
theorem sub0_97 : sub0 [0, 1, 2] = true := by decide +kernel
theorem sub0_98 : sub0 [0, 1, 3] = true := by decide +kernel
theorem sub0_99 : sub0 [0, 1, 4] = true := by decide +kernel
theorem sub0_100 : sub0 [0, 1, 5] = true := by decide +kernel
theorem sub0_101 : sub0 [0, 1, 6] = true := by decide +kernel
theorem sub0_102 : sub0 [0, 1, 7] = true := by decide +kernel
theorem sub0_103 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_104 : sub0 [0, 3] = true := by decide +kernel
theorem sub0_105 : sub0 [1, -4] = true := by decide +kernel
theorem sub0_106 : sub0 [1, -3] = true := by decide +kernel
theorem sub0_107 : sub0 [1, -2] = true := by decide +kernel
theorem sub0_108 : sub0 [1, -1, -8] = true := by decide +kernel
theorem sub0_109 : sub0 [1, -1, -7] = true := by decide +kernel
theorem sub0_110 : sub0 [1, -1, -6] = true := by decide +kernel
theorem sub0_111 : sub0 [1, -1, -5] = true := by decide +kernel
theorem sub0_112 : sub0 [1, -1, -4] = true := by decide +kernel
theorem sub0_113 : sub0 [1, -1, -3] = true := by decide +kernel
theorem sub0_114 : sub0 [1, -1, -2] = true := by decide +kernel
theorem sub0_115 : sub0 [1, -1, -1] = true := by decide +kernel
theorem sub0_116 : sub0 [1, -1, 0] = true := by decide +kernel
theorem sub0_117 : sub0 [1, -1, 1] = true := by decide +kernel
theorem sub0_118 : sub0 [1, -1, 2] = true := by decide +kernel
theorem sub0_119 : sub0 [1, -1, 3] = true := by decide +kernel
theorem sub0_120 : sub0 [1, -1, 4] = true := by decide +kernel
theorem sub0_121 : sub0 [1, -1, 5] = true := by decide +kernel
theorem sub0_122 : sub0 [1, 0, -8] = true := by decide +kernel
theorem sub0_123 : sub0 [1, 0, -7] = true := by decide +kernel
theorem sub0_124 : sub0 [1, 0, -6] = true := by decide +kernel
theorem sub0_125 : sub0 [1, 0, -5] = true := by decide +kernel
theorem sub0_126 : sub0 [1, 0, -4] = true := by decide +kernel
theorem sub0_127 : sub0 [1, 0, -3] = true := by decide +kernel
theorem sb0_3 : ∀ q ∈ blk0_3, sub0 q = true := by
  unfold blk0_3
  exact List.forall_mem_cons.2 ⟨sub0_96, List.forall_mem_cons.2 ⟨sub0_97, List.forall_mem_cons.2 ⟨sub0_98, List.forall_mem_cons.2 ⟨sub0_99, List.forall_mem_cons.2 ⟨sub0_100, List.forall_mem_cons.2 ⟨sub0_101, List.forall_mem_cons.2 ⟨sub0_102, List.forall_mem_cons.2 ⟨sub0_103, List.forall_mem_cons.2 ⟨sub0_104, List.forall_mem_cons.2 ⟨sub0_105, List.forall_mem_cons.2 ⟨sub0_106, List.forall_mem_cons.2 ⟨sub0_107, List.forall_mem_cons.2 ⟨sub0_108, List.forall_mem_cons.2 ⟨sub0_109, List.forall_mem_cons.2 ⟨sub0_110, List.forall_mem_cons.2 ⟨sub0_111, List.forall_mem_cons.2 ⟨sub0_112, List.forall_mem_cons.2 ⟨sub0_113, List.forall_mem_cons.2 ⟨sub0_114, List.forall_mem_cons.2 ⟨sub0_115, List.forall_mem_cons.2 ⟨sub0_116, List.forall_mem_cons.2 ⟨sub0_117, List.forall_mem_cons.2 ⟨sub0_118, List.forall_mem_cons.2 ⟨sub0_119, List.forall_mem_cons.2 ⟨sub0_120, List.forall_mem_cons.2 ⟨sub0_121, List.forall_mem_cons.2 ⟨sub0_122, List.forall_mem_cons.2 ⟨sub0_123, List.forall_mem_cons.2 ⟨sub0_124, List.forall_mem_cons.2 ⟨sub0_125, List.forall_mem_cons.2 ⟨sub0_126, List.forall_mem_cons.2 ⟨sub0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_128 : sub0 [1, 0, -2] = true := by decide +kernel
theorem sub0_129 : sub0 [1, 0, -1] = true := by decide +kernel
theorem sub0_130 : sub0 [1, 0, 0] = true := by decide +kernel
theorem sub0_131 : sub0 [1, 0, 1] = true := by decide +kernel
theorem sub0_132 : sub0 [1, 0, 2] = true := by decide +kernel
theorem sub0_133 : sub0 [1, 0, 3] = true := by decide +kernel
theorem sub0_134 : sub0 [1, 0, 4] = true := by decide +kernel
theorem sub0_135 : sub0 [1, 0, 5] = true := by decide +kernel
theorem sub0_136 : sub0 [1, 0, 6] = true := by decide +kernel
theorem sub0_137 : sub0 [1, 1, -7] = true := by decide +kernel
theorem sub0_138 : sub0 [1, 1, -6] = true := by decide +kernel
theorem sub0_139 : sub0 [1, 1, -5] = true := by decide +kernel
theorem sub0_140 : sub0 [1, 1, -4] = true := by decide +kernel
theorem sub0_141 : sub0 [1, 1, -3] = true := by decide +kernel
theorem sub0_142 : sub0 [1, 1, -2] = true := by decide +kernel
theorem sub0_143 : sub0 [1, 1, -1] = true := by decide +kernel
theorem sub0_144 : sub0 [1, 1, 0] = true := by decide +kernel
theorem sub0_145 : sub0 [1, 1, 1] = true := by decide +kernel
theorem sub0_146 : sub0 [1, 1, 2] = true := by decide +kernel
theorem sub0_147 : sub0 [1, 1, 3] = true := by decide +kernel
theorem sub0_148 : sub0 [1, 1, 4] = true := by decide +kernel
theorem sub0_149 : sub0 [1, 1, 5] = true := by decide +kernel
theorem sub0_150 : sub0 [1, 1, 6] = true := by decide +kernel
theorem sub0_151 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_152 : sub0 [2, -4] = true := by decide +kernel
theorem sub0_153 : sub0 [2, -3] = true := by decide +kernel
theorem sub0_154 : sub0 [2, -2] = true := by decide +kernel
theorem sub0_155 : sub0 [2, -1] = true := by decide +kernel
theorem sub0_156 : sub0 [2, 0] = true := by decide +kernel
theorem sub0_157 : sub0 [2, 1] = true := by decide +kernel
theorem sub0_158 : sub0 [3] = true := by decide +kernel
theorem sb0_4 : ∀ q ∈ blk0_4, sub0 q = true := by
  unfold blk0_4
  exact List.forall_mem_cons.2 ⟨sub0_128, List.forall_mem_cons.2 ⟨sub0_129, List.forall_mem_cons.2 ⟨sub0_130, List.forall_mem_cons.2 ⟨sub0_131, List.forall_mem_cons.2 ⟨sub0_132, List.forall_mem_cons.2 ⟨sub0_133, List.forall_mem_cons.2 ⟨sub0_134, List.forall_mem_cons.2 ⟨sub0_135, List.forall_mem_cons.2 ⟨sub0_136, List.forall_mem_cons.2 ⟨sub0_137, List.forall_mem_cons.2 ⟨sub0_138, List.forall_mem_cons.2 ⟨sub0_139, List.forall_mem_cons.2 ⟨sub0_140, List.forall_mem_cons.2 ⟨sub0_141, List.forall_mem_cons.2 ⟨sub0_142, List.forall_mem_cons.2 ⟨sub0_143, List.forall_mem_cons.2 ⟨sub0_144, List.forall_mem_cons.2 ⟨sub0_145, List.forall_mem_cons.2 ⟨sub0_146, List.forall_mem_cons.2 ⟨sub0_147, List.forall_mem_cons.2 ⟨sub0_148, List.forall_mem_cons.2 ⟨sub0_149, List.forall_mem_cons.2 ⟨sub0_150, List.forall_mem_cons.2 ⟨sub0_151, List.forall_mem_cons.2 ⟨sub0_152, List.forall_mem_cons.2 ⟨sub0_153, List.forall_mem_cons.2 ⟨sub0_154, List.forall_mem_cons.2 ⟨sub0_155, List.forall_mem_cons.2 ⟨sub0_156, List.forall_mem_cons.2 ⟨sub0_157, List.forall_mem_cons.2 ⟨sub0_158, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-2, -4] = true := by decide +kernel
theorem sub1_1 : sub1 [-2, -3] = true := by decide +kernel
theorem sub1_2 : sub1 [-2, -2] = true := by decide +kernel
theorem sub1_3 : sub1 [-2, -1] = true := by decide +kernel
theorem sub1_4 : sub1 [-2, 0] = true := by decide +kernel
theorem sub1_5 : sub1 [-2, 1] = true := by decide +kernel
theorem sub1_6 : sub1 [-1, -4] = true := by decide +kernel
theorem sub1_7 : sub1 [-1, -3] = true := by decide +kernel
theorem sub1_8 : sub1 [-1, -2] = true := by decide +kernel
theorem sub1_9 : sub1 [-1, -1] = true := by decide +kernel
theorem sub1_10 : sub1 [-1, 0] = true := by decide +kernel
theorem sub1_11 : sub1 [-1, 1] = true := by decide +kernel
theorem sub1_12 : sub1 [-1, 2] = true := by decide +kernel
theorem sub1_13 : sub1 [0, -4] = true := by decide +kernel
theorem sub1_14 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_15 : sub1 [0, -2] = true := by decide +kernel
theorem sub1_16 : sub1 [0, -1] = true := by decide +kernel
theorem sub1_17 : sub1 [0, 0, -6] = true := by decide +kernel
theorem sub1_18 : sub1 [0, 0, -5] = true := by decide +kernel
theorem sub1_19 : sub1 [0, 0, -4] = true := by decide +kernel
theorem sub1_20 : sub1 [0, 0, -3] = true := by decide +kernel
theorem sub1_21 : sub1 [0, 0, -2] = true := by decide +kernel
theorem sub1_22 : sub1 [0, 0, -1] = true := by decide +kernel
theorem sub1_23 : sub1 [0, 0, 0] = true := by decide +kernel
theorem sub1_24 : sub1 [0, 0, 1] = true := by decide +kernel
theorem sub1_25 : sub1 [0, 0, 2] = true := by decide +kernel
theorem sub1_26 : sub1 [0, 0, 3] = true := by decide +kernel
theorem sub1_27 : sub1 [0, 0, 4] = true := by decide +kernel
theorem sub1_28 : sub1 [0, 0, 5] = true := by decide +kernel
theorem sub1_29 : sub1 [0, 0, 6] = true := by decide +kernel
theorem sub1_30 : sub1 [0, 1] = true := by decide +kernel
theorem sub1_31 : sub1 [0, 2] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_cons.2 ⟨sub1_18, List.forall_mem_cons.2 ⟨sub1_19, List.forall_mem_cons.2 ⟨sub1_20, List.forall_mem_cons.2 ⟨sub1_21, List.forall_mem_cons.2 ⟨sub1_22, List.forall_mem_cons.2 ⟨sub1_23, List.forall_mem_cons.2 ⟨sub1_24, List.forall_mem_cons.2 ⟨sub1_25, List.forall_mem_cons.2 ⟨sub1_26, List.forall_mem_cons.2 ⟨sub1_27, List.forall_mem_cons.2 ⟨sub1_28, List.forall_mem_cons.2 ⟨sub1_29, List.forall_mem_cons.2 ⟨sub1_30, List.forall_mem_cons.2 ⟨sub1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_32 : sub1 [0, 3] = true := by decide +kernel
theorem sub1_33 : sub1 [1, -3] = true := by decide +kernel
theorem sub1_34 : sub1 [1, -2] = true := by decide +kernel
theorem sub1_35 : sub1 [1, -1] = true := by decide +kernel
theorem sub1_36 : sub1 [1, 0] = true := by decide +kernel
theorem sub1_37 : sub1 [1, 1] = true := by decide +kernel
theorem sub1_38 : sub1 [1, 2] = true := by decide +kernel
theorem sub1_39 : sub1 [1, 3] = true := by decide +kernel
theorem sub1_40 : sub1 [2, -2] = true := by decide +kernel
theorem sub1_41 : sub1 [2, -1] = true := by decide +kernel
theorem sub1_42 : sub1 [2, 0] = true := by decide +kernel
theorem sub1_43 : sub1 [2, 1] = true := by decide +kernel
theorem sub1_44 : sub1 [2, 2] = true := by decide +kernel
theorem sub1_45 : sub1 [2, 3] = true := by decide +kernel
theorem sb1_1 : ∀ q ∈ blk1_1, sub1 q = true := by
  unfold blk1_1
  exact List.forall_mem_cons.2 ⟨sub1_32, List.forall_mem_cons.2 ⟨sub1_33, List.forall_mem_cons.2 ⟨sub1_34, List.forall_mem_cons.2 ⟨sub1_35, List.forall_mem_cons.2 ⟨sub1_36, List.forall_mem_cons.2 ⟨sub1_37, List.forall_mem_cons.2 ⟨sub1_38, List.forall_mem_cons.2 ⟨sub1_39, List.forall_mem_cons.2 ⟨sub1_40, List.forall_mem_cons.2 ⟨sub1_41, List.forall_mem_cons.2 ⟨sub1_42, List.forall_mem_cons.2 ⟨sub1_43, List.forall_mem_cons.2 ⟨sub1_44, List.forall_mem_cons.2 ⟨sub1_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
