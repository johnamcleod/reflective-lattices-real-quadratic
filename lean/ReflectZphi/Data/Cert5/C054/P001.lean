import ReflectZphi.Data.Cert5.C054.Base

namespace ReflectZphi.Data.Cert5.C054
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_0 : sub3 [-4, -4] = true := by decide +kernel
theorem sub3_1 : sub3 [-4, -3] = true := by decide +kernel
theorem sub3_2 : sub3 [-4, -2] = true := by decide +kernel
theorem sub3_3 : sub3 [-4, -1] = true := by decide +kernel
theorem sub3_4 : sub3 [-4, 0] = true := by decide +kernel
theorem sub3_5 : sub3 [-4, 1] = true := by decide +kernel
theorem sub3_6 : sub3 [-4, 2] = true := by decide +kernel
theorem sub3_7 : sub3 [-3, -5] = true := by decide +kernel
theorem sub3_8 : sub3 [-3, -4] = true := by decide +kernel
theorem sub3_9 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_10 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_11 : sub3 [-3, -1, -8] = true := by decide +kernel
theorem sub3_12 : sub3 [-3, -1, -7] = true := by decide +kernel
theorem sub3_13 : sub3 [-3, -1, -6] = true := by decide +kernel
theorem sub3_14 : sub3 [-3, -1, -5] = true := by decide +kernel
theorem sub3_15 : sub3 [-3, -1, -4] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, -1, -3] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, -1, -2] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, -1, -1] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, -1, 0] = true := by decide +kernel
theorem sub3_20 : sub3 [-3, -1, 1] = true := by decide +kernel
theorem sub3_21 : sub3 [-3, -1, 2] = true := by decide +kernel
theorem sub3_22 : sub3 [-3, -1, 3] = true := by decide +kernel
theorem sub3_23 : sub3 [-3, -1, 4] = true := by decide +kernel
theorem sub3_24 : sub3 [-3, -1, 5] = true := by decide +kernel
theorem sub3_25 : sub3 [-3, 0, -8] = true := by decide +kernel
theorem sub3_26 : sub3 [-3, 0, -7] = true := by decide +kernel
theorem sub3_27 : sub3 [-3, 0, -6] = true := by decide +kernel
theorem sub3_28 : sub3 [-3, 0, -5] = true := by decide +kernel
theorem sub3_29 : sub3 [-3, 0, -4] = true := by decide +kernel
theorem sub3_30 : sub3 [-3, 0, -3] = true := by decide +kernel
theorem sub3_31 : sub3 [-3, 0, -2] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-3, 0, -1] = true := by decide +kernel
theorem sub3_33 : sub3 [-3, 0, 0] = true := by decide +kernel
theorem sub3_34 : sub3 [-3, 0, 1] = true := by decide +kernel
theorem sub3_35 : sub3 [-3, 0, 2] = true := by decide +kernel
theorem sub3_36 : sub3 [-3, 0, 3] = true := by decide +kernel
theorem sub3_37 : sub3 [-3, 0, 4] = true := by decide +kernel
theorem sub3_38 : sub3 [-3, 0, 5] = true := by decide +kernel
theorem sub3_39 : sub3 [-3, 1, -8] = true := by decide +kernel
theorem sub3_40 : sub3 [-3, 1, -7] = true := by decide +kernel
theorem sub3_41 : sub3 [-3, 1, -6] = true := by decide +kernel
theorem sub3_42 : sub3 [-3, 1, -5] = true := by decide +kernel
theorem sub3_43 : sub3 [-3, 1, -4] = true := by decide +kernel
theorem sub3_44 : sub3 [-3, 1, -3] = true := by decide +kernel
theorem sub3_45 : sub3 [-3, 1, -2] = true := by decide +kernel
theorem sub3_46 : sub3 [-3, 1, -1] = true := by decide +kernel
theorem sub3_47 : sub3 [-3, 1, 0] = true := by decide +kernel
theorem sub3_48 : sub3 [-3, 1, 1] = true := by decide +kernel
theorem sub3_49 : sub3 [-3, 1, 2] = true := by decide +kernel
theorem sub3_50 : sub3 [-3, 1, 3] = true := by decide +kernel
theorem sub3_51 : sub3 [-3, 1, 4] = true := by decide +kernel
theorem sub3_52 : sub3 [-3, 1, 5] = true := by decide +kernel
theorem sub3_53 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_54 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_55 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_56 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_57 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_58 : sub3 [-2, -2, -9] = true := by decide +kernel
theorem sub3_59 : sub3 [-2, -2, -8] = true := by decide +kernel
theorem sub3_60 : sub3 [-2, -2, -7] = true := by decide +kernel
theorem sub3_61 : sub3 [-2, -2, -6] = true := by decide +kernel
theorem sub3_62 : sub3 [-2, -2, -5] = true := by decide +kernel
theorem sub3_63 : sub3 [-2, -2, -4] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [-2, -2, -3] = true := by decide +kernel
theorem sub3_65 : sub3 [-2, -2, -2] = true := by decide +kernel
theorem sub3_66 : sub3 [-2, -2, -1] = true := by decide +kernel
theorem sub3_67 : sub3 [-2, -2, 0] = true := by decide +kernel
theorem sub3_68 : sub3 [-2, -2, 1] = true := by decide +kernel
theorem sub3_69 : sub3 [-2, -2, 2] = true := by decide +kernel
theorem sub3_70 : sub3 [-2, -2, 3] = true := by decide +kernel
theorem sub3_71 : sub3 [-2, -2, 4] = true := by decide +kernel
theorem sub3_72 : sub3 [-2, -2, 5] = true := by decide +kernel
theorem sub3_73 : sub3 [-2, -1, -9] = true := by decide +kernel
theorem sub3_74 : sub3 [-2, -1, -8] = true := by decide +kernel
theorem sub3_75 : sub3 [-2, -1, -7] = true := by decide +kernel
theorem sub3_76 : sub3 [-2, -1, -6] = true := by decide +kernel
theorem sub3_77 : sub3 [-2, -1, -5] = true := by decide +kernel
theorem sub3_78 : sub3 [-2, -1, -4] = true := by decide +kernel
theorem sub3_79 : sub3 [-2, -1, -3] = true := by decide +kernel
theorem sub3_80 : sub3 [-2, -1, -2] = true := by decide +kernel
theorem sub3_81 : sub3 [-2, -1, -1] = true := by decide +kernel
theorem sub3_82 : sub3 [-2, -1, 0] = true := by decide +kernel
theorem sub3_83 : sub3 [-2, -1, 1] = true := by decide +kernel
theorem sub3_84 : sub3 [-2, -1, 2] = true := by decide +kernel
theorem sub3_85 : sub3 [-2, -1, 3] = true := by decide +kernel
theorem sub3_86 : sub3 [-2, -1, 4] = true := by decide +kernel
theorem sub3_87 : sub3 [-2, -1, 5] = true := by decide +kernel
theorem sub3_88 : sub3 [-2, -1, 6] = true := by decide +kernel
theorem sub3_89 : sub3 [-2, 0, -9] = true := by decide +kernel
theorem sub3_90 : sub3 [-2, 0, -8] = true := by decide +kernel
theorem sub3_91 : sub3 [-2, 0, -7] = true := by decide +kernel
theorem sub3_92 : sub3 [-2, 0, -6] = true := by decide +kernel
theorem sub3_93 : sub3 [-2, 0, -5] = true := by decide +kernel
theorem sub3_94 : sub3 [-2, 0, -4] = true := by decide +kernel
theorem sub3_95 : sub3 [-2, 0, -3] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [-2, 0, -2] = true := by decide +kernel
theorem sub3_97 : sub3 [-2, 0, -1] = true := by decide +kernel
theorem sub3_98 : sub3 [-2, 0, 0] = true := by decide +kernel
theorem sub3_99 : sub3 [-2, 0, 1] = true := by decide +kernel
theorem sub3_100 : sub3 [-2, 0, 2] = true := by decide +kernel
theorem sub3_101 : sub3 [-2, 0, 3] = true := by decide +kernel
theorem sub3_102 : sub3 [-2, 0, 4] = true := by decide +kernel
theorem sub3_103 : sub3 [-2, 0, 5] = true := by decide +kernel
theorem sub3_104 : sub3 [-2, 0, 6] = true := by decide +kernel
theorem sub3_105 : sub3 [-2, 0, 7] = true := by decide +kernel
theorem sub3_106 : sub3 [-2, 1, -8] = true := by decide +kernel
theorem sub3_107 : sub3 [-2, 1, -7] = true := by decide +kernel
theorem sub3_108 : sub3 [-2, 1, -6] = true := by decide +kernel
theorem sub3_109 : sub3 [-2, 1, -5] = true := by decide +kernel
theorem sub3_110 : sub3 [-2, 1, -4] = true := by decide +kernel
theorem sub3_111 : sub3 [-2, 1, -3] = true := by decide +kernel
theorem sub3_112 : sub3 [-2, 1, -2] = true := by decide +kernel
theorem sub3_113 : sub3 [-2, 1, -1] = true := by decide +kernel
theorem sub3_114 : sub3 [-2, 1, 0] = true := by decide +kernel
theorem sub3_115 : sub3 [-2, 1, 1] = true := by decide +kernel
theorem sub3_116 : sub3 [-2, 1, 2] = true := by decide +kernel
theorem sub3_117 : sub3 [-2, 1, 3] = true := by decide +kernel
theorem sub3_118 : sub3 [-2, 1, 4] = true := by decide +kernel
theorem sub3_119 : sub3 [-2, 1, 5] = true := by decide +kernel
theorem sub3_120 : sub3 [-2, 1, 6] = true := by decide +kernel
theorem sub3_121 : sub3 [-2, 1, 7] = true := by decide +kernel
theorem sub3_122 : sub3 [-2, 2, -7] = true := by decide +kernel
theorem sub3_123 : sub3 [-2, 2, -6] = true := by decide +kernel
theorem sub3_124 : sub3 [-2, 2, -5] = true := by decide +kernel
theorem sub3_125 : sub3 [-2, 2, -4] = true := by decide +kernel
theorem sub3_126 : sub3 [-2, 2, -3] = true := by decide +kernel
theorem sub3_127 : sub3 [-2, 2, -2] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_128 : sub3 [-2, 2, -1] = true := by decide +kernel
theorem sub3_129 : sub3 [-2, 2, 0] = true := by decide +kernel
theorem sub3_130 : sub3 [-2, 2, 1] = true := by decide +kernel
theorem sub3_131 : sub3 [-2, 2, 2] = true := by decide +kernel
theorem sub3_132 : sub3 [-2, 2, 3] = true := by decide +kernel
theorem sub3_133 : sub3 [-2, 2, 4] = true := by decide +kernel
theorem sub3_134 : sub3 [-2, 2, 5] = true := by decide +kernel
theorem sub3_135 : sub3 [-2, 2, 6] = true := by decide +kernel
theorem sub3_136 : sub3 [-2, 2, 7] = true := by decide +kernel
theorem sub3_137 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_138 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_139 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_140 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_141 : sub3 [-1, -3, -9] = true := by decide +kernel
theorem sub3_142 : sub3 [-1, -3, -8] = true := by decide +kernel
theorem sub3_143 : sub3 [-1, -3, -7] = true := by decide +kernel
theorem sub3_144 : sub3 [-1, -3, -6] = true := by decide +kernel
theorem sub3_145 : sub3 [-1, -3, -5] = true := by decide +kernel
theorem sub3_146 : sub3 [-1, -3, -4] = true := by decide +kernel
theorem sub3_147 : sub3 [-1, -3, -3] = true := by decide +kernel
theorem sub3_148 : sub3 [-1, -3, -2] = true := by decide +kernel
theorem sub3_149 : sub3 [-1, -3, -1] = true := by decide +kernel
theorem sub3_150 : sub3 [-1, -3, 0] = true := by decide +kernel
theorem sub3_151 : sub3 [-1, -3, 1] = true := by decide +kernel
theorem sub3_152 : sub3 [-1, -3, 2] = true := by decide +kernel
theorem sub3_153 : sub3 [-1, -3, 3] = true := by decide +kernel
theorem sub3_154 : sub3 [-1, -3, 4] = true := by decide +kernel
theorem sub3_155 : sub3 [-1, -3, 5] = true := by decide +kernel
theorem sub3_156 : sub3 [-1, -2, -9] = true := by decide +kernel
theorem sub3_157 : sub3 [-1, -2, -8] = true := by decide +kernel
theorem sub3_158 : sub3 [-1, -2, -7] = true := by decide +kernel
theorem sub3_159 : sub3 [-1, -2, -6] = true := by decide +kernel
theorem sb3_4 : ∀ q ∈ blk3_4, sub3 q = true := by
  unfold blk3_4
  exact List.forall_mem_cons.2 ⟨sub3_128, List.forall_mem_cons.2 ⟨sub3_129, List.forall_mem_cons.2 ⟨sub3_130, List.forall_mem_cons.2 ⟨sub3_131, List.forall_mem_cons.2 ⟨sub3_132, List.forall_mem_cons.2 ⟨sub3_133, List.forall_mem_cons.2 ⟨sub3_134, List.forall_mem_cons.2 ⟨sub3_135, List.forall_mem_cons.2 ⟨sub3_136, List.forall_mem_cons.2 ⟨sub3_137, List.forall_mem_cons.2 ⟨sub3_138, List.forall_mem_cons.2 ⟨sub3_139, List.forall_mem_cons.2 ⟨sub3_140, List.forall_mem_cons.2 ⟨sub3_141, List.forall_mem_cons.2 ⟨sub3_142, List.forall_mem_cons.2 ⟨sub3_143, List.forall_mem_cons.2 ⟨sub3_144, List.forall_mem_cons.2 ⟨sub3_145, List.forall_mem_cons.2 ⟨sub3_146, List.forall_mem_cons.2 ⟨sub3_147, List.forall_mem_cons.2 ⟨sub3_148, List.forall_mem_cons.2 ⟨sub3_149, List.forall_mem_cons.2 ⟨sub3_150, List.forall_mem_cons.2 ⟨sub3_151, List.forall_mem_cons.2 ⟨sub3_152, List.forall_mem_cons.2 ⟨sub3_153, List.forall_mem_cons.2 ⟨sub3_154, List.forall_mem_cons.2 ⟨sub3_155, List.forall_mem_cons.2 ⟨sub3_156, List.forall_mem_cons.2 ⟨sub3_157, List.forall_mem_cons.2 ⟨sub3_158, List.forall_mem_cons.2 ⟨sub3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_160 : sub3 [-1, -2, -5] = true := by decide +kernel
theorem sub3_161 : sub3 [-1, -2, -4] = true := by decide +kernel
theorem sub3_162 : sub3 [-1, -2, -3] = true := by decide +kernel
theorem sub3_163 : sub3 [-1, -2, -2] = true := by decide +kernel
theorem sub3_164 : sub3 [-1, -2, -1] = true := by decide +kernel
theorem sub3_165 : sub3 [-1, -2, 0] = true := by decide +kernel
theorem sub3_166 : sub3 [-1, -2, 1] = true := by decide +kernel
theorem sub3_167 : sub3 [-1, -2, 2] = true := by decide +kernel
theorem sub3_168 : sub3 [-1, -2, 3] = true := by decide +kernel
theorem sub3_169 : sub3 [-1, -2, 4] = true := by decide +kernel
theorem sub3_170 : sub3 [-1, -2, 5] = true := by decide +kernel
theorem sub3_171 : sub3 [-1, -2, 6] = true := by decide +kernel
theorem sub3_172 : sub3 [-1, -1, -9] = true := by decide +kernel
theorem sub3_173 : sub3 [-1, -1, -8] = true := by decide +kernel
theorem sub3_174 : sub3 [-1, -1, -7] = true := by decide +kernel
theorem sub3_175 : sub3 [-1, -1, -6] = true := by decide +kernel
theorem sub3_176 : sub3 [-1, -1, -5] = true := by decide +kernel
theorem sub3_177 : sub3 [-1, -1, -4] = true := by decide +kernel
theorem sub3_178 : sub3 [-1, -1, -3] = true := by decide +kernel
theorem sub3_179 : sub3 [-1, -1, -2] = true := by decide +kernel
theorem sub3_180 : sub3 [-1, -1, -1] = true := by decide +kernel
theorem sub3_181 : sub3 [-1, -1, 0] = true := by decide +kernel
theorem sub3_182 : sub3 [-1, -1, 1] = true := by decide +kernel
theorem sub3_183 : sub3 [-1, -1, 2] = true := by decide +kernel
theorem sub3_184 : sub3 [-1, -1, 3] = true := by decide +kernel
theorem sub3_185 : sub3 [-1, -1, 4] = true := by decide +kernel
theorem sub3_186 : sub3 [-1, -1, 5] = true := by decide +kernel
theorem sub3_187 : sub3 [-1, -1, 6] = true := by decide +kernel
theorem sub3_188 : sub3 [-1, -1, 7] = true := by decide +kernel
theorem sub3_189 : sub3 [-1, 0, -9] = true := by decide +kernel
theorem sub3_190 : sub3 [-1, 0, -8] = true := by decide +kernel
theorem sub3_191 : sub3 [-1, 0, -7] = true := by decide +kernel
theorem sb3_5 : ∀ q ∈ blk3_5, sub3 q = true := by
  unfold blk3_5
  exact List.forall_mem_cons.2 ⟨sub3_160, List.forall_mem_cons.2 ⟨sub3_161, List.forall_mem_cons.2 ⟨sub3_162, List.forall_mem_cons.2 ⟨sub3_163, List.forall_mem_cons.2 ⟨sub3_164, List.forall_mem_cons.2 ⟨sub3_165, List.forall_mem_cons.2 ⟨sub3_166, List.forall_mem_cons.2 ⟨sub3_167, List.forall_mem_cons.2 ⟨sub3_168, List.forall_mem_cons.2 ⟨sub3_169, List.forall_mem_cons.2 ⟨sub3_170, List.forall_mem_cons.2 ⟨sub3_171, List.forall_mem_cons.2 ⟨sub3_172, List.forall_mem_cons.2 ⟨sub3_173, List.forall_mem_cons.2 ⟨sub3_174, List.forall_mem_cons.2 ⟨sub3_175, List.forall_mem_cons.2 ⟨sub3_176, List.forall_mem_cons.2 ⟨sub3_177, List.forall_mem_cons.2 ⟨sub3_178, List.forall_mem_cons.2 ⟨sub3_179, List.forall_mem_cons.2 ⟨sub3_180, List.forall_mem_cons.2 ⟨sub3_181, List.forall_mem_cons.2 ⟨sub3_182, List.forall_mem_cons.2 ⟨sub3_183, List.forall_mem_cons.2 ⟨sub3_184, List.forall_mem_cons.2 ⟨sub3_185, List.forall_mem_cons.2 ⟨sub3_186, List.forall_mem_cons.2 ⟨sub3_187, List.forall_mem_cons.2 ⟨sub3_188, List.forall_mem_cons.2 ⟨sub3_189, List.forall_mem_cons.2 ⟨sub3_190, List.forall_mem_cons.2 ⟨sub3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_192 : sub3 [-1, 0, -6] = true := by decide +kernel
theorem sub3_193 : sub3 [-1, 0, -5] = true := by decide +kernel
theorem sub3_194 : sub3 [-1, 0, -4] = true := by decide +kernel
theorem sub3_195 : sub3 [-1, 0, -3] = true := by decide +kernel
theorem sub3_196 : sub3 [-1, 0, -2] = true := by decide +kernel
theorem sub3_197 : sub3 [-1, 0, -1] = true := by decide +kernel
theorem sub3_198 : sub3 [-1, 0, 0] = true := by decide +kernel
theorem sub3_199 : sub3 [-1, 0, 1] = true := by decide +kernel
theorem sub3_200 : sub3 [-1, 0, 2] = true := by decide +kernel
theorem sub3_201 : sub3 [-1, 0, 3] = true := by decide +kernel
theorem sub3_202 : sub3 [-1, 0, 4] = true := by decide +kernel
theorem sub3_203 : sub3 [-1, 0, 5] = true := by decide +kernel
theorem sub3_204 : sub3 [-1, 0, 6] = true := by decide +kernel
theorem sub3_205 : sub3 [-1, 0, 7] = true := by decide +kernel
theorem sub3_206 : sub3 [-1, 1, -9] = true := by decide +kernel
theorem sub3_207 : sub3 [-1, 1, -8] = true := by decide +kernel
theorem sub3_208 : sub3 [-1, 1, -7] = true := by decide +kernel
theorem sub3_209 : sub3 [-1, 1, -6] = true := by decide +kernel
theorem sub3_210 : sub3 [-1, 1, -5] = true := by decide +kernel
theorem sub3_211 : sub3 [-1, 1, -4] = true := by decide +kernel
theorem sub3_212 : sub3 [-1, 1, -3] = true := by decide +kernel
theorem sub3_213 : sub3 [-1, 1, -2] = true := by decide +kernel
theorem sub3_214 : sub3 [-1, 1, -1] = true := by decide +kernel
theorem sub3_215 : sub3 [-1, 1, 0] = true := by decide +kernel
theorem sub3_216 : sub3 [-1, 1, 1] = true := by decide +kernel
theorem sub3_217 : sub3 [-1, 1, 2] = true := by decide +kernel
theorem sub3_218 : sub3 [-1, 1, 3] = true := by decide +kernel
theorem sub3_219 : sub3 [-1, 1, 4] = true := by decide +kernel
theorem sub3_220 : sub3 [-1, 1, 5] = true := by decide +kernel
theorem sub3_221 : sub3 [-1, 1, 6] = true := by decide +kernel
theorem sub3_222 : sub3 [-1, 1, 7] = true := by decide +kernel
theorem sub3_223 : sub3 [-1, 1, 8] = true := by decide +kernel
theorem sb3_6 : ∀ q ∈ blk3_6, sub3 q = true := by
  unfold blk3_6
  exact List.forall_mem_cons.2 ⟨sub3_192, List.forall_mem_cons.2 ⟨sub3_193, List.forall_mem_cons.2 ⟨sub3_194, List.forall_mem_cons.2 ⟨sub3_195, List.forall_mem_cons.2 ⟨sub3_196, List.forall_mem_cons.2 ⟨sub3_197, List.forall_mem_cons.2 ⟨sub3_198, List.forall_mem_cons.2 ⟨sub3_199, List.forall_mem_cons.2 ⟨sub3_200, List.forall_mem_cons.2 ⟨sub3_201, List.forall_mem_cons.2 ⟨sub3_202, List.forall_mem_cons.2 ⟨sub3_203, List.forall_mem_cons.2 ⟨sub3_204, List.forall_mem_cons.2 ⟨sub3_205, List.forall_mem_cons.2 ⟨sub3_206, List.forall_mem_cons.2 ⟨sub3_207, List.forall_mem_cons.2 ⟨sub3_208, List.forall_mem_cons.2 ⟨sub3_209, List.forall_mem_cons.2 ⟨sub3_210, List.forall_mem_cons.2 ⟨sub3_211, List.forall_mem_cons.2 ⟨sub3_212, List.forall_mem_cons.2 ⟨sub3_213, List.forall_mem_cons.2 ⟨sub3_214, List.forall_mem_cons.2 ⟨sub3_215, List.forall_mem_cons.2 ⟨sub3_216, List.forall_mem_cons.2 ⟨sub3_217, List.forall_mem_cons.2 ⟨sub3_218, List.forall_mem_cons.2 ⟨sub3_219, List.forall_mem_cons.2 ⟨sub3_220, List.forall_mem_cons.2 ⟨sub3_221, List.forall_mem_cons.2 ⟨sub3_222, List.forall_mem_cons.2 ⟨sub3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_224 : sub3 [-1, 2, -8] = true := by decide +kernel
theorem sub3_225 : sub3 [-1, 2, -7] = true := by decide +kernel
theorem sub3_226 : sub3 [-1, 2, -6] = true := by decide +kernel
theorem sub3_227 : sub3 [-1, 2, -5] = true := by decide +kernel
theorem sub3_228 : sub3 [-1, 2, -4] = true := by decide +kernel
theorem sub3_229 : sub3 [-1, 2, -3] = true := by decide +kernel
theorem sub3_230 : sub3 [-1, 2, -2] = true := by decide +kernel
theorem sub3_231 : sub3 [-1, 2, -1] = true := by decide +kernel
theorem sub3_232 : sub3 [-1, 2, 0] = true := by decide +kernel
theorem sub3_233 : sub3 [-1, 2, 1] = true := by decide +kernel
theorem sub3_234 : sub3 [-1, 2, 2] = true := by decide +kernel
theorem sub3_235 : sub3 [-1, 2, 3] = true := by decide +kernel
theorem sub3_236 : sub3 [-1, 2, 4] = true := by decide +kernel
theorem sub3_237 : sub3 [-1, 2, 5] = true := by decide +kernel
theorem sub3_238 : sub3 [-1, 2, 6] = true := by decide +kernel
theorem sub3_239 : sub3 [-1, 2, 7] = true := by decide +kernel
theorem sub3_240 : sub3 [-1, 2, 8] = true := by decide +kernel
theorem sub3_241 : sub3 [-1, 3, -6] = true := by decide +kernel
theorem sub3_242 : sub3 [-1, 3, -5] = true := by decide +kernel
theorem sub3_243 : sub3 [-1, 3, -4] = true := by decide +kernel
theorem sub3_244 : sub3 [-1, 3, -3] = true := by decide +kernel
theorem sub3_245 : sub3 [-1, 3, -2] = true := by decide +kernel
theorem sub3_246 : sub3 [-1, 3, -1] = true := by decide +kernel
theorem sub3_247 : sub3 [-1, 3, 0] = true := by decide +kernel
theorem sub3_248 : sub3 [-1, 3, 1] = true := by decide +kernel
theorem sub3_249 : sub3 [-1, 3, 2] = true := by decide +kernel
theorem sub3_250 : sub3 [-1, 3, 3] = true := by decide +kernel
theorem sub3_251 : sub3 [-1, 3, 4] = true := by decide +kernel
theorem sub3_252 : sub3 [-1, 3, 5] = true := by decide +kernel
theorem sub3_253 : sub3 [-1, 3, 6] = true := by decide +kernel
theorem sub3_254 : sub3 [-1, 3, 7] = true := by decide +kernel
theorem sub3_255 : sub3 [-1, 4] = true := by decide +kernel
theorem sb3_7 : ∀ q ∈ blk3_7, sub3 q = true := by
  unfold blk3_7
  exact List.forall_mem_cons.2 ⟨sub3_224, List.forall_mem_cons.2 ⟨sub3_225, List.forall_mem_cons.2 ⟨sub3_226, List.forall_mem_cons.2 ⟨sub3_227, List.forall_mem_cons.2 ⟨sub3_228, List.forall_mem_cons.2 ⟨sub3_229, List.forall_mem_cons.2 ⟨sub3_230, List.forall_mem_cons.2 ⟨sub3_231, List.forall_mem_cons.2 ⟨sub3_232, List.forall_mem_cons.2 ⟨sub3_233, List.forall_mem_cons.2 ⟨sub3_234, List.forall_mem_cons.2 ⟨sub3_235, List.forall_mem_cons.2 ⟨sub3_236, List.forall_mem_cons.2 ⟨sub3_237, List.forall_mem_cons.2 ⟨sub3_238, List.forall_mem_cons.2 ⟨sub3_239, List.forall_mem_cons.2 ⟨sub3_240, List.forall_mem_cons.2 ⟨sub3_241, List.forall_mem_cons.2 ⟨sub3_242, List.forall_mem_cons.2 ⟨sub3_243, List.forall_mem_cons.2 ⟨sub3_244, List.forall_mem_cons.2 ⟨sub3_245, List.forall_mem_cons.2 ⟨sub3_246, List.forall_mem_cons.2 ⟨sub3_247, List.forall_mem_cons.2 ⟨sub3_248, List.forall_mem_cons.2 ⟨sub3_249, List.forall_mem_cons.2 ⟨sub3_250, List.forall_mem_cons.2 ⟨sub3_251, List.forall_mem_cons.2 ⟨sub3_252, List.forall_mem_cons.2 ⟨sub3_253, List.forall_mem_cons.2 ⟨sub3_254, List.forall_mem_cons.2 ⟨sub3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_256 : sub3 [0, -6] = true := by decide +kernel
theorem sub3_257 : sub3 [0, -5] = true := by decide +kernel
theorem sub3_258 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_259 : sub3 [0, -3, -8] = true := by decide +kernel
theorem sub3_260 : sub3 [0, -3, -7] = true := by decide +kernel
theorem sub3_261 : sub3 [0, -3, -6] = true := by decide +kernel
theorem sub3_262 : sub3 [0, -3, -5] = true := by decide +kernel
theorem sub3_263 : sub3 [0, -3, -4] = true := by decide +kernel
theorem sub3_264 : sub3 [0, -3, -3] = true := by decide +kernel
theorem sub3_265 : sub3 [0, -3, -2] = true := by decide +kernel
theorem sub3_266 : sub3 [0, -3, -1] = true := by decide +kernel
theorem sub3_267 : sub3 [0, -3, 0] = true := by decide +kernel
theorem sub3_268 : sub3 [0, -3, 1] = true := by decide +kernel
theorem sub3_269 : sub3 [0, -3, 2] = true := by decide +kernel
theorem sub3_270 : sub3 [0, -3, 3] = true := by decide +kernel
theorem sub3_271 : sub3 [0, -3, 4] = true := by decide +kernel
theorem sub3_272 : sub3 [0, -3, 5] = true := by decide +kernel
theorem sub3_273 : sub3 [0, -2, -9] = true := by decide +kernel
theorem sub3_274 : sub3 [0, -2, -8] = true := by decide +kernel
theorem sub3_275 : sub3 [0, -2, -7] = true := by decide +kernel
theorem sub3_276 : sub3 [0, -2, -6] = true := by decide +kernel
theorem sub3_277 : sub3 [0, -2, -5] = true := by decide +kernel
theorem sub3_278 : sub3 [0, -2, -4] = true := by decide +kernel
theorem sub3_279 : sub3 [0, -2, -3] = true := by decide +kernel
theorem sub3_280 : sub3 [0, -2, -2] = true := by decide +kernel
theorem sub3_281 : sub3 [0, -2, -1] = true := by decide +kernel
theorem sub3_282 : sub3 [0, -2, 0] = true := by decide +kernel
theorem sub3_283 : sub3 [0, -2, 1] = true := by decide +kernel
theorem sub3_284 : sub3 [0, -2, 2] = true := by decide +kernel
theorem sub3_285 : sub3 [0, -2, 3] = true := by decide +kernel
theorem sub3_286 : sub3 [0, -2, 4] = true := by decide +kernel
theorem sub3_287 : sub3 [0, -2, 5] = true := by decide +kernel
theorem sb3_8 : ∀ q ∈ blk3_8, sub3 q = true := by
  unfold blk3_8
  exact List.forall_mem_cons.2 ⟨sub3_256, List.forall_mem_cons.2 ⟨sub3_257, List.forall_mem_cons.2 ⟨sub3_258, List.forall_mem_cons.2 ⟨sub3_259, List.forall_mem_cons.2 ⟨sub3_260, List.forall_mem_cons.2 ⟨sub3_261, List.forall_mem_cons.2 ⟨sub3_262, List.forall_mem_cons.2 ⟨sub3_263, List.forall_mem_cons.2 ⟨sub3_264, List.forall_mem_cons.2 ⟨sub3_265, List.forall_mem_cons.2 ⟨sub3_266, List.forall_mem_cons.2 ⟨sub3_267, List.forall_mem_cons.2 ⟨sub3_268, List.forall_mem_cons.2 ⟨sub3_269, List.forall_mem_cons.2 ⟨sub3_270, List.forall_mem_cons.2 ⟨sub3_271, List.forall_mem_cons.2 ⟨sub3_272, List.forall_mem_cons.2 ⟨sub3_273, List.forall_mem_cons.2 ⟨sub3_274, List.forall_mem_cons.2 ⟨sub3_275, List.forall_mem_cons.2 ⟨sub3_276, List.forall_mem_cons.2 ⟨sub3_277, List.forall_mem_cons.2 ⟨sub3_278, List.forall_mem_cons.2 ⟨sub3_279, List.forall_mem_cons.2 ⟨sub3_280, List.forall_mem_cons.2 ⟨sub3_281, List.forall_mem_cons.2 ⟨sub3_282, List.forall_mem_cons.2 ⟨sub3_283, List.forall_mem_cons.2 ⟨sub3_284, List.forall_mem_cons.2 ⟨sub3_285, List.forall_mem_cons.2 ⟨sub3_286, List.forall_mem_cons.2 ⟨sub3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_288 : sub3 [0, -2, 6] = true := by decide +kernel
theorem sub3_289 : sub3 [0, -1, -9] = true := by decide +kernel
theorem sub3_290 : sub3 [0, -1, -8] = true := by decide +kernel
theorem sub3_291 : sub3 [0, -1, -7] = true := by decide +kernel
theorem sub3_292 : sub3 [0, -1, -6] = true := by decide +kernel
theorem sub3_293 : sub3 [0, -1, -5] = true := by decide +kernel
theorem sub3_294 : sub3 [0, -1, -4] = true := by decide +kernel
theorem sub3_295 : sub3 [0, -1, -3] = true := by decide +kernel
theorem sub3_296 : sub3 [0, -1, -2] = true := by decide +kernel
theorem sub3_297 : sub3 [0, -1, -1] = true := by decide +kernel
theorem sub3_298 : sub3 [0, -1, 0] = true := by decide +kernel
theorem sub3_299 : sub3 [0, -1, 1] = true := by decide +kernel
theorem sub3_300 : sub3 [0, -1, 2] = true := by decide +kernel
theorem sub3_301 : sub3 [0, -1, 3] = true := by decide +kernel
theorem sub3_302 : sub3 [0, -1, 4] = true := by decide +kernel
theorem sub3_303 : sub3 [0, -1, 5] = true := by decide +kernel
theorem sub3_304 : sub3 [0, -1, 6] = true := by decide +kernel
theorem sub3_305 : sub3 [0, -1, 7] = true := by decide +kernel
theorem sub3_306 : sub3 [0, 0, -9] = true := by decide +kernel
theorem sub3_307 : sub3 [0, 0, -8] = true := by decide +kernel
theorem sub3_308 : sub3 [0, 0, -7] = true := by decide +kernel
theorem sub3_309 : sub3 [0, 0, -6] = true := by decide +kernel
theorem sub3_310 : sub3 [0, 0, -5] = true := by decide +kernel
theorem sub3_311 : sub3 [0, 0, -4] = true := by decide +kernel
theorem sub3_312 : sub3 [0, 0, -3] = true := by decide +kernel
theorem sub3_313 : sub3 [0, 0, -2] = true := by decide +kernel
theorem sub3_314 : sub3 [0, 0, -1] = true := by decide +kernel
theorem sub3_315 : sub3 [0, 0, 0] = true := by decide +kernel
theorem sub3_316 : sub3 [0, 0, 1] = true := by decide +kernel
theorem sub3_317 : sub3 [0, 0, 2] = true := by decide +kernel
theorem sub3_318 : sub3 [0, 0, 3] = true := by decide +kernel
theorem sub3_319 : sub3 [0, 0, 4] = true := by decide +kernel
theorem sb3_9 : ∀ q ∈ blk3_9, sub3 q = true := by
  unfold blk3_9
  exact List.forall_mem_cons.2 ⟨sub3_288, List.forall_mem_cons.2 ⟨sub3_289, List.forall_mem_cons.2 ⟨sub3_290, List.forall_mem_cons.2 ⟨sub3_291, List.forall_mem_cons.2 ⟨sub3_292, List.forall_mem_cons.2 ⟨sub3_293, List.forall_mem_cons.2 ⟨sub3_294, List.forall_mem_cons.2 ⟨sub3_295, List.forall_mem_cons.2 ⟨sub3_296, List.forall_mem_cons.2 ⟨sub3_297, List.forall_mem_cons.2 ⟨sub3_298, List.forall_mem_cons.2 ⟨sub3_299, List.forall_mem_cons.2 ⟨sub3_300, List.forall_mem_cons.2 ⟨sub3_301, List.forall_mem_cons.2 ⟨sub3_302, List.forall_mem_cons.2 ⟨sub3_303, List.forall_mem_cons.2 ⟨sub3_304, List.forall_mem_cons.2 ⟨sub3_305, List.forall_mem_cons.2 ⟨sub3_306, List.forall_mem_cons.2 ⟨sub3_307, List.forall_mem_cons.2 ⟨sub3_308, List.forall_mem_cons.2 ⟨sub3_309, List.forall_mem_cons.2 ⟨sub3_310, List.forall_mem_cons.2 ⟨sub3_311, List.forall_mem_cons.2 ⟨sub3_312, List.forall_mem_cons.2 ⟨sub3_313, List.forall_mem_cons.2 ⟨sub3_314, List.forall_mem_cons.2 ⟨sub3_315, List.forall_mem_cons.2 ⟨sub3_316, List.forall_mem_cons.2 ⟨sub3_317, List.forall_mem_cons.2 ⟨sub3_318, List.forall_mem_cons.2 ⟨sub3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_320 : sub3 [0, 0, 5] = true := by decide +kernel
theorem sub3_321 : sub3 [0, 0, 6] = true := by decide +kernel
theorem sub3_322 : sub3 [0, 0, 7] = true := by decide +kernel
theorem sub3_323 : sub3 [0, 0, 8] = true := by decide +kernel
theorem sub3_324 : sub3 [0, 1, -8] = true := by decide +kernel
theorem sub3_325 : sub3 [0, 1, -7] = true := by decide +kernel
theorem sub3_326 : sub3 [0, 1, -6] = true := by decide +kernel
theorem sub3_327 : sub3 [0, 1, -5] = true := by decide +kernel
theorem sub3_328 : sub3 [0, 1, -4] = true := by decide +kernel
theorem sub3_329 : sub3 [0, 1, -3] = true := by decide +kernel
theorem sub3_330 : sub3 [0, 1, -2] = true := by decide +kernel
theorem sub3_331 : sub3 [0, 1, -1] = true := by decide +kernel
theorem sub3_332 : sub3 [0, 1, 0] = true := by decide +kernel
theorem sub3_333 : sub3 [0, 1, 1] = true := by decide +kernel
theorem sub3_334 : sub3 [0, 1, 2] = true := by decide +kernel
theorem sub3_335 : sub3 [0, 1, 3] = true := by decide +kernel
theorem sub3_336 : sub3 [0, 1, 4] = true := by decide +kernel
theorem sub3_337 : sub3 [0, 1, 5] = true := by decide +kernel
theorem sub3_338 : sub3 [0, 1, 6] = true := by decide +kernel
theorem sub3_339 : sub3 [0, 1, 7] = true := by decide +kernel
theorem sub3_340 : sub3 [0, 1, 8] = true := by decide +kernel
theorem sub3_341 : sub3 [0, 2, -7] = true := by decide +kernel
theorem sub3_342 : sub3 [0, 2, -6] = true := by decide +kernel
theorem sub3_343 : sub3 [0, 2, -5] = true := by decide +kernel
theorem sub3_344 : sub3 [0, 2, -4] = true := by decide +kernel
theorem sub3_345 : sub3 [0, 2, -3] = true := by decide +kernel
theorem sub3_346 : sub3 [0, 2, -2] = true := by decide +kernel
theorem sub3_347 : sub3 [0, 2, -1] = true := by decide +kernel
theorem sub3_348 : sub3 [0, 2, 0] = true := by decide +kernel
theorem sub3_349 : sub3 [0, 2, 1] = true := by decide +kernel
theorem sub3_350 : sub3 [0, 2, 2] = true := by decide +kernel
theorem sub3_351 : sub3 [0, 2, 3] = true := by decide +kernel
theorem sb3_10 : ∀ q ∈ blk3_10, sub3 q = true := by
  unfold blk3_10
  exact List.forall_mem_cons.2 ⟨sub3_320, List.forall_mem_cons.2 ⟨sub3_321, List.forall_mem_cons.2 ⟨sub3_322, List.forall_mem_cons.2 ⟨sub3_323, List.forall_mem_cons.2 ⟨sub3_324, List.forall_mem_cons.2 ⟨sub3_325, List.forall_mem_cons.2 ⟨sub3_326, List.forall_mem_cons.2 ⟨sub3_327, List.forall_mem_cons.2 ⟨sub3_328, List.forall_mem_cons.2 ⟨sub3_329, List.forall_mem_cons.2 ⟨sub3_330, List.forall_mem_cons.2 ⟨sub3_331, List.forall_mem_cons.2 ⟨sub3_332, List.forall_mem_cons.2 ⟨sub3_333, List.forall_mem_cons.2 ⟨sub3_334, List.forall_mem_cons.2 ⟨sub3_335, List.forall_mem_cons.2 ⟨sub3_336, List.forall_mem_cons.2 ⟨sub3_337, List.forall_mem_cons.2 ⟨sub3_338, List.forall_mem_cons.2 ⟨sub3_339, List.forall_mem_cons.2 ⟨sub3_340, List.forall_mem_cons.2 ⟨sub3_341, List.forall_mem_cons.2 ⟨sub3_342, List.forall_mem_cons.2 ⟨sub3_343, List.forall_mem_cons.2 ⟨sub3_344, List.forall_mem_cons.2 ⟨sub3_345, List.forall_mem_cons.2 ⟨sub3_346, List.forall_mem_cons.2 ⟨sub3_347, List.forall_mem_cons.2 ⟨sub3_348, List.forall_mem_cons.2 ⟨sub3_349, List.forall_mem_cons.2 ⟨sub3_350, List.forall_mem_cons.2 ⟨sub3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_352 : sub3 [0, 2, 4] = true := by decide +kernel
theorem sub3_353 : sub3 [0, 2, 5] = true := by decide +kernel
theorem sub3_354 : sub3 [0, 2, 6] = true := by decide +kernel
theorem sub3_355 : sub3 [0, 2, 7] = true := by decide +kernel
theorem sub3_356 : sub3 [0, 2, 8] = true := by decide +kernel
theorem sub3_357 : sub3 [0, 3, -6] = true := by decide +kernel
theorem sub3_358 : sub3 [0, 3, -5] = true := by decide +kernel
theorem sub3_359 : sub3 [0, 3, -4] = true := by decide +kernel
theorem sub3_360 : sub3 [0, 3, -3] = true := by decide +kernel
theorem sub3_361 : sub3 [0, 3, -2] = true := by decide +kernel
theorem sub3_362 : sub3 [0, 3, -1] = true := by decide +kernel
theorem sub3_363 : sub3 [0, 3, 0] = true := by decide +kernel
theorem sub3_364 : sub3 [0, 3, 1] = true := by decide +kernel
theorem sub3_365 : sub3 [0, 3, 2] = true := by decide +kernel
theorem sub3_366 : sub3 [0, 3, 3] = true := by decide +kernel
theorem sub3_367 : sub3 [0, 3, 4] = true := by decide +kernel
theorem sub3_368 : sub3 [0, 3, 5] = true := by decide +kernel
theorem sub3_369 : sub3 [0, 3, 6] = true := by decide +kernel
theorem sub3_370 : sub3 [0, 3, 7] = true := by decide +kernel
theorem sub3_371 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_372 : sub3 [0, 5] = true := by decide +kernel
theorem sub3_373 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_374 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_375 : sub3 [1, -3, -8] = true := by decide +kernel
theorem sub3_376 : sub3 [1, -3, -7] = true := by decide +kernel
theorem sub3_377 : sub3 [1, -3, -6] = true := by decide +kernel
theorem sub3_378 : sub3 [1, -3, -5] = true := by decide +kernel
theorem sub3_379 : sub3 [1, -3, -4] = true := by decide +kernel
theorem sub3_380 : sub3 [1, -3, -3] = true := by decide +kernel
theorem sub3_381 : sub3 [1, -3, -2] = true := by decide +kernel
theorem sub3_382 : sub3 [1, -3, -1] = true := by decide +kernel
theorem sub3_383 : sub3 [1, -3, 0] = true := by decide +kernel
theorem sb3_11 : ∀ q ∈ blk3_11, sub3 q = true := by
  unfold blk3_11
  exact List.forall_mem_cons.2 ⟨sub3_352, List.forall_mem_cons.2 ⟨sub3_353, List.forall_mem_cons.2 ⟨sub3_354, List.forall_mem_cons.2 ⟨sub3_355, List.forall_mem_cons.2 ⟨sub3_356, List.forall_mem_cons.2 ⟨sub3_357, List.forall_mem_cons.2 ⟨sub3_358, List.forall_mem_cons.2 ⟨sub3_359, List.forall_mem_cons.2 ⟨sub3_360, List.forall_mem_cons.2 ⟨sub3_361, List.forall_mem_cons.2 ⟨sub3_362, List.forall_mem_cons.2 ⟨sub3_363, List.forall_mem_cons.2 ⟨sub3_364, List.forall_mem_cons.2 ⟨sub3_365, List.forall_mem_cons.2 ⟨sub3_366, List.forall_mem_cons.2 ⟨sub3_367, List.forall_mem_cons.2 ⟨sub3_368, List.forall_mem_cons.2 ⟨sub3_369, List.forall_mem_cons.2 ⟨sub3_370, List.forall_mem_cons.2 ⟨sub3_371, List.forall_mem_cons.2 ⟨sub3_372, List.forall_mem_cons.2 ⟨sub3_373, List.forall_mem_cons.2 ⟨sub3_374, List.forall_mem_cons.2 ⟨sub3_375, List.forall_mem_cons.2 ⟨sub3_376, List.forall_mem_cons.2 ⟨sub3_377, List.forall_mem_cons.2 ⟨sub3_378, List.forall_mem_cons.2 ⟨sub3_379, List.forall_mem_cons.2 ⟨sub3_380, List.forall_mem_cons.2 ⟨sub3_381, List.forall_mem_cons.2 ⟨sub3_382, List.forall_mem_cons.2 ⟨sub3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_384 : sub3 [1, -3, 1] = true := by decide +kernel
theorem sub3_385 : sub3 [1, -3, 2] = true := by decide +kernel
theorem sub3_386 : sub3 [1, -3, 3] = true := by decide +kernel
theorem sub3_387 : sub3 [1, -3, 4] = true := by decide +kernel
theorem sub3_388 : sub3 [1, -3, 5] = true := by decide +kernel
theorem sub3_389 : sub3 [1, -2, -9] = true := by decide +kernel
theorem sub3_390 : sub3 [1, -2, -8] = true := by decide +kernel
theorem sub3_391 : sub3 [1, -2, -7] = true := by decide +kernel
theorem sub3_392 : sub3 [1, -2, -6] = true := by decide +kernel
theorem sub3_393 : sub3 [1, -2, -5] = true := by decide +kernel
theorem sub3_394 : sub3 [1, -2, -4] = true := by decide +kernel
theorem sub3_395 : sub3 [1, -2, -3] = true := by decide +kernel
theorem sub3_396 : sub3 [1, -2, -2] = true := by decide +kernel
theorem sub3_397 : sub3 [1, -2, -1] = true := by decide +kernel
theorem sub3_398 : sub3 [1, -2, 0] = true := by decide +kernel
theorem sub3_399 : sub3 [1, -2, 1] = true := by decide +kernel
theorem sub3_400 : sub3 [1, -2, 2] = true := by decide +kernel
theorem sub3_401 : sub3 [1, -2, 3] = true := by decide +kernel
theorem sub3_402 : sub3 [1, -2, 4] = true := by decide +kernel
theorem sub3_403 : sub3 [1, -2, 5] = true := by decide +kernel
theorem sub3_404 : sub3 [1, -2, 6] = true := by decide +kernel
theorem sub3_405 : sub3 [1, -2, 7] = true := by decide +kernel
theorem sub3_406 : sub3 [1, -1, -9] = true := by decide +kernel
theorem sub3_407 : sub3 [1, -1, -8] = true := by decide +kernel
theorem sub3_408 : sub3 [1, -1, -7] = true := by decide +kernel
theorem sub3_409 : sub3 [1, -1, -6] = true := by decide +kernel
theorem sub3_410 : sub3 [1, -1, -5] = true := by decide +kernel
theorem sub3_411 : sub3 [1, -1, -4] = true := by decide +kernel
theorem sub3_412 : sub3 [1, -1, -3] = true := by decide +kernel
theorem sub3_413 : sub3 [1, -1, -2] = true := by decide +kernel
theorem sub3_414 : sub3 [1, -1, -1] = true := by decide +kernel
theorem sub3_415 : sub3 [1, -1, 0] = true := by decide +kernel
theorem sb3_12 : ∀ q ∈ blk3_12, sub3 q = true := by
  unfold blk3_12
  exact List.forall_mem_cons.2 ⟨sub3_384, List.forall_mem_cons.2 ⟨sub3_385, List.forall_mem_cons.2 ⟨sub3_386, List.forall_mem_cons.2 ⟨sub3_387, List.forall_mem_cons.2 ⟨sub3_388, List.forall_mem_cons.2 ⟨sub3_389, List.forall_mem_cons.2 ⟨sub3_390, List.forall_mem_cons.2 ⟨sub3_391, List.forall_mem_cons.2 ⟨sub3_392, List.forall_mem_cons.2 ⟨sub3_393, List.forall_mem_cons.2 ⟨sub3_394, List.forall_mem_cons.2 ⟨sub3_395, List.forall_mem_cons.2 ⟨sub3_396, List.forall_mem_cons.2 ⟨sub3_397, List.forall_mem_cons.2 ⟨sub3_398, List.forall_mem_cons.2 ⟨sub3_399, List.forall_mem_cons.2 ⟨sub3_400, List.forall_mem_cons.2 ⟨sub3_401, List.forall_mem_cons.2 ⟨sub3_402, List.forall_mem_cons.2 ⟨sub3_403, List.forall_mem_cons.2 ⟨sub3_404, List.forall_mem_cons.2 ⟨sub3_405, List.forall_mem_cons.2 ⟨sub3_406, List.forall_mem_cons.2 ⟨sub3_407, List.forall_mem_cons.2 ⟨sub3_408, List.forall_mem_cons.2 ⟨sub3_409, List.forall_mem_cons.2 ⟨sub3_410, List.forall_mem_cons.2 ⟨sub3_411, List.forall_mem_cons.2 ⟨sub3_412, List.forall_mem_cons.2 ⟨sub3_413, List.forall_mem_cons.2 ⟨sub3_414, List.forall_mem_cons.2 ⟨sub3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_416 : sub3 [1, -1, 1] = true := by decide +kernel
theorem sub3_417 : sub3 [1, -1, 2] = true := by decide +kernel
theorem sub3_418 : sub3 [1, -1, 3] = true := by decide +kernel
theorem sub3_419 : sub3 [1, -1, 4] = true := by decide +kernel
theorem sub3_420 : sub3 [1, -1, 5] = true := by decide +kernel
theorem sub3_421 : sub3 [1, -1, 6] = true := by decide +kernel
theorem sub3_422 : sub3 [1, -1, 7] = true := by decide +kernel
theorem sub3_423 : sub3 [1, -1, 8] = true := by decide +kernel
theorem sub3_424 : sub3 [1, 0, -8] = true := by decide +kernel
theorem sub3_425 : sub3 [1, 0, -7] = true := by decide +kernel
theorem sub3_426 : sub3 [1, 0, -6] = true := by decide +kernel
theorem sub3_427 : sub3 [1, 0, -5] = true := by decide +kernel
theorem sub3_428 : sub3 [1, 0, -4] = true := by decide +kernel
theorem sub3_429 : sub3 [1, 0, -3] = true := by decide +kernel
theorem sub3_430 : sub3 [1, 0, -2] = true := by decide +kernel
theorem sub3_431 : sub3 [1, 0, -1] = true := by decide +kernel
theorem sub3_432 : sub3 [1, 0, 0] = true := by decide +kernel
theorem sub3_433 : sub3 [1, 0, 1] = true := by decide +kernel
theorem sub3_434 : sub3 [1, 0, 2] = true := by decide +kernel
theorem sub3_435 : sub3 [1, 0, 3] = true := by decide +kernel
theorem sub3_436 : sub3 [1, 0, 4] = true := by decide +kernel
theorem sub3_437 : sub3 [1, 0, 5] = true := by decide +kernel
theorem sub3_438 : sub3 [1, 0, 6] = true := by decide +kernel
theorem sub3_439 : sub3 [1, 0, 7] = true := by decide +kernel
theorem sub3_440 : sub3 [1, 0, 8] = true := by decide +kernel
theorem sub3_441 : sub3 [1, 1, -8] = true := by decide +kernel
theorem sub3_442 : sub3 [1, 1, -7] = true := by decide +kernel
theorem sub3_443 : sub3 [1, 1, -6] = true := by decide +kernel
theorem sub3_444 : sub3 [1, 1, -5] = true := by decide +kernel
theorem sub3_445 : sub3 [1, 1, -4] = true := by decide +kernel
theorem sub3_446 : sub3 [1, 1, -3] = true := by decide +kernel
theorem sub3_447 : sub3 [1, 1, -2] = true := by decide +kernel
theorem sb3_13 : ∀ q ∈ blk3_13, sub3 q = true := by
  unfold blk3_13
  exact List.forall_mem_cons.2 ⟨sub3_416, List.forall_mem_cons.2 ⟨sub3_417, List.forall_mem_cons.2 ⟨sub3_418, List.forall_mem_cons.2 ⟨sub3_419, List.forall_mem_cons.2 ⟨sub3_420, List.forall_mem_cons.2 ⟨sub3_421, List.forall_mem_cons.2 ⟨sub3_422, List.forall_mem_cons.2 ⟨sub3_423, List.forall_mem_cons.2 ⟨sub3_424, List.forall_mem_cons.2 ⟨sub3_425, List.forall_mem_cons.2 ⟨sub3_426, List.forall_mem_cons.2 ⟨sub3_427, List.forall_mem_cons.2 ⟨sub3_428, List.forall_mem_cons.2 ⟨sub3_429, List.forall_mem_cons.2 ⟨sub3_430, List.forall_mem_cons.2 ⟨sub3_431, List.forall_mem_cons.2 ⟨sub3_432, List.forall_mem_cons.2 ⟨sub3_433, List.forall_mem_cons.2 ⟨sub3_434, List.forall_mem_cons.2 ⟨sub3_435, List.forall_mem_cons.2 ⟨sub3_436, List.forall_mem_cons.2 ⟨sub3_437, List.forall_mem_cons.2 ⟨sub3_438, List.forall_mem_cons.2 ⟨sub3_439, List.forall_mem_cons.2 ⟨sub3_440, List.forall_mem_cons.2 ⟨sub3_441, List.forall_mem_cons.2 ⟨sub3_442, List.forall_mem_cons.2 ⟨sub3_443, List.forall_mem_cons.2 ⟨sub3_444, List.forall_mem_cons.2 ⟨sub3_445, List.forall_mem_cons.2 ⟨sub3_446, List.forall_mem_cons.2 ⟨sub3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_448 : sub3 [1, 1, -1] = true := by decide +kernel
theorem sub3_449 : sub3 [1, 1, 0] = true := by decide +kernel
theorem sub3_450 : sub3 [1, 1, 1] = true := by decide +kernel
theorem sub3_451 : sub3 [1, 1, 2] = true := by decide +kernel
theorem sub3_452 : sub3 [1, 1, 3] = true := by decide +kernel
theorem sub3_453 : sub3 [1, 1, 4] = true := by decide +kernel
theorem sub3_454 : sub3 [1, 1, 5] = true := by decide +kernel
theorem sub3_455 : sub3 [1, 1, 6] = true := by decide +kernel
theorem sub3_456 : sub3 [1, 1, 7] = true := by decide +kernel
theorem sub3_457 : sub3 [1, 1, 8] = true := by decide +kernel
theorem sub3_458 : sub3 [1, 2, -7] = true := by decide +kernel
theorem sub3_459 : sub3 [1, 2, -6] = true := by decide +kernel
theorem sub3_460 : sub3 [1, 2, -5] = true := by decide +kernel
theorem sub3_461 : sub3 [1, 2, -4] = true := by decide +kernel
theorem sub3_462 : sub3 [1, 2, -3] = true := by decide +kernel
theorem sub3_463 : sub3 [1, 2, -2] = true := by decide +kernel
theorem sub3_464 : sub3 [1, 2, -1] = true := by decide +kernel
theorem sub3_465 : sub3 [1, 2, 0] = true := by decide +kernel
theorem sub3_466 : sub3 [1, 2, 1] = true := by decide +kernel
theorem sub3_467 : sub3 [1, 2, 2] = true := by decide +kernel
theorem sub3_468 : sub3 [1, 2, 3] = true := by decide +kernel
theorem sub3_469 : sub3 [1, 2, 4] = true := by decide +kernel
theorem sub3_470 : sub3 [1, 2, 5] = true := by decide +kernel
theorem sub3_471 : sub3 [1, 2, 6] = true := by decide +kernel
theorem sub3_472 : sub3 [1, 2, 7] = true := by decide +kernel
theorem sub3_473 : sub3 [1, 2, 8] = true := by decide +kernel
theorem sub3_474 : sub3 [1, 3, -6] = true := by decide +kernel
theorem sub3_475 : sub3 [1, 3, -5] = true := by decide +kernel
theorem sub3_476 : sub3 [1, 3, -4] = true := by decide +kernel
theorem sub3_477 : sub3 [1, 3, -3] = true := by decide +kernel
theorem sub3_478 : sub3 [1, 3, -2] = true := by decide +kernel
theorem sub3_479 : sub3 [1, 3, -1] = true := by decide +kernel
theorem sb3_14 : ∀ q ∈ blk3_14, sub3 q = true := by
  unfold blk3_14
  exact List.forall_mem_cons.2 ⟨sub3_448, List.forall_mem_cons.2 ⟨sub3_449, List.forall_mem_cons.2 ⟨sub3_450, List.forall_mem_cons.2 ⟨sub3_451, List.forall_mem_cons.2 ⟨sub3_452, List.forall_mem_cons.2 ⟨sub3_453, List.forall_mem_cons.2 ⟨sub3_454, List.forall_mem_cons.2 ⟨sub3_455, List.forall_mem_cons.2 ⟨sub3_456, List.forall_mem_cons.2 ⟨sub3_457, List.forall_mem_cons.2 ⟨sub3_458, List.forall_mem_cons.2 ⟨sub3_459, List.forall_mem_cons.2 ⟨sub3_460, List.forall_mem_cons.2 ⟨sub3_461, List.forall_mem_cons.2 ⟨sub3_462, List.forall_mem_cons.2 ⟨sub3_463, List.forall_mem_cons.2 ⟨sub3_464, List.forall_mem_cons.2 ⟨sub3_465, List.forall_mem_cons.2 ⟨sub3_466, List.forall_mem_cons.2 ⟨sub3_467, List.forall_mem_cons.2 ⟨sub3_468, List.forall_mem_cons.2 ⟨sub3_469, List.forall_mem_cons.2 ⟨sub3_470, List.forall_mem_cons.2 ⟨sub3_471, List.forall_mem_cons.2 ⟨sub3_472, List.forall_mem_cons.2 ⟨sub3_473, List.forall_mem_cons.2 ⟨sub3_474, List.forall_mem_cons.2 ⟨sub3_475, List.forall_mem_cons.2 ⟨sub3_476, List.forall_mem_cons.2 ⟨sub3_477, List.forall_mem_cons.2 ⟨sub3_478, List.forall_mem_cons.2 ⟨sub3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C054
