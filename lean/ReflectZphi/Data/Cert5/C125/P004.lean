import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_0 : sub5 [-5] = true := by decide +kernel
theorem sub5_1 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_2 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_3 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_4 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_5 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_6 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_7 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_8 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_9 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_10 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_11 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_12 : sub5 [-3, -3, -5] = true := by decide +kernel
theorem sub5_13 : sub5 [-3, -3, -4] = true := by decide +kernel
theorem sub5_14 : sub5 [-3, -3, -3] = true := by decide +kernel
theorem sub5_15 : sub5 [-3, -3, -2] = true := by decide +kernel
theorem sub5_16 : sub5 [-3, -3, -1] = true := by decide +kernel
theorem sub5_17 : sub5 [-3, -3, 0] = true := by decide +kernel
theorem sub5_18 : sub5 [-3, -3, 1] = true := by decide +kernel
theorem sub5_19 : sub5 [-3, -3, 2] = true := by decide +kernel
theorem sub5_20 : sub5 [-3, -3, 3] = true := by decide +kernel
theorem sub5_21 : sub5 [-3, -3, 4] = true := by decide +kernel
theorem sub5_22 : sub5 [-3, -3, 5] = true := by decide +kernel
theorem sub5_23 : sub5 [-3, -3, 6] = true := by decide +kernel
theorem sub5_24 : sub5 [-3, -3, 7] = true := by decide +kernel
theorem sub5_25 : sub5 [-3, -3, 8] = true := by decide +kernel
theorem sub5_26 : sub5 [-3, -2, -7] = true := by decide +kernel
theorem sub5_27 : sub5 [-3, -2, -6] = true := by decide +kernel
theorem sub5_28 : sub5 [-3, -2, -5] = true := by decide +kernel
theorem sub5_29 : sub5 [-3, -2, -4] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, -2, -3] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, -2, -2] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-3, -2, -1] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, -2, 0] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, -2, 1] = true := by decide +kernel
theorem sub5_35 : sub5 [-3, -2, 2] = true := by decide +kernel
theorem sub5_36 : sub5 [-3, -2, 3] = true := by decide +kernel
theorem sub5_37 : sub5 [-3, -2, 4] = true := by decide +kernel
theorem sub5_38 : sub5 [-3, -2, 5] = true := by decide +kernel
theorem sub5_39 : sub5 [-3, -2, 6] = true := by decide +kernel
theorem sub5_40 : sub5 [-3, -2, 7] = true := by decide +kernel
theorem sub5_41 : sub5 [-3, -2, 8] = true := by decide +kernel
theorem sub5_42 : sub5 [-3, -1, -7] = true := by decide +kernel
theorem sub5_43 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_44 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_45 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_46 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_47 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_48 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_49 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_50 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_51 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_52 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_53 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_54 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_55 : sub5 [-3, -1, 6] = true := by decide +kernel
theorem sub5_56 : sub5 [-3, -1, 7] = true := by decide +kernel
theorem sub5_57 : sub5 [-3, -1, 8] = true := by decide +kernel
theorem sub5_58 : sub5 [-3, 0, -8] = true := by decide +kernel
theorem sub5_59 : sub5 [-3, 0, -7] = true := by decide +kernel
theorem sub5_60 : sub5 [-3, 0, -6] = true := by decide +kernel
theorem sub5_61 : sub5 [-3, 0, -5] = true := by decide +kernel
theorem sub5_62 : sub5 [-3, 0, -4] = true := by decide +kernel
theorem sub5_63 : sub5 [-3, 0, -3] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-3, 0, -2] = true := by decide +kernel
theorem sub5_65 : sub5 [-3, 0, -1] = true := by decide +kernel
theorem sub5_66 : sub5 [-3, 0, 0] = true := by decide +kernel
theorem sub5_67 : sub5 [-3, 0, 1] = true := by decide +kernel
theorem sub5_68 : sub5 [-3, 0, 2] = true := by decide +kernel
theorem sub5_69 : sub5 [-3, 0, 3] = true := by decide +kernel
theorem sub5_70 : sub5 [-3, 0, 4] = true := by decide +kernel
theorem sub5_71 : sub5 [-3, 0, 5] = true := by decide +kernel
theorem sub5_72 : sub5 [-3, 0, 6] = true := by decide +kernel
theorem sub5_73 : sub5 [-3, 0, 7] = true := by decide +kernel
theorem sub5_74 : sub5 [-3, 1, -8] = true := by decide +kernel
theorem sub5_75 : sub5 [-3, 1, -7] = true := by decide +kernel
theorem sub5_76 : sub5 [-3, 1, -6] = true := by decide +kernel
theorem sub5_77 : sub5 [-3, 1, -5] = true := by decide +kernel
theorem sub5_78 : sub5 [-3, 1, -4] = true := by decide +kernel
theorem sub5_79 : sub5 [-3, 1, -3] = true := by decide +kernel
theorem sub5_80 : sub5 [-3, 1, -2] = true := by decide +kernel
theorem sub5_81 : sub5 [-3, 1, -1] = true := by decide +kernel
theorem sub5_82 : sub5 [-3, 1, 0] = true := by decide +kernel
theorem sub5_83 : sub5 [-3, 1, 1] = true := by decide +kernel
theorem sub5_84 : sub5 [-3, 1, 2] = true := by decide +kernel
theorem sub5_85 : sub5 [-3, 1, 3] = true := by decide +kernel
theorem sub5_86 : sub5 [-3, 1, 4] = true := by decide +kernel
theorem sub5_87 : sub5 [-3, 1, 5] = true := by decide +kernel
theorem sub5_88 : sub5 [-3, 1, 6] = true := by decide +kernel
theorem sub5_89 : sub5 [-3, 2, -8] = true := by decide +kernel
theorem sub5_90 : sub5 [-3, 2, -7] = true := by decide +kernel
theorem sub5_91 : sub5 [-3, 2, -6] = true := by decide +kernel
theorem sub5_92 : sub5 [-3, 2, -5] = true := by decide +kernel
theorem sub5_93 : sub5 [-3, 2, -4] = true := by decide +kernel
theorem sub5_94 : sub5 [-3, 2, -3] = true := by decide +kernel
theorem sub5_95 : sub5 [-3, 2, -2] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [-3, 2, -1] = true := by decide +kernel
theorem sub5_97 : sub5 [-3, 2, 0] = true := by decide +kernel
theorem sub5_98 : sub5 [-3, 2, 1] = true := by decide +kernel
theorem sub5_99 : sub5 [-3, 2, 2] = true := by decide +kernel
theorem sub5_100 : sub5 [-3, 2, 3] = true := by decide +kernel
theorem sub5_101 : sub5 [-3, 2, 4] = true := by decide +kernel
theorem sub5_102 : sub5 [-3, 2, 5] = true := by decide +kernel
theorem sub5_103 : sub5 [-3, 3] = true := by decide +kernel
theorem sub5_104 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_105 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_106 : sub5 [-2, -4, -5] = true := by decide +kernel
theorem sub5_107 : sub5 [-2, -4, -4] = true := by decide +kernel
theorem sub5_108 : sub5 [-2, -4, -3] = true := by decide +kernel
theorem sub5_109 : sub5 [-2, -4, -2] = true := by decide +kernel
theorem sub5_110 : sub5 [-2, -4, -1] = true := by decide +kernel
theorem sub5_111 : sub5 [-2, -4, 0] = true := by decide +kernel
theorem sub5_112 : sub5 [-2, -4, 1] = true := by decide +kernel
theorem sub5_113 : sub5 [-2, -4, 2] = true := by decide +kernel
theorem sub5_114 : sub5 [-2, -4, 3] = true := by decide +kernel
theorem sub5_115 : sub5 [-2, -4, 4] = true := by decide +kernel
theorem sub5_116 : sub5 [-2, -4, 5] = true := by decide +kernel
theorem sub5_117 : sub5 [-2, -4, 6] = true := by decide +kernel
theorem sub5_118 : sub5 [-2, -4, 7] = true := by decide +kernel
theorem sub5_119 : sub5 [-2, -4, 8] = true := by decide +kernel
theorem sub5_120 : sub5 [-2, -3, -6] = true := by decide +kernel
theorem sub5_121 : sub5 [-2, -3, -5] = true := by decide +kernel
theorem sub5_122 : sub5 [-2, -3, -4] = true := by decide +kernel
theorem sub5_123 : sub5 [-2, -3, -3] = true := by decide +kernel
theorem sub5_124 : sub5 [-2, -3, -2] = true := by decide +kernel
theorem sub5_125 : sub5 [-2, -3, -1] = true := by decide +kernel
theorem sub5_126 : sub5 [-2, -3, 0] = true := by decide +kernel
theorem sub5_127 : sub5 [-2, -3, 1] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_128 : sub5 [-2, -3, 2] = true := by decide +kernel
theorem sub5_129 : sub5 [-2, -3, 3] = true := by decide +kernel
theorem sub5_130 : sub5 [-2, -3, 4] = true := by decide +kernel
theorem sub5_131 : sub5 [-2, -3, 5] = true := by decide +kernel
theorem sub5_132 : sub5 [-2, -3, 6] = true := by decide +kernel
theorem sub5_133 : sub5 [-2, -3, 7] = true := by decide +kernel
theorem sub5_134 : sub5 [-2, -3, 8] = true := by decide +kernel
theorem sub5_135 : sub5 [-2, -3, 9] = true := by decide +kernel
theorem sub5_136 : sub5 [-2, -2, -8] = true := by decide +kernel
theorem sub5_137 : sub5 [-2, -2, -7] = true := by decide +kernel
theorem sub5_138 : sub5 [-2, -2, -6] = true := by decide +kernel
theorem sub5_139 : sub5 [-2, -2, -5] = true := by decide +kernel
theorem sub5_140 : sub5 [-2, -2, -4] = true := by decide +kernel
theorem sub5_141 : sub5 [-2, -2, -3] = true := by decide +kernel
theorem sub5_142 : sub5 [-2, -2, -2] = true := by decide +kernel
theorem sub5_143 : sub5 [-2, -2, -1] = true := by decide +kernel
theorem sub5_144 : sub5 [-2, -2, 0] = true := by decide +kernel
theorem sub5_145 : sub5 [-2, -2, 1] = true := by decide +kernel
theorem sub5_146 : sub5 [-2, -2, 2] = true := by decide +kernel
theorem sub5_147 : sub5 [-2, -2, 3] = true := by decide +kernel
theorem sub5_148 : sub5 [-2, -2, 4] = true := by decide +kernel
theorem sub5_149 : sub5 [-2, -2, 5] = true := by decide +kernel
theorem sub5_150 : sub5 [-2, -2, 6] = true := by decide +kernel
theorem sub5_151 : sub5 [-2, -2, 7] = true := by decide +kernel
theorem sub5_152 : sub5 [-2, -2, 8] = true := by decide +kernel
theorem sub5_153 : sub5 [-2, -2, 9] = true := by decide +kernel
theorem sub5_154 : sub5 [-2, -1, -9] = true := by decide +kernel
theorem sub5_155 : sub5 [-2, -1, -8] = true := by decide +kernel
theorem sub5_156 : sub5 [-2, -1, -7] = true := by decide +kernel
theorem sub5_157 : sub5 [-2, -1, -6] = true := by decide +kernel
theorem sub5_158 : sub5 [-2, -1, -5] = true := by decide +kernel
theorem sub5_159 : sub5 [-2, -1, -4] = true := by decide +kernel
theorem sb5_4 : ∀ q ∈ blk5_4, sub5 q = true := by
  unfold blk5_4
  exact List.forall_mem_cons.2 ⟨sub5_128, List.forall_mem_cons.2 ⟨sub5_129, List.forall_mem_cons.2 ⟨sub5_130, List.forall_mem_cons.2 ⟨sub5_131, List.forall_mem_cons.2 ⟨sub5_132, List.forall_mem_cons.2 ⟨sub5_133, List.forall_mem_cons.2 ⟨sub5_134, List.forall_mem_cons.2 ⟨sub5_135, List.forall_mem_cons.2 ⟨sub5_136, List.forall_mem_cons.2 ⟨sub5_137, List.forall_mem_cons.2 ⟨sub5_138, List.forall_mem_cons.2 ⟨sub5_139, List.forall_mem_cons.2 ⟨sub5_140, List.forall_mem_cons.2 ⟨sub5_141, List.forall_mem_cons.2 ⟨sub5_142, List.forall_mem_cons.2 ⟨sub5_143, List.forall_mem_cons.2 ⟨sub5_144, List.forall_mem_cons.2 ⟨sub5_145, List.forall_mem_cons.2 ⟨sub5_146, List.forall_mem_cons.2 ⟨sub5_147, List.forall_mem_cons.2 ⟨sub5_148, List.forall_mem_cons.2 ⟨sub5_149, List.forall_mem_cons.2 ⟨sub5_150, List.forall_mem_cons.2 ⟨sub5_151, List.forall_mem_cons.2 ⟨sub5_152, List.forall_mem_cons.2 ⟨sub5_153, List.forall_mem_cons.2 ⟨sub5_154, List.forall_mem_cons.2 ⟨sub5_155, List.forall_mem_cons.2 ⟨sub5_156, List.forall_mem_cons.2 ⟨sub5_157, List.forall_mem_cons.2 ⟨sub5_158, List.forall_mem_cons.2 ⟨sub5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_160 : sub5 [-2, -1, -3] = true := by decide +kernel
theorem sub5_161 : sub5 [-2, -1, -2] = true := by decide +kernel
theorem sub5_162 : sub5 [-2, -1, -1] = true := by decide +kernel
theorem sub5_163 : sub5 [-2, -1, 0] = true := by decide +kernel
theorem sub5_164 : sub5 [-2, -1, 1] = true := by decide +kernel
theorem sub5_165 : sub5 [-2, -1, 2] = true := by decide +kernel
theorem sub5_166 : sub5 [-2, -1, 3] = true := by decide +kernel
theorem sub5_167 : sub5 [-2, -1, 4] = true := by decide +kernel
theorem sub5_168 : sub5 [-2, -1, 5] = true := by decide +kernel
theorem sub5_169 : sub5 [-2, -1, 6] = true := by decide +kernel
theorem sub5_170 : sub5 [-2, -1, 7] = true := by decide +kernel
theorem sub5_171 : sub5 [-2, -1, 8] = true := by decide +kernel
theorem sub5_172 : sub5 [-2, -1, 9] = true := by decide +kernel
theorem sub5_173 : sub5 [-2, 0, -9] = true := by decide +kernel
theorem sub5_174 : sub5 [-2, 0, -8] = true := by decide +kernel
theorem sub5_175 : sub5 [-2, 0, -7] = true := by decide +kernel
theorem sub5_176 : sub5 [-2, 0, -6] = true := by decide +kernel
theorem sub5_177 : sub5 [-2, 0, -5] = true := by decide +kernel
theorem sub5_178 : sub5 [-2, 0, -4] = true := by decide +kernel
theorem sub5_179 : sub5 [-2, 0, -3] = true := by decide +kernel
theorem sub5_180 : sub5 [-2, 0, -2] = true := by decide +kernel
theorem sub5_181 : sub5 [-2, 0, -1] = true := by decide +kernel
theorem sub5_182 : sub5 [-2, 0, 0] = true := by decide +kernel
theorem sub5_183 : sub5 [-2, 0, 1] = true := by decide +kernel
theorem sub5_184 : sub5 [-2, 0, 2] = true := by decide +kernel
theorem sub5_185 : sub5 [-2, 0, 3] = true := by decide +kernel
theorem sub5_186 : sub5 [-2, 0, 4] = true := by decide +kernel
theorem sub5_187 : sub5 [-2, 0, 5] = true := by decide +kernel
theorem sub5_188 : sub5 [-2, 0, 6] = true := by decide +kernel
theorem sub5_189 : sub5 [-2, 0, 7] = true := by decide +kernel
theorem sub5_190 : sub5 [-2, 0, 8] = true := by decide +kernel
theorem sub5_191 : sub5 [-2, 1, -9] = true := by decide +kernel
theorem sb5_5 : ∀ q ∈ blk5_5, sub5 q = true := by
  unfold blk5_5
  exact List.forall_mem_cons.2 ⟨sub5_160, List.forall_mem_cons.2 ⟨sub5_161, List.forall_mem_cons.2 ⟨sub5_162, List.forall_mem_cons.2 ⟨sub5_163, List.forall_mem_cons.2 ⟨sub5_164, List.forall_mem_cons.2 ⟨sub5_165, List.forall_mem_cons.2 ⟨sub5_166, List.forall_mem_cons.2 ⟨sub5_167, List.forall_mem_cons.2 ⟨sub5_168, List.forall_mem_cons.2 ⟨sub5_169, List.forall_mem_cons.2 ⟨sub5_170, List.forall_mem_cons.2 ⟨sub5_171, List.forall_mem_cons.2 ⟨sub5_172, List.forall_mem_cons.2 ⟨sub5_173, List.forall_mem_cons.2 ⟨sub5_174, List.forall_mem_cons.2 ⟨sub5_175, List.forall_mem_cons.2 ⟨sub5_176, List.forall_mem_cons.2 ⟨sub5_177, List.forall_mem_cons.2 ⟨sub5_178, List.forall_mem_cons.2 ⟨sub5_179, List.forall_mem_cons.2 ⟨sub5_180, List.forall_mem_cons.2 ⟨sub5_181, List.forall_mem_cons.2 ⟨sub5_182, List.forall_mem_cons.2 ⟨sub5_183, List.forall_mem_cons.2 ⟨sub5_184, List.forall_mem_cons.2 ⟨sub5_185, List.forall_mem_cons.2 ⟨sub5_186, List.forall_mem_cons.2 ⟨sub5_187, List.forall_mem_cons.2 ⟨sub5_188, List.forall_mem_cons.2 ⟨sub5_189, List.forall_mem_cons.2 ⟨sub5_190, List.forall_mem_cons.2 ⟨sub5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_192 : sub5 [-2, 1, -8] = true := by decide +kernel
theorem sub5_193 : sub5 [-2, 1, -7] = true := by decide +kernel
theorem sub5_194 : sub5 [-2, 1, -6] = true := by decide +kernel
theorem sub5_195 : sub5 [-2, 1, -5] = true := by decide +kernel
theorem sub5_196 : sub5 [-2, 1, -4] = true := by decide +kernel
theorem sub5_197 : sub5 [-2, 1, -3] = true := by decide +kernel
theorem sub5_198 : sub5 [-2, 1, -2] = true := by decide +kernel
theorem sub5_199 : sub5 [-2, 1, -1] = true := by decide +kernel
theorem sub5_200 : sub5 [-2, 1, 0] = true := by decide +kernel
theorem sub5_201 : sub5 [-2, 1, 1] = true := by decide +kernel
theorem sub5_202 : sub5 [-2, 1, 2] = true := by decide +kernel
theorem sub5_203 : sub5 [-2, 1, 3] = true := by decide +kernel
theorem sub5_204 : sub5 [-2, 1, 4] = true := by decide +kernel
theorem sub5_205 : sub5 [-2, 1, 5] = true := by decide +kernel
theorem sub5_206 : sub5 [-2, 1, 6] = true := by decide +kernel
theorem sub5_207 : sub5 [-2, 1, 7] = true := by decide +kernel
theorem sub5_208 : sub5 [-2, 2, -9] = true := by decide +kernel
theorem sub5_209 : sub5 [-2, 2, -8] = true := by decide +kernel
theorem sub5_210 : sub5 [-2, 2, -7] = true := by decide +kernel
theorem sub5_211 : sub5 [-2, 2, -6] = true := by decide +kernel
theorem sub5_212 : sub5 [-2, 2, -5] = true := by decide +kernel
theorem sub5_213 : sub5 [-2, 2, -4] = true := by decide +kernel
theorem sub5_214 : sub5 [-2, 2, -3] = true := by decide +kernel
theorem sub5_215 : sub5 [-2, 2, -2] = true := by decide +kernel
theorem sub5_216 : sub5 [-2, 2, -1] = true := by decide +kernel
theorem sub5_217 : sub5 [-2, 2, 0] = true := by decide +kernel
theorem sub5_218 : sub5 [-2, 2, 1] = true := by decide +kernel
theorem sub5_219 : sub5 [-2, 2, 2] = true := by decide +kernel
theorem sub5_220 : sub5 [-2, 2, 3] = true := by decide +kernel
theorem sub5_221 : sub5 [-2, 2, 4] = true := by decide +kernel
theorem sub5_222 : sub5 [-2, 2, 5] = true := by decide +kernel
theorem sub5_223 : sub5 [-2, 2, 6] = true := by decide +kernel
theorem sb5_6 : ∀ q ∈ blk5_6, sub5 q = true := by
  unfold blk5_6
  exact List.forall_mem_cons.2 ⟨sub5_192, List.forall_mem_cons.2 ⟨sub5_193, List.forall_mem_cons.2 ⟨sub5_194, List.forall_mem_cons.2 ⟨sub5_195, List.forall_mem_cons.2 ⟨sub5_196, List.forall_mem_cons.2 ⟨sub5_197, List.forall_mem_cons.2 ⟨sub5_198, List.forall_mem_cons.2 ⟨sub5_199, List.forall_mem_cons.2 ⟨sub5_200, List.forall_mem_cons.2 ⟨sub5_201, List.forall_mem_cons.2 ⟨sub5_202, List.forall_mem_cons.2 ⟨sub5_203, List.forall_mem_cons.2 ⟨sub5_204, List.forall_mem_cons.2 ⟨sub5_205, List.forall_mem_cons.2 ⟨sub5_206, List.forall_mem_cons.2 ⟨sub5_207, List.forall_mem_cons.2 ⟨sub5_208, List.forall_mem_cons.2 ⟨sub5_209, List.forall_mem_cons.2 ⟨sub5_210, List.forall_mem_cons.2 ⟨sub5_211, List.forall_mem_cons.2 ⟨sub5_212, List.forall_mem_cons.2 ⟨sub5_213, List.forall_mem_cons.2 ⟨sub5_214, List.forall_mem_cons.2 ⟨sub5_215, List.forall_mem_cons.2 ⟨sub5_216, List.forall_mem_cons.2 ⟨sub5_217, List.forall_mem_cons.2 ⟨sub5_218, List.forall_mem_cons.2 ⟨sub5_219, List.forall_mem_cons.2 ⟨sub5_220, List.forall_mem_cons.2 ⟨sub5_221, List.forall_mem_cons.2 ⟨sub5_222, List.forall_mem_cons.2 ⟨sub5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_224 : sub5 [-2, 3, -8] = true := by decide +kernel
theorem sub5_225 : sub5 [-2, 3, -7] = true := by decide +kernel
theorem sub5_226 : sub5 [-2, 3, -6] = true := by decide +kernel
theorem sub5_227 : sub5 [-2, 3, -5] = true := by decide +kernel
theorem sub5_228 : sub5 [-2, 3, -4] = true := by decide +kernel
theorem sub5_229 : sub5 [-2, 3, -3] = true := by decide +kernel
theorem sub5_230 : sub5 [-2, 3, -2] = true := by decide +kernel
theorem sub5_231 : sub5 [-2, 3, -1] = true := by decide +kernel
theorem sub5_232 : sub5 [-2, 3, 0] = true := by decide +kernel
theorem sub5_233 : sub5 [-2, 3, 1] = true := by decide +kernel
theorem sub5_234 : sub5 [-2, 3, 2] = true := by decide +kernel
theorem sub5_235 : sub5 [-2, 3, 3] = true := by decide +kernel
theorem sub5_236 : sub5 [-2, 3, 4] = true := by decide +kernel
theorem sub5_237 : sub5 [-2, 3, 5] = true := by decide +kernel
theorem sub5_238 : sub5 [-2, 4] = true := by decide +kernel
theorem sub5_239 : sub5 [-1, -6] = true := by decide +kernel
theorem sub5_240 : sub5 [-1, -5] = true := by decide +kernel
theorem sub5_241 : sub5 [-1, -4, -5] = true := by decide +kernel
theorem sub5_242 : sub5 [-1, -4, -4] = true := by decide +kernel
theorem sub5_243 : sub5 [-1, -4, -3] = true := by decide +kernel
theorem sub5_244 : sub5 [-1, -4, -2] = true := by decide +kernel
theorem sub5_245 : sub5 [-1, -4, -1] = true := by decide +kernel
theorem sub5_246 : sub5 [-1, -4, 0] = true := by decide +kernel
theorem sub5_247 : sub5 [-1, -4, 1] = true := by decide +kernel
theorem sub5_248 : sub5 [-1, -4, 2] = true := by decide +kernel
theorem sub5_249 : sub5 [-1, -4, 3] = true := by decide +kernel
theorem sub5_250 : sub5 [-1, -4, 4] = true := by decide +kernel
theorem sub5_251 : sub5 [-1, -4, 5] = true := by decide +kernel
theorem sub5_252 : sub5 [-1, -4, 6] = true := by decide +kernel
theorem sub5_253 : sub5 [-1, -4, 7] = true := by decide +kernel
theorem sub5_254 : sub5 [-1, -4, 8] = true := by decide +kernel
theorem sub5_255 : sub5 [-1, -3, -7] = true := by decide +kernel
theorem sb5_7 : ∀ q ∈ blk5_7, sub5 q = true := by
  unfold blk5_7
  exact List.forall_mem_cons.2 ⟨sub5_224, List.forall_mem_cons.2 ⟨sub5_225, List.forall_mem_cons.2 ⟨sub5_226, List.forall_mem_cons.2 ⟨sub5_227, List.forall_mem_cons.2 ⟨sub5_228, List.forall_mem_cons.2 ⟨sub5_229, List.forall_mem_cons.2 ⟨sub5_230, List.forall_mem_cons.2 ⟨sub5_231, List.forall_mem_cons.2 ⟨sub5_232, List.forall_mem_cons.2 ⟨sub5_233, List.forall_mem_cons.2 ⟨sub5_234, List.forall_mem_cons.2 ⟨sub5_235, List.forall_mem_cons.2 ⟨sub5_236, List.forall_mem_cons.2 ⟨sub5_237, List.forall_mem_cons.2 ⟨sub5_238, List.forall_mem_cons.2 ⟨sub5_239, List.forall_mem_cons.2 ⟨sub5_240, List.forall_mem_cons.2 ⟨sub5_241, List.forall_mem_cons.2 ⟨sub5_242, List.forall_mem_cons.2 ⟨sub5_243, List.forall_mem_cons.2 ⟨sub5_244, List.forall_mem_cons.2 ⟨sub5_245, List.forall_mem_cons.2 ⟨sub5_246, List.forall_mem_cons.2 ⟨sub5_247, List.forall_mem_cons.2 ⟨sub5_248, List.forall_mem_cons.2 ⟨sub5_249, List.forall_mem_cons.2 ⟨sub5_250, List.forall_mem_cons.2 ⟨sub5_251, List.forall_mem_cons.2 ⟨sub5_252, List.forall_mem_cons.2 ⟨sub5_253, List.forall_mem_cons.2 ⟨sub5_254, List.forall_mem_cons.2 ⟨sub5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_256 : sub5 [-1, -3, -6] = true := by decide +kernel
theorem sub5_257 : sub5 [-1, -3, -5] = true := by decide +kernel
theorem sub5_258 : sub5 [-1, -3, -4] = true := by decide +kernel
theorem sub5_259 : sub5 [-1, -3, -3] = true := by decide +kernel
theorem sub5_260 : sub5 [-1, -3, -2] = true := by decide +kernel
theorem sub5_261 : sub5 [-1, -3, -1] = true := by decide +kernel
theorem sub5_262 : sub5 [-1, -3, 0] = true := by decide +kernel
theorem sub5_263 : sub5 [-1, -3, 1] = true := by decide +kernel
theorem sub5_264 : sub5 [-1, -3, 2] = true := by decide +kernel
theorem sub5_265 : sub5 [-1, -3, 3] = true := by decide +kernel
theorem sub5_266 : sub5 [-1, -3, 4] = true := by decide +kernel
theorem sub5_267 : sub5 [-1, -3, 5] = true := by decide +kernel
theorem sub5_268 : sub5 [-1, -3, 6] = true := by decide +kernel
theorem sub5_269 : sub5 [-1, -3, 7] = true := by decide +kernel
theorem sub5_270 : sub5 [-1, -3, 8] = true := by decide +kernel
theorem sub5_271 : sub5 [-1, -3, 9] = true := by decide +kernel
theorem sub5_272 : sub5 [-1, -2, -8] = true := by decide +kernel
theorem sub5_273 : sub5 [-1, -2, -7] = true := by decide +kernel
theorem sub5_274 : sub5 [-1, -2, -6] = true := by decide +kernel
theorem sub5_275 : sub5 [-1, -2, -5] = true := by decide +kernel
theorem sub5_276 : sub5 [-1, -2, -4] = true := by decide +kernel
theorem sub5_277 : sub5 [-1, -2, -3] = true := by decide +kernel
theorem sub5_278 : sub5 [-1, -2, -2] = true := by decide +kernel
theorem sub5_279 : sub5 [-1, -2, -1] = true := by decide +kernel
theorem sub5_280 : sub5 [-1, -2, 0] = true := by decide +kernel
theorem sub5_281 : sub5 [-1, -2, 1] = true := by decide +kernel
theorem sub5_282 : sub5 [-1, -2, 2] = true := by decide +kernel
theorem sub5_283 : sub5 [-1, -2, 3] = true := by decide +kernel
theorem sub5_284 : sub5 [-1, -2, 4] = true := by decide +kernel
theorem sub5_285 : sub5 [-1, -2, 5] = true := by decide +kernel
theorem sub5_286 : sub5 [-1, -2, 6] = true := by decide +kernel
theorem sub5_287 : sub5 [-1, -2, 7] = true := by decide +kernel
theorem sb5_8 : ∀ q ∈ blk5_8, sub5 q = true := by
  unfold blk5_8
  exact List.forall_mem_cons.2 ⟨sub5_256, List.forall_mem_cons.2 ⟨sub5_257, List.forall_mem_cons.2 ⟨sub5_258, List.forall_mem_cons.2 ⟨sub5_259, List.forall_mem_cons.2 ⟨sub5_260, List.forall_mem_cons.2 ⟨sub5_261, List.forall_mem_cons.2 ⟨sub5_262, List.forall_mem_cons.2 ⟨sub5_263, List.forall_mem_cons.2 ⟨sub5_264, List.forall_mem_cons.2 ⟨sub5_265, List.forall_mem_cons.2 ⟨sub5_266, List.forall_mem_cons.2 ⟨sub5_267, List.forall_mem_cons.2 ⟨sub5_268, List.forall_mem_cons.2 ⟨sub5_269, List.forall_mem_cons.2 ⟨sub5_270, List.forall_mem_cons.2 ⟨sub5_271, List.forall_mem_cons.2 ⟨sub5_272, List.forall_mem_cons.2 ⟨sub5_273, List.forall_mem_cons.2 ⟨sub5_274, List.forall_mem_cons.2 ⟨sub5_275, List.forall_mem_cons.2 ⟨sub5_276, List.forall_mem_cons.2 ⟨sub5_277, List.forall_mem_cons.2 ⟨sub5_278, List.forall_mem_cons.2 ⟨sub5_279, List.forall_mem_cons.2 ⟨sub5_280, List.forall_mem_cons.2 ⟨sub5_281, List.forall_mem_cons.2 ⟨sub5_282, List.forall_mem_cons.2 ⟨sub5_283, List.forall_mem_cons.2 ⟨sub5_284, List.forall_mem_cons.2 ⟨sub5_285, List.forall_mem_cons.2 ⟨sub5_286, List.forall_mem_cons.2 ⟨sub5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_288 : sub5 [-1, -2, 8] = true := by decide +kernel
theorem sub5_289 : sub5 [-1, -2, 9] = true := by decide +kernel
theorem sub5_290 : sub5 [-1, -1, -9] = true := by decide +kernel
theorem sub5_291 : sub5 [-1, -1, -8] = true := by decide +kernel
theorem sub5_292 : sub5 [-1, -1, -7] = true := by decide +kernel
theorem sub5_293 : sub5 [-1, -1, -6] = true := by decide +kernel
theorem sub5_294 : sub5 [-1, -1, -5] = true := by decide +kernel
theorem sub5_295 : sub5 [-1, -1, -4] = true := by decide +kernel
theorem sub5_296 : sub5 [-1, -1, -3] = true := by decide +kernel
theorem sub5_297 : sub5 [-1, -1, -2] = true := by decide +kernel
theorem sub5_298 : sub5 [-1, -1, -1] = true := by decide +kernel
theorem sub5_299 : sub5 [-1, -1, 0] = true := by decide +kernel
theorem sub5_300 : sub5 [-1, -1, 1] = true := by decide +kernel
theorem sub5_301 : sub5 [-1, -1, 2] = true := by decide +kernel
theorem sub5_302 : sub5 [-1, -1, 3] = true := by decide +kernel
theorem sub5_303 : sub5 [-1, -1, 4] = true := by decide +kernel
theorem sub5_304 : sub5 [-1, -1, 5] = true := by decide +kernel
theorem sub5_305 : sub5 [-1, -1, 6] = true := by decide +kernel
theorem sub5_306 : sub5 [-1, -1, 7] = true := by decide +kernel
theorem sub5_307 : sub5 [-1, -1, 8] = true := by decide +kernel
theorem sub5_308 : sub5 [-1, -1, 9] = true := by decide +kernel
theorem sub5_309 : sub5 [-1, 0, -10] = true := by decide +kernel
theorem sub5_310 : sub5 [-1, 0, -9] = true := by decide +kernel
theorem sub5_311 : sub5 [-1, 0, -8] = true := by decide +kernel
theorem sub5_312 : sub5 [-1, 0, -7] = true := by decide +kernel
theorem sub5_313 : sub5 [-1, 0, -6] = true := by decide +kernel
theorem sub5_314 : sub5 [-1, 0, -5] = true := by decide +kernel
theorem sub5_315 : sub5 [-1, 0, -4] = true := by decide +kernel
theorem sub5_316 : sub5 [-1, 0, -3] = true := by decide +kernel
theorem sub5_317 : sub5 [-1, 0, -2] = true := by decide +kernel
theorem sub5_318 : sub5 [-1, 0, -1] = true := by decide +kernel
theorem sub5_319 : sub5 [-1, 0, 0] = true := by decide +kernel
theorem sb5_9 : ∀ q ∈ blk5_9, sub5 q = true := by
  unfold blk5_9
  exact List.forall_mem_cons.2 ⟨sub5_288, List.forall_mem_cons.2 ⟨sub5_289, List.forall_mem_cons.2 ⟨sub5_290, List.forall_mem_cons.2 ⟨sub5_291, List.forall_mem_cons.2 ⟨sub5_292, List.forall_mem_cons.2 ⟨sub5_293, List.forall_mem_cons.2 ⟨sub5_294, List.forall_mem_cons.2 ⟨sub5_295, List.forall_mem_cons.2 ⟨sub5_296, List.forall_mem_cons.2 ⟨sub5_297, List.forall_mem_cons.2 ⟨sub5_298, List.forall_mem_cons.2 ⟨sub5_299, List.forall_mem_cons.2 ⟨sub5_300, List.forall_mem_cons.2 ⟨sub5_301, List.forall_mem_cons.2 ⟨sub5_302, List.forall_mem_cons.2 ⟨sub5_303, List.forall_mem_cons.2 ⟨sub5_304, List.forall_mem_cons.2 ⟨sub5_305, List.forall_mem_cons.2 ⟨sub5_306, List.forall_mem_cons.2 ⟨sub5_307, List.forall_mem_cons.2 ⟨sub5_308, List.forall_mem_cons.2 ⟨sub5_309, List.forall_mem_cons.2 ⟨sub5_310, List.forall_mem_cons.2 ⟨sub5_311, List.forall_mem_cons.2 ⟨sub5_312, List.forall_mem_cons.2 ⟨sub5_313, List.forall_mem_cons.2 ⟨sub5_314, List.forall_mem_cons.2 ⟨sub5_315, List.forall_mem_cons.2 ⟨sub5_316, List.forall_mem_cons.2 ⟨sub5_317, List.forall_mem_cons.2 ⟨sub5_318, List.forall_mem_cons.2 ⟨sub5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_320 : sub5 [-1, 0, 1] = true := by decide +kernel
theorem sub5_321 : sub5 [-1, 0, 2] = true := by decide +kernel
theorem sub5_322 : sub5 [-1, 0, 3] = true := by decide +kernel
theorem sub5_323 : sub5 [-1, 0, 4] = true := by decide +kernel
theorem sub5_324 : sub5 [-1, 0, 5] = true := by decide +kernel
theorem sub5_325 : sub5 [-1, 0, 6] = true := by decide +kernel
theorem sub5_326 : sub5 [-1, 0, 7] = true := by decide +kernel
theorem sub5_327 : sub5 [-1, 0, 8] = true := by decide +kernel
theorem sub5_328 : sub5 [-1, 0, 9] = true := by decide +kernel
theorem sub5_329 : sub5 [-1, 1, -10] = true := by decide +kernel
theorem sub5_330 : sub5 [-1, 1, -9] = true := by decide +kernel
theorem sub5_331 : sub5 [-1, 1, -8] = true := by decide +kernel
theorem sub5_332 : sub5 [-1, 1, -7] = true := by decide +kernel
theorem sub5_333 : sub5 [-1, 1, -6] = true := by decide +kernel
theorem sub5_334 : sub5 [-1, 1, -5] = true := by decide +kernel
theorem sub5_335 : sub5 [-1, 1, -4] = true := by decide +kernel
theorem sub5_336 : sub5 [-1, 1, -3] = true := by decide +kernel
theorem sub5_337 : sub5 [-1, 1, -2] = true := by decide +kernel
theorem sub5_338 : sub5 [-1, 1, -1] = true := by decide +kernel
theorem sub5_339 : sub5 [-1, 1, 0] = true := by decide +kernel
theorem sub5_340 : sub5 [-1, 1, 1] = true := by decide +kernel
theorem sub5_341 : sub5 [-1, 1, 2] = true := by decide +kernel
theorem sub5_342 : sub5 [-1, 1, 3] = true := by decide +kernel
theorem sub5_343 : sub5 [-1, 1, 4] = true := by decide +kernel
theorem sub5_344 : sub5 [-1, 1, 5] = true := by decide +kernel
theorem sub5_345 : sub5 [-1, 1, 6] = true := by decide +kernel
theorem sub5_346 : sub5 [-1, 1, 7] = true := by decide +kernel
theorem sub5_347 : sub5 [-1, 1, 8] = true := by decide +kernel
theorem sub5_348 : sub5 [-1, 2, -10] = true := by decide +kernel
theorem sub5_349 : sub5 [-1, 2, -9] = true := by decide +kernel
theorem sub5_350 : sub5 [-1, 2, -8] = true := by decide +kernel
theorem sub5_351 : sub5 [-1, 2, -7] = true := by decide +kernel
theorem sb5_10 : ∀ q ∈ blk5_10, sub5 q = true := by
  unfold blk5_10
  exact List.forall_mem_cons.2 ⟨sub5_320, List.forall_mem_cons.2 ⟨sub5_321, List.forall_mem_cons.2 ⟨sub5_322, List.forall_mem_cons.2 ⟨sub5_323, List.forall_mem_cons.2 ⟨sub5_324, List.forall_mem_cons.2 ⟨sub5_325, List.forall_mem_cons.2 ⟨sub5_326, List.forall_mem_cons.2 ⟨sub5_327, List.forall_mem_cons.2 ⟨sub5_328, List.forall_mem_cons.2 ⟨sub5_329, List.forall_mem_cons.2 ⟨sub5_330, List.forall_mem_cons.2 ⟨sub5_331, List.forall_mem_cons.2 ⟨sub5_332, List.forall_mem_cons.2 ⟨sub5_333, List.forall_mem_cons.2 ⟨sub5_334, List.forall_mem_cons.2 ⟨sub5_335, List.forall_mem_cons.2 ⟨sub5_336, List.forall_mem_cons.2 ⟨sub5_337, List.forall_mem_cons.2 ⟨sub5_338, List.forall_mem_cons.2 ⟨sub5_339, List.forall_mem_cons.2 ⟨sub5_340, List.forall_mem_cons.2 ⟨sub5_341, List.forall_mem_cons.2 ⟨sub5_342, List.forall_mem_cons.2 ⟨sub5_343, List.forall_mem_cons.2 ⟨sub5_344, List.forall_mem_cons.2 ⟨sub5_345, List.forall_mem_cons.2 ⟨sub5_346, List.forall_mem_cons.2 ⟨sub5_347, List.forall_mem_cons.2 ⟨sub5_348, List.forall_mem_cons.2 ⟨sub5_349, List.forall_mem_cons.2 ⟨sub5_350, List.forall_mem_cons.2 ⟨sub5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_352 : sub5 [-1, 2, -6] = true := by decide +kernel
theorem sub5_353 : sub5 [-1, 2, -5] = true := by decide +kernel
theorem sub5_354 : sub5 [-1, 2, -4] = true := by decide +kernel
theorem sub5_355 : sub5 [-1, 2, -3] = true := by decide +kernel
theorem sub5_356 : sub5 [-1, 2, -2] = true := by decide +kernel
theorem sub5_357 : sub5 [-1, 2, -1] = true := by decide +kernel
theorem sub5_358 : sub5 [-1, 2, 0] = true := by decide +kernel
theorem sub5_359 : sub5 [-1, 2, 1] = true := by decide +kernel
theorem sub5_360 : sub5 [-1, 2, 2] = true := by decide +kernel
theorem sub5_361 : sub5 [-1, 2, 3] = true := by decide +kernel
theorem sub5_362 : sub5 [-1, 2, 4] = true := by decide +kernel
theorem sub5_363 : sub5 [-1, 2, 5] = true := by decide +kernel
theorem sub5_364 : sub5 [-1, 2, 6] = true := by decide +kernel
theorem sub5_365 : sub5 [-1, 2, 7] = true := by decide +kernel
theorem sub5_366 : sub5 [-1, 3, -9] = true := by decide +kernel
theorem sub5_367 : sub5 [-1, 3, -8] = true := by decide +kernel
theorem sub5_368 : sub5 [-1, 3, -7] = true := by decide +kernel
theorem sub5_369 : sub5 [-1, 3, -6] = true := by decide +kernel
theorem sub5_370 : sub5 [-1, 3, -5] = true := by decide +kernel
theorem sub5_371 : sub5 [-1, 3, -4] = true := by decide +kernel
theorem sub5_372 : sub5 [-1, 3, -3] = true := by decide +kernel
theorem sub5_373 : sub5 [-1, 3, -2] = true := by decide +kernel
theorem sub5_374 : sub5 [-1, 3, -1] = true := by decide +kernel
theorem sub5_375 : sub5 [-1, 3, 0] = true := by decide +kernel
theorem sub5_376 : sub5 [-1, 3, 1] = true := by decide +kernel
theorem sub5_377 : sub5 [-1, 3, 2] = true := by decide +kernel
theorem sub5_378 : sub5 [-1, 3, 3] = true := by decide +kernel
theorem sub5_379 : sub5 [-1, 3, 4] = true := by decide +kernel
theorem sub5_380 : sub5 [-1, 3, 5] = true := by decide +kernel
theorem sub5_381 : sub5 [-1, 3, 6] = true := by decide +kernel
theorem sub5_382 : sub5 [-1, 4] = true := by decide +kernel
theorem sub5_383 : sub5 [-1, 5] = true := by decide +kernel
theorem sb5_11 : ∀ q ∈ blk5_11, sub5 q = true := by
  unfold blk5_11
  exact List.forall_mem_cons.2 ⟨sub5_352, List.forall_mem_cons.2 ⟨sub5_353, List.forall_mem_cons.2 ⟨sub5_354, List.forall_mem_cons.2 ⟨sub5_355, List.forall_mem_cons.2 ⟨sub5_356, List.forall_mem_cons.2 ⟨sub5_357, List.forall_mem_cons.2 ⟨sub5_358, List.forall_mem_cons.2 ⟨sub5_359, List.forall_mem_cons.2 ⟨sub5_360, List.forall_mem_cons.2 ⟨sub5_361, List.forall_mem_cons.2 ⟨sub5_362, List.forall_mem_cons.2 ⟨sub5_363, List.forall_mem_cons.2 ⟨sub5_364, List.forall_mem_cons.2 ⟨sub5_365, List.forall_mem_cons.2 ⟨sub5_366, List.forall_mem_cons.2 ⟨sub5_367, List.forall_mem_cons.2 ⟨sub5_368, List.forall_mem_cons.2 ⟨sub5_369, List.forall_mem_cons.2 ⟨sub5_370, List.forall_mem_cons.2 ⟨sub5_371, List.forall_mem_cons.2 ⟨sub5_372, List.forall_mem_cons.2 ⟨sub5_373, List.forall_mem_cons.2 ⟨sub5_374, List.forall_mem_cons.2 ⟨sub5_375, List.forall_mem_cons.2 ⟨sub5_376, List.forall_mem_cons.2 ⟨sub5_377, List.forall_mem_cons.2 ⟨sub5_378, List.forall_mem_cons.2 ⟨sub5_379, List.forall_mem_cons.2 ⟨sub5_380, List.forall_mem_cons.2 ⟨sub5_381, List.forall_mem_cons.2 ⟨sub5_382, List.forall_mem_cons.2 ⟨sub5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_384 : sub5 [0, -6] = true := by decide +kernel
theorem sub5_385 : sub5 [0, -5] = true := by decide +kernel
theorem sub5_386 : sub5 [0, -4, -5] = true := by decide +kernel
theorem sub5_387 : sub5 [0, -4, -4] = true := by decide +kernel
theorem sub5_388 : sub5 [0, -4, -3] = true := by decide +kernel
theorem sub5_389 : sub5 [0, -4, -2] = true := by decide +kernel
theorem sub5_390 : sub5 [0, -4, -1] = true := by decide +kernel
theorem sub5_391 : sub5 [0, -4, 0] = true := by decide +kernel
theorem sub5_392 : sub5 [0, -4, 1] = true := by decide +kernel
theorem sub5_393 : sub5 [0, -4, 2] = true := by decide +kernel
theorem sub5_394 : sub5 [0, -4, 3] = true := by decide +kernel
theorem sub5_395 : sub5 [0, -4, 4] = true := by decide +kernel
theorem sub5_396 : sub5 [0, -4, 5] = true := by decide +kernel
theorem sub5_397 : sub5 [0, -4, 6] = true := by decide +kernel
theorem sub5_398 : sub5 [0, -4, 7] = true := by decide +kernel
theorem sub5_399 : sub5 [0, -4, 8] = true := by decide +kernel
theorem sub5_400 : sub5 [0, -3, -7] = true := by decide +kernel
theorem sub5_401 : sub5 [0, -3, -6] = true := by decide +kernel
theorem sub5_402 : sub5 [0, -3, -5] = true := by decide +kernel
theorem sub5_403 : sub5 [0, -3, -4] = true := by decide +kernel
theorem sub5_404 : sub5 [0, -3, -3] = true := by decide +kernel
theorem sub5_405 : sub5 [0, -3, -2] = true := by decide +kernel
theorem sub5_406 : sub5 [0, -3, -1] = true := by decide +kernel
theorem sub5_407 : sub5 [0, -3, 0] = true := by decide +kernel
theorem sub5_408 : sub5 [0, -3, 1] = true := by decide +kernel
theorem sub5_409 : sub5 [0, -3, 2] = true := by decide +kernel
theorem sub5_410 : sub5 [0, -3, 3] = true := by decide +kernel
theorem sub5_411 : sub5 [0, -3, 4] = true := by decide +kernel
theorem sub5_412 : sub5 [0, -3, 5] = true := by decide +kernel
theorem sub5_413 : sub5 [0, -3, 6] = true := by decide +kernel
theorem sub5_414 : sub5 [0, -3, 7] = true := by decide +kernel
theorem sub5_415 : sub5 [0, -3, 8] = true := by decide +kernel
theorem sb5_12 : ∀ q ∈ blk5_12, sub5 q = true := by
  unfold blk5_12
  exact List.forall_mem_cons.2 ⟨sub5_384, List.forall_mem_cons.2 ⟨sub5_385, List.forall_mem_cons.2 ⟨sub5_386, List.forall_mem_cons.2 ⟨sub5_387, List.forall_mem_cons.2 ⟨sub5_388, List.forall_mem_cons.2 ⟨sub5_389, List.forall_mem_cons.2 ⟨sub5_390, List.forall_mem_cons.2 ⟨sub5_391, List.forall_mem_cons.2 ⟨sub5_392, List.forall_mem_cons.2 ⟨sub5_393, List.forall_mem_cons.2 ⟨sub5_394, List.forall_mem_cons.2 ⟨sub5_395, List.forall_mem_cons.2 ⟨sub5_396, List.forall_mem_cons.2 ⟨sub5_397, List.forall_mem_cons.2 ⟨sub5_398, List.forall_mem_cons.2 ⟨sub5_399, List.forall_mem_cons.2 ⟨sub5_400, List.forall_mem_cons.2 ⟨sub5_401, List.forall_mem_cons.2 ⟨sub5_402, List.forall_mem_cons.2 ⟨sub5_403, List.forall_mem_cons.2 ⟨sub5_404, List.forall_mem_cons.2 ⟨sub5_405, List.forall_mem_cons.2 ⟨sub5_406, List.forall_mem_cons.2 ⟨sub5_407, List.forall_mem_cons.2 ⟨sub5_408, List.forall_mem_cons.2 ⟨sub5_409, List.forall_mem_cons.2 ⟨sub5_410, List.forall_mem_cons.2 ⟨sub5_411, List.forall_mem_cons.2 ⟨sub5_412, List.forall_mem_cons.2 ⟨sub5_413, List.forall_mem_cons.2 ⟨sub5_414, List.forall_mem_cons.2 ⟨sub5_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_416 : sub5 [0, -3, 9] = true := by decide +kernel
theorem sub5_417 : sub5 [0, -2, -8] = true := by decide +kernel
theorem sub5_418 : sub5 [0, -2, -7] = true := by decide +kernel
theorem sub5_419 : sub5 [0, -2, -6] = true := by decide +kernel
theorem sub5_420 : sub5 [0, -2, -5] = true := by decide +kernel
theorem sub5_421 : sub5 [0, -2, -4] = true := by decide +kernel
theorem sub5_422 : sub5 [0, -2, -3] = true := by decide +kernel
theorem sub5_423 : sub5 [0, -2, -2] = true := by decide +kernel
theorem sub5_424 : sub5 [0, -2, -1] = true := by decide +kernel
theorem sub5_425 : sub5 [0, -2, 0] = true := by decide +kernel
theorem sub5_426 : sub5 [0, -2, 1] = true := by decide +kernel
theorem sub5_427 : sub5 [0, -2, 2] = true := by decide +kernel
theorem sub5_428 : sub5 [0, -2, 3] = true := by decide +kernel
theorem sub5_429 : sub5 [0, -2, 4] = true := by decide +kernel
theorem sub5_430 : sub5 [0, -2, 5] = true := by decide +kernel
theorem sub5_431 : sub5 [0, -2, 6] = true := by decide +kernel
theorem sub5_432 : sub5 [0, -2, 7] = true := by decide +kernel
theorem sub5_433 : sub5 [0, -2, 8] = true := by decide +kernel
theorem sub5_434 : sub5 [0, -2, 9] = true := by decide +kernel
theorem sub5_435 : sub5 [0, -1, -9] = true := by decide +kernel
theorem sub5_436 : sub5 [0, -1, -8] = true := by decide +kernel
theorem sub5_437 : sub5 [0, -1, -7] = true := by decide +kernel
theorem sub5_438 : sub5 [0, -1, -6] = true := by decide +kernel
theorem sub5_439 : sub5 [0, -1, -5] = true := by decide +kernel
theorem sub5_440 : sub5 [0, -1, -4] = true := by decide +kernel
theorem sub5_441 : sub5 [0, -1, -3] = true := by decide +kernel
theorem sub5_442 : sub5 [0, -1, -2] = true := by decide +kernel
theorem sub5_443 : sub5 [0, -1, -1] = true := by decide +kernel
theorem sub5_444 : sub5 [0, -1, 0] = true := by decide +kernel
theorem sub5_445 : sub5 [0, -1, 1] = true := by decide +kernel
theorem sub5_446 : sub5 [0, -1, 2] = true := by decide +kernel
theorem sub5_447 : sub5 [0, -1, 3] = true := by decide +kernel
theorem sb5_13 : ∀ q ∈ blk5_13, sub5 q = true := by
  unfold blk5_13
  exact List.forall_mem_cons.2 ⟨sub5_416, List.forall_mem_cons.2 ⟨sub5_417, List.forall_mem_cons.2 ⟨sub5_418, List.forall_mem_cons.2 ⟨sub5_419, List.forall_mem_cons.2 ⟨sub5_420, List.forall_mem_cons.2 ⟨sub5_421, List.forall_mem_cons.2 ⟨sub5_422, List.forall_mem_cons.2 ⟨sub5_423, List.forall_mem_cons.2 ⟨sub5_424, List.forall_mem_cons.2 ⟨sub5_425, List.forall_mem_cons.2 ⟨sub5_426, List.forall_mem_cons.2 ⟨sub5_427, List.forall_mem_cons.2 ⟨sub5_428, List.forall_mem_cons.2 ⟨sub5_429, List.forall_mem_cons.2 ⟨sub5_430, List.forall_mem_cons.2 ⟨sub5_431, List.forall_mem_cons.2 ⟨sub5_432, List.forall_mem_cons.2 ⟨sub5_433, List.forall_mem_cons.2 ⟨sub5_434, List.forall_mem_cons.2 ⟨sub5_435, List.forall_mem_cons.2 ⟨sub5_436, List.forall_mem_cons.2 ⟨sub5_437, List.forall_mem_cons.2 ⟨sub5_438, List.forall_mem_cons.2 ⟨sub5_439, List.forall_mem_cons.2 ⟨sub5_440, List.forall_mem_cons.2 ⟨sub5_441, List.forall_mem_cons.2 ⟨sub5_442, List.forall_mem_cons.2 ⟨sub5_443, List.forall_mem_cons.2 ⟨sub5_444, List.forall_mem_cons.2 ⟨sub5_445, List.forall_mem_cons.2 ⟨sub5_446, List.forall_mem_cons.2 ⟨sub5_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
