import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub12_0 : sub12 [-5] = true := by decide +kernel
theorem sub12_1 : sub12 [-4, -3] = true := by decide +kernel
theorem sub12_2 : sub12 [-4, -2] = true := by decide +kernel
theorem sub12_3 : sub12 [-4, -1] = true := by decide +kernel
theorem sub12_4 : sub12 [-4, 0] = true := by decide +kernel
theorem sub12_5 : sub12 [-4, 1] = true := by decide +kernel
theorem sub12_6 : sub12 [-4, 2] = true := by decide +kernel
theorem sub12_7 : sub12 [-4, 3] = true := by decide +kernel
theorem sub12_8 : sub12 [-3, -4] = true := by decide +kernel
theorem sub12_9 : sub12 [-3, -3] = true := by decide +kernel
theorem sub12_10 : sub12 [-3, -2] = true := by decide +kernel
theorem sub12_11 : sub12 [-3, -1, -7] = true := by decide +kernel
theorem sub12_12 : sub12 [-3, -1, -6] = true := by decide +kernel
theorem sub12_13 : sub12 [-3, -1, -5] = true := by decide +kernel
theorem sub12_14 : sub12 [-3, -1, -4] = true := by decide +kernel
theorem sub12_15 : sub12 [-3, -1, -3] = true := by decide +kernel
theorem sub12_16 : sub12 [-3, -1, -2] = true := by decide +kernel
theorem sub12_17 : sub12 [-3, -1, -1] = true := by decide +kernel
theorem sub12_18 : sub12 [-3, -1, 0] = true := by decide +kernel
theorem sub12_19 : sub12 [-3, -1, 1] = true := by decide +kernel
theorem sub12_20 : sub12 [-3, -1, 2] = true := by decide +kernel
theorem sub12_21 : sub12 [-3, -1, 3] = true := by decide +kernel
theorem sub12_22 : sub12 [-3, -1, 4] = true := by decide +kernel
theorem sub12_23 : sub12 [-3, -1, 5] = true := by decide +kernel
theorem sub12_24 : sub12 [-3, 0, -8] = true := by decide +kernel
theorem sub12_25 : sub12 [-3, 0, -7] = true := by decide +kernel
theorem sub12_26 : sub12 [-3, 0, -6] = true := by decide +kernel
theorem sub12_27 : sub12 [-3, 0, -5] = true := by decide +kernel
theorem sub12_28 : sub12 [-3, 0, -4] = true := by decide +kernel
theorem sub12_29 : sub12 [-3, 0, -3] = true := by decide +kernel
theorem sub12_30 : sub12 [-3, 0, -2] = true := by decide +kernel
theorem sub12_31 : sub12 [-3, 0, -1] = true := by decide +kernel
theorem sb12_0 : ∀ q ∈ blk12_0, sub12 q = true := by
  unfold blk12_0
  exact List.forall_mem_cons.2 ⟨sub12_0, List.forall_mem_cons.2 ⟨sub12_1, List.forall_mem_cons.2 ⟨sub12_2, List.forall_mem_cons.2 ⟨sub12_3, List.forall_mem_cons.2 ⟨sub12_4, List.forall_mem_cons.2 ⟨sub12_5, List.forall_mem_cons.2 ⟨sub12_6, List.forall_mem_cons.2 ⟨sub12_7, List.forall_mem_cons.2 ⟨sub12_8, List.forall_mem_cons.2 ⟨sub12_9, List.forall_mem_cons.2 ⟨sub12_10, List.forall_mem_cons.2 ⟨sub12_11, List.forall_mem_cons.2 ⟨sub12_12, List.forall_mem_cons.2 ⟨sub12_13, List.forall_mem_cons.2 ⟨sub12_14, List.forall_mem_cons.2 ⟨sub12_15, List.forall_mem_cons.2 ⟨sub12_16, List.forall_mem_cons.2 ⟨sub12_17, List.forall_mem_cons.2 ⟨sub12_18, List.forall_mem_cons.2 ⟨sub12_19, List.forall_mem_cons.2 ⟨sub12_20, List.forall_mem_cons.2 ⟨sub12_21, List.forall_mem_cons.2 ⟨sub12_22, List.forall_mem_cons.2 ⟨sub12_23, List.forall_mem_cons.2 ⟨sub12_24, List.forall_mem_cons.2 ⟨sub12_25, List.forall_mem_cons.2 ⟨sub12_26, List.forall_mem_cons.2 ⟨sub12_27, List.forall_mem_cons.2 ⟨sub12_28, List.forall_mem_cons.2 ⟨sub12_29, List.forall_mem_cons.2 ⟨sub12_30, List.forall_mem_cons.2 ⟨sub12_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_32 : sub12 [-3, 0, 0] = true := by decide +kernel
theorem sub12_33 : sub12 [-3, 0, 1] = true := by decide +kernel
theorem sub12_34 : sub12 [-3, 0, 2] = true := by decide +kernel
theorem sub12_35 : sub12 [-3, 0, 3] = true := by decide +kernel
theorem sub12_36 : sub12 [-3, 0, 4] = true := by decide +kernel
theorem sub12_37 : sub12 [-3, 0, 5] = true := by decide +kernel
theorem sub12_38 : sub12 [-3, 1, -8] = true := by decide +kernel
theorem sub12_39 : sub12 [-3, 1, -7] = true := by decide +kernel
theorem sub12_40 : sub12 [-3, 1, -6] = true := by decide +kernel
theorem sub12_41 : sub12 [-3, 1, -5] = true := by decide +kernel
theorem sub12_42 : sub12 [-3, 1, -4] = true := by decide +kernel
theorem sub12_43 : sub12 [-3, 1, -3] = true := by decide +kernel
theorem sub12_44 : sub12 [-3, 1, -2] = true := by decide +kernel
theorem sub12_45 : sub12 [-3, 1, -1] = true := by decide +kernel
theorem sub12_46 : sub12 [-3, 1, 0] = true := by decide +kernel
theorem sub12_47 : sub12 [-3, 1, 1] = true := by decide +kernel
theorem sub12_48 : sub12 [-3, 1, 2] = true := by decide +kernel
theorem sub12_49 : sub12 [-3, 1, 3] = true := by decide +kernel
theorem sub12_50 : sub12 [-3, 1, 4] = true := by decide +kernel
theorem sub12_51 : sub12 [-3, 1, 5] = true := by decide +kernel
theorem sub12_52 : sub12 [-3, 2] = true := by decide +kernel
theorem sub12_53 : sub12 [-3, 3] = true := by decide +kernel
theorem sub12_54 : sub12 [-3, 4] = true := by decide +kernel
theorem sub12_55 : sub12 [-2, -5] = true := by decide +kernel
theorem sub12_56 : sub12 [-2, -4] = true := by decide +kernel
theorem sub12_57 : sub12 [-2, -3] = true := by decide +kernel
theorem sub12_58 : sub12 [-2, -2, -7] = true := by decide +kernel
theorem sub12_59 : sub12 [-2, -2, -6] = true := by decide +kernel
theorem sub12_60 : sub12 [-2, -2, -5] = true := by decide +kernel
theorem sub12_61 : sub12 [-2, -2, -4] = true := by decide +kernel
theorem sub12_62 : sub12 [-2, -2, -3] = true := by decide +kernel
theorem sub12_63 : sub12 [-2, -2, -2] = true := by decide +kernel
theorem sb12_1 : ∀ q ∈ blk12_1, sub12 q = true := by
  unfold blk12_1
  exact List.forall_mem_cons.2 ⟨sub12_32, List.forall_mem_cons.2 ⟨sub12_33, List.forall_mem_cons.2 ⟨sub12_34, List.forall_mem_cons.2 ⟨sub12_35, List.forall_mem_cons.2 ⟨sub12_36, List.forall_mem_cons.2 ⟨sub12_37, List.forall_mem_cons.2 ⟨sub12_38, List.forall_mem_cons.2 ⟨sub12_39, List.forall_mem_cons.2 ⟨sub12_40, List.forall_mem_cons.2 ⟨sub12_41, List.forall_mem_cons.2 ⟨sub12_42, List.forall_mem_cons.2 ⟨sub12_43, List.forall_mem_cons.2 ⟨sub12_44, List.forall_mem_cons.2 ⟨sub12_45, List.forall_mem_cons.2 ⟨sub12_46, List.forall_mem_cons.2 ⟨sub12_47, List.forall_mem_cons.2 ⟨sub12_48, List.forall_mem_cons.2 ⟨sub12_49, List.forall_mem_cons.2 ⟨sub12_50, List.forall_mem_cons.2 ⟨sub12_51, List.forall_mem_cons.2 ⟨sub12_52, List.forall_mem_cons.2 ⟨sub12_53, List.forall_mem_cons.2 ⟨sub12_54, List.forall_mem_cons.2 ⟨sub12_55, List.forall_mem_cons.2 ⟨sub12_56, List.forall_mem_cons.2 ⟨sub12_57, List.forall_mem_cons.2 ⟨sub12_58, List.forall_mem_cons.2 ⟨sub12_59, List.forall_mem_cons.2 ⟨sub12_60, List.forall_mem_cons.2 ⟨sub12_61, List.forall_mem_cons.2 ⟨sub12_62, List.forall_mem_cons.2 ⟨sub12_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_64 : sub12 [-2, -2, -1] = true := by decide +kernel
theorem sub12_65 : sub12 [-2, -2, 0] = true := by decide +kernel
theorem sub12_66 : sub12 [-2, -2, 1] = true := by decide +kernel
theorem sub12_67 : sub12 [-2, -2, 2] = true := by decide +kernel
theorem sub12_68 : sub12 [-2, -2, 3] = true := by decide +kernel
theorem sub12_69 : sub12 [-2, -2, 4] = true := by decide +kernel
theorem sub12_70 : sub12 [-2, -2, 5] = true := by decide +kernel
theorem sub12_71 : sub12 [-2, -2, 6] = true := by decide +kernel
theorem sub12_72 : sub12 [-2, -1, -8] = true := by decide +kernel
theorem sub12_73 : sub12 [-2, -1, -7] = true := by decide +kernel
theorem sub12_74 : sub12 [-2, -1, -6] = true := by decide +kernel
theorem sub12_75 : sub12 [-2, -1, -5] = true := by decide +kernel
theorem sub12_76 : sub12 [-2, -1, -4] = true := by decide +kernel
theorem sub12_77 : sub12 [-2, -1, -3] = true := by decide +kernel
theorem sub12_78 : sub12 [-2, -1, -2] = true := by decide +kernel
theorem sub12_79 : sub12 [-2, -1, -1] = true := by decide +kernel
theorem sub12_80 : sub12 [-2, -1, 0] = true := by decide +kernel
theorem sub12_81 : sub12 [-2, -1, 1] = true := by decide +kernel
theorem sub12_82 : sub12 [-2, -1, 2] = true := by decide +kernel
theorem sub12_83 : sub12 [-2, -1, 3] = true := by decide +kernel
theorem sub12_84 : sub12 [-2, -1, 4] = true := by decide +kernel
theorem sub12_85 : sub12 [-2, -1, 5] = true := by decide +kernel
theorem sub12_86 : sub12 [-2, -1, 6] = true := by decide +kernel
theorem sub12_87 : sub12 [-2, 0, -8] = true := by decide +kernel
theorem sub12_88 : sub12 [-2, 0, -7] = true := by decide +kernel
theorem sub12_89 : sub12 [-2, 0, -6] = true := by decide +kernel
theorem sub12_90 : sub12 [-2, 0, -5] = true := by decide +kernel
theorem sub12_91 : sub12 [-2, 0, -4] = true := by decide +kernel
theorem sub12_92 : sub12 [-2, 0, -3] = true := by decide +kernel
theorem sub12_93 : sub12 [-2, 0, -2] = true := by decide +kernel
theorem sub12_94 : sub12 [-2, 0, -1] = true := by decide +kernel
theorem sub12_95 : sub12 [-2, 0, 0] = true := by decide +kernel
theorem sb12_2 : ∀ q ∈ blk12_2, sub12 q = true := by
  unfold blk12_2
  exact List.forall_mem_cons.2 ⟨sub12_64, List.forall_mem_cons.2 ⟨sub12_65, List.forall_mem_cons.2 ⟨sub12_66, List.forall_mem_cons.2 ⟨sub12_67, List.forall_mem_cons.2 ⟨sub12_68, List.forall_mem_cons.2 ⟨sub12_69, List.forall_mem_cons.2 ⟨sub12_70, List.forall_mem_cons.2 ⟨sub12_71, List.forall_mem_cons.2 ⟨sub12_72, List.forall_mem_cons.2 ⟨sub12_73, List.forall_mem_cons.2 ⟨sub12_74, List.forall_mem_cons.2 ⟨sub12_75, List.forall_mem_cons.2 ⟨sub12_76, List.forall_mem_cons.2 ⟨sub12_77, List.forall_mem_cons.2 ⟨sub12_78, List.forall_mem_cons.2 ⟨sub12_79, List.forall_mem_cons.2 ⟨sub12_80, List.forall_mem_cons.2 ⟨sub12_81, List.forall_mem_cons.2 ⟨sub12_82, List.forall_mem_cons.2 ⟨sub12_83, List.forall_mem_cons.2 ⟨sub12_84, List.forall_mem_cons.2 ⟨sub12_85, List.forall_mem_cons.2 ⟨sub12_86, List.forall_mem_cons.2 ⟨sub12_87, List.forall_mem_cons.2 ⟨sub12_88, List.forall_mem_cons.2 ⟨sub12_89, List.forall_mem_cons.2 ⟨sub12_90, List.forall_mem_cons.2 ⟨sub12_91, List.forall_mem_cons.2 ⟨sub12_92, List.forall_mem_cons.2 ⟨sub12_93, List.forall_mem_cons.2 ⟨sub12_94, List.forall_mem_cons.2 ⟨sub12_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_96 : sub12 [-2, 0, 1] = true := by decide +kernel
theorem sub12_97 : sub12 [-2, 0, 2] = true := by decide +kernel
theorem sub12_98 : sub12 [-2, 0, 3] = true := by decide +kernel
theorem sub12_99 : sub12 [-2, 0, 4] = true := by decide +kernel
theorem sub12_100 : sub12 [-2, 0, 5] = true := by decide +kernel
theorem sub12_101 : sub12 [-2, 0, 6] = true := by decide +kernel
theorem sub12_102 : sub12 [-2, 1, -8] = true := by decide +kernel
theorem sub12_103 : sub12 [-2, 1, -7] = true := by decide +kernel
theorem sub12_104 : sub12 [-2, 1, -6] = true := by decide +kernel
theorem sub12_105 : sub12 [-2, 1, -5] = true := by decide +kernel
theorem sub12_106 : sub12 [-2, 1, -4] = true := by decide +kernel
theorem sub12_107 : sub12 [-2, 1, -3] = true := by decide +kernel
theorem sub12_108 : sub12 [-2, 1, -2] = true := by decide +kernel
theorem sub12_109 : sub12 [-2, 1, -1] = true := by decide +kernel
theorem sub12_110 : sub12 [-2, 1, 0] = true := by decide +kernel
theorem sub12_111 : sub12 [-2, 1, 1] = true := by decide +kernel
theorem sub12_112 : sub12 [-2, 1, 2] = true := by decide +kernel
theorem sub12_113 : sub12 [-2, 1, 3] = true := by decide +kernel
theorem sub12_114 : sub12 [-2, 1, 4] = true := by decide +kernel
theorem sub12_115 : sub12 [-2, 1, 5] = true := by decide +kernel
theorem sub12_116 : sub12 [-2, 1, 6] = true := by decide +kernel
theorem sub12_117 : sub12 [-2, 2, -8] = true := by decide +kernel
theorem sub12_118 : sub12 [-2, 2, -7] = true := by decide +kernel
theorem sub12_119 : sub12 [-2, 2, -6] = true := by decide +kernel
theorem sub12_120 : sub12 [-2, 2, -5] = true := by decide +kernel
theorem sub12_121 : sub12 [-2, 2, -4] = true := by decide +kernel
theorem sub12_122 : sub12 [-2, 2, -3] = true := by decide +kernel
theorem sub12_123 : sub12 [-2, 2, -2] = true := by decide +kernel
theorem sub12_124 : sub12 [-2, 2, -1] = true := by decide +kernel
theorem sub12_125 : sub12 [-2, 2, 0] = true := by decide +kernel
theorem sub12_126 : sub12 [-2, 2, 1] = true := by decide +kernel
theorem sub12_127 : sub12 [-2, 2, 2] = true := by decide +kernel
theorem sb12_3 : ∀ q ∈ blk12_3, sub12 q = true := by
  unfold blk12_3
  exact List.forall_mem_cons.2 ⟨sub12_96, List.forall_mem_cons.2 ⟨sub12_97, List.forall_mem_cons.2 ⟨sub12_98, List.forall_mem_cons.2 ⟨sub12_99, List.forall_mem_cons.2 ⟨sub12_100, List.forall_mem_cons.2 ⟨sub12_101, List.forall_mem_cons.2 ⟨sub12_102, List.forall_mem_cons.2 ⟨sub12_103, List.forall_mem_cons.2 ⟨sub12_104, List.forall_mem_cons.2 ⟨sub12_105, List.forall_mem_cons.2 ⟨sub12_106, List.forall_mem_cons.2 ⟨sub12_107, List.forall_mem_cons.2 ⟨sub12_108, List.forall_mem_cons.2 ⟨sub12_109, List.forall_mem_cons.2 ⟨sub12_110, List.forall_mem_cons.2 ⟨sub12_111, List.forall_mem_cons.2 ⟨sub12_112, List.forall_mem_cons.2 ⟨sub12_113, List.forall_mem_cons.2 ⟨sub12_114, List.forall_mem_cons.2 ⟨sub12_115, List.forall_mem_cons.2 ⟨sub12_116, List.forall_mem_cons.2 ⟨sub12_117, List.forall_mem_cons.2 ⟨sub12_118, List.forall_mem_cons.2 ⟨sub12_119, List.forall_mem_cons.2 ⟨sub12_120, List.forall_mem_cons.2 ⟨sub12_121, List.forall_mem_cons.2 ⟨sub12_122, List.forall_mem_cons.2 ⟨sub12_123, List.forall_mem_cons.2 ⟨sub12_124, List.forall_mem_cons.2 ⟨sub12_125, List.forall_mem_cons.2 ⟨sub12_126, List.forall_mem_cons.2 ⟨sub12_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_128 : sub12 [-2, 2, 3] = true := by decide +kernel
theorem sub12_129 : sub12 [-2, 2, 4] = true := by decide +kernel
theorem sub12_130 : sub12 [-2, 2, 5] = true := by decide +kernel
theorem sub12_131 : sub12 [-2, 3] = true := by decide +kernel
theorem sub12_132 : sub12 [-2, 4] = true := by decide +kernel
theorem sub12_133 : sub12 [-1, -5] = true := by decide +kernel
theorem sub12_134 : sub12 [-1, -4] = true := by decide +kernel
theorem sub12_135 : sub12 [-1, -3, -6] = true := by decide +kernel
theorem sub12_136 : sub12 [-1, -3, -5] = true := by decide +kernel
theorem sub12_137 : sub12 [-1, -3, -4] = true := by decide +kernel
theorem sub12_138 : sub12 [-1, -3, -3] = true := by decide +kernel
theorem sub12_139 : sub12 [-1, -3, -2] = true := by decide +kernel
theorem sub12_140 : sub12 [-1, -3, -1] = true := by decide +kernel
theorem sub12_141 : sub12 [-1, -3, 0] = true := by decide +kernel
theorem sub12_142 : sub12 [-1, -3, 1] = true := by decide +kernel
theorem sub12_143 : sub12 [-1, -3, 2] = true := by decide +kernel
theorem sub12_144 : sub12 [-1, -3, 3] = true := by decide +kernel
theorem sub12_145 : sub12 [-1, -3, 4] = true := by decide +kernel
theorem sub12_146 : sub12 [-1, -3, 5] = true := by decide +kernel
theorem sub12_147 : sub12 [-1, -3, 6] = true := by decide +kernel
theorem sub12_148 : sub12 [-1, -2, -8] = true := by decide +kernel
theorem sub12_149 : sub12 [-1, -2, -7] = true := by decide +kernel
theorem sub12_150 : sub12 [-1, -2, -6] = true := by decide +kernel
theorem sub12_151 : sub12 [-1, -2, -5] = true := by decide +kernel
theorem sub12_152 : sub12 [-1, -2, -4] = true := by decide +kernel
theorem sub12_153 : sub12 [-1, -2, -3] = true := by decide +kernel
theorem sub12_154 : sub12 [-1, -2, -2] = true := by decide +kernel
theorem sub12_155 : sub12 [-1, -2, -1] = true := by decide +kernel
theorem sub12_156 : sub12 [-1, -2, 0] = true := by decide +kernel
theorem sub12_157 : sub12 [-1, -2, 1] = true := by decide +kernel
theorem sub12_158 : sub12 [-1, -2, 2] = true := by decide +kernel
theorem sub12_159 : sub12 [-1, -2, 3] = true := by decide +kernel
theorem sb12_4 : ∀ q ∈ blk12_4, sub12 q = true := by
  unfold blk12_4
  exact List.forall_mem_cons.2 ⟨sub12_128, List.forall_mem_cons.2 ⟨sub12_129, List.forall_mem_cons.2 ⟨sub12_130, List.forall_mem_cons.2 ⟨sub12_131, List.forall_mem_cons.2 ⟨sub12_132, List.forall_mem_cons.2 ⟨sub12_133, List.forall_mem_cons.2 ⟨sub12_134, List.forall_mem_cons.2 ⟨sub12_135, List.forall_mem_cons.2 ⟨sub12_136, List.forall_mem_cons.2 ⟨sub12_137, List.forall_mem_cons.2 ⟨sub12_138, List.forall_mem_cons.2 ⟨sub12_139, List.forall_mem_cons.2 ⟨sub12_140, List.forall_mem_cons.2 ⟨sub12_141, List.forall_mem_cons.2 ⟨sub12_142, List.forall_mem_cons.2 ⟨sub12_143, List.forall_mem_cons.2 ⟨sub12_144, List.forall_mem_cons.2 ⟨sub12_145, List.forall_mem_cons.2 ⟨sub12_146, List.forall_mem_cons.2 ⟨sub12_147, List.forall_mem_cons.2 ⟨sub12_148, List.forall_mem_cons.2 ⟨sub12_149, List.forall_mem_cons.2 ⟨sub12_150, List.forall_mem_cons.2 ⟨sub12_151, List.forall_mem_cons.2 ⟨sub12_152, List.forall_mem_cons.2 ⟨sub12_153, List.forall_mem_cons.2 ⟨sub12_154, List.forall_mem_cons.2 ⟨sub12_155, List.forall_mem_cons.2 ⟨sub12_156, List.forall_mem_cons.2 ⟨sub12_157, List.forall_mem_cons.2 ⟨sub12_158, List.forall_mem_cons.2 ⟨sub12_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_160 : sub12 [-1, -2, 4] = true := by decide +kernel
theorem sub12_161 : sub12 [-1, -2, 5] = true := by decide +kernel
theorem sub12_162 : sub12 [-1, -2, 6] = true := by decide +kernel
theorem sub12_163 : sub12 [-1, -2, 7] = true := by decide +kernel
theorem sub12_164 : sub12 [-1, -1, -8] = true := by decide +kernel
theorem sub12_165 : sub12 [-1, -1, -7] = true := by decide +kernel
theorem sub12_166 : sub12 [-1, -1, -6] = true := by decide +kernel
theorem sub12_167 : sub12 [-1, -1, -5] = true := by decide +kernel
theorem sub12_168 : sub12 [-1, -1, -4] = true := by decide +kernel
theorem sub12_169 : sub12 [-1, -1, -3] = true := by decide +kernel
theorem sub12_170 : sub12 [-1, -1, -2] = true := by decide +kernel
theorem sub12_171 : sub12 [-1, -1, -1] = true := by decide +kernel
theorem sub12_172 : sub12 [-1, -1, 0] = true := by decide +kernel
theorem sub12_173 : sub12 [-1, -1, 1] = true := by decide +kernel
theorem sub12_174 : sub12 [-1, -1, 2] = true := by decide +kernel
theorem sub12_175 : sub12 [-1, -1, 3] = true := by decide +kernel
theorem sub12_176 : sub12 [-1, -1, 4] = true := by decide +kernel
theorem sub12_177 : sub12 [-1, -1, 5] = true := by decide +kernel
theorem sub12_178 : sub12 [-1, -1, 6] = true := by decide +kernel
theorem sub12_179 : sub12 [-1, -1, 7] = true := by decide +kernel
theorem sub12_180 : sub12 [-1, 0, -9] = true := by decide +kernel
theorem sub12_181 : sub12 [-1, 0, -8] = true := by decide +kernel
theorem sub12_182 : sub12 [-1, 0, -7] = true := by decide +kernel
theorem sub12_183 : sub12 [-1, 0, -6] = true := by decide +kernel
theorem sub12_184 : sub12 [-1, 0, -5] = true := by decide +kernel
theorem sub12_185 : sub12 [-1, 0, -4] = true := by decide +kernel
theorem sub12_186 : sub12 [-1, 0, -3] = true := by decide +kernel
theorem sub12_187 : sub12 [-1, 0, -2] = true := by decide +kernel
theorem sub12_188 : sub12 [-1, 0, -1] = true := by decide +kernel
theorem sub12_189 : sub12 [-1, 0, 0] = true := by decide +kernel
theorem sub12_190 : sub12 [-1, 0, 1] = true := by decide +kernel
theorem sub12_191 : sub12 [-1, 0, 2] = true := by decide +kernel
theorem sb12_5 : ∀ q ∈ blk12_5, sub12 q = true := by
  unfold blk12_5
  exact List.forall_mem_cons.2 ⟨sub12_160, List.forall_mem_cons.2 ⟨sub12_161, List.forall_mem_cons.2 ⟨sub12_162, List.forall_mem_cons.2 ⟨sub12_163, List.forall_mem_cons.2 ⟨sub12_164, List.forall_mem_cons.2 ⟨sub12_165, List.forall_mem_cons.2 ⟨sub12_166, List.forall_mem_cons.2 ⟨sub12_167, List.forall_mem_cons.2 ⟨sub12_168, List.forall_mem_cons.2 ⟨sub12_169, List.forall_mem_cons.2 ⟨sub12_170, List.forall_mem_cons.2 ⟨sub12_171, List.forall_mem_cons.2 ⟨sub12_172, List.forall_mem_cons.2 ⟨sub12_173, List.forall_mem_cons.2 ⟨sub12_174, List.forall_mem_cons.2 ⟨sub12_175, List.forall_mem_cons.2 ⟨sub12_176, List.forall_mem_cons.2 ⟨sub12_177, List.forall_mem_cons.2 ⟨sub12_178, List.forall_mem_cons.2 ⟨sub12_179, List.forall_mem_cons.2 ⟨sub12_180, List.forall_mem_cons.2 ⟨sub12_181, List.forall_mem_cons.2 ⟨sub12_182, List.forall_mem_cons.2 ⟨sub12_183, List.forall_mem_cons.2 ⟨sub12_184, List.forall_mem_cons.2 ⟨sub12_185, List.forall_mem_cons.2 ⟨sub12_186, List.forall_mem_cons.2 ⟨sub12_187, List.forall_mem_cons.2 ⟨sub12_188, List.forall_mem_cons.2 ⟨sub12_189, List.forall_mem_cons.2 ⟨sub12_190, List.forall_mem_cons.2 ⟨sub12_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_192 : sub12 [-1, 0, 3] = true := by decide +kernel
theorem sub12_193 : sub12 [-1, 0, 4] = true := by decide +kernel
theorem sub12_194 : sub12 [-1, 0, 5] = true := by decide +kernel
theorem sub12_195 : sub12 [-1, 0, 6] = true := by decide +kernel
theorem sub12_196 : sub12 [-1, 0, 7] = true := by decide +kernel
theorem sub12_197 : sub12 [-1, 1, -9] = true := by decide +kernel
theorem sub12_198 : sub12 [-1, 1, -8] = true := by decide +kernel
theorem sub12_199 : sub12 [-1, 1, -7] = true := by decide +kernel
theorem sub12_200 : sub12 [-1, 1, -6] = true := by decide +kernel
theorem sub12_201 : sub12 [-1, 1, -5] = true := by decide +kernel
theorem sub12_202 : sub12 [-1, 1, -4] = true := by decide +kernel
theorem sub12_203 : sub12 [-1, 1, -3] = true := by decide +kernel
theorem sub12_204 : sub12 [-1, 1, -2] = true := by decide +kernel
theorem sub12_205 : sub12 [-1, 1, -1] = true := by decide +kernel
theorem sub12_206 : sub12 [-1, 1, 0] = true := by decide +kernel
theorem sub12_207 : sub12 [-1, 1, 1] = true := by decide +kernel
theorem sub12_208 : sub12 [-1, 1, 2] = true := by decide +kernel
theorem sub12_209 : sub12 [-1, 1, 3] = true := by decide +kernel
theorem sub12_210 : sub12 [-1, 1, 4] = true := by decide +kernel
theorem sub12_211 : sub12 [-1, 1, 5] = true := by decide +kernel
theorem sub12_212 : sub12 [-1, 1, 6] = true := by decide +kernel
theorem sub12_213 : sub12 [-1, 1, 7] = true := by decide +kernel
theorem sub12_214 : sub12 [-1, 2, -8] = true := by decide +kernel
theorem sub12_215 : sub12 [-1, 2, -7] = true := by decide +kernel
theorem sub12_216 : sub12 [-1, 2, -6] = true := by decide +kernel
theorem sub12_217 : sub12 [-1, 2, -5] = true := by decide +kernel
theorem sub12_218 : sub12 [-1, 2, -4] = true := by decide +kernel
theorem sub12_219 : sub12 [-1, 2, -3] = true := by decide +kernel
theorem sub12_220 : sub12 [-1, 2, -2] = true := by decide +kernel
theorem sub12_221 : sub12 [-1, 2, -1] = true := by decide +kernel
theorem sub12_222 : sub12 [-1, 2, 0] = true := by decide +kernel
theorem sub12_223 : sub12 [-1, 2, 1] = true := by decide +kernel
theorem sb12_6 : ∀ q ∈ blk12_6, sub12 q = true := by
  unfold blk12_6
  exact List.forall_mem_cons.2 ⟨sub12_192, List.forall_mem_cons.2 ⟨sub12_193, List.forall_mem_cons.2 ⟨sub12_194, List.forall_mem_cons.2 ⟨sub12_195, List.forall_mem_cons.2 ⟨sub12_196, List.forall_mem_cons.2 ⟨sub12_197, List.forall_mem_cons.2 ⟨sub12_198, List.forall_mem_cons.2 ⟨sub12_199, List.forall_mem_cons.2 ⟨sub12_200, List.forall_mem_cons.2 ⟨sub12_201, List.forall_mem_cons.2 ⟨sub12_202, List.forall_mem_cons.2 ⟨sub12_203, List.forall_mem_cons.2 ⟨sub12_204, List.forall_mem_cons.2 ⟨sub12_205, List.forall_mem_cons.2 ⟨sub12_206, List.forall_mem_cons.2 ⟨sub12_207, List.forall_mem_cons.2 ⟨sub12_208, List.forall_mem_cons.2 ⟨sub12_209, List.forall_mem_cons.2 ⟨sub12_210, List.forall_mem_cons.2 ⟨sub12_211, List.forall_mem_cons.2 ⟨sub12_212, List.forall_mem_cons.2 ⟨sub12_213, List.forall_mem_cons.2 ⟨sub12_214, List.forall_mem_cons.2 ⟨sub12_215, List.forall_mem_cons.2 ⟨sub12_216, List.forall_mem_cons.2 ⟨sub12_217, List.forall_mem_cons.2 ⟨sub12_218, List.forall_mem_cons.2 ⟨sub12_219, List.forall_mem_cons.2 ⟨sub12_220, List.forall_mem_cons.2 ⟨sub12_221, List.forall_mem_cons.2 ⟨sub12_222, List.forall_mem_cons.2 ⟨sub12_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_224 : sub12 [-1, 2, 2] = true := by decide +kernel
theorem sub12_225 : sub12 [-1, 2, 3] = true := by decide +kernel
theorem sub12_226 : sub12 [-1, 2, 4] = true := by decide +kernel
theorem sub12_227 : sub12 [-1, 2, 5] = true := by decide +kernel
theorem sub12_228 : sub12 [-1, 2, 6] = true := by decide +kernel
theorem sub12_229 : sub12 [-1, 3, -8] = true := by decide +kernel
theorem sub12_230 : sub12 [-1, 3, -7] = true := by decide +kernel
theorem sub12_231 : sub12 [-1, 3, -6] = true := by decide +kernel
theorem sub12_232 : sub12 [-1, 3, -5] = true := by decide +kernel
theorem sub12_233 : sub12 [-1, 3, -4] = true := by decide +kernel
theorem sub12_234 : sub12 [-1, 3, -3] = true := by decide +kernel
theorem sub12_235 : sub12 [-1, 3, -2] = true := by decide +kernel
theorem sub12_236 : sub12 [-1, 3, -1] = true := by decide +kernel
theorem sub12_237 : sub12 [-1, 3, 0] = true := by decide +kernel
theorem sub12_238 : sub12 [-1, 3, 1] = true := by decide +kernel
theorem sub12_239 : sub12 [-1, 3, 2] = true := by decide +kernel
theorem sub12_240 : sub12 [-1, 3, 3] = true := by decide +kernel
theorem sub12_241 : sub12 [-1, 3, 4] = true := by decide +kernel
theorem sub12_242 : sub12 [-1, 3, 5] = true := by decide +kernel
theorem sub12_243 : sub12 [-1, 4] = true := by decide +kernel
theorem sub12_244 : sub12 [0, -5] = true := by decide +kernel
theorem sub12_245 : sub12 [0, -4] = true := by decide +kernel
theorem sub12_246 : sub12 [0, -3, -6] = true := by decide +kernel
theorem sub12_247 : sub12 [0, -3, -5] = true := by decide +kernel
theorem sub12_248 : sub12 [0, -3, -4] = true := by decide +kernel
theorem sub12_249 : sub12 [0, -3, -3] = true := by decide +kernel
theorem sub12_250 : sub12 [0, -3, -2] = true := by decide +kernel
theorem sub12_251 : sub12 [0, -3, -1] = true := by decide +kernel
theorem sub12_252 : sub12 [0, -3, 0] = true := by decide +kernel
theorem sub12_253 : sub12 [0, -3, 1] = true := by decide +kernel
theorem sub12_254 : sub12 [0, -3, 2] = true := by decide +kernel
theorem sub12_255 : sub12 [0, -3, 3] = true := by decide +kernel
theorem sb12_7 : ∀ q ∈ blk12_7, sub12 q = true := by
  unfold blk12_7
  exact List.forall_mem_cons.2 ⟨sub12_224, List.forall_mem_cons.2 ⟨sub12_225, List.forall_mem_cons.2 ⟨sub12_226, List.forall_mem_cons.2 ⟨sub12_227, List.forall_mem_cons.2 ⟨sub12_228, List.forall_mem_cons.2 ⟨sub12_229, List.forall_mem_cons.2 ⟨sub12_230, List.forall_mem_cons.2 ⟨sub12_231, List.forall_mem_cons.2 ⟨sub12_232, List.forall_mem_cons.2 ⟨sub12_233, List.forall_mem_cons.2 ⟨sub12_234, List.forall_mem_cons.2 ⟨sub12_235, List.forall_mem_cons.2 ⟨sub12_236, List.forall_mem_cons.2 ⟨sub12_237, List.forall_mem_cons.2 ⟨sub12_238, List.forall_mem_cons.2 ⟨sub12_239, List.forall_mem_cons.2 ⟨sub12_240, List.forall_mem_cons.2 ⟨sub12_241, List.forall_mem_cons.2 ⟨sub12_242, List.forall_mem_cons.2 ⟨sub12_243, List.forall_mem_cons.2 ⟨sub12_244, List.forall_mem_cons.2 ⟨sub12_245, List.forall_mem_cons.2 ⟨sub12_246, List.forall_mem_cons.2 ⟨sub12_247, List.forall_mem_cons.2 ⟨sub12_248, List.forall_mem_cons.2 ⟨sub12_249, List.forall_mem_cons.2 ⟨sub12_250, List.forall_mem_cons.2 ⟨sub12_251, List.forall_mem_cons.2 ⟨sub12_252, List.forall_mem_cons.2 ⟨sub12_253, List.forall_mem_cons.2 ⟨sub12_254, List.forall_mem_cons.2 ⟨sub12_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_256 : sub12 [0, -3, 4] = true := by decide +kernel
theorem sub12_257 : sub12 [0, -3, 5] = true := by decide +kernel
theorem sub12_258 : sub12 [0, -3, 6] = true := by decide +kernel
theorem sub12_259 : sub12 [0, -2, -7] = true := by decide +kernel
theorem sub12_260 : sub12 [0, -2, -6] = true := by decide +kernel
theorem sub12_261 : sub12 [0, -2, -5] = true := by decide +kernel
theorem sub12_262 : sub12 [0, -2, -4] = true := by decide +kernel
theorem sub12_263 : sub12 [0, -2, -3] = true := by decide +kernel
theorem sub12_264 : sub12 [0, -2, -2] = true := by decide +kernel
theorem sub12_265 : sub12 [0, -2, -1] = true := by decide +kernel
theorem sub12_266 : sub12 [0, -2, 0] = true := by decide +kernel
theorem sub12_267 : sub12 [0, -2, 1] = true := by decide +kernel
theorem sub12_268 : sub12 [0, -2, 2] = true := by decide +kernel
theorem sub12_269 : sub12 [0, -2, 3] = true := by decide +kernel
theorem sub12_270 : sub12 [0, -2, 4] = true := by decide +kernel
theorem sub12_271 : sub12 [0, -2, 5] = true := by decide +kernel
theorem sub12_272 : sub12 [0, -2, 6] = true := by decide +kernel
theorem sub12_273 : sub12 [0, -2, 7] = true := by decide +kernel
theorem sub12_274 : sub12 [0, -1, -8] = true := by decide +kernel
theorem sub12_275 : sub12 [0, -1, -7] = true := by decide +kernel
theorem sub12_276 : sub12 [0, -1, -6] = true := by decide +kernel
theorem sub12_277 : sub12 [0, -1, -5] = true := by decide +kernel
theorem sub12_278 : sub12 [0, -1, -4] = true := by decide +kernel
theorem sub12_279 : sub12 [0, -1, -3] = true := by decide +kernel
theorem sub12_280 : sub12 [0, -1, -2] = true := by decide +kernel
theorem sub12_281 : sub12 [0, -1, -1] = true := by decide +kernel
theorem sub12_282 : sub12 [0, -1, 0] = true := by decide +kernel
theorem sub12_283 : sub12 [0, -1, 1] = true := by decide +kernel
theorem sub12_284 : sub12 [0, -1, 2] = true := by decide +kernel
theorem sub12_285 : sub12 [0, -1, 3] = true := by decide +kernel
theorem sub12_286 : sub12 [0, -1, 4] = true := by decide +kernel
theorem sub12_287 : sub12 [0, -1, 5] = true := by decide +kernel
theorem sb12_8 : ∀ q ∈ blk12_8, sub12 q = true := by
  unfold blk12_8
  exact List.forall_mem_cons.2 ⟨sub12_256, List.forall_mem_cons.2 ⟨sub12_257, List.forall_mem_cons.2 ⟨sub12_258, List.forall_mem_cons.2 ⟨sub12_259, List.forall_mem_cons.2 ⟨sub12_260, List.forall_mem_cons.2 ⟨sub12_261, List.forall_mem_cons.2 ⟨sub12_262, List.forall_mem_cons.2 ⟨sub12_263, List.forall_mem_cons.2 ⟨sub12_264, List.forall_mem_cons.2 ⟨sub12_265, List.forall_mem_cons.2 ⟨sub12_266, List.forall_mem_cons.2 ⟨sub12_267, List.forall_mem_cons.2 ⟨sub12_268, List.forall_mem_cons.2 ⟨sub12_269, List.forall_mem_cons.2 ⟨sub12_270, List.forall_mem_cons.2 ⟨sub12_271, List.forall_mem_cons.2 ⟨sub12_272, List.forall_mem_cons.2 ⟨sub12_273, List.forall_mem_cons.2 ⟨sub12_274, List.forall_mem_cons.2 ⟨sub12_275, List.forall_mem_cons.2 ⟨sub12_276, List.forall_mem_cons.2 ⟨sub12_277, List.forall_mem_cons.2 ⟨sub12_278, List.forall_mem_cons.2 ⟨sub12_279, List.forall_mem_cons.2 ⟨sub12_280, List.forall_mem_cons.2 ⟨sub12_281, List.forall_mem_cons.2 ⟨sub12_282, List.forall_mem_cons.2 ⟨sub12_283, List.forall_mem_cons.2 ⟨sub12_284, List.forall_mem_cons.2 ⟨sub12_285, List.forall_mem_cons.2 ⟨sub12_286, List.forall_mem_cons.2 ⟨sub12_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_288 : sub12 [0, -1, 6] = true := by decide +kernel
theorem sub12_289 : sub12 [0, -1, 7] = true := by decide +kernel
theorem sub12_290 : sub12 [0, -1, 8] = true := by decide +kernel
theorem sub12_291 : sub12 [0, 0, -8] = true := by decide +kernel
theorem sub12_292 : sub12 [0, 0, -7] = true := by decide +kernel
theorem sub12_293 : sub12 [0, 0, -6] = true := by decide +kernel
theorem sub12_294 : sub12 [0, 0, -5] = true := by decide +kernel
theorem sub12_295 : sub12 [0, 0, -4] = true := by decide +kernel
theorem sub12_296 : sub12 [0, 0, -3] = true := by decide +kernel
theorem sub12_297 : sub12 [0, 0, -2] = true := by decide +kernel
theorem sub12_298 : sub12 [0, 0, -1] = true := by decide +kernel
theorem sub12_299 : sub12 [0, 0, 0] = true := by decide +kernel
theorem sub12_300 : sub12 [0, 0, 1] = true := by decide +kernel
theorem sub12_301 : sub12 [0, 0, 2] = true := by decide +kernel
theorem sub12_302 : sub12 [0, 0, 3] = true := by decide +kernel
theorem sub12_303 : sub12 [0, 0, 4] = true := by decide +kernel
theorem sub12_304 : sub12 [0, 0, 5] = true := by decide +kernel
theorem sub12_305 : sub12 [0, 0, 6] = true := by decide +kernel
theorem sub12_306 : sub12 [0, 0, 7] = true := by decide +kernel
theorem sub12_307 : sub12 [0, 1, -9] = true := by decide +kernel
theorem sub12_308 : sub12 [0, 1, -8] = true := by decide +kernel
theorem sub12_309 : sub12 [0, 1, -7] = true := by decide +kernel
theorem sub12_310 : sub12 [0, 1, -6] = true := by decide +kernel
theorem sub12_311 : sub12 [0, 1, -5] = true := by decide +kernel
theorem sub12_312 : sub12 [0, 1, -4] = true := by decide +kernel
theorem sub12_313 : sub12 [0, 1, -3] = true := by decide +kernel
theorem sub12_314 : sub12 [0, 1, -2] = true := by decide +kernel
theorem sub12_315 : sub12 [0, 1, -1] = true := by decide +kernel
theorem sub12_316 : sub12 [0, 1, 0] = true := by decide +kernel
theorem sub12_317 : sub12 [0, 1, 1] = true := by decide +kernel
theorem sub12_318 : sub12 [0, 1, 2] = true := by decide +kernel
theorem sub12_319 : sub12 [0, 1, 3] = true := by decide +kernel
theorem sb12_9 : ∀ q ∈ blk12_9, sub12 q = true := by
  unfold blk12_9
  exact List.forall_mem_cons.2 ⟨sub12_288, List.forall_mem_cons.2 ⟨sub12_289, List.forall_mem_cons.2 ⟨sub12_290, List.forall_mem_cons.2 ⟨sub12_291, List.forall_mem_cons.2 ⟨sub12_292, List.forall_mem_cons.2 ⟨sub12_293, List.forall_mem_cons.2 ⟨sub12_294, List.forall_mem_cons.2 ⟨sub12_295, List.forall_mem_cons.2 ⟨sub12_296, List.forall_mem_cons.2 ⟨sub12_297, List.forall_mem_cons.2 ⟨sub12_298, List.forall_mem_cons.2 ⟨sub12_299, List.forall_mem_cons.2 ⟨sub12_300, List.forall_mem_cons.2 ⟨sub12_301, List.forall_mem_cons.2 ⟨sub12_302, List.forall_mem_cons.2 ⟨sub12_303, List.forall_mem_cons.2 ⟨sub12_304, List.forall_mem_cons.2 ⟨sub12_305, List.forall_mem_cons.2 ⟨sub12_306, List.forall_mem_cons.2 ⟨sub12_307, List.forall_mem_cons.2 ⟨sub12_308, List.forall_mem_cons.2 ⟨sub12_309, List.forall_mem_cons.2 ⟨sub12_310, List.forall_mem_cons.2 ⟨sub12_311, List.forall_mem_cons.2 ⟨sub12_312, List.forall_mem_cons.2 ⟨sub12_313, List.forall_mem_cons.2 ⟨sub12_314, List.forall_mem_cons.2 ⟨sub12_315, List.forall_mem_cons.2 ⟨sub12_316, List.forall_mem_cons.2 ⟨sub12_317, List.forall_mem_cons.2 ⟨sub12_318, List.forall_mem_cons.2 ⟨sub12_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_320 : sub12 [0, 1, 4] = true := by decide +kernel
theorem sub12_321 : sub12 [0, 1, 5] = true := by decide +kernel
theorem sub12_322 : sub12 [0, 1, 6] = true := by decide +kernel
theorem sub12_323 : sub12 [0, 1, 7] = true := by decide +kernel
theorem sub12_324 : sub12 [0, 2, -8] = true := by decide +kernel
theorem sub12_325 : sub12 [0, 2, -7] = true := by decide +kernel
theorem sub12_326 : sub12 [0, 2, -6] = true := by decide +kernel
theorem sub12_327 : sub12 [0, 2, -5] = true := by decide +kernel
theorem sub12_328 : sub12 [0, 2, -4] = true := by decide +kernel
theorem sub12_329 : sub12 [0, 2, -3] = true := by decide +kernel
theorem sub12_330 : sub12 [0, 2, -2] = true := by decide +kernel
theorem sub12_331 : sub12 [0, 2, -1] = true := by decide +kernel
theorem sub12_332 : sub12 [0, 2, 0] = true := by decide +kernel
theorem sub12_333 : sub12 [0, 2, 1] = true := by decide +kernel
theorem sub12_334 : sub12 [0, 2, 2] = true := by decide +kernel
theorem sub12_335 : sub12 [0, 2, 3] = true := by decide +kernel
theorem sub12_336 : sub12 [0, 2, 4] = true := by decide +kernel
theorem sub12_337 : sub12 [0, 2, 5] = true := by decide +kernel
theorem sub12_338 : sub12 [0, 2, 6] = true := by decide +kernel
theorem sub12_339 : sub12 [0, 3, -7] = true := by decide +kernel
theorem sub12_340 : sub12 [0, 3, -6] = true := by decide +kernel
theorem sub12_341 : sub12 [0, 3, -5] = true := by decide +kernel
theorem sub12_342 : sub12 [0, 3, -4] = true := by decide +kernel
theorem sub12_343 : sub12 [0, 3, -3] = true := by decide +kernel
theorem sub12_344 : sub12 [0, 3, -2] = true := by decide +kernel
theorem sub12_345 : sub12 [0, 3, -1] = true := by decide +kernel
theorem sub12_346 : sub12 [0, 3, 0] = true := by decide +kernel
theorem sub12_347 : sub12 [0, 3, 1] = true := by decide +kernel
theorem sub12_348 : sub12 [0, 3, 2] = true := by decide +kernel
theorem sub12_349 : sub12 [0, 3, 3] = true := by decide +kernel
theorem sub12_350 : sub12 [0, 3, 4] = true := by decide +kernel
theorem sub12_351 : sub12 [0, 3, 5] = true := by decide +kernel
theorem sb12_10 : ∀ q ∈ blk12_10, sub12 q = true := by
  unfold blk12_10
  exact List.forall_mem_cons.2 ⟨sub12_320, List.forall_mem_cons.2 ⟨sub12_321, List.forall_mem_cons.2 ⟨sub12_322, List.forall_mem_cons.2 ⟨sub12_323, List.forall_mem_cons.2 ⟨sub12_324, List.forall_mem_cons.2 ⟨sub12_325, List.forall_mem_cons.2 ⟨sub12_326, List.forall_mem_cons.2 ⟨sub12_327, List.forall_mem_cons.2 ⟨sub12_328, List.forall_mem_cons.2 ⟨sub12_329, List.forall_mem_cons.2 ⟨sub12_330, List.forall_mem_cons.2 ⟨sub12_331, List.forall_mem_cons.2 ⟨sub12_332, List.forall_mem_cons.2 ⟨sub12_333, List.forall_mem_cons.2 ⟨sub12_334, List.forall_mem_cons.2 ⟨sub12_335, List.forall_mem_cons.2 ⟨sub12_336, List.forall_mem_cons.2 ⟨sub12_337, List.forall_mem_cons.2 ⟨sub12_338, List.forall_mem_cons.2 ⟨sub12_339, List.forall_mem_cons.2 ⟨sub12_340, List.forall_mem_cons.2 ⟨sub12_341, List.forall_mem_cons.2 ⟨sub12_342, List.forall_mem_cons.2 ⟨sub12_343, List.forall_mem_cons.2 ⟨sub12_344, List.forall_mem_cons.2 ⟨sub12_345, List.forall_mem_cons.2 ⟨sub12_346, List.forall_mem_cons.2 ⟨sub12_347, List.forall_mem_cons.2 ⟨sub12_348, List.forall_mem_cons.2 ⟨sub12_349, List.forall_mem_cons.2 ⟨sub12_350, List.forall_mem_cons.2 ⟨sub12_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_352 : sub12 [0, 4] = true := by decide +kernel
theorem sub12_353 : sub12 [1, -5] = true := by decide +kernel
theorem sub12_354 : sub12 [1, -4] = true := by decide +kernel
theorem sub12_355 : sub12 [1, -3, -6] = true := by decide +kernel
theorem sub12_356 : sub12 [1, -3, -5] = true := by decide +kernel
theorem sub12_357 : sub12 [1, -3, -4] = true := by decide +kernel
theorem sub12_358 : sub12 [1, -3, -3] = true := by decide +kernel
theorem sub12_359 : sub12 [1, -3, -2] = true := by decide +kernel
theorem sub12_360 : sub12 [1, -3, -1] = true := by decide +kernel
theorem sub12_361 : sub12 [1, -3, 0] = true := by decide +kernel
theorem sub12_362 : sub12 [1, -3, 1] = true := by decide +kernel
theorem sub12_363 : sub12 [1, -3, 2] = true := by decide +kernel
theorem sub12_364 : sub12 [1, -3, 3] = true := by decide +kernel
theorem sub12_365 : sub12 [1, -3, 4] = true := by decide +kernel
theorem sub12_366 : sub12 [1, -3, 5] = true := by decide +kernel
theorem sub12_367 : sub12 [1, -3, 6] = true := by decide +kernel
theorem sub12_368 : sub12 [1, -3, 7] = true := by decide +kernel
theorem sub12_369 : sub12 [1, -2, -7] = true := by decide +kernel
theorem sub12_370 : sub12 [1, -2, -6] = true := by decide +kernel
theorem sub12_371 : sub12 [1, -2, -5] = true := by decide +kernel
theorem sub12_372 : sub12 [1, -2, -4] = true := by decide +kernel
theorem sub12_373 : sub12 [1, -2, -3] = true := by decide +kernel
theorem sub12_374 : sub12 [1, -2, -2] = true := by decide +kernel
theorem sub12_375 : sub12 [1, -2, -1] = true := by decide +kernel
theorem sub12_376 : sub12 [1, -2, 0] = true := by decide +kernel
theorem sub12_377 : sub12 [1, -2, 1] = true := by decide +kernel
theorem sub12_378 : sub12 [1, -2, 2] = true := by decide +kernel
theorem sub12_379 : sub12 [1, -2, 3] = true := by decide +kernel
theorem sub12_380 : sub12 [1, -2, 4] = true := by decide +kernel
theorem sub12_381 : sub12 [1, -2, 5] = true := by decide +kernel
theorem sub12_382 : sub12 [1, -2, 6] = true := by decide +kernel
theorem sub12_383 : sub12 [1, -2, 7] = true := by decide +kernel
theorem sb12_11 : ∀ q ∈ blk12_11, sub12 q = true := by
  unfold blk12_11
  exact List.forall_mem_cons.2 ⟨sub12_352, List.forall_mem_cons.2 ⟨sub12_353, List.forall_mem_cons.2 ⟨sub12_354, List.forall_mem_cons.2 ⟨sub12_355, List.forall_mem_cons.2 ⟨sub12_356, List.forall_mem_cons.2 ⟨sub12_357, List.forall_mem_cons.2 ⟨sub12_358, List.forall_mem_cons.2 ⟨sub12_359, List.forall_mem_cons.2 ⟨sub12_360, List.forall_mem_cons.2 ⟨sub12_361, List.forall_mem_cons.2 ⟨sub12_362, List.forall_mem_cons.2 ⟨sub12_363, List.forall_mem_cons.2 ⟨sub12_364, List.forall_mem_cons.2 ⟨sub12_365, List.forall_mem_cons.2 ⟨sub12_366, List.forall_mem_cons.2 ⟨sub12_367, List.forall_mem_cons.2 ⟨sub12_368, List.forall_mem_cons.2 ⟨sub12_369, List.forall_mem_cons.2 ⟨sub12_370, List.forall_mem_cons.2 ⟨sub12_371, List.forall_mem_cons.2 ⟨sub12_372, List.forall_mem_cons.2 ⟨sub12_373, List.forall_mem_cons.2 ⟨sub12_374, List.forall_mem_cons.2 ⟨sub12_375, List.forall_mem_cons.2 ⟨sub12_376, List.forall_mem_cons.2 ⟨sub12_377, List.forall_mem_cons.2 ⟨sub12_378, List.forall_mem_cons.2 ⟨sub12_379, List.forall_mem_cons.2 ⟨sub12_380, List.forall_mem_cons.2 ⟨sub12_381, List.forall_mem_cons.2 ⟨sub12_382, List.forall_mem_cons.2 ⟨sub12_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_384 : sub12 [1, -1, -8] = true := by decide +kernel
theorem sub12_385 : sub12 [1, -1, -7] = true := by decide +kernel
theorem sub12_386 : sub12 [1, -1, -6] = true := by decide +kernel
theorem sub12_387 : sub12 [1, -1, -5] = true := by decide +kernel
theorem sub12_388 : sub12 [1, -1, -4] = true := by decide +kernel
theorem sub12_389 : sub12 [1, -1, -3] = true := by decide +kernel
theorem sub12_390 : sub12 [1, -1, -2] = true := by decide +kernel
theorem sub12_391 : sub12 [1, -1, -1] = true := by decide +kernel
theorem sub12_392 : sub12 [1, -1, 0] = true := by decide +kernel
theorem sub12_393 : sub12 [1, -1, 1] = true := by decide +kernel
theorem sub12_394 : sub12 [1, -1, 2] = true := by decide +kernel
theorem sub12_395 : sub12 [1, -1, 3] = true := by decide +kernel
theorem sub12_396 : sub12 [1, -1, 4] = true := by decide +kernel
theorem sub12_397 : sub12 [1, -1, 5] = true := by decide +kernel
theorem sub12_398 : sub12 [1, -1, 6] = true := by decide +kernel
theorem sub12_399 : sub12 [1, -1, 7] = true := by decide +kernel
theorem sub12_400 : sub12 [1, -1, 8] = true := by decide +kernel
theorem sub12_401 : sub12 [1, 0, -8] = true := by decide +kernel
theorem sub12_402 : sub12 [1, 0, -7] = true := by decide +kernel
theorem sub12_403 : sub12 [1, 0, -6] = true := by decide +kernel
theorem sub12_404 : sub12 [1, 0, -5] = true := by decide +kernel
theorem sub12_405 : sub12 [1, 0, -4] = true := by decide +kernel
theorem sub12_406 : sub12 [1, 0, -3] = true := by decide +kernel
theorem sub12_407 : sub12 [1, 0, -2] = true := by decide +kernel
theorem sub12_408 : sub12 [1, 0, -1] = true := by decide +kernel
theorem sub12_409 : sub12 [1, 0, 0] = true := by decide +kernel
theorem sub12_410 : sub12 [1, 0, 1] = true := by decide +kernel
theorem sub12_411 : sub12 [1, 0, 2] = true := by decide +kernel
theorem sub12_412 : sub12 [1, 0, 3] = true := by decide +kernel
theorem sub12_413 : sub12 [1, 0, 4] = true := by decide +kernel
theorem sub12_414 : sub12 [1, 0, 5] = true := by decide +kernel
theorem sub12_415 : sub12 [1, 0, 6] = true := by decide +kernel
theorem sb12_12 : ∀ q ∈ blk12_12, sub12 q = true := by
  unfold blk12_12
  exact List.forall_mem_cons.2 ⟨sub12_384, List.forall_mem_cons.2 ⟨sub12_385, List.forall_mem_cons.2 ⟨sub12_386, List.forall_mem_cons.2 ⟨sub12_387, List.forall_mem_cons.2 ⟨sub12_388, List.forall_mem_cons.2 ⟨sub12_389, List.forall_mem_cons.2 ⟨sub12_390, List.forall_mem_cons.2 ⟨sub12_391, List.forall_mem_cons.2 ⟨sub12_392, List.forall_mem_cons.2 ⟨sub12_393, List.forall_mem_cons.2 ⟨sub12_394, List.forall_mem_cons.2 ⟨sub12_395, List.forall_mem_cons.2 ⟨sub12_396, List.forall_mem_cons.2 ⟨sub12_397, List.forall_mem_cons.2 ⟨sub12_398, List.forall_mem_cons.2 ⟨sub12_399, List.forall_mem_cons.2 ⟨sub12_400, List.forall_mem_cons.2 ⟨sub12_401, List.forall_mem_cons.2 ⟨sub12_402, List.forall_mem_cons.2 ⟨sub12_403, List.forall_mem_cons.2 ⟨sub12_404, List.forall_mem_cons.2 ⟨sub12_405, List.forall_mem_cons.2 ⟨sub12_406, List.forall_mem_cons.2 ⟨sub12_407, List.forall_mem_cons.2 ⟨sub12_408, List.forall_mem_cons.2 ⟨sub12_409, List.forall_mem_cons.2 ⟨sub12_410, List.forall_mem_cons.2 ⟨sub12_411, List.forall_mem_cons.2 ⟨sub12_412, List.forall_mem_cons.2 ⟨sub12_413, List.forall_mem_cons.2 ⟨sub12_414, List.forall_mem_cons.2 ⟨sub12_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_416 : sub12 [1, 0, 7] = true := by decide +kernel
theorem sub12_417 : sub12 [1, 0, 8] = true := by decide +kernel
theorem sub12_418 : sub12 [1, 1, -8] = true := by decide +kernel
theorem sub12_419 : sub12 [1, 1, -7] = true := by decide +kernel
theorem sub12_420 : sub12 [1, 1, -6] = true := by decide +kernel
theorem sub12_421 : sub12 [1, 1, -5] = true := by decide +kernel
theorem sub12_422 : sub12 [1, 1, -4] = true := by decide +kernel
theorem sub12_423 : sub12 [1, 1, -3] = true := by decide +kernel
theorem sub12_424 : sub12 [1, 1, -2] = true := by decide +kernel
theorem sub12_425 : sub12 [1, 1, -1] = true := by decide +kernel
theorem sub12_426 : sub12 [1, 1, 0] = true := by decide +kernel
theorem sub12_427 : sub12 [1, 1, 1] = true := by decide +kernel
theorem sub12_428 : sub12 [1, 1, 2] = true := by decide +kernel
theorem sub12_429 : sub12 [1, 1, 3] = true := by decide +kernel
theorem sub12_430 : sub12 [1, 1, 4] = true := by decide +kernel
theorem sub12_431 : sub12 [1, 1, 5] = true := by decide +kernel
theorem sub12_432 : sub12 [1, 1, 6] = true := by decide +kernel
theorem sub12_433 : sub12 [1, 1, 7] = true := by decide +kernel
theorem sub12_434 : sub12 [1, 2, -8] = true := by decide +kernel
theorem sub12_435 : sub12 [1, 2, -7] = true := by decide +kernel
theorem sub12_436 : sub12 [1, 2, -6] = true := by decide +kernel
theorem sub12_437 : sub12 [1, 2, -5] = true := by decide +kernel
theorem sub12_438 : sub12 [1, 2, -4] = true := by decide +kernel
theorem sub12_439 : sub12 [1, 2, -3] = true := by decide +kernel
theorem sub12_440 : sub12 [1, 2, -2] = true := by decide +kernel
theorem sub12_441 : sub12 [1, 2, -1] = true := by decide +kernel
theorem sub12_442 : sub12 [1, 2, 0] = true := by decide +kernel
theorem sub12_443 : sub12 [1, 2, 1] = true := by decide +kernel
theorem sub12_444 : sub12 [1, 2, 2] = true := by decide +kernel
theorem sub12_445 : sub12 [1, 2, 3] = true := by decide +kernel
theorem sub12_446 : sub12 [1, 2, 4] = true := by decide +kernel
theorem sub12_447 : sub12 [1, 2, 5] = true := by decide +kernel
theorem sb12_13 : ∀ q ∈ blk12_13, sub12 q = true := by
  unfold blk12_13
  exact List.forall_mem_cons.2 ⟨sub12_416, List.forall_mem_cons.2 ⟨sub12_417, List.forall_mem_cons.2 ⟨sub12_418, List.forall_mem_cons.2 ⟨sub12_419, List.forall_mem_cons.2 ⟨sub12_420, List.forall_mem_cons.2 ⟨sub12_421, List.forall_mem_cons.2 ⟨sub12_422, List.forall_mem_cons.2 ⟨sub12_423, List.forall_mem_cons.2 ⟨sub12_424, List.forall_mem_cons.2 ⟨sub12_425, List.forall_mem_cons.2 ⟨sub12_426, List.forall_mem_cons.2 ⟨sub12_427, List.forall_mem_cons.2 ⟨sub12_428, List.forall_mem_cons.2 ⟨sub12_429, List.forall_mem_cons.2 ⟨sub12_430, List.forall_mem_cons.2 ⟨sub12_431, List.forall_mem_cons.2 ⟨sub12_432, List.forall_mem_cons.2 ⟨sub12_433, List.forall_mem_cons.2 ⟨sub12_434, List.forall_mem_cons.2 ⟨sub12_435, List.forall_mem_cons.2 ⟨sub12_436, List.forall_mem_cons.2 ⟨sub12_437, List.forall_mem_cons.2 ⟨sub12_438, List.forall_mem_cons.2 ⟨sub12_439, List.forall_mem_cons.2 ⟨sub12_440, List.forall_mem_cons.2 ⟨sub12_441, List.forall_mem_cons.2 ⟨sub12_442, List.forall_mem_cons.2 ⟨sub12_443, List.forall_mem_cons.2 ⟨sub12_444, List.forall_mem_cons.2 ⟨sub12_445, List.forall_mem_cons.2 ⟨sub12_446, List.forall_mem_cons.2 ⟨sub12_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
