import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_4_32 : subd9_4 [-1, 0, 3] = true := by decide +kernel
theorem subd9_4_33 : subd9_4 [-1, 0, 4] = true := by decide +kernel
theorem subd9_4_34 : subd9_4 [-1, 0, 5] = true := by decide +kernel
theorem subd9_4_35 : subd9_4 [-1, 0, 6] = true := by decide +kernel
theorem subd9_4_36 : subd9_4 [-1, 0, 7] = true := by decide +kernel
theorem subd9_4_37 : subd9_4 [-1, 1, -7] = true := by decide +kernel
theorem subd9_4_38 : subd9_4 [-1, 1, -6] = true := by decide +kernel
theorem subd9_4_39 : subd9_4 [-1, 1, -5] = true := by decide +kernel
theorem subd9_4_40 : subd9_4 [-1, 1, -4] = true := by decide +kernel
theorem subd9_4_41 : subd9_4 [-1, 1, -3] = true := by decide +kernel
theorem subd9_4_42 : subd9_4 [-1, 1, -2] = true := by decide +kernel
theorem subd9_4_43 : subd9_4 [-1, 1, -1] = true := by decide +kernel
theorem subd9_4_44 : subd9_4 [-1, 1, 0] = true := by decide +kernel
theorem subd9_4_45 : subd9_4 [-1, 1, 1] = true := by decide +kernel
theorem subd9_4_46 : subd9_4 [-1, 1, 2] = true := by decide +kernel
theorem subd9_4_47 : subd9_4 [-1, 1, 3] = true := by decide +kernel
theorem subd9_4_48 : subd9_4 [-1, 1, 4] = true := by decide +kernel
theorem subd9_4_49 : subd9_4 [-1, 1, 5] = true := by decide +kernel
theorem subd9_4_50 : subd9_4 [-1, 1, 6] = true := by decide +kernel
theorem subd9_4_51 : subd9_4 [-1, 1, 7] = true := by decide +kernel
theorem subd9_4_52 : subd9_4 [-1, 2] = true := by decide +kernel
theorem subd9_4_53 : subd9_4 [0, -3] = true := by decide +kernel
theorem subd9_4_54 : subd9_4 [0, -2] = true := by decide +kernel
theorem subd9_4_55 : subd9_4 [0, -1, -8] = true := by decide +kernel
theorem subd9_4_56 : subd9_4 [0, -1, -7] = true := by decide +kernel
theorem subd9_4_57 : subd9_4 [0, -1, -6] = true := by decide +kernel
theorem subd9_4_58 : subd9_4 [0, -1, -5] = true := by decide +kernel
theorem subd9_4_59 : subd9_4 [0, -1, -4] = true := by decide +kernel
theorem subd9_4_60 : subd9_4 [0, -1, -3] = true := by decide +kernel
theorem subd9_4_61 : subd9_4 [0, -1, -2] = true := by decide +kernel
theorem subd9_4_62 : subd9_4 [0, -1, -1] = true := by decide +kernel
theorem subd9_4_63 : subd9_4 [0, -1, 0] = true := by decide +kernel
theorem sbd9_4_1 : ∀ q ∈ blkd9_4_1, subd9_4 q = true := by
  unfold blkd9_4_1
  exact List.forall_mem_cons.2 ⟨subd9_4_32, List.forall_mem_cons.2 ⟨subd9_4_33, List.forall_mem_cons.2 ⟨subd9_4_34, List.forall_mem_cons.2 ⟨subd9_4_35, List.forall_mem_cons.2 ⟨subd9_4_36, List.forall_mem_cons.2 ⟨subd9_4_37, List.forall_mem_cons.2 ⟨subd9_4_38, List.forall_mem_cons.2 ⟨subd9_4_39, List.forall_mem_cons.2 ⟨subd9_4_40, List.forall_mem_cons.2 ⟨subd9_4_41, List.forall_mem_cons.2 ⟨subd9_4_42, List.forall_mem_cons.2 ⟨subd9_4_43, List.forall_mem_cons.2 ⟨subd9_4_44, List.forall_mem_cons.2 ⟨subd9_4_45, List.forall_mem_cons.2 ⟨subd9_4_46, List.forall_mem_cons.2 ⟨subd9_4_47, List.forall_mem_cons.2 ⟨subd9_4_48, List.forall_mem_cons.2 ⟨subd9_4_49, List.forall_mem_cons.2 ⟨subd9_4_50, List.forall_mem_cons.2 ⟨subd9_4_51, List.forall_mem_cons.2 ⟨subd9_4_52, List.forall_mem_cons.2 ⟨subd9_4_53, List.forall_mem_cons.2 ⟨subd9_4_54, List.forall_mem_cons.2 ⟨subd9_4_55, List.forall_mem_cons.2 ⟨subd9_4_56, List.forall_mem_cons.2 ⟨subd9_4_57, List.forall_mem_cons.2 ⟨subd9_4_58, List.forall_mem_cons.2 ⟨subd9_4_59, List.forall_mem_cons.2 ⟨subd9_4_60, List.forall_mem_cons.2 ⟨subd9_4_61, List.forall_mem_cons.2 ⟨subd9_4_62, List.forall_mem_cons.2 ⟨subd9_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_64 : subd9_4 [0, -1, 1] = true := by decide +kernel
theorem subd9_4_65 : subd9_4 [0, -1, 2] = true := by decide +kernel
theorem subd9_4_66 : subd9_4 [0, -1, 3] = true := by decide +kernel
theorem subd9_4_67 : subd9_4 [0, -1, 4] = true := by decide +kernel
theorem subd9_4_68 : subd9_4 [0, -1, 5] = true := by decide +kernel
theorem subd9_4_69 : subd9_4 [0, -1, 6] = true := by decide +kernel
theorem subd9_4_70 : subd9_4 [0, -1, 7] = true := by decide +kernel
theorem subd9_4_71 : subd9_4 [0, 0, -9] = true := by decide +kernel
theorem subd9_4_72 : subd9_4 [0, 0, -8] = true := by decide +kernel
theorem subd9_4_73 : subd9_4 [0, 0, -7] = true := by decide +kernel
theorem subd9_4_74 : subd9_4 [0, 0, -6] = true := by decide +kernel
theorem subd9_4_75 : subd9_4 [0, 0, -5] = true := by decide +kernel
theorem subd9_4_76 : subd9_4 [0, 0, -4] = true := by decide +kernel
theorem subd9_4_77 : subd9_4 [0, 0, -3] = true := by decide +kernel
theorem subd9_4_78 : subd9_4 [0, 0, -2] = true := by decide +kernel
theorem subd9_4_79 : subd9_4 [0, 0, -1] = true := by decide +kernel
theorem subd9_4_80 : subd9_4 [0, 0, 0] = true := by decide +kernel
theorem subd9_4_81 : subd9_4 [0, 0, 1] = true := by decide +kernel
theorem subd9_4_82 : subd9_4 [0, 0, 2] = true := by decide +kernel
theorem subd9_4_83 : subd9_4 [0, 0, 3] = true := by decide +kernel
theorem subd9_4_84 : subd9_4 [0, 0, 4] = true := by decide +kernel
theorem subd9_4_85 : subd9_4 [0, 0, 5] = true := by decide +kernel
theorem subd9_4_86 : subd9_4 [0, 0, 6] = true := by decide +kernel
theorem subd9_4_87 : subd9_4 [0, 0, 7] = true := by decide +kernel
theorem subd9_4_88 : subd9_4 [0, 0, 8] = true := by decide +kernel
theorem subd9_4_89 : subd9_4 [0, 1, -8] = true := by decide +kernel
theorem subd9_4_90 : subd9_4 [0, 1, -7] = true := by decide +kernel
theorem subd9_4_91 : subd9_4 [0, 1, -6] = true := by decide +kernel
theorem subd9_4_92 : subd9_4 [0, 1, -5] = true := by decide +kernel
theorem subd9_4_93 : subd9_4 [0, 1, -4] = true := by decide +kernel
theorem subd9_4_94 : subd9_4 [0, 1, -3] = true := by decide +kernel
theorem subd9_4_95 : subd9_4 [0, 1, -2] = true := by decide +kernel
theorem sbd9_4_2 : ∀ q ∈ blkd9_4_2, subd9_4 q = true := by
  unfold blkd9_4_2
  exact List.forall_mem_cons.2 ⟨subd9_4_64, List.forall_mem_cons.2 ⟨subd9_4_65, List.forall_mem_cons.2 ⟨subd9_4_66, List.forall_mem_cons.2 ⟨subd9_4_67, List.forall_mem_cons.2 ⟨subd9_4_68, List.forall_mem_cons.2 ⟨subd9_4_69, List.forall_mem_cons.2 ⟨subd9_4_70, List.forall_mem_cons.2 ⟨subd9_4_71, List.forall_mem_cons.2 ⟨subd9_4_72, List.forall_mem_cons.2 ⟨subd9_4_73, List.forall_mem_cons.2 ⟨subd9_4_74, List.forall_mem_cons.2 ⟨subd9_4_75, List.forall_mem_cons.2 ⟨subd9_4_76, List.forall_mem_cons.2 ⟨subd9_4_77, List.forall_mem_cons.2 ⟨subd9_4_78, List.forall_mem_cons.2 ⟨subd9_4_79, List.forall_mem_cons.2 ⟨subd9_4_80, List.forall_mem_cons.2 ⟨subd9_4_81, List.forall_mem_cons.2 ⟨subd9_4_82, List.forall_mem_cons.2 ⟨subd9_4_83, List.forall_mem_cons.2 ⟨subd9_4_84, List.forall_mem_cons.2 ⟨subd9_4_85, List.forall_mem_cons.2 ⟨subd9_4_86, List.forall_mem_cons.2 ⟨subd9_4_87, List.forall_mem_cons.2 ⟨subd9_4_88, List.forall_mem_cons.2 ⟨subd9_4_89, List.forall_mem_cons.2 ⟨subd9_4_90, List.forall_mem_cons.2 ⟨subd9_4_91, List.forall_mem_cons.2 ⟨subd9_4_92, List.forall_mem_cons.2 ⟨subd9_4_93, List.forall_mem_cons.2 ⟨subd9_4_94, List.forall_mem_cons.2 ⟨subd9_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_96 : subd9_4 [0, 1, -1] = true := by decide +kernel
theorem subd9_4_97 : subd9_4 [0, 1, 0] = true := by decide +kernel
theorem subd9_4_98 : subd9_4 [0, 1, 1] = true := by decide +kernel
theorem subd9_4_99 : subd9_4 [0, 1, 2] = true := by decide +kernel
theorem subd9_4_100 : subd9_4 [0, 1, 3] = true := by decide +kernel
theorem subd9_4_101 : subd9_4 [0, 1, 4] = true := by decide +kernel
theorem subd9_4_102 : subd9_4 [0, 1, 5] = true := by decide +kernel
theorem subd9_4_103 : subd9_4 [0, 1, 6] = true := by decide +kernel
theorem subd9_4_104 : subd9_4 [0, 1, 7] = true := by decide +kernel
theorem subd9_4_105 : subd9_4 [0, 2] = true := by decide +kernel
theorem subd9_4_106 : subd9_4 [1, -3] = true := by decide +kernel
theorem subd9_4_107 : subd9_4 [1, -2] = true := by decide +kernel
theorem subd9_4_108 : subd9_4 [1, -1, -8] = true := by decide +kernel
theorem subd9_4_109 : subd9_4 [1, -1, -7] = true := by decide +kernel
theorem subd9_4_110 : subd9_4 [1, -1, -6] = true := by decide +kernel
theorem subd9_4_111 : subd9_4 [1, -1, -5] = true := by decide +kernel
theorem subd9_4_112 : subd9_4 [1, -1, -4] = true := by decide +kernel
theorem subd9_4_113 : subd9_4 [1, -1, -3] = true := by decide +kernel
theorem subd9_4_114 : subd9_4 [1, -1, -2] = true := by decide +kernel
theorem subd9_4_115 : subd9_4 [1, -1, -1] = true := by decide +kernel
theorem subd9_4_116 : subd9_4 [1, -1, 0] = true := by decide +kernel
theorem subd9_4_117 : subd9_4 [1, -1, 1] = true := by decide +kernel
theorem subd9_4_118 : subd9_4 [1, -1, 2] = true := by decide +kernel
theorem subd9_4_119 : subd9_4 [1, -1, 3] = true := by decide +kernel
theorem subd9_4_120 : subd9_4 [1, -1, 4] = true := by decide +kernel
theorem subd9_4_121 : subd9_4 [1, -1, 5] = true := by decide +kernel
theorem subd9_4_122 : subd9_4 [1, -1, 6] = true := by decide +kernel
theorem subd9_4_123 : subd9_4 [1, 0, -8] = true := by decide +kernel
theorem subd9_4_124 : subd9_4 [1, 0, -7] = true := by decide +kernel
theorem subd9_4_125 : subd9_4 [1, 0, -6] = true := by decide +kernel
theorem subd9_4_126 : subd9_4 [1, 0, -5] = true := by decide +kernel
theorem subd9_4_127 : subd9_4 [1, 0, -4] = true := by decide +kernel
theorem sbd9_4_3 : ∀ q ∈ blkd9_4_3, subd9_4 q = true := by
  unfold blkd9_4_3
  exact List.forall_mem_cons.2 ⟨subd9_4_96, List.forall_mem_cons.2 ⟨subd9_4_97, List.forall_mem_cons.2 ⟨subd9_4_98, List.forall_mem_cons.2 ⟨subd9_4_99, List.forall_mem_cons.2 ⟨subd9_4_100, List.forall_mem_cons.2 ⟨subd9_4_101, List.forall_mem_cons.2 ⟨subd9_4_102, List.forall_mem_cons.2 ⟨subd9_4_103, List.forall_mem_cons.2 ⟨subd9_4_104, List.forall_mem_cons.2 ⟨subd9_4_105, List.forall_mem_cons.2 ⟨subd9_4_106, List.forall_mem_cons.2 ⟨subd9_4_107, List.forall_mem_cons.2 ⟨subd9_4_108, List.forall_mem_cons.2 ⟨subd9_4_109, List.forall_mem_cons.2 ⟨subd9_4_110, List.forall_mem_cons.2 ⟨subd9_4_111, List.forall_mem_cons.2 ⟨subd9_4_112, List.forall_mem_cons.2 ⟨subd9_4_113, List.forall_mem_cons.2 ⟨subd9_4_114, List.forall_mem_cons.2 ⟨subd9_4_115, List.forall_mem_cons.2 ⟨subd9_4_116, List.forall_mem_cons.2 ⟨subd9_4_117, List.forall_mem_cons.2 ⟨subd9_4_118, List.forall_mem_cons.2 ⟨subd9_4_119, List.forall_mem_cons.2 ⟨subd9_4_120, List.forall_mem_cons.2 ⟨subd9_4_121, List.forall_mem_cons.2 ⟨subd9_4_122, List.forall_mem_cons.2 ⟨subd9_4_123, List.forall_mem_cons.2 ⟨subd9_4_124, List.forall_mem_cons.2 ⟨subd9_4_125, List.forall_mem_cons.2 ⟨subd9_4_126, List.forall_mem_cons.2 ⟨subd9_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_128 : subd9_4 [1, 0, -3] = true := by decide +kernel
theorem subd9_4_129 : subd9_4 [1, 0, -2] = true := by decide +kernel
theorem subd9_4_130 : subd9_4 [1, 0, -1] = true := by decide +kernel
theorem subd9_4_131 : subd9_4 [1, 0, 0] = true := by decide +kernel
theorem subd9_4_132 : subd9_4 [1, 0, 1] = true := by decide +kernel
theorem subd9_4_133 : subd9_4 [1, 0, 2] = true := by decide +kernel
theorem subd9_4_134 : subd9_4 [1, 0, 3] = true := by decide +kernel
theorem subd9_4_135 : subd9_4 [1, 0, 4] = true := by decide +kernel
theorem subd9_4_136 : subd9_4 [1, 0, 5] = true := by decide +kernel
theorem subd9_4_137 : subd9_4 [1, 0, 6] = true := by decide +kernel
theorem subd9_4_138 : subd9_4 [1, 0, 7] = true := by decide +kernel
theorem subd9_4_139 : subd9_4 [1, 1, -8] = true := by decide +kernel
theorem subd9_4_140 : subd9_4 [1, 1, -7] = true := by decide +kernel
theorem subd9_4_141 : subd9_4 [1, 1, -6] = true := by decide +kernel
theorem subd9_4_142 : subd9_4 [1, 1, -5] = true := by decide +kernel
theorem subd9_4_143 : subd9_4 [1, 1, -4] = true := by decide +kernel
theorem subd9_4_144 : subd9_4 [1, 1, -3] = true := by decide +kernel
theorem subd9_4_145 : subd9_4 [1, 1, -2] = true := by decide +kernel
theorem subd9_4_146 : subd9_4 [1, 1, -1] = true := by decide +kernel
theorem subd9_4_147 : subd9_4 [1, 1, 0] = true := by decide +kernel
theorem subd9_4_148 : subd9_4 [1, 1, 1] = true := by decide +kernel
theorem subd9_4_149 : subd9_4 [1, 1, 2] = true := by decide +kernel
theorem subd9_4_150 : subd9_4 [1, 1, 3] = true := by decide +kernel
theorem subd9_4_151 : subd9_4 [1, 1, 4] = true := by decide +kernel
theorem subd9_4_152 : subd9_4 [1, 1, 5] = true := by decide +kernel
theorem subd9_4_153 : subd9_4 [1, 1, 6] = true := by decide +kernel
theorem subd9_4_154 : subd9_4 [1, 2] = true := by decide +kernel
theorem subd9_4_155 : subd9_4 [2, -2] = true := by decide +kernel
theorem subd9_4_156 : subd9_4 [2, -1] = true := by decide +kernel
theorem subd9_4_157 : subd9_4 [2, 0] = true := by decide +kernel
theorem subd9_4_158 : subd9_4 [2, 1] = true := by decide +kernel
theorem sbd9_4_4 : ∀ q ∈ blkd9_4_4, subd9_4 q = true := by
  unfold blkd9_4_4
  exact List.forall_mem_cons.2 ⟨subd9_4_128, List.forall_mem_cons.2 ⟨subd9_4_129, List.forall_mem_cons.2 ⟨subd9_4_130, List.forall_mem_cons.2 ⟨subd9_4_131, List.forall_mem_cons.2 ⟨subd9_4_132, List.forall_mem_cons.2 ⟨subd9_4_133, List.forall_mem_cons.2 ⟨subd9_4_134, List.forall_mem_cons.2 ⟨subd9_4_135, List.forall_mem_cons.2 ⟨subd9_4_136, List.forall_mem_cons.2 ⟨subd9_4_137, List.forall_mem_cons.2 ⟨subd9_4_138, List.forall_mem_cons.2 ⟨subd9_4_139, List.forall_mem_cons.2 ⟨subd9_4_140, List.forall_mem_cons.2 ⟨subd9_4_141, List.forall_mem_cons.2 ⟨subd9_4_142, List.forall_mem_cons.2 ⟨subd9_4_143, List.forall_mem_cons.2 ⟨subd9_4_144, List.forall_mem_cons.2 ⟨subd9_4_145, List.forall_mem_cons.2 ⟨subd9_4_146, List.forall_mem_cons.2 ⟨subd9_4_147, List.forall_mem_cons.2 ⟨subd9_4_148, List.forall_mem_cons.2 ⟨subd9_4_149, List.forall_mem_cons.2 ⟨subd9_4_150, List.forall_mem_cons.2 ⟨subd9_4_151, List.forall_mem_cons.2 ⟨subd9_4_152, List.forall_mem_cons.2 ⟨subd9_4_153, List.forall_mem_cons.2 ⟨subd9_4_154, List.forall_mem_cons.2 ⟨subd9_4_155, List.forall_mem_cons.2 ⟨subd9_4_156, List.forall_mem_cons.2 ⟨subd9_4_157, List.forall_mem_cons.2 ⟨subd9_4_158, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-2] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-1] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [0, -3] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [0, -2] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [0, -1] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [0, 0] = true := by decide +kernel
theorem subd9_5_6 : subd9_5 [0, 1] = true := by decide +kernel
theorem subd9_5_7 : subd9_5 [0, 2] = true := by decide +kernel
theorem subd9_5_8 : subd9_5 [1] = true := by decide +kernel
theorem subd9_5_9 : subd9_5 [2] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_cons.2 ⟨subd9_5_6, List.forall_mem_cons.2 ⟨subd9_5_7, List.forall_mem_cons.2 ⟨subd9_5_8, List.forall_mem_cons.2 ⟨subd9_5_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel
theorem subd9_6_0 : subd9_6 [] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_nil _⟩
theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_nil _⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_nil _⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
