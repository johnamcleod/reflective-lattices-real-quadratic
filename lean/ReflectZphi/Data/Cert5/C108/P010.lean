import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_32 : subd8_4 [-1, 0, 7] = true := by decide +kernel
theorem subd8_4_33 : subd8_4 [-1, 0, 8] = true := by decide +kernel
theorem subd8_4_34 : subd8_4 [-1, 1, -8] = true := by decide +kernel
theorem subd8_4_35 : subd8_4 [-1, 1, -7] = true := by decide +kernel
theorem subd8_4_36 : subd8_4 [-1, 1, -6] = true := by decide +kernel
theorem subd8_4_37 : subd8_4 [-1, 1, -5] = true := by decide +kernel
theorem subd8_4_38 : subd8_4 [-1, 1, -4] = true := by decide +kernel
theorem subd8_4_39 : subd8_4 [-1, 1, -3] = true := by decide +kernel
theorem subd8_4_40 : subd8_4 [-1, 1, -2] = true := by decide +kernel
theorem subd8_4_41 : subd8_4 [-1, 1, -1] = true := by decide +kernel
theorem subd8_4_42 : subd8_4 [-1, 1, 0] = true := by decide +kernel
theorem subd8_4_43 : subd8_4 [-1, 1, 1] = true := by decide +kernel
theorem subd8_4_44 : subd8_4 [-1, 1, 2] = true := by decide +kernel
theorem subd8_4_45 : subd8_4 [-1, 1, 3] = true := by decide +kernel
theorem subd8_4_46 : subd8_4 [-1, 1, 4] = true := by decide +kernel
theorem subd8_4_47 : subd8_4 [-1, 1, 5] = true := by decide +kernel
theorem subd8_4_48 : subd8_4 [-1, 1, 6] = true := by decide +kernel
theorem subd8_4_49 : subd8_4 [0, -2] = true := by decide +kernel
theorem subd8_4_50 : subd8_4 [0, -1, -9] = true := by decide +kernel
theorem subd8_4_51 : subd8_4 [0, -1, -8] = true := by decide +kernel
theorem subd8_4_52 : subd8_4 [0, -1, -7] = true := by decide +kernel
theorem subd8_4_53 : subd8_4 [0, -1, -6] = true := by decide +kernel
theorem subd8_4_54 : subd8_4 [0, -1, -5] = true := by decide +kernel
theorem subd8_4_55 : subd8_4 [0, -1, -4] = true := by decide +kernel
theorem subd8_4_56 : subd8_4 [0, -1, -3] = true := by decide +kernel
theorem subd8_4_57 : subd8_4 [0, -1, -2] = true := by decide +kernel
theorem subd8_4_58 : subd8_4 [0, -1, -1] = true := by decide +kernel
theorem subd8_4_59 : subd8_4 [0, -1, 0] = true := by decide +kernel
theorem subd8_4_60 : subd8_4 [0, -1, 1] = true := by decide +kernel
theorem subd8_4_61 : subd8_4 [0, -1, 2] = true := by decide +kernel
theorem subd8_4_62 : subd8_4 [0, -1, 3] = true := by decide +kernel
theorem subd8_4_63 : subd8_4 [0, -1, 4] = true := by decide +kernel
theorem sbd8_4_1 : ∀ q ∈ blkd8_4_1, subd8_4 q = true := by
  unfold blkd8_4_1
  exact List.forall_mem_cons.2 ⟨subd8_4_32, List.forall_mem_cons.2 ⟨subd8_4_33, List.forall_mem_cons.2 ⟨subd8_4_34, List.forall_mem_cons.2 ⟨subd8_4_35, List.forall_mem_cons.2 ⟨subd8_4_36, List.forall_mem_cons.2 ⟨subd8_4_37, List.forall_mem_cons.2 ⟨subd8_4_38, List.forall_mem_cons.2 ⟨subd8_4_39, List.forall_mem_cons.2 ⟨subd8_4_40, List.forall_mem_cons.2 ⟨subd8_4_41, List.forall_mem_cons.2 ⟨subd8_4_42, List.forall_mem_cons.2 ⟨subd8_4_43, List.forall_mem_cons.2 ⟨subd8_4_44, List.forall_mem_cons.2 ⟨subd8_4_45, List.forall_mem_cons.2 ⟨subd8_4_46, List.forall_mem_cons.2 ⟨subd8_4_47, List.forall_mem_cons.2 ⟨subd8_4_48, List.forall_mem_cons.2 ⟨subd8_4_49, List.forall_mem_cons.2 ⟨subd8_4_50, List.forall_mem_cons.2 ⟨subd8_4_51, List.forall_mem_cons.2 ⟨subd8_4_52, List.forall_mem_cons.2 ⟨subd8_4_53, List.forall_mem_cons.2 ⟨subd8_4_54, List.forall_mem_cons.2 ⟨subd8_4_55, List.forall_mem_cons.2 ⟨subd8_4_56, List.forall_mem_cons.2 ⟨subd8_4_57, List.forall_mem_cons.2 ⟨subd8_4_58, List.forall_mem_cons.2 ⟨subd8_4_59, List.forall_mem_cons.2 ⟨subd8_4_60, List.forall_mem_cons.2 ⟨subd8_4_61, List.forall_mem_cons.2 ⟨subd8_4_62, List.forall_mem_cons.2 ⟨subd8_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_64 : subd8_4 [0, -1, 5] = true := by decide +kernel
theorem subd8_4_65 : subd8_4 [0, -1, 6] = true := by decide +kernel
theorem subd8_4_66 : subd8_4 [0, -1, 7] = true := by decide +kernel
theorem subd8_4_67 : subd8_4 [0, -1, 8] = true := by decide +kernel
theorem subd8_4_68 : subd8_4 [0, 0, -10] = true := by decide +kernel
theorem subd8_4_69 : subd8_4 [0, 0, -9] = true := by decide +kernel
theorem subd8_4_70 : subd8_4 [0, 0, -8] = true := by decide +kernel
theorem subd8_4_71 : subd8_4 [0, 0, -7] = true := by decide +kernel
theorem subd8_4_72 : subd8_4 [0, 0, -6] = true := by decide +kernel
theorem subd8_4_73 : subd8_4 [0, 0, -5] = true := by decide +kernel
theorem subd8_4_74 : subd8_4 [0, 0, -4] = true := by decide +kernel
theorem subd8_4_75 : subd8_4 [0, 0, -3] = true := by decide +kernel
theorem subd8_4_76 : subd8_4 [0, 0, -2] = true := by decide +kernel
theorem subd8_4_77 : subd8_4 [0, 0, -1] = true := by decide +kernel
theorem subd8_4_78 : subd8_4 [0, 0, 0] = true := by decide +kernel
theorem subd8_4_79 : subd8_4 [0, 0, 1] = true := by decide +kernel
theorem subd8_4_80 : subd8_4 [0, 0, 2] = true := by decide +kernel
theorem subd8_4_81 : subd8_4 [0, 0, 3] = true := by decide +kernel
theorem subd8_4_82 : subd8_4 [0, 0, 4] = true := by decide +kernel
theorem subd8_4_83 : subd8_4 [0, 0, 5] = true := by decide +kernel
theorem subd8_4_84 : subd8_4 [0, 0, 6] = true := by decide +kernel
theorem subd8_4_85 : subd8_4 [0, 0, 7] = true := by decide +kernel
theorem subd8_4_86 : subd8_4 [0, 0, 8] = true := by decide +kernel
theorem subd8_4_87 : subd8_4 [0, 0, 9] = true := by decide +kernel
theorem subd8_4_88 : subd8_4 [0, 1, -9] = true := by decide +kernel
theorem subd8_4_89 : subd8_4 [0, 1, -8] = true := by decide +kernel
theorem subd8_4_90 : subd8_4 [0, 1, -7] = true := by decide +kernel
theorem subd8_4_91 : subd8_4 [0, 1, -6] = true := by decide +kernel
theorem subd8_4_92 : subd8_4 [0, 1, -5] = true := by decide +kernel
theorem subd8_4_93 : subd8_4 [0, 1, -4] = true := by decide +kernel
theorem subd8_4_94 : subd8_4 [0, 1, -3] = true := by decide +kernel
theorem subd8_4_95 : subd8_4 [0, 1, -2] = true := by decide +kernel
theorem sbd8_4_2 : ∀ q ∈ blkd8_4_2, subd8_4 q = true := by
  unfold blkd8_4_2
  exact List.forall_mem_cons.2 ⟨subd8_4_64, List.forall_mem_cons.2 ⟨subd8_4_65, List.forall_mem_cons.2 ⟨subd8_4_66, List.forall_mem_cons.2 ⟨subd8_4_67, List.forall_mem_cons.2 ⟨subd8_4_68, List.forall_mem_cons.2 ⟨subd8_4_69, List.forall_mem_cons.2 ⟨subd8_4_70, List.forall_mem_cons.2 ⟨subd8_4_71, List.forall_mem_cons.2 ⟨subd8_4_72, List.forall_mem_cons.2 ⟨subd8_4_73, List.forall_mem_cons.2 ⟨subd8_4_74, List.forall_mem_cons.2 ⟨subd8_4_75, List.forall_mem_cons.2 ⟨subd8_4_76, List.forall_mem_cons.2 ⟨subd8_4_77, List.forall_mem_cons.2 ⟨subd8_4_78, List.forall_mem_cons.2 ⟨subd8_4_79, List.forall_mem_cons.2 ⟨subd8_4_80, List.forall_mem_cons.2 ⟨subd8_4_81, List.forall_mem_cons.2 ⟨subd8_4_82, List.forall_mem_cons.2 ⟨subd8_4_83, List.forall_mem_cons.2 ⟨subd8_4_84, List.forall_mem_cons.2 ⟨subd8_4_85, List.forall_mem_cons.2 ⟨subd8_4_86, List.forall_mem_cons.2 ⟨subd8_4_87, List.forall_mem_cons.2 ⟨subd8_4_88, List.forall_mem_cons.2 ⟨subd8_4_89, List.forall_mem_cons.2 ⟨subd8_4_90, List.forall_mem_cons.2 ⟨subd8_4_91, List.forall_mem_cons.2 ⟨subd8_4_92, List.forall_mem_cons.2 ⟨subd8_4_93, List.forall_mem_cons.2 ⟨subd8_4_94, List.forall_mem_cons.2 ⟨subd8_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_96 : subd8_4 [0, 1, -1] = true := by decide +kernel
theorem subd8_4_97 : subd8_4 [0, 1, 0] = true := by decide +kernel
theorem subd8_4_98 : subd8_4 [0, 1, 1] = true := by decide +kernel
theorem subd8_4_99 : subd8_4 [0, 1, 2] = true := by decide +kernel
theorem subd8_4_100 : subd8_4 [0, 1, 3] = true := by decide +kernel
theorem subd8_4_101 : subd8_4 [0, 1, 4] = true := by decide +kernel
theorem subd8_4_102 : subd8_4 [0, 1, 5] = true := by decide +kernel
theorem subd8_4_103 : subd8_4 [0, 1, 6] = true := by decide +kernel
theorem subd8_4_104 : subd8_4 [0, 1, 7] = true := by decide +kernel
theorem subd8_4_105 : subd8_4 [0, 1, 8] = true := by decide +kernel
theorem subd8_4_106 : subd8_4 [1, -2] = true := by decide +kernel
theorem subd8_4_107 : subd8_4 [1, -1, -7] = true := by decide +kernel
theorem subd8_4_108 : subd8_4 [1, -1, -6] = true := by decide +kernel
theorem subd8_4_109 : subd8_4 [1, -1, -5] = true := by decide +kernel
theorem subd8_4_110 : subd8_4 [1, -1, -4] = true := by decide +kernel
theorem subd8_4_111 : subd8_4 [1, -1, -3] = true := by decide +kernel
theorem subd8_4_112 : subd8_4 [1, -1, -2] = true := by decide +kernel
theorem subd8_4_113 : subd8_4 [1, -1, -1] = true := by decide +kernel
theorem subd8_4_114 : subd8_4 [1, -1, 0] = true := by decide +kernel
theorem subd8_4_115 : subd8_4 [1, -1, 1] = true := by decide +kernel
theorem subd8_4_116 : subd8_4 [1, -1, 2] = true := by decide +kernel
theorem subd8_4_117 : subd8_4 [1, -1, 3] = true := by decide +kernel
theorem subd8_4_118 : subd8_4 [1, -1, 4] = true := by decide +kernel
theorem subd8_4_119 : subd8_4 [1, -1, 5] = true := by decide +kernel
theorem subd8_4_120 : subd8_4 [1, -1, 6] = true := by decide +kernel
theorem subd8_4_121 : subd8_4 [1, -1, 7] = true := by decide +kernel
theorem subd8_4_122 : subd8_4 [1, 0, -9] = true := by decide +kernel
theorem subd8_4_123 : subd8_4 [1, 0, -8] = true := by decide +kernel
theorem subd8_4_124 : subd8_4 [1, 0, -7] = true := by decide +kernel
theorem subd8_4_125 : subd8_4 [1, 0, -6] = true := by decide +kernel
theorem subd8_4_126 : subd8_4 [1, 0, -5] = true := by decide +kernel
theorem subd8_4_127 : subd8_4 [1, 0, -4] = true := by decide +kernel
theorem sbd8_4_3 : ∀ q ∈ blkd8_4_3, subd8_4 q = true := by
  unfold blkd8_4_3
  exact List.forall_mem_cons.2 ⟨subd8_4_96, List.forall_mem_cons.2 ⟨subd8_4_97, List.forall_mem_cons.2 ⟨subd8_4_98, List.forall_mem_cons.2 ⟨subd8_4_99, List.forall_mem_cons.2 ⟨subd8_4_100, List.forall_mem_cons.2 ⟨subd8_4_101, List.forall_mem_cons.2 ⟨subd8_4_102, List.forall_mem_cons.2 ⟨subd8_4_103, List.forall_mem_cons.2 ⟨subd8_4_104, List.forall_mem_cons.2 ⟨subd8_4_105, List.forall_mem_cons.2 ⟨subd8_4_106, List.forall_mem_cons.2 ⟨subd8_4_107, List.forall_mem_cons.2 ⟨subd8_4_108, List.forall_mem_cons.2 ⟨subd8_4_109, List.forall_mem_cons.2 ⟨subd8_4_110, List.forall_mem_cons.2 ⟨subd8_4_111, List.forall_mem_cons.2 ⟨subd8_4_112, List.forall_mem_cons.2 ⟨subd8_4_113, List.forall_mem_cons.2 ⟨subd8_4_114, List.forall_mem_cons.2 ⟨subd8_4_115, List.forall_mem_cons.2 ⟨subd8_4_116, List.forall_mem_cons.2 ⟨subd8_4_117, List.forall_mem_cons.2 ⟨subd8_4_118, List.forall_mem_cons.2 ⟨subd8_4_119, List.forall_mem_cons.2 ⟨subd8_4_120, List.forall_mem_cons.2 ⟨subd8_4_121, List.forall_mem_cons.2 ⟨subd8_4_122, List.forall_mem_cons.2 ⟨subd8_4_123, List.forall_mem_cons.2 ⟨subd8_4_124, List.forall_mem_cons.2 ⟨subd8_4_125, List.forall_mem_cons.2 ⟨subd8_4_126, List.forall_mem_cons.2 ⟨subd8_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_128 : subd8_4 [1, 0, -3] = true := by decide +kernel
theorem subd8_4_129 : subd8_4 [1, 0, -2] = true := by decide +kernel
theorem subd8_4_130 : subd8_4 [1, 0, -1] = true := by decide +kernel
theorem subd8_4_131 : subd8_4 [1, 0, 0] = true := by decide +kernel
theorem subd8_4_132 : subd8_4 [1, 0, 1] = true := by decide +kernel
theorem subd8_4_133 : subd8_4 [1, 0, 2] = true := by decide +kernel
theorem subd8_4_134 : subd8_4 [1, 0, 3] = true := by decide +kernel
theorem subd8_4_135 : subd8_4 [1, 0, 4] = true := by decide +kernel
theorem subd8_4_136 : subd8_4 [1, 0, 5] = true := by decide +kernel
theorem subd8_4_137 : subd8_4 [1, 0, 6] = true := by decide +kernel
theorem subd8_4_138 : subd8_4 [1, 0, 7] = true := by decide +kernel
theorem subd8_4_139 : subd8_4 [1, 0, 8] = true := by decide +kernel
theorem subd8_4_140 : subd8_4 [1, 1, -7] = true := by decide +kernel
theorem subd8_4_141 : subd8_4 [1, 1, -6] = true := by decide +kernel
theorem subd8_4_142 : subd8_4 [1, 1, -5] = true := by decide +kernel
theorem subd8_4_143 : subd8_4 [1, 1, -4] = true := by decide +kernel
theorem subd8_4_144 : subd8_4 [1, 1, -3] = true := by decide +kernel
theorem subd8_4_145 : subd8_4 [1, 1, -2] = true := by decide +kernel
theorem subd8_4_146 : subd8_4 [1, 1, -1] = true := by decide +kernel
theorem subd8_4_147 : subd8_4 [1, 1, 0] = true := by decide +kernel
theorem subd8_4_148 : subd8_4 [1, 1, 1] = true := by decide +kernel
theorem subd8_4_149 : subd8_4 [1, 1, 2] = true := by decide +kernel
theorem subd8_4_150 : subd8_4 [1, 1, 3] = true := by decide +kernel
theorem subd8_4_151 : subd8_4 [1, 1, 4] = true := by decide +kernel
theorem subd8_4_152 : subd8_4 [1, 1, 5] = true := by decide +kernel
theorem subd8_4_153 : subd8_4 [1, 1, 6] = true := by decide +kernel
theorem subd8_4_154 : subd8_4 [1, 1, 7] = true := by decide +kernel
theorem sbd8_4_4 : ∀ q ∈ blkd8_4_4, subd8_4 q = true := by
  unfold blkd8_4_4
  exact List.forall_mem_cons.2 ⟨subd8_4_128, List.forall_mem_cons.2 ⟨subd8_4_129, List.forall_mem_cons.2 ⟨subd8_4_130, List.forall_mem_cons.2 ⟨subd8_4_131, List.forall_mem_cons.2 ⟨subd8_4_132, List.forall_mem_cons.2 ⟨subd8_4_133, List.forall_mem_cons.2 ⟨subd8_4_134, List.forall_mem_cons.2 ⟨subd8_4_135, List.forall_mem_cons.2 ⟨subd8_4_136, List.forall_mem_cons.2 ⟨subd8_4_137, List.forall_mem_cons.2 ⟨subd8_4_138, List.forall_mem_cons.2 ⟨subd8_4_139, List.forall_mem_cons.2 ⟨subd8_4_140, List.forall_mem_cons.2 ⟨subd8_4_141, List.forall_mem_cons.2 ⟨subd8_4_142, List.forall_mem_cons.2 ⟨subd8_4_143, List.forall_mem_cons.2 ⟨subd8_4_144, List.forall_mem_cons.2 ⟨subd8_4_145, List.forall_mem_cons.2 ⟨subd8_4_146, List.forall_mem_cons.2 ⟨subd8_4_147, List.forall_mem_cons.2 ⟨subd8_4_148, List.forall_mem_cons.2 ⟨subd8_4_149, List.forall_mem_cons.2 ⟨subd8_4_150, List.forall_mem_cons.2 ⟨subd8_4_151, List.forall_mem_cons.2 ⟨subd8_4_152, List.forall_mem_cons.2 ⟨subd8_4_153, List.forall_mem_cons.2 ⟨subd8_4_154, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-3] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-2] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [-1, -4] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [-1, -3] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [-1, -2] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [-1, -1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [-1, 0] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [-1, 1] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [-1, 2] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [0, -4] = true := by decide +kernel
theorem subd8_5_10 : subd8_5 [0, -3] = true := by decide +kernel
theorem subd8_5_11 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_12 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_13 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_14 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_15 : subd8_5 [0, 2] = true := by decide +kernel
theorem subd8_5_16 : subd8_5 [0, 3] = true := by decide +kernel
theorem subd8_5_17 : subd8_5 [1, -3] = true := by decide +kernel
theorem subd8_5_18 : subd8_5 [1, -2] = true := by decide +kernel
theorem subd8_5_19 : subd8_5 [1, -1] = true := by decide +kernel
theorem subd8_5_20 : subd8_5 [1, 0] = true := by decide +kernel
theorem subd8_5_21 : subd8_5 [1, 1] = true := by decide +kernel
theorem subd8_5_22 : subd8_5 [1, 2] = true := by decide +kernel
theorem subd8_5_23 : subd8_5 [1, 3] = true := by decide +kernel
theorem subd8_5_24 : subd8_5 [2] = true := by decide +kernel
theorem subd8_5_25 : subd8_5 [3] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_cons.2 ⟨subd8_5_10, List.forall_mem_cons.2 ⟨subd8_5_11, List.forall_mem_cons.2 ⟨subd8_5_12, List.forall_mem_cons.2 ⟨subd8_5_13, List.forall_mem_cons.2 ⟨subd8_5_14, List.forall_mem_cons.2 ⟨subd8_5_15, List.forall_mem_cons.2 ⟨subd8_5_16, List.forall_mem_cons.2 ⟨subd8_5_17, List.forall_mem_cons.2 ⟨subd8_5_18, List.forall_mem_cons.2 ⟨subd8_5_19, List.forall_mem_cons.2 ⟨subd8_5_20, List.forall_mem_cons.2 ⟨subd8_5_21, List.forall_mem_cons.2 ⟨subd8_5_22, List.forall_mem_cons.2 ⟨subd8_5_23, List.forall_mem_cons.2 ⟨subd8_5_24, List.forall_mem_cons.2 ⟨subd8_5_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-2] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-1, -3] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-1, -2] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [-1, -1] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [-1, 0] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [-1, 1] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [-1, 2] = true := by decide +kernel
theorem subd8_6_7 : subd8_6 [0, -3] = true := by decide +kernel
theorem subd8_6_8 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_9 : subd8_6 [0, -1] = true := by decide +kernel
theorem subd8_6_10 : subd8_6 [0, 0] = true := by decide +kernel
theorem subd8_6_11 : subd8_6 [0, 1] = true := by decide +kernel
theorem subd8_6_12 : subd8_6 [0, 2] = true := by decide +kernel
theorem subd8_6_13 : subd8_6 [1, -3] = true := by decide +kernel
theorem subd8_6_14 : subd8_6 [1, -2] = true := by decide +kernel
theorem subd8_6_15 : subd8_6 [1, -1] = true := by decide +kernel
theorem subd8_6_16 : subd8_6 [1, 0] = true := by decide +kernel
theorem subd8_6_17 : subd8_6 [1, 1] = true := by decide +kernel
theorem subd8_6_18 : subd8_6 [1, 2] = true := by decide +kernel
theorem subd8_6_19 : subd8_6 [2] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_cons.2 ⟨subd8_6_7, List.forall_mem_cons.2 ⟨subd8_6_8, List.forall_mem_cons.2 ⟨subd8_6_9, List.forall_mem_cons.2 ⟨subd8_6_10, List.forall_mem_cons.2 ⟨subd8_6_11, List.forall_mem_cons.2 ⟨subd8_6_12, List.forall_mem_cons.2 ⟨subd8_6_13, List.forall_mem_cons.2 ⟨subd8_6_14, List.forall_mem_cons.2 ⟨subd8_6_15, List.forall_mem_cons.2 ⟨subd8_6_16, List.forall_mem_cons.2 ⟨subd8_6_17, List.forall_mem_cons.2 ⟨subd8_6_18, List.forall_mem_cons.2 ⟨subd8_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel
theorem subd8_7_0 : subd8_7 [-2] = true := by decide +kernel
theorem subd8_7_1 : subd8_7 [-1] = true := by decide +kernel
theorem subd8_7_2 : subd8_7 [0, -4] = true := by decide +kernel
theorem subd8_7_3 : subd8_7 [0, -3] = true := by decide +kernel
theorem subd8_7_4 : subd8_7 [0, -2] = true := by decide +kernel
theorem subd8_7_5 : subd8_7 [0, -1] = true := by decide +kernel
theorem subd8_7_6 : subd8_7 [0, 0] = true := by decide +kernel
theorem subd8_7_7 : subd8_7 [0, 1] = true := by decide +kernel
theorem subd8_7_8 : subd8_7 [0, 2] = true := by decide +kernel
theorem subd8_7_9 : subd8_7 [0, 3] = true := by decide +kernel
theorem subd8_7_10 : subd8_7 [1] = true := by decide +kernel
theorem subd8_7_11 : subd8_7 [2] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_cons.2 ⟨subd8_7_1, List.forall_mem_cons.2 ⟨subd8_7_2, List.forall_mem_cons.2 ⟨subd8_7_3, List.forall_mem_cons.2 ⟨subd8_7_4, List.forall_mem_cons.2 ⟨subd8_7_5, List.forall_mem_cons.2 ⟨subd8_7_6, List.forall_mem_cons.2 ⟨subd8_7_7, List.forall_mem_cons.2 ⟨subd8_7_8, List.forall_mem_cons.2 ⟨subd8_7_9, List.forall_mem_cons.2 ⟨subd8_7_10, List.forall_mem_cons.2 ⟨subd8_7_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C108
