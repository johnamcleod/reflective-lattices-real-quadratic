import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_32 : subd8_2 [-2, 3] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-2, 4] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-1, -6] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-1, -5] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-1, -4] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-1, -1, -6] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-1, -1, -5] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-1, -1, -4] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-1, -1, -3] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-1, -1, -2] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-1, -1, -1] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-1, -1, 0] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-1, -1, 1] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-1, -1, 2] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-1, -1, 3] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-1, -1, 4] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-1, -1, 5] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-1, -1, 6] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-1, 3] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [-1, 4] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [0, -6] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [0, -5] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [0, -4] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [0, 0, -7] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_64 : subd8_2 [0, 0, -6] = true := by decide +kernel
theorem subd8_2_65 : subd8_2 [0, 0, -5] = true := by decide +kernel
theorem subd8_2_66 : subd8_2 [0, 0, -4] = true := by decide +kernel
theorem subd8_2_67 : subd8_2 [0, 0, -3] = true := by decide +kernel
theorem subd8_2_68 : subd8_2 [0, 0, -2] = true := by decide +kernel
theorem subd8_2_69 : subd8_2 [0, 0, -1] = true := by decide +kernel
theorem subd8_2_70 : subd8_2 [0, 0, 0] = true := by decide +kernel
theorem subd8_2_71 : subd8_2 [0, 0, 1] = true := by decide +kernel
theorem subd8_2_72 : subd8_2 [0, 0, 2] = true := by decide +kernel
theorem subd8_2_73 : subd8_2 [0, 0, 3] = true := by decide +kernel
theorem subd8_2_74 : subd8_2 [0, 0, 4] = true := by decide +kernel
theorem subd8_2_75 : subd8_2 [0, 0, 5] = true := by decide +kernel
theorem subd8_2_76 : subd8_2 [0, 0, 6] = true := by decide +kernel
theorem subd8_2_77 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_78 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_79 : subd8_2 [0, 3] = true := by decide +kernel
theorem subd8_2_80 : subd8_2 [0, 4] = true := by decide +kernel
theorem subd8_2_81 : subd8_2 [0, 5] = true := by decide +kernel
theorem subd8_2_82 : subd8_2 [1, -5] = true := by decide +kernel
theorem subd8_2_83 : subd8_2 [1, -4] = true := by decide +kernel
theorem subd8_2_84 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_85 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_86 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_87 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_88 : subd8_2 [1, 1, -7] = true := by decide +kernel
theorem subd8_2_89 : subd8_2 [1, 1, -6] = true := by decide +kernel
theorem subd8_2_90 : subd8_2 [1, 1, -5] = true := by decide +kernel
theorem subd8_2_91 : subd8_2 [1, 1, -4] = true := by decide +kernel
theorem subd8_2_92 : subd8_2 [1, 1, -3] = true := by decide +kernel
theorem subd8_2_93 : subd8_2 [1, 1, -2] = true := by decide +kernel
theorem subd8_2_94 : subd8_2 [1, 1, -1] = true := by decide +kernel
theorem subd8_2_95 : subd8_2 [1, 1, 0] = true := by decide +kernel
theorem sbd8_2_2 : ∀ q ∈ blkd8_2_2, subd8_2 q = true := by
  unfold blkd8_2_2
  exact List.forall_mem_cons.2 ⟨subd8_2_64, List.forall_mem_cons.2 ⟨subd8_2_65, List.forall_mem_cons.2 ⟨subd8_2_66, List.forall_mem_cons.2 ⟨subd8_2_67, List.forall_mem_cons.2 ⟨subd8_2_68, List.forall_mem_cons.2 ⟨subd8_2_69, List.forall_mem_cons.2 ⟨subd8_2_70, List.forall_mem_cons.2 ⟨subd8_2_71, List.forall_mem_cons.2 ⟨subd8_2_72, List.forall_mem_cons.2 ⟨subd8_2_73, List.forall_mem_cons.2 ⟨subd8_2_74, List.forall_mem_cons.2 ⟨subd8_2_75, List.forall_mem_cons.2 ⟨subd8_2_76, List.forall_mem_cons.2 ⟨subd8_2_77, List.forall_mem_cons.2 ⟨subd8_2_78, List.forall_mem_cons.2 ⟨subd8_2_79, List.forall_mem_cons.2 ⟨subd8_2_80, List.forall_mem_cons.2 ⟨subd8_2_81, List.forall_mem_cons.2 ⟨subd8_2_82, List.forall_mem_cons.2 ⟨subd8_2_83, List.forall_mem_cons.2 ⟨subd8_2_84, List.forall_mem_cons.2 ⟨subd8_2_85, List.forall_mem_cons.2 ⟨subd8_2_86, List.forall_mem_cons.2 ⟨subd8_2_87, List.forall_mem_cons.2 ⟨subd8_2_88, List.forall_mem_cons.2 ⟨subd8_2_89, List.forall_mem_cons.2 ⟨subd8_2_90, List.forall_mem_cons.2 ⟨subd8_2_91, List.forall_mem_cons.2 ⟨subd8_2_92, List.forall_mem_cons.2 ⟨subd8_2_93, List.forall_mem_cons.2 ⟨subd8_2_94, List.forall_mem_cons.2 ⟨subd8_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_96 : subd8_2 [1, 1, 1] = true := by decide +kernel
theorem subd8_2_97 : subd8_2 [1, 1, 2] = true := by decide +kernel
theorem subd8_2_98 : subd8_2 [1, 1, 3] = true := by decide +kernel
theorem subd8_2_99 : subd8_2 [1, 1, 4] = true := by decide +kernel
theorem subd8_2_100 : subd8_2 [1, 1, 5] = true := by decide +kernel
theorem subd8_2_101 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_102 : subd8_2 [1, 3] = true := by decide +kernel
theorem subd8_2_103 : subd8_2 [1, 4] = true := by decide +kernel
theorem subd8_2_104 : subd8_2 [1, 5] = true := by decide +kernel
theorem subd8_2_105 : subd8_2 [2, -5] = true := by decide +kernel
theorem subd8_2_106 : subd8_2 [2, -4] = true := by decide +kernel
theorem subd8_2_107 : subd8_2 [2, -3] = true := by decide +kernel
theorem subd8_2_108 : subd8_2 [2, -2] = true := by decide +kernel
theorem subd8_2_109 : subd8_2 [2, -1] = true := by decide +kernel
theorem subd8_2_110 : subd8_2 [2, 0] = true := by decide +kernel
theorem subd8_2_111 : subd8_2 [2, 1] = true := by decide +kernel
theorem subd8_2_112 : subd8_2 [2, 2] = true := by decide +kernel
theorem subd8_2_113 : subd8_2 [2, 3] = true := by decide +kernel
theorem subd8_2_114 : subd8_2 [2, 4] = true := by decide +kernel
theorem subd8_2_115 : subd8_2 [2, 5] = true := by decide +kernel
theorem subd8_2_116 : subd8_2 [3, -4] = true := by decide +kernel
theorem subd8_2_117 : subd8_2 [3, -3] = true := by decide +kernel
theorem subd8_2_118 : subd8_2 [3, -2] = true := by decide +kernel
theorem subd8_2_119 : subd8_2 [3, -1] = true := by decide +kernel
theorem subd8_2_120 : subd8_2 [3, 0] = true := by decide +kernel
theorem subd8_2_121 : subd8_2 [3, 1] = true := by decide +kernel
theorem subd8_2_122 : subd8_2 [3, 2] = true := by decide +kernel
theorem subd8_2_123 : subd8_2 [3, 3] = true := by decide +kernel
theorem subd8_2_124 : subd8_2 [3, 4] = true := by decide +kernel
theorem subd8_2_125 : subd8_2 [4, -3] = true := by decide +kernel
theorem subd8_2_126 : subd8_2 [4, -2] = true := by decide +kernel
theorem subd8_2_127 : subd8_2 [4, -1] = true := by decide +kernel
theorem sbd8_2_3 : ∀ q ∈ blkd8_2_3, subd8_2 q = true := by
  unfold blkd8_2_3
  exact List.forall_mem_cons.2 ⟨subd8_2_96, List.forall_mem_cons.2 ⟨subd8_2_97, List.forall_mem_cons.2 ⟨subd8_2_98, List.forall_mem_cons.2 ⟨subd8_2_99, List.forall_mem_cons.2 ⟨subd8_2_100, List.forall_mem_cons.2 ⟨subd8_2_101, List.forall_mem_cons.2 ⟨subd8_2_102, List.forall_mem_cons.2 ⟨subd8_2_103, List.forall_mem_cons.2 ⟨subd8_2_104, List.forall_mem_cons.2 ⟨subd8_2_105, List.forall_mem_cons.2 ⟨subd8_2_106, List.forall_mem_cons.2 ⟨subd8_2_107, List.forall_mem_cons.2 ⟨subd8_2_108, List.forall_mem_cons.2 ⟨subd8_2_109, List.forall_mem_cons.2 ⟨subd8_2_110, List.forall_mem_cons.2 ⟨subd8_2_111, List.forall_mem_cons.2 ⟨subd8_2_112, List.forall_mem_cons.2 ⟨subd8_2_113, List.forall_mem_cons.2 ⟨subd8_2_114, List.forall_mem_cons.2 ⟨subd8_2_115, List.forall_mem_cons.2 ⟨subd8_2_116, List.forall_mem_cons.2 ⟨subd8_2_117, List.forall_mem_cons.2 ⟨subd8_2_118, List.forall_mem_cons.2 ⟨subd8_2_119, List.forall_mem_cons.2 ⟨subd8_2_120, List.forall_mem_cons.2 ⟨subd8_2_121, List.forall_mem_cons.2 ⟨subd8_2_122, List.forall_mem_cons.2 ⟨subd8_2_123, List.forall_mem_cons.2 ⟨subd8_2_124, List.forall_mem_cons.2 ⟨subd8_2_125, List.forall_mem_cons.2 ⟨subd8_2_126, List.forall_mem_cons.2 ⟨subd8_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_128 : subd8_2 [4, 0] = true := by decide +kernel
theorem subd8_2_129 : subd8_2 [4, 1] = true := by decide +kernel
theorem subd8_2_130 : subd8_2 [4, 2] = true := by decide +kernel
theorem subd8_2_131 : subd8_2 [4, 3] = true := by decide +kernel
theorem subd8_2_132 : subd8_2 [4, 4] = true := by decide +kernel
theorem subd8_2_133 : subd8_2 [5, -2] = true := by decide +kernel
theorem subd8_2_134 : subd8_2 [5, -1] = true := by decide +kernel
theorem subd8_2_135 : subd8_2 [5, 0] = true := by decide +kernel
theorem subd8_2_136 : subd8_2 [5, 1] = true := by decide +kernel
theorem subd8_2_137 : subd8_2 [5, 2] = true := by decide +kernel
theorem subd8_2_138 : subd8_2 [5, 3] = true := by decide +kernel
theorem sbd8_2_4 : ∀ q ∈ blkd8_2_4, subd8_2 q = true := by
  unfold blkd8_2_4
  exact List.forall_mem_cons.2 ⟨subd8_2_128, List.forall_mem_cons.2 ⟨subd8_2_129, List.forall_mem_cons.2 ⟨subd8_2_130, List.forall_mem_cons.2 ⟨subd8_2_131, List.forall_mem_cons.2 ⟨subd8_2_132, List.forall_mem_cons.2 ⟨subd8_2_133, List.forall_mem_cons.2 ⟨subd8_2_134, List.forall_mem_cons.2 ⟨subd8_2_135, List.forall_mem_cons.2 ⟨subd8_2_136, List.forall_mem_cons.2 ⟨subd8_2_137, List.forall_mem_cons.2 ⟨subd8_2_138, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [0, 0, -8] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [0, 0, -7] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [0, 0, -6] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [0, 0, -5] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [0, 0, -4] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [0, 0, -3] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [0, 0, -2] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [0, 0, -1] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [0, 0, 0] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [0, 0, 1] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [0, 0, 2] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [0, 0, 3] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [0, 0, 4] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [0, 0, 5] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [0, 0, 6] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [0, 0, 7] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [1, 1] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
