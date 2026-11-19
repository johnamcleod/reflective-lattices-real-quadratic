import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [-2, -1] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-2, 0] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-2, 1] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-2, 2] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [-1, -3] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [-1, -1, -8] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [-1, -1, -7] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [-1, -1, -6] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [-1, -1, -5] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [-1, -1, -4] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [-1, -1, -3] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [-1, -1, -2] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [-1, -1, -1] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [-1, -1, 0] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [-1, -1, 1] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [-1, -1, 2] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [-1, -1, 3] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [-1, -1, 4] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [-1, -1, 5] = true := by decide +kernel
theorem subd3_0_20 : subd3_0 [-1, 0, -9] = true := by decide +kernel
theorem subd3_0_21 : subd3_0 [-1, 0, -8] = true := by decide +kernel
theorem subd3_0_22 : subd3_0 [-1, 0, -7] = true := by decide +kernel
theorem subd3_0_23 : subd3_0 [-1, 0, -6] = true := by decide +kernel
theorem subd3_0_24 : subd3_0 [-1, 0, -5] = true := by decide +kernel
theorem subd3_0_25 : subd3_0 [-1, 0, -4] = true := by decide +kernel
theorem subd3_0_26 : subd3_0 [-1, 0, -3] = true := by decide +kernel
theorem subd3_0_27 : subd3_0 [-1, 0, -2] = true := by decide +kernel
theorem subd3_0_28 : subd3_0 [-1, 0, -1] = true := by decide +kernel
theorem subd3_0_29 : subd3_0 [-1, 0, 0] = true := by decide +kernel
theorem subd3_0_30 : subd3_0 [-1, 0, 1] = true := by decide +kernel
theorem subd3_0_31 : subd3_0 [-1, 0, 2] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_cons.2 ⟨subd3_0_20, List.forall_mem_cons.2 ⟨subd3_0_21, List.forall_mem_cons.2 ⟨subd3_0_22, List.forall_mem_cons.2 ⟨subd3_0_23, List.forall_mem_cons.2 ⟨subd3_0_24, List.forall_mem_cons.2 ⟨subd3_0_25, List.forall_mem_cons.2 ⟨subd3_0_26, List.forall_mem_cons.2 ⟨subd3_0_27, List.forall_mem_cons.2 ⟨subd3_0_28, List.forall_mem_cons.2 ⟨subd3_0_29, List.forall_mem_cons.2 ⟨subd3_0_30, List.forall_mem_cons.2 ⟨subd3_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_32 : subd3_0 [-1, 0, 3] = true := by decide +kernel
theorem subd3_0_33 : subd3_0 [-1, 0, 4] = true := by decide +kernel
theorem subd3_0_34 : subd3_0 [-1, 0, 5] = true := by decide +kernel
theorem subd3_0_35 : subd3_0 [-1, 0, 6] = true := by decide +kernel
theorem subd3_0_36 : subd3_0 [-1, 0, 7] = true := by decide +kernel
theorem subd3_0_37 : subd3_0 [-1, 1, -8] = true := by decide +kernel
theorem subd3_0_38 : subd3_0 [-1, 1, -7] = true := by decide +kernel
theorem subd3_0_39 : subd3_0 [-1, 1, -6] = true := by decide +kernel
theorem subd3_0_40 : subd3_0 [-1, 1, -5] = true := by decide +kernel
theorem subd3_0_41 : subd3_0 [-1, 1, -4] = true := by decide +kernel
theorem subd3_0_42 : subd3_0 [-1, 1, -3] = true := by decide +kernel
theorem subd3_0_43 : subd3_0 [-1, 1, -2] = true := by decide +kernel
theorem subd3_0_44 : subd3_0 [-1, 1, -1] = true := by decide +kernel
theorem subd3_0_45 : subd3_0 [-1, 1, 0] = true := by decide +kernel
theorem subd3_0_46 : subd3_0 [-1, 1, 1] = true := by decide +kernel
theorem subd3_0_47 : subd3_0 [-1, 1, 2] = true := by decide +kernel
theorem subd3_0_48 : subd3_0 [-1, 1, 3] = true := by decide +kernel
theorem subd3_0_49 : subd3_0 [-1, 1, 4] = true := by decide +kernel
theorem subd3_0_50 : subd3_0 [-1, 1, 5] = true := by decide +kernel
theorem subd3_0_51 : subd3_0 [-1, 1, 6] = true := by decide +kernel
theorem subd3_0_52 : subd3_0 [-1, 1, 7] = true := by decide +kernel
theorem subd3_0_53 : subd3_0 [-1, 2] = true := by decide +kernel
theorem subd3_0_54 : subd3_0 [-1, 3] = true := by decide +kernel
theorem subd3_0_55 : subd3_0 [0, -3] = true := by decide +kernel
theorem subd3_0_56 : subd3_0 [0, -2] = true := by decide +kernel
theorem subd3_0_57 : subd3_0 [0, -1, -9] = true := by decide +kernel
theorem subd3_0_58 : subd3_0 [0, -1, -8] = true := by decide +kernel
theorem subd3_0_59 : subd3_0 [0, -1, -7] = true := by decide +kernel
theorem subd3_0_60 : subd3_0 [0, -1, -6] = true := by decide +kernel
theorem subd3_0_61 : subd3_0 [0, -1, -5] = true := by decide +kernel
theorem subd3_0_62 : subd3_0 [0, -1, -4] = true := by decide +kernel
theorem subd3_0_63 : subd3_0 [0, -1, -3] = true := by decide +kernel
theorem sbd3_0_1 : ∀ q ∈ blkd3_0_1, subd3_0 q = true := by
  unfold blkd3_0_1
  exact List.forall_mem_cons.2 ⟨subd3_0_32, List.forall_mem_cons.2 ⟨subd3_0_33, List.forall_mem_cons.2 ⟨subd3_0_34, List.forall_mem_cons.2 ⟨subd3_0_35, List.forall_mem_cons.2 ⟨subd3_0_36, List.forall_mem_cons.2 ⟨subd3_0_37, List.forall_mem_cons.2 ⟨subd3_0_38, List.forall_mem_cons.2 ⟨subd3_0_39, List.forall_mem_cons.2 ⟨subd3_0_40, List.forall_mem_cons.2 ⟨subd3_0_41, List.forall_mem_cons.2 ⟨subd3_0_42, List.forall_mem_cons.2 ⟨subd3_0_43, List.forall_mem_cons.2 ⟨subd3_0_44, List.forall_mem_cons.2 ⟨subd3_0_45, List.forall_mem_cons.2 ⟨subd3_0_46, List.forall_mem_cons.2 ⟨subd3_0_47, List.forall_mem_cons.2 ⟨subd3_0_48, List.forall_mem_cons.2 ⟨subd3_0_49, List.forall_mem_cons.2 ⟨subd3_0_50, List.forall_mem_cons.2 ⟨subd3_0_51, List.forall_mem_cons.2 ⟨subd3_0_52, List.forall_mem_cons.2 ⟨subd3_0_53, List.forall_mem_cons.2 ⟨subd3_0_54, List.forall_mem_cons.2 ⟨subd3_0_55, List.forall_mem_cons.2 ⟨subd3_0_56, List.forall_mem_cons.2 ⟨subd3_0_57, List.forall_mem_cons.2 ⟨subd3_0_58, List.forall_mem_cons.2 ⟨subd3_0_59, List.forall_mem_cons.2 ⟨subd3_0_60, List.forall_mem_cons.2 ⟨subd3_0_61, List.forall_mem_cons.2 ⟨subd3_0_62, List.forall_mem_cons.2 ⟨subd3_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_64 : subd3_0 [0, -1, -2] = true := by decide +kernel
theorem subd3_0_65 : subd3_0 [0, -1, -1] = true := by decide +kernel
theorem subd3_0_66 : subd3_0 [0, -1, 0] = true := by decide +kernel
theorem subd3_0_67 : subd3_0 [0, -1, 1] = true := by decide +kernel
theorem subd3_0_68 : subd3_0 [0, -1, 2] = true := by decide +kernel
theorem subd3_0_69 : subd3_0 [0, -1, 3] = true := by decide +kernel
theorem subd3_0_70 : subd3_0 [0, -1, 4] = true := by decide +kernel
theorem subd3_0_71 : subd3_0 [0, -1, 5] = true := by decide +kernel
theorem subd3_0_72 : subd3_0 [0, -1, 6] = true := by decide +kernel
theorem subd3_0_73 : subd3_0 [0, -1, 7] = true := by decide +kernel
theorem subd3_0_74 : subd3_0 [0, 0, -9] = true := by decide +kernel
theorem subd3_0_75 : subd3_0 [0, 0, -8] = true := by decide +kernel
theorem subd3_0_76 : subd3_0 [0, 0, -7] = true := by decide +kernel
theorem subd3_0_77 : subd3_0 [0, 0, -6] = true := by decide +kernel
theorem subd3_0_78 : subd3_0 [0, 0, -5] = true := by decide +kernel
theorem subd3_0_79 : subd3_0 [0, 0, -4] = true := by decide +kernel
theorem subd3_0_80 : subd3_0 [0, 0, -3] = true := by decide +kernel
theorem subd3_0_81 : subd3_0 [0, 0, -2] = true := by decide +kernel
theorem subd3_0_82 : subd3_0 [0, 0, -1] = true := by decide +kernel
theorem subd3_0_83 : subd3_0 [0, 0, 0] = true := by decide +kernel
theorem subd3_0_84 : subd3_0 [0, 0, 1] = true := by decide +kernel
theorem subd3_0_85 : subd3_0 [0, 0, 2] = true := by decide +kernel
theorem subd3_0_86 : subd3_0 [0, 0, 3] = true := by decide +kernel
theorem subd3_0_87 : subd3_0 [0, 0, 4] = true := by decide +kernel
theorem subd3_0_88 : subd3_0 [0, 0, 5] = true := by decide +kernel
theorem subd3_0_89 : subd3_0 [0, 0, 6] = true := by decide +kernel
theorem subd3_0_90 : subd3_0 [0, 0, 7] = true := by decide +kernel
theorem subd3_0_91 : subd3_0 [0, 0, 8] = true := by decide +kernel
theorem subd3_0_92 : subd3_0 [0, 1, -8] = true := by decide +kernel
theorem subd3_0_93 : subd3_0 [0, 1, -7] = true := by decide +kernel
theorem subd3_0_94 : subd3_0 [0, 1, -6] = true := by decide +kernel
theorem subd3_0_95 : subd3_0 [0, 1, -5] = true := by decide +kernel
theorem sbd3_0_2 : ∀ q ∈ blkd3_0_2, subd3_0 q = true := by
  unfold blkd3_0_2
  exact List.forall_mem_cons.2 ⟨subd3_0_64, List.forall_mem_cons.2 ⟨subd3_0_65, List.forall_mem_cons.2 ⟨subd3_0_66, List.forall_mem_cons.2 ⟨subd3_0_67, List.forall_mem_cons.2 ⟨subd3_0_68, List.forall_mem_cons.2 ⟨subd3_0_69, List.forall_mem_cons.2 ⟨subd3_0_70, List.forall_mem_cons.2 ⟨subd3_0_71, List.forall_mem_cons.2 ⟨subd3_0_72, List.forall_mem_cons.2 ⟨subd3_0_73, List.forall_mem_cons.2 ⟨subd3_0_74, List.forall_mem_cons.2 ⟨subd3_0_75, List.forall_mem_cons.2 ⟨subd3_0_76, List.forall_mem_cons.2 ⟨subd3_0_77, List.forall_mem_cons.2 ⟨subd3_0_78, List.forall_mem_cons.2 ⟨subd3_0_79, List.forall_mem_cons.2 ⟨subd3_0_80, List.forall_mem_cons.2 ⟨subd3_0_81, List.forall_mem_cons.2 ⟨subd3_0_82, List.forall_mem_cons.2 ⟨subd3_0_83, List.forall_mem_cons.2 ⟨subd3_0_84, List.forall_mem_cons.2 ⟨subd3_0_85, List.forall_mem_cons.2 ⟨subd3_0_86, List.forall_mem_cons.2 ⟨subd3_0_87, List.forall_mem_cons.2 ⟨subd3_0_88, List.forall_mem_cons.2 ⟨subd3_0_89, List.forall_mem_cons.2 ⟨subd3_0_90, List.forall_mem_cons.2 ⟨subd3_0_91, List.forall_mem_cons.2 ⟨subd3_0_92, List.forall_mem_cons.2 ⟨subd3_0_93, List.forall_mem_cons.2 ⟨subd3_0_94, List.forall_mem_cons.2 ⟨subd3_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_96 : subd3_0 [0, 1, -4] = true := by decide +kernel
theorem subd3_0_97 : subd3_0 [0, 1, -3] = true := by decide +kernel
theorem subd3_0_98 : subd3_0 [0, 1, -2] = true := by decide +kernel
theorem subd3_0_99 : subd3_0 [0, 1, -1] = true := by decide +kernel
theorem subd3_0_100 : subd3_0 [0, 1, 0] = true := by decide +kernel
theorem subd3_0_101 : subd3_0 [0, 1, 1] = true := by decide +kernel
theorem subd3_0_102 : subd3_0 [0, 1, 2] = true := by decide +kernel
theorem subd3_0_103 : subd3_0 [0, 1, 3] = true := by decide +kernel
theorem subd3_0_104 : subd3_0 [0, 1, 4] = true := by decide +kernel
theorem subd3_0_105 : subd3_0 [0, 1, 5] = true := by decide +kernel
theorem subd3_0_106 : subd3_0 [0, 1, 6] = true := by decide +kernel
theorem subd3_0_107 : subd3_0 [0, 1, 7] = true := by decide +kernel
theorem subd3_0_108 : subd3_0 [0, 1, 8] = true := by decide +kernel
theorem subd3_0_109 : subd3_0 [0, 2] = true := by decide +kernel
theorem subd3_0_110 : subd3_0 [1, -4] = true := by decide +kernel
theorem subd3_0_111 : subd3_0 [1, -3] = true := by decide +kernel
theorem subd3_0_112 : subd3_0 [1, -2] = true := by decide +kernel
theorem subd3_0_113 : subd3_0 [1, -1, -8] = true := by decide +kernel
theorem subd3_0_114 : subd3_0 [1, -1, -7] = true := by decide +kernel
theorem subd3_0_115 : subd3_0 [1, -1, -6] = true := by decide +kernel
theorem subd3_0_116 : subd3_0 [1, -1, -5] = true := by decide +kernel
theorem subd3_0_117 : subd3_0 [1, -1, -4] = true := by decide +kernel
theorem subd3_0_118 : subd3_0 [1, -1, -3] = true := by decide +kernel
theorem subd3_0_119 : subd3_0 [1, -1, -2] = true := by decide +kernel
theorem subd3_0_120 : subd3_0 [1, -1, -1] = true := by decide +kernel
theorem subd3_0_121 : subd3_0 [1, -1, 0] = true := by decide +kernel
theorem subd3_0_122 : subd3_0 [1, -1, 1] = true := by decide +kernel
theorem subd3_0_123 : subd3_0 [1, -1, 2] = true := by decide +kernel
theorem subd3_0_124 : subd3_0 [1, -1, 3] = true := by decide +kernel
theorem subd3_0_125 : subd3_0 [1, -1, 4] = true := by decide +kernel
theorem subd3_0_126 : subd3_0 [1, -1, 5] = true := by decide +kernel
theorem subd3_0_127 : subd3_0 [1, -1, 6] = true := by decide +kernel
theorem sbd3_0_3 : ∀ q ∈ blkd3_0_3, subd3_0 q = true := by
  unfold blkd3_0_3
  exact List.forall_mem_cons.2 ⟨subd3_0_96, List.forall_mem_cons.2 ⟨subd3_0_97, List.forall_mem_cons.2 ⟨subd3_0_98, List.forall_mem_cons.2 ⟨subd3_0_99, List.forall_mem_cons.2 ⟨subd3_0_100, List.forall_mem_cons.2 ⟨subd3_0_101, List.forall_mem_cons.2 ⟨subd3_0_102, List.forall_mem_cons.2 ⟨subd3_0_103, List.forall_mem_cons.2 ⟨subd3_0_104, List.forall_mem_cons.2 ⟨subd3_0_105, List.forall_mem_cons.2 ⟨subd3_0_106, List.forall_mem_cons.2 ⟨subd3_0_107, List.forall_mem_cons.2 ⟨subd3_0_108, List.forall_mem_cons.2 ⟨subd3_0_109, List.forall_mem_cons.2 ⟨subd3_0_110, List.forall_mem_cons.2 ⟨subd3_0_111, List.forall_mem_cons.2 ⟨subd3_0_112, List.forall_mem_cons.2 ⟨subd3_0_113, List.forall_mem_cons.2 ⟨subd3_0_114, List.forall_mem_cons.2 ⟨subd3_0_115, List.forall_mem_cons.2 ⟨subd3_0_116, List.forall_mem_cons.2 ⟨subd3_0_117, List.forall_mem_cons.2 ⟨subd3_0_118, List.forall_mem_cons.2 ⟨subd3_0_119, List.forall_mem_cons.2 ⟨subd3_0_120, List.forall_mem_cons.2 ⟨subd3_0_121, List.forall_mem_cons.2 ⟨subd3_0_122, List.forall_mem_cons.2 ⟨subd3_0_123, List.forall_mem_cons.2 ⟨subd3_0_124, List.forall_mem_cons.2 ⟨subd3_0_125, List.forall_mem_cons.2 ⟨subd3_0_126, List.forall_mem_cons.2 ⟨subd3_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_128 : subd3_0 [1, -1, 7] = true := by decide +kernel
theorem subd3_0_129 : subd3_0 [1, 0, -8] = true := by decide +kernel
theorem subd3_0_130 : subd3_0 [1, 0, -7] = true := by decide +kernel
theorem subd3_0_131 : subd3_0 [1, 0, -6] = true := by decide +kernel
theorem subd3_0_132 : subd3_0 [1, 0, -5] = true := by decide +kernel
theorem subd3_0_133 : subd3_0 [1, 0, -4] = true := by decide +kernel
theorem subd3_0_134 : subd3_0 [1, 0, -3] = true := by decide +kernel
theorem subd3_0_135 : subd3_0 [1, 0, -2] = true := by decide +kernel
theorem subd3_0_136 : subd3_0 [1, 0, -1] = true := by decide +kernel
theorem subd3_0_137 : subd3_0 [1, 0, 0] = true := by decide +kernel
theorem subd3_0_138 : subd3_0 [1, 0, 1] = true := by decide +kernel
theorem subd3_0_139 : subd3_0 [1, 0, 2] = true := by decide +kernel
theorem subd3_0_140 : subd3_0 [1, 0, 3] = true := by decide +kernel
theorem subd3_0_141 : subd3_0 [1, 0, 4] = true := by decide +kernel
theorem subd3_0_142 : subd3_0 [1, 0, 5] = true := by decide +kernel
theorem subd3_0_143 : subd3_0 [1, 0, 6] = true := by decide +kernel
theorem subd3_0_144 : subd3_0 [1, 0, 7] = true := by decide +kernel
theorem subd3_0_145 : subd3_0 [1, 0, 8] = true := by decide +kernel
theorem subd3_0_146 : subd3_0 [1, 1, -6] = true := by decide +kernel
theorem subd3_0_147 : subd3_0 [1, 1, -5] = true := by decide +kernel
theorem subd3_0_148 : subd3_0 [1, 1, -4] = true := by decide +kernel
theorem subd3_0_149 : subd3_0 [1, 1, -3] = true := by decide +kernel
theorem subd3_0_150 : subd3_0 [1, 1, -2] = true := by decide +kernel
theorem subd3_0_151 : subd3_0 [1, 1, -1] = true := by decide +kernel
theorem subd3_0_152 : subd3_0 [1, 1, 0] = true := by decide +kernel
theorem subd3_0_153 : subd3_0 [1, 1, 1] = true := by decide +kernel
theorem subd3_0_154 : subd3_0 [1, 1, 2] = true := by decide +kernel
theorem subd3_0_155 : subd3_0 [1, 1, 3] = true := by decide +kernel
theorem subd3_0_156 : subd3_0 [1, 1, 4] = true := by decide +kernel
theorem subd3_0_157 : subd3_0 [1, 1, 5] = true := by decide +kernel
theorem subd3_0_158 : subd3_0 [1, 1, 6] = true := by decide +kernel
theorem subd3_0_159 : subd3_0 [1, 1, 7] = true := by decide +kernel
theorem sbd3_0_4 : ∀ q ∈ blkd3_0_4, subd3_0 q = true := by
  unfold blkd3_0_4
  exact List.forall_mem_cons.2 ⟨subd3_0_128, List.forall_mem_cons.2 ⟨subd3_0_129, List.forall_mem_cons.2 ⟨subd3_0_130, List.forall_mem_cons.2 ⟨subd3_0_131, List.forall_mem_cons.2 ⟨subd3_0_132, List.forall_mem_cons.2 ⟨subd3_0_133, List.forall_mem_cons.2 ⟨subd3_0_134, List.forall_mem_cons.2 ⟨subd3_0_135, List.forall_mem_cons.2 ⟨subd3_0_136, List.forall_mem_cons.2 ⟨subd3_0_137, List.forall_mem_cons.2 ⟨subd3_0_138, List.forall_mem_cons.2 ⟨subd3_0_139, List.forall_mem_cons.2 ⟨subd3_0_140, List.forall_mem_cons.2 ⟨subd3_0_141, List.forall_mem_cons.2 ⟨subd3_0_142, List.forall_mem_cons.2 ⟨subd3_0_143, List.forall_mem_cons.2 ⟨subd3_0_144, List.forall_mem_cons.2 ⟨subd3_0_145, List.forall_mem_cons.2 ⟨subd3_0_146, List.forall_mem_cons.2 ⟨subd3_0_147, List.forall_mem_cons.2 ⟨subd3_0_148, List.forall_mem_cons.2 ⟨subd3_0_149, List.forall_mem_cons.2 ⟨subd3_0_150, List.forall_mem_cons.2 ⟨subd3_0_151, List.forall_mem_cons.2 ⟨subd3_0_152, List.forall_mem_cons.2 ⟨subd3_0_153, List.forall_mem_cons.2 ⟨subd3_0_154, List.forall_mem_cons.2 ⟨subd3_0_155, List.forall_mem_cons.2 ⟨subd3_0_156, List.forall_mem_cons.2 ⟨subd3_0_157, List.forall_mem_cons.2 ⟨subd3_0_158, List.forall_mem_cons.2 ⟨subd3_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_160 : subd3_0 [1, 2] = true := by decide +kernel
theorem subd3_0_161 : subd3_0 [2, -3] = true := by decide +kernel
theorem subd3_0_162 : subd3_0 [2, -2] = true := by decide +kernel
theorem subd3_0_163 : subd3_0 [2, -1] = true := by decide +kernel
theorem subd3_0_164 : subd3_0 [2, 0] = true := by decide +kernel
theorem sbd3_0_5 : ∀ q ∈ blkd3_0_5, subd3_0 q = true := by
  unfold blkd3_0_5
  exact List.forall_mem_cons.2 ⟨subd3_0_160, List.forall_mem_cons.2 ⟨subd3_0_161, List.forall_mem_cons.2 ⟨subd3_0_162, List.forall_mem_cons.2 ⟨subd3_0_163, List.forall_mem_cons.2 ⟨subd3_0_164, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [0] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [1] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2, -2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-2, -1] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-2, 0] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-2, 1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-2, 2] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [-1, -1, -7] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [-1, -1, -6] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [-1, -1, -5] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [-1, -1, -4] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [-1, -1, -3] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [-1, -1, -2] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [-1, -1, -1] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [-1, -1, 0] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [-1, -1, 1] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [-1, -1, 2] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [-1, -1, 3] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [-1, -1, 4] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [-1, -1, 5] = true := by decide +kernel
theorem subd4_0_20 : subd4_0 [-1, -1, 6] = true := by decide +kernel
theorem subd4_0_21 : subd4_0 [-1, -1, 7] = true := by decide +kernel
theorem subd4_0_22 : subd4_0 [-1, 0, -9] = true := by decide +kernel
theorem subd4_0_23 : subd4_0 [-1, 0, -8] = true := by decide +kernel
theorem subd4_0_24 : subd4_0 [-1, 0, -7] = true := by decide +kernel
theorem subd4_0_25 : subd4_0 [-1, 0, -6] = true := by decide +kernel
theorem subd4_0_26 : subd4_0 [-1, 0, -5] = true := by decide +kernel
theorem subd4_0_27 : subd4_0 [-1, 0, -4] = true := by decide +kernel
theorem subd4_0_28 : subd4_0 [-1, 0, -3] = true := by decide +kernel
theorem subd4_0_29 : subd4_0 [-1, 0, -2] = true := by decide +kernel
theorem subd4_0_30 : subd4_0 [-1, 0, -1] = true := by decide +kernel
theorem subd4_0_31 : subd4_0 [-1, 0, 0] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_cons.2 ⟨subd4_0_20, List.forall_mem_cons.2 ⟨subd4_0_21, List.forall_mem_cons.2 ⟨subd4_0_22, List.forall_mem_cons.2 ⟨subd4_0_23, List.forall_mem_cons.2 ⟨subd4_0_24, List.forall_mem_cons.2 ⟨subd4_0_25, List.forall_mem_cons.2 ⟨subd4_0_26, List.forall_mem_cons.2 ⟨subd4_0_27, List.forall_mem_cons.2 ⟨subd4_0_28, List.forall_mem_cons.2 ⟨subd4_0_29, List.forall_mem_cons.2 ⟨subd4_0_30, List.forall_mem_cons.2 ⟨subd4_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_32 : subd4_0 [-1, 0, 1] = true := by decide +kernel
theorem subd4_0_33 : subd4_0 [-1, 0, 2] = true := by decide +kernel
theorem subd4_0_34 : subd4_0 [-1, 0, 3] = true := by decide +kernel
theorem subd4_0_35 : subd4_0 [-1, 0, 4] = true := by decide +kernel
theorem subd4_0_36 : subd4_0 [-1, 0, 5] = true := by decide +kernel
theorem subd4_0_37 : subd4_0 [-1, 0, 6] = true := by decide +kernel
theorem subd4_0_38 : subd4_0 [-1, 0, 7] = true := by decide +kernel
theorem subd4_0_39 : subd4_0 [-1, 1, -9] = true := by decide +kernel
theorem subd4_0_40 : subd4_0 [-1, 1, -8] = true := by decide +kernel
theorem subd4_0_41 : subd4_0 [-1, 1, -7] = true := by decide +kernel
theorem subd4_0_42 : subd4_0 [-1, 1, -6] = true := by decide +kernel
theorem subd4_0_43 : subd4_0 [-1, 1, -5] = true := by decide +kernel
theorem subd4_0_44 : subd4_0 [-1, 1, -4] = true := by decide +kernel
theorem subd4_0_45 : subd4_0 [-1, 1, -3] = true := by decide +kernel
theorem subd4_0_46 : subd4_0 [-1, 1, -2] = true := by decide +kernel
theorem subd4_0_47 : subd4_0 [-1, 1, -1] = true := by decide +kernel
theorem subd4_0_48 : subd4_0 [-1, 1, 0] = true := by decide +kernel
theorem subd4_0_49 : subd4_0 [-1, 1, 1] = true := by decide +kernel
theorem subd4_0_50 : subd4_0 [-1, 1, 2] = true := by decide +kernel
theorem subd4_0_51 : subd4_0 [-1, 1, 3] = true := by decide +kernel
theorem subd4_0_52 : subd4_0 [-1, 1, 4] = true := by decide +kernel
theorem subd4_0_53 : subd4_0 [-1, 1, 5] = true := by decide +kernel
theorem subd4_0_54 : subd4_0 [-1, 1, 6] = true := by decide +kernel
theorem subd4_0_55 : subd4_0 [-1, 1, 7] = true := by decide +kernel
theorem subd4_0_56 : subd4_0 [-1, 2, -8] = true := by decide +kernel
theorem subd4_0_57 : subd4_0 [-1, 2, -7] = true := by decide +kernel
theorem subd4_0_58 : subd4_0 [-1, 2, -6] = true := by decide +kernel
theorem subd4_0_59 : subd4_0 [-1, 2, -5] = true := by decide +kernel
theorem subd4_0_60 : subd4_0 [-1, 2, -4] = true := by decide +kernel
theorem subd4_0_61 : subd4_0 [-1, 2, -3] = true := by decide +kernel
theorem subd4_0_62 : subd4_0 [-1, 2, -2] = true := by decide +kernel
theorem subd4_0_63 : subd4_0 [-1, 2, -1] = true := by decide +kernel
theorem sbd4_0_1 : ∀ q ∈ blkd4_0_1, subd4_0 q = true := by
  unfold blkd4_0_1
  exact List.forall_mem_cons.2 ⟨subd4_0_32, List.forall_mem_cons.2 ⟨subd4_0_33, List.forall_mem_cons.2 ⟨subd4_0_34, List.forall_mem_cons.2 ⟨subd4_0_35, List.forall_mem_cons.2 ⟨subd4_0_36, List.forall_mem_cons.2 ⟨subd4_0_37, List.forall_mem_cons.2 ⟨subd4_0_38, List.forall_mem_cons.2 ⟨subd4_0_39, List.forall_mem_cons.2 ⟨subd4_0_40, List.forall_mem_cons.2 ⟨subd4_0_41, List.forall_mem_cons.2 ⟨subd4_0_42, List.forall_mem_cons.2 ⟨subd4_0_43, List.forall_mem_cons.2 ⟨subd4_0_44, List.forall_mem_cons.2 ⟨subd4_0_45, List.forall_mem_cons.2 ⟨subd4_0_46, List.forall_mem_cons.2 ⟨subd4_0_47, List.forall_mem_cons.2 ⟨subd4_0_48, List.forall_mem_cons.2 ⟨subd4_0_49, List.forall_mem_cons.2 ⟨subd4_0_50, List.forall_mem_cons.2 ⟨subd4_0_51, List.forall_mem_cons.2 ⟨subd4_0_52, List.forall_mem_cons.2 ⟨subd4_0_53, List.forall_mem_cons.2 ⟨subd4_0_54, List.forall_mem_cons.2 ⟨subd4_0_55, List.forall_mem_cons.2 ⟨subd4_0_56, List.forall_mem_cons.2 ⟨subd4_0_57, List.forall_mem_cons.2 ⟨subd4_0_58, List.forall_mem_cons.2 ⟨subd4_0_59, List.forall_mem_cons.2 ⟨subd4_0_60, List.forall_mem_cons.2 ⟨subd4_0_61, List.forall_mem_cons.2 ⟨subd4_0_62, List.forall_mem_cons.2 ⟨subd4_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_64 : subd4_0 [-1, 2, 0] = true := by decide +kernel
theorem subd4_0_65 : subd4_0 [-1, 2, 1] = true := by decide +kernel
theorem subd4_0_66 : subd4_0 [-1, 2, 2] = true := by decide +kernel
theorem subd4_0_67 : subd4_0 [-1, 2, 3] = true := by decide +kernel
theorem subd4_0_68 : subd4_0 [-1, 2, 4] = true := by decide +kernel
theorem subd4_0_69 : subd4_0 [-1, 2, 5] = true := by decide +kernel
theorem subd4_0_70 : subd4_0 [-1, 3] = true := by decide +kernel
theorem subd4_0_71 : subd4_0 [0, -4] = true := by decide +kernel
theorem subd4_0_72 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_73 : subd4_0 [0, -2, -6] = true := by decide +kernel
theorem subd4_0_74 : subd4_0 [0, -2, -5] = true := by decide +kernel
theorem subd4_0_75 : subd4_0 [0, -2, -4] = true := by decide +kernel
theorem subd4_0_76 : subd4_0 [0, -2, -3] = true := by decide +kernel
theorem subd4_0_77 : subd4_0 [0, -2, -2] = true := by decide +kernel
theorem subd4_0_78 : subd4_0 [0, -2, -1] = true := by decide +kernel
theorem subd4_0_79 : subd4_0 [0, -2, 0] = true := by decide +kernel
theorem subd4_0_80 : subd4_0 [0, -2, 1] = true := by decide +kernel
theorem subd4_0_81 : subd4_0 [0, -2, 2] = true := by decide +kernel
theorem subd4_0_82 : subd4_0 [0, -2, 3] = true := by decide +kernel
theorem subd4_0_83 : subd4_0 [0, -2, 4] = true := by decide +kernel
theorem subd4_0_84 : subd4_0 [0, -2, 5] = true := by decide +kernel
theorem subd4_0_85 : subd4_0 [0, -2, 6] = true := by decide +kernel
theorem subd4_0_86 : subd4_0 [0, -2, 7] = true := by decide +kernel
theorem subd4_0_87 : subd4_0 [0, -1, -8] = true := by decide +kernel
theorem subd4_0_88 : subd4_0 [0, -1, -7] = true := by decide +kernel
theorem subd4_0_89 : subd4_0 [0, -1, -6] = true := by decide +kernel
theorem subd4_0_90 : subd4_0 [0, -1, -5] = true := by decide +kernel
theorem subd4_0_91 : subd4_0 [0, -1, -4] = true := by decide +kernel
theorem subd4_0_92 : subd4_0 [0, -1, -3] = true := by decide +kernel
theorem subd4_0_93 : subd4_0 [0, -1, -2] = true := by decide +kernel
theorem subd4_0_94 : subd4_0 [0, -1, -1] = true := by decide +kernel
theorem subd4_0_95 : subd4_0 [0, -1, 0] = true := by decide +kernel
theorem sbd4_0_2 : ∀ q ∈ blkd4_0_2, subd4_0 q = true := by
  unfold blkd4_0_2
  exact List.forall_mem_cons.2 ⟨subd4_0_64, List.forall_mem_cons.2 ⟨subd4_0_65, List.forall_mem_cons.2 ⟨subd4_0_66, List.forall_mem_cons.2 ⟨subd4_0_67, List.forall_mem_cons.2 ⟨subd4_0_68, List.forall_mem_cons.2 ⟨subd4_0_69, List.forall_mem_cons.2 ⟨subd4_0_70, List.forall_mem_cons.2 ⟨subd4_0_71, List.forall_mem_cons.2 ⟨subd4_0_72, List.forall_mem_cons.2 ⟨subd4_0_73, List.forall_mem_cons.2 ⟨subd4_0_74, List.forall_mem_cons.2 ⟨subd4_0_75, List.forall_mem_cons.2 ⟨subd4_0_76, List.forall_mem_cons.2 ⟨subd4_0_77, List.forall_mem_cons.2 ⟨subd4_0_78, List.forall_mem_cons.2 ⟨subd4_0_79, List.forall_mem_cons.2 ⟨subd4_0_80, List.forall_mem_cons.2 ⟨subd4_0_81, List.forall_mem_cons.2 ⟨subd4_0_82, List.forall_mem_cons.2 ⟨subd4_0_83, List.forall_mem_cons.2 ⟨subd4_0_84, List.forall_mem_cons.2 ⟨subd4_0_85, List.forall_mem_cons.2 ⟨subd4_0_86, List.forall_mem_cons.2 ⟨subd4_0_87, List.forall_mem_cons.2 ⟨subd4_0_88, List.forall_mem_cons.2 ⟨subd4_0_89, List.forall_mem_cons.2 ⟨subd4_0_90, List.forall_mem_cons.2 ⟨subd4_0_91, List.forall_mem_cons.2 ⟨subd4_0_92, List.forall_mem_cons.2 ⟨subd4_0_93, List.forall_mem_cons.2 ⟨subd4_0_94, List.forall_mem_cons.2 ⟨subd4_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
