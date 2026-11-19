import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_2_128 : subd16_2 [4, 5] = true := by decide +kernel
theorem subd16_2_129 : subd16_2 [5, -5] = true := by decide +kernel
theorem subd16_2_130 : subd16_2 [5, -4] = true := by decide +kernel
theorem subd16_2_131 : subd16_2 [5, -3] = true := by decide +kernel
theorem subd16_2_132 : subd16_2 [5, -2] = true := by decide +kernel
theorem subd16_2_133 : subd16_2 [5, -1] = true := by decide +kernel
theorem subd16_2_134 : subd16_2 [5, 0] = true := by decide +kernel
theorem subd16_2_135 : subd16_2 [5, 1] = true := by decide +kernel
theorem subd16_2_136 : subd16_2 [5, 2] = true := by decide +kernel
theorem subd16_2_137 : subd16_2 [5, 3] = true := by decide +kernel
theorem subd16_2_138 : subd16_2 [5, 4] = true := by decide +kernel
theorem subd16_2_139 : subd16_2 [6] = true := by decide +kernel
theorem sbd16_2_4 : ∀ q ∈ blkd16_2_4, subd16_2 q = true := by
  unfold blkd16_2_4
  exact List.forall_mem_cons.2 ⟨subd16_2_128, List.forall_mem_cons.2 ⟨subd16_2_129, List.forall_mem_cons.2 ⟨subd16_2_130, List.forall_mem_cons.2 ⟨subd16_2_131, List.forall_mem_cons.2 ⟨subd16_2_132, List.forall_mem_cons.2 ⟨subd16_2_133, List.forall_mem_cons.2 ⟨subd16_2_134, List.forall_mem_cons.2 ⟨subd16_2_135, List.forall_mem_cons.2 ⟨subd16_2_136, List.forall_mem_cons.2 ⟨subd16_2_137, List.forall_mem_cons.2 ⟨subd16_2_138, List.forall_mem_cons.2 ⟨subd16_2_139, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [-3, -3] = true := by decide +kernel
theorem subd16_3_1 : subd16_3 [-3, -2] = true := by decide +kernel
theorem subd16_3_2 : subd16_3 [-3, -1, -6] = true := by decide +kernel
theorem subd16_3_3 : subd16_3 [-3, -1, -5] = true := by decide +kernel
theorem subd16_3_4 : subd16_3 [-3, -1, -4] = true := by decide +kernel
theorem subd16_3_5 : subd16_3 [-3, -1, -3] = true := by decide +kernel
theorem subd16_3_6 : subd16_3 [-3, -1, -2] = true := by decide +kernel
theorem subd16_3_7 : subd16_3 [-3, -1, -1] = true := by decide +kernel
theorem subd16_3_8 : subd16_3 [-3, -1, 0] = true := by decide +kernel
theorem subd16_3_9 : subd16_3 [-3, -1, 1] = true := by decide +kernel
theorem subd16_3_10 : subd16_3 [-3, -1, 2] = true := by decide +kernel
theorem subd16_3_11 : subd16_3 [-3, -1, 3] = true := by decide +kernel
theorem subd16_3_12 : subd16_3 [-3, -1, 4] = true := by decide +kernel
theorem subd16_3_13 : subd16_3 [-3, -1, 5] = true := by decide +kernel
theorem subd16_3_14 : subd16_3 [-3, -1, 6] = true := by decide +kernel
theorem subd16_3_15 : subd16_3 [-3, -1, 7] = true := by decide +kernel
theorem subd16_3_16 : subd16_3 [-3, -1, 8] = true := by decide +kernel
theorem subd16_3_17 : subd16_3 [-3, 0, -7] = true := by decide +kernel
theorem subd16_3_18 : subd16_3 [-3, 0, -6] = true := by decide +kernel
theorem subd16_3_19 : subd16_3 [-3, 0, -5] = true := by decide +kernel
theorem subd16_3_20 : subd16_3 [-3, 0, -4] = true := by decide +kernel
theorem subd16_3_21 : subd16_3 [-3, 0, -3] = true := by decide +kernel
theorem subd16_3_22 : subd16_3 [-3, 0, -2] = true := by decide +kernel
theorem subd16_3_23 : subd16_3 [-3, 0, -1] = true := by decide +kernel
theorem subd16_3_24 : subd16_3 [-3, 0, 0] = true := by decide +kernel
theorem subd16_3_25 : subd16_3 [-3, 0, 1] = true := by decide +kernel
theorem subd16_3_26 : subd16_3 [-3, 0, 2] = true := by decide +kernel
theorem subd16_3_27 : subd16_3 [-3, 0, 3] = true := by decide +kernel
theorem subd16_3_28 : subd16_3 [-3, 0, 4] = true := by decide +kernel
theorem subd16_3_29 : subd16_3 [-3, 0, 5] = true := by decide +kernel
theorem subd16_3_30 : subd16_3 [-3, 0, 6] = true := by decide +kernel
theorem subd16_3_31 : subd16_3 [-3, 0, 7] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_cons.2 ⟨subd16_3_1, List.forall_mem_cons.2 ⟨subd16_3_2, List.forall_mem_cons.2 ⟨subd16_3_3, List.forall_mem_cons.2 ⟨subd16_3_4, List.forall_mem_cons.2 ⟨subd16_3_5, List.forall_mem_cons.2 ⟨subd16_3_6, List.forall_mem_cons.2 ⟨subd16_3_7, List.forall_mem_cons.2 ⟨subd16_3_8, List.forall_mem_cons.2 ⟨subd16_3_9, List.forall_mem_cons.2 ⟨subd16_3_10, List.forall_mem_cons.2 ⟨subd16_3_11, List.forall_mem_cons.2 ⟨subd16_3_12, List.forall_mem_cons.2 ⟨subd16_3_13, List.forall_mem_cons.2 ⟨subd16_3_14, List.forall_mem_cons.2 ⟨subd16_3_15, List.forall_mem_cons.2 ⟨subd16_3_16, List.forall_mem_cons.2 ⟨subd16_3_17, List.forall_mem_cons.2 ⟨subd16_3_18, List.forall_mem_cons.2 ⟨subd16_3_19, List.forall_mem_cons.2 ⟨subd16_3_20, List.forall_mem_cons.2 ⟨subd16_3_21, List.forall_mem_cons.2 ⟨subd16_3_22, List.forall_mem_cons.2 ⟨subd16_3_23, List.forall_mem_cons.2 ⟨subd16_3_24, List.forall_mem_cons.2 ⟨subd16_3_25, List.forall_mem_cons.2 ⟨subd16_3_26, List.forall_mem_cons.2 ⟨subd16_3_27, List.forall_mem_cons.2 ⟨subd16_3_28, List.forall_mem_cons.2 ⟨subd16_3_29, List.forall_mem_cons.2 ⟨subd16_3_30, List.forall_mem_cons.2 ⟨subd16_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_32 : subd16_3 [-3, 0, 8] = true := by decide +kernel
theorem subd16_3_33 : subd16_3 [-3, 1, -7] = true := by decide +kernel
theorem subd16_3_34 : subd16_3 [-3, 1, -6] = true := by decide +kernel
theorem subd16_3_35 : subd16_3 [-3, 1, -5] = true := by decide +kernel
theorem subd16_3_36 : subd16_3 [-3, 1, -4] = true := by decide +kernel
theorem subd16_3_37 : subd16_3 [-3, 1, -3] = true := by decide +kernel
theorem subd16_3_38 : subd16_3 [-3, 1, -2] = true := by decide +kernel
theorem subd16_3_39 : subd16_3 [-3, 1, -1] = true := by decide +kernel
theorem subd16_3_40 : subd16_3 [-3, 1, 0] = true := by decide +kernel
theorem subd16_3_41 : subd16_3 [-3, 1, 1] = true := by decide +kernel
theorem subd16_3_42 : subd16_3 [-3, 1, 2] = true := by decide +kernel
theorem subd16_3_43 : subd16_3 [-3, 1, 3] = true := by decide +kernel
theorem subd16_3_44 : subd16_3 [-3, 1, 4] = true := by decide +kernel
theorem subd16_3_45 : subd16_3 [-3, 1, 5] = true := by decide +kernel
theorem subd16_3_46 : subd16_3 [-3, 1, 6] = true := by decide +kernel
theorem subd16_3_47 : subd16_3 [-3, 1, 7] = true := by decide +kernel
theorem subd16_3_48 : subd16_3 [-3, 2] = true := by decide +kernel
theorem subd16_3_49 : subd16_3 [-2, -4] = true := by decide +kernel
theorem subd16_3_50 : subd16_3 [-2, -3] = true := by decide +kernel
theorem subd16_3_51 : subd16_3 [-2, -2, -7] = true := by decide +kernel
theorem subd16_3_52 : subd16_3 [-2, -2, -6] = true := by decide +kernel
theorem subd16_3_53 : subd16_3 [-2, -2, -5] = true := by decide +kernel
theorem subd16_3_54 : subd16_3 [-2, -2, -4] = true := by decide +kernel
theorem subd16_3_55 : subd16_3 [-2, -2, -3] = true := by decide +kernel
theorem subd16_3_56 : subd16_3 [-2, -2, -2] = true := by decide +kernel
theorem subd16_3_57 : subd16_3 [-2, -2, -1] = true := by decide +kernel
theorem subd16_3_58 : subd16_3 [-2, -2, 0] = true := by decide +kernel
theorem subd16_3_59 : subd16_3 [-2, -2, 1] = true := by decide +kernel
theorem subd16_3_60 : subd16_3 [-2, -2, 2] = true := by decide +kernel
theorem subd16_3_61 : subd16_3 [-2, -2, 3] = true := by decide +kernel
theorem subd16_3_62 : subd16_3 [-2, -2, 4] = true := by decide +kernel
theorem subd16_3_63 : subd16_3 [-2, -2, 5] = true := by decide +kernel
theorem sbd16_3_1 : ∀ q ∈ blkd16_3_1, subd16_3 q = true := by
  unfold blkd16_3_1
  exact List.forall_mem_cons.2 ⟨subd16_3_32, List.forall_mem_cons.2 ⟨subd16_3_33, List.forall_mem_cons.2 ⟨subd16_3_34, List.forall_mem_cons.2 ⟨subd16_3_35, List.forall_mem_cons.2 ⟨subd16_3_36, List.forall_mem_cons.2 ⟨subd16_3_37, List.forall_mem_cons.2 ⟨subd16_3_38, List.forall_mem_cons.2 ⟨subd16_3_39, List.forall_mem_cons.2 ⟨subd16_3_40, List.forall_mem_cons.2 ⟨subd16_3_41, List.forall_mem_cons.2 ⟨subd16_3_42, List.forall_mem_cons.2 ⟨subd16_3_43, List.forall_mem_cons.2 ⟨subd16_3_44, List.forall_mem_cons.2 ⟨subd16_3_45, List.forall_mem_cons.2 ⟨subd16_3_46, List.forall_mem_cons.2 ⟨subd16_3_47, List.forall_mem_cons.2 ⟨subd16_3_48, List.forall_mem_cons.2 ⟨subd16_3_49, List.forall_mem_cons.2 ⟨subd16_3_50, List.forall_mem_cons.2 ⟨subd16_3_51, List.forall_mem_cons.2 ⟨subd16_3_52, List.forall_mem_cons.2 ⟨subd16_3_53, List.forall_mem_cons.2 ⟨subd16_3_54, List.forall_mem_cons.2 ⟨subd16_3_55, List.forall_mem_cons.2 ⟨subd16_3_56, List.forall_mem_cons.2 ⟨subd16_3_57, List.forall_mem_cons.2 ⟨subd16_3_58, List.forall_mem_cons.2 ⟨subd16_3_59, List.forall_mem_cons.2 ⟨subd16_3_60, List.forall_mem_cons.2 ⟨subd16_3_61, List.forall_mem_cons.2 ⟨subd16_3_62, List.forall_mem_cons.2 ⟨subd16_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_64 : subd16_3 [-2, -2, 6] = true := by decide +kernel
theorem subd16_3_65 : subd16_3 [-2, -2, 7] = true := by decide +kernel
theorem subd16_3_66 : subd16_3 [-2, -2, 8] = true := by decide +kernel
theorem subd16_3_67 : subd16_3 [-2, -2, 9] = true := by decide +kernel
theorem subd16_3_68 : subd16_3 [-2, -1, -9] = true := by decide +kernel
theorem subd16_3_69 : subd16_3 [-2, -1, -8] = true := by decide +kernel
theorem subd16_3_70 : subd16_3 [-2, -1, -7] = true := by decide +kernel
theorem subd16_3_71 : subd16_3 [-2, -1, -6] = true := by decide +kernel
theorem subd16_3_72 : subd16_3 [-2, -1, -5] = true := by decide +kernel
theorem subd16_3_73 : subd16_3 [-2, -1, -4] = true := by decide +kernel
theorem subd16_3_74 : subd16_3 [-2, -1, -3] = true := by decide +kernel
theorem subd16_3_75 : subd16_3 [-2, -1, -2] = true := by decide +kernel
theorem subd16_3_76 : subd16_3 [-2, -1, -1] = true := by decide +kernel
theorem subd16_3_77 : subd16_3 [-2, -1, 0] = true := by decide +kernel
theorem subd16_3_78 : subd16_3 [-2, -1, 1] = true := by decide +kernel
theorem subd16_3_79 : subd16_3 [-2, -1, 2] = true := by decide +kernel
theorem subd16_3_80 : subd16_3 [-2, -1, 3] = true := by decide +kernel
theorem subd16_3_81 : subd16_3 [-2, -1, 4] = true := by decide +kernel
theorem subd16_3_82 : subd16_3 [-2, -1, 5] = true := by decide +kernel
theorem subd16_3_83 : subd16_3 [-2, -1, 6] = true := by decide +kernel
theorem subd16_3_84 : subd16_3 [-2, -1, 7] = true := by decide +kernel
theorem subd16_3_85 : subd16_3 [-2, -1, 8] = true := by decide +kernel
theorem subd16_3_86 : subd16_3 [-2, -1, 9] = true := by decide +kernel
theorem subd16_3_87 : subd16_3 [-2, -1, 10] = true := by decide +kernel
theorem subd16_3_88 : subd16_3 [-2, 0, -10] = true := by decide +kernel
theorem subd16_3_89 : subd16_3 [-2, 0, -9] = true := by decide +kernel
theorem subd16_3_90 : subd16_3 [-2, 0, -8] = true := by decide +kernel
theorem subd16_3_91 : subd16_3 [-2, 0, -7] = true := by decide +kernel
theorem subd16_3_92 : subd16_3 [-2, 0, -6] = true := by decide +kernel
theorem subd16_3_93 : subd16_3 [-2, 0, -5] = true := by decide +kernel
theorem subd16_3_94 : subd16_3 [-2, 0, -4] = true := by decide +kernel
theorem subd16_3_95 : subd16_3 [-2, 0, -3] = true := by decide +kernel
theorem sbd16_3_2 : ∀ q ∈ blkd16_3_2, subd16_3 q = true := by
  unfold blkd16_3_2
  exact List.forall_mem_cons.2 ⟨subd16_3_64, List.forall_mem_cons.2 ⟨subd16_3_65, List.forall_mem_cons.2 ⟨subd16_3_66, List.forall_mem_cons.2 ⟨subd16_3_67, List.forall_mem_cons.2 ⟨subd16_3_68, List.forall_mem_cons.2 ⟨subd16_3_69, List.forall_mem_cons.2 ⟨subd16_3_70, List.forall_mem_cons.2 ⟨subd16_3_71, List.forall_mem_cons.2 ⟨subd16_3_72, List.forall_mem_cons.2 ⟨subd16_3_73, List.forall_mem_cons.2 ⟨subd16_3_74, List.forall_mem_cons.2 ⟨subd16_3_75, List.forall_mem_cons.2 ⟨subd16_3_76, List.forall_mem_cons.2 ⟨subd16_3_77, List.forall_mem_cons.2 ⟨subd16_3_78, List.forall_mem_cons.2 ⟨subd16_3_79, List.forall_mem_cons.2 ⟨subd16_3_80, List.forall_mem_cons.2 ⟨subd16_3_81, List.forall_mem_cons.2 ⟨subd16_3_82, List.forall_mem_cons.2 ⟨subd16_3_83, List.forall_mem_cons.2 ⟨subd16_3_84, List.forall_mem_cons.2 ⟨subd16_3_85, List.forall_mem_cons.2 ⟨subd16_3_86, List.forall_mem_cons.2 ⟨subd16_3_87, List.forall_mem_cons.2 ⟨subd16_3_88, List.forall_mem_cons.2 ⟨subd16_3_89, List.forall_mem_cons.2 ⟨subd16_3_90, List.forall_mem_cons.2 ⟨subd16_3_91, List.forall_mem_cons.2 ⟨subd16_3_92, List.forall_mem_cons.2 ⟨subd16_3_93, List.forall_mem_cons.2 ⟨subd16_3_94, List.forall_mem_cons.2 ⟨subd16_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_96 : subd16_3 [-2, 0, -2] = true := by decide +kernel
theorem subd16_3_97 : subd16_3 [-2, 0, -1] = true := by decide +kernel
theorem subd16_3_98 : subd16_3 [-2, 0, 0] = true := by decide +kernel
theorem subd16_3_99 : subd16_3 [-2, 0, 1] = true := by decide +kernel
theorem subd16_3_100 : subd16_3 [-2, 0, 2] = true := by decide +kernel
theorem subd16_3_101 : subd16_3 [-2, 0, 3] = true := by decide +kernel
theorem subd16_3_102 : subd16_3 [-2, 0, 4] = true := by decide +kernel
theorem subd16_3_103 : subd16_3 [-2, 0, 5] = true := by decide +kernel
theorem subd16_3_104 : subd16_3 [-2, 0, 6] = true := by decide +kernel
theorem subd16_3_105 : subd16_3 [-2, 0, 7] = true := by decide +kernel
theorem subd16_3_106 : subd16_3 [-2, 0, 8] = true := by decide +kernel
theorem subd16_3_107 : subd16_3 [-2, 0, 9] = true := by decide +kernel
theorem subd16_3_108 : subd16_3 [-2, 0, 10] = true := by decide +kernel
theorem subd16_3_109 : subd16_3 [-2, 1, -10] = true := by decide +kernel
theorem subd16_3_110 : subd16_3 [-2, 1, -9] = true := by decide +kernel
theorem subd16_3_111 : subd16_3 [-2, 1, -8] = true := by decide +kernel
theorem subd16_3_112 : subd16_3 [-2, 1, -7] = true := by decide +kernel
theorem subd16_3_113 : subd16_3 [-2, 1, -6] = true := by decide +kernel
theorem subd16_3_114 : subd16_3 [-2, 1, -5] = true := by decide +kernel
theorem subd16_3_115 : subd16_3 [-2, 1, -4] = true := by decide +kernel
theorem subd16_3_116 : subd16_3 [-2, 1, -3] = true := by decide +kernel
theorem subd16_3_117 : subd16_3 [-2, 1, -2] = true := by decide +kernel
theorem subd16_3_118 : subd16_3 [-2, 1, -1] = true := by decide +kernel
theorem subd16_3_119 : subd16_3 [-2, 1, 0] = true := by decide +kernel
theorem subd16_3_120 : subd16_3 [-2, 1, 1] = true := by decide +kernel
theorem subd16_3_121 : subd16_3 [-2, 1, 2] = true := by decide +kernel
theorem subd16_3_122 : subd16_3 [-2, 1, 3] = true := by decide +kernel
theorem subd16_3_123 : subd16_3 [-2, 1, 4] = true := by decide +kernel
theorem subd16_3_124 : subd16_3 [-2, 1, 5] = true := by decide +kernel
theorem subd16_3_125 : subd16_3 [-2, 1, 6] = true := by decide +kernel
theorem subd16_3_126 : subd16_3 [-2, 1, 7] = true := by decide +kernel
theorem subd16_3_127 : subd16_3 [-2, 1, 8] = true := by decide +kernel
theorem sbd16_3_3 : ∀ q ∈ blkd16_3_3, subd16_3 q = true := by
  unfold blkd16_3_3
  exact List.forall_mem_cons.2 ⟨subd16_3_96, List.forall_mem_cons.2 ⟨subd16_3_97, List.forall_mem_cons.2 ⟨subd16_3_98, List.forall_mem_cons.2 ⟨subd16_3_99, List.forall_mem_cons.2 ⟨subd16_3_100, List.forall_mem_cons.2 ⟨subd16_3_101, List.forall_mem_cons.2 ⟨subd16_3_102, List.forall_mem_cons.2 ⟨subd16_3_103, List.forall_mem_cons.2 ⟨subd16_3_104, List.forall_mem_cons.2 ⟨subd16_3_105, List.forall_mem_cons.2 ⟨subd16_3_106, List.forall_mem_cons.2 ⟨subd16_3_107, List.forall_mem_cons.2 ⟨subd16_3_108, List.forall_mem_cons.2 ⟨subd16_3_109, List.forall_mem_cons.2 ⟨subd16_3_110, List.forall_mem_cons.2 ⟨subd16_3_111, List.forall_mem_cons.2 ⟨subd16_3_112, List.forall_mem_cons.2 ⟨subd16_3_113, List.forall_mem_cons.2 ⟨subd16_3_114, List.forall_mem_cons.2 ⟨subd16_3_115, List.forall_mem_cons.2 ⟨subd16_3_116, List.forall_mem_cons.2 ⟨subd16_3_117, List.forall_mem_cons.2 ⟨subd16_3_118, List.forall_mem_cons.2 ⟨subd16_3_119, List.forall_mem_cons.2 ⟨subd16_3_120, List.forall_mem_cons.2 ⟨subd16_3_121, List.forall_mem_cons.2 ⟨subd16_3_122, List.forall_mem_cons.2 ⟨subd16_3_123, List.forall_mem_cons.2 ⟨subd16_3_124, List.forall_mem_cons.2 ⟨subd16_3_125, List.forall_mem_cons.2 ⟨subd16_3_126, List.forall_mem_cons.2 ⟨subd16_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_128 : subd16_3 [-2, 1, 9] = true := by decide +kernel
theorem subd16_3_129 : subd16_3 [-2, 2, -9] = true := by decide +kernel
theorem subd16_3_130 : subd16_3 [-2, 2, -8] = true := by decide +kernel
theorem subd16_3_131 : subd16_3 [-2, 2, -7] = true := by decide +kernel
theorem subd16_3_132 : subd16_3 [-2, 2, -6] = true := by decide +kernel
theorem subd16_3_133 : subd16_3 [-2, 2, -5] = true := by decide +kernel
theorem subd16_3_134 : subd16_3 [-2, 2, -4] = true := by decide +kernel
theorem subd16_3_135 : subd16_3 [-2, 2, -3] = true := by decide +kernel
theorem subd16_3_136 : subd16_3 [-2, 2, -2] = true := by decide +kernel
theorem subd16_3_137 : subd16_3 [-2, 2, -1] = true := by decide +kernel
theorem subd16_3_138 : subd16_3 [-2, 2, 0] = true := by decide +kernel
theorem subd16_3_139 : subd16_3 [-2, 2, 1] = true := by decide +kernel
theorem subd16_3_140 : subd16_3 [-2, 2, 2] = true := by decide +kernel
theorem subd16_3_141 : subd16_3 [-2, 2, 3] = true := by decide +kernel
theorem subd16_3_142 : subd16_3 [-2, 2, 4] = true := by decide +kernel
theorem subd16_3_143 : subd16_3 [-2, 2, 5] = true := by decide +kernel
theorem subd16_3_144 : subd16_3 [-2, 2, 6] = true := by decide +kernel
theorem subd16_3_145 : subd16_3 [-2, 2, 7] = true := by decide +kernel
theorem subd16_3_146 : subd16_3 [-2, 3] = true := by decide +kernel
theorem subd16_3_147 : subd16_3 [-1, -4] = true := by decide +kernel
theorem subd16_3_148 : subd16_3 [-1, -3, -6] = true := by decide +kernel
theorem subd16_3_149 : subd16_3 [-1, -3, -5] = true := by decide +kernel
theorem subd16_3_150 : subd16_3 [-1, -3, -4] = true := by decide +kernel
theorem subd16_3_151 : subd16_3 [-1, -3, -3] = true := by decide +kernel
theorem subd16_3_152 : subd16_3 [-1, -3, -2] = true := by decide +kernel
theorem subd16_3_153 : subd16_3 [-1, -3, -1] = true := by decide +kernel
theorem subd16_3_154 : subd16_3 [-1, -3, 0] = true := by decide +kernel
theorem subd16_3_155 : subd16_3 [-1, -3, 1] = true := by decide +kernel
theorem subd16_3_156 : subd16_3 [-1, -3, 2] = true := by decide +kernel
theorem subd16_3_157 : subd16_3 [-1, -3, 3] = true := by decide +kernel
theorem subd16_3_158 : subd16_3 [-1, -3, 4] = true := by decide +kernel
theorem subd16_3_159 : subd16_3 [-1, -3, 5] = true := by decide +kernel
theorem sbd16_3_4 : ∀ q ∈ blkd16_3_4, subd16_3 q = true := by
  unfold blkd16_3_4
  exact List.forall_mem_cons.2 ⟨subd16_3_128, List.forall_mem_cons.2 ⟨subd16_3_129, List.forall_mem_cons.2 ⟨subd16_3_130, List.forall_mem_cons.2 ⟨subd16_3_131, List.forall_mem_cons.2 ⟨subd16_3_132, List.forall_mem_cons.2 ⟨subd16_3_133, List.forall_mem_cons.2 ⟨subd16_3_134, List.forall_mem_cons.2 ⟨subd16_3_135, List.forall_mem_cons.2 ⟨subd16_3_136, List.forall_mem_cons.2 ⟨subd16_3_137, List.forall_mem_cons.2 ⟨subd16_3_138, List.forall_mem_cons.2 ⟨subd16_3_139, List.forall_mem_cons.2 ⟨subd16_3_140, List.forall_mem_cons.2 ⟨subd16_3_141, List.forall_mem_cons.2 ⟨subd16_3_142, List.forall_mem_cons.2 ⟨subd16_3_143, List.forall_mem_cons.2 ⟨subd16_3_144, List.forall_mem_cons.2 ⟨subd16_3_145, List.forall_mem_cons.2 ⟨subd16_3_146, List.forall_mem_cons.2 ⟨subd16_3_147, List.forall_mem_cons.2 ⟨subd16_3_148, List.forall_mem_cons.2 ⟨subd16_3_149, List.forall_mem_cons.2 ⟨subd16_3_150, List.forall_mem_cons.2 ⟨subd16_3_151, List.forall_mem_cons.2 ⟨subd16_3_152, List.forall_mem_cons.2 ⟨subd16_3_153, List.forall_mem_cons.2 ⟨subd16_3_154, List.forall_mem_cons.2 ⟨subd16_3_155, List.forall_mem_cons.2 ⟨subd16_3_156, List.forall_mem_cons.2 ⟨subd16_3_157, List.forall_mem_cons.2 ⟨subd16_3_158, List.forall_mem_cons.2 ⟨subd16_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_160 : subd16_3 [-1, -3, 6] = true := by decide +kernel
theorem subd16_3_161 : subd16_3 [-1, -3, 7] = true := by decide +kernel
theorem subd16_3_162 : subd16_3 [-1, -3, 8] = true := by decide +kernel
theorem subd16_3_163 : subd16_3 [-1, -2, -9] = true := by decide +kernel
theorem subd16_3_164 : subd16_3 [-1, -2, -8] = true := by decide +kernel
theorem subd16_3_165 : subd16_3 [-1, -2, -7] = true := by decide +kernel
theorem subd16_3_166 : subd16_3 [-1, -2, -6] = true := by decide +kernel
theorem subd16_3_167 : subd16_3 [-1, -2, -5] = true := by decide +kernel
theorem subd16_3_168 : subd16_3 [-1, -2, -4] = true := by decide +kernel
theorem subd16_3_169 : subd16_3 [-1, -2, -3] = true := by decide +kernel
theorem subd16_3_170 : subd16_3 [-1, -2, -2] = true := by decide +kernel
theorem subd16_3_171 : subd16_3 [-1, -2, -1] = true := by decide +kernel
theorem subd16_3_172 : subd16_3 [-1, -2, 0] = true := by decide +kernel
theorem subd16_3_173 : subd16_3 [-1, -2, 1] = true := by decide +kernel
theorem subd16_3_174 : subd16_3 [-1, -2, 2] = true := by decide +kernel
theorem subd16_3_175 : subd16_3 [-1, -2, 3] = true := by decide +kernel
theorem subd16_3_176 : subd16_3 [-1, -2, 4] = true := by decide +kernel
theorem subd16_3_177 : subd16_3 [-1, -2, 5] = true := by decide +kernel
theorem subd16_3_178 : subd16_3 [-1, -2, 6] = true := by decide +kernel
theorem subd16_3_179 : subd16_3 [-1, -2, 7] = true := by decide +kernel
theorem subd16_3_180 : subd16_3 [-1, -2, 8] = true := by decide +kernel
theorem subd16_3_181 : subd16_3 [-1, -2, 9] = true := by decide +kernel
theorem subd16_3_182 : subd16_3 [-1, -2, 10] = true := by decide +kernel
theorem subd16_3_183 : subd16_3 [-1, -2, 11] = true := by decide +kernel
theorem subd16_3_184 : subd16_3 [-1, -1, -11] = true := by decide +kernel
theorem subd16_3_185 : subd16_3 [-1, -1, -10] = true := by decide +kernel
theorem subd16_3_186 : subd16_3 [-1, -1, -9] = true := by decide +kernel
theorem subd16_3_187 : subd16_3 [-1, -1, -8] = true := by decide +kernel
theorem subd16_3_188 : subd16_3 [-1, -1, -7] = true := by decide +kernel
theorem subd16_3_189 : subd16_3 [-1, -1, -6] = true := by decide +kernel
theorem subd16_3_190 : subd16_3 [-1, -1, -5] = true := by decide +kernel
theorem subd16_3_191 : subd16_3 [-1, -1, -4] = true := by decide +kernel
theorem sbd16_3_5 : ∀ q ∈ blkd16_3_5, subd16_3 q = true := by
  unfold blkd16_3_5
  exact List.forall_mem_cons.2 ⟨subd16_3_160, List.forall_mem_cons.2 ⟨subd16_3_161, List.forall_mem_cons.2 ⟨subd16_3_162, List.forall_mem_cons.2 ⟨subd16_3_163, List.forall_mem_cons.2 ⟨subd16_3_164, List.forall_mem_cons.2 ⟨subd16_3_165, List.forall_mem_cons.2 ⟨subd16_3_166, List.forall_mem_cons.2 ⟨subd16_3_167, List.forall_mem_cons.2 ⟨subd16_3_168, List.forall_mem_cons.2 ⟨subd16_3_169, List.forall_mem_cons.2 ⟨subd16_3_170, List.forall_mem_cons.2 ⟨subd16_3_171, List.forall_mem_cons.2 ⟨subd16_3_172, List.forall_mem_cons.2 ⟨subd16_3_173, List.forall_mem_cons.2 ⟨subd16_3_174, List.forall_mem_cons.2 ⟨subd16_3_175, List.forall_mem_cons.2 ⟨subd16_3_176, List.forall_mem_cons.2 ⟨subd16_3_177, List.forall_mem_cons.2 ⟨subd16_3_178, List.forall_mem_cons.2 ⟨subd16_3_179, List.forall_mem_cons.2 ⟨subd16_3_180, List.forall_mem_cons.2 ⟨subd16_3_181, List.forall_mem_cons.2 ⟨subd16_3_182, List.forall_mem_cons.2 ⟨subd16_3_183, List.forall_mem_cons.2 ⟨subd16_3_184, List.forall_mem_cons.2 ⟨subd16_3_185, List.forall_mem_cons.2 ⟨subd16_3_186, List.forall_mem_cons.2 ⟨subd16_3_187, List.forall_mem_cons.2 ⟨subd16_3_188, List.forall_mem_cons.2 ⟨subd16_3_189, List.forall_mem_cons.2 ⟨subd16_3_190, List.forall_mem_cons.2 ⟨subd16_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_192 : subd16_3 [-1, -1, -3] = true := by decide +kernel
theorem subd16_3_193 : subd16_3 [-1, -1, -2] = true := by decide +kernel
theorem subd16_3_194 : subd16_3 [-1, -1, -1] = true := by decide +kernel
theorem subd16_3_195 : subd16_3 [-1, -1, 0] = true := by decide +kernel
theorem subd16_3_196 : subd16_3 [-1, -1, 1] = true := by decide +kernel
theorem subd16_3_197 : subd16_3 [-1, -1, 2] = true := by decide +kernel
theorem subd16_3_198 : subd16_3 [-1, -1, 3] = true := by decide +kernel
theorem subd16_3_199 : subd16_3 [-1, -1, 4] = true := by decide +kernel
theorem subd16_3_200 : subd16_3 [-1, -1, 5] = true := by decide +kernel
theorem subd16_3_201 : subd16_3 [-1, -1, 6] = true := by decide +kernel
theorem subd16_3_202 : subd16_3 [-1, -1, 7] = true := by decide +kernel
theorem subd16_3_203 : subd16_3 [-1, -1, 8] = true := by decide +kernel
theorem subd16_3_204 : subd16_3 [-1, -1, 9] = true := by decide +kernel
theorem subd16_3_205 : subd16_3 [-1, -1, 10] = true := by decide +kernel
theorem subd16_3_206 : subd16_3 [-1, -1, 11] = true := by decide +kernel
theorem subd16_3_207 : subd16_3 [-1, 0, -12] = true := by decide +kernel
theorem subd16_3_208 : subd16_3 [-1, 0, -11] = true := by decide +kernel
theorem subd16_3_209 : subd16_3 [-1, 0, -10] = true := by decide +kernel
theorem subd16_3_210 : subd16_3 [-1, 0, -9] = true := by decide +kernel
theorem subd16_3_211 : subd16_3 [-1, 0, -8] = true := by decide +kernel
theorem subd16_3_212 : subd16_3 [-1, 0, -7] = true := by decide +kernel
theorem subd16_3_213 : subd16_3 [-1, 0, -6] = true := by decide +kernel
theorem subd16_3_214 : subd16_3 [-1, 0, -5] = true := by decide +kernel
theorem subd16_3_215 : subd16_3 [-1, 0, -4] = true := by decide +kernel
theorem subd16_3_216 : subd16_3 [-1, 0, -3] = true := by decide +kernel
theorem subd16_3_217 : subd16_3 [-1, 0, -2] = true := by decide +kernel
theorem subd16_3_218 : subd16_3 [-1, 0, -1] = true := by decide +kernel
theorem subd16_3_219 : subd16_3 [-1, 0, 0] = true := by decide +kernel
theorem subd16_3_220 : subd16_3 [-1, 0, 1] = true := by decide +kernel
theorem subd16_3_221 : subd16_3 [-1, 0, 2] = true := by decide +kernel
theorem subd16_3_222 : subd16_3 [-1, 0, 3] = true := by decide +kernel
theorem subd16_3_223 : subd16_3 [-1, 0, 4] = true := by decide +kernel
theorem sbd16_3_6 : ∀ q ∈ blkd16_3_6, subd16_3 q = true := by
  unfold blkd16_3_6
  exact List.forall_mem_cons.2 ⟨subd16_3_192, List.forall_mem_cons.2 ⟨subd16_3_193, List.forall_mem_cons.2 ⟨subd16_3_194, List.forall_mem_cons.2 ⟨subd16_3_195, List.forall_mem_cons.2 ⟨subd16_3_196, List.forall_mem_cons.2 ⟨subd16_3_197, List.forall_mem_cons.2 ⟨subd16_3_198, List.forall_mem_cons.2 ⟨subd16_3_199, List.forall_mem_cons.2 ⟨subd16_3_200, List.forall_mem_cons.2 ⟨subd16_3_201, List.forall_mem_cons.2 ⟨subd16_3_202, List.forall_mem_cons.2 ⟨subd16_3_203, List.forall_mem_cons.2 ⟨subd16_3_204, List.forall_mem_cons.2 ⟨subd16_3_205, List.forall_mem_cons.2 ⟨subd16_3_206, List.forall_mem_cons.2 ⟨subd16_3_207, List.forall_mem_cons.2 ⟨subd16_3_208, List.forall_mem_cons.2 ⟨subd16_3_209, List.forall_mem_cons.2 ⟨subd16_3_210, List.forall_mem_cons.2 ⟨subd16_3_211, List.forall_mem_cons.2 ⟨subd16_3_212, List.forall_mem_cons.2 ⟨subd16_3_213, List.forall_mem_cons.2 ⟨subd16_3_214, List.forall_mem_cons.2 ⟨subd16_3_215, List.forall_mem_cons.2 ⟨subd16_3_216, List.forall_mem_cons.2 ⟨subd16_3_217, List.forall_mem_cons.2 ⟨subd16_3_218, List.forall_mem_cons.2 ⟨subd16_3_219, List.forall_mem_cons.2 ⟨subd16_3_220, List.forall_mem_cons.2 ⟨subd16_3_221, List.forall_mem_cons.2 ⟨subd16_3_222, List.forall_mem_cons.2 ⟨subd16_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_224 : subd16_3 [-1, 0, 5] = true := by decide +kernel
theorem subd16_3_225 : subd16_3 [-1, 0, 6] = true := by decide +kernel
theorem subd16_3_226 : subd16_3 [-1, 0, 7] = true := by decide +kernel
theorem subd16_3_227 : subd16_3 [-1, 0, 8] = true := by decide +kernel
theorem subd16_3_228 : subd16_3 [-1, 0, 9] = true := by decide +kernel
theorem subd16_3_229 : subd16_3 [-1, 0, 10] = true := by decide +kernel
theorem subd16_3_230 : subd16_3 [-1, 0, 11] = true := by decide +kernel
theorem subd16_3_231 : subd16_3 [-1, 1, -12] = true := by decide +kernel
theorem subd16_3_232 : subd16_3 [-1, 1, -11] = true := by decide +kernel
theorem subd16_3_233 : subd16_3 [-1, 1, -10] = true := by decide +kernel
theorem subd16_3_234 : subd16_3 [-1, 1, -9] = true := by decide +kernel
theorem subd16_3_235 : subd16_3 [-1, 1, -8] = true := by decide +kernel
theorem subd16_3_236 : subd16_3 [-1, 1, -7] = true := by decide +kernel
theorem subd16_3_237 : subd16_3 [-1, 1, -6] = true := by decide +kernel
theorem subd16_3_238 : subd16_3 [-1, 1, -5] = true := by decide +kernel
theorem subd16_3_239 : subd16_3 [-1, 1, -4] = true := by decide +kernel
theorem subd16_3_240 : subd16_3 [-1, 1, -3] = true := by decide +kernel
theorem subd16_3_241 : subd16_3 [-1, 1, -2] = true := by decide +kernel
theorem subd16_3_242 : subd16_3 [-1, 1, -1] = true := by decide +kernel
theorem subd16_3_243 : subd16_3 [-1, 1, 0] = true := by decide +kernel
theorem subd16_3_244 : subd16_3 [-1, 1, 1] = true := by decide +kernel
theorem subd16_3_245 : subd16_3 [-1, 1, 2] = true := by decide +kernel
theorem subd16_3_246 : subd16_3 [-1, 1, 3] = true := by decide +kernel
theorem subd16_3_247 : subd16_3 [-1, 1, 4] = true := by decide +kernel
theorem subd16_3_248 : subd16_3 [-1, 1, 5] = true := by decide +kernel
theorem subd16_3_249 : subd16_3 [-1, 1, 6] = true := by decide +kernel
theorem subd16_3_250 : subd16_3 [-1, 1, 7] = true := by decide +kernel
theorem subd16_3_251 : subd16_3 [-1, 1, 8] = true := by decide +kernel
theorem subd16_3_252 : subd16_3 [-1, 1, 9] = true := by decide +kernel
theorem subd16_3_253 : subd16_3 [-1, 1, 10] = true := by decide +kernel
theorem subd16_3_254 : subd16_3 [-1, 2, -11] = true := by decide +kernel
theorem subd16_3_255 : subd16_3 [-1, 2, -10] = true := by decide +kernel
theorem sbd16_3_7 : ∀ q ∈ blkd16_3_7, subd16_3 q = true := by
  unfold blkd16_3_7
  exact List.forall_mem_cons.2 ⟨subd16_3_224, List.forall_mem_cons.2 ⟨subd16_3_225, List.forall_mem_cons.2 ⟨subd16_3_226, List.forall_mem_cons.2 ⟨subd16_3_227, List.forall_mem_cons.2 ⟨subd16_3_228, List.forall_mem_cons.2 ⟨subd16_3_229, List.forall_mem_cons.2 ⟨subd16_3_230, List.forall_mem_cons.2 ⟨subd16_3_231, List.forall_mem_cons.2 ⟨subd16_3_232, List.forall_mem_cons.2 ⟨subd16_3_233, List.forall_mem_cons.2 ⟨subd16_3_234, List.forall_mem_cons.2 ⟨subd16_3_235, List.forall_mem_cons.2 ⟨subd16_3_236, List.forall_mem_cons.2 ⟨subd16_3_237, List.forall_mem_cons.2 ⟨subd16_3_238, List.forall_mem_cons.2 ⟨subd16_3_239, List.forall_mem_cons.2 ⟨subd16_3_240, List.forall_mem_cons.2 ⟨subd16_3_241, List.forall_mem_cons.2 ⟨subd16_3_242, List.forall_mem_cons.2 ⟨subd16_3_243, List.forall_mem_cons.2 ⟨subd16_3_244, List.forall_mem_cons.2 ⟨subd16_3_245, List.forall_mem_cons.2 ⟨subd16_3_246, List.forall_mem_cons.2 ⟨subd16_3_247, List.forall_mem_cons.2 ⟨subd16_3_248, List.forall_mem_cons.2 ⟨subd16_3_249, List.forall_mem_cons.2 ⟨subd16_3_250, List.forall_mem_cons.2 ⟨subd16_3_251, List.forall_mem_cons.2 ⟨subd16_3_252, List.forall_mem_cons.2 ⟨subd16_3_253, List.forall_mem_cons.2 ⟨subd16_3_254, List.forall_mem_cons.2 ⟨subd16_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_256 : subd16_3 [-1, 2, -9] = true := by decide +kernel
theorem subd16_3_257 : subd16_3 [-1, 2, -8] = true := by decide +kernel
theorem subd16_3_258 : subd16_3 [-1, 2, -7] = true := by decide +kernel
theorem subd16_3_259 : subd16_3 [-1, 2, -6] = true := by decide +kernel
theorem subd16_3_260 : subd16_3 [-1, 2, -5] = true := by decide +kernel
theorem subd16_3_261 : subd16_3 [-1, 2, -4] = true := by decide +kernel
theorem subd16_3_262 : subd16_3 [-1, 2, -3] = true := by decide +kernel
theorem subd16_3_263 : subd16_3 [-1, 2, -2] = true := by decide +kernel
theorem subd16_3_264 : subd16_3 [-1, 2, -1] = true := by decide +kernel
theorem subd16_3_265 : subd16_3 [-1, 2, 0] = true := by decide +kernel
theorem subd16_3_266 : subd16_3 [-1, 2, 1] = true := by decide +kernel
theorem subd16_3_267 : subd16_3 [-1, 2, 2] = true := by decide +kernel
theorem subd16_3_268 : subd16_3 [-1, 2, 3] = true := by decide +kernel
theorem subd16_3_269 : subd16_3 [-1, 2, 4] = true := by decide +kernel
theorem subd16_3_270 : subd16_3 [-1, 2, 5] = true := by decide +kernel
theorem subd16_3_271 : subd16_3 [-1, 2, 6] = true := by decide +kernel
theorem subd16_3_272 : subd16_3 [-1, 2, 7] = true := by decide +kernel
theorem subd16_3_273 : subd16_3 [-1, 2, 8] = true := by decide +kernel
theorem subd16_3_274 : subd16_3 [-1, 2, 9] = true := by decide +kernel
theorem subd16_3_275 : subd16_3 [-1, 3, -9] = true := by decide +kernel
theorem subd16_3_276 : subd16_3 [-1, 3, -8] = true := by decide +kernel
theorem subd16_3_277 : subd16_3 [-1, 3, -7] = true := by decide +kernel
theorem subd16_3_278 : subd16_3 [-1, 3, -6] = true := by decide +kernel
theorem subd16_3_279 : subd16_3 [-1, 3, -5] = true := by decide +kernel
theorem subd16_3_280 : subd16_3 [-1, 3, -4] = true := by decide +kernel
theorem subd16_3_281 : subd16_3 [-1, 3, -3] = true := by decide +kernel
theorem subd16_3_282 : subd16_3 [-1, 3, -2] = true := by decide +kernel
theorem subd16_3_283 : subd16_3 [-1, 3, -1] = true := by decide +kernel
theorem subd16_3_284 : subd16_3 [-1, 3, 0] = true := by decide +kernel
theorem subd16_3_285 : subd16_3 [-1, 3, 1] = true := by decide +kernel
theorem subd16_3_286 : subd16_3 [-1, 3, 2] = true := by decide +kernel
theorem subd16_3_287 : subd16_3 [-1, 3, 3] = true := by decide +kernel
theorem sbd16_3_8 : ∀ q ∈ blkd16_3_8, subd16_3 q = true := by
  unfold blkd16_3_8
  exact List.forall_mem_cons.2 ⟨subd16_3_256, List.forall_mem_cons.2 ⟨subd16_3_257, List.forall_mem_cons.2 ⟨subd16_3_258, List.forall_mem_cons.2 ⟨subd16_3_259, List.forall_mem_cons.2 ⟨subd16_3_260, List.forall_mem_cons.2 ⟨subd16_3_261, List.forall_mem_cons.2 ⟨subd16_3_262, List.forall_mem_cons.2 ⟨subd16_3_263, List.forall_mem_cons.2 ⟨subd16_3_264, List.forall_mem_cons.2 ⟨subd16_3_265, List.forall_mem_cons.2 ⟨subd16_3_266, List.forall_mem_cons.2 ⟨subd16_3_267, List.forall_mem_cons.2 ⟨subd16_3_268, List.forall_mem_cons.2 ⟨subd16_3_269, List.forall_mem_cons.2 ⟨subd16_3_270, List.forall_mem_cons.2 ⟨subd16_3_271, List.forall_mem_cons.2 ⟨subd16_3_272, List.forall_mem_cons.2 ⟨subd16_3_273, List.forall_mem_cons.2 ⟨subd16_3_274, List.forall_mem_cons.2 ⟨subd16_3_275, List.forall_mem_cons.2 ⟨subd16_3_276, List.forall_mem_cons.2 ⟨subd16_3_277, List.forall_mem_cons.2 ⟨subd16_3_278, List.forall_mem_cons.2 ⟨subd16_3_279, List.forall_mem_cons.2 ⟨subd16_3_280, List.forall_mem_cons.2 ⟨subd16_3_281, List.forall_mem_cons.2 ⟨subd16_3_282, List.forall_mem_cons.2 ⟨subd16_3_283, List.forall_mem_cons.2 ⟨subd16_3_284, List.forall_mem_cons.2 ⟨subd16_3_285, List.forall_mem_cons.2 ⟨subd16_3_286, List.forall_mem_cons.2 ⟨subd16_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_288 : subd16_3 [-1, 3, 4] = true := by decide +kernel
theorem subd16_3_289 : subd16_3 [-1, 3, 5] = true := by decide +kernel
theorem subd16_3_290 : subd16_3 [0, -4] = true := by decide +kernel
theorem subd16_3_291 : subd16_3 [0, -3, -7] = true := by decide +kernel
theorem subd16_3_292 : subd16_3 [0, -3, -6] = true := by decide +kernel
theorem subd16_3_293 : subd16_3 [0, -3, -5] = true := by decide +kernel
theorem subd16_3_294 : subd16_3 [0, -3, -4] = true := by decide +kernel
theorem subd16_3_295 : subd16_3 [0, -3, -3] = true := by decide +kernel
theorem subd16_3_296 : subd16_3 [0, -3, -2] = true := by decide +kernel
theorem subd16_3_297 : subd16_3 [0, -3, -1] = true := by decide +kernel
theorem subd16_3_298 : subd16_3 [0, -3, 0] = true := by decide +kernel
theorem subd16_3_299 : subd16_3 [0, -3, 1] = true := by decide +kernel
theorem subd16_3_300 : subd16_3 [0, -3, 2] = true := by decide +kernel
theorem subd16_3_301 : subd16_3 [0, -3, 3] = true := by decide +kernel
theorem subd16_3_302 : subd16_3 [0, -3, 4] = true := by decide +kernel
theorem subd16_3_303 : subd16_3 [0, -3, 5] = true := by decide +kernel
theorem subd16_3_304 : subd16_3 [0, -3, 6] = true := by decide +kernel
theorem subd16_3_305 : subd16_3 [0, -3, 7] = true := by decide +kernel
theorem subd16_3_306 : subd16_3 [0, -3, 8] = true := by decide +kernel
theorem subd16_3_307 : subd16_3 [0, -3, 9] = true := by decide +kernel
theorem subd16_3_308 : subd16_3 [0, -2, -10] = true := by decide +kernel
theorem subd16_3_309 : subd16_3 [0, -2, -9] = true := by decide +kernel
theorem subd16_3_310 : subd16_3 [0, -2, -8] = true := by decide +kernel
theorem subd16_3_311 : subd16_3 [0, -2, -7] = true := by decide +kernel
theorem subd16_3_312 : subd16_3 [0, -2, -6] = true := by decide +kernel
theorem subd16_3_313 : subd16_3 [0, -2, -5] = true := by decide +kernel
theorem subd16_3_314 : subd16_3 [0, -2, -4] = true := by decide +kernel
theorem subd16_3_315 : subd16_3 [0, -2, -3] = true := by decide +kernel
theorem subd16_3_316 : subd16_3 [0, -2, -2] = true := by decide +kernel
theorem subd16_3_317 : subd16_3 [0, -2, -1] = true := by decide +kernel
theorem subd16_3_318 : subd16_3 [0, -2, 0] = true := by decide +kernel
theorem subd16_3_319 : subd16_3 [0, -2, 1] = true := by decide +kernel
theorem sbd16_3_9 : ∀ q ∈ blkd16_3_9, subd16_3 q = true := by
  unfold blkd16_3_9
  exact List.forall_mem_cons.2 ⟨subd16_3_288, List.forall_mem_cons.2 ⟨subd16_3_289, List.forall_mem_cons.2 ⟨subd16_3_290, List.forall_mem_cons.2 ⟨subd16_3_291, List.forall_mem_cons.2 ⟨subd16_3_292, List.forall_mem_cons.2 ⟨subd16_3_293, List.forall_mem_cons.2 ⟨subd16_3_294, List.forall_mem_cons.2 ⟨subd16_3_295, List.forall_mem_cons.2 ⟨subd16_3_296, List.forall_mem_cons.2 ⟨subd16_3_297, List.forall_mem_cons.2 ⟨subd16_3_298, List.forall_mem_cons.2 ⟨subd16_3_299, List.forall_mem_cons.2 ⟨subd16_3_300, List.forall_mem_cons.2 ⟨subd16_3_301, List.forall_mem_cons.2 ⟨subd16_3_302, List.forall_mem_cons.2 ⟨subd16_3_303, List.forall_mem_cons.2 ⟨subd16_3_304, List.forall_mem_cons.2 ⟨subd16_3_305, List.forall_mem_cons.2 ⟨subd16_3_306, List.forall_mem_cons.2 ⟨subd16_3_307, List.forall_mem_cons.2 ⟨subd16_3_308, List.forall_mem_cons.2 ⟨subd16_3_309, List.forall_mem_cons.2 ⟨subd16_3_310, List.forall_mem_cons.2 ⟨subd16_3_311, List.forall_mem_cons.2 ⟨subd16_3_312, List.forall_mem_cons.2 ⟨subd16_3_313, List.forall_mem_cons.2 ⟨subd16_3_314, List.forall_mem_cons.2 ⟨subd16_3_315, List.forall_mem_cons.2 ⟨subd16_3_316, List.forall_mem_cons.2 ⟨subd16_3_317, List.forall_mem_cons.2 ⟨subd16_3_318, List.forall_mem_cons.2 ⟨subd16_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_320 : subd16_3 [0, -2, 2] = true := by decide +kernel
theorem subd16_3_321 : subd16_3 [0, -2, 3] = true := by decide +kernel
theorem subd16_3_322 : subd16_3 [0, -2, 4] = true := by decide +kernel
theorem subd16_3_323 : subd16_3 [0, -2, 5] = true := by decide +kernel
theorem subd16_3_324 : subd16_3 [0, -2, 6] = true := by decide +kernel
theorem subd16_3_325 : subd16_3 [0, -2, 7] = true := by decide +kernel
theorem subd16_3_326 : subd16_3 [0, -2, 8] = true := by decide +kernel
theorem subd16_3_327 : subd16_3 [0, -2, 9] = true := by decide +kernel
theorem subd16_3_328 : subd16_3 [0, -2, 10] = true := by decide +kernel
theorem subd16_3_329 : subd16_3 [0, -2, 11] = true := by decide +kernel
theorem subd16_3_330 : subd16_3 [0, -1, -12] = true := by decide +kernel
theorem subd16_3_331 : subd16_3 [0, -1, -11] = true := by decide +kernel
theorem subd16_3_332 : subd16_3 [0, -1, -10] = true := by decide +kernel
theorem subd16_3_333 : subd16_3 [0, -1, -9] = true := by decide +kernel
theorem subd16_3_334 : subd16_3 [0, -1, -8] = true := by decide +kernel
theorem subd16_3_335 : subd16_3 [0, -1, -7] = true := by decide +kernel
theorem subd16_3_336 : subd16_3 [0, -1, -6] = true := by decide +kernel
theorem subd16_3_337 : subd16_3 [0, -1, -5] = true := by decide +kernel
theorem subd16_3_338 : subd16_3 [0, -1, -4] = true := by decide +kernel
theorem subd16_3_339 : subd16_3 [0, -1, -3] = true := by decide +kernel
theorem subd16_3_340 : subd16_3 [0, -1, -2] = true := by decide +kernel
theorem subd16_3_341 : subd16_3 [0, -1, -1] = true := by decide +kernel
theorem subd16_3_342 : subd16_3 [0, -1, 0] = true := by decide +kernel
theorem subd16_3_343 : subd16_3 [0, -1, 1] = true := by decide +kernel
theorem subd16_3_344 : subd16_3 [0, -1, 2] = true := by decide +kernel
theorem subd16_3_345 : subd16_3 [0, -1, 3] = true := by decide +kernel
theorem subd16_3_346 : subd16_3 [0, -1, 4] = true := by decide +kernel
theorem subd16_3_347 : subd16_3 [0, -1, 5] = true := by decide +kernel
theorem subd16_3_348 : subd16_3 [0, -1, 6] = true := by decide +kernel
theorem subd16_3_349 : subd16_3 [0, -1, 7] = true := by decide +kernel
theorem subd16_3_350 : subd16_3 [0, -1, 8] = true := by decide +kernel
theorem subd16_3_351 : subd16_3 [0, -1, 9] = true := by decide +kernel
theorem sbd16_3_10 : ∀ q ∈ blkd16_3_10, subd16_3 q = true := by
  unfold blkd16_3_10
  exact List.forall_mem_cons.2 ⟨subd16_3_320, List.forall_mem_cons.2 ⟨subd16_3_321, List.forall_mem_cons.2 ⟨subd16_3_322, List.forall_mem_cons.2 ⟨subd16_3_323, List.forall_mem_cons.2 ⟨subd16_3_324, List.forall_mem_cons.2 ⟨subd16_3_325, List.forall_mem_cons.2 ⟨subd16_3_326, List.forall_mem_cons.2 ⟨subd16_3_327, List.forall_mem_cons.2 ⟨subd16_3_328, List.forall_mem_cons.2 ⟨subd16_3_329, List.forall_mem_cons.2 ⟨subd16_3_330, List.forall_mem_cons.2 ⟨subd16_3_331, List.forall_mem_cons.2 ⟨subd16_3_332, List.forall_mem_cons.2 ⟨subd16_3_333, List.forall_mem_cons.2 ⟨subd16_3_334, List.forall_mem_cons.2 ⟨subd16_3_335, List.forall_mem_cons.2 ⟨subd16_3_336, List.forall_mem_cons.2 ⟨subd16_3_337, List.forall_mem_cons.2 ⟨subd16_3_338, List.forall_mem_cons.2 ⟨subd16_3_339, List.forall_mem_cons.2 ⟨subd16_3_340, List.forall_mem_cons.2 ⟨subd16_3_341, List.forall_mem_cons.2 ⟨subd16_3_342, List.forall_mem_cons.2 ⟨subd16_3_343, List.forall_mem_cons.2 ⟨subd16_3_344, List.forall_mem_cons.2 ⟨subd16_3_345, List.forall_mem_cons.2 ⟨subd16_3_346, List.forall_mem_cons.2 ⟨subd16_3_347, List.forall_mem_cons.2 ⟨subd16_3_348, List.forall_mem_cons.2 ⟨subd16_3_349, List.forall_mem_cons.2 ⟨subd16_3_350, List.forall_mem_cons.2 ⟨subd16_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_352 : subd16_3 [0, -1, 10] = true := by decide +kernel
theorem subd16_3_353 : subd16_3 [0, -1, 11] = true := by decide +kernel
theorem subd16_3_354 : subd16_3 [0, -1, 12] = true := by decide +kernel
theorem subd16_3_355 : subd16_3 [0, 0, -13] = true := by decide +kernel
theorem subd16_3_356 : subd16_3 [0, 0, -12] = true := by decide +kernel
theorem subd16_3_357 : subd16_3 [0, 0, -11] = true := by decide +kernel
theorem subd16_3_358 : subd16_3 [0, 0, -10] = true := by decide +kernel
theorem subd16_3_359 : subd16_3 [0, 0, -9] = true := by decide +kernel
theorem subd16_3_360 : subd16_3 [0, 0, -8] = true := by decide +kernel
theorem subd16_3_361 : subd16_3 [0, 0, -7] = true := by decide +kernel
theorem subd16_3_362 : subd16_3 [0, 0, -6] = true := by decide +kernel
theorem subd16_3_363 : subd16_3 [0, 0, -5] = true := by decide +kernel
theorem subd16_3_364 : subd16_3 [0, 0, -4] = true := by decide +kernel
theorem subd16_3_365 : subd16_3 [0, 0, -3] = true := by decide +kernel
theorem subd16_3_366 : subd16_3 [0, 0, -2] = true := by decide +kernel
theorem subd16_3_367 : subd16_3 [0, 0, -1] = true := by decide +kernel
theorem subd16_3_368 : subd16_3 [0, 0, 0] = true := by decide +kernel
theorem subd16_3_369 : subd16_3 [0, 0, 1] = true := by decide +kernel
theorem subd16_3_370 : subd16_3 [0, 0, 2] = true := by decide +kernel
theorem subd16_3_371 : subd16_3 [0, 0, 3] = true := by decide +kernel
theorem subd16_3_372 : subd16_3 [0, 0, 4] = true := by decide +kernel
theorem subd16_3_373 : subd16_3 [0, 0, 5] = true := by decide +kernel
theorem subd16_3_374 : subd16_3 [0, 0, 6] = true := by decide +kernel
theorem subd16_3_375 : subd16_3 [0, 0, 7] = true := by decide +kernel
theorem subd16_3_376 : subd16_3 [0, 0, 8] = true := by decide +kernel
theorem subd16_3_377 : subd16_3 [0, 0, 9] = true := by decide +kernel
theorem subd16_3_378 : subd16_3 [0, 0, 10] = true := by decide +kernel
theorem subd16_3_379 : subd16_3 [0, 0, 11] = true := by decide +kernel
theorem subd16_3_380 : subd16_3 [0, 0, 12] = true := by decide +kernel
theorem subd16_3_381 : subd16_3 [0, 1, -13] = true := by decide +kernel
theorem subd16_3_382 : subd16_3 [0, 1, -12] = true := by decide +kernel
theorem subd16_3_383 : subd16_3 [0, 1, -11] = true := by decide +kernel
theorem sbd16_3_11 : ∀ q ∈ blkd16_3_11, subd16_3 q = true := by
  unfold blkd16_3_11
  exact List.forall_mem_cons.2 ⟨subd16_3_352, List.forall_mem_cons.2 ⟨subd16_3_353, List.forall_mem_cons.2 ⟨subd16_3_354, List.forall_mem_cons.2 ⟨subd16_3_355, List.forall_mem_cons.2 ⟨subd16_3_356, List.forall_mem_cons.2 ⟨subd16_3_357, List.forall_mem_cons.2 ⟨subd16_3_358, List.forall_mem_cons.2 ⟨subd16_3_359, List.forall_mem_cons.2 ⟨subd16_3_360, List.forall_mem_cons.2 ⟨subd16_3_361, List.forall_mem_cons.2 ⟨subd16_3_362, List.forall_mem_cons.2 ⟨subd16_3_363, List.forall_mem_cons.2 ⟨subd16_3_364, List.forall_mem_cons.2 ⟨subd16_3_365, List.forall_mem_cons.2 ⟨subd16_3_366, List.forall_mem_cons.2 ⟨subd16_3_367, List.forall_mem_cons.2 ⟨subd16_3_368, List.forall_mem_cons.2 ⟨subd16_3_369, List.forall_mem_cons.2 ⟨subd16_3_370, List.forall_mem_cons.2 ⟨subd16_3_371, List.forall_mem_cons.2 ⟨subd16_3_372, List.forall_mem_cons.2 ⟨subd16_3_373, List.forall_mem_cons.2 ⟨subd16_3_374, List.forall_mem_cons.2 ⟨subd16_3_375, List.forall_mem_cons.2 ⟨subd16_3_376, List.forall_mem_cons.2 ⟨subd16_3_377, List.forall_mem_cons.2 ⟨subd16_3_378, List.forall_mem_cons.2 ⟨subd16_3_379, List.forall_mem_cons.2 ⟨subd16_3_380, List.forall_mem_cons.2 ⟨subd16_3_381, List.forall_mem_cons.2 ⟨subd16_3_382, List.forall_mem_cons.2 ⟨subd16_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
