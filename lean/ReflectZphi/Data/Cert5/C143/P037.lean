import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [-4, -1] = true := by decide +kernel
theorem subd16_0_1 : subd16_0 [-4, 0] = true := by decide +kernel
theorem subd16_0_2 : subd16_0 [-4, 1] = true := by decide +kernel
theorem subd16_0_3 : subd16_0 [-4, 2] = true := by decide +kernel
theorem subd16_0_4 : subd16_0 [-4, 3] = true := by decide +kernel
theorem subd16_0_5 : subd16_0 [-3, -3] = true := by decide +kernel
theorem subd16_0_6 : subd16_0 [-3, -2] = true := by decide +kernel
theorem subd16_0_7 : subd16_0 [-3, -1] = true := by decide +kernel
theorem subd16_0_8 : subd16_0 [-3, 0] = true := by decide +kernel
theorem subd16_0_9 : subd16_0 [-3, 1] = true := by decide +kernel
theorem subd16_0_10 : subd16_0 [-3, 2] = true := by decide +kernel
theorem subd16_0_11 : subd16_0 [-3, 3] = true := by decide +kernel
theorem subd16_0_12 : subd16_0 [-3, 4] = true := by decide +kernel
theorem subd16_0_13 : subd16_0 [-2, -4] = true := by decide +kernel
theorem subd16_0_14 : subd16_0 [-2, -3] = true := by decide +kernel
theorem subd16_0_15 : subd16_0 [-2, -2] = true := by decide +kernel
theorem subd16_0_16 : subd16_0 [-2, -1, -6] = true := by decide +kernel
theorem subd16_0_17 : subd16_0 [-2, -1, -5] = true := by decide +kernel
theorem subd16_0_18 : subd16_0 [-2, -1, -4] = true := by decide +kernel
theorem subd16_0_19 : subd16_0 [-2, -1, -3] = true := by decide +kernel
theorem subd16_0_20 : subd16_0 [-2, -1, -2] = true := by decide +kernel
theorem subd16_0_21 : subd16_0 [-2, -1, -1] = true := by decide +kernel
theorem subd16_0_22 : subd16_0 [-2, -1, 0] = true := by decide +kernel
theorem subd16_0_23 : subd16_0 [-2, -1, 1] = true := by decide +kernel
theorem subd16_0_24 : subd16_0 [-2, -1, 2] = true := by decide +kernel
theorem subd16_0_25 : subd16_0 [-2, -1, 3] = true := by decide +kernel
theorem subd16_0_26 : subd16_0 [-2, -1, 4] = true := by decide +kernel
theorem subd16_0_27 : subd16_0 [-2, -1, 5] = true := by decide +kernel
theorem subd16_0_28 : subd16_0 [-2, -1, 6] = true := by decide +kernel
theorem subd16_0_29 : subd16_0 [-2, -1, 7] = true := by decide +kernel
theorem subd16_0_30 : subd16_0 [-2, -1, 8] = true := by decide +kernel
theorem subd16_0_31 : subd16_0 [-2, 0, -7] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_cons.2 ⟨subd16_0_1, List.forall_mem_cons.2 ⟨subd16_0_2, List.forall_mem_cons.2 ⟨subd16_0_3, List.forall_mem_cons.2 ⟨subd16_0_4, List.forall_mem_cons.2 ⟨subd16_0_5, List.forall_mem_cons.2 ⟨subd16_0_6, List.forall_mem_cons.2 ⟨subd16_0_7, List.forall_mem_cons.2 ⟨subd16_0_8, List.forall_mem_cons.2 ⟨subd16_0_9, List.forall_mem_cons.2 ⟨subd16_0_10, List.forall_mem_cons.2 ⟨subd16_0_11, List.forall_mem_cons.2 ⟨subd16_0_12, List.forall_mem_cons.2 ⟨subd16_0_13, List.forall_mem_cons.2 ⟨subd16_0_14, List.forall_mem_cons.2 ⟨subd16_0_15, List.forall_mem_cons.2 ⟨subd16_0_16, List.forall_mem_cons.2 ⟨subd16_0_17, List.forall_mem_cons.2 ⟨subd16_0_18, List.forall_mem_cons.2 ⟨subd16_0_19, List.forall_mem_cons.2 ⟨subd16_0_20, List.forall_mem_cons.2 ⟨subd16_0_21, List.forall_mem_cons.2 ⟨subd16_0_22, List.forall_mem_cons.2 ⟨subd16_0_23, List.forall_mem_cons.2 ⟨subd16_0_24, List.forall_mem_cons.2 ⟨subd16_0_25, List.forall_mem_cons.2 ⟨subd16_0_26, List.forall_mem_cons.2 ⟨subd16_0_27, List.forall_mem_cons.2 ⟨subd16_0_28, List.forall_mem_cons.2 ⟨subd16_0_29, List.forall_mem_cons.2 ⟨subd16_0_30, List.forall_mem_cons.2 ⟨subd16_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_32 : subd16_0 [-2, 0, -6] = true := by decide +kernel
theorem subd16_0_33 : subd16_0 [-2, 0, -5] = true := by decide +kernel
theorem subd16_0_34 : subd16_0 [-2, 0, -4] = true := by decide +kernel
theorem subd16_0_35 : subd16_0 [-2, 0, -3] = true := by decide +kernel
theorem subd16_0_36 : subd16_0 [-2, 0, -2] = true := by decide +kernel
theorem subd16_0_37 : subd16_0 [-2, 0, -1] = true := by decide +kernel
theorem subd16_0_38 : subd16_0 [-2, 0, 0] = true := by decide +kernel
theorem subd16_0_39 : subd16_0 [-2, 0, 1] = true := by decide +kernel
theorem subd16_0_40 : subd16_0 [-2, 0, 2] = true := by decide +kernel
theorem subd16_0_41 : subd16_0 [-2, 0, 3] = true := by decide +kernel
theorem subd16_0_42 : subd16_0 [-2, 0, 4] = true := by decide +kernel
theorem subd16_0_43 : subd16_0 [-2, 0, 5] = true := by decide +kernel
theorem subd16_0_44 : subd16_0 [-2, 0, 6] = true := by decide +kernel
theorem subd16_0_45 : subd16_0 [-2, 0, 7] = true := by decide +kernel
theorem subd16_0_46 : subd16_0 [-2, 0, 8] = true := by decide +kernel
theorem subd16_0_47 : subd16_0 [-2, 1, -8] = true := by decide +kernel
theorem subd16_0_48 : subd16_0 [-2, 1, -7] = true := by decide +kernel
theorem subd16_0_49 : subd16_0 [-2, 1, -6] = true := by decide +kernel
theorem subd16_0_50 : subd16_0 [-2, 1, -5] = true := by decide +kernel
theorem subd16_0_51 : subd16_0 [-2, 1, -4] = true := by decide +kernel
theorem subd16_0_52 : subd16_0 [-2, 1, -3] = true := by decide +kernel
theorem subd16_0_53 : subd16_0 [-2, 1, -2] = true := by decide +kernel
theorem subd16_0_54 : subd16_0 [-2, 1, -1] = true := by decide +kernel
theorem subd16_0_55 : subd16_0 [-2, 1, 0] = true := by decide +kernel
theorem subd16_0_56 : subd16_0 [-2, 1, 1] = true := by decide +kernel
theorem subd16_0_57 : subd16_0 [-2, 1, 2] = true := by decide +kernel
theorem subd16_0_58 : subd16_0 [-2, 1, 3] = true := by decide +kernel
theorem subd16_0_59 : subd16_0 [-2, 1, 4] = true := by decide +kernel
theorem subd16_0_60 : subd16_0 [-2, 1, 5] = true := by decide +kernel
theorem subd16_0_61 : subd16_0 [-2, 1, 6] = true := by decide +kernel
theorem subd16_0_62 : subd16_0 [-2, 1, 7] = true := by decide +kernel
theorem subd16_0_63 : subd16_0 [-2, 2, -8] = true := by decide +kernel
theorem sbd16_0_1 : ∀ q ∈ blkd16_0_1, subd16_0 q = true := by
  unfold blkd16_0_1
  exact List.forall_mem_cons.2 ⟨subd16_0_32, List.forall_mem_cons.2 ⟨subd16_0_33, List.forall_mem_cons.2 ⟨subd16_0_34, List.forall_mem_cons.2 ⟨subd16_0_35, List.forall_mem_cons.2 ⟨subd16_0_36, List.forall_mem_cons.2 ⟨subd16_0_37, List.forall_mem_cons.2 ⟨subd16_0_38, List.forall_mem_cons.2 ⟨subd16_0_39, List.forall_mem_cons.2 ⟨subd16_0_40, List.forall_mem_cons.2 ⟨subd16_0_41, List.forall_mem_cons.2 ⟨subd16_0_42, List.forall_mem_cons.2 ⟨subd16_0_43, List.forall_mem_cons.2 ⟨subd16_0_44, List.forall_mem_cons.2 ⟨subd16_0_45, List.forall_mem_cons.2 ⟨subd16_0_46, List.forall_mem_cons.2 ⟨subd16_0_47, List.forall_mem_cons.2 ⟨subd16_0_48, List.forall_mem_cons.2 ⟨subd16_0_49, List.forall_mem_cons.2 ⟨subd16_0_50, List.forall_mem_cons.2 ⟨subd16_0_51, List.forall_mem_cons.2 ⟨subd16_0_52, List.forall_mem_cons.2 ⟨subd16_0_53, List.forall_mem_cons.2 ⟨subd16_0_54, List.forall_mem_cons.2 ⟨subd16_0_55, List.forall_mem_cons.2 ⟨subd16_0_56, List.forall_mem_cons.2 ⟨subd16_0_57, List.forall_mem_cons.2 ⟨subd16_0_58, List.forall_mem_cons.2 ⟨subd16_0_59, List.forall_mem_cons.2 ⟨subd16_0_60, List.forall_mem_cons.2 ⟨subd16_0_61, List.forall_mem_cons.2 ⟨subd16_0_62, List.forall_mem_cons.2 ⟨subd16_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_64 : subd16_0 [-2, 2, -7] = true := by decide +kernel
theorem subd16_0_65 : subd16_0 [-2, 2, -6] = true := by decide +kernel
theorem subd16_0_66 : subd16_0 [-2, 2, -5] = true := by decide +kernel
theorem subd16_0_67 : subd16_0 [-2, 2, -4] = true := by decide +kernel
theorem subd16_0_68 : subd16_0 [-2, 2, -3] = true := by decide +kernel
theorem subd16_0_69 : subd16_0 [-2, 2, -2] = true := by decide +kernel
theorem subd16_0_70 : subd16_0 [-2, 2, -1] = true := by decide +kernel
theorem subd16_0_71 : subd16_0 [-2, 2, 0] = true := by decide +kernel
theorem subd16_0_72 : subd16_0 [-2, 2, 1] = true := by decide +kernel
theorem subd16_0_73 : subd16_0 [-2, 2, 2] = true := by decide +kernel
theorem subd16_0_74 : subd16_0 [-2, 2, 3] = true := by decide +kernel
theorem subd16_0_75 : subd16_0 [-2, 2, 4] = true := by decide +kernel
theorem subd16_0_76 : subd16_0 [-2, 2, 5] = true := by decide +kernel
theorem subd16_0_77 : subd16_0 [-2, 2, 6] = true := by decide +kernel
theorem subd16_0_78 : subd16_0 [-2, 2, 7] = true := by decide +kernel
theorem subd16_0_79 : subd16_0 [-2, 3, -8] = true := by decide +kernel
theorem subd16_0_80 : subd16_0 [-2, 3, -7] = true := by decide +kernel
theorem subd16_0_81 : subd16_0 [-2, 3, -6] = true := by decide +kernel
theorem subd16_0_82 : subd16_0 [-2, 3, -5] = true := by decide +kernel
theorem subd16_0_83 : subd16_0 [-2, 3, -4] = true := by decide +kernel
theorem subd16_0_84 : subd16_0 [-2, 3, -3] = true := by decide +kernel
theorem subd16_0_85 : subd16_0 [-2, 3, -2] = true := by decide +kernel
theorem subd16_0_86 : subd16_0 [-2, 3, -1] = true := by decide +kernel
theorem subd16_0_87 : subd16_0 [-2, 3, 0] = true := by decide +kernel
theorem subd16_0_88 : subd16_0 [-2, 3, 1] = true := by decide +kernel
theorem subd16_0_89 : subd16_0 [-2, 3, 2] = true := by decide +kernel
theorem subd16_0_90 : subd16_0 [-2, 3, 3] = true := by decide +kernel
theorem subd16_0_91 : subd16_0 [-2, 3, 4] = true := by decide +kernel
theorem subd16_0_92 : subd16_0 [-2, 3, 5] = true := by decide +kernel
theorem subd16_0_93 : subd16_0 [-2, 3, 6] = true := by decide +kernel
theorem subd16_0_94 : subd16_0 [-2, 4] = true := by decide +kernel
theorem subd16_0_95 : subd16_0 [-2, 5] = true := by decide +kernel
theorem sbd16_0_2 : ∀ q ∈ blkd16_0_2, subd16_0 q = true := by
  unfold blkd16_0_2
  exact List.forall_mem_cons.2 ⟨subd16_0_64, List.forall_mem_cons.2 ⟨subd16_0_65, List.forall_mem_cons.2 ⟨subd16_0_66, List.forall_mem_cons.2 ⟨subd16_0_67, List.forall_mem_cons.2 ⟨subd16_0_68, List.forall_mem_cons.2 ⟨subd16_0_69, List.forall_mem_cons.2 ⟨subd16_0_70, List.forall_mem_cons.2 ⟨subd16_0_71, List.forall_mem_cons.2 ⟨subd16_0_72, List.forall_mem_cons.2 ⟨subd16_0_73, List.forall_mem_cons.2 ⟨subd16_0_74, List.forall_mem_cons.2 ⟨subd16_0_75, List.forall_mem_cons.2 ⟨subd16_0_76, List.forall_mem_cons.2 ⟨subd16_0_77, List.forall_mem_cons.2 ⟨subd16_0_78, List.forall_mem_cons.2 ⟨subd16_0_79, List.forall_mem_cons.2 ⟨subd16_0_80, List.forall_mem_cons.2 ⟨subd16_0_81, List.forall_mem_cons.2 ⟨subd16_0_82, List.forall_mem_cons.2 ⟨subd16_0_83, List.forall_mem_cons.2 ⟨subd16_0_84, List.forall_mem_cons.2 ⟨subd16_0_85, List.forall_mem_cons.2 ⟨subd16_0_86, List.forall_mem_cons.2 ⟨subd16_0_87, List.forall_mem_cons.2 ⟨subd16_0_88, List.forall_mem_cons.2 ⟨subd16_0_89, List.forall_mem_cons.2 ⟨subd16_0_90, List.forall_mem_cons.2 ⟨subd16_0_91, List.forall_mem_cons.2 ⟨subd16_0_92, List.forall_mem_cons.2 ⟨subd16_0_93, List.forall_mem_cons.2 ⟨subd16_0_94, List.forall_mem_cons.2 ⟨subd16_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_96 : subd16_0 [-1, -5] = true := by decide +kernel
theorem subd16_0_97 : subd16_0 [-1, -4] = true := by decide +kernel
theorem subd16_0_98 : subd16_0 [-1, -3] = true := by decide +kernel
theorem subd16_0_99 : subd16_0 [-1, -2, -7] = true := by decide +kernel
theorem subd16_0_100 : subd16_0 [-1, -2, -6] = true := by decide +kernel
theorem subd16_0_101 : subd16_0 [-1, -2, -5] = true := by decide +kernel
theorem subd16_0_102 : subd16_0 [-1, -2, -4] = true := by decide +kernel
theorem subd16_0_103 : subd16_0 [-1, -2, -3] = true := by decide +kernel
theorem subd16_0_104 : subd16_0 [-1, -2, -2] = true := by decide +kernel
theorem subd16_0_105 : subd16_0 [-1, -2, -1] = true := by decide +kernel
theorem subd16_0_106 : subd16_0 [-1, -2, 0] = true := by decide +kernel
theorem subd16_0_107 : subd16_0 [-1, -2, 1] = true := by decide +kernel
theorem subd16_0_108 : subd16_0 [-1, -2, 2] = true := by decide +kernel
theorem subd16_0_109 : subd16_0 [-1, -2, 3] = true := by decide +kernel
theorem subd16_0_110 : subd16_0 [-1, -2, 4] = true := by decide +kernel
theorem subd16_0_111 : subd16_0 [-1, -2, 5] = true := by decide +kernel
theorem subd16_0_112 : subd16_0 [-1, -2, 6] = true := by decide +kernel
theorem subd16_0_113 : subd16_0 [-1, -2, 7] = true := by decide +kernel
theorem subd16_0_114 : subd16_0 [-1, -2, 8] = true := by decide +kernel
theorem subd16_0_115 : subd16_0 [-1, -1, -8] = true := by decide +kernel
theorem subd16_0_116 : subd16_0 [-1, -1, -7] = true := by decide +kernel
theorem subd16_0_117 : subd16_0 [-1, -1, -6] = true := by decide +kernel
theorem subd16_0_118 : subd16_0 [-1, -1, -5] = true := by decide +kernel
theorem subd16_0_119 : subd16_0 [-1, -1, -4] = true := by decide +kernel
theorem subd16_0_120 : subd16_0 [-1, -1, -3] = true := by decide +kernel
theorem subd16_0_121 : subd16_0 [-1, -1, -2] = true := by decide +kernel
theorem subd16_0_122 : subd16_0 [-1, -1, -1] = true := by decide +kernel
theorem subd16_0_123 : subd16_0 [-1, -1, 0] = true := by decide +kernel
theorem subd16_0_124 : subd16_0 [-1, -1, 1] = true := by decide +kernel
theorem subd16_0_125 : subd16_0 [-1, -1, 2] = true := by decide +kernel
theorem subd16_0_126 : subd16_0 [-1, -1, 3] = true := by decide +kernel
theorem subd16_0_127 : subd16_0 [-1, -1, 4] = true := by decide +kernel
theorem sbd16_0_3 : ∀ q ∈ blkd16_0_3, subd16_0 q = true := by
  unfold blkd16_0_3
  exact List.forall_mem_cons.2 ⟨subd16_0_96, List.forall_mem_cons.2 ⟨subd16_0_97, List.forall_mem_cons.2 ⟨subd16_0_98, List.forall_mem_cons.2 ⟨subd16_0_99, List.forall_mem_cons.2 ⟨subd16_0_100, List.forall_mem_cons.2 ⟨subd16_0_101, List.forall_mem_cons.2 ⟨subd16_0_102, List.forall_mem_cons.2 ⟨subd16_0_103, List.forall_mem_cons.2 ⟨subd16_0_104, List.forall_mem_cons.2 ⟨subd16_0_105, List.forall_mem_cons.2 ⟨subd16_0_106, List.forall_mem_cons.2 ⟨subd16_0_107, List.forall_mem_cons.2 ⟨subd16_0_108, List.forall_mem_cons.2 ⟨subd16_0_109, List.forall_mem_cons.2 ⟨subd16_0_110, List.forall_mem_cons.2 ⟨subd16_0_111, List.forall_mem_cons.2 ⟨subd16_0_112, List.forall_mem_cons.2 ⟨subd16_0_113, List.forall_mem_cons.2 ⟨subd16_0_114, List.forall_mem_cons.2 ⟨subd16_0_115, List.forall_mem_cons.2 ⟨subd16_0_116, List.forall_mem_cons.2 ⟨subd16_0_117, List.forall_mem_cons.2 ⟨subd16_0_118, List.forall_mem_cons.2 ⟨subd16_0_119, List.forall_mem_cons.2 ⟨subd16_0_120, List.forall_mem_cons.2 ⟨subd16_0_121, List.forall_mem_cons.2 ⟨subd16_0_122, List.forall_mem_cons.2 ⟨subd16_0_123, List.forall_mem_cons.2 ⟨subd16_0_124, List.forall_mem_cons.2 ⟨subd16_0_125, List.forall_mem_cons.2 ⟨subd16_0_126, List.forall_mem_cons.2 ⟨subd16_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_128 : subd16_0 [-1, -1, 5] = true := by decide +kernel
theorem subd16_0_129 : subd16_0 [-1, -1, 6] = true := by decide +kernel
theorem subd16_0_130 : subd16_0 [-1, -1, 7] = true := by decide +kernel
theorem subd16_0_131 : subd16_0 [-1, -1, 8] = true := by decide +kernel
theorem subd16_0_132 : subd16_0 [-1, 0, -8] = true := by decide +kernel
theorem subd16_0_133 : subd16_0 [-1, 0, -7] = true := by decide +kernel
theorem subd16_0_134 : subd16_0 [-1, 0, -6] = true := by decide +kernel
theorem subd16_0_135 : subd16_0 [-1, 0, -5] = true := by decide +kernel
theorem subd16_0_136 : subd16_0 [-1, 0, -4] = true := by decide +kernel
theorem subd16_0_137 : subd16_0 [-1, 0, -3] = true := by decide +kernel
theorem subd16_0_138 : subd16_0 [-1, 0, -2] = true := by decide +kernel
theorem subd16_0_139 : subd16_0 [-1, 0, -1] = true := by decide +kernel
theorem subd16_0_140 : subd16_0 [-1, 0, 0] = true := by decide +kernel
theorem subd16_0_141 : subd16_0 [-1, 0, 1] = true := by decide +kernel
theorem subd16_0_142 : subd16_0 [-1, 0, 2] = true := by decide +kernel
theorem subd16_0_143 : subd16_0 [-1, 0, 3] = true := by decide +kernel
theorem subd16_0_144 : subd16_0 [-1, 0, 4] = true := by decide +kernel
theorem subd16_0_145 : subd16_0 [-1, 0, 5] = true := by decide +kernel
theorem subd16_0_146 : subd16_0 [-1, 0, 6] = true := by decide +kernel
theorem subd16_0_147 : subd16_0 [-1, 0, 7] = true := by decide +kernel
theorem subd16_0_148 : subd16_0 [-1, 0, 8] = true := by decide +kernel
theorem subd16_0_149 : subd16_0 [-1, 1, -9] = true := by decide +kernel
theorem subd16_0_150 : subd16_0 [-1, 1, -8] = true := by decide +kernel
theorem subd16_0_151 : subd16_0 [-1, 1, -7] = true := by decide +kernel
theorem subd16_0_152 : subd16_0 [-1, 1, -6] = true := by decide +kernel
theorem subd16_0_153 : subd16_0 [-1, 1, -5] = true := by decide +kernel
theorem subd16_0_154 : subd16_0 [-1, 1, -4] = true := by decide +kernel
theorem subd16_0_155 : subd16_0 [-1, 1, -3] = true := by decide +kernel
theorem subd16_0_156 : subd16_0 [-1, 1, -2] = true := by decide +kernel
theorem subd16_0_157 : subd16_0 [-1, 1, -1] = true := by decide +kernel
theorem subd16_0_158 : subd16_0 [-1, 1, 0] = true := by decide +kernel
theorem subd16_0_159 : subd16_0 [-1, 1, 1] = true := by decide +kernel
theorem sbd16_0_4 : ∀ q ∈ blkd16_0_4, subd16_0 q = true := by
  unfold blkd16_0_4
  exact List.forall_mem_cons.2 ⟨subd16_0_128, List.forall_mem_cons.2 ⟨subd16_0_129, List.forall_mem_cons.2 ⟨subd16_0_130, List.forall_mem_cons.2 ⟨subd16_0_131, List.forall_mem_cons.2 ⟨subd16_0_132, List.forall_mem_cons.2 ⟨subd16_0_133, List.forall_mem_cons.2 ⟨subd16_0_134, List.forall_mem_cons.2 ⟨subd16_0_135, List.forall_mem_cons.2 ⟨subd16_0_136, List.forall_mem_cons.2 ⟨subd16_0_137, List.forall_mem_cons.2 ⟨subd16_0_138, List.forall_mem_cons.2 ⟨subd16_0_139, List.forall_mem_cons.2 ⟨subd16_0_140, List.forall_mem_cons.2 ⟨subd16_0_141, List.forall_mem_cons.2 ⟨subd16_0_142, List.forall_mem_cons.2 ⟨subd16_0_143, List.forall_mem_cons.2 ⟨subd16_0_144, List.forall_mem_cons.2 ⟨subd16_0_145, List.forall_mem_cons.2 ⟨subd16_0_146, List.forall_mem_cons.2 ⟨subd16_0_147, List.forall_mem_cons.2 ⟨subd16_0_148, List.forall_mem_cons.2 ⟨subd16_0_149, List.forall_mem_cons.2 ⟨subd16_0_150, List.forall_mem_cons.2 ⟨subd16_0_151, List.forall_mem_cons.2 ⟨subd16_0_152, List.forall_mem_cons.2 ⟨subd16_0_153, List.forall_mem_cons.2 ⟨subd16_0_154, List.forall_mem_cons.2 ⟨subd16_0_155, List.forall_mem_cons.2 ⟨subd16_0_156, List.forall_mem_cons.2 ⟨subd16_0_157, List.forall_mem_cons.2 ⟨subd16_0_158, List.forall_mem_cons.2 ⟨subd16_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_160 : subd16_0 [-1, 1, 2] = true := by decide +kernel
theorem subd16_0_161 : subd16_0 [-1, 1, 3] = true := by decide +kernel
theorem subd16_0_162 : subd16_0 [-1, 1, 4] = true := by decide +kernel
theorem subd16_0_163 : subd16_0 [-1, 1, 5] = true := by decide +kernel
theorem subd16_0_164 : subd16_0 [-1, 1, 6] = true := by decide +kernel
theorem subd16_0_165 : subd16_0 [-1, 1, 7] = true := by decide +kernel
theorem subd16_0_166 : subd16_0 [-1, 1, 8] = true := by decide +kernel
theorem subd16_0_167 : subd16_0 [-1, 2, -9] = true := by decide +kernel
theorem subd16_0_168 : subd16_0 [-1, 2, -8] = true := by decide +kernel
theorem subd16_0_169 : subd16_0 [-1, 2, -7] = true := by decide +kernel
theorem subd16_0_170 : subd16_0 [-1, 2, -6] = true := by decide +kernel
theorem subd16_0_171 : subd16_0 [-1, 2, -5] = true := by decide +kernel
theorem subd16_0_172 : subd16_0 [-1, 2, -4] = true := by decide +kernel
theorem subd16_0_173 : subd16_0 [-1, 2, -3] = true := by decide +kernel
theorem subd16_0_174 : subd16_0 [-1, 2, -2] = true := by decide +kernel
theorem subd16_0_175 : subd16_0 [-1, 2, -1] = true := by decide +kernel
theorem subd16_0_176 : subd16_0 [-1, 2, 0] = true := by decide +kernel
theorem subd16_0_177 : subd16_0 [-1, 2, 1] = true := by decide +kernel
theorem subd16_0_178 : subd16_0 [-1, 2, 2] = true := by decide +kernel
theorem subd16_0_179 : subd16_0 [-1, 2, 3] = true := by decide +kernel
theorem subd16_0_180 : subd16_0 [-1, 2, 4] = true := by decide +kernel
theorem subd16_0_181 : subd16_0 [-1, 2, 5] = true := by decide +kernel
theorem subd16_0_182 : subd16_0 [-1, 2, 6] = true := by decide +kernel
theorem subd16_0_183 : subd16_0 [-1, 2, 7] = true := by decide +kernel
theorem subd16_0_184 : subd16_0 [-1, 3, -8] = true := by decide +kernel
theorem subd16_0_185 : subd16_0 [-1, 3, -7] = true := by decide +kernel
theorem subd16_0_186 : subd16_0 [-1, 3, -6] = true := by decide +kernel
theorem subd16_0_187 : subd16_0 [-1, 3, -5] = true := by decide +kernel
theorem subd16_0_188 : subd16_0 [-1, 3, -4] = true := by decide +kernel
theorem subd16_0_189 : subd16_0 [-1, 3, -3] = true := by decide +kernel
theorem subd16_0_190 : subd16_0 [-1, 3, -2] = true := by decide +kernel
theorem subd16_0_191 : subd16_0 [-1, 3, -1] = true := by decide +kernel
theorem sbd16_0_5 : ∀ q ∈ blkd16_0_5, subd16_0 q = true := by
  unfold blkd16_0_5
  exact List.forall_mem_cons.2 ⟨subd16_0_160, List.forall_mem_cons.2 ⟨subd16_0_161, List.forall_mem_cons.2 ⟨subd16_0_162, List.forall_mem_cons.2 ⟨subd16_0_163, List.forall_mem_cons.2 ⟨subd16_0_164, List.forall_mem_cons.2 ⟨subd16_0_165, List.forall_mem_cons.2 ⟨subd16_0_166, List.forall_mem_cons.2 ⟨subd16_0_167, List.forall_mem_cons.2 ⟨subd16_0_168, List.forall_mem_cons.2 ⟨subd16_0_169, List.forall_mem_cons.2 ⟨subd16_0_170, List.forall_mem_cons.2 ⟨subd16_0_171, List.forall_mem_cons.2 ⟨subd16_0_172, List.forall_mem_cons.2 ⟨subd16_0_173, List.forall_mem_cons.2 ⟨subd16_0_174, List.forall_mem_cons.2 ⟨subd16_0_175, List.forall_mem_cons.2 ⟨subd16_0_176, List.forall_mem_cons.2 ⟨subd16_0_177, List.forall_mem_cons.2 ⟨subd16_0_178, List.forall_mem_cons.2 ⟨subd16_0_179, List.forall_mem_cons.2 ⟨subd16_0_180, List.forall_mem_cons.2 ⟨subd16_0_181, List.forall_mem_cons.2 ⟨subd16_0_182, List.forall_mem_cons.2 ⟨subd16_0_183, List.forall_mem_cons.2 ⟨subd16_0_184, List.forall_mem_cons.2 ⟨subd16_0_185, List.forall_mem_cons.2 ⟨subd16_0_186, List.forall_mem_cons.2 ⟨subd16_0_187, List.forall_mem_cons.2 ⟨subd16_0_188, List.forall_mem_cons.2 ⟨subd16_0_189, List.forall_mem_cons.2 ⟨subd16_0_190, List.forall_mem_cons.2 ⟨subd16_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_192 : subd16_0 [-1, 3, 0] = true := by decide +kernel
theorem subd16_0_193 : subd16_0 [-1, 3, 1] = true := by decide +kernel
theorem subd16_0_194 : subd16_0 [-1, 3, 2] = true := by decide +kernel
theorem subd16_0_195 : subd16_0 [-1, 3, 3] = true := by decide +kernel
theorem subd16_0_196 : subd16_0 [-1, 3, 4] = true := by decide +kernel
theorem subd16_0_197 : subd16_0 [-1, 3, 5] = true := by decide +kernel
theorem subd16_0_198 : subd16_0 [-1, 3, 6] = true := by decide +kernel
theorem subd16_0_199 : subd16_0 [-1, 4] = true := by decide +kernel
theorem subd16_0_200 : subd16_0 [-1, 5] = true := by decide +kernel
theorem subd16_0_201 : subd16_0 [0, -6] = true := by decide +kernel
theorem subd16_0_202 : subd16_0 [0, -5] = true := by decide +kernel
theorem subd16_0_203 : subd16_0 [0, -4] = true := by decide +kernel
theorem subd16_0_204 : subd16_0 [0, -3, -6] = true := by decide +kernel
theorem subd16_0_205 : subd16_0 [0, -3, -5] = true := by decide +kernel
theorem subd16_0_206 : subd16_0 [0, -3, -4] = true := by decide +kernel
theorem subd16_0_207 : subd16_0 [0, -3, -3] = true := by decide +kernel
theorem subd16_0_208 : subd16_0 [0, -3, -2] = true := by decide +kernel
theorem subd16_0_209 : subd16_0 [0, -3, -1] = true := by decide +kernel
theorem subd16_0_210 : subd16_0 [0, -3, 0] = true := by decide +kernel
theorem subd16_0_211 : subd16_0 [0, -3, 1] = true := by decide +kernel
theorem subd16_0_212 : subd16_0 [0, -3, 2] = true := by decide +kernel
theorem subd16_0_213 : subd16_0 [0, -3, 3] = true := by decide +kernel
theorem subd16_0_214 : subd16_0 [0, -3, 4] = true := by decide +kernel
theorem subd16_0_215 : subd16_0 [0, -3, 5] = true := by decide +kernel
theorem subd16_0_216 : subd16_0 [0, -3, 6] = true := by decide +kernel
theorem subd16_0_217 : subd16_0 [0, -3, 7] = true := by decide +kernel
theorem subd16_0_218 : subd16_0 [0, -3, 8] = true := by decide +kernel
theorem subd16_0_219 : subd16_0 [0, -2, -8] = true := by decide +kernel
theorem subd16_0_220 : subd16_0 [0, -2, -7] = true := by decide +kernel
theorem subd16_0_221 : subd16_0 [0, -2, -6] = true := by decide +kernel
theorem subd16_0_222 : subd16_0 [0, -2, -5] = true := by decide +kernel
theorem subd16_0_223 : subd16_0 [0, -2, -4] = true := by decide +kernel
theorem sbd16_0_6 : ∀ q ∈ blkd16_0_6, subd16_0 q = true := by
  unfold blkd16_0_6
  exact List.forall_mem_cons.2 ⟨subd16_0_192, List.forall_mem_cons.2 ⟨subd16_0_193, List.forall_mem_cons.2 ⟨subd16_0_194, List.forall_mem_cons.2 ⟨subd16_0_195, List.forall_mem_cons.2 ⟨subd16_0_196, List.forall_mem_cons.2 ⟨subd16_0_197, List.forall_mem_cons.2 ⟨subd16_0_198, List.forall_mem_cons.2 ⟨subd16_0_199, List.forall_mem_cons.2 ⟨subd16_0_200, List.forall_mem_cons.2 ⟨subd16_0_201, List.forall_mem_cons.2 ⟨subd16_0_202, List.forall_mem_cons.2 ⟨subd16_0_203, List.forall_mem_cons.2 ⟨subd16_0_204, List.forall_mem_cons.2 ⟨subd16_0_205, List.forall_mem_cons.2 ⟨subd16_0_206, List.forall_mem_cons.2 ⟨subd16_0_207, List.forall_mem_cons.2 ⟨subd16_0_208, List.forall_mem_cons.2 ⟨subd16_0_209, List.forall_mem_cons.2 ⟨subd16_0_210, List.forall_mem_cons.2 ⟨subd16_0_211, List.forall_mem_cons.2 ⟨subd16_0_212, List.forall_mem_cons.2 ⟨subd16_0_213, List.forall_mem_cons.2 ⟨subd16_0_214, List.forall_mem_cons.2 ⟨subd16_0_215, List.forall_mem_cons.2 ⟨subd16_0_216, List.forall_mem_cons.2 ⟨subd16_0_217, List.forall_mem_cons.2 ⟨subd16_0_218, List.forall_mem_cons.2 ⟨subd16_0_219, List.forall_mem_cons.2 ⟨subd16_0_220, List.forall_mem_cons.2 ⟨subd16_0_221, List.forall_mem_cons.2 ⟨subd16_0_222, List.forall_mem_cons.2 ⟨subd16_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_224 : subd16_0 [0, -2, -3] = true := by decide +kernel
theorem subd16_0_225 : subd16_0 [0, -2, -2] = true := by decide +kernel
theorem subd16_0_226 : subd16_0 [0, -2, -1] = true := by decide +kernel
theorem subd16_0_227 : subd16_0 [0, -2, 0] = true := by decide +kernel
theorem subd16_0_228 : subd16_0 [0, -2, 1] = true := by decide +kernel
theorem subd16_0_229 : subd16_0 [0, -2, 2] = true := by decide +kernel
theorem subd16_0_230 : subd16_0 [0, -2, 3] = true := by decide +kernel
theorem subd16_0_231 : subd16_0 [0, -2, 4] = true := by decide +kernel
theorem subd16_0_232 : subd16_0 [0, -2, 5] = true := by decide +kernel
theorem subd16_0_233 : subd16_0 [0, -2, 6] = true := by decide +kernel
theorem subd16_0_234 : subd16_0 [0, -2, 7] = true := by decide +kernel
theorem subd16_0_235 : subd16_0 [0, -2, 8] = true := by decide +kernel
theorem subd16_0_236 : subd16_0 [0, -1, -8] = true := by decide +kernel
theorem subd16_0_237 : subd16_0 [0, -1, -7] = true := by decide +kernel
theorem subd16_0_238 : subd16_0 [0, -1, -6] = true := by decide +kernel
theorem subd16_0_239 : subd16_0 [0, -1, -5] = true := by decide +kernel
theorem subd16_0_240 : subd16_0 [0, -1, -4] = true := by decide +kernel
theorem subd16_0_241 : subd16_0 [0, -1, -3] = true := by decide +kernel
theorem subd16_0_242 : subd16_0 [0, -1, -2] = true := by decide +kernel
theorem subd16_0_243 : subd16_0 [0, -1, -1] = true := by decide +kernel
theorem subd16_0_244 : subd16_0 [0, -1, 0] = true := by decide +kernel
theorem subd16_0_245 : subd16_0 [0, -1, 1] = true := by decide +kernel
theorem subd16_0_246 : subd16_0 [0, -1, 2] = true := by decide +kernel
theorem subd16_0_247 : subd16_0 [0, -1, 3] = true := by decide +kernel
theorem subd16_0_248 : subd16_0 [0, -1, 4] = true := by decide +kernel
theorem subd16_0_249 : subd16_0 [0, -1, 5] = true := by decide +kernel
theorem subd16_0_250 : subd16_0 [0, -1, 6] = true := by decide +kernel
theorem subd16_0_251 : subd16_0 [0, -1, 7] = true := by decide +kernel
theorem subd16_0_252 : subd16_0 [0, -1, 8] = true := by decide +kernel
theorem subd16_0_253 : subd16_0 [0, 0, -9] = true := by decide +kernel
theorem subd16_0_254 : subd16_0 [0, 0, -8] = true := by decide +kernel
theorem subd16_0_255 : subd16_0 [0, 0, -7] = true := by decide +kernel
theorem sbd16_0_7 : ∀ q ∈ blkd16_0_7, subd16_0 q = true := by
  unfold blkd16_0_7
  exact List.forall_mem_cons.2 ⟨subd16_0_224, List.forall_mem_cons.2 ⟨subd16_0_225, List.forall_mem_cons.2 ⟨subd16_0_226, List.forall_mem_cons.2 ⟨subd16_0_227, List.forall_mem_cons.2 ⟨subd16_0_228, List.forall_mem_cons.2 ⟨subd16_0_229, List.forall_mem_cons.2 ⟨subd16_0_230, List.forall_mem_cons.2 ⟨subd16_0_231, List.forall_mem_cons.2 ⟨subd16_0_232, List.forall_mem_cons.2 ⟨subd16_0_233, List.forall_mem_cons.2 ⟨subd16_0_234, List.forall_mem_cons.2 ⟨subd16_0_235, List.forall_mem_cons.2 ⟨subd16_0_236, List.forall_mem_cons.2 ⟨subd16_0_237, List.forall_mem_cons.2 ⟨subd16_0_238, List.forall_mem_cons.2 ⟨subd16_0_239, List.forall_mem_cons.2 ⟨subd16_0_240, List.forall_mem_cons.2 ⟨subd16_0_241, List.forall_mem_cons.2 ⟨subd16_0_242, List.forall_mem_cons.2 ⟨subd16_0_243, List.forall_mem_cons.2 ⟨subd16_0_244, List.forall_mem_cons.2 ⟨subd16_0_245, List.forall_mem_cons.2 ⟨subd16_0_246, List.forall_mem_cons.2 ⟨subd16_0_247, List.forall_mem_cons.2 ⟨subd16_0_248, List.forall_mem_cons.2 ⟨subd16_0_249, List.forall_mem_cons.2 ⟨subd16_0_250, List.forall_mem_cons.2 ⟨subd16_0_251, List.forall_mem_cons.2 ⟨subd16_0_252, List.forall_mem_cons.2 ⟨subd16_0_253, List.forall_mem_cons.2 ⟨subd16_0_254, List.forall_mem_cons.2 ⟨subd16_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_256 : subd16_0 [0, 0, -6] = true := by decide +kernel
theorem subd16_0_257 : subd16_0 [0, 0, -5] = true := by decide +kernel
theorem subd16_0_258 : subd16_0 [0, 0, -4] = true := by decide +kernel
theorem subd16_0_259 : subd16_0 [0, 0, -3] = true := by decide +kernel
theorem subd16_0_260 : subd16_0 [0, 0, -2] = true := by decide +kernel
theorem subd16_0_261 : subd16_0 [0, 0, -1] = true := by decide +kernel
theorem subd16_0_262 : subd16_0 [0, 0, 0] = true := by decide +kernel
theorem subd16_0_263 : subd16_0 [0, 0, 1] = true := by decide +kernel
theorem subd16_0_264 : subd16_0 [0, 0, 2] = true := by decide +kernel
theorem subd16_0_265 : subd16_0 [0, 0, 3] = true := by decide +kernel
theorem subd16_0_266 : subd16_0 [0, 0, 4] = true := by decide +kernel
theorem subd16_0_267 : subd16_0 [0, 0, 5] = true := by decide +kernel
theorem subd16_0_268 : subd16_0 [0, 0, 6] = true := by decide +kernel
theorem subd16_0_269 : subd16_0 [0, 0, 7] = true := by decide +kernel
theorem subd16_0_270 : subd16_0 [0, 0, 8] = true := by decide +kernel
theorem subd16_0_271 : subd16_0 [0, 1, -9] = true := by decide +kernel
theorem subd16_0_272 : subd16_0 [0, 1, -8] = true := by decide +kernel
theorem subd16_0_273 : subd16_0 [0, 1, -7] = true := by decide +kernel
theorem subd16_0_274 : subd16_0 [0, 1, -6] = true := by decide +kernel
theorem subd16_0_275 : subd16_0 [0, 1, -5] = true := by decide +kernel
theorem subd16_0_276 : subd16_0 [0, 1, -4] = true := by decide +kernel
theorem subd16_0_277 : subd16_0 [0, 1, -3] = true := by decide +kernel
theorem subd16_0_278 : subd16_0 [0, 1, -2] = true := by decide +kernel
theorem subd16_0_279 : subd16_0 [0, 1, -1] = true := by decide +kernel
theorem subd16_0_280 : subd16_0 [0, 1, 0] = true := by decide +kernel
theorem subd16_0_281 : subd16_0 [0, 1, 1] = true := by decide +kernel
theorem subd16_0_282 : subd16_0 [0, 1, 2] = true := by decide +kernel
theorem subd16_0_283 : subd16_0 [0, 1, 3] = true := by decide +kernel
theorem subd16_0_284 : subd16_0 [0, 1, 4] = true := by decide +kernel
theorem subd16_0_285 : subd16_0 [0, 1, 5] = true := by decide +kernel
theorem subd16_0_286 : subd16_0 [0, 1, 6] = true := by decide +kernel
theorem subd16_0_287 : subd16_0 [0, 1, 7] = true := by decide +kernel
theorem sbd16_0_8 : ∀ q ∈ blkd16_0_8, subd16_0 q = true := by
  unfold blkd16_0_8
  exact List.forall_mem_cons.2 ⟨subd16_0_256, List.forall_mem_cons.2 ⟨subd16_0_257, List.forall_mem_cons.2 ⟨subd16_0_258, List.forall_mem_cons.2 ⟨subd16_0_259, List.forall_mem_cons.2 ⟨subd16_0_260, List.forall_mem_cons.2 ⟨subd16_0_261, List.forall_mem_cons.2 ⟨subd16_0_262, List.forall_mem_cons.2 ⟨subd16_0_263, List.forall_mem_cons.2 ⟨subd16_0_264, List.forall_mem_cons.2 ⟨subd16_0_265, List.forall_mem_cons.2 ⟨subd16_0_266, List.forall_mem_cons.2 ⟨subd16_0_267, List.forall_mem_cons.2 ⟨subd16_0_268, List.forall_mem_cons.2 ⟨subd16_0_269, List.forall_mem_cons.2 ⟨subd16_0_270, List.forall_mem_cons.2 ⟨subd16_0_271, List.forall_mem_cons.2 ⟨subd16_0_272, List.forall_mem_cons.2 ⟨subd16_0_273, List.forall_mem_cons.2 ⟨subd16_0_274, List.forall_mem_cons.2 ⟨subd16_0_275, List.forall_mem_cons.2 ⟨subd16_0_276, List.forall_mem_cons.2 ⟨subd16_0_277, List.forall_mem_cons.2 ⟨subd16_0_278, List.forall_mem_cons.2 ⟨subd16_0_279, List.forall_mem_cons.2 ⟨subd16_0_280, List.forall_mem_cons.2 ⟨subd16_0_281, List.forall_mem_cons.2 ⟨subd16_0_282, List.forall_mem_cons.2 ⟨subd16_0_283, List.forall_mem_cons.2 ⟨subd16_0_284, List.forall_mem_cons.2 ⟨subd16_0_285, List.forall_mem_cons.2 ⟨subd16_0_286, List.forall_mem_cons.2 ⟨subd16_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_288 : subd16_0 [0, 2, -9] = true := by decide +kernel
theorem subd16_0_289 : subd16_0 [0, 2, -8] = true := by decide +kernel
theorem subd16_0_290 : subd16_0 [0, 2, -7] = true := by decide +kernel
theorem subd16_0_291 : subd16_0 [0, 2, -6] = true := by decide +kernel
theorem subd16_0_292 : subd16_0 [0, 2, -5] = true := by decide +kernel
theorem subd16_0_293 : subd16_0 [0, 2, -4] = true := by decide +kernel
theorem subd16_0_294 : subd16_0 [0, 2, -3] = true := by decide +kernel
theorem subd16_0_295 : subd16_0 [0, 2, -2] = true := by decide +kernel
theorem subd16_0_296 : subd16_0 [0, 2, -1] = true := by decide +kernel
theorem subd16_0_297 : subd16_0 [0, 2, 0] = true := by decide +kernel
theorem subd16_0_298 : subd16_0 [0, 2, 1] = true := by decide +kernel
theorem subd16_0_299 : subd16_0 [0, 2, 2] = true := by decide +kernel
theorem subd16_0_300 : subd16_0 [0, 2, 3] = true := by decide +kernel
theorem subd16_0_301 : subd16_0 [0, 2, 4] = true := by decide +kernel
theorem subd16_0_302 : subd16_0 [0, 2, 5] = true := by decide +kernel
theorem subd16_0_303 : subd16_0 [0, 2, 6] = true := by decide +kernel
theorem subd16_0_304 : subd16_0 [0, 2, 7] = true := by decide +kernel
theorem subd16_0_305 : subd16_0 [0, 3, -9] = true := by decide +kernel
theorem subd16_0_306 : subd16_0 [0, 3, -8] = true := by decide +kernel
theorem subd16_0_307 : subd16_0 [0, 3, -7] = true := by decide +kernel
theorem subd16_0_308 : subd16_0 [0, 3, -6] = true := by decide +kernel
theorem subd16_0_309 : subd16_0 [0, 3, -5] = true := by decide +kernel
theorem subd16_0_310 : subd16_0 [0, 3, -4] = true := by decide +kernel
theorem subd16_0_311 : subd16_0 [0, 3, -3] = true := by decide +kernel
theorem subd16_0_312 : subd16_0 [0, 3, -2] = true := by decide +kernel
theorem subd16_0_313 : subd16_0 [0, 3, -1] = true := by decide +kernel
theorem subd16_0_314 : subd16_0 [0, 3, 0] = true := by decide +kernel
theorem subd16_0_315 : subd16_0 [0, 3, 1] = true := by decide +kernel
theorem subd16_0_316 : subd16_0 [0, 3, 2] = true := by decide +kernel
theorem subd16_0_317 : subd16_0 [0, 3, 3] = true := by decide +kernel
theorem subd16_0_318 : subd16_0 [0, 3, 4] = true := by decide +kernel
theorem subd16_0_319 : subd16_0 [0, 3, 5] = true := by decide +kernel
theorem sbd16_0_9 : ∀ q ∈ blkd16_0_9, subd16_0 q = true := by
  unfold blkd16_0_9
  exact List.forall_mem_cons.2 ⟨subd16_0_288, List.forall_mem_cons.2 ⟨subd16_0_289, List.forall_mem_cons.2 ⟨subd16_0_290, List.forall_mem_cons.2 ⟨subd16_0_291, List.forall_mem_cons.2 ⟨subd16_0_292, List.forall_mem_cons.2 ⟨subd16_0_293, List.forall_mem_cons.2 ⟨subd16_0_294, List.forall_mem_cons.2 ⟨subd16_0_295, List.forall_mem_cons.2 ⟨subd16_0_296, List.forall_mem_cons.2 ⟨subd16_0_297, List.forall_mem_cons.2 ⟨subd16_0_298, List.forall_mem_cons.2 ⟨subd16_0_299, List.forall_mem_cons.2 ⟨subd16_0_300, List.forall_mem_cons.2 ⟨subd16_0_301, List.forall_mem_cons.2 ⟨subd16_0_302, List.forall_mem_cons.2 ⟨subd16_0_303, List.forall_mem_cons.2 ⟨subd16_0_304, List.forall_mem_cons.2 ⟨subd16_0_305, List.forall_mem_cons.2 ⟨subd16_0_306, List.forall_mem_cons.2 ⟨subd16_0_307, List.forall_mem_cons.2 ⟨subd16_0_308, List.forall_mem_cons.2 ⟨subd16_0_309, List.forall_mem_cons.2 ⟨subd16_0_310, List.forall_mem_cons.2 ⟨subd16_0_311, List.forall_mem_cons.2 ⟨subd16_0_312, List.forall_mem_cons.2 ⟨subd16_0_313, List.forall_mem_cons.2 ⟨subd16_0_314, List.forall_mem_cons.2 ⟨subd16_0_315, List.forall_mem_cons.2 ⟨subd16_0_316, List.forall_mem_cons.2 ⟨subd16_0_317, List.forall_mem_cons.2 ⟨subd16_0_318, List.forall_mem_cons.2 ⟨subd16_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_320 : subd16_0 [0, 4] = true := by decide +kernel
theorem subd16_0_321 : subd16_0 [0, 5] = true := by decide +kernel
theorem subd16_0_322 : subd16_0 [1, -6] = true := by decide +kernel
theorem subd16_0_323 : subd16_0 [1, -5] = true := by decide +kernel
theorem subd16_0_324 : subd16_0 [1, -4] = true := by decide +kernel
theorem subd16_0_325 : subd16_0 [1, -3, -7] = true := by decide +kernel
theorem subd16_0_326 : subd16_0 [1, -3, -6] = true := by decide +kernel
theorem subd16_0_327 : subd16_0 [1, -3, -5] = true := by decide +kernel
theorem subd16_0_328 : subd16_0 [1, -3, -4] = true := by decide +kernel
theorem subd16_0_329 : subd16_0 [1, -3, -3] = true := by decide +kernel
theorem subd16_0_330 : subd16_0 [1, -3, -2] = true := by decide +kernel
theorem subd16_0_331 : subd16_0 [1, -3, -1] = true := by decide +kernel
theorem subd16_0_332 : subd16_0 [1, -3, 0] = true := by decide +kernel
theorem subd16_0_333 : subd16_0 [1, -3, 1] = true := by decide +kernel
theorem subd16_0_334 : subd16_0 [1, -3, 2] = true := by decide +kernel
theorem subd16_0_335 : subd16_0 [1, -3, 3] = true := by decide +kernel
theorem subd16_0_336 : subd16_0 [1, -3, 4] = true := by decide +kernel
theorem subd16_0_337 : subd16_0 [1, -3, 5] = true := by decide +kernel
theorem subd16_0_338 : subd16_0 [1, -3, 6] = true := by decide +kernel
theorem subd16_0_339 : subd16_0 [1, -3, 7] = true := by decide +kernel
theorem subd16_0_340 : subd16_0 [1, -2, -8] = true := by decide +kernel
theorem subd16_0_341 : subd16_0 [1, -2, -7] = true := by decide +kernel
theorem subd16_0_342 : subd16_0 [1, -2, -6] = true := by decide +kernel
theorem subd16_0_343 : subd16_0 [1, -2, -5] = true := by decide +kernel
theorem subd16_0_344 : subd16_0 [1, -2, -4] = true := by decide +kernel
theorem subd16_0_345 : subd16_0 [1, -2, -3] = true := by decide +kernel
theorem subd16_0_346 : subd16_0 [1, -2, -2] = true := by decide +kernel
theorem subd16_0_347 : subd16_0 [1, -2, -1] = true := by decide +kernel
theorem subd16_0_348 : subd16_0 [1, -2, 0] = true := by decide +kernel
theorem subd16_0_349 : subd16_0 [1, -2, 1] = true := by decide +kernel
theorem subd16_0_350 : subd16_0 [1, -2, 2] = true := by decide +kernel
theorem subd16_0_351 : subd16_0 [1, -2, 3] = true := by decide +kernel
theorem sbd16_0_10 : ∀ q ∈ blkd16_0_10, subd16_0 q = true := by
  unfold blkd16_0_10
  exact List.forall_mem_cons.2 ⟨subd16_0_320, List.forall_mem_cons.2 ⟨subd16_0_321, List.forall_mem_cons.2 ⟨subd16_0_322, List.forall_mem_cons.2 ⟨subd16_0_323, List.forall_mem_cons.2 ⟨subd16_0_324, List.forall_mem_cons.2 ⟨subd16_0_325, List.forall_mem_cons.2 ⟨subd16_0_326, List.forall_mem_cons.2 ⟨subd16_0_327, List.forall_mem_cons.2 ⟨subd16_0_328, List.forall_mem_cons.2 ⟨subd16_0_329, List.forall_mem_cons.2 ⟨subd16_0_330, List.forall_mem_cons.2 ⟨subd16_0_331, List.forall_mem_cons.2 ⟨subd16_0_332, List.forall_mem_cons.2 ⟨subd16_0_333, List.forall_mem_cons.2 ⟨subd16_0_334, List.forall_mem_cons.2 ⟨subd16_0_335, List.forall_mem_cons.2 ⟨subd16_0_336, List.forall_mem_cons.2 ⟨subd16_0_337, List.forall_mem_cons.2 ⟨subd16_0_338, List.forall_mem_cons.2 ⟨subd16_0_339, List.forall_mem_cons.2 ⟨subd16_0_340, List.forall_mem_cons.2 ⟨subd16_0_341, List.forall_mem_cons.2 ⟨subd16_0_342, List.forall_mem_cons.2 ⟨subd16_0_343, List.forall_mem_cons.2 ⟨subd16_0_344, List.forall_mem_cons.2 ⟨subd16_0_345, List.forall_mem_cons.2 ⟨subd16_0_346, List.forall_mem_cons.2 ⟨subd16_0_347, List.forall_mem_cons.2 ⟨subd16_0_348, List.forall_mem_cons.2 ⟨subd16_0_349, List.forall_mem_cons.2 ⟨subd16_0_350, List.forall_mem_cons.2 ⟨subd16_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_352 : subd16_0 [1, -2, 4] = true := by decide +kernel
theorem subd16_0_353 : subd16_0 [1, -2, 5] = true := by decide +kernel
theorem subd16_0_354 : subd16_0 [1, -2, 6] = true := by decide +kernel
theorem subd16_0_355 : subd16_0 [1, -2, 7] = true := by decide +kernel
theorem subd16_0_356 : subd16_0 [1, -2, 8] = true := by decide +kernel
theorem subd16_0_357 : subd16_0 [1, -1, -9] = true := by decide +kernel
theorem subd16_0_358 : subd16_0 [1, -1, -8] = true := by decide +kernel
theorem subd16_0_359 : subd16_0 [1, -1, -7] = true := by decide +kernel
theorem subd16_0_360 : subd16_0 [1, -1, -6] = true := by decide +kernel
theorem subd16_0_361 : subd16_0 [1, -1, -5] = true := by decide +kernel
theorem subd16_0_362 : subd16_0 [1, -1, -4] = true := by decide +kernel
theorem subd16_0_363 : subd16_0 [1, -1, -3] = true := by decide +kernel
theorem subd16_0_364 : subd16_0 [1, -1, -2] = true := by decide +kernel
theorem subd16_0_365 : subd16_0 [1, -1, -1] = true := by decide +kernel
theorem subd16_0_366 : subd16_0 [1, -1, 0] = true := by decide +kernel
theorem subd16_0_367 : subd16_0 [1, -1, 1] = true := by decide +kernel
theorem subd16_0_368 : subd16_0 [1, -1, 2] = true := by decide +kernel
theorem subd16_0_369 : subd16_0 [1, -1, 3] = true := by decide +kernel
theorem subd16_0_370 : subd16_0 [1, -1, 4] = true := by decide +kernel
theorem subd16_0_371 : subd16_0 [1, -1, 5] = true := by decide +kernel
theorem subd16_0_372 : subd16_0 [1, -1, 6] = true := by decide +kernel
theorem subd16_0_373 : subd16_0 [1, -1, 7] = true := by decide +kernel
theorem subd16_0_374 : subd16_0 [1, -1, 8] = true := by decide +kernel
theorem subd16_0_375 : subd16_0 [1, 0, -9] = true := by decide +kernel
theorem subd16_0_376 : subd16_0 [1, 0, -8] = true := by decide +kernel
theorem subd16_0_377 : subd16_0 [1, 0, -7] = true := by decide +kernel
theorem subd16_0_378 : subd16_0 [1, 0, -6] = true := by decide +kernel
theorem subd16_0_379 : subd16_0 [1, 0, -5] = true := by decide +kernel
theorem subd16_0_380 : subd16_0 [1, 0, -4] = true := by decide +kernel
theorem subd16_0_381 : subd16_0 [1, 0, -3] = true := by decide +kernel
theorem subd16_0_382 : subd16_0 [1, 0, -2] = true := by decide +kernel
theorem subd16_0_383 : subd16_0 [1, 0, -1] = true := by decide +kernel
theorem sbd16_0_11 : ∀ q ∈ blkd16_0_11, subd16_0 q = true := by
  unfold blkd16_0_11
  exact List.forall_mem_cons.2 ⟨subd16_0_352, List.forall_mem_cons.2 ⟨subd16_0_353, List.forall_mem_cons.2 ⟨subd16_0_354, List.forall_mem_cons.2 ⟨subd16_0_355, List.forall_mem_cons.2 ⟨subd16_0_356, List.forall_mem_cons.2 ⟨subd16_0_357, List.forall_mem_cons.2 ⟨subd16_0_358, List.forall_mem_cons.2 ⟨subd16_0_359, List.forall_mem_cons.2 ⟨subd16_0_360, List.forall_mem_cons.2 ⟨subd16_0_361, List.forall_mem_cons.2 ⟨subd16_0_362, List.forall_mem_cons.2 ⟨subd16_0_363, List.forall_mem_cons.2 ⟨subd16_0_364, List.forall_mem_cons.2 ⟨subd16_0_365, List.forall_mem_cons.2 ⟨subd16_0_366, List.forall_mem_cons.2 ⟨subd16_0_367, List.forall_mem_cons.2 ⟨subd16_0_368, List.forall_mem_cons.2 ⟨subd16_0_369, List.forall_mem_cons.2 ⟨subd16_0_370, List.forall_mem_cons.2 ⟨subd16_0_371, List.forall_mem_cons.2 ⟨subd16_0_372, List.forall_mem_cons.2 ⟨subd16_0_373, List.forall_mem_cons.2 ⟨subd16_0_374, List.forall_mem_cons.2 ⟨subd16_0_375, List.forall_mem_cons.2 ⟨subd16_0_376, List.forall_mem_cons.2 ⟨subd16_0_377, List.forall_mem_cons.2 ⟨subd16_0_378, List.forall_mem_cons.2 ⟨subd16_0_379, List.forall_mem_cons.2 ⟨subd16_0_380, List.forall_mem_cons.2 ⟨subd16_0_381, List.forall_mem_cons.2 ⟨subd16_0_382, List.forall_mem_cons.2 ⟨subd16_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_384 : subd16_0 [1, 0, 0] = true := by decide +kernel
theorem subd16_0_385 : subd16_0 [1, 0, 1] = true := by decide +kernel
theorem subd16_0_386 : subd16_0 [1, 0, 2] = true := by decide +kernel
theorem subd16_0_387 : subd16_0 [1, 0, 3] = true := by decide +kernel
theorem subd16_0_388 : subd16_0 [1, 0, 4] = true := by decide +kernel
theorem subd16_0_389 : subd16_0 [1, 0, 5] = true := by decide +kernel
theorem subd16_0_390 : subd16_0 [1, 0, 6] = true := by decide +kernel
theorem subd16_0_391 : subd16_0 [1, 0, 7] = true := by decide +kernel
theorem subd16_0_392 : subd16_0 [1, 1, -9] = true := by decide +kernel
theorem subd16_0_393 : subd16_0 [1, 1, -8] = true := by decide +kernel
theorem subd16_0_394 : subd16_0 [1, 1, -7] = true := by decide +kernel
theorem subd16_0_395 : subd16_0 [1, 1, -6] = true := by decide +kernel
theorem subd16_0_396 : subd16_0 [1, 1, -5] = true := by decide +kernel
theorem subd16_0_397 : subd16_0 [1, 1, -4] = true := by decide +kernel
theorem subd16_0_398 : subd16_0 [1, 1, -3] = true := by decide +kernel
theorem subd16_0_399 : subd16_0 [1, 1, -2] = true := by decide +kernel
theorem subd16_0_400 : subd16_0 [1, 1, -1] = true := by decide +kernel
theorem subd16_0_401 : subd16_0 [1, 1, 0] = true := by decide +kernel
theorem subd16_0_402 : subd16_0 [1, 1, 1] = true := by decide +kernel
theorem subd16_0_403 : subd16_0 [1, 1, 2] = true := by decide +kernel
theorem subd16_0_404 : subd16_0 [1, 1, 3] = true := by decide +kernel
theorem subd16_0_405 : subd16_0 [1, 1, 4] = true := by decide +kernel
theorem subd16_0_406 : subd16_0 [1, 1, 5] = true := by decide +kernel
theorem subd16_0_407 : subd16_0 [1, 1, 6] = true := by decide +kernel
theorem subd16_0_408 : subd16_0 [1, 1, 7] = true := by decide +kernel
theorem subd16_0_409 : subd16_0 [1, 2, -9] = true := by decide +kernel
theorem subd16_0_410 : subd16_0 [1, 2, -8] = true := by decide +kernel
theorem subd16_0_411 : subd16_0 [1, 2, -7] = true := by decide +kernel
theorem subd16_0_412 : subd16_0 [1, 2, -6] = true := by decide +kernel
theorem subd16_0_413 : subd16_0 [1, 2, -5] = true := by decide +kernel
theorem subd16_0_414 : subd16_0 [1, 2, -4] = true := by decide +kernel
theorem subd16_0_415 : subd16_0 [1, 2, -3] = true := by decide +kernel
theorem sbd16_0_12 : ∀ q ∈ blkd16_0_12, subd16_0 q = true := by
  unfold blkd16_0_12
  exact List.forall_mem_cons.2 ⟨subd16_0_384, List.forall_mem_cons.2 ⟨subd16_0_385, List.forall_mem_cons.2 ⟨subd16_0_386, List.forall_mem_cons.2 ⟨subd16_0_387, List.forall_mem_cons.2 ⟨subd16_0_388, List.forall_mem_cons.2 ⟨subd16_0_389, List.forall_mem_cons.2 ⟨subd16_0_390, List.forall_mem_cons.2 ⟨subd16_0_391, List.forall_mem_cons.2 ⟨subd16_0_392, List.forall_mem_cons.2 ⟨subd16_0_393, List.forall_mem_cons.2 ⟨subd16_0_394, List.forall_mem_cons.2 ⟨subd16_0_395, List.forall_mem_cons.2 ⟨subd16_0_396, List.forall_mem_cons.2 ⟨subd16_0_397, List.forall_mem_cons.2 ⟨subd16_0_398, List.forall_mem_cons.2 ⟨subd16_0_399, List.forall_mem_cons.2 ⟨subd16_0_400, List.forall_mem_cons.2 ⟨subd16_0_401, List.forall_mem_cons.2 ⟨subd16_0_402, List.forall_mem_cons.2 ⟨subd16_0_403, List.forall_mem_cons.2 ⟨subd16_0_404, List.forall_mem_cons.2 ⟨subd16_0_405, List.forall_mem_cons.2 ⟨subd16_0_406, List.forall_mem_cons.2 ⟨subd16_0_407, List.forall_mem_cons.2 ⟨subd16_0_408, List.forall_mem_cons.2 ⟨subd16_0_409, List.forall_mem_cons.2 ⟨subd16_0_410, List.forall_mem_cons.2 ⟨subd16_0_411, List.forall_mem_cons.2 ⟨subd16_0_412, List.forall_mem_cons.2 ⟨subd16_0_413, List.forall_mem_cons.2 ⟨subd16_0_414, List.forall_mem_cons.2 ⟨subd16_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
