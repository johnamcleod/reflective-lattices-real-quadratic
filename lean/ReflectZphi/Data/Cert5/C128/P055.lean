import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [-2, -4] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [-2, -3] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [-2, -2, -8] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [-2, -2, -7] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [-2, -2, -6] = true := by decide +kernel
theorem subd8_4_5 : subd8_4 [-2, -2, -5] = true := by decide +kernel
theorem subd8_4_6 : subd8_4 [-2, -2, -4] = true := by decide +kernel
theorem subd8_4_7 : subd8_4 [-2, -2, -3] = true := by decide +kernel
theorem subd8_4_8 : subd8_4 [-2, -2, -2] = true := by decide +kernel
theorem subd8_4_9 : subd8_4 [-2, -2, -1] = true := by decide +kernel
theorem subd8_4_10 : subd8_4 [-2, -2, 0] = true := by decide +kernel
theorem subd8_4_11 : subd8_4 [-2, -2, 1] = true := by decide +kernel
theorem subd8_4_12 : subd8_4 [-2, -2, 2] = true := by decide +kernel
theorem subd8_4_13 : subd8_4 [-2, -2, 3] = true := by decide +kernel
theorem subd8_4_14 : subd8_4 [-2, -2, 4] = true := by decide +kernel
theorem subd8_4_15 : subd8_4 [-2, -2, 5] = true := by decide +kernel
theorem subd8_4_16 : subd8_4 [-2, -2, 6] = true := by decide +kernel
theorem subd8_4_17 : subd8_4 [-2, -1, -9] = true := by decide +kernel
theorem subd8_4_18 : subd8_4 [-2, -1, -8] = true := by decide +kernel
theorem subd8_4_19 : subd8_4 [-2, -1, -7] = true := by decide +kernel
theorem subd8_4_20 : subd8_4 [-2, -1, -6] = true := by decide +kernel
theorem subd8_4_21 : subd8_4 [-2, -1, -5] = true := by decide +kernel
theorem subd8_4_22 : subd8_4 [-2, -1, -4] = true := by decide +kernel
theorem subd8_4_23 : subd8_4 [-2, -1, -3] = true := by decide +kernel
theorem subd8_4_24 : subd8_4 [-2, -1, -2] = true := by decide +kernel
theorem subd8_4_25 : subd8_4 [-2, -1, -1] = true := by decide +kernel
theorem subd8_4_26 : subd8_4 [-2, -1, 0] = true := by decide +kernel
theorem subd8_4_27 : subd8_4 [-2, -1, 1] = true := by decide +kernel
theorem subd8_4_28 : subd8_4 [-2, -1, 2] = true := by decide +kernel
theorem subd8_4_29 : subd8_4 [-2, -1, 3] = true := by decide +kernel
theorem subd8_4_30 : subd8_4 [-2, -1, 4] = true := by decide +kernel
theorem subd8_4_31 : subd8_4 [-2, -1, 5] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_cons.2 ⟨subd8_4_5, List.forall_mem_cons.2 ⟨subd8_4_6, List.forall_mem_cons.2 ⟨subd8_4_7, List.forall_mem_cons.2 ⟨subd8_4_8, List.forall_mem_cons.2 ⟨subd8_4_9, List.forall_mem_cons.2 ⟨subd8_4_10, List.forall_mem_cons.2 ⟨subd8_4_11, List.forall_mem_cons.2 ⟨subd8_4_12, List.forall_mem_cons.2 ⟨subd8_4_13, List.forall_mem_cons.2 ⟨subd8_4_14, List.forall_mem_cons.2 ⟨subd8_4_15, List.forall_mem_cons.2 ⟨subd8_4_16, List.forall_mem_cons.2 ⟨subd8_4_17, List.forall_mem_cons.2 ⟨subd8_4_18, List.forall_mem_cons.2 ⟨subd8_4_19, List.forall_mem_cons.2 ⟨subd8_4_20, List.forall_mem_cons.2 ⟨subd8_4_21, List.forall_mem_cons.2 ⟨subd8_4_22, List.forall_mem_cons.2 ⟨subd8_4_23, List.forall_mem_cons.2 ⟨subd8_4_24, List.forall_mem_cons.2 ⟨subd8_4_25, List.forall_mem_cons.2 ⟨subd8_4_26, List.forall_mem_cons.2 ⟨subd8_4_27, List.forall_mem_cons.2 ⟨subd8_4_28, List.forall_mem_cons.2 ⟨subd8_4_29, List.forall_mem_cons.2 ⟨subd8_4_30, List.forall_mem_cons.2 ⟨subd8_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_32 : subd8_4 [-2, -1, 6] = true := by decide +kernel
theorem subd8_4_33 : subd8_4 [-2, -1, 7] = true := by decide +kernel
theorem subd8_4_34 : subd8_4 [-2, 0, -8] = true := by decide +kernel
theorem subd8_4_35 : subd8_4 [-2, 0, -7] = true := by decide +kernel
theorem subd8_4_36 : subd8_4 [-2, 0, -6] = true := by decide +kernel
theorem subd8_4_37 : subd8_4 [-2, 0, -5] = true := by decide +kernel
theorem subd8_4_38 : subd8_4 [-2, 0, -4] = true := by decide +kernel
theorem subd8_4_39 : subd8_4 [-2, 0, -3] = true := by decide +kernel
theorem subd8_4_40 : subd8_4 [-2, 0, -2] = true := by decide +kernel
theorem subd8_4_41 : subd8_4 [-2, 0, -1] = true := by decide +kernel
theorem subd8_4_42 : subd8_4 [-2, 0, 0] = true := by decide +kernel
theorem subd8_4_43 : subd8_4 [-2, 0, 1] = true := by decide +kernel
theorem subd8_4_44 : subd8_4 [-2, 0, 2] = true := by decide +kernel
theorem subd8_4_45 : subd8_4 [-2, 0, 3] = true := by decide +kernel
theorem subd8_4_46 : subd8_4 [-2, 0, 4] = true := by decide +kernel
theorem subd8_4_47 : subd8_4 [-2, 0, 5] = true := by decide +kernel
theorem subd8_4_48 : subd8_4 [-2, 0, 6] = true := by decide +kernel
theorem subd8_4_49 : subd8_4 [-2, 0, 7] = true := by decide +kernel
theorem subd8_4_50 : subd8_4 [-2, 1] = true := by decide +kernel
theorem subd8_4_51 : subd8_4 [-1, -4] = true := by decide +kernel
theorem subd8_4_52 : subd8_4 [-1, -3] = true := by decide +kernel
theorem subd8_4_53 : subd8_4 [-1, -2, -11] = true := by decide +kernel
theorem subd8_4_54 : subd8_4 [-1, -2, -10] = true := by decide +kernel
theorem subd8_4_55 : subd8_4 [-1, -2, -9] = true := by decide +kernel
theorem subd8_4_56 : subd8_4 [-1, -2, -8] = true := by decide +kernel
theorem subd8_4_57 : subd8_4 [-1, -2, -7] = true := by decide +kernel
theorem subd8_4_58 : subd8_4 [-1, -2, -6] = true := by decide +kernel
theorem subd8_4_59 : subd8_4 [-1, -2, -5] = true := by decide +kernel
theorem subd8_4_60 : subd8_4 [-1, -2, -4] = true := by decide +kernel
theorem subd8_4_61 : subd8_4 [-1, -2, -3] = true := by decide +kernel
theorem subd8_4_62 : subd8_4 [-1, -2, -2] = true := by decide +kernel
theorem subd8_4_63 : subd8_4 [-1, -2, -1] = true := by decide +kernel
theorem sbd8_4_1 : ∀ q ∈ blkd8_4_1, subd8_4 q = true := by
  unfold blkd8_4_1
  exact List.forall_mem_cons.2 ⟨subd8_4_32, List.forall_mem_cons.2 ⟨subd8_4_33, List.forall_mem_cons.2 ⟨subd8_4_34, List.forall_mem_cons.2 ⟨subd8_4_35, List.forall_mem_cons.2 ⟨subd8_4_36, List.forall_mem_cons.2 ⟨subd8_4_37, List.forall_mem_cons.2 ⟨subd8_4_38, List.forall_mem_cons.2 ⟨subd8_4_39, List.forall_mem_cons.2 ⟨subd8_4_40, List.forall_mem_cons.2 ⟨subd8_4_41, List.forall_mem_cons.2 ⟨subd8_4_42, List.forall_mem_cons.2 ⟨subd8_4_43, List.forall_mem_cons.2 ⟨subd8_4_44, List.forall_mem_cons.2 ⟨subd8_4_45, List.forall_mem_cons.2 ⟨subd8_4_46, List.forall_mem_cons.2 ⟨subd8_4_47, List.forall_mem_cons.2 ⟨subd8_4_48, List.forall_mem_cons.2 ⟨subd8_4_49, List.forall_mem_cons.2 ⟨subd8_4_50, List.forall_mem_cons.2 ⟨subd8_4_51, List.forall_mem_cons.2 ⟨subd8_4_52, List.forall_mem_cons.2 ⟨subd8_4_53, List.forall_mem_cons.2 ⟨subd8_4_54, List.forall_mem_cons.2 ⟨subd8_4_55, List.forall_mem_cons.2 ⟨subd8_4_56, List.forall_mem_cons.2 ⟨subd8_4_57, List.forall_mem_cons.2 ⟨subd8_4_58, List.forall_mem_cons.2 ⟨subd8_4_59, List.forall_mem_cons.2 ⟨subd8_4_60, List.forall_mem_cons.2 ⟨subd8_4_61, List.forall_mem_cons.2 ⟨subd8_4_62, List.forall_mem_cons.2 ⟨subd8_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_64 : subd8_4 [-1, -2, 0] = true := by decide +kernel
theorem subd8_4_65 : subd8_4 [-1, -2, 1] = true := by decide +kernel
theorem subd8_4_66 : subd8_4 [-1, -2, 2] = true := by decide +kernel
theorem subd8_4_67 : subd8_4 [-1, -2, 3] = true := by decide +kernel
theorem subd8_4_68 : subd8_4 [-1, -2, 4] = true := by decide +kernel
theorem subd8_4_69 : subd8_4 [-1, -2, 5] = true := by decide +kernel
theorem subd8_4_70 : subd8_4 [-1, -2, 6] = true := by decide +kernel
theorem subd8_4_71 : subd8_4 [-1, -2, 7] = true := by decide +kernel
theorem subd8_4_72 : subd8_4 [-1, -2, 8] = true := by decide +kernel
theorem subd8_4_73 : subd8_4 [-1, -1, -12] = true := by decide +kernel
theorem subd8_4_74 : subd8_4 [-1, -1, -11] = true := by decide +kernel
theorem subd8_4_75 : subd8_4 [-1, -1, -10] = true := by decide +kernel
theorem subd8_4_76 : subd8_4 [-1, -1, -9] = true := by decide +kernel
theorem subd8_4_77 : subd8_4 [-1, -1, -8] = true := by decide +kernel
theorem subd8_4_78 : subd8_4 [-1, -1, -7] = true := by decide +kernel
theorem subd8_4_79 : subd8_4 [-1, -1, -6] = true := by decide +kernel
theorem subd8_4_80 : subd8_4 [-1, -1, -5] = true := by decide +kernel
theorem subd8_4_81 : subd8_4 [-1, -1, -4] = true := by decide +kernel
theorem subd8_4_82 : subd8_4 [-1, -1, -3] = true := by decide +kernel
theorem subd8_4_83 : subd8_4 [-1, -1, -2] = true := by decide +kernel
theorem subd8_4_84 : subd8_4 [-1, -1, -1] = true := by decide +kernel
theorem subd8_4_85 : subd8_4 [-1, -1, 0] = true := by decide +kernel
theorem subd8_4_86 : subd8_4 [-1, -1, 1] = true := by decide +kernel
theorem subd8_4_87 : subd8_4 [-1, -1, 2] = true := by decide +kernel
theorem subd8_4_88 : subd8_4 [-1, -1, 3] = true := by decide +kernel
theorem subd8_4_89 : subd8_4 [-1, -1, 4] = true := by decide +kernel
theorem subd8_4_90 : subd8_4 [-1, -1, 5] = true := by decide +kernel
theorem subd8_4_91 : subd8_4 [-1, -1, 6] = true := by decide +kernel
theorem subd8_4_92 : subd8_4 [-1, -1, 7] = true := by decide +kernel
theorem subd8_4_93 : subd8_4 [-1, -1, 8] = true := by decide +kernel
theorem subd8_4_94 : subd8_4 [-1, -1, 9] = true := by decide +kernel
theorem subd8_4_95 : subd8_4 [-1, -1, 10] = true := by decide +kernel
theorem sbd8_4_2 : ∀ q ∈ blkd8_4_2, subd8_4 q = true := by
  unfold blkd8_4_2
  exact List.forall_mem_cons.2 ⟨subd8_4_64, List.forall_mem_cons.2 ⟨subd8_4_65, List.forall_mem_cons.2 ⟨subd8_4_66, List.forall_mem_cons.2 ⟨subd8_4_67, List.forall_mem_cons.2 ⟨subd8_4_68, List.forall_mem_cons.2 ⟨subd8_4_69, List.forall_mem_cons.2 ⟨subd8_4_70, List.forall_mem_cons.2 ⟨subd8_4_71, List.forall_mem_cons.2 ⟨subd8_4_72, List.forall_mem_cons.2 ⟨subd8_4_73, List.forall_mem_cons.2 ⟨subd8_4_74, List.forall_mem_cons.2 ⟨subd8_4_75, List.forall_mem_cons.2 ⟨subd8_4_76, List.forall_mem_cons.2 ⟨subd8_4_77, List.forall_mem_cons.2 ⟨subd8_4_78, List.forall_mem_cons.2 ⟨subd8_4_79, List.forall_mem_cons.2 ⟨subd8_4_80, List.forall_mem_cons.2 ⟨subd8_4_81, List.forall_mem_cons.2 ⟨subd8_4_82, List.forall_mem_cons.2 ⟨subd8_4_83, List.forall_mem_cons.2 ⟨subd8_4_84, List.forall_mem_cons.2 ⟨subd8_4_85, List.forall_mem_cons.2 ⟨subd8_4_86, List.forall_mem_cons.2 ⟨subd8_4_87, List.forall_mem_cons.2 ⟨subd8_4_88, List.forall_mem_cons.2 ⟨subd8_4_89, List.forall_mem_cons.2 ⟨subd8_4_90, List.forall_mem_cons.2 ⟨subd8_4_91, List.forall_mem_cons.2 ⟨subd8_4_92, List.forall_mem_cons.2 ⟨subd8_4_93, List.forall_mem_cons.2 ⟨subd8_4_94, List.forall_mem_cons.2 ⟨subd8_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_96 : subd8_4 [-1, 0, -12] = true := by decide +kernel
theorem subd8_4_97 : subd8_4 [-1, 0, -11] = true := by decide +kernel
theorem subd8_4_98 : subd8_4 [-1, 0, -10] = true := by decide +kernel
theorem subd8_4_99 : subd8_4 [-1, 0, -9] = true := by decide +kernel
theorem subd8_4_100 : subd8_4 [-1, 0, -8] = true := by decide +kernel
theorem subd8_4_101 : subd8_4 [-1, 0, -7] = true := by decide +kernel
theorem subd8_4_102 : subd8_4 [-1, 0, -6] = true := by decide +kernel
theorem subd8_4_103 : subd8_4 [-1, 0, -5] = true := by decide +kernel
theorem subd8_4_104 : subd8_4 [-1, 0, -4] = true := by decide +kernel
theorem subd8_4_105 : subd8_4 [-1, 0, -3] = true := by decide +kernel
theorem subd8_4_106 : subd8_4 [-1, 0, -2] = true := by decide +kernel
theorem subd8_4_107 : subd8_4 [-1, 0, -1] = true := by decide +kernel
theorem subd8_4_108 : subd8_4 [-1, 0, 0] = true := by decide +kernel
theorem subd8_4_109 : subd8_4 [-1, 0, 1] = true := by decide +kernel
theorem subd8_4_110 : subd8_4 [-1, 0, 2] = true := by decide +kernel
theorem subd8_4_111 : subd8_4 [-1, 0, 3] = true := by decide +kernel
theorem subd8_4_112 : subd8_4 [-1, 0, 4] = true := by decide +kernel
theorem subd8_4_113 : subd8_4 [-1, 0, 5] = true := by decide +kernel
theorem subd8_4_114 : subd8_4 [-1, 0, 6] = true := by decide +kernel
theorem subd8_4_115 : subd8_4 [-1, 0, 7] = true := by decide +kernel
theorem subd8_4_116 : subd8_4 [-1, 0, 8] = true := by decide +kernel
theorem subd8_4_117 : subd8_4 [-1, 0, 9] = true := by decide +kernel
theorem subd8_4_118 : subd8_4 [-1, 0, 10] = true := by decide +kernel
theorem subd8_4_119 : subd8_4 [-1, 0, 11] = true := by decide +kernel
theorem subd8_4_120 : subd8_4 [-1, 1, -10] = true := by decide +kernel
theorem subd8_4_121 : subd8_4 [-1, 1, -9] = true := by decide +kernel
theorem subd8_4_122 : subd8_4 [-1, 1, -8] = true := by decide +kernel
theorem subd8_4_123 : subd8_4 [-1, 1, -7] = true := by decide +kernel
theorem subd8_4_124 : subd8_4 [-1, 1, -6] = true := by decide +kernel
theorem subd8_4_125 : subd8_4 [-1, 1, -5] = true := by decide +kernel
theorem subd8_4_126 : subd8_4 [-1, 1, -4] = true := by decide +kernel
theorem subd8_4_127 : subd8_4 [-1, 1, -3] = true := by decide +kernel
theorem sbd8_4_3 : ∀ q ∈ blkd8_4_3, subd8_4 q = true := by
  unfold blkd8_4_3
  exact List.forall_mem_cons.2 ⟨subd8_4_96, List.forall_mem_cons.2 ⟨subd8_4_97, List.forall_mem_cons.2 ⟨subd8_4_98, List.forall_mem_cons.2 ⟨subd8_4_99, List.forall_mem_cons.2 ⟨subd8_4_100, List.forall_mem_cons.2 ⟨subd8_4_101, List.forall_mem_cons.2 ⟨subd8_4_102, List.forall_mem_cons.2 ⟨subd8_4_103, List.forall_mem_cons.2 ⟨subd8_4_104, List.forall_mem_cons.2 ⟨subd8_4_105, List.forall_mem_cons.2 ⟨subd8_4_106, List.forall_mem_cons.2 ⟨subd8_4_107, List.forall_mem_cons.2 ⟨subd8_4_108, List.forall_mem_cons.2 ⟨subd8_4_109, List.forall_mem_cons.2 ⟨subd8_4_110, List.forall_mem_cons.2 ⟨subd8_4_111, List.forall_mem_cons.2 ⟨subd8_4_112, List.forall_mem_cons.2 ⟨subd8_4_113, List.forall_mem_cons.2 ⟨subd8_4_114, List.forall_mem_cons.2 ⟨subd8_4_115, List.forall_mem_cons.2 ⟨subd8_4_116, List.forall_mem_cons.2 ⟨subd8_4_117, List.forall_mem_cons.2 ⟨subd8_4_118, List.forall_mem_cons.2 ⟨subd8_4_119, List.forall_mem_cons.2 ⟨subd8_4_120, List.forall_mem_cons.2 ⟨subd8_4_121, List.forall_mem_cons.2 ⟨subd8_4_122, List.forall_mem_cons.2 ⟨subd8_4_123, List.forall_mem_cons.2 ⟨subd8_4_124, List.forall_mem_cons.2 ⟨subd8_4_125, List.forall_mem_cons.2 ⟨subd8_4_126, List.forall_mem_cons.2 ⟨subd8_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_128 : subd8_4 [-1, 1, -2] = true := by decide +kernel
theorem subd8_4_129 : subd8_4 [-1, 1, -1] = true := by decide +kernel
theorem subd8_4_130 : subd8_4 [-1, 1, 0] = true := by decide +kernel
theorem subd8_4_131 : subd8_4 [-1, 1, 1] = true := by decide +kernel
theorem subd8_4_132 : subd8_4 [-1, 1, 2] = true := by decide +kernel
theorem subd8_4_133 : subd8_4 [-1, 1, 3] = true := by decide +kernel
theorem subd8_4_134 : subd8_4 [-1, 1, 4] = true := by decide +kernel
theorem subd8_4_135 : subd8_4 [-1, 1, 5] = true := by decide +kernel
theorem subd8_4_136 : subd8_4 [-1, 1, 6] = true := by decide +kernel
theorem subd8_4_137 : subd8_4 [-1, 1, 7] = true := by decide +kernel
theorem subd8_4_138 : subd8_4 [-1, 1, 8] = true := by decide +kernel
theorem subd8_4_139 : subd8_4 [-1, 1, 9] = true := by decide +kernel
theorem subd8_4_140 : subd8_4 [-1, 1, 10] = true := by decide +kernel
theorem subd8_4_141 : subd8_4 [-1, 2] = true := by decide +kernel
theorem subd8_4_142 : subd8_4 [0, -4] = true := by decide +kernel
theorem subd8_4_143 : subd8_4 [0, -3] = true := by decide +kernel
theorem subd8_4_144 : subd8_4 [0, -2, -10] = true := by decide +kernel
theorem subd8_4_145 : subd8_4 [0, -2, -9] = true := by decide +kernel
theorem subd8_4_146 : subd8_4 [0, -2, -8] = true := by decide +kernel
theorem subd8_4_147 : subd8_4 [0, -2, -7] = true := by decide +kernel
theorem subd8_4_148 : subd8_4 [0, -2, -6] = true := by decide +kernel
theorem subd8_4_149 : subd8_4 [0, -2, -5] = true := by decide +kernel
theorem subd8_4_150 : subd8_4 [0, -2, -4] = true := by decide +kernel
theorem subd8_4_151 : subd8_4 [0, -2, -3] = true := by decide +kernel
theorem subd8_4_152 : subd8_4 [0, -2, -2] = true := by decide +kernel
theorem subd8_4_153 : subd8_4 [0, -2, -1] = true := by decide +kernel
theorem subd8_4_154 : subd8_4 [0, -2, 0] = true := by decide +kernel
theorem subd8_4_155 : subd8_4 [0, -2, 1] = true := by decide +kernel
theorem subd8_4_156 : subd8_4 [0, -2, 2] = true := by decide +kernel
theorem subd8_4_157 : subd8_4 [0, -2, 3] = true := by decide +kernel
theorem subd8_4_158 : subd8_4 [0, -2, 4] = true := by decide +kernel
theorem subd8_4_159 : subd8_4 [0, -2, 5] = true := by decide +kernel
theorem sbd8_4_4 : ∀ q ∈ blkd8_4_4, subd8_4 q = true := by
  unfold blkd8_4_4
  exact List.forall_mem_cons.2 ⟨subd8_4_128, List.forall_mem_cons.2 ⟨subd8_4_129, List.forall_mem_cons.2 ⟨subd8_4_130, List.forall_mem_cons.2 ⟨subd8_4_131, List.forall_mem_cons.2 ⟨subd8_4_132, List.forall_mem_cons.2 ⟨subd8_4_133, List.forall_mem_cons.2 ⟨subd8_4_134, List.forall_mem_cons.2 ⟨subd8_4_135, List.forall_mem_cons.2 ⟨subd8_4_136, List.forall_mem_cons.2 ⟨subd8_4_137, List.forall_mem_cons.2 ⟨subd8_4_138, List.forall_mem_cons.2 ⟨subd8_4_139, List.forall_mem_cons.2 ⟨subd8_4_140, List.forall_mem_cons.2 ⟨subd8_4_141, List.forall_mem_cons.2 ⟨subd8_4_142, List.forall_mem_cons.2 ⟨subd8_4_143, List.forall_mem_cons.2 ⟨subd8_4_144, List.forall_mem_cons.2 ⟨subd8_4_145, List.forall_mem_cons.2 ⟨subd8_4_146, List.forall_mem_cons.2 ⟨subd8_4_147, List.forall_mem_cons.2 ⟨subd8_4_148, List.forall_mem_cons.2 ⟨subd8_4_149, List.forall_mem_cons.2 ⟨subd8_4_150, List.forall_mem_cons.2 ⟨subd8_4_151, List.forall_mem_cons.2 ⟨subd8_4_152, List.forall_mem_cons.2 ⟨subd8_4_153, List.forall_mem_cons.2 ⟨subd8_4_154, List.forall_mem_cons.2 ⟨subd8_4_155, List.forall_mem_cons.2 ⟨subd8_4_156, List.forall_mem_cons.2 ⟨subd8_4_157, List.forall_mem_cons.2 ⟨subd8_4_158, List.forall_mem_cons.2 ⟨subd8_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_160 : subd8_4 [0, -2, 6] = true := by decide +kernel
theorem subd8_4_161 : subd8_4 [0, -2, 7] = true := by decide +kernel
theorem subd8_4_162 : subd8_4 [0, -2, 8] = true := by decide +kernel
theorem subd8_4_163 : subd8_4 [0, -1, -12] = true := by decide +kernel
theorem subd8_4_164 : subd8_4 [0, -1, -11] = true := by decide +kernel
theorem subd8_4_165 : subd8_4 [0, -1, -10] = true := by decide +kernel
theorem subd8_4_166 : subd8_4 [0, -1, -9] = true := by decide +kernel
theorem subd8_4_167 : subd8_4 [0, -1, -8] = true := by decide +kernel
theorem subd8_4_168 : subd8_4 [0, -1, -7] = true := by decide +kernel
theorem subd8_4_169 : subd8_4 [0, -1, -6] = true := by decide +kernel
theorem subd8_4_170 : subd8_4 [0, -1, -5] = true := by decide +kernel
theorem subd8_4_171 : subd8_4 [0, -1, -4] = true := by decide +kernel
theorem subd8_4_172 : subd8_4 [0, -1, -3] = true := by decide +kernel
theorem subd8_4_173 : subd8_4 [0, -1, -2] = true := by decide +kernel
theorem subd8_4_174 : subd8_4 [0, -1, -1] = true := by decide +kernel
theorem subd8_4_175 : subd8_4 [0, -1, 0] = true := by decide +kernel
theorem subd8_4_176 : subd8_4 [0, -1, 1] = true := by decide +kernel
theorem subd8_4_177 : subd8_4 [0, -1, 2] = true := by decide +kernel
theorem subd8_4_178 : subd8_4 [0, -1, 3] = true := by decide +kernel
theorem subd8_4_179 : subd8_4 [0, -1, 4] = true := by decide +kernel
theorem subd8_4_180 : subd8_4 [0, -1, 5] = true := by decide +kernel
theorem subd8_4_181 : subd8_4 [0, -1, 6] = true := by decide +kernel
theorem subd8_4_182 : subd8_4 [0, -1, 7] = true := by decide +kernel
theorem subd8_4_183 : subd8_4 [0, -1, 8] = true := by decide +kernel
theorem subd8_4_184 : subd8_4 [0, -1, 9] = true := by decide +kernel
theorem subd8_4_185 : subd8_4 [0, -1, 10] = true := by decide +kernel
theorem subd8_4_186 : subd8_4 [0, -1, 11] = true := by decide +kernel
theorem subd8_4_187 : subd8_4 [0, 0, -13] = true := by decide +kernel
theorem subd8_4_188 : subd8_4 [0, 0, -12] = true := by decide +kernel
theorem subd8_4_189 : subd8_4 [0, 0, -11] = true := by decide +kernel
theorem subd8_4_190 : subd8_4 [0, 0, -10] = true := by decide +kernel
theorem subd8_4_191 : subd8_4 [0, 0, -9] = true := by decide +kernel
theorem sbd8_4_5 : ∀ q ∈ blkd8_4_5, subd8_4 q = true := by
  unfold blkd8_4_5
  exact List.forall_mem_cons.2 ⟨subd8_4_160, List.forall_mem_cons.2 ⟨subd8_4_161, List.forall_mem_cons.2 ⟨subd8_4_162, List.forall_mem_cons.2 ⟨subd8_4_163, List.forall_mem_cons.2 ⟨subd8_4_164, List.forall_mem_cons.2 ⟨subd8_4_165, List.forall_mem_cons.2 ⟨subd8_4_166, List.forall_mem_cons.2 ⟨subd8_4_167, List.forall_mem_cons.2 ⟨subd8_4_168, List.forall_mem_cons.2 ⟨subd8_4_169, List.forall_mem_cons.2 ⟨subd8_4_170, List.forall_mem_cons.2 ⟨subd8_4_171, List.forall_mem_cons.2 ⟨subd8_4_172, List.forall_mem_cons.2 ⟨subd8_4_173, List.forall_mem_cons.2 ⟨subd8_4_174, List.forall_mem_cons.2 ⟨subd8_4_175, List.forall_mem_cons.2 ⟨subd8_4_176, List.forall_mem_cons.2 ⟨subd8_4_177, List.forall_mem_cons.2 ⟨subd8_4_178, List.forall_mem_cons.2 ⟨subd8_4_179, List.forall_mem_cons.2 ⟨subd8_4_180, List.forall_mem_cons.2 ⟨subd8_4_181, List.forall_mem_cons.2 ⟨subd8_4_182, List.forall_mem_cons.2 ⟨subd8_4_183, List.forall_mem_cons.2 ⟨subd8_4_184, List.forall_mem_cons.2 ⟨subd8_4_185, List.forall_mem_cons.2 ⟨subd8_4_186, List.forall_mem_cons.2 ⟨subd8_4_187, List.forall_mem_cons.2 ⟨subd8_4_188, List.forall_mem_cons.2 ⟨subd8_4_189, List.forall_mem_cons.2 ⟨subd8_4_190, List.forall_mem_cons.2 ⟨subd8_4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_192 : subd8_4 [0, 0, -8] = true := by decide +kernel
theorem subd8_4_193 : subd8_4 [0, 0, -7] = true := by decide +kernel
theorem subd8_4_194 : subd8_4 [0, 0, -6] = true := by decide +kernel
theorem subd8_4_195 : subd8_4 [0, 0, -5] = true := by decide +kernel
theorem subd8_4_196 : subd8_4 [0, 0, -4] = true := by decide +kernel
theorem subd8_4_197 : subd8_4 [0, 0, -3] = true := by decide +kernel
theorem subd8_4_198 : subd8_4 [0, 0, -2] = true := by decide +kernel
theorem subd8_4_199 : subd8_4 [0, 0, -1] = true := by decide +kernel
theorem subd8_4_200 : subd8_4 [0, 0, 0] = true := by decide +kernel
theorem subd8_4_201 : subd8_4 [0, 0, 1] = true := by decide +kernel
theorem subd8_4_202 : subd8_4 [0, 0, 2] = true := by decide +kernel
theorem subd8_4_203 : subd8_4 [0, 0, 3] = true := by decide +kernel
theorem subd8_4_204 : subd8_4 [0, 0, 4] = true := by decide +kernel
theorem subd8_4_205 : subd8_4 [0, 0, 5] = true := by decide +kernel
theorem subd8_4_206 : subd8_4 [0, 0, 6] = true := by decide +kernel
theorem subd8_4_207 : subd8_4 [0, 0, 7] = true := by decide +kernel
theorem subd8_4_208 : subd8_4 [0, 0, 8] = true := by decide +kernel
theorem subd8_4_209 : subd8_4 [0, 0, 9] = true := by decide +kernel
theorem subd8_4_210 : subd8_4 [0, 0, 10] = true := by decide +kernel
theorem subd8_4_211 : subd8_4 [0, 0, 11] = true := by decide +kernel
theorem subd8_4_212 : subd8_4 [0, 0, 12] = true := by decide +kernel
theorem subd8_4_213 : subd8_4 [0, 1, -12] = true := by decide +kernel
theorem subd8_4_214 : subd8_4 [0, 1, -11] = true := by decide +kernel
theorem subd8_4_215 : subd8_4 [0, 1, -10] = true := by decide +kernel
theorem subd8_4_216 : subd8_4 [0, 1, -9] = true := by decide +kernel
theorem subd8_4_217 : subd8_4 [0, 1, -8] = true := by decide +kernel
theorem subd8_4_218 : subd8_4 [0, 1, -7] = true := by decide +kernel
theorem subd8_4_219 : subd8_4 [0, 1, -6] = true := by decide +kernel
theorem subd8_4_220 : subd8_4 [0, 1, -5] = true := by decide +kernel
theorem subd8_4_221 : subd8_4 [0, 1, -4] = true := by decide +kernel
theorem subd8_4_222 : subd8_4 [0, 1, -3] = true := by decide +kernel
theorem subd8_4_223 : subd8_4 [0, 1, -2] = true := by decide +kernel
theorem sbd8_4_6 : ∀ q ∈ blkd8_4_6, subd8_4 q = true := by
  unfold blkd8_4_6
  exact List.forall_mem_cons.2 ⟨subd8_4_192, List.forall_mem_cons.2 ⟨subd8_4_193, List.forall_mem_cons.2 ⟨subd8_4_194, List.forall_mem_cons.2 ⟨subd8_4_195, List.forall_mem_cons.2 ⟨subd8_4_196, List.forall_mem_cons.2 ⟨subd8_4_197, List.forall_mem_cons.2 ⟨subd8_4_198, List.forall_mem_cons.2 ⟨subd8_4_199, List.forall_mem_cons.2 ⟨subd8_4_200, List.forall_mem_cons.2 ⟨subd8_4_201, List.forall_mem_cons.2 ⟨subd8_4_202, List.forall_mem_cons.2 ⟨subd8_4_203, List.forall_mem_cons.2 ⟨subd8_4_204, List.forall_mem_cons.2 ⟨subd8_4_205, List.forall_mem_cons.2 ⟨subd8_4_206, List.forall_mem_cons.2 ⟨subd8_4_207, List.forall_mem_cons.2 ⟨subd8_4_208, List.forall_mem_cons.2 ⟨subd8_4_209, List.forall_mem_cons.2 ⟨subd8_4_210, List.forall_mem_cons.2 ⟨subd8_4_211, List.forall_mem_cons.2 ⟨subd8_4_212, List.forall_mem_cons.2 ⟨subd8_4_213, List.forall_mem_cons.2 ⟨subd8_4_214, List.forall_mem_cons.2 ⟨subd8_4_215, List.forall_mem_cons.2 ⟨subd8_4_216, List.forall_mem_cons.2 ⟨subd8_4_217, List.forall_mem_cons.2 ⟨subd8_4_218, List.forall_mem_cons.2 ⟨subd8_4_219, List.forall_mem_cons.2 ⟨subd8_4_220, List.forall_mem_cons.2 ⟨subd8_4_221, List.forall_mem_cons.2 ⟨subd8_4_222, List.forall_mem_cons.2 ⟨subd8_4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_224 : subd8_4 [0, 1, -1] = true := by decide +kernel
theorem subd8_4_225 : subd8_4 [0, 1, 0] = true := by decide +kernel
theorem subd8_4_226 : subd8_4 [0, 1, 1] = true := by decide +kernel
theorem subd8_4_227 : subd8_4 [0, 1, 2] = true := by decide +kernel
theorem subd8_4_228 : subd8_4 [0, 1, 3] = true := by decide +kernel
theorem subd8_4_229 : subd8_4 [0, 1, 4] = true := by decide +kernel
theorem subd8_4_230 : subd8_4 [0, 1, 5] = true := by decide +kernel
theorem subd8_4_231 : subd8_4 [0, 1, 6] = true := by decide +kernel
theorem subd8_4_232 : subd8_4 [0, 1, 7] = true := by decide +kernel
theorem subd8_4_233 : subd8_4 [0, 1, 8] = true := by decide +kernel
theorem subd8_4_234 : subd8_4 [0, 1, 9] = true := by decide +kernel
theorem subd8_4_235 : subd8_4 [0, 1, 10] = true := by decide +kernel
theorem subd8_4_236 : subd8_4 [0, 1, 11] = true := by decide +kernel
theorem subd8_4_237 : subd8_4 [0, 2, -9] = true := by decide +kernel
theorem subd8_4_238 : subd8_4 [0, 2, -8] = true := by decide +kernel
theorem subd8_4_239 : subd8_4 [0, 2, -7] = true := by decide +kernel
theorem subd8_4_240 : subd8_4 [0, 2, -6] = true := by decide +kernel
theorem subd8_4_241 : subd8_4 [0, 2, -5] = true := by decide +kernel
theorem subd8_4_242 : subd8_4 [0, 2, -4] = true := by decide +kernel
theorem subd8_4_243 : subd8_4 [0, 2, -3] = true := by decide +kernel
theorem subd8_4_244 : subd8_4 [0, 2, -2] = true := by decide +kernel
theorem subd8_4_245 : subd8_4 [0, 2, -1] = true := by decide +kernel
theorem subd8_4_246 : subd8_4 [0, 2, 0] = true := by decide +kernel
theorem subd8_4_247 : subd8_4 [0, 2, 1] = true := by decide +kernel
theorem subd8_4_248 : subd8_4 [0, 2, 2] = true := by decide +kernel
theorem subd8_4_249 : subd8_4 [0, 2, 3] = true := by decide +kernel
theorem subd8_4_250 : subd8_4 [0, 2, 4] = true := by decide +kernel
theorem subd8_4_251 : subd8_4 [0, 2, 5] = true := by decide +kernel
theorem subd8_4_252 : subd8_4 [0, 2, 6] = true := by decide +kernel
theorem subd8_4_253 : subd8_4 [0, 2, 7] = true := by decide +kernel
theorem subd8_4_254 : subd8_4 [0, 2, 8] = true := by decide +kernel
theorem subd8_4_255 : subd8_4 [0, 2, 9] = true := by decide +kernel
theorem sbd8_4_7 : ∀ q ∈ blkd8_4_7, subd8_4 q = true := by
  unfold blkd8_4_7
  exact List.forall_mem_cons.2 ⟨subd8_4_224, List.forall_mem_cons.2 ⟨subd8_4_225, List.forall_mem_cons.2 ⟨subd8_4_226, List.forall_mem_cons.2 ⟨subd8_4_227, List.forall_mem_cons.2 ⟨subd8_4_228, List.forall_mem_cons.2 ⟨subd8_4_229, List.forall_mem_cons.2 ⟨subd8_4_230, List.forall_mem_cons.2 ⟨subd8_4_231, List.forall_mem_cons.2 ⟨subd8_4_232, List.forall_mem_cons.2 ⟨subd8_4_233, List.forall_mem_cons.2 ⟨subd8_4_234, List.forall_mem_cons.2 ⟨subd8_4_235, List.forall_mem_cons.2 ⟨subd8_4_236, List.forall_mem_cons.2 ⟨subd8_4_237, List.forall_mem_cons.2 ⟨subd8_4_238, List.forall_mem_cons.2 ⟨subd8_4_239, List.forall_mem_cons.2 ⟨subd8_4_240, List.forall_mem_cons.2 ⟨subd8_4_241, List.forall_mem_cons.2 ⟨subd8_4_242, List.forall_mem_cons.2 ⟨subd8_4_243, List.forall_mem_cons.2 ⟨subd8_4_244, List.forall_mem_cons.2 ⟨subd8_4_245, List.forall_mem_cons.2 ⟨subd8_4_246, List.forall_mem_cons.2 ⟨subd8_4_247, List.forall_mem_cons.2 ⟨subd8_4_248, List.forall_mem_cons.2 ⟨subd8_4_249, List.forall_mem_cons.2 ⟨subd8_4_250, List.forall_mem_cons.2 ⟨subd8_4_251, List.forall_mem_cons.2 ⟨subd8_4_252, List.forall_mem_cons.2 ⟨subd8_4_253, List.forall_mem_cons.2 ⟨subd8_4_254, List.forall_mem_cons.2 ⟨subd8_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_256 : subd8_4 [0, 3] = true := by decide +kernel
theorem subd8_4_257 : subd8_4 [1, -3] = true := by decide +kernel
theorem subd8_4_258 : subd8_4 [1, -2] = true := by decide +kernel
theorem subd8_4_259 : subd8_4 [1, -1, -11] = true := by decide +kernel
theorem subd8_4_260 : subd8_4 [1, -1, -10] = true := by decide +kernel
theorem subd8_4_261 : subd8_4 [1, -1, -9] = true := by decide +kernel
theorem subd8_4_262 : subd8_4 [1, -1, -8] = true := by decide +kernel
theorem subd8_4_263 : subd8_4 [1, -1, -7] = true := by decide +kernel
theorem subd8_4_264 : subd8_4 [1, -1, -6] = true := by decide +kernel
theorem subd8_4_265 : subd8_4 [1, -1, -5] = true := by decide +kernel
theorem subd8_4_266 : subd8_4 [1, -1, -4] = true := by decide +kernel
theorem subd8_4_267 : subd8_4 [1, -1, -3] = true := by decide +kernel
theorem subd8_4_268 : subd8_4 [1, -1, -2] = true := by decide +kernel
theorem subd8_4_269 : subd8_4 [1, -1, -1] = true := by decide +kernel
theorem subd8_4_270 : subd8_4 [1, -1, 0] = true := by decide +kernel
theorem subd8_4_271 : subd8_4 [1, -1, 1] = true := by decide +kernel
theorem subd8_4_272 : subd8_4 [1, -1, 2] = true := by decide +kernel
theorem subd8_4_273 : subd8_4 [1, -1, 3] = true := by decide +kernel
theorem subd8_4_274 : subd8_4 [1, -1, 4] = true := by decide +kernel
theorem subd8_4_275 : subd8_4 [1, -1, 5] = true := by decide +kernel
theorem subd8_4_276 : subd8_4 [1, -1, 6] = true := by decide +kernel
theorem subd8_4_277 : subd8_4 [1, -1, 7] = true := by decide +kernel
theorem subd8_4_278 : subd8_4 [1, -1, 8] = true := by decide +kernel
theorem subd8_4_279 : subd8_4 [1, -1, 9] = true := by decide +kernel
theorem subd8_4_280 : subd8_4 [1, 0, -12] = true := by decide +kernel
theorem subd8_4_281 : subd8_4 [1, 0, -11] = true := by decide +kernel
theorem subd8_4_282 : subd8_4 [1, 0, -10] = true := by decide +kernel
theorem subd8_4_283 : subd8_4 [1, 0, -9] = true := by decide +kernel
theorem subd8_4_284 : subd8_4 [1, 0, -8] = true := by decide +kernel
theorem subd8_4_285 : subd8_4 [1, 0, -7] = true := by decide +kernel
theorem subd8_4_286 : subd8_4 [1, 0, -6] = true := by decide +kernel
theorem subd8_4_287 : subd8_4 [1, 0, -5] = true := by decide +kernel
theorem sbd8_4_8 : ∀ q ∈ blkd8_4_8, subd8_4 q = true := by
  unfold blkd8_4_8
  exact List.forall_mem_cons.2 ⟨subd8_4_256, List.forall_mem_cons.2 ⟨subd8_4_257, List.forall_mem_cons.2 ⟨subd8_4_258, List.forall_mem_cons.2 ⟨subd8_4_259, List.forall_mem_cons.2 ⟨subd8_4_260, List.forall_mem_cons.2 ⟨subd8_4_261, List.forall_mem_cons.2 ⟨subd8_4_262, List.forall_mem_cons.2 ⟨subd8_4_263, List.forall_mem_cons.2 ⟨subd8_4_264, List.forall_mem_cons.2 ⟨subd8_4_265, List.forall_mem_cons.2 ⟨subd8_4_266, List.forall_mem_cons.2 ⟨subd8_4_267, List.forall_mem_cons.2 ⟨subd8_4_268, List.forall_mem_cons.2 ⟨subd8_4_269, List.forall_mem_cons.2 ⟨subd8_4_270, List.forall_mem_cons.2 ⟨subd8_4_271, List.forall_mem_cons.2 ⟨subd8_4_272, List.forall_mem_cons.2 ⟨subd8_4_273, List.forall_mem_cons.2 ⟨subd8_4_274, List.forall_mem_cons.2 ⟨subd8_4_275, List.forall_mem_cons.2 ⟨subd8_4_276, List.forall_mem_cons.2 ⟨subd8_4_277, List.forall_mem_cons.2 ⟨subd8_4_278, List.forall_mem_cons.2 ⟨subd8_4_279, List.forall_mem_cons.2 ⟨subd8_4_280, List.forall_mem_cons.2 ⟨subd8_4_281, List.forall_mem_cons.2 ⟨subd8_4_282, List.forall_mem_cons.2 ⟨subd8_4_283, List.forall_mem_cons.2 ⟨subd8_4_284, List.forall_mem_cons.2 ⟨subd8_4_285, List.forall_mem_cons.2 ⟨subd8_4_286, List.forall_mem_cons.2 ⟨subd8_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_288 : subd8_4 [1, 0, -4] = true := by decide +kernel
theorem subd8_4_289 : subd8_4 [1, 0, -3] = true := by decide +kernel
theorem subd8_4_290 : subd8_4 [1, 0, -2] = true := by decide +kernel
theorem subd8_4_291 : subd8_4 [1, 0, -1] = true := by decide +kernel
theorem subd8_4_292 : subd8_4 [1, 0, 0] = true := by decide +kernel
theorem subd8_4_293 : subd8_4 [1, 0, 1] = true := by decide +kernel
theorem subd8_4_294 : subd8_4 [1, 0, 2] = true := by decide +kernel
theorem subd8_4_295 : subd8_4 [1, 0, 3] = true := by decide +kernel
theorem subd8_4_296 : subd8_4 [1, 0, 4] = true := by decide +kernel
theorem subd8_4_297 : subd8_4 [1, 0, 5] = true := by decide +kernel
theorem subd8_4_298 : subd8_4 [1, 0, 6] = true := by decide +kernel
theorem subd8_4_299 : subd8_4 [1, 0, 7] = true := by decide +kernel
theorem subd8_4_300 : subd8_4 [1, 0, 8] = true := by decide +kernel
theorem subd8_4_301 : subd8_4 [1, 0, 9] = true := by decide +kernel
theorem subd8_4_302 : subd8_4 [1, 0, 10] = true := by decide +kernel
theorem subd8_4_303 : subd8_4 [1, 0, 11] = true := by decide +kernel
theorem subd8_4_304 : subd8_4 [1, 1, -11] = true := by decide +kernel
theorem subd8_4_305 : subd8_4 [1, 1, -10] = true := by decide +kernel
theorem subd8_4_306 : subd8_4 [1, 1, -9] = true := by decide +kernel
theorem subd8_4_307 : subd8_4 [1, 1, -8] = true := by decide +kernel
theorem subd8_4_308 : subd8_4 [1, 1, -7] = true := by decide +kernel
theorem subd8_4_309 : subd8_4 [1, 1, -6] = true := by decide +kernel
theorem subd8_4_310 : subd8_4 [1, 1, -5] = true := by decide +kernel
theorem subd8_4_311 : subd8_4 [1, 1, -4] = true := by decide +kernel
theorem subd8_4_312 : subd8_4 [1, 1, -3] = true := by decide +kernel
theorem subd8_4_313 : subd8_4 [1, 1, -2] = true := by decide +kernel
theorem subd8_4_314 : subd8_4 [1, 1, -1] = true := by decide +kernel
theorem subd8_4_315 : subd8_4 [1, 1, 0] = true := by decide +kernel
theorem subd8_4_316 : subd8_4 [1, 1, 1] = true := by decide +kernel
theorem subd8_4_317 : subd8_4 [1, 1, 2] = true := by decide +kernel
theorem subd8_4_318 : subd8_4 [1, 1, 3] = true := by decide +kernel
theorem subd8_4_319 : subd8_4 [1, 1, 4] = true := by decide +kernel
theorem sbd8_4_9 : ∀ q ∈ blkd8_4_9, subd8_4 q = true := by
  unfold blkd8_4_9
  exact List.forall_mem_cons.2 ⟨subd8_4_288, List.forall_mem_cons.2 ⟨subd8_4_289, List.forall_mem_cons.2 ⟨subd8_4_290, List.forall_mem_cons.2 ⟨subd8_4_291, List.forall_mem_cons.2 ⟨subd8_4_292, List.forall_mem_cons.2 ⟨subd8_4_293, List.forall_mem_cons.2 ⟨subd8_4_294, List.forall_mem_cons.2 ⟨subd8_4_295, List.forall_mem_cons.2 ⟨subd8_4_296, List.forall_mem_cons.2 ⟨subd8_4_297, List.forall_mem_cons.2 ⟨subd8_4_298, List.forall_mem_cons.2 ⟨subd8_4_299, List.forall_mem_cons.2 ⟨subd8_4_300, List.forall_mem_cons.2 ⟨subd8_4_301, List.forall_mem_cons.2 ⟨subd8_4_302, List.forall_mem_cons.2 ⟨subd8_4_303, List.forall_mem_cons.2 ⟨subd8_4_304, List.forall_mem_cons.2 ⟨subd8_4_305, List.forall_mem_cons.2 ⟨subd8_4_306, List.forall_mem_cons.2 ⟨subd8_4_307, List.forall_mem_cons.2 ⟨subd8_4_308, List.forall_mem_cons.2 ⟨subd8_4_309, List.forall_mem_cons.2 ⟨subd8_4_310, List.forall_mem_cons.2 ⟨subd8_4_311, List.forall_mem_cons.2 ⟨subd8_4_312, List.forall_mem_cons.2 ⟨subd8_4_313, List.forall_mem_cons.2 ⟨subd8_4_314, List.forall_mem_cons.2 ⟨subd8_4_315, List.forall_mem_cons.2 ⟨subd8_4_316, List.forall_mem_cons.2 ⟨subd8_4_317, List.forall_mem_cons.2 ⟨subd8_4_318, List.forall_mem_cons.2 ⟨subd8_4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_320 : subd8_4 [1, 1, 5] = true := by decide +kernel
theorem subd8_4_321 : subd8_4 [1, 1, 6] = true := by decide +kernel
theorem subd8_4_322 : subd8_4 [1, 1, 7] = true := by decide +kernel
theorem subd8_4_323 : subd8_4 [1, 1, 8] = true := by decide +kernel
theorem subd8_4_324 : subd8_4 [1, 1, 9] = true := by decide +kernel
theorem subd8_4_325 : subd8_4 [1, 1, 10] = true := by decide +kernel
theorem subd8_4_326 : subd8_4 [1, 1, 11] = true := by decide +kernel
theorem subd8_4_327 : subd8_4 [1, 2, -9] = true := by decide +kernel
theorem subd8_4_328 : subd8_4 [1, 2, -8] = true := by decide +kernel
theorem subd8_4_329 : subd8_4 [1, 2, -7] = true := by decide +kernel
theorem subd8_4_330 : subd8_4 [1, 2, -6] = true := by decide +kernel
theorem subd8_4_331 : subd8_4 [1, 2, -5] = true := by decide +kernel
theorem subd8_4_332 : subd8_4 [1, 2, -4] = true := by decide +kernel
theorem subd8_4_333 : subd8_4 [1, 2, -3] = true := by decide +kernel
theorem subd8_4_334 : subd8_4 [1, 2, -2] = true := by decide +kernel
theorem subd8_4_335 : subd8_4 [1, 2, -1] = true := by decide +kernel
theorem subd8_4_336 : subd8_4 [1, 2, 0] = true := by decide +kernel
theorem subd8_4_337 : subd8_4 [1, 2, 1] = true := by decide +kernel
theorem subd8_4_338 : subd8_4 [1, 2, 2] = true := by decide +kernel
theorem subd8_4_339 : subd8_4 [1, 2, 3] = true := by decide +kernel
theorem subd8_4_340 : subd8_4 [1, 2, 4] = true := by decide +kernel
theorem subd8_4_341 : subd8_4 [1, 2, 5] = true := by decide +kernel
theorem subd8_4_342 : subd8_4 [1, 2, 6] = true := by decide +kernel
theorem subd8_4_343 : subd8_4 [1, 2, 7] = true := by decide +kernel
theorem subd8_4_344 : subd8_4 [1, 2, 8] = true := by decide +kernel
theorem subd8_4_345 : subd8_4 [1, 2, 9] = true := by decide +kernel
theorem subd8_4_346 : subd8_4 [1, 2, 10] = true := by decide +kernel
theorem subd8_4_347 : subd8_4 [1, 3] = true := by decide +kernel
theorem subd8_4_348 : subd8_4 [2, -2] = true := by decide +kernel
theorem subd8_4_349 : subd8_4 [2, -1] = true := by decide +kernel
theorem subd8_4_350 : subd8_4 [2, 0, -8] = true := by decide +kernel
theorem subd8_4_351 : subd8_4 [2, 0, -7] = true := by decide +kernel
theorem sbd8_4_10 : ∀ q ∈ blkd8_4_10, subd8_4 q = true := by
  unfold blkd8_4_10
  exact List.forall_mem_cons.2 ⟨subd8_4_320, List.forall_mem_cons.2 ⟨subd8_4_321, List.forall_mem_cons.2 ⟨subd8_4_322, List.forall_mem_cons.2 ⟨subd8_4_323, List.forall_mem_cons.2 ⟨subd8_4_324, List.forall_mem_cons.2 ⟨subd8_4_325, List.forall_mem_cons.2 ⟨subd8_4_326, List.forall_mem_cons.2 ⟨subd8_4_327, List.forall_mem_cons.2 ⟨subd8_4_328, List.forall_mem_cons.2 ⟨subd8_4_329, List.forall_mem_cons.2 ⟨subd8_4_330, List.forall_mem_cons.2 ⟨subd8_4_331, List.forall_mem_cons.2 ⟨subd8_4_332, List.forall_mem_cons.2 ⟨subd8_4_333, List.forall_mem_cons.2 ⟨subd8_4_334, List.forall_mem_cons.2 ⟨subd8_4_335, List.forall_mem_cons.2 ⟨subd8_4_336, List.forall_mem_cons.2 ⟨subd8_4_337, List.forall_mem_cons.2 ⟨subd8_4_338, List.forall_mem_cons.2 ⟨subd8_4_339, List.forall_mem_cons.2 ⟨subd8_4_340, List.forall_mem_cons.2 ⟨subd8_4_341, List.forall_mem_cons.2 ⟨subd8_4_342, List.forall_mem_cons.2 ⟨subd8_4_343, List.forall_mem_cons.2 ⟨subd8_4_344, List.forall_mem_cons.2 ⟨subd8_4_345, List.forall_mem_cons.2 ⟨subd8_4_346, List.forall_mem_cons.2 ⟨subd8_4_347, List.forall_mem_cons.2 ⟨subd8_4_348, List.forall_mem_cons.2 ⟨subd8_4_349, List.forall_mem_cons.2 ⟨subd8_4_350, List.forall_mem_cons.2 ⟨subd8_4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
