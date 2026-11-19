import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [-3, -3] = true := by decide +kernel
theorem subd18_0_1 : subd18_0 [-3, -2] = true := by decide +kernel
theorem subd18_0_2 : subd18_0 [-3, -1] = true := by decide +kernel
theorem subd18_0_3 : subd18_0 [-3, 0] = true := by decide +kernel
theorem subd18_0_4 : subd18_0 [-2, -4] = true := by decide +kernel
theorem subd18_0_5 : subd18_0 [-2, -3] = true := by decide +kernel
theorem subd18_0_6 : subd18_0 [-2, -2, -10] = true := by decide +kernel
theorem subd18_0_7 : subd18_0 [-2, -2, -9] = true := by decide +kernel
theorem subd18_0_8 : subd18_0 [-2, -2, -8] = true := by decide +kernel
theorem subd18_0_9 : subd18_0 [-2, -2, -7] = true := by decide +kernel
theorem subd18_0_10 : subd18_0 [-2, -2, -6] = true := by decide +kernel
theorem subd18_0_11 : subd18_0 [-2, -2, -5] = true := by decide +kernel
theorem subd18_0_12 : subd18_0 [-2, -2, -4] = true := by decide +kernel
theorem subd18_0_13 : subd18_0 [-2, -2, -3] = true := by decide +kernel
theorem subd18_0_14 : subd18_0 [-2, -2, -2] = true := by decide +kernel
theorem subd18_0_15 : subd18_0 [-2, -2, -1] = true := by decide +kernel
theorem subd18_0_16 : subd18_0 [-2, -2, 0] = true := by decide +kernel
theorem subd18_0_17 : subd18_0 [-2, -2, 1] = true := by decide +kernel
theorem subd18_0_18 : subd18_0 [-2, -2, 2] = true := by decide +kernel
theorem subd18_0_19 : subd18_0 [-2, -2, 3] = true := by decide +kernel
theorem subd18_0_20 : subd18_0 [-2, -2, 4] = true := by decide +kernel
theorem subd18_0_21 : subd18_0 [-2, -2, 5] = true := by decide +kernel
theorem subd18_0_22 : subd18_0 [-2, -2, 6] = true := by decide +kernel
theorem subd18_0_23 : subd18_0 [-2, -2, 7] = true := by decide +kernel
theorem subd18_0_24 : subd18_0 [-2, -2, 8] = true := by decide +kernel
theorem subd18_0_25 : subd18_0 [-2, -1, -11] = true := by decide +kernel
theorem subd18_0_26 : subd18_0 [-2, -1, -10] = true := by decide +kernel
theorem subd18_0_27 : subd18_0 [-2, -1, -9] = true := by decide +kernel
theorem subd18_0_28 : subd18_0 [-2, -1, -8] = true := by decide +kernel
theorem subd18_0_29 : subd18_0 [-2, -1, -7] = true := by decide +kernel
theorem subd18_0_30 : subd18_0 [-2, -1, -6] = true := by decide +kernel
theorem subd18_0_31 : subd18_0 [-2, -1, -5] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_cons.2 ⟨subd18_0_1, List.forall_mem_cons.2 ⟨subd18_0_2, List.forall_mem_cons.2 ⟨subd18_0_3, List.forall_mem_cons.2 ⟨subd18_0_4, List.forall_mem_cons.2 ⟨subd18_0_5, List.forall_mem_cons.2 ⟨subd18_0_6, List.forall_mem_cons.2 ⟨subd18_0_7, List.forall_mem_cons.2 ⟨subd18_0_8, List.forall_mem_cons.2 ⟨subd18_0_9, List.forall_mem_cons.2 ⟨subd18_0_10, List.forall_mem_cons.2 ⟨subd18_0_11, List.forall_mem_cons.2 ⟨subd18_0_12, List.forall_mem_cons.2 ⟨subd18_0_13, List.forall_mem_cons.2 ⟨subd18_0_14, List.forall_mem_cons.2 ⟨subd18_0_15, List.forall_mem_cons.2 ⟨subd18_0_16, List.forall_mem_cons.2 ⟨subd18_0_17, List.forall_mem_cons.2 ⟨subd18_0_18, List.forall_mem_cons.2 ⟨subd18_0_19, List.forall_mem_cons.2 ⟨subd18_0_20, List.forall_mem_cons.2 ⟨subd18_0_21, List.forall_mem_cons.2 ⟨subd18_0_22, List.forall_mem_cons.2 ⟨subd18_0_23, List.forall_mem_cons.2 ⟨subd18_0_24, List.forall_mem_cons.2 ⟨subd18_0_25, List.forall_mem_cons.2 ⟨subd18_0_26, List.forall_mem_cons.2 ⟨subd18_0_27, List.forall_mem_cons.2 ⟨subd18_0_28, List.forall_mem_cons.2 ⟨subd18_0_29, List.forall_mem_cons.2 ⟨subd18_0_30, List.forall_mem_cons.2 ⟨subd18_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_32 : subd18_0 [-2, -1, -4] = true := by decide +kernel
theorem subd18_0_33 : subd18_0 [-2, -1, -3] = true := by decide +kernel
theorem subd18_0_34 : subd18_0 [-2, -1, -2] = true := by decide +kernel
theorem subd18_0_35 : subd18_0 [-2, -1, -1] = true := by decide +kernel
theorem subd18_0_36 : subd18_0 [-2, -1, 0] = true := by decide +kernel
theorem subd18_0_37 : subd18_0 [-2, -1, 1] = true := by decide +kernel
theorem subd18_0_38 : subd18_0 [-2, -1, 2] = true := by decide +kernel
theorem subd18_0_39 : subd18_0 [-2, -1, 3] = true := by decide +kernel
theorem subd18_0_40 : subd18_0 [-2, -1, 4] = true := by decide +kernel
theorem subd18_0_41 : subd18_0 [-2, -1, 5] = true := by decide +kernel
theorem subd18_0_42 : subd18_0 [-2, -1, 6] = true := by decide +kernel
theorem subd18_0_43 : subd18_0 [-2, -1, 7] = true := by decide +kernel
theorem subd18_0_44 : subd18_0 [-2, -1, 8] = true := by decide +kernel
theorem subd18_0_45 : subd18_0 [-2, -1, 9] = true := by decide +kernel
theorem subd18_0_46 : subd18_0 [-2, 0, -11] = true := by decide +kernel
theorem subd18_0_47 : subd18_0 [-2, 0, -10] = true := by decide +kernel
theorem subd18_0_48 : subd18_0 [-2, 0, -9] = true := by decide +kernel
theorem subd18_0_49 : subd18_0 [-2, 0, -8] = true := by decide +kernel
theorem subd18_0_50 : subd18_0 [-2, 0, -7] = true := by decide +kernel
theorem subd18_0_51 : subd18_0 [-2, 0, -6] = true := by decide +kernel
theorem subd18_0_52 : subd18_0 [-2, 0, -5] = true := by decide +kernel
theorem subd18_0_53 : subd18_0 [-2, 0, -4] = true := by decide +kernel
theorem subd18_0_54 : subd18_0 [-2, 0, -3] = true := by decide +kernel
theorem subd18_0_55 : subd18_0 [-2, 0, -2] = true := by decide +kernel
theorem subd18_0_56 : subd18_0 [-2, 0, -1] = true := by decide +kernel
theorem subd18_0_57 : subd18_0 [-2, 0, 0] = true := by decide +kernel
theorem subd18_0_58 : subd18_0 [-2, 0, 1] = true := by decide +kernel
theorem subd18_0_59 : subd18_0 [-2, 0, 2] = true := by decide +kernel
theorem subd18_0_60 : subd18_0 [-2, 0, 3] = true := by decide +kernel
theorem subd18_0_61 : subd18_0 [-2, 0, 4] = true := by decide +kernel
theorem subd18_0_62 : subd18_0 [-2, 0, 5] = true := by decide +kernel
theorem subd18_0_63 : subd18_0 [-2, 0, 6] = true := by decide +kernel
theorem sbd18_0_1 : ∀ q ∈ blkd18_0_1, subd18_0 q = true := by
  unfold blkd18_0_1
  exact List.forall_mem_cons.2 ⟨subd18_0_32, List.forall_mem_cons.2 ⟨subd18_0_33, List.forall_mem_cons.2 ⟨subd18_0_34, List.forall_mem_cons.2 ⟨subd18_0_35, List.forall_mem_cons.2 ⟨subd18_0_36, List.forall_mem_cons.2 ⟨subd18_0_37, List.forall_mem_cons.2 ⟨subd18_0_38, List.forall_mem_cons.2 ⟨subd18_0_39, List.forall_mem_cons.2 ⟨subd18_0_40, List.forall_mem_cons.2 ⟨subd18_0_41, List.forall_mem_cons.2 ⟨subd18_0_42, List.forall_mem_cons.2 ⟨subd18_0_43, List.forall_mem_cons.2 ⟨subd18_0_44, List.forall_mem_cons.2 ⟨subd18_0_45, List.forall_mem_cons.2 ⟨subd18_0_46, List.forall_mem_cons.2 ⟨subd18_0_47, List.forall_mem_cons.2 ⟨subd18_0_48, List.forall_mem_cons.2 ⟨subd18_0_49, List.forall_mem_cons.2 ⟨subd18_0_50, List.forall_mem_cons.2 ⟨subd18_0_51, List.forall_mem_cons.2 ⟨subd18_0_52, List.forall_mem_cons.2 ⟨subd18_0_53, List.forall_mem_cons.2 ⟨subd18_0_54, List.forall_mem_cons.2 ⟨subd18_0_55, List.forall_mem_cons.2 ⟨subd18_0_56, List.forall_mem_cons.2 ⟨subd18_0_57, List.forall_mem_cons.2 ⟨subd18_0_58, List.forall_mem_cons.2 ⟨subd18_0_59, List.forall_mem_cons.2 ⟨subd18_0_60, List.forall_mem_cons.2 ⟨subd18_0_61, List.forall_mem_cons.2 ⟨subd18_0_62, List.forall_mem_cons.2 ⟨subd18_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_64 : subd18_0 [-2, 0, 7] = true := by decide +kernel
theorem subd18_0_65 : subd18_0 [-2, 0, 8] = true := by decide +kernel
theorem subd18_0_66 : subd18_0 [-2, 0, 9] = true := by decide +kernel
theorem subd18_0_67 : subd18_0 [-2, 1, -10] = true := by decide +kernel
theorem subd18_0_68 : subd18_0 [-2, 1, -9] = true := by decide +kernel
theorem subd18_0_69 : subd18_0 [-2, 1, -8] = true := by decide +kernel
theorem subd18_0_70 : subd18_0 [-2, 1, -7] = true := by decide +kernel
theorem subd18_0_71 : subd18_0 [-2, 1, -6] = true := by decide +kernel
theorem subd18_0_72 : subd18_0 [-2, 1, -5] = true := by decide +kernel
theorem subd18_0_73 : subd18_0 [-2, 1, -4] = true := by decide +kernel
theorem subd18_0_74 : subd18_0 [-2, 1, -3] = true := by decide +kernel
theorem subd18_0_75 : subd18_0 [-2, 1, -2] = true := by decide +kernel
theorem subd18_0_76 : subd18_0 [-2, 1, -1] = true := by decide +kernel
theorem subd18_0_77 : subd18_0 [-2, 1, 0] = true := by decide +kernel
theorem subd18_0_78 : subd18_0 [-2, 1, 1] = true := by decide +kernel
theorem subd18_0_79 : subd18_0 [-2, 1, 2] = true := by decide +kernel
theorem subd18_0_80 : subd18_0 [-2, 1, 3] = true := by decide +kernel
theorem subd18_0_81 : subd18_0 [-2, 1, 4] = true := by decide +kernel
theorem subd18_0_82 : subd18_0 [-2, 1, 5] = true := by decide +kernel
theorem subd18_0_83 : subd18_0 [-2, 1, 6] = true := by decide +kernel
theorem subd18_0_84 : subd18_0 [-2, 1, 7] = true := by decide +kernel
theorem subd18_0_85 : subd18_0 [-2, 2] = true := by decide +kernel
theorem subd18_0_86 : subd18_0 [-1, -4] = true := by decide +kernel
theorem subd18_0_87 : subd18_0 [-1, -3, -8] = true := by decide +kernel
theorem subd18_0_88 : subd18_0 [-1, -3, -7] = true := by decide +kernel
theorem subd18_0_89 : subd18_0 [-1, -3, -6] = true := by decide +kernel
theorem subd18_0_90 : subd18_0 [-1, -3, -5] = true := by decide +kernel
theorem subd18_0_91 : subd18_0 [-1, -3, -4] = true := by decide +kernel
theorem subd18_0_92 : subd18_0 [-1, -3, -3] = true := by decide +kernel
theorem subd18_0_93 : subd18_0 [-1, -3, -2] = true := by decide +kernel
theorem subd18_0_94 : subd18_0 [-1, -3, -1] = true := by decide +kernel
theorem subd18_0_95 : subd18_0 [-1, -3, 0] = true := by decide +kernel
theorem sbd18_0_2 : ∀ q ∈ blkd18_0_2, subd18_0 q = true := by
  unfold blkd18_0_2
  exact List.forall_mem_cons.2 ⟨subd18_0_64, List.forall_mem_cons.2 ⟨subd18_0_65, List.forall_mem_cons.2 ⟨subd18_0_66, List.forall_mem_cons.2 ⟨subd18_0_67, List.forall_mem_cons.2 ⟨subd18_0_68, List.forall_mem_cons.2 ⟨subd18_0_69, List.forall_mem_cons.2 ⟨subd18_0_70, List.forall_mem_cons.2 ⟨subd18_0_71, List.forall_mem_cons.2 ⟨subd18_0_72, List.forall_mem_cons.2 ⟨subd18_0_73, List.forall_mem_cons.2 ⟨subd18_0_74, List.forall_mem_cons.2 ⟨subd18_0_75, List.forall_mem_cons.2 ⟨subd18_0_76, List.forall_mem_cons.2 ⟨subd18_0_77, List.forall_mem_cons.2 ⟨subd18_0_78, List.forall_mem_cons.2 ⟨subd18_0_79, List.forall_mem_cons.2 ⟨subd18_0_80, List.forall_mem_cons.2 ⟨subd18_0_81, List.forall_mem_cons.2 ⟨subd18_0_82, List.forall_mem_cons.2 ⟨subd18_0_83, List.forall_mem_cons.2 ⟨subd18_0_84, List.forall_mem_cons.2 ⟨subd18_0_85, List.forall_mem_cons.2 ⟨subd18_0_86, List.forall_mem_cons.2 ⟨subd18_0_87, List.forall_mem_cons.2 ⟨subd18_0_88, List.forall_mem_cons.2 ⟨subd18_0_89, List.forall_mem_cons.2 ⟨subd18_0_90, List.forall_mem_cons.2 ⟨subd18_0_91, List.forall_mem_cons.2 ⟨subd18_0_92, List.forall_mem_cons.2 ⟨subd18_0_93, List.forall_mem_cons.2 ⟨subd18_0_94, List.forall_mem_cons.2 ⟨subd18_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_96 : subd18_0 [-1, -3, 1] = true := by decide +kernel
theorem subd18_0_97 : subd18_0 [-1, -3, 2] = true := by decide +kernel
theorem subd18_0_98 : subd18_0 [-1, -3, 3] = true := by decide +kernel
theorem subd18_0_99 : subd18_0 [-1, -3, 4] = true := by decide +kernel
theorem subd18_0_100 : subd18_0 [-1, -3, 5] = true := by decide +kernel
theorem subd18_0_101 : subd18_0 [-1, -3, 6] = true := by decide +kernel
theorem subd18_0_102 : subd18_0 [-1, -3, 7] = true := by decide +kernel
theorem subd18_0_103 : subd18_0 [-1, -2, -11] = true := by decide +kernel
theorem subd18_0_104 : subd18_0 [-1, -2, -10] = true := by decide +kernel
theorem subd18_0_105 : subd18_0 [-1, -2, -9] = true := by decide +kernel
theorem subd18_0_106 : subd18_0 [-1, -2, -8] = true := by decide +kernel
theorem subd18_0_107 : subd18_0 [-1, -2, -7] = true := by decide +kernel
theorem subd18_0_108 : subd18_0 [-1, -2, -6] = true := by decide +kernel
theorem subd18_0_109 : subd18_0 [-1, -2, -5] = true := by decide +kernel
theorem subd18_0_110 : subd18_0 [-1, -2, -4] = true := by decide +kernel
theorem subd18_0_111 : subd18_0 [-1, -2, -3] = true := by decide +kernel
theorem subd18_0_112 : subd18_0 [-1, -2, -2] = true := by decide +kernel
theorem subd18_0_113 : subd18_0 [-1, -2, -1] = true := by decide +kernel
theorem subd18_0_114 : subd18_0 [-1, -2, 0] = true := by decide +kernel
theorem subd18_0_115 : subd18_0 [-1, -2, 1] = true := by decide +kernel
theorem subd18_0_116 : subd18_0 [-1, -2, 2] = true := by decide +kernel
theorem subd18_0_117 : subd18_0 [-1, -2, 3] = true := by decide +kernel
theorem subd18_0_118 : subd18_0 [-1, -2, 4] = true := by decide +kernel
theorem subd18_0_119 : subd18_0 [-1, -2, 5] = true := by decide +kernel
theorem subd18_0_120 : subd18_0 [-1, -2, 6] = true := by decide +kernel
theorem subd18_0_121 : subd18_0 [-1, -2, 7] = true := by decide +kernel
theorem subd18_0_122 : subd18_0 [-1, -2, 8] = true := by decide +kernel
theorem subd18_0_123 : subd18_0 [-1, -2, 9] = true := by decide +kernel
theorem subd18_0_124 : subd18_0 [-1, -2, 10] = true := by decide +kernel
theorem subd18_0_125 : subd18_0 [-1, -1, -13] = true := by decide +kernel
theorem subd18_0_126 : subd18_0 [-1, -1, -12] = true := by decide +kernel
theorem subd18_0_127 : subd18_0 [-1, -1, -11] = true := by decide +kernel
theorem sbd18_0_3 : ∀ q ∈ blkd18_0_3, subd18_0 q = true := by
  unfold blkd18_0_3
  exact List.forall_mem_cons.2 ⟨subd18_0_96, List.forall_mem_cons.2 ⟨subd18_0_97, List.forall_mem_cons.2 ⟨subd18_0_98, List.forall_mem_cons.2 ⟨subd18_0_99, List.forall_mem_cons.2 ⟨subd18_0_100, List.forall_mem_cons.2 ⟨subd18_0_101, List.forall_mem_cons.2 ⟨subd18_0_102, List.forall_mem_cons.2 ⟨subd18_0_103, List.forall_mem_cons.2 ⟨subd18_0_104, List.forall_mem_cons.2 ⟨subd18_0_105, List.forall_mem_cons.2 ⟨subd18_0_106, List.forall_mem_cons.2 ⟨subd18_0_107, List.forall_mem_cons.2 ⟨subd18_0_108, List.forall_mem_cons.2 ⟨subd18_0_109, List.forall_mem_cons.2 ⟨subd18_0_110, List.forall_mem_cons.2 ⟨subd18_0_111, List.forall_mem_cons.2 ⟨subd18_0_112, List.forall_mem_cons.2 ⟨subd18_0_113, List.forall_mem_cons.2 ⟨subd18_0_114, List.forall_mem_cons.2 ⟨subd18_0_115, List.forall_mem_cons.2 ⟨subd18_0_116, List.forall_mem_cons.2 ⟨subd18_0_117, List.forall_mem_cons.2 ⟨subd18_0_118, List.forall_mem_cons.2 ⟨subd18_0_119, List.forall_mem_cons.2 ⟨subd18_0_120, List.forall_mem_cons.2 ⟨subd18_0_121, List.forall_mem_cons.2 ⟨subd18_0_122, List.forall_mem_cons.2 ⟨subd18_0_123, List.forall_mem_cons.2 ⟨subd18_0_124, List.forall_mem_cons.2 ⟨subd18_0_125, List.forall_mem_cons.2 ⟨subd18_0_126, List.forall_mem_cons.2 ⟨subd18_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_128 : subd18_0 [-1, -1, -10] = true := by decide +kernel
theorem subd18_0_129 : subd18_0 [-1, -1, -9] = true := by decide +kernel
theorem subd18_0_130 : subd18_0 [-1, -1, -8] = true := by decide +kernel
theorem subd18_0_131 : subd18_0 [-1, -1, -7] = true := by decide +kernel
theorem subd18_0_132 : subd18_0 [-1, -1, -6] = true := by decide +kernel
theorem subd18_0_133 : subd18_0 [-1, -1, -5] = true := by decide +kernel
theorem subd18_0_134 : subd18_0 [-1, -1, -4] = true := by decide +kernel
theorem subd18_0_135 : subd18_0 [-1, -1, -3] = true := by decide +kernel
theorem subd18_0_136 : subd18_0 [-1, -1, -2] = true := by decide +kernel
theorem subd18_0_137 : subd18_0 [-1, -1, -1] = true := by decide +kernel
theorem subd18_0_138 : subd18_0 [-1, -1, 0] = true := by decide +kernel
theorem subd18_0_139 : subd18_0 [-1, -1, 1] = true := by decide +kernel
theorem subd18_0_140 : subd18_0 [-1, -1, 2] = true := by decide +kernel
theorem subd18_0_141 : subd18_0 [-1, -1, 3] = true := by decide +kernel
theorem subd18_0_142 : subd18_0 [-1, -1, 4] = true := by decide +kernel
theorem subd18_0_143 : subd18_0 [-1, -1, 5] = true := by decide +kernel
theorem subd18_0_144 : subd18_0 [-1, -1, 6] = true := by decide +kernel
theorem subd18_0_145 : subd18_0 [-1, -1, 7] = true := by decide +kernel
theorem subd18_0_146 : subd18_0 [-1, -1, 8] = true := by decide +kernel
theorem subd18_0_147 : subd18_0 [-1, -1, 9] = true := by decide +kernel
theorem subd18_0_148 : subd18_0 [-1, -1, 10] = true := by decide +kernel
theorem subd18_0_149 : subd18_0 [-1, -1, 11] = true := by decide +kernel
theorem subd18_0_150 : subd18_0 [-1, -1, 12] = true := by decide +kernel
theorem subd18_0_151 : subd18_0 [-1, 0, -13] = true := by decide +kernel
theorem subd18_0_152 : subd18_0 [-1, 0, -12] = true := by decide +kernel
theorem subd18_0_153 : subd18_0 [-1, 0, -11] = true := by decide +kernel
theorem subd18_0_154 : subd18_0 [-1, 0, -10] = true := by decide +kernel
theorem subd18_0_155 : subd18_0 [-1, 0, -9] = true := by decide +kernel
theorem subd18_0_156 : subd18_0 [-1, 0, -8] = true := by decide +kernel
theorem subd18_0_157 : subd18_0 [-1, 0, -7] = true := by decide +kernel
theorem subd18_0_158 : subd18_0 [-1, 0, -6] = true := by decide +kernel
theorem subd18_0_159 : subd18_0 [-1, 0, -5] = true := by decide +kernel
theorem sbd18_0_4 : ∀ q ∈ blkd18_0_4, subd18_0 q = true := by
  unfold blkd18_0_4
  exact List.forall_mem_cons.2 ⟨subd18_0_128, List.forall_mem_cons.2 ⟨subd18_0_129, List.forall_mem_cons.2 ⟨subd18_0_130, List.forall_mem_cons.2 ⟨subd18_0_131, List.forall_mem_cons.2 ⟨subd18_0_132, List.forall_mem_cons.2 ⟨subd18_0_133, List.forall_mem_cons.2 ⟨subd18_0_134, List.forall_mem_cons.2 ⟨subd18_0_135, List.forall_mem_cons.2 ⟨subd18_0_136, List.forall_mem_cons.2 ⟨subd18_0_137, List.forall_mem_cons.2 ⟨subd18_0_138, List.forall_mem_cons.2 ⟨subd18_0_139, List.forall_mem_cons.2 ⟨subd18_0_140, List.forall_mem_cons.2 ⟨subd18_0_141, List.forall_mem_cons.2 ⟨subd18_0_142, List.forall_mem_cons.2 ⟨subd18_0_143, List.forall_mem_cons.2 ⟨subd18_0_144, List.forall_mem_cons.2 ⟨subd18_0_145, List.forall_mem_cons.2 ⟨subd18_0_146, List.forall_mem_cons.2 ⟨subd18_0_147, List.forall_mem_cons.2 ⟨subd18_0_148, List.forall_mem_cons.2 ⟨subd18_0_149, List.forall_mem_cons.2 ⟨subd18_0_150, List.forall_mem_cons.2 ⟨subd18_0_151, List.forall_mem_cons.2 ⟨subd18_0_152, List.forall_mem_cons.2 ⟨subd18_0_153, List.forall_mem_cons.2 ⟨subd18_0_154, List.forall_mem_cons.2 ⟨subd18_0_155, List.forall_mem_cons.2 ⟨subd18_0_156, List.forall_mem_cons.2 ⟨subd18_0_157, List.forall_mem_cons.2 ⟨subd18_0_158, List.forall_mem_cons.2 ⟨subd18_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_160 : subd18_0 [-1, 0, -4] = true := by decide +kernel
theorem subd18_0_161 : subd18_0 [-1, 0, -3] = true := by decide +kernel
theorem subd18_0_162 : subd18_0 [-1, 0, -2] = true := by decide +kernel
theorem subd18_0_163 : subd18_0 [-1, 0, -1] = true := by decide +kernel
theorem subd18_0_164 : subd18_0 [-1, 0, 0] = true := by decide +kernel
theorem subd18_0_165 : subd18_0 [-1, 0, 1] = true := by decide +kernel
theorem subd18_0_166 : subd18_0 [-1, 0, 2] = true := by decide +kernel
theorem subd18_0_167 : subd18_0 [-1, 0, 3] = true := by decide +kernel
theorem subd18_0_168 : subd18_0 [-1, 0, 4] = true := by decide +kernel
theorem subd18_0_169 : subd18_0 [-1, 0, 5] = true := by decide +kernel
theorem subd18_0_170 : subd18_0 [-1, 0, 6] = true := by decide +kernel
theorem subd18_0_171 : subd18_0 [-1, 0, 7] = true := by decide +kernel
theorem subd18_0_172 : subd18_0 [-1, 0, 8] = true := by decide +kernel
theorem subd18_0_173 : subd18_0 [-1, 0, 9] = true := by decide +kernel
theorem subd18_0_174 : subd18_0 [-1, 0, 10] = true := by decide +kernel
theorem subd18_0_175 : subd18_0 [-1, 0, 11] = true := by decide +kernel
theorem subd18_0_176 : subd18_0 [-1, 0, 12] = true := by decide +kernel
theorem subd18_0_177 : subd18_0 [-1, 1, -13] = true := by decide +kernel
theorem subd18_0_178 : subd18_0 [-1, 1, -12] = true := by decide +kernel
theorem subd18_0_179 : subd18_0 [-1, 1, -11] = true := by decide +kernel
theorem subd18_0_180 : subd18_0 [-1, 1, -10] = true := by decide +kernel
theorem subd18_0_181 : subd18_0 [-1, 1, -9] = true := by decide +kernel
theorem subd18_0_182 : subd18_0 [-1, 1, -8] = true := by decide +kernel
theorem subd18_0_183 : subd18_0 [-1, 1, -7] = true := by decide +kernel
theorem subd18_0_184 : subd18_0 [-1, 1, -6] = true := by decide +kernel
theorem subd18_0_185 : subd18_0 [-1, 1, -5] = true := by decide +kernel
theorem subd18_0_186 : subd18_0 [-1, 1, -4] = true := by decide +kernel
theorem subd18_0_187 : subd18_0 [-1, 1, -3] = true := by decide +kernel
theorem subd18_0_188 : subd18_0 [-1, 1, -2] = true := by decide +kernel
theorem subd18_0_189 : subd18_0 [-1, 1, -1] = true := by decide +kernel
theorem subd18_0_190 : subd18_0 [-1, 1, 0] = true := by decide +kernel
theorem subd18_0_191 : subd18_0 [-1, 1, 1] = true := by decide +kernel
theorem sbd18_0_5 : ∀ q ∈ blkd18_0_5, subd18_0 q = true := by
  unfold blkd18_0_5
  exact List.forall_mem_cons.2 ⟨subd18_0_160, List.forall_mem_cons.2 ⟨subd18_0_161, List.forall_mem_cons.2 ⟨subd18_0_162, List.forall_mem_cons.2 ⟨subd18_0_163, List.forall_mem_cons.2 ⟨subd18_0_164, List.forall_mem_cons.2 ⟨subd18_0_165, List.forall_mem_cons.2 ⟨subd18_0_166, List.forall_mem_cons.2 ⟨subd18_0_167, List.forall_mem_cons.2 ⟨subd18_0_168, List.forall_mem_cons.2 ⟨subd18_0_169, List.forall_mem_cons.2 ⟨subd18_0_170, List.forall_mem_cons.2 ⟨subd18_0_171, List.forall_mem_cons.2 ⟨subd18_0_172, List.forall_mem_cons.2 ⟨subd18_0_173, List.forall_mem_cons.2 ⟨subd18_0_174, List.forall_mem_cons.2 ⟨subd18_0_175, List.forall_mem_cons.2 ⟨subd18_0_176, List.forall_mem_cons.2 ⟨subd18_0_177, List.forall_mem_cons.2 ⟨subd18_0_178, List.forall_mem_cons.2 ⟨subd18_0_179, List.forall_mem_cons.2 ⟨subd18_0_180, List.forall_mem_cons.2 ⟨subd18_0_181, List.forall_mem_cons.2 ⟨subd18_0_182, List.forall_mem_cons.2 ⟨subd18_0_183, List.forall_mem_cons.2 ⟨subd18_0_184, List.forall_mem_cons.2 ⟨subd18_0_185, List.forall_mem_cons.2 ⟨subd18_0_186, List.forall_mem_cons.2 ⟨subd18_0_187, List.forall_mem_cons.2 ⟨subd18_0_188, List.forall_mem_cons.2 ⟨subd18_0_189, List.forall_mem_cons.2 ⟨subd18_0_190, List.forall_mem_cons.2 ⟨subd18_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_192 : subd18_0 [-1, 1, 2] = true := by decide +kernel
theorem subd18_0_193 : subd18_0 [-1, 1, 3] = true := by decide +kernel
theorem subd18_0_194 : subd18_0 [-1, 1, 4] = true := by decide +kernel
theorem subd18_0_195 : subd18_0 [-1, 1, 5] = true := by decide +kernel
theorem subd18_0_196 : subd18_0 [-1, 1, 6] = true := by decide +kernel
theorem subd18_0_197 : subd18_0 [-1, 1, 7] = true := by decide +kernel
theorem subd18_0_198 : subd18_0 [-1, 1, 8] = true := by decide +kernel
theorem subd18_0_199 : subd18_0 [-1, 1, 9] = true := by decide +kernel
theorem subd18_0_200 : subd18_0 [-1, 1, 10] = true := by decide +kernel
theorem subd18_0_201 : subd18_0 [-1, 2, -10] = true := by decide +kernel
theorem subd18_0_202 : subd18_0 [-1, 2, -9] = true := by decide +kernel
theorem subd18_0_203 : subd18_0 [-1, 2, -8] = true := by decide +kernel
theorem subd18_0_204 : subd18_0 [-1, 2, -7] = true := by decide +kernel
theorem subd18_0_205 : subd18_0 [-1, 2, -6] = true := by decide +kernel
theorem subd18_0_206 : subd18_0 [-1, 2, -5] = true := by decide +kernel
theorem subd18_0_207 : subd18_0 [-1, 2, -4] = true := by decide +kernel
theorem subd18_0_208 : subd18_0 [-1, 2, -3] = true := by decide +kernel
theorem subd18_0_209 : subd18_0 [-1, 2, -2] = true := by decide +kernel
theorem subd18_0_210 : subd18_0 [-1, 2, -1] = true := by decide +kernel
theorem subd18_0_211 : subd18_0 [-1, 2, 0] = true := by decide +kernel
theorem subd18_0_212 : subd18_0 [-1, 2, 1] = true := by decide +kernel
theorem subd18_0_213 : subd18_0 [-1, 2, 2] = true := by decide +kernel
theorem subd18_0_214 : subd18_0 [-1, 2, 3] = true := by decide +kernel
theorem subd18_0_215 : subd18_0 [-1, 2, 4] = true := by decide +kernel
theorem subd18_0_216 : subd18_0 [-1, 2, 5] = true := by decide +kernel
theorem subd18_0_217 : subd18_0 [-1, 2, 6] = true := by decide +kernel
theorem subd18_0_218 : subd18_0 [-1, 2, 7] = true := by decide +kernel
theorem subd18_0_219 : subd18_0 [-1, 2, 8] = true := by decide +kernel
theorem subd18_0_220 : subd18_0 [-1, 3] = true := by decide +kernel
theorem subd18_0_221 : subd18_0 [0, -4] = true := by decide +kernel
theorem subd18_0_222 : subd18_0 [0, -3, -7] = true := by decide +kernel
theorem subd18_0_223 : subd18_0 [0, -3, -6] = true := by decide +kernel
theorem sbd18_0_6 : ∀ q ∈ blkd18_0_6, subd18_0 q = true := by
  unfold blkd18_0_6
  exact List.forall_mem_cons.2 ⟨subd18_0_192, List.forall_mem_cons.2 ⟨subd18_0_193, List.forall_mem_cons.2 ⟨subd18_0_194, List.forall_mem_cons.2 ⟨subd18_0_195, List.forall_mem_cons.2 ⟨subd18_0_196, List.forall_mem_cons.2 ⟨subd18_0_197, List.forall_mem_cons.2 ⟨subd18_0_198, List.forall_mem_cons.2 ⟨subd18_0_199, List.forall_mem_cons.2 ⟨subd18_0_200, List.forall_mem_cons.2 ⟨subd18_0_201, List.forall_mem_cons.2 ⟨subd18_0_202, List.forall_mem_cons.2 ⟨subd18_0_203, List.forall_mem_cons.2 ⟨subd18_0_204, List.forall_mem_cons.2 ⟨subd18_0_205, List.forall_mem_cons.2 ⟨subd18_0_206, List.forall_mem_cons.2 ⟨subd18_0_207, List.forall_mem_cons.2 ⟨subd18_0_208, List.forall_mem_cons.2 ⟨subd18_0_209, List.forall_mem_cons.2 ⟨subd18_0_210, List.forall_mem_cons.2 ⟨subd18_0_211, List.forall_mem_cons.2 ⟨subd18_0_212, List.forall_mem_cons.2 ⟨subd18_0_213, List.forall_mem_cons.2 ⟨subd18_0_214, List.forall_mem_cons.2 ⟨subd18_0_215, List.forall_mem_cons.2 ⟨subd18_0_216, List.forall_mem_cons.2 ⟨subd18_0_217, List.forall_mem_cons.2 ⟨subd18_0_218, List.forall_mem_cons.2 ⟨subd18_0_219, List.forall_mem_cons.2 ⟨subd18_0_220, List.forall_mem_cons.2 ⟨subd18_0_221, List.forall_mem_cons.2 ⟨subd18_0_222, List.forall_mem_cons.2 ⟨subd18_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_224 : subd18_0 [0, -3, -5] = true := by decide +kernel
theorem subd18_0_225 : subd18_0 [0, -3, -4] = true := by decide +kernel
theorem subd18_0_226 : subd18_0 [0, -3, -3] = true := by decide +kernel
theorem subd18_0_227 : subd18_0 [0, -3, -2] = true := by decide +kernel
theorem subd18_0_228 : subd18_0 [0, -3, -1] = true := by decide +kernel
theorem subd18_0_229 : subd18_0 [0, -3, 0] = true := by decide +kernel
theorem subd18_0_230 : subd18_0 [0, -3, 1] = true := by decide +kernel
theorem subd18_0_231 : subd18_0 [0, -3, 2] = true := by decide +kernel
theorem subd18_0_232 : subd18_0 [0, -3, 3] = true := by decide +kernel
theorem subd18_0_233 : subd18_0 [0, -3, 4] = true := by decide +kernel
theorem subd18_0_234 : subd18_0 [0, -3, 5] = true := by decide +kernel
theorem subd18_0_235 : subd18_0 [0, -3, 6] = true := by decide +kernel
theorem subd18_0_236 : subd18_0 [0, -3, 7] = true := by decide +kernel
theorem subd18_0_237 : subd18_0 [0, -2, -11] = true := by decide +kernel
theorem subd18_0_238 : subd18_0 [0, -2, -10] = true := by decide +kernel
theorem subd18_0_239 : subd18_0 [0, -2, -9] = true := by decide +kernel
theorem subd18_0_240 : subd18_0 [0, -2, -8] = true := by decide +kernel
theorem subd18_0_241 : subd18_0 [0, -2, -7] = true := by decide +kernel
theorem subd18_0_242 : subd18_0 [0, -2, -6] = true := by decide +kernel
theorem subd18_0_243 : subd18_0 [0, -2, -5] = true := by decide +kernel
theorem subd18_0_244 : subd18_0 [0, -2, -4] = true := by decide +kernel
theorem subd18_0_245 : subd18_0 [0, -2, -3] = true := by decide +kernel
theorem subd18_0_246 : subd18_0 [0, -2, -2] = true := by decide +kernel
theorem subd18_0_247 : subd18_0 [0, -2, -1] = true := by decide +kernel
theorem subd18_0_248 : subd18_0 [0, -2, 0] = true := by decide +kernel
theorem subd18_0_249 : subd18_0 [0, -2, 1] = true := by decide +kernel
theorem subd18_0_250 : subd18_0 [0, -2, 2] = true := by decide +kernel
theorem subd18_0_251 : subd18_0 [0, -2, 3] = true := by decide +kernel
theorem subd18_0_252 : subd18_0 [0, -2, 4] = true := by decide +kernel
theorem subd18_0_253 : subd18_0 [0, -2, 5] = true := by decide +kernel
theorem subd18_0_254 : subd18_0 [0, -2, 6] = true := by decide +kernel
theorem subd18_0_255 : subd18_0 [0, -2, 7] = true := by decide +kernel
theorem sbd18_0_7 : ∀ q ∈ blkd18_0_7, subd18_0 q = true := by
  unfold blkd18_0_7
  exact List.forall_mem_cons.2 ⟨subd18_0_224, List.forall_mem_cons.2 ⟨subd18_0_225, List.forall_mem_cons.2 ⟨subd18_0_226, List.forall_mem_cons.2 ⟨subd18_0_227, List.forall_mem_cons.2 ⟨subd18_0_228, List.forall_mem_cons.2 ⟨subd18_0_229, List.forall_mem_cons.2 ⟨subd18_0_230, List.forall_mem_cons.2 ⟨subd18_0_231, List.forall_mem_cons.2 ⟨subd18_0_232, List.forall_mem_cons.2 ⟨subd18_0_233, List.forall_mem_cons.2 ⟨subd18_0_234, List.forall_mem_cons.2 ⟨subd18_0_235, List.forall_mem_cons.2 ⟨subd18_0_236, List.forall_mem_cons.2 ⟨subd18_0_237, List.forall_mem_cons.2 ⟨subd18_0_238, List.forall_mem_cons.2 ⟨subd18_0_239, List.forall_mem_cons.2 ⟨subd18_0_240, List.forall_mem_cons.2 ⟨subd18_0_241, List.forall_mem_cons.2 ⟨subd18_0_242, List.forall_mem_cons.2 ⟨subd18_0_243, List.forall_mem_cons.2 ⟨subd18_0_244, List.forall_mem_cons.2 ⟨subd18_0_245, List.forall_mem_cons.2 ⟨subd18_0_246, List.forall_mem_cons.2 ⟨subd18_0_247, List.forall_mem_cons.2 ⟨subd18_0_248, List.forall_mem_cons.2 ⟨subd18_0_249, List.forall_mem_cons.2 ⟨subd18_0_250, List.forall_mem_cons.2 ⟨subd18_0_251, List.forall_mem_cons.2 ⟨subd18_0_252, List.forall_mem_cons.2 ⟨subd18_0_253, List.forall_mem_cons.2 ⟨subd18_0_254, List.forall_mem_cons.2 ⟨subd18_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_256 : subd18_0 [0, -2, 8] = true := by decide +kernel
theorem subd18_0_257 : subd18_0 [0, -2, 9] = true := by decide +kernel
theorem subd18_0_258 : subd18_0 [0, -2, 10] = true := by decide +kernel
theorem subd18_0_259 : subd18_0 [0, -2, 11] = true := by decide +kernel
theorem subd18_0_260 : subd18_0 [0, -1, -13] = true := by decide +kernel
theorem subd18_0_261 : subd18_0 [0, -1, -12] = true := by decide +kernel
theorem subd18_0_262 : subd18_0 [0, -1, -11] = true := by decide +kernel
theorem subd18_0_263 : subd18_0 [0, -1, -10] = true := by decide +kernel
theorem subd18_0_264 : subd18_0 [0, -1, -9] = true := by decide +kernel
theorem subd18_0_265 : subd18_0 [0, -1, -8] = true := by decide +kernel
theorem subd18_0_266 : subd18_0 [0, -1, -7] = true := by decide +kernel
theorem subd18_0_267 : subd18_0 [0, -1, -6] = true := by decide +kernel
theorem subd18_0_268 : subd18_0 [0, -1, -5] = true := by decide +kernel
theorem subd18_0_269 : subd18_0 [0, -1, -4] = true := by decide +kernel
theorem subd18_0_270 : subd18_0 [0, -1, -3] = true := by decide +kernel
theorem subd18_0_271 : subd18_0 [0, -1, -2] = true := by decide +kernel
theorem subd18_0_272 : subd18_0 [0, -1, -1] = true := by decide +kernel
theorem subd18_0_273 : subd18_0 [0, -1, 0] = true := by decide +kernel
theorem subd18_0_274 : subd18_0 [0, -1, 1] = true := by decide +kernel
theorem subd18_0_275 : subd18_0 [0, -1, 2] = true := by decide +kernel
theorem subd18_0_276 : subd18_0 [0, -1, 3] = true := by decide +kernel
theorem subd18_0_277 : subd18_0 [0, -1, 4] = true := by decide +kernel
theorem subd18_0_278 : subd18_0 [0, -1, 5] = true := by decide +kernel
theorem subd18_0_279 : subd18_0 [0, -1, 6] = true := by decide +kernel
theorem subd18_0_280 : subd18_0 [0, -1, 7] = true := by decide +kernel
theorem subd18_0_281 : subd18_0 [0, -1, 8] = true := by decide +kernel
theorem subd18_0_282 : subd18_0 [0, -1, 9] = true := by decide +kernel
theorem subd18_0_283 : subd18_0 [0, -1, 10] = true := by decide +kernel
theorem subd18_0_284 : subd18_0 [0, -1, 11] = true := by decide +kernel
theorem subd18_0_285 : subd18_0 [0, -1, 12] = true := by decide +kernel
theorem subd18_0_286 : subd18_0 [0, 0, -14] = true := by decide +kernel
theorem subd18_0_287 : subd18_0 [0, 0, -13] = true := by decide +kernel
theorem sbd18_0_8 : ∀ q ∈ blkd18_0_8, subd18_0 q = true := by
  unfold blkd18_0_8
  exact List.forall_mem_cons.2 ⟨subd18_0_256, List.forall_mem_cons.2 ⟨subd18_0_257, List.forall_mem_cons.2 ⟨subd18_0_258, List.forall_mem_cons.2 ⟨subd18_0_259, List.forall_mem_cons.2 ⟨subd18_0_260, List.forall_mem_cons.2 ⟨subd18_0_261, List.forall_mem_cons.2 ⟨subd18_0_262, List.forall_mem_cons.2 ⟨subd18_0_263, List.forall_mem_cons.2 ⟨subd18_0_264, List.forall_mem_cons.2 ⟨subd18_0_265, List.forall_mem_cons.2 ⟨subd18_0_266, List.forall_mem_cons.2 ⟨subd18_0_267, List.forall_mem_cons.2 ⟨subd18_0_268, List.forall_mem_cons.2 ⟨subd18_0_269, List.forall_mem_cons.2 ⟨subd18_0_270, List.forall_mem_cons.2 ⟨subd18_0_271, List.forall_mem_cons.2 ⟨subd18_0_272, List.forall_mem_cons.2 ⟨subd18_0_273, List.forall_mem_cons.2 ⟨subd18_0_274, List.forall_mem_cons.2 ⟨subd18_0_275, List.forall_mem_cons.2 ⟨subd18_0_276, List.forall_mem_cons.2 ⟨subd18_0_277, List.forall_mem_cons.2 ⟨subd18_0_278, List.forall_mem_cons.2 ⟨subd18_0_279, List.forall_mem_cons.2 ⟨subd18_0_280, List.forall_mem_cons.2 ⟨subd18_0_281, List.forall_mem_cons.2 ⟨subd18_0_282, List.forall_mem_cons.2 ⟨subd18_0_283, List.forall_mem_cons.2 ⟨subd18_0_284, List.forall_mem_cons.2 ⟨subd18_0_285, List.forall_mem_cons.2 ⟨subd18_0_286, List.forall_mem_cons.2 ⟨subd18_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_288 : subd18_0 [0, 0, -12] = true := by decide +kernel
theorem subd18_0_289 : subd18_0 [0, 0, -11] = true := by decide +kernel
theorem subd18_0_290 : subd18_0 [0, 0, -10] = true := by decide +kernel
theorem subd18_0_291 : subd18_0 [0, 0, -9] = true := by decide +kernel
theorem subd18_0_292 : subd18_0 [0, 0, -8] = true := by decide +kernel
theorem subd18_0_293 : subd18_0 [0, 0, -7] = true := by decide +kernel
theorem subd18_0_294 : subd18_0 [0, 0, -6] = true := by decide +kernel
theorem subd18_0_295 : subd18_0 [0, 0, -5] = true := by decide +kernel
theorem subd18_0_296 : subd18_0 [0, 0, -4] = true := by decide +kernel
theorem subd18_0_297 : subd18_0 [0, 0, -3] = true := by decide +kernel
theorem subd18_0_298 : subd18_0 [0, 0, -2] = true := by decide +kernel
theorem subd18_0_299 : subd18_0 [0, 0, -1] = true := by decide +kernel
theorem subd18_0_300 : subd18_0 [0, 0, 0] = true := by decide +kernel
theorem subd18_0_301 : subd18_0 [0, 0, 1] = true := by decide +kernel
theorem subd18_0_302 : subd18_0 [0, 0, 2] = true := by decide +kernel
theorem subd18_0_303 : subd18_0 [0, 0, 3] = true := by decide +kernel
theorem subd18_0_304 : subd18_0 [0, 0, 4] = true := by decide +kernel
theorem subd18_0_305 : subd18_0 [0, 0, 5] = true := by decide +kernel
theorem subd18_0_306 : subd18_0 [0, 0, 6] = true := by decide +kernel
theorem subd18_0_307 : subd18_0 [0, 0, 7] = true := by decide +kernel
theorem subd18_0_308 : subd18_0 [0, 0, 8] = true := by decide +kernel
theorem subd18_0_309 : subd18_0 [0, 0, 9] = true := by decide +kernel
theorem subd18_0_310 : subd18_0 [0, 0, 10] = true := by decide +kernel
theorem subd18_0_311 : subd18_0 [0, 0, 11] = true := by decide +kernel
theorem subd18_0_312 : subd18_0 [0, 0, 12] = true := by decide +kernel
theorem subd18_0_313 : subd18_0 [0, 0, 13] = true := by decide +kernel
theorem subd18_0_314 : subd18_0 [0, 1, -13] = true := by decide +kernel
theorem subd18_0_315 : subd18_0 [0, 1, -12] = true := by decide +kernel
theorem subd18_0_316 : subd18_0 [0, 1, -11] = true := by decide +kernel
theorem subd18_0_317 : subd18_0 [0, 1, -10] = true := by decide +kernel
theorem subd18_0_318 : subd18_0 [0, 1, -9] = true := by decide +kernel
theorem subd18_0_319 : subd18_0 [0, 1, -8] = true := by decide +kernel
theorem sbd18_0_9 : ∀ q ∈ blkd18_0_9, subd18_0 q = true := by
  unfold blkd18_0_9
  exact List.forall_mem_cons.2 ⟨subd18_0_288, List.forall_mem_cons.2 ⟨subd18_0_289, List.forall_mem_cons.2 ⟨subd18_0_290, List.forall_mem_cons.2 ⟨subd18_0_291, List.forall_mem_cons.2 ⟨subd18_0_292, List.forall_mem_cons.2 ⟨subd18_0_293, List.forall_mem_cons.2 ⟨subd18_0_294, List.forall_mem_cons.2 ⟨subd18_0_295, List.forall_mem_cons.2 ⟨subd18_0_296, List.forall_mem_cons.2 ⟨subd18_0_297, List.forall_mem_cons.2 ⟨subd18_0_298, List.forall_mem_cons.2 ⟨subd18_0_299, List.forall_mem_cons.2 ⟨subd18_0_300, List.forall_mem_cons.2 ⟨subd18_0_301, List.forall_mem_cons.2 ⟨subd18_0_302, List.forall_mem_cons.2 ⟨subd18_0_303, List.forall_mem_cons.2 ⟨subd18_0_304, List.forall_mem_cons.2 ⟨subd18_0_305, List.forall_mem_cons.2 ⟨subd18_0_306, List.forall_mem_cons.2 ⟨subd18_0_307, List.forall_mem_cons.2 ⟨subd18_0_308, List.forall_mem_cons.2 ⟨subd18_0_309, List.forall_mem_cons.2 ⟨subd18_0_310, List.forall_mem_cons.2 ⟨subd18_0_311, List.forall_mem_cons.2 ⟨subd18_0_312, List.forall_mem_cons.2 ⟨subd18_0_313, List.forall_mem_cons.2 ⟨subd18_0_314, List.forall_mem_cons.2 ⟨subd18_0_315, List.forall_mem_cons.2 ⟨subd18_0_316, List.forall_mem_cons.2 ⟨subd18_0_317, List.forall_mem_cons.2 ⟨subd18_0_318, List.forall_mem_cons.2 ⟨subd18_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_320 : subd18_0 [0, 1, -7] = true := by decide +kernel
theorem subd18_0_321 : subd18_0 [0, 1, -6] = true := by decide +kernel
theorem subd18_0_322 : subd18_0 [0, 1, -5] = true := by decide +kernel
theorem subd18_0_323 : subd18_0 [0, 1, -4] = true := by decide +kernel
theorem subd18_0_324 : subd18_0 [0, 1, -3] = true := by decide +kernel
theorem subd18_0_325 : subd18_0 [0, 1, -2] = true := by decide +kernel
theorem subd18_0_326 : subd18_0 [0, 1, -1] = true := by decide +kernel
theorem subd18_0_327 : subd18_0 [0, 1, 0] = true := by decide +kernel
theorem subd18_0_328 : subd18_0 [0, 1, 1] = true := by decide +kernel
theorem subd18_0_329 : subd18_0 [0, 1, 2] = true := by decide +kernel
theorem subd18_0_330 : subd18_0 [0, 1, 3] = true := by decide +kernel
theorem subd18_0_331 : subd18_0 [0, 1, 4] = true := by decide +kernel
theorem subd18_0_332 : subd18_0 [0, 1, 5] = true := by decide +kernel
theorem subd18_0_333 : subd18_0 [0, 1, 6] = true := by decide +kernel
theorem subd18_0_334 : subd18_0 [0, 1, 7] = true := by decide +kernel
theorem subd18_0_335 : subd18_0 [0, 1, 8] = true := by decide +kernel
theorem subd18_0_336 : subd18_0 [0, 1, 9] = true := by decide +kernel
theorem subd18_0_337 : subd18_0 [0, 1, 10] = true := by decide +kernel
theorem subd18_0_338 : subd18_0 [0, 1, 11] = true := by decide +kernel
theorem subd18_0_339 : subd18_0 [0, 1, 12] = true := by decide +kernel
theorem subd18_0_340 : subd18_0 [0, 2, -12] = true := by decide +kernel
theorem subd18_0_341 : subd18_0 [0, 2, -11] = true := by decide +kernel
theorem subd18_0_342 : subd18_0 [0, 2, -10] = true := by decide +kernel
theorem subd18_0_343 : subd18_0 [0, 2, -9] = true := by decide +kernel
theorem subd18_0_344 : subd18_0 [0, 2, -8] = true := by decide +kernel
theorem subd18_0_345 : subd18_0 [0, 2, -7] = true := by decide +kernel
theorem subd18_0_346 : subd18_0 [0, 2, -6] = true := by decide +kernel
theorem subd18_0_347 : subd18_0 [0, 2, -5] = true := by decide +kernel
theorem subd18_0_348 : subd18_0 [0, 2, -4] = true := by decide +kernel
theorem subd18_0_349 : subd18_0 [0, 2, -3] = true := by decide +kernel
theorem subd18_0_350 : subd18_0 [0, 2, -2] = true := by decide +kernel
theorem subd18_0_351 : subd18_0 [0, 2, -1] = true := by decide +kernel
theorem sbd18_0_10 : ∀ q ∈ blkd18_0_10, subd18_0 q = true := by
  unfold blkd18_0_10
  exact List.forall_mem_cons.2 ⟨subd18_0_320, List.forall_mem_cons.2 ⟨subd18_0_321, List.forall_mem_cons.2 ⟨subd18_0_322, List.forall_mem_cons.2 ⟨subd18_0_323, List.forall_mem_cons.2 ⟨subd18_0_324, List.forall_mem_cons.2 ⟨subd18_0_325, List.forall_mem_cons.2 ⟨subd18_0_326, List.forall_mem_cons.2 ⟨subd18_0_327, List.forall_mem_cons.2 ⟨subd18_0_328, List.forall_mem_cons.2 ⟨subd18_0_329, List.forall_mem_cons.2 ⟨subd18_0_330, List.forall_mem_cons.2 ⟨subd18_0_331, List.forall_mem_cons.2 ⟨subd18_0_332, List.forall_mem_cons.2 ⟨subd18_0_333, List.forall_mem_cons.2 ⟨subd18_0_334, List.forall_mem_cons.2 ⟨subd18_0_335, List.forall_mem_cons.2 ⟨subd18_0_336, List.forall_mem_cons.2 ⟨subd18_0_337, List.forall_mem_cons.2 ⟨subd18_0_338, List.forall_mem_cons.2 ⟨subd18_0_339, List.forall_mem_cons.2 ⟨subd18_0_340, List.forall_mem_cons.2 ⟨subd18_0_341, List.forall_mem_cons.2 ⟨subd18_0_342, List.forall_mem_cons.2 ⟨subd18_0_343, List.forall_mem_cons.2 ⟨subd18_0_344, List.forall_mem_cons.2 ⟨subd18_0_345, List.forall_mem_cons.2 ⟨subd18_0_346, List.forall_mem_cons.2 ⟨subd18_0_347, List.forall_mem_cons.2 ⟨subd18_0_348, List.forall_mem_cons.2 ⟨subd18_0_349, List.forall_mem_cons.2 ⟨subd18_0_350, List.forall_mem_cons.2 ⟨subd18_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_0_352 : subd18_0 [0, 2, 0] = true := by decide +kernel
theorem subd18_0_353 : subd18_0 [0, 2, 1] = true := by decide +kernel
theorem subd18_0_354 : subd18_0 [0, 2, 2] = true := by decide +kernel
theorem subd18_0_355 : subd18_0 [0, 2, 3] = true := by decide +kernel
theorem subd18_0_356 : subd18_0 [0, 2, 4] = true := by decide +kernel
theorem subd18_0_357 : subd18_0 [0, 2, 5] = true := by decide +kernel
theorem subd18_0_358 : subd18_0 [0, 2, 6] = true := by decide +kernel
theorem subd18_0_359 : subd18_0 [0, 2, 7] = true := by decide +kernel
theorem subd18_0_360 : subd18_0 [0, 2, 8] = true := by decide +kernel
theorem subd18_0_361 : subd18_0 [0, 2, 9] = true := by decide +kernel
theorem subd18_0_362 : subd18_0 [0, 2, 10] = true := by decide +kernel
theorem subd18_0_363 : subd18_0 [0, 3, -8] = true := by decide +kernel
theorem subd18_0_364 : subd18_0 [0, 3, -7] = true := by decide +kernel
theorem subd18_0_365 : subd18_0 [0, 3, -6] = true := by decide +kernel
theorem subd18_0_366 : subd18_0 [0, 3, -5] = true := by decide +kernel
theorem subd18_0_367 : subd18_0 [0, 3, -4] = true := by decide +kernel
theorem subd18_0_368 : subd18_0 [0, 3, -3] = true := by decide +kernel
theorem subd18_0_369 : subd18_0 [0, 3, -2] = true := by decide +kernel
theorem subd18_0_370 : subd18_0 [0, 3, -1] = true := by decide +kernel
theorem subd18_0_371 : subd18_0 [0, 3, 0] = true := by decide +kernel
theorem subd18_0_372 : subd18_0 [0, 3, 1] = true := by decide +kernel
theorem subd18_0_373 : subd18_0 [0, 3, 2] = true := by decide +kernel
theorem subd18_0_374 : subd18_0 [0, 3, 3] = true := by decide +kernel
theorem subd18_0_375 : subd18_0 [0, 3, 4] = true := by decide +kernel
theorem subd18_0_376 : subd18_0 [0, 3, 5] = true := by decide +kernel
theorem subd18_0_377 : subd18_0 [0, 3, 6] = true := by decide +kernel
theorem subd18_0_378 : subd18_0 [1, -4] = true := by decide +kernel
theorem subd18_0_379 : subd18_0 [1, -3] = true := by decide +kernel
theorem subd18_0_380 : subd18_0 [1, -2, -9] = true := by decide +kernel
theorem subd18_0_381 : subd18_0 [1, -2, -8] = true := by decide +kernel
theorem subd18_0_382 : subd18_0 [1, -2, -7] = true := by decide +kernel
theorem subd18_0_383 : subd18_0 [1, -2, -6] = true := by decide +kernel
theorem sbd18_0_11 : ∀ q ∈ blkd18_0_11, subd18_0 q = true := by
  unfold blkd18_0_11
  exact List.forall_mem_cons.2 ⟨subd18_0_352, List.forall_mem_cons.2 ⟨subd18_0_353, List.forall_mem_cons.2 ⟨subd18_0_354, List.forall_mem_cons.2 ⟨subd18_0_355, List.forall_mem_cons.2 ⟨subd18_0_356, List.forall_mem_cons.2 ⟨subd18_0_357, List.forall_mem_cons.2 ⟨subd18_0_358, List.forall_mem_cons.2 ⟨subd18_0_359, List.forall_mem_cons.2 ⟨subd18_0_360, List.forall_mem_cons.2 ⟨subd18_0_361, List.forall_mem_cons.2 ⟨subd18_0_362, List.forall_mem_cons.2 ⟨subd18_0_363, List.forall_mem_cons.2 ⟨subd18_0_364, List.forall_mem_cons.2 ⟨subd18_0_365, List.forall_mem_cons.2 ⟨subd18_0_366, List.forall_mem_cons.2 ⟨subd18_0_367, List.forall_mem_cons.2 ⟨subd18_0_368, List.forall_mem_cons.2 ⟨subd18_0_369, List.forall_mem_cons.2 ⟨subd18_0_370, List.forall_mem_cons.2 ⟨subd18_0_371, List.forall_mem_cons.2 ⟨subd18_0_372, List.forall_mem_cons.2 ⟨subd18_0_373, List.forall_mem_cons.2 ⟨subd18_0_374, List.forall_mem_cons.2 ⟨subd18_0_375, List.forall_mem_cons.2 ⟨subd18_0_376, List.forall_mem_cons.2 ⟨subd18_0_377, List.forall_mem_cons.2 ⟨subd18_0_378, List.forall_mem_cons.2 ⟨subd18_0_379, List.forall_mem_cons.2 ⟨subd18_0_380, List.forall_mem_cons.2 ⟨subd18_0_381, List.forall_mem_cons.2 ⟨subd18_0_382, List.forall_mem_cons.2 ⟨subd18_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
