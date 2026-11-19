import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [-5] = true := by decide +kernel
theorem subd15_3_1 : subd15_3 [-4, -5] = true := by decide +kernel
theorem subd15_3_2 : subd15_3 [-4, -4] = true := by decide +kernel
theorem subd15_3_3 : subd15_3 [-4, -3] = true := by decide +kernel
theorem subd15_3_4 : subd15_3 [-4, -2] = true := by decide +kernel
theorem subd15_3_5 : subd15_3 [-4, -1] = true := by decide +kernel
theorem subd15_3_6 : subd15_3 [-4, 0] = true := by decide +kernel
theorem subd15_3_7 : subd15_3 [-4, 1] = true := by decide +kernel
theorem subd15_3_8 : subd15_3 [-4, 2] = true := by decide +kernel
theorem subd15_3_9 : subd15_3 [-3, -6] = true := by decide +kernel
theorem subd15_3_10 : subd15_3 [-3, -5] = true := by decide +kernel
theorem subd15_3_11 : subd15_3 [-3, -4] = true := by decide +kernel
theorem subd15_3_12 : subd15_3 [-3, -3, -7] = true := by decide +kernel
theorem subd15_3_13 : subd15_3 [-3, -3, -6] = true := by decide +kernel
theorem subd15_3_14 : subd15_3 [-3, -3, -5] = true := by decide +kernel
theorem subd15_3_15 : subd15_3 [-3, -3, -4] = true := by decide +kernel
theorem subd15_3_16 : subd15_3 [-3, -3, -3] = true := by decide +kernel
theorem subd15_3_17 : subd15_3 [-3, -3, -2] = true := by decide +kernel
theorem subd15_3_18 : subd15_3 [-3, -3, -1] = true := by decide +kernel
theorem subd15_3_19 : subd15_3 [-3, -3, 0] = true := by decide +kernel
theorem subd15_3_20 : subd15_3 [-3, -3, 1] = true := by decide +kernel
theorem subd15_3_21 : subd15_3 [-3, -3, 2] = true := by decide +kernel
theorem subd15_3_22 : subd15_3 [-3, -3, 3] = true := by decide +kernel
theorem subd15_3_23 : subd15_3 [-3, -3, 4] = true := by decide +kernel
theorem subd15_3_24 : subd15_3 [-3, -3, 5] = true := by decide +kernel
theorem subd15_3_25 : subd15_3 [-3, -2, -8] = true := by decide +kernel
theorem subd15_3_26 : subd15_3 [-3, -2, -7] = true := by decide +kernel
theorem subd15_3_27 : subd15_3 [-3, -2, -6] = true := by decide +kernel
theorem subd15_3_28 : subd15_3 [-3, -2, -5] = true := by decide +kernel
theorem subd15_3_29 : subd15_3 [-3, -2, -4] = true := by decide +kernel
theorem subd15_3_30 : subd15_3 [-3, -2, -3] = true := by decide +kernel
theorem subd15_3_31 : subd15_3 [-3, -2, -2] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_cons.2 ⟨subd15_3_1, List.forall_mem_cons.2 ⟨subd15_3_2, List.forall_mem_cons.2 ⟨subd15_3_3, List.forall_mem_cons.2 ⟨subd15_3_4, List.forall_mem_cons.2 ⟨subd15_3_5, List.forall_mem_cons.2 ⟨subd15_3_6, List.forall_mem_cons.2 ⟨subd15_3_7, List.forall_mem_cons.2 ⟨subd15_3_8, List.forall_mem_cons.2 ⟨subd15_3_9, List.forall_mem_cons.2 ⟨subd15_3_10, List.forall_mem_cons.2 ⟨subd15_3_11, List.forall_mem_cons.2 ⟨subd15_3_12, List.forall_mem_cons.2 ⟨subd15_3_13, List.forall_mem_cons.2 ⟨subd15_3_14, List.forall_mem_cons.2 ⟨subd15_3_15, List.forall_mem_cons.2 ⟨subd15_3_16, List.forall_mem_cons.2 ⟨subd15_3_17, List.forall_mem_cons.2 ⟨subd15_3_18, List.forall_mem_cons.2 ⟨subd15_3_19, List.forall_mem_cons.2 ⟨subd15_3_20, List.forall_mem_cons.2 ⟨subd15_3_21, List.forall_mem_cons.2 ⟨subd15_3_22, List.forall_mem_cons.2 ⟨subd15_3_23, List.forall_mem_cons.2 ⟨subd15_3_24, List.forall_mem_cons.2 ⟨subd15_3_25, List.forall_mem_cons.2 ⟨subd15_3_26, List.forall_mem_cons.2 ⟨subd15_3_27, List.forall_mem_cons.2 ⟨subd15_3_28, List.forall_mem_cons.2 ⟨subd15_3_29, List.forall_mem_cons.2 ⟨subd15_3_30, List.forall_mem_cons.2 ⟨subd15_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_32 : subd15_3 [-3, -2, -1] = true := by decide +kernel
theorem subd15_3_33 : subd15_3 [-3, -2, 0] = true := by decide +kernel
theorem subd15_3_34 : subd15_3 [-3, -2, 1] = true := by decide +kernel
theorem subd15_3_35 : subd15_3 [-3, -2, 2] = true := by decide +kernel
theorem subd15_3_36 : subd15_3 [-3, -2, 3] = true := by decide +kernel
theorem subd15_3_37 : subd15_3 [-3, -2, 4] = true := by decide +kernel
theorem subd15_3_38 : subd15_3 [-3, -2, 5] = true := by decide +kernel
theorem subd15_3_39 : subd15_3 [-3, -1, -9] = true := by decide +kernel
theorem subd15_3_40 : subd15_3 [-3, -1, -8] = true := by decide +kernel
theorem subd15_3_41 : subd15_3 [-3, -1, -7] = true := by decide +kernel
theorem subd15_3_42 : subd15_3 [-3, -1, -6] = true := by decide +kernel
theorem subd15_3_43 : subd15_3 [-3, -1, -5] = true := by decide +kernel
theorem subd15_3_44 : subd15_3 [-3, -1, -4] = true := by decide +kernel
theorem subd15_3_45 : subd15_3 [-3, -1, -3] = true := by decide +kernel
theorem subd15_3_46 : subd15_3 [-3, -1, -2] = true := by decide +kernel
theorem subd15_3_47 : subd15_3 [-3, -1, -1] = true := by decide +kernel
theorem subd15_3_48 : subd15_3 [-3, -1, 0] = true := by decide +kernel
theorem subd15_3_49 : subd15_3 [-3, -1, 1] = true := by decide +kernel
theorem subd15_3_50 : subd15_3 [-3, -1, 2] = true := by decide +kernel
theorem subd15_3_51 : subd15_3 [-3, -1, 3] = true := by decide +kernel
theorem subd15_3_52 : subd15_3 [-3, -1, 4] = true := by decide +kernel
theorem subd15_3_53 : subd15_3 [-3, -1, 5] = true := by decide +kernel
theorem subd15_3_54 : subd15_3 [-3, 0, -9] = true := by decide +kernel
theorem subd15_3_55 : subd15_3 [-3, 0, -8] = true := by decide +kernel
theorem subd15_3_56 : subd15_3 [-3, 0, -7] = true := by decide +kernel
theorem subd15_3_57 : subd15_3 [-3, 0, -6] = true := by decide +kernel
theorem subd15_3_58 : subd15_3 [-3, 0, -5] = true := by decide +kernel
theorem subd15_3_59 : subd15_3 [-3, 0, -4] = true := by decide +kernel
theorem subd15_3_60 : subd15_3 [-3, 0, -3] = true := by decide +kernel
theorem subd15_3_61 : subd15_3 [-3, 0, -2] = true := by decide +kernel
theorem subd15_3_62 : subd15_3 [-3, 0, -1] = true := by decide +kernel
theorem subd15_3_63 : subd15_3 [-3, 0, 0] = true := by decide +kernel
theorem sbd15_3_1 : ∀ q ∈ blkd15_3_1, subd15_3 q = true := by
  unfold blkd15_3_1
  exact List.forall_mem_cons.2 ⟨subd15_3_32, List.forall_mem_cons.2 ⟨subd15_3_33, List.forall_mem_cons.2 ⟨subd15_3_34, List.forall_mem_cons.2 ⟨subd15_3_35, List.forall_mem_cons.2 ⟨subd15_3_36, List.forall_mem_cons.2 ⟨subd15_3_37, List.forall_mem_cons.2 ⟨subd15_3_38, List.forall_mem_cons.2 ⟨subd15_3_39, List.forall_mem_cons.2 ⟨subd15_3_40, List.forall_mem_cons.2 ⟨subd15_3_41, List.forall_mem_cons.2 ⟨subd15_3_42, List.forall_mem_cons.2 ⟨subd15_3_43, List.forall_mem_cons.2 ⟨subd15_3_44, List.forall_mem_cons.2 ⟨subd15_3_45, List.forall_mem_cons.2 ⟨subd15_3_46, List.forall_mem_cons.2 ⟨subd15_3_47, List.forall_mem_cons.2 ⟨subd15_3_48, List.forall_mem_cons.2 ⟨subd15_3_49, List.forall_mem_cons.2 ⟨subd15_3_50, List.forall_mem_cons.2 ⟨subd15_3_51, List.forall_mem_cons.2 ⟨subd15_3_52, List.forall_mem_cons.2 ⟨subd15_3_53, List.forall_mem_cons.2 ⟨subd15_3_54, List.forall_mem_cons.2 ⟨subd15_3_55, List.forall_mem_cons.2 ⟨subd15_3_56, List.forall_mem_cons.2 ⟨subd15_3_57, List.forall_mem_cons.2 ⟨subd15_3_58, List.forall_mem_cons.2 ⟨subd15_3_59, List.forall_mem_cons.2 ⟨subd15_3_60, List.forall_mem_cons.2 ⟨subd15_3_61, List.forall_mem_cons.2 ⟨subd15_3_62, List.forall_mem_cons.2 ⟨subd15_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_64 : subd15_3 [-3, 0, 1] = true := by decide +kernel
theorem subd15_3_65 : subd15_3 [-3, 0, 2] = true := by decide +kernel
theorem subd15_3_66 : subd15_3 [-3, 0, 3] = true := by decide +kernel
theorem subd15_3_67 : subd15_3 [-3, 0, 4] = true := by decide +kernel
theorem subd15_3_68 : subd15_3 [-3, 0, 5] = true := by decide +kernel
theorem subd15_3_69 : subd15_3 [-3, 1, -9] = true := by decide +kernel
theorem subd15_3_70 : subd15_3 [-3, 1, -8] = true := by decide +kernel
theorem subd15_3_71 : subd15_3 [-3, 1, -7] = true := by decide +kernel
theorem subd15_3_72 : subd15_3 [-3, 1, -6] = true := by decide +kernel
theorem subd15_3_73 : subd15_3 [-3, 1, -5] = true := by decide +kernel
theorem subd15_3_74 : subd15_3 [-3, 1, -4] = true := by decide +kernel
theorem subd15_3_75 : subd15_3 [-3, 1, -3] = true := by decide +kernel
theorem subd15_3_76 : subd15_3 [-3, 1, -2] = true := by decide +kernel
theorem subd15_3_77 : subd15_3 [-3, 1, -1] = true := by decide +kernel
theorem subd15_3_78 : subd15_3 [-3, 1, 0] = true := by decide +kernel
theorem subd15_3_79 : subd15_3 [-3, 1, 1] = true := by decide +kernel
theorem subd15_3_80 : subd15_3 [-3, 1, 2] = true := by decide +kernel
theorem subd15_3_81 : subd15_3 [-3, 1, 3] = true := by decide +kernel
theorem subd15_3_82 : subd15_3 [-3, 1, 4] = true := by decide +kernel
theorem subd15_3_83 : subd15_3 [-3, 2] = true := by decide +kernel
theorem subd15_3_84 : subd15_3 [-3, 3] = true := by decide +kernel
theorem subd15_3_85 : subd15_3 [-3, 4] = true := by decide +kernel
theorem subd15_3_86 : subd15_3 [-2, -6] = true := by decide +kernel
theorem subd15_3_87 : subd15_3 [-2, -5] = true := by decide +kernel
theorem subd15_3_88 : subd15_3 [-2, -4] = true := by decide +kernel
theorem subd15_3_89 : subd15_3 [-2, -3, -7] = true := by decide +kernel
theorem subd15_3_90 : subd15_3 [-2, -3, -6] = true := by decide +kernel
theorem subd15_3_91 : subd15_3 [-2, -3, -5] = true := by decide +kernel
theorem subd15_3_92 : subd15_3 [-2, -3, -4] = true := by decide +kernel
theorem subd15_3_93 : subd15_3 [-2, -3, -3] = true := by decide +kernel
theorem subd15_3_94 : subd15_3 [-2, -3, -2] = true := by decide +kernel
theorem subd15_3_95 : subd15_3 [-2, -3, -1] = true := by decide +kernel
theorem sbd15_3_2 : ∀ q ∈ blkd15_3_2, subd15_3 q = true := by
  unfold blkd15_3_2
  exact List.forall_mem_cons.2 ⟨subd15_3_64, List.forall_mem_cons.2 ⟨subd15_3_65, List.forall_mem_cons.2 ⟨subd15_3_66, List.forall_mem_cons.2 ⟨subd15_3_67, List.forall_mem_cons.2 ⟨subd15_3_68, List.forall_mem_cons.2 ⟨subd15_3_69, List.forall_mem_cons.2 ⟨subd15_3_70, List.forall_mem_cons.2 ⟨subd15_3_71, List.forall_mem_cons.2 ⟨subd15_3_72, List.forall_mem_cons.2 ⟨subd15_3_73, List.forall_mem_cons.2 ⟨subd15_3_74, List.forall_mem_cons.2 ⟨subd15_3_75, List.forall_mem_cons.2 ⟨subd15_3_76, List.forall_mem_cons.2 ⟨subd15_3_77, List.forall_mem_cons.2 ⟨subd15_3_78, List.forall_mem_cons.2 ⟨subd15_3_79, List.forall_mem_cons.2 ⟨subd15_3_80, List.forall_mem_cons.2 ⟨subd15_3_81, List.forall_mem_cons.2 ⟨subd15_3_82, List.forall_mem_cons.2 ⟨subd15_3_83, List.forall_mem_cons.2 ⟨subd15_3_84, List.forall_mem_cons.2 ⟨subd15_3_85, List.forall_mem_cons.2 ⟨subd15_3_86, List.forall_mem_cons.2 ⟨subd15_3_87, List.forall_mem_cons.2 ⟨subd15_3_88, List.forall_mem_cons.2 ⟨subd15_3_89, List.forall_mem_cons.2 ⟨subd15_3_90, List.forall_mem_cons.2 ⟨subd15_3_91, List.forall_mem_cons.2 ⟨subd15_3_92, List.forall_mem_cons.2 ⟨subd15_3_93, List.forall_mem_cons.2 ⟨subd15_3_94, List.forall_mem_cons.2 ⟨subd15_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_96 : subd15_3 [-2, -3, 0] = true := by decide +kernel
theorem subd15_3_97 : subd15_3 [-2, -3, 1] = true := by decide +kernel
theorem subd15_3_98 : subd15_3 [-2, -3, 2] = true := by decide +kernel
theorem subd15_3_99 : subd15_3 [-2, -3, 3] = true := by decide +kernel
theorem subd15_3_100 : subd15_3 [-2, -3, 4] = true := by decide +kernel
theorem subd15_3_101 : subd15_3 [-2, -3, 5] = true := by decide +kernel
theorem subd15_3_102 : subd15_3 [-2, -3, 6] = true := by decide +kernel
theorem subd15_3_103 : subd15_3 [-2, -2, -8] = true := by decide +kernel
theorem subd15_3_104 : subd15_3 [-2, -2, -7] = true := by decide +kernel
theorem subd15_3_105 : subd15_3 [-2, -2, -6] = true := by decide +kernel
theorem subd15_3_106 : subd15_3 [-2, -2, -5] = true := by decide +kernel
theorem subd15_3_107 : subd15_3 [-2, -2, -4] = true := by decide +kernel
theorem subd15_3_108 : subd15_3 [-2, -2, -3] = true := by decide +kernel
theorem subd15_3_109 : subd15_3 [-2, -2, -2] = true := by decide +kernel
theorem subd15_3_110 : subd15_3 [-2, -2, -1] = true := by decide +kernel
theorem subd15_3_111 : subd15_3 [-2, -2, 0] = true := by decide +kernel
theorem subd15_3_112 : subd15_3 [-2, -2, 1] = true := by decide +kernel
theorem subd15_3_113 : subd15_3 [-2, -2, 2] = true := by decide +kernel
theorem subd15_3_114 : subd15_3 [-2, -2, 3] = true := by decide +kernel
theorem subd15_3_115 : subd15_3 [-2, -2, 4] = true := by decide +kernel
theorem subd15_3_116 : subd15_3 [-2, -2, 5] = true := by decide +kernel
theorem subd15_3_117 : subd15_3 [-2, -2, 6] = true := by decide +kernel
theorem subd15_3_118 : subd15_3 [-2, -2, 7] = true := by decide +kernel
theorem subd15_3_119 : subd15_3 [-2, -1, -9] = true := by decide +kernel
theorem subd15_3_120 : subd15_3 [-2, -1, -8] = true := by decide +kernel
theorem subd15_3_121 : subd15_3 [-2, -1, -7] = true := by decide +kernel
theorem subd15_3_122 : subd15_3 [-2, -1, -6] = true := by decide +kernel
theorem subd15_3_123 : subd15_3 [-2, -1, -5] = true := by decide +kernel
theorem subd15_3_124 : subd15_3 [-2, -1, -4] = true := by decide +kernel
theorem subd15_3_125 : subd15_3 [-2, -1, -3] = true := by decide +kernel
theorem subd15_3_126 : subd15_3 [-2, -1, -2] = true := by decide +kernel
theorem subd15_3_127 : subd15_3 [-2, -1, -1] = true := by decide +kernel
theorem sbd15_3_3 : ∀ q ∈ blkd15_3_3, subd15_3 q = true := by
  unfold blkd15_3_3
  exact List.forall_mem_cons.2 ⟨subd15_3_96, List.forall_mem_cons.2 ⟨subd15_3_97, List.forall_mem_cons.2 ⟨subd15_3_98, List.forall_mem_cons.2 ⟨subd15_3_99, List.forall_mem_cons.2 ⟨subd15_3_100, List.forall_mem_cons.2 ⟨subd15_3_101, List.forall_mem_cons.2 ⟨subd15_3_102, List.forall_mem_cons.2 ⟨subd15_3_103, List.forall_mem_cons.2 ⟨subd15_3_104, List.forall_mem_cons.2 ⟨subd15_3_105, List.forall_mem_cons.2 ⟨subd15_3_106, List.forall_mem_cons.2 ⟨subd15_3_107, List.forall_mem_cons.2 ⟨subd15_3_108, List.forall_mem_cons.2 ⟨subd15_3_109, List.forall_mem_cons.2 ⟨subd15_3_110, List.forall_mem_cons.2 ⟨subd15_3_111, List.forall_mem_cons.2 ⟨subd15_3_112, List.forall_mem_cons.2 ⟨subd15_3_113, List.forall_mem_cons.2 ⟨subd15_3_114, List.forall_mem_cons.2 ⟨subd15_3_115, List.forall_mem_cons.2 ⟨subd15_3_116, List.forall_mem_cons.2 ⟨subd15_3_117, List.forall_mem_cons.2 ⟨subd15_3_118, List.forall_mem_cons.2 ⟨subd15_3_119, List.forall_mem_cons.2 ⟨subd15_3_120, List.forall_mem_cons.2 ⟨subd15_3_121, List.forall_mem_cons.2 ⟨subd15_3_122, List.forall_mem_cons.2 ⟨subd15_3_123, List.forall_mem_cons.2 ⟨subd15_3_124, List.forall_mem_cons.2 ⟨subd15_3_125, List.forall_mem_cons.2 ⟨subd15_3_126, List.forall_mem_cons.2 ⟨subd15_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_128 : subd15_3 [-2, -1, 0] = true := by decide +kernel
theorem subd15_3_129 : subd15_3 [-2, -1, 1] = true := by decide +kernel
theorem subd15_3_130 : subd15_3 [-2, -1, 2] = true := by decide +kernel
theorem subd15_3_131 : subd15_3 [-2, -1, 3] = true := by decide +kernel
theorem subd15_3_132 : subd15_3 [-2, -1, 4] = true := by decide +kernel
theorem subd15_3_133 : subd15_3 [-2, -1, 5] = true := by decide +kernel
theorem subd15_3_134 : subd15_3 [-2, -1, 6] = true := by decide +kernel
theorem subd15_3_135 : subd15_3 [-2, -1, 7] = true := by decide +kernel
theorem subd15_3_136 : subd15_3 [-2, 0, -9] = true := by decide +kernel
theorem subd15_3_137 : subd15_3 [-2, 0, -8] = true := by decide +kernel
theorem subd15_3_138 : subd15_3 [-2, 0, -7] = true := by decide +kernel
theorem subd15_3_139 : subd15_3 [-2, 0, -6] = true := by decide +kernel
theorem subd15_3_140 : subd15_3 [-2, 0, -5] = true := by decide +kernel
theorem subd15_3_141 : subd15_3 [-2, 0, -4] = true := by decide +kernel
theorem subd15_3_142 : subd15_3 [-2, 0, -3] = true := by decide +kernel
theorem subd15_3_143 : subd15_3 [-2, 0, -2] = true := by decide +kernel
theorem subd15_3_144 : subd15_3 [-2, 0, -1] = true := by decide +kernel
theorem subd15_3_145 : subd15_3 [-2, 0, 0] = true := by decide +kernel
theorem subd15_3_146 : subd15_3 [-2, 0, 1] = true := by decide +kernel
theorem subd15_3_147 : subd15_3 [-2, 0, 2] = true := by decide +kernel
theorem subd15_3_148 : subd15_3 [-2, 0, 3] = true := by decide +kernel
theorem subd15_3_149 : subd15_3 [-2, 0, 4] = true := by decide +kernel
theorem subd15_3_150 : subd15_3 [-2, 0, 5] = true := by decide +kernel
theorem subd15_3_151 : subd15_3 [-2, 0, 6] = true := by decide +kernel
theorem subd15_3_152 : subd15_3 [-2, 1, -9] = true := by decide +kernel
theorem subd15_3_153 : subd15_3 [-2, 1, -8] = true := by decide +kernel
theorem subd15_3_154 : subd15_3 [-2, 1, -7] = true := by decide +kernel
theorem subd15_3_155 : subd15_3 [-2, 1, -6] = true := by decide +kernel
theorem subd15_3_156 : subd15_3 [-2, 1, -5] = true := by decide +kernel
theorem subd15_3_157 : subd15_3 [-2, 1, -4] = true := by decide +kernel
theorem subd15_3_158 : subd15_3 [-2, 1, -3] = true := by decide +kernel
theorem subd15_3_159 : subd15_3 [-2, 1, -2] = true := by decide +kernel
theorem sbd15_3_4 : ∀ q ∈ blkd15_3_4, subd15_3 q = true := by
  unfold blkd15_3_4
  exact List.forall_mem_cons.2 ⟨subd15_3_128, List.forall_mem_cons.2 ⟨subd15_3_129, List.forall_mem_cons.2 ⟨subd15_3_130, List.forall_mem_cons.2 ⟨subd15_3_131, List.forall_mem_cons.2 ⟨subd15_3_132, List.forall_mem_cons.2 ⟨subd15_3_133, List.forall_mem_cons.2 ⟨subd15_3_134, List.forall_mem_cons.2 ⟨subd15_3_135, List.forall_mem_cons.2 ⟨subd15_3_136, List.forall_mem_cons.2 ⟨subd15_3_137, List.forall_mem_cons.2 ⟨subd15_3_138, List.forall_mem_cons.2 ⟨subd15_3_139, List.forall_mem_cons.2 ⟨subd15_3_140, List.forall_mem_cons.2 ⟨subd15_3_141, List.forall_mem_cons.2 ⟨subd15_3_142, List.forall_mem_cons.2 ⟨subd15_3_143, List.forall_mem_cons.2 ⟨subd15_3_144, List.forall_mem_cons.2 ⟨subd15_3_145, List.forall_mem_cons.2 ⟨subd15_3_146, List.forall_mem_cons.2 ⟨subd15_3_147, List.forall_mem_cons.2 ⟨subd15_3_148, List.forall_mem_cons.2 ⟨subd15_3_149, List.forall_mem_cons.2 ⟨subd15_3_150, List.forall_mem_cons.2 ⟨subd15_3_151, List.forall_mem_cons.2 ⟨subd15_3_152, List.forall_mem_cons.2 ⟨subd15_3_153, List.forall_mem_cons.2 ⟨subd15_3_154, List.forall_mem_cons.2 ⟨subd15_3_155, List.forall_mem_cons.2 ⟨subd15_3_156, List.forall_mem_cons.2 ⟨subd15_3_157, List.forall_mem_cons.2 ⟨subd15_3_158, List.forall_mem_cons.2 ⟨subd15_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_160 : subd15_3 [-2, 1, -1] = true := by decide +kernel
theorem subd15_3_161 : subd15_3 [-2, 1, 0] = true := by decide +kernel
theorem subd15_3_162 : subd15_3 [-2, 1, 1] = true := by decide +kernel
theorem subd15_3_163 : subd15_3 [-2, 1, 2] = true := by decide +kernel
theorem subd15_3_164 : subd15_3 [-2, 1, 3] = true := by decide +kernel
theorem subd15_3_165 : subd15_3 [-2, 1, 4] = true := by decide +kernel
theorem subd15_3_166 : subd15_3 [-2, 1, 5] = true := by decide +kernel
theorem subd15_3_167 : subd15_3 [-2, 1, 6] = true := by decide +kernel
theorem subd15_3_168 : subd15_3 [-2, 2, -9] = true := by decide +kernel
theorem subd15_3_169 : subd15_3 [-2, 2, -8] = true := by decide +kernel
theorem subd15_3_170 : subd15_3 [-2, 2, -7] = true := by decide +kernel
theorem subd15_3_171 : subd15_3 [-2, 2, -6] = true := by decide +kernel
theorem subd15_3_172 : subd15_3 [-2, 2, -5] = true := by decide +kernel
theorem subd15_3_173 : subd15_3 [-2, 2, -4] = true := by decide +kernel
theorem subd15_3_174 : subd15_3 [-2, 2, -3] = true := by decide +kernel
theorem subd15_3_175 : subd15_3 [-2, 2, -2] = true := by decide +kernel
theorem subd15_3_176 : subd15_3 [-2, 2, -1] = true := by decide +kernel
theorem subd15_3_177 : subd15_3 [-2, 2, 0] = true := by decide +kernel
theorem subd15_3_178 : subd15_3 [-2, 2, 1] = true := by decide +kernel
theorem subd15_3_179 : subd15_3 [-2, 2, 2] = true := by decide +kernel
theorem subd15_3_180 : subd15_3 [-2, 2, 3] = true := by decide +kernel
theorem subd15_3_181 : subd15_3 [-2, 2, 4] = true := by decide +kernel
theorem subd15_3_182 : subd15_3 [-2, 2, 5] = true := by decide +kernel
theorem subd15_3_183 : subd15_3 [-2, 3] = true := by decide +kernel
theorem subd15_3_184 : subd15_3 [-2, 4] = true := by decide +kernel
theorem subd15_3_185 : subd15_3 [-1, -6] = true := by decide +kernel
theorem subd15_3_186 : subd15_3 [-1, -5] = true := by decide +kernel
theorem subd15_3_187 : subd15_3 [-1, -4, -6] = true := by decide +kernel
theorem subd15_3_188 : subd15_3 [-1, -4, -5] = true := by decide +kernel
theorem subd15_3_189 : subd15_3 [-1, -4, -4] = true := by decide +kernel
theorem subd15_3_190 : subd15_3 [-1, -4, -3] = true := by decide +kernel
theorem subd15_3_191 : subd15_3 [-1, -4, -2] = true := by decide +kernel
theorem sbd15_3_5 : ∀ q ∈ blkd15_3_5, subd15_3 q = true := by
  unfold blkd15_3_5
  exact List.forall_mem_cons.2 ⟨subd15_3_160, List.forall_mem_cons.2 ⟨subd15_3_161, List.forall_mem_cons.2 ⟨subd15_3_162, List.forall_mem_cons.2 ⟨subd15_3_163, List.forall_mem_cons.2 ⟨subd15_3_164, List.forall_mem_cons.2 ⟨subd15_3_165, List.forall_mem_cons.2 ⟨subd15_3_166, List.forall_mem_cons.2 ⟨subd15_3_167, List.forall_mem_cons.2 ⟨subd15_3_168, List.forall_mem_cons.2 ⟨subd15_3_169, List.forall_mem_cons.2 ⟨subd15_3_170, List.forall_mem_cons.2 ⟨subd15_3_171, List.forall_mem_cons.2 ⟨subd15_3_172, List.forall_mem_cons.2 ⟨subd15_3_173, List.forall_mem_cons.2 ⟨subd15_3_174, List.forall_mem_cons.2 ⟨subd15_3_175, List.forall_mem_cons.2 ⟨subd15_3_176, List.forall_mem_cons.2 ⟨subd15_3_177, List.forall_mem_cons.2 ⟨subd15_3_178, List.forall_mem_cons.2 ⟨subd15_3_179, List.forall_mem_cons.2 ⟨subd15_3_180, List.forall_mem_cons.2 ⟨subd15_3_181, List.forall_mem_cons.2 ⟨subd15_3_182, List.forall_mem_cons.2 ⟨subd15_3_183, List.forall_mem_cons.2 ⟨subd15_3_184, List.forall_mem_cons.2 ⟨subd15_3_185, List.forall_mem_cons.2 ⟨subd15_3_186, List.forall_mem_cons.2 ⟨subd15_3_187, List.forall_mem_cons.2 ⟨subd15_3_188, List.forall_mem_cons.2 ⟨subd15_3_189, List.forall_mem_cons.2 ⟨subd15_3_190, List.forall_mem_cons.2 ⟨subd15_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_192 : subd15_3 [-1, -4, -1] = true := by decide +kernel
theorem subd15_3_193 : subd15_3 [-1, -4, 0] = true := by decide +kernel
theorem subd15_3_194 : subd15_3 [-1, -4, 1] = true := by decide +kernel
theorem subd15_3_195 : subd15_3 [-1, -4, 2] = true := by decide +kernel
theorem subd15_3_196 : subd15_3 [-1, -4, 3] = true := by decide +kernel
theorem subd15_3_197 : subd15_3 [-1, -4, 4] = true := by decide +kernel
theorem subd15_3_198 : subd15_3 [-1, -4, 5] = true := by decide +kernel
theorem subd15_3_199 : subd15_3 [-1, -4, 6] = true := by decide +kernel
theorem subd15_3_200 : subd15_3 [-1, -4, 7] = true := by decide +kernel
theorem subd15_3_201 : subd15_3 [-1, -3, -7] = true := by decide +kernel
theorem subd15_3_202 : subd15_3 [-1, -3, -6] = true := by decide +kernel
theorem subd15_3_203 : subd15_3 [-1, -3, -5] = true := by decide +kernel
theorem subd15_3_204 : subd15_3 [-1, -3, -4] = true := by decide +kernel
theorem subd15_3_205 : subd15_3 [-1, -3, -3] = true := by decide +kernel
theorem subd15_3_206 : subd15_3 [-1, -3, -2] = true := by decide +kernel
theorem subd15_3_207 : subd15_3 [-1, -3, -1] = true := by decide +kernel
theorem subd15_3_208 : subd15_3 [-1, -3, 0] = true := by decide +kernel
theorem subd15_3_209 : subd15_3 [-1, -3, 1] = true := by decide +kernel
theorem subd15_3_210 : subd15_3 [-1, -3, 2] = true := by decide +kernel
theorem subd15_3_211 : subd15_3 [-1, -3, 3] = true := by decide +kernel
theorem subd15_3_212 : subd15_3 [-1, -3, 4] = true := by decide +kernel
theorem subd15_3_213 : subd15_3 [-1, -3, 5] = true := by decide +kernel
theorem subd15_3_214 : subd15_3 [-1, -3, 6] = true := by decide +kernel
theorem subd15_3_215 : subd15_3 [-1, -3, 7] = true := by decide +kernel
theorem subd15_3_216 : subd15_3 [-1, -2, -8] = true := by decide +kernel
theorem subd15_3_217 : subd15_3 [-1, -2, -7] = true := by decide +kernel
theorem subd15_3_218 : subd15_3 [-1, -2, -6] = true := by decide +kernel
theorem subd15_3_219 : subd15_3 [-1, -2, -5] = true := by decide +kernel
theorem subd15_3_220 : subd15_3 [-1, -2, -4] = true := by decide +kernel
theorem subd15_3_221 : subd15_3 [-1, -2, -3] = true := by decide +kernel
theorem subd15_3_222 : subd15_3 [-1, -2, -2] = true := by decide +kernel
theorem subd15_3_223 : subd15_3 [-1, -2, -1] = true := by decide +kernel
theorem sbd15_3_6 : ∀ q ∈ blkd15_3_6, subd15_3 q = true := by
  unfold blkd15_3_6
  exact List.forall_mem_cons.2 ⟨subd15_3_192, List.forall_mem_cons.2 ⟨subd15_3_193, List.forall_mem_cons.2 ⟨subd15_3_194, List.forall_mem_cons.2 ⟨subd15_3_195, List.forall_mem_cons.2 ⟨subd15_3_196, List.forall_mem_cons.2 ⟨subd15_3_197, List.forall_mem_cons.2 ⟨subd15_3_198, List.forall_mem_cons.2 ⟨subd15_3_199, List.forall_mem_cons.2 ⟨subd15_3_200, List.forall_mem_cons.2 ⟨subd15_3_201, List.forall_mem_cons.2 ⟨subd15_3_202, List.forall_mem_cons.2 ⟨subd15_3_203, List.forall_mem_cons.2 ⟨subd15_3_204, List.forall_mem_cons.2 ⟨subd15_3_205, List.forall_mem_cons.2 ⟨subd15_3_206, List.forall_mem_cons.2 ⟨subd15_3_207, List.forall_mem_cons.2 ⟨subd15_3_208, List.forall_mem_cons.2 ⟨subd15_3_209, List.forall_mem_cons.2 ⟨subd15_3_210, List.forall_mem_cons.2 ⟨subd15_3_211, List.forall_mem_cons.2 ⟨subd15_3_212, List.forall_mem_cons.2 ⟨subd15_3_213, List.forall_mem_cons.2 ⟨subd15_3_214, List.forall_mem_cons.2 ⟨subd15_3_215, List.forall_mem_cons.2 ⟨subd15_3_216, List.forall_mem_cons.2 ⟨subd15_3_217, List.forall_mem_cons.2 ⟨subd15_3_218, List.forall_mem_cons.2 ⟨subd15_3_219, List.forall_mem_cons.2 ⟨subd15_3_220, List.forall_mem_cons.2 ⟨subd15_3_221, List.forall_mem_cons.2 ⟨subd15_3_222, List.forall_mem_cons.2 ⟨subd15_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_224 : subd15_3 [-1, -2, 0] = true := by decide +kernel
theorem subd15_3_225 : subd15_3 [-1, -2, 1] = true := by decide +kernel
theorem subd15_3_226 : subd15_3 [-1, -2, 2] = true := by decide +kernel
theorem subd15_3_227 : subd15_3 [-1, -2, 3] = true := by decide +kernel
theorem subd15_3_228 : subd15_3 [-1, -2, 4] = true := by decide +kernel
theorem subd15_3_229 : subd15_3 [-1, -2, 5] = true := by decide +kernel
theorem subd15_3_230 : subd15_3 [-1, -2, 6] = true := by decide +kernel
theorem subd15_3_231 : subd15_3 [-1, -2, 7] = true := by decide +kernel
theorem subd15_3_232 : subd15_3 [-1, -2, 8] = true := by decide +kernel
theorem subd15_3_233 : subd15_3 [-1, -1, -9] = true := by decide +kernel
theorem subd15_3_234 : subd15_3 [-1, -1, -8] = true := by decide +kernel
theorem subd15_3_235 : subd15_3 [-1, -1, -7] = true := by decide +kernel
theorem subd15_3_236 : subd15_3 [-1, -1, -6] = true := by decide +kernel
theorem subd15_3_237 : subd15_3 [-1, -1, -5] = true := by decide +kernel
theorem subd15_3_238 : subd15_3 [-1, -1, -4] = true := by decide +kernel
theorem subd15_3_239 : subd15_3 [-1, -1, -3] = true := by decide +kernel
theorem subd15_3_240 : subd15_3 [-1, -1, -2] = true := by decide +kernel
theorem subd15_3_241 : subd15_3 [-1, -1, -1] = true := by decide +kernel
theorem subd15_3_242 : subd15_3 [-1, -1, 0] = true := by decide +kernel
theorem subd15_3_243 : subd15_3 [-1, -1, 1] = true := by decide +kernel
theorem subd15_3_244 : subd15_3 [-1, -1, 2] = true := by decide +kernel
theorem subd15_3_245 : subd15_3 [-1, -1, 3] = true := by decide +kernel
theorem subd15_3_246 : subd15_3 [-1, -1, 4] = true := by decide +kernel
theorem subd15_3_247 : subd15_3 [-1, -1, 5] = true := by decide +kernel
theorem subd15_3_248 : subd15_3 [-1, -1, 6] = true := by decide +kernel
theorem subd15_3_249 : subd15_3 [-1, -1, 7] = true := by decide +kernel
theorem subd15_3_250 : subd15_3 [-1, -1, 8] = true := by decide +kernel
theorem subd15_3_251 : subd15_3 [-1, 0, -9] = true := by decide +kernel
theorem subd15_3_252 : subd15_3 [-1, 0, -8] = true := by decide +kernel
theorem subd15_3_253 : subd15_3 [-1, 0, -7] = true := by decide +kernel
theorem subd15_3_254 : subd15_3 [-1, 0, -6] = true := by decide +kernel
theorem subd15_3_255 : subd15_3 [-1, 0, -5] = true := by decide +kernel
theorem sbd15_3_7 : ∀ q ∈ blkd15_3_7, subd15_3 q = true := by
  unfold blkd15_3_7
  exact List.forall_mem_cons.2 ⟨subd15_3_224, List.forall_mem_cons.2 ⟨subd15_3_225, List.forall_mem_cons.2 ⟨subd15_3_226, List.forall_mem_cons.2 ⟨subd15_3_227, List.forall_mem_cons.2 ⟨subd15_3_228, List.forall_mem_cons.2 ⟨subd15_3_229, List.forall_mem_cons.2 ⟨subd15_3_230, List.forall_mem_cons.2 ⟨subd15_3_231, List.forall_mem_cons.2 ⟨subd15_3_232, List.forall_mem_cons.2 ⟨subd15_3_233, List.forall_mem_cons.2 ⟨subd15_3_234, List.forall_mem_cons.2 ⟨subd15_3_235, List.forall_mem_cons.2 ⟨subd15_3_236, List.forall_mem_cons.2 ⟨subd15_3_237, List.forall_mem_cons.2 ⟨subd15_3_238, List.forall_mem_cons.2 ⟨subd15_3_239, List.forall_mem_cons.2 ⟨subd15_3_240, List.forall_mem_cons.2 ⟨subd15_3_241, List.forall_mem_cons.2 ⟨subd15_3_242, List.forall_mem_cons.2 ⟨subd15_3_243, List.forall_mem_cons.2 ⟨subd15_3_244, List.forall_mem_cons.2 ⟨subd15_3_245, List.forall_mem_cons.2 ⟨subd15_3_246, List.forall_mem_cons.2 ⟨subd15_3_247, List.forall_mem_cons.2 ⟨subd15_3_248, List.forall_mem_cons.2 ⟨subd15_3_249, List.forall_mem_cons.2 ⟨subd15_3_250, List.forall_mem_cons.2 ⟨subd15_3_251, List.forall_mem_cons.2 ⟨subd15_3_252, List.forall_mem_cons.2 ⟨subd15_3_253, List.forall_mem_cons.2 ⟨subd15_3_254, List.forall_mem_cons.2 ⟨subd15_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_256 : subd15_3 [-1, 0, -4] = true := by decide +kernel
theorem subd15_3_257 : subd15_3 [-1, 0, -3] = true := by decide +kernel
theorem subd15_3_258 : subd15_3 [-1, 0, -2] = true := by decide +kernel
theorem subd15_3_259 : subd15_3 [-1, 0, -1] = true := by decide +kernel
theorem subd15_3_260 : subd15_3 [-1, 0, 0] = true := by decide +kernel
theorem subd15_3_261 : subd15_3 [-1, 0, 1] = true := by decide +kernel
theorem subd15_3_262 : subd15_3 [-1, 0, 2] = true := by decide +kernel
theorem subd15_3_263 : subd15_3 [-1, 0, 3] = true := by decide +kernel
theorem subd15_3_264 : subd15_3 [-1, 0, 4] = true := by decide +kernel
theorem subd15_3_265 : subd15_3 [-1, 0, 5] = true := by decide +kernel
theorem subd15_3_266 : subd15_3 [-1, 0, 6] = true := by decide +kernel
theorem subd15_3_267 : subd15_3 [-1, 0, 7] = true := by decide +kernel
theorem subd15_3_268 : subd15_3 [-1, 1, -9] = true := by decide +kernel
theorem subd15_3_269 : subd15_3 [-1, 1, -8] = true := by decide +kernel
theorem subd15_3_270 : subd15_3 [-1, 1, -7] = true := by decide +kernel
theorem subd15_3_271 : subd15_3 [-1, 1, -6] = true := by decide +kernel
theorem subd15_3_272 : subd15_3 [-1, 1, -5] = true := by decide +kernel
theorem subd15_3_273 : subd15_3 [-1, 1, -4] = true := by decide +kernel
theorem subd15_3_274 : subd15_3 [-1, 1, -3] = true := by decide +kernel
theorem subd15_3_275 : subd15_3 [-1, 1, -2] = true := by decide +kernel
theorem subd15_3_276 : subd15_3 [-1, 1, -1] = true := by decide +kernel
theorem subd15_3_277 : subd15_3 [-1, 1, 0] = true := by decide +kernel
theorem subd15_3_278 : subd15_3 [-1, 1, 1] = true := by decide +kernel
theorem subd15_3_279 : subd15_3 [-1, 1, 2] = true := by decide +kernel
theorem subd15_3_280 : subd15_3 [-1, 1, 3] = true := by decide +kernel
theorem subd15_3_281 : subd15_3 [-1, 1, 4] = true := by decide +kernel
theorem subd15_3_282 : subd15_3 [-1, 1, 5] = true := by decide +kernel
theorem subd15_3_283 : subd15_3 [-1, 1, 6] = true := by decide +kernel
theorem subd15_3_284 : subd15_3 [-1, 1, 7] = true := by decide +kernel
theorem subd15_3_285 : subd15_3 [-1, 2, -9] = true := by decide +kernel
theorem subd15_3_286 : subd15_3 [-1, 2, -8] = true := by decide +kernel
theorem subd15_3_287 : subd15_3 [-1, 2, -7] = true := by decide +kernel
theorem sbd15_3_8 : ∀ q ∈ blkd15_3_8, subd15_3 q = true := by
  unfold blkd15_3_8
  exact List.forall_mem_cons.2 ⟨subd15_3_256, List.forall_mem_cons.2 ⟨subd15_3_257, List.forall_mem_cons.2 ⟨subd15_3_258, List.forall_mem_cons.2 ⟨subd15_3_259, List.forall_mem_cons.2 ⟨subd15_3_260, List.forall_mem_cons.2 ⟨subd15_3_261, List.forall_mem_cons.2 ⟨subd15_3_262, List.forall_mem_cons.2 ⟨subd15_3_263, List.forall_mem_cons.2 ⟨subd15_3_264, List.forall_mem_cons.2 ⟨subd15_3_265, List.forall_mem_cons.2 ⟨subd15_3_266, List.forall_mem_cons.2 ⟨subd15_3_267, List.forall_mem_cons.2 ⟨subd15_3_268, List.forall_mem_cons.2 ⟨subd15_3_269, List.forall_mem_cons.2 ⟨subd15_3_270, List.forall_mem_cons.2 ⟨subd15_3_271, List.forall_mem_cons.2 ⟨subd15_3_272, List.forall_mem_cons.2 ⟨subd15_3_273, List.forall_mem_cons.2 ⟨subd15_3_274, List.forall_mem_cons.2 ⟨subd15_3_275, List.forall_mem_cons.2 ⟨subd15_3_276, List.forall_mem_cons.2 ⟨subd15_3_277, List.forall_mem_cons.2 ⟨subd15_3_278, List.forall_mem_cons.2 ⟨subd15_3_279, List.forall_mem_cons.2 ⟨subd15_3_280, List.forall_mem_cons.2 ⟨subd15_3_281, List.forall_mem_cons.2 ⟨subd15_3_282, List.forall_mem_cons.2 ⟨subd15_3_283, List.forall_mem_cons.2 ⟨subd15_3_284, List.forall_mem_cons.2 ⟨subd15_3_285, List.forall_mem_cons.2 ⟨subd15_3_286, List.forall_mem_cons.2 ⟨subd15_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_288 : subd15_3 [-1, 2, -6] = true := by decide +kernel
theorem subd15_3_289 : subd15_3 [-1, 2, -5] = true := by decide +kernel
theorem subd15_3_290 : subd15_3 [-1, 2, -4] = true := by decide +kernel
theorem subd15_3_291 : subd15_3 [-1, 2, -3] = true := by decide +kernel
theorem subd15_3_292 : subd15_3 [-1, 2, -2] = true := by decide +kernel
theorem subd15_3_293 : subd15_3 [-1, 2, -1] = true := by decide +kernel
theorem subd15_3_294 : subd15_3 [-1, 2, 0] = true := by decide +kernel
theorem subd15_3_295 : subd15_3 [-1, 2, 1] = true := by decide +kernel
theorem subd15_3_296 : subd15_3 [-1, 2, 2] = true := by decide +kernel
theorem subd15_3_297 : subd15_3 [-1, 2, 3] = true := by decide +kernel
theorem subd15_3_298 : subd15_3 [-1, 2, 4] = true := by decide +kernel
theorem subd15_3_299 : subd15_3 [-1, 2, 5] = true := by decide +kernel
theorem subd15_3_300 : subd15_3 [-1, 2, 6] = true := by decide +kernel
theorem subd15_3_301 : subd15_3 [-1, 3, -9] = true := by decide +kernel
theorem subd15_3_302 : subd15_3 [-1, 3, -8] = true := by decide +kernel
theorem subd15_3_303 : subd15_3 [-1, 3, -7] = true := by decide +kernel
theorem subd15_3_304 : subd15_3 [-1, 3, -6] = true := by decide +kernel
theorem subd15_3_305 : subd15_3 [-1, 3, -5] = true := by decide +kernel
theorem subd15_3_306 : subd15_3 [-1, 3, -4] = true := by decide +kernel
theorem subd15_3_307 : subd15_3 [-1, 3, -3] = true := by decide +kernel
theorem subd15_3_308 : subd15_3 [-1, 3, -2] = true := by decide +kernel
theorem subd15_3_309 : subd15_3 [-1, 3, -1] = true := by decide +kernel
theorem subd15_3_310 : subd15_3 [-1, 3, 0] = true := by decide +kernel
theorem subd15_3_311 : subd15_3 [-1, 3, 1] = true := by decide +kernel
theorem subd15_3_312 : subd15_3 [-1, 3, 2] = true := by decide +kernel
theorem subd15_3_313 : subd15_3 [-1, 3, 3] = true := by decide +kernel
theorem subd15_3_314 : subd15_3 [-1, 3, 4] = true := by decide +kernel
theorem subd15_3_315 : subd15_3 [-1, 3, 5] = true := by decide +kernel
theorem subd15_3_316 : subd15_3 [-1, 4] = true := by decide +kernel
theorem subd15_3_317 : subd15_3 [-1, 5] = true := by decide +kernel
theorem subd15_3_318 : subd15_3 [0, -6] = true := by decide +kernel
theorem subd15_3_319 : subd15_3 [0, -5] = true := by decide +kernel
theorem sbd15_3_9 : ∀ q ∈ blkd15_3_9, subd15_3 q = true := by
  unfold blkd15_3_9
  exact List.forall_mem_cons.2 ⟨subd15_3_288, List.forall_mem_cons.2 ⟨subd15_3_289, List.forall_mem_cons.2 ⟨subd15_3_290, List.forall_mem_cons.2 ⟨subd15_3_291, List.forall_mem_cons.2 ⟨subd15_3_292, List.forall_mem_cons.2 ⟨subd15_3_293, List.forall_mem_cons.2 ⟨subd15_3_294, List.forall_mem_cons.2 ⟨subd15_3_295, List.forall_mem_cons.2 ⟨subd15_3_296, List.forall_mem_cons.2 ⟨subd15_3_297, List.forall_mem_cons.2 ⟨subd15_3_298, List.forall_mem_cons.2 ⟨subd15_3_299, List.forall_mem_cons.2 ⟨subd15_3_300, List.forall_mem_cons.2 ⟨subd15_3_301, List.forall_mem_cons.2 ⟨subd15_3_302, List.forall_mem_cons.2 ⟨subd15_3_303, List.forall_mem_cons.2 ⟨subd15_3_304, List.forall_mem_cons.2 ⟨subd15_3_305, List.forall_mem_cons.2 ⟨subd15_3_306, List.forall_mem_cons.2 ⟨subd15_3_307, List.forall_mem_cons.2 ⟨subd15_3_308, List.forall_mem_cons.2 ⟨subd15_3_309, List.forall_mem_cons.2 ⟨subd15_3_310, List.forall_mem_cons.2 ⟨subd15_3_311, List.forall_mem_cons.2 ⟨subd15_3_312, List.forall_mem_cons.2 ⟨subd15_3_313, List.forall_mem_cons.2 ⟨subd15_3_314, List.forall_mem_cons.2 ⟨subd15_3_315, List.forall_mem_cons.2 ⟨subd15_3_316, List.forall_mem_cons.2 ⟨subd15_3_317, List.forall_mem_cons.2 ⟨subd15_3_318, List.forall_mem_cons.2 ⟨subd15_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_320 : subd15_3 [0, -4, -5] = true := by decide +kernel
theorem subd15_3_321 : subd15_3 [0, -4, -4] = true := by decide +kernel
theorem subd15_3_322 : subd15_3 [0, -4, -3] = true := by decide +kernel
theorem subd15_3_323 : subd15_3 [0, -4, -2] = true := by decide +kernel
theorem subd15_3_324 : subd15_3 [0, -4, -1] = true := by decide +kernel
theorem subd15_3_325 : subd15_3 [0, -4, 0] = true := by decide +kernel
theorem subd15_3_326 : subd15_3 [0, -4, 1] = true := by decide +kernel
theorem subd15_3_327 : subd15_3 [0, -4, 2] = true := by decide +kernel
theorem subd15_3_328 : subd15_3 [0, -4, 3] = true := by decide +kernel
theorem subd15_3_329 : subd15_3 [0, -4, 4] = true := by decide +kernel
theorem subd15_3_330 : subd15_3 [0, -4, 5] = true := by decide +kernel
theorem subd15_3_331 : subd15_3 [0, -4, 6] = true := by decide +kernel
theorem subd15_3_332 : subd15_3 [0, -4, 7] = true := by decide +kernel
theorem subd15_3_333 : subd15_3 [0, -3, -7] = true := by decide +kernel
theorem subd15_3_334 : subd15_3 [0, -3, -6] = true := by decide +kernel
theorem subd15_3_335 : subd15_3 [0, -3, -5] = true := by decide +kernel
theorem subd15_3_336 : subd15_3 [0, -3, -4] = true := by decide +kernel
theorem subd15_3_337 : subd15_3 [0, -3, -3] = true := by decide +kernel
theorem subd15_3_338 : subd15_3 [0, -3, -2] = true := by decide +kernel
theorem subd15_3_339 : subd15_3 [0, -3, -1] = true := by decide +kernel
theorem subd15_3_340 : subd15_3 [0, -3, 0] = true := by decide +kernel
theorem subd15_3_341 : subd15_3 [0, -3, 1] = true := by decide +kernel
theorem subd15_3_342 : subd15_3 [0, -3, 2] = true := by decide +kernel
theorem subd15_3_343 : subd15_3 [0, -3, 3] = true := by decide +kernel
theorem subd15_3_344 : subd15_3 [0, -3, 4] = true := by decide +kernel
theorem subd15_3_345 : subd15_3 [0, -3, 5] = true := by decide +kernel
theorem subd15_3_346 : subd15_3 [0, -3, 6] = true := by decide +kernel
theorem subd15_3_347 : subd15_3 [0, -3, 7] = true := by decide +kernel
theorem subd15_3_348 : subd15_3 [0, -3, 8] = true := by decide +kernel
theorem subd15_3_349 : subd15_3 [0, -2, -8] = true := by decide +kernel
theorem subd15_3_350 : subd15_3 [0, -2, -7] = true := by decide +kernel
theorem subd15_3_351 : subd15_3 [0, -2, -6] = true := by decide +kernel
theorem sbd15_3_10 : ∀ q ∈ blkd15_3_10, subd15_3 q = true := by
  unfold blkd15_3_10
  exact List.forall_mem_cons.2 ⟨subd15_3_320, List.forall_mem_cons.2 ⟨subd15_3_321, List.forall_mem_cons.2 ⟨subd15_3_322, List.forall_mem_cons.2 ⟨subd15_3_323, List.forall_mem_cons.2 ⟨subd15_3_324, List.forall_mem_cons.2 ⟨subd15_3_325, List.forall_mem_cons.2 ⟨subd15_3_326, List.forall_mem_cons.2 ⟨subd15_3_327, List.forall_mem_cons.2 ⟨subd15_3_328, List.forall_mem_cons.2 ⟨subd15_3_329, List.forall_mem_cons.2 ⟨subd15_3_330, List.forall_mem_cons.2 ⟨subd15_3_331, List.forall_mem_cons.2 ⟨subd15_3_332, List.forall_mem_cons.2 ⟨subd15_3_333, List.forall_mem_cons.2 ⟨subd15_3_334, List.forall_mem_cons.2 ⟨subd15_3_335, List.forall_mem_cons.2 ⟨subd15_3_336, List.forall_mem_cons.2 ⟨subd15_3_337, List.forall_mem_cons.2 ⟨subd15_3_338, List.forall_mem_cons.2 ⟨subd15_3_339, List.forall_mem_cons.2 ⟨subd15_3_340, List.forall_mem_cons.2 ⟨subd15_3_341, List.forall_mem_cons.2 ⟨subd15_3_342, List.forall_mem_cons.2 ⟨subd15_3_343, List.forall_mem_cons.2 ⟨subd15_3_344, List.forall_mem_cons.2 ⟨subd15_3_345, List.forall_mem_cons.2 ⟨subd15_3_346, List.forall_mem_cons.2 ⟨subd15_3_347, List.forall_mem_cons.2 ⟨subd15_3_348, List.forall_mem_cons.2 ⟨subd15_3_349, List.forall_mem_cons.2 ⟨subd15_3_350, List.forall_mem_cons.2 ⟨subd15_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_3_352 : subd15_3 [0, -2, -5] = true := by decide +kernel
theorem subd15_3_353 : subd15_3 [0, -2, -4] = true := by decide +kernel
theorem subd15_3_354 : subd15_3 [0, -2, -3] = true := by decide +kernel
theorem subd15_3_355 : subd15_3 [0, -2, -2] = true := by decide +kernel
theorem subd15_3_356 : subd15_3 [0, -2, -1] = true := by decide +kernel
theorem subd15_3_357 : subd15_3 [0, -2, 0] = true := by decide +kernel
theorem subd15_3_358 : subd15_3 [0, -2, 1] = true := by decide +kernel
theorem subd15_3_359 : subd15_3 [0, -2, 2] = true := by decide +kernel
theorem subd15_3_360 : subd15_3 [0, -2, 3] = true := by decide +kernel
theorem subd15_3_361 : subd15_3 [0, -2, 4] = true := by decide +kernel
theorem subd15_3_362 : subd15_3 [0, -2, 5] = true := by decide +kernel
theorem subd15_3_363 : subd15_3 [0, -2, 6] = true := by decide +kernel
theorem subd15_3_364 : subd15_3 [0, -2, 7] = true := by decide +kernel
theorem subd15_3_365 : subd15_3 [0, -2, 8] = true := by decide +kernel
theorem subd15_3_366 : subd15_3 [0, -1, -9] = true := by decide +kernel
theorem subd15_3_367 : subd15_3 [0, -1, -8] = true := by decide +kernel
theorem subd15_3_368 : subd15_3 [0, -1, -7] = true := by decide +kernel
theorem subd15_3_369 : subd15_3 [0, -1, -6] = true := by decide +kernel
theorem subd15_3_370 : subd15_3 [0, -1, -5] = true := by decide +kernel
theorem subd15_3_371 : subd15_3 [0, -1, -4] = true := by decide +kernel
theorem subd15_3_372 : subd15_3 [0, -1, -3] = true := by decide +kernel
theorem subd15_3_373 : subd15_3 [0, -1, -2] = true := by decide +kernel
theorem subd15_3_374 : subd15_3 [0, -1, -1] = true := by decide +kernel
theorem subd15_3_375 : subd15_3 [0, -1, 0] = true := by decide +kernel
theorem subd15_3_376 : subd15_3 [0, -1, 1] = true := by decide +kernel
theorem subd15_3_377 : subd15_3 [0, -1, 2] = true := by decide +kernel
theorem subd15_3_378 : subd15_3 [0, -1, 3] = true := by decide +kernel
theorem subd15_3_379 : subd15_3 [0, -1, 4] = true := by decide +kernel
theorem subd15_3_380 : subd15_3 [0, -1, 5] = true := by decide +kernel
theorem subd15_3_381 : subd15_3 [0, -1, 6] = true := by decide +kernel
theorem subd15_3_382 : subd15_3 [0, -1, 7] = true := by decide +kernel
theorem subd15_3_383 : subd15_3 [0, -1, 8] = true := by decide +kernel
theorem sbd15_3_11 : ∀ q ∈ blkd15_3_11, subd15_3 q = true := by
  unfold blkd15_3_11
  exact List.forall_mem_cons.2 ⟨subd15_3_352, List.forall_mem_cons.2 ⟨subd15_3_353, List.forall_mem_cons.2 ⟨subd15_3_354, List.forall_mem_cons.2 ⟨subd15_3_355, List.forall_mem_cons.2 ⟨subd15_3_356, List.forall_mem_cons.2 ⟨subd15_3_357, List.forall_mem_cons.2 ⟨subd15_3_358, List.forall_mem_cons.2 ⟨subd15_3_359, List.forall_mem_cons.2 ⟨subd15_3_360, List.forall_mem_cons.2 ⟨subd15_3_361, List.forall_mem_cons.2 ⟨subd15_3_362, List.forall_mem_cons.2 ⟨subd15_3_363, List.forall_mem_cons.2 ⟨subd15_3_364, List.forall_mem_cons.2 ⟨subd15_3_365, List.forall_mem_cons.2 ⟨subd15_3_366, List.forall_mem_cons.2 ⟨subd15_3_367, List.forall_mem_cons.2 ⟨subd15_3_368, List.forall_mem_cons.2 ⟨subd15_3_369, List.forall_mem_cons.2 ⟨subd15_3_370, List.forall_mem_cons.2 ⟨subd15_3_371, List.forall_mem_cons.2 ⟨subd15_3_372, List.forall_mem_cons.2 ⟨subd15_3_373, List.forall_mem_cons.2 ⟨subd15_3_374, List.forall_mem_cons.2 ⟨subd15_3_375, List.forall_mem_cons.2 ⟨subd15_3_376, List.forall_mem_cons.2 ⟨subd15_3_377, List.forall_mem_cons.2 ⟨subd15_3_378, List.forall_mem_cons.2 ⟨subd15_3_379, List.forall_mem_cons.2 ⟨subd15_3_380, List.forall_mem_cons.2 ⟨subd15_3_381, List.forall_mem_cons.2 ⟨subd15_3_382, List.forall_mem_cons.2 ⟨subd15_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
