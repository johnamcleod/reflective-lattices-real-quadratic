import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-4] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-3, -2] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-3, -1] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-3, 0] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-3, 1, -8] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-3, 1, -7] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-3, 1, -6] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-3, 1, -5] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [-3, 1, -4] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [-3, 1, -3] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [-3, 1, -2] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [-3, 1, -1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [-3, 1, 0] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [-3, 1, 1] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [-3, 1, 2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [-3, 1, 3] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [-3, 1, 4] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [-3, 1, 5] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [-3, 1, 6] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [-3, 2, -8] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [-3, 2, -7] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [-3, 2, -6] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [-3, 2, -5] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [-3, 2, -4] = true := by decide +kernel
theorem subd10_0_24 : subd10_0 [-3, 2, -3] = true := by decide +kernel
theorem subd10_0_25 : subd10_0 [-3, 2, -2] = true := by decide +kernel
theorem subd10_0_26 : subd10_0 [-3, 2, -1] = true := by decide +kernel
theorem subd10_0_27 : subd10_0 [-3, 2, 0] = true := by decide +kernel
theorem subd10_0_28 : subd10_0 [-3, 2, 1] = true := by decide +kernel
theorem subd10_0_29 : subd10_0 [-3, 2, 2] = true := by decide +kernel
theorem subd10_0_30 : subd10_0 [-3, 2, 3] = true := by decide +kernel
theorem subd10_0_31 : subd10_0 [-3, 2, 4] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_cons.2 ⟨subd10_0_24, List.forall_mem_cons.2 ⟨subd10_0_25, List.forall_mem_cons.2 ⟨subd10_0_26, List.forall_mem_cons.2 ⟨subd10_0_27, List.forall_mem_cons.2 ⟨subd10_0_28, List.forall_mem_cons.2 ⟨subd10_0_29, List.forall_mem_cons.2 ⟨subd10_0_30, List.forall_mem_cons.2 ⟨subd10_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_32 : subd10_0 [-3, 2, 5] = true := by decide +kernel
theorem subd10_0_33 : subd10_0 [-3, 3] = true := by decide +kernel
theorem subd10_0_34 : subd10_0 [-3, 4] = true := by decide +kernel
theorem subd10_0_35 : subd10_0 [-2, -4] = true := by decide +kernel
theorem subd10_0_36 : subd10_0 [-2, -3] = true := by decide +kernel
theorem subd10_0_37 : subd10_0 [-2, -2] = true := by decide +kernel
theorem subd10_0_38 : subd10_0 [-2, -1, -8] = true := by decide +kernel
theorem subd10_0_39 : subd10_0 [-2, -1, -7] = true := by decide +kernel
theorem subd10_0_40 : subd10_0 [-2, -1, -6] = true := by decide +kernel
theorem subd10_0_41 : subd10_0 [-2, -1, -5] = true := by decide +kernel
theorem subd10_0_42 : subd10_0 [-2, -1, -4] = true := by decide +kernel
theorem subd10_0_43 : subd10_0 [-2, -1, -3] = true := by decide +kernel
theorem subd10_0_44 : subd10_0 [-2, -1, -2] = true := by decide +kernel
theorem subd10_0_45 : subd10_0 [-2, -1, -1] = true := by decide +kernel
theorem subd10_0_46 : subd10_0 [-2, -1, 0] = true := by decide +kernel
theorem subd10_0_47 : subd10_0 [-2, -1, 1] = true := by decide +kernel
theorem subd10_0_48 : subd10_0 [-2, -1, 2] = true := by decide +kernel
theorem subd10_0_49 : subd10_0 [-2, -1, 3] = true := by decide +kernel
theorem subd10_0_50 : subd10_0 [-2, -1, 4] = true := by decide +kernel
theorem subd10_0_51 : subd10_0 [-2, -1, 5] = true := by decide +kernel
theorem subd10_0_52 : subd10_0 [-2, -1, 6] = true := by decide +kernel
theorem subd10_0_53 : subd10_0 [-2, -1, 7] = true := by decide +kernel
theorem subd10_0_54 : subd10_0 [-2, 0, -9] = true := by decide +kernel
theorem subd10_0_55 : subd10_0 [-2, 0, -8] = true := by decide +kernel
theorem subd10_0_56 : subd10_0 [-2, 0, -7] = true := by decide +kernel
theorem subd10_0_57 : subd10_0 [-2, 0, -6] = true := by decide +kernel
theorem subd10_0_58 : subd10_0 [-2, 0, -5] = true := by decide +kernel
theorem subd10_0_59 : subd10_0 [-2, 0, -4] = true := by decide +kernel
theorem subd10_0_60 : subd10_0 [-2, 0, -3] = true := by decide +kernel
theorem subd10_0_61 : subd10_0 [-2, 0, -2] = true := by decide +kernel
theorem subd10_0_62 : subd10_0 [-2, 0, -1] = true := by decide +kernel
theorem subd10_0_63 : subd10_0 [-2, 0, 0] = true := by decide +kernel
theorem sbd10_0_1 : ∀ q ∈ blkd10_0_1, subd10_0 q = true := by
  unfold blkd10_0_1
  exact List.forall_mem_cons.2 ⟨subd10_0_32, List.forall_mem_cons.2 ⟨subd10_0_33, List.forall_mem_cons.2 ⟨subd10_0_34, List.forall_mem_cons.2 ⟨subd10_0_35, List.forall_mem_cons.2 ⟨subd10_0_36, List.forall_mem_cons.2 ⟨subd10_0_37, List.forall_mem_cons.2 ⟨subd10_0_38, List.forall_mem_cons.2 ⟨subd10_0_39, List.forall_mem_cons.2 ⟨subd10_0_40, List.forall_mem_cons.2 ⟨subd10_0_41, List.forall_mem_cons.2 ⟨subd10_0_42, List.forall_mem_cons.2 ⟨subd10_0_43, List.forall_mem_cons.2 ⟨subd10_0_44, List.forall_mem_cons.2 ⟨subd10_0_45, List.forall_mem_cons.2 ⟨subd10_0_46, List.forall_mem_cons.2 ⟨subd10_0_47, List.forall_mem_cons.2 ⟨subd10_0_48, List.forall_mem_cons.2 ⟨subd10_0_49, List.forall_mem_cons.2 ⟨subd10_0_50, List.forall_mem_cons.2 ⟨subd10_0_51, List.forall_mem_cons.2 ⟨subd10_0_52, List.forall_mem_cons.2 ⟨subd10_0_53, List.forall_mem_cons.2 ⟨subd10_0_54, List.forall_mem_cons.2 ⟨subd10_0_55, List.forall_mem_cons.2 ⟨subd10_0_56, List.forall_mem_cons.2 ⟨subd10_0_57, List.forall_mem_cons.2 ⟨subd10_0_58, List.forall_mem_cons.2 ⟨subd10_0_59, List.forall_mem_cons.2 ⟨subd10_0_60, List.forall_mem_cons.2 ⟨subd10_0_61, List.forall_mem_cons.2 ⟨subd10_0_62, List.forall_mem_cons.2 ⟨subd10_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_64 : subd10_0 [-2, 0, 1] = true := by decide +kernel
theorem subd10_0_65 : subd10_0 [-2, 0, 2] = true := by decide +kernel
theorem subd10_0_66 : subd10_0 [-2, 0, 3] = true := by decide +kernel
theorem subd10_0_67 : subd10_0 [-2, 0, 4] = true := by decide +kernel
theorem subd10_0_68 : subd10_0 [-2, 0, 5] = true := by decide +kernel
theorem subd10_0_69 : subd10_0 [-2, 0, 6] = true := by decide +kernel
theorem subd10_0_70 : subd10_0 [-2, 0, 7] = true := by decide +kernel
theorem subd10_0_71 : subd10_0 [-2, 0, 8] = true := by decide +kernel
theorem subd10_0_72 : subd10_0 [-2, 1, -10] = true := by decide +kernel
theorem subd10_0_73 : subd10_0 [-2, 1, -9] = true := by decide +kernel
theorem subd10_0_74 : subd10_0 [-2, 1, -8] = true := by decide +kernel
theorem subd10_0_75 : subd10_0 [-2, 1, -7] = true := by decide +kernel
theorem subd10_0_76 : subd10_0 [-2, 1, -6] = true := by decide +kernel
theorem subd10_0_77 : subd10_0 [-2, 1, -5] = true := by decide +kernel
theorem subd10_0_78 : subd10_0 [-2, 1, -4] = true := by decide +kernel
theorem subd10_0_79 : subd10_0 [-2, 1, -3] = true := by decide +kernel
theorem subd10_0_80 : subd10_0 [-2, 1, -2] = true := by decide +kernel
theorem subd10_0_81 : subd10_0 [-2, 1, -1] = true := by decide +kernel
theorem subd10_0_82 : subd10_0 [-2, 1, 0] = true := by decide +kernel
theorem subd10_0_83 : subd10_0 [-2, 1, 1] = true := by decide +kernel
theorem subd10_0_84 : subd10_0 [-2, 1, 2] = true := by decide +kernel
theorem subd10_0_85 : subd10_0 [-2, 1, 3] = true := by decide +kernel
theorem subd10_0_86 : subd10_0 [-2, 1, 4] = true := by decide +kernel
theorem subd10_0_87 : subd10_0 [-2, 1, 5] = true := by decide +kernel
theorem subd10_0_88 : subd10_0 [-2, 1, 6] = true := by decide +kernel
theorem subd10_0_89 : subd10_0 [-2, 1, 7] = true := by decide +kernel
theorem subd10_0_90 : subd10_0 [-2, 1, 8] = true := by decide +kernel
theorem subd10_0_91 : subd10_0 [-2, 2, -10] = true := by decide +kernel
theorem subd10_0_92 : subd10_0 [-2, 2, -9] = true := by decide +kernel
theorem subd10_0_93 : subd10_0 [-2, 2, -8] = true := by decide +kernel
theorem subd10_0_94 : subd10_0 [-2, 2, -7] = true := by decide +kernel
theorem subd10_0_95 : subd10_0 [-2, 2, -6] = true := by decide +kernel
theorem sbd10_0_2 : ∀ q ∈ blkd10_0_2, subd10_0 q = true := by
  unfold blkd10_0_2
  exact List.forall_mem_cons.2 ⟨subd10_0_64, List.forall_mem_cons.2 ⟨subd10_0_65, List.forall_mem_cons.2 ⟨subd10_0_66, List.forall_mem_cons.2 ⟨subd10_0_67, List.forall_mem_cons.2 ⟨subd10_0_68, List.forall_mem_cons.2 ⟨subd10_0_69, List.forall_mem_cons.2 ⟨subd10_0_70, List.forall_mem_cons.2 ⟨subd10_0_71, List.forall_mem_cons.2 ⟨subd10_0_72, List.forall_mem_cons.2 ⟨subd10_0_73, List.forall_mem_cons.2 ⟨subd10_0_74, List.forall_mem_cons.2 ⟨subd10_0_75, List.forall_mem_cons.2 ⟨subd10_0_76, List.forall_mem_cons.2 ⟨subd10_0_77, List.forall_mem_cons.2 ⟨subd10_0_78, List.forall_mem_cons.2 ⟨subd10_0_79, List.forall_mem_cons.2 ⟨subd10_0_80, List.forall_mem_cons.2 ⟨subd10_0_81, List.forall_mem_cons.2 ⟨subd10_0_82, List.forall_mem_cons.2 ⟨subd10_0_83, List.forall_mem_cons.2 ⟨subd10_0_84, List.forall_mem_cons.2 ⟨subd10_0_85, List.forall_mem_cons.2 ⟨subd10_0_86, List.forall_mem_cons.2 ⟨subd10_0_87, List.forall_mem_cons.2 ⟨subd10_0_88, List.forall_mem_cons.2 ⟨subd10_0_89, List.forall_mem_cons.2 ⟨subd10_0_90, List.forall_mem_cons.2 ⟨subd10_0_91, List.forall_mem_cons.2 ⟨subd10_0_92, List.forall_mem_cons.2 ⟨subd10_0_93, List.forall_mem_cons.2 ⟨subd10_0_94, List.forall_mem_cons.2 ⟨subd10_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_96 : subd10_0 [-2, 2, -5] = true := by decide +kernel
theorem subd10_0_97 : subd10_0 [-2, 2, -4] = true := by decide +kernel
theorem subd10_0_98 : subd10_0 [-2, 2, -3] = true := by decide +kernel
theorem subd10_0_99 : subd10_0 [-2, 2, -2] = true := by decide +kernel
theorem subd10_0_100 : subd10_0 [-2, 2, -1] = true := by decide +kernel
theorem subd10_0_101 : subd10_0 [-2, 2, 0] = true := by decide +kernel
theorem subd10_0_102 : subd10_0 [-2, 2, 1] = true := by decide +kernel
theorem subd10_0_103 : subd10_0 [-2, 2, 2] = true := by decide +kernel
theorem subd10_0_104 : subd10_0 [-2, 2, 3] = true := by decide +kernel
theorem subd10_0_105 : subd10_0 [-2, 2, 4] = true := by decide +kernel
theorem subd10_0_106 : subd10_0 [-2, 2, 5] = true := by decide +kernel
theorem subd10_0_107 : subd10_0 [-2, 2, 6] = true := by decide +kernel
theorem subd10_0_108 : subd10_0 [-2, 2, 7] = true := by decide +kernel
theorem subd10_0_109 : subd10_0 [-2, 3, -9] = true := by decide +kernel
theorem subd10_0_110 : subd10_0 [-2, 3, -8] = true := by decide +kernel
theorem subd10_0_111 : subd10_0 [-2, 3, -7] = true := by decide +kernel
theorem subd10_0_112 : subd10_0 [-2, 3, -6] = true := by decide +kernel
theorem subd10_0_113 : subd10_0 [-2, 3, -5] = true := by decide +kernel
theorem subd10_0_114 : subd10_0 [-2, 3, -4] = true := by decide +kernel
theorem subd10_0_115 : subd10_0 [-2, 3, -3] = true := by decide +kernel
theorem subd10_0_116 : subd10_0 [-2, 3, -2] = true := by decide +kernel
theorem subd10_0_117 : subd10_0 [-2, 3, -1] = true := by decide +kernel
theorem subd10_0_118 : subd10_0 [-2, 3, 0] = true := by decide +kernel
theorem subd10_0_119 : subd10_0 [-2, 3, 1] = true := by decide +kernel
theorem subd10_0_120 : subd10_0 [-2, 3, 2] = true := by decide +kernel
theorem subd10_0_121 : subd10_0 [-2, 3, 3] = true := by decide +kernel
theorem subd10_0_122 : subd10_0 [-2, 3, 4] = true := by decide +kernel
theorem subd10_0_123 : subd10_0 [-2, 3, 5] = true := by decide +kernel
theorem subd10_0_124 : subd10_0 [-2, 3, 6] = true := by decide +kernel
theorem subd10_0_125 : subd10_0 [-2, 4] = true := by decide +kernel
theorem subd10_0_126 : subd10_0 [-1, -4] = true := by decide +kernel
theorem subd10_0_127 : subd10_0 [-1, -3] = true := by decide +kernel
theorem sbd10_0_3 : ∀ q ∈ blkd10_0_3, subd10_0 q = true := by
  unfold blkd10_0_3
  exact List.forall_mem_cons.2 ⟨subd10_0_96, List.forall_mem_cons.2 ⟨subd10_0_97, List.forall_mem_cons.2 ⟨subd10_0_98, List.forall_mem_cons.2 ⟨subd10_0_99, List.forall_mem_cons.2 ⟨subd10_0_100, List.forall_mem_cons.2 ⟨subd10_0_101, List.forall_mem_cons.2 ⟨subd10_0_102, List.forall_mem_cons.2 ⟨subd10_0_103, List.forall_mem_cons.2 ⟨subd10_0_104, List.forall_mem_cons.2 ⟨subd10_0_105, List.forall_mem_cons.2 ⟨subd10_0_106, List.forall_mem_cons.2 ⟨subd10_0_107, List.forall_mem_cons.2 ⟨subd10_0_108, List.forall_mem_cons.2 ⟨subd10_0_109, List.forall_mem_cons.2 ⟨subd10_0_110, List.forall_mem_cons.2 ⟨subd10_0_111, List.forall_mem_cons.2 ⟨subd10_0_112, List.forall_mem_cons.2 ⟨subd10_0_113, List.forall_mem_cons.2 ⟨subd10_0_114, List.forall_mem_cons.2 ⟨subd10_0_115, List.forall_mem_cons.2 ⟨subd10_0_116, List.forall_mem_cons.2 ⟨subd10_0_117, List.forall_mem_cons.2 ⟨subd10_0_118, List.forall_mem_cons.2 ⟨subd10_0_119, List.forall_mem_cons.2 ⟨subd10_0_120, List.forall_mem_cons.2 ⟨subd10_0_121, List.forall_mem_cons.2 ⟨subd10_0_122, List.forall_mem_cons.2 ⟨subd10_0_123, List.forall_mem_cons.2 ⟨subd10_0_124, List.forall_mem_cons.2 ⟨subd10_0_125, List.forall_mem_cons.2 ⟨subd10_0_126, List.forall_mem_cons.2 ⟨subd10_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_128 : subd10_0 [-1, -2, -8] = true := by decide +kernel
theorem subd10_0_129 : subd10_0 [-1, -2, -7] = true := by decide +kernel
theorem subd10_0_130 : subd10_0 [-1, -2, -6] = true := by decide +kernel
theorem subd10_0_131 : subd10_0 [-1, -2, -5] = true := by decide +kernel
theorem subd10_0_132 : subd10_0 [-1, -2, -4] = true := by decide +kernel
theorem subd10_0_133 : subd10_0 [-1, -2, -3] = true := by decide +kernel
theorem subd10_0_134 : subd10_0 [-1, -2, -2] = true := by decide +kernel
theorem subd10_0_135 : subd10_0 [-1, -2, -1] = true := by decide +kernel
theorem subd10_0_136 : subd10_0 [-1, -2, 0] = true := by decide +kernel
theorem subd10_0_137 : subd10_0 [-1, -2, 1] = true := by decide +kernel
theorem subd10_0_138 : subd10_0 [-1, -2, 2] = true := by decide +kernel
theorem subd10_0_139 : subd10_0 [-1, -2, 3] = true := by decide +kernel
theorem subd10_0_140 : subd10_0 [-1, -2, 4] = true := by decide +kernel
theorem subd10_0_141 : subd10_0 [-1, -2, 5] = true := by decide +kernel
theorem subd10_0_142 : subd10_0 [-1, -2, 6] = true := by decide +kernel
theorem subd10_0_143 : subd10_0 [-1, -2, 7] = true := by decide +kernel
theorem subd10_0_144 : subd10_0 [-1, -2, 8] = true := by decide +kernel
theorem subd10_0_145 : subd10_0 [-1, -1, -10] = true := by decide +kernel
theorem subd10_0_146 : subd10_0 [-1, -1, -9] = true := by decide +kernel
theorem subd10_0_147 : subd10_0 [-1, -1, -8] = true := by decide +kernel
theorem subd10_0_148 : subd10_0 [-1, -1, -7] = true := by decide +kernel
theorem subd10_0_149 : subd10_0 [-1, -1, -6] = true := by decide +kernel
theorem subd10_0_150 : subd10_0 [-1, -1, -5] = true := by decide +kernel
theorem subd10_0_151 : subd10_0 [-1, -1, -4] = true := by decide +kernel
theorem subd10_0_152 : subd10_0 [-1, -1, -3] = true := by decide +kernel
theorem subd10_0_153 : subd10_0 [-1, -1, -2] = true := by decide +kernel
theorem subd10_0_154 : subd10_0 [-1, -1, -1] = true := by decide +kernel
theorem subd10_0_155 : subd10_0 [-1, -1, 0] = true := by decide +kernel
theorem subd10_0_156 : subd10_0 [-1, -1, 1] = true := by decide +kernel
theorem subd10_0_157 : subd10_0 [-1, -1, 2] = true := by decide +kernel
theorem subd10_0_158 : subd10_0 [-1, -1, 3] = true := by decide +kernel
theorem subd10_0_159 : subd10_0 [-1, -1, 4] = true := by decide +kernel
theorem sbd10_0_4 : ∀ q ∈ blkd10_0_4, subd10_0 q = true := by
  unfold blkd10_0_4
  exact List.forall_mem_cons.2 ⟨subd10_0_128, List.forall_mem_cons.2 ⟨subd10_0_129, List.forall_mem_cons.2 ⟨subd10_0_130, List.forall_mem_cons.2 ⟨subd10_0_131, List.forall_mem_cons.2 ⟨subd10_0_132, List.forall_mem_cons.2 ⟨subd10_0_133, List.forall_mem_cons.2 ⟨subd10_0_134, List.forall_mem_cons.2 ⟨subd10_0_135, List.forall_mem_cons.2 ⟨subd10_0_136, List.forall_mem_cons.2 ⟨subd10_0_137, List.forall_mem_cons.2 ⟨subd10_0_138, List.forall_mem_cons.2 ⟨subd10_0_139, List.forall_mem_cons.2 ⟨subd10_0_140, List.forall_mem_cons.2 ⟨subd10_0_141, List.forall_mem_cons.2 ⟨subd10_0_142, List.forall_mem_cons.2 ⟨subd10_0_143, List.forall_mem_cons.2 ⟨subd10_0_144, List.forall_mem_cons.2 ⟨subd10_0_145, List.forall_mem_cons.2 ⟨subd10_0_146, List.forall_mem_cons.2 ⟨subd10_0_147, List.forall_mem_cons.2 ⟨subd10_0_148, List.forall_mem_cons.2 ⟨subd10_0_149, List.forall_mem_cons.2 ⟨subd10_0_150, List.forall_mem_cons.2 ⟨subd10_0_151, List.forall_mem_cons.2 ⟨subd10_0_152, List.forall_mem_cons.2 ⟨subd10_0_153, List.forall_mem_cons.2 ⟨subd10_0_154, List.forall_mem_cons.2 ⟨subd10_0_155, List.forall_mem_cons.2 ⟨subd10_0_156, List.forall_mem_cons.2 ⟨subd10_0_157, List.forall_mem_cons.2 ⟨subd10_0_158, List.forall_mem_cons.2 ⟨subd10_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_160 : subd10_0 [-1, -1, 5] = true := by decide +kernel
theorem subd10_0_161 : subd10_0 [-1, -1, 6] = true := by decide +kernel
theorem subd10_0_162 : subd10_0 [-1, -1, 7] = true := by decide +kernel
theorem subd10_0_163 : subd10_0 [-1, -1, 8] = true := by decide +kernel
theorem subd10_0_164 : subd10_0 [-1, -1, 9] = true := by decide +kernel
theorem subd10_0_165 : subd10_0 [-1, 0, -10] = true := by decide +kernel
theorem subd10_0_166 : subd10_0 [-1, 0, -9] = true := by decide +kernel
theorem subd10_0_167 : subd10_0 [-1, 0, -8] = true := by decide +kernel
theorem subd10_0_168 : subd10_0 [-1, 0, -7] = true := by decide +kernel
theorem subd10_0_169 : subd10_0 [-1, 0, -6] = true := by decide +kernel
theorem subd10_0_170 : subd10_0 [-1, 0, -5] = true := by decide +kernel
theorem subd10_0_171 : subd10_0 [-1, 0, -4] = true := by decide +kernel
theorem subd10_0_172 : subd10_0 [-1, 0, -3] = true := by decide +kernel
theorem subd10_0_173 : subd10_0 [-1, 0, -2] = true := by decide +kernel
theorem subd10_0_174 : subd10_0 [-1, 0, -1] = true := by decide +kernel
theorem subd10_0_175 : subd10_0 [-1, 0, 0] = true := by decide +kernel
theorem subd10_0_176 : subd10_0 [-1, 0, 1] = true := by decide +kernel
theorem subd10_0_177 : subd10_0 [-1, 0, 2] = true := by decide +kernel
theorem subd10_0_178 : subd10_0 [-1, 0, 3] = true := by decide +kernel
theorem subd10_0_179 : subd10_0 [-1, 0, 4] = true := by decide +kernel
theorem subd10_0_180 : subd10_0 [-1, 0, 5] = true := by decide +kernel
theorem subd10_0_181 : subd10_0 [-1, 0, 6] = true := by decide +kernel
theorem subd10_0_182 : subd10_0 [-1, 0, 7] = true := by decide +kernel
theorem subd10_0_183 : subd10_0 [-1, 0, 8] = true := by decide +kernel
theorem subd10_0_184 : subd10_0 [-1, 0, 9] = true := by decide +kernel
theorem subd10_0_185 : subd10_0 [-1, 1, -11] = true := by decide +kernel
theorem subd10_0_186 : subd10_0 [-1, 1, -10] = true := by decide +kernel
theorem subd10_0_187 : subd10_0 [-1, 1, -9] = true := by decide +kernel
theorem subd10_0_188 : subd10_0 [-1, 1, -8] = true := by decide +kernel
theorem subd10_0_189 : subd10_0 [-1, 1, -7] = true := by decide +kernel
theorem subd10_0_190 : subd10_0 [-1, 1, -6] = true := by decide +kernel
theorem subd10_0_191 : subd10_0 [-1, 1, -5] = true := by decide +kernel
theorem sbd10_0_5 : ∀ q ∈ blkd10_0_5, subd10_0 q = true := by
  unfold blkd10_0_5
  exact List.forall_mem_cons.2 ⟨subd10_0_160, List.forall_mem_cons.2 ⟨subd10_0_161, List.forall_mem_cons.2 ⟨subd10_0_162, List.forall_mem_cons.2 ⟨subd10_0_163, List.forall_mem_cons.2 ⟨subd10_0_164, List.forall_mem_cons.2 ⟨subd10_0_165, List.forall_mem_cons.2 ⟨subd10_0_166, List.forall_mem_cons.2 ⟨subd10_0_167, List.forall_mem_cons.2 ⟨subd10_0_168, List.forall_mem_cons.2 ⟨subd10_0_169, List.forall_mem_cons.2 ⟨subd10_0_170, List.forall_mem_cons.2 ⟨subd10_0_171, List.forall_mem_cons.2 ⟨subd10_0_172, List.forall_mem_cons.2 ⟨subd10_0_173, List.forall_mem_cons.2 ⟨subd10_0_174, List.forall_mem_cons.2 ⟨subd10_0_175, List.forall_mem_cons.2 ⟨subd10_0_176, List.forall_mem_cons.2 ⟨subd10_0_177, List.forall_mem_cons.2 ⟨subd10_0_178, List.forall_mem_cons.2 ⟨subd10_0_179, List.forall_mem_cons.2 ⟨subd10_0_180, List.forall_mem_cons.2 ⟨subd10_0_181, List.forall_mem_cons.2 ⟨subd10_0_182, List.forall_mem_cons.2 ⟨subd10_0_183, List.forall_mem_cons.2 ⟨subd10_0_184, List.forall_mem_cons.2 ⟨subd10_0_185, List.forall_mem_cons.2 ⟨subd10_0_186, List.forall_mem_cons.2 ⟨subd10_0_187, List.forall_mem_cons.2 ⟨subd10_0_188, List.forall_mem_cons.2 ⟨subd10_0_189, List.forall_mem_cons.2 ⟨subd10_0_190, List.forall_mem_cons.2 ⟨subd10_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_192 : subd10_0 [-1, 1, -4] = true := by decide +kernel
theorem subd10_0_193 : subd10_0 [-1, 1, -3] = true := by decide +kernel
theorem subd10_0_194 : subd10_0 [-1, 1, -2] = true := by decide +kernel
theorem subd10_0_195 : subd10_0 [-1, 1, -1] = true := by decide +kernel
theorem subd10_0_196 : subd10_0 [-1, 1, 0] = true := by decide +kernel
theorem subd10_0_197 : subd10_0 [-1, 1, 1] = true := by decide +kernel
theorem subd10_0_198 : subd10_0 [-1, 1, 2] = true := by decide +kernel
theorem subd10_0_199 : subd10_0 [-1, 1, 3] = true := by decide +kernel
theorem subd10_0_200 : subd10_0 [-1, 1, 4] = true := by decide +kernel
theorem subd10_0_201 : subd10_0 [-1, 1, 5] = true := by decide +kernel
theorem subd10_0_202 : subd10_0 [-1, 1, 6] = true := by decide +kernel
theorem subd10_0_203 : subd10_0 [-1, 1, 7] = true := by decide +kernel
theorem subd10_0_204 : subd10_0 [-1, 1, 8] = true := by decide +kernel
theorem subd10_0_205 : subd10_0 [-1, 1, 9] = true := by decide +kernel
theorem subd10_0_206 : subd10_0 [-1, 2, -10] = true := by decide +kernel
theorem subd10_0_207 : subd10_0 [-1, 2, -9] = true := by decide +kernel
theorem subd10_0_208 : subd10_0 [-1, 2, -8] = true := by decide +kernel
theorem subd10_0_209 : subd10_0 [-1, 2, -7] = true := by decide +kernel
theorem subd10_0_210 : subd10_0 [-1, 2, -6] = true := by decide +kernel
theorem subd10_0_211 : subd10_0 [-1, 2, -5] = true := by decide +kernel
theorem subd10_0_212 : subd10_0 [-1, 2, -4] = true := by decide +kernel
theorem subd10_0_213 : subd10_0 [-1, 2, -3] = true := by decide +kernel
theorem subd10_0_214 : subd10_0 [-1, 2, -2] = true := by decide +kernel
theorem subd10_0_215 : subd10_0 [-1, 2, -1] = true := by decide +kernel
theorem subd10_0_216 : subd10_0 [-1, 2, 0] = true := by decide +kernel
theorem subd10_0_217 : subd10_0 [-1, 2, 1] = true := by decide +kernel
theorem subd10_0_218 : subd10_0 [-1, 2, 2] = true := by decide +kernel
theorem subd10_0_219 : subd10_0 [-1, 2, 3] = true := by decide +kernel
theorem subd10_0_220 : subd10_0 [-1, 2, 4] = true := by decide +kernel
theorem subd10_0_221 : subd10_0 [-1, 2, 5] = true := by decide +kernel
theorem subd10_0_222 : subd10_0 [-1, 2, 6] = true := by decide +kernel
theorem subd10_0_223 : subd10_0 [-1, 2, 7] = true := by decide +kernel
theorem sbd10_0_6 : ∀ q ∈ blkd10_0_6, subd10_0 q = true := by
  unfold blkd10_0_6
  exact List.forall_mem_cons.2 ⟨subd10_0_192, List.forall_mem_cons.2 ⟨subd10_0_193, List.forall_mem_cons.2 ⟨subd10_0_194, List.forall_mem_cons.2 ⟨subd10_0_195, List.forall_mem_cons.2 ⟨subd10_0_196, List.forall_mem_cons.2 ⟨subd10_0_197, List.forall_mem_cons.2 ⟨subd10_0_198, List.forall_mem_cons.2 ⟨subd10_0_199, List.forall_mem_cons.2 ⟨subd10_0_200, List.forall_mem_cons.2 ⟨subd10_0_201, List.forall_mem_cons.2 ⟨subd10_0_202, List.forall_mem_cons.2 ⟨subd10_0_203, List.forall_mem_cons.2 ⟨subd10_0_204, List.forall_mem_cons.2 ⟨subd10_0_205, List.forall_mem_cons.2 ⟨subd10_0_206, List.forall_mem_cons.2 ⟨subd10_0_207, List.forall_mem_cons.2 ⟨subd10_0_208, List.forall_mem_cons.2 ⟨subd10_0_209, List.forall_mem_cons.2 ⟨subd10_0_210, List.forall_mem_cons.2 ⟨subd10_0_211, List.forall_mem_cons.2 ⟨subd10_0_212, List.forall_mem_cons.2 ⟨subd10_0_213, List.forall_mem_cons.2 ⟨subd10_0_214, List.forall_mem_cons.2 ⟨subd10_0_215, List.forall_mem_cons.2 ⟨subd10_0_216, List.forall_mem_cons.2 ⟨subd10_0_217, List.forall_mem_cons.2 ⟨subd10_0_218, List.forall_mem_cons.2 ⟨subd10_0_219, List.forall_mem_cons.2 ⟨subd10_0_220, List.forall_mem_cons.2 ⟨subd10_0_221, List.forall_mem_cons.2 ⟨subd10_0_222, List.forall_mem_cons.2 ⟨subd10_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_224 : subd10_0 [-1, 2, 8] = true := by decide +kernel
theorem subd10_0_225 : subd10_0 [-1, 3, -9] = true := by decide +kernel
theorem subd10_0_226 : subd10_0 [-1, 3, -8] = true := by decide +kernel
theorem subd10_0_227 : subd10_0 [-1, 3, -7] = true := by decide +kernel
theorem subd10_0_228 : subd10_0 [-1, 3, -6] = true := by decide +kernel
theorem subd10_0_229 : subd10_0 [-1, 3, -5] = true := by decide +kernel
theorem subd10_0_230 : subd10_0 [-1, 3, -4] = true := by decide +kernel
theorem subd10_0_231 : subd10_0 [-1, 3, -3] = true := by decide +kernel
theorem subd10_0_232 : subd10_0 [-1, 3, -2] = true := by decide +kernel
theorem subd10_0_233 : subd10_0 [-1, 3, -1] = true := by decide +kernel
theorem subd10_0_234 : subd10_0 [-1, 3, 0] = true := by decide +kernel
theorem subd10_0_235 : subd10_0 [-1, 3, 1] = true := by decide +kernel
theorem subd10_0_236 : subd10_0 [-1, 3, 2] = true := by decide +kernel
theorem subd10_0_237 : subd10_0 [-1, 3, 3] = true := by decide +kernel
theorem subd10_0_238 : subd10_0 [-1, 3, 4] = true := by decide +kernel
theorem subd10_0_239 : subd10_0 [-1, 3, 5] = true := by decide +kernel
theorem subd10_0_240 : subd10_0 [-1, 3, 6] = true := by decide +kernel
theorem subd10_0_241 : subd10_0 [-1, 3, 7] = true := by decide +kernel
theorem subd10_0_242 : subd10_0 [-1, 4] = true := by decide +kernel
theorem subd10_0_243 : subd10_0 [0, -5] = true := by decide +kernel
theorem subd10_0_244 : subd10_0 [0, -4] = true := by decide +kernel
theorem subd10_0_245 : subd10_0 [0, -3, -7] = true := by decide +kernel
theorem subd10_0_246 : subd10_0 [0, -3, -6] = true := by decide +kernel
theorem subd10_0_247 : subd10_0 [0, -3, -5] = true := by decide +kernel
theorem subd10_0_248 : subd10_0 [0, -3, -4] = true := by decide +kernel
theorem subd10_0_249 : subd10_0 [0, -3, -3] = true := by decide +kernel
theorem subd10_0_250 : subd10_0 [0, -3, -2] = true := by decide +kernel
theorem subd10_0_251 : subd10_0 [0, -3, -1] = true := by decide +kernel
theorem subd10_0_252 : subd10_0 [0, -3, 0] = true := by decide +kernel
theorem subd10_0_253 : subd10_0 [0, -3, 1] = true := by decide +kernel
theorem subd10_0_254 : subd10_0 [0, -3, 2] = true := by decide +kernel
theorem subd10_0_255 : subd10_0 [0, -3, 3] = true := by decide +kernel
theorem sbd10_0_7 : ∀ q ∈ blkd10_0_7, subd10_0 q = true := by
  unfold blkd10_0_7
  exact List.forall_mem_cons.2 ⟨subd10_0_224, List.forall_mem_cons.2 ⟨subd10_0_225, List.forall_mem_cons.2 ⟨subd10_0_226, List.forall_mem_cons.2 ⟨subd10_0_227, List.forall_mem_cons.2 ⟨subd10_0_228, List.forall_mem_cons.2 ⟨subd10_0_229, List.forall_mem_cons.2 ⟨subd10_0_230, List.forall_mem_cons.2 ⟨subd10_0_231, List.forall_mem_cons.2 ⟨subd10_0_232, List.forall_mem_cons.2 ⟨subd10_0_233, List.forall_mem_cons.2 ⟨subd10_0_234, List.forall_mem_cons.2 ⟨subd10_0_235, List.forall_mem_cons.2 ⟨subd10_0_236, List.forall_mem_cons.2 ⟨subd10_0_237, List.forall_mem_cons.2 ⟨subd10_0_238, List.forall_mem_cons.2 ⟨subd10_0_239, List.forall_mem_cons.2 ⟨subd10_0_240, List.forall_mem_cons.2 ⟨subd10_0_241, List.forall_mem_cons.2 ⟨subd10_0_242, List.forall_mem_cons.2 ⟨subd10_0_243, List.forall_mem_cons.2 ⟨subd10_0_244, List.forall_mem_cons.2 ⟨subd10_0_245, List.forall_mem_cons.2 ⟨subd10_0_246, List.forall_mem_cons.2 ⟨subd10_0_247, List.forall_mem_cons.2 ⟨subd10_0_248, List.forall_mem_cons.2 ⟨subd10_0_249, List.forall_mem_cons.2 ⟨subd10_0_250, List.forall_mem_cons.2 ⟨subd10_0_251, List.forall_mem_cons.2 ⟨subd10_0_252, List.forall_mem_cons.2 ⟨subd10_0_253, List.forall_mem_cons.2 ⟨subd10_0_254, List.forall_mem_cons.2 ⟨subd10_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_256 : subd10_0 [0, -3, 4] = true := by decide +kernel
theorem subd10_0_257 : subd10_0 [0, -3, 5] = true := by decide +kernel
theorem subd10_0_258 : subd10_0 [0, -3, 6] = true := by decide +kernel
theorem subd10_0_259 : subd10_0 [0, -3, 7] = true := by decide +kernel
theorem subd10_0_260 : subd10_0 [0, -3, 8] = true := by decide +kernel
theorem subd10_0_261 : subd10_0 [0, -2, -9] = true := by decide +kernel
theorem subd10_0_262 : subd10_0 [0, -2, -8] = true := by decide +kernel
theorem subd10_0_263 : subd10_0 [0, -2, -7] = true := by decide +kernel
theorem subd10_0_264 : subd10_0 [0, -2, -6] = true := by decide +kernel
theorem subd10_0_265 : subd10_0 [0, -2, -5] = true := by decide +kernel
theorem subd10_0_266 : subd10_0 [0, -2, -4] = true := by decide +kernel
theorem subd10_0_267 : subd10_0 [0, -2, -3] = true := by decide +kernel
theorem subd10_0_268 : subd10_0 [0, -2, -2] = true := by decide +kernel
theorem subd10_0_269 : subd10_0 [0, -2, -1] = true := by decide +kernel
theorem subd10_0_270 : subd10_0 [0, -2, 0] = true := by decide +kernel
theorem subd10_0_271 : subd10_0 [0, -2, 1] = true := by decide +kernel
theorem subd10_0_272 : subd10_0 [0, -2, 2] = true := by decide +kernel
theorem subd10_0_273 : subd10_0 [0, -2, 3] = true := by decide +kernel
theorem subd10_0_274 : subd10_0 [0, -2, 4] = true := by decide +kernel
theorem subd10_0_275 : subd10_0 [0, -2, 5] = true := by decide +kernel
theorem subd10_0_276 : subd10_0 [0, -2, 6] = true := by decide +kernel
theorem subd10_0_277 : subd10_0 [0, -2, 7] = true := by decide +kernel
theorem subd10_0_278 : subd10_0 [0, -2, 8] = true := by decide +kernel
theorem subd10_0_279 : subd10_0 [0, -2, 9] = true := by decide +kernel
theorem subd10_0_280 : subd10_0 [0, -1, -10] = true := by decide +kernel
theorem subd10_0_281 : subd10_0 [0, -1, -9] = true := by decide +kernel
theorem subd10_0_282 : subd10_0 [0, -1, -8] = true := by decide +kernel
theorem subd10_0_283 : subd10_0 [0, -1, -7] = true := by decide +kernel
theorem subd10_0_284 : subd10_0 [0, -1, -6] = true := by decide +kernel
theorem subd10_0_285 : subd10_0 [0, -1, -5] = true := by decide +kernel
theorem subd10_0_286 : subd10_0 [0, -1, -4] = true := by decide +kernel
theorem subd10_0_287 : subd10_0 [0, -1, -3] = true := by decide +kernel
theorem sbd10_0_8 : ∀ q ∈ blkd10_0_8, subd10_0 q = true := by
  unfold blkd10_0_8
  exact List.forall_mem_cons.2 ⟨subd10_0_256, List.forall_mem_cons.2 ⟨subd10_0_257, List.forall_mem_cons.2 ⟨subd10_0_258, List.forall_mem_cons.2 ⟨subd10_0_259, List.forall_mem_cons.2 ⟨subd10_0_260, List.forall_mem_cons.2 ⟨subd10_0_261, List.forall_mem_cons.2 ⟨subd10_0_262, List.forall_mem_cons.2 ⟨subd10_0_263, List.forall_mem_cons.2 ⟨subd10_0_264, List.forall_mem_cons.2 ⟨subd10_0_265, List.forall_mem_cons.2 ⟨subd10_0_266, List.forall_mem_cons.2 ⟨subd10_0_267, List.forall_mem_cons.2 ⟨subd10_0_268, List.forall_mem_cons.2 ⟨subd10_0_269, List.forall_mem_cons.2 ⟨subd10_0_270, List.forall_mem_cons.2 ⟨subd10_0_271, List.forall_mem_cons.2 ⟨subd10_0_272, List.forall_mem_cons.2 ⟨subd10_0_273, List.forall_mem_cons.2 ⟨subd10_0_274, List.forall_mem_cons.2 ⟨subd10_0_275, List.forall_mem_cons.2 ⟨subd10_0_276, List.forall_mem_cons.2 ⟨subd10_0_277, List.forall_mem_cons.2 ⟨subd10_0_278, List.forall_mem_cons.2 ⟨subd10_0_279, List.forall_mem_cons.2 ⟨subd10_0_280, List.forall_mem_cons.2 ⟨subd10_0_281, List.forall_mem_cons.2 ⟨subd10_0_282, List.forall_mem_cons.2 ⟨subd10_0_283, List.forall_mem_cons.2 ⟨subd10_0_284, List.forall_mem_cons.2 ⟨subd10_0_285, List.forall_mem_cons.2 ⟨subd10_0_286, List.forall_mem_cons.2 ⟨subd10_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_288 : subd10_0 [0, -1, -2] = true := by decide +kernel
theorem subd10_0_289 : subd10_0 [0, -1, -1] = true := by decide +kernel
theorem subd10_0_290 : subd10_0 [0, -1, 0] = true := by decide +kernel
theorem subd10_0_291 : subd10_0 [0, -1, 1] = true := by decide +kernel
theorem subd10_0_292 : subd10_0 [0, -1, 2] = true := by decide +kernel
theorem subd10_0_293 : subd10_0 [0, -1, 3] = true := by decide +kernel
theorem subd10_0_294 : subd10_0 [0, -1, 4] = true := by decide +kernel
theorem subd10_0_295 : subd10_0 [0, -1, 5] = true := by decide +kernel
theorem subd10_0_296 : subd10_0 [0, -1, 6] = true := by decide +kernel
theorem subd10_0_297 : subd10_0 [0, -1, 7] = true := by decide +kernel
theorem subd10_0_298 : subd10_0 [0, -1, 8] = true := by decide +kernel
theorem subd10_0_299 : subd10_0 [0, -1, 9] = true := by decide +kernel
theorem subd10_0_300 : subd10_0 [0, -1, 10] = true := by decide +kernel
theorem subd10_0_301 : subd10_0 [0, 0, -11] = true := by decide +kernel
theorem subd10_0_302 : subd10_0 [0, 0, -10] = true := by decide +kernel
theorem subd10_0_303 : subd10_0 [0, 0, -9] = true := by decide +kernel
theorem subd10_0_304 : subd10_0 [0, 0, -8] = true := by decide +kernel
theorem subd10_0_305 : subd10_0 [0, 0, -7] = true := by decide +kernel
theorem subd10_0_306 : subd10_0 [0, 0, -6] = true := by decide +kernel
theorem subd10_0_307 : subd10_0 [0, 0, -5] = true := by decide +kernel
theorem subd10_0_308 : subd10_0 [0, 0, -4] = true := by decide +kernel
theorem subd10_0_309 : subd10_0 [0, 0, -3] = true := by decide +kernel
theorem subd10_0_310 : subd10_0 [0, 0, -2] = true := by decide +kernel
theorem subd10_0_311 : subd10_0 [0, 0, -1] = true := by decide +kernel
theorem subd10_0_312 : subd10_0 [0, 0, 0] = true := by decide +kernel
theorem subd10_0_313 : subd10_0 [0, 0, 1] = true := by decide +kernel
theorem subd10_0_314 : subd10_0 [0, 0, 2] = true := by decide +kernel
theorem subd10_0_315 : subd10_0 [0, 0, 3] = true := by decide +kernel
theorem subd10_0_316 : subd10_0 [0, 0, 4] = true := by decide +kernel
theorem subd10_0_317 : subd10_0 [0, 0, 5] = true := by decide +kernel
theorem subd10_0_318 : subd10_0 [0, 0, 6] = true := by decide +kernel
theorem subd10_0_319 : subd10_0 [0, 0, 7] = true := by decide +kernel
theorem sbd10_0_9 : ∀ q ∈ blkd10_0_9, subd10_0 q = true := by
  unfold blkd10_0_9
  exact List.forall_mem_cons.2 ⟨subd10_0_288, List.forall_mem_cons.2 ⟨subd10_0_289, List.forall_mem_cons.2 ⟨subd10_0_290, List.forall_mem_cons.2 ⟨subd10_0_291, List.forall_mem_cons.2 ⟨subd10_0_292, List.forall_mem_cons.2 ⟨subd10_0_293, List.forall_mem_cons.2 ⟨subd10_0_294, List.forall_mem_cons.2 ⟨subd10_0_295, List.forall_mem_cons.2 ⟨subd10_0_296, List.forall_mem_cons.2 ⟨subd10_0_297, List.forall_mem_cons.2 ⟨subd10_0_298, List.forall_mem_cons.2 ⟨subd10_0_299, List.forall_mem_cons.2 ⟨subd10_0_300, List.forall_mem_cons.2 ⟨subd10_0_301, List.forall_mem_cons.2 ⟨subd10_0_302, List.forall_mem_cons.2 ⟨subd10_0_303, List.forall_mem_cons.2 ⟨subd10_0_304, List.forall_mem_cons.2 ⟨subd10_0_305, List.forall_mem_cons.2 ⟨subd10_0_306, List.forall_mem_cons.2 ⟨subd10_0_307, List.forall_mem_cons.2 ⟨subd10_0_308, List.forall_mem_cons.2 ⟨subd10_0_309, List.forall_mem_cons.2 ⟨subd10_0_310, List.forall_mem_cons.2 ⟨subd10_0_311, List.forall_mem_cons.2 ⟨subd10_0_312, List.forall_mem_cons.2 ⟨subd10_0_313, List.forall_mem_cons.2 ⟨subd10_0_314, List.forall_mem_cons.2 ⟨subd10_0_315, List.forall_mem_cons.2 ⟨subd10_0_316, List.forall_mem_cons.2 ⟨subd10_0_317, List.forall_mem_cons.2 ⟨subd10_0_318, List.forall_mem_cons.2 ⟨subd10_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_320 : subd10_0 [0, 0, 8] = true := by decide +kernel
theorem subd10_0_321 : subd10_0 [0, 0, 9] = true := by decide +kernel
theorem subd10_0_322 : subd10_0 [0, 0, 10] = true := by decide +kernel
theorem subd10_0_323 : subd10_0 [0, 1, -11] = true := by decide +kernel
theorem subd10_0_324 : subd10_0 [0, 1, -10] = true := by decide +kernel
theorem subd10_0_325 : subd10_0 [0, 1, -9] = true := by decide +kernel
theorem subd10_0_326 : subd10_0 [0, 1, -8] = true := by decide +kernel
theorem subd10_0_327 : subd10_0 [0, 1, -7] = true := by decide +kernel
theorem subd10_0_328 : subd10_0 [0, 1, -6] = true := by decide +kernel
theorem subd10_0_329 : subd10_0 [0, 1, -5] = true := by decide +kernel
theorem subd10_0_330 : subd10_0 [0, 1, -4] = true := by decide +kernel
theorem subd10_0_331 : subd10_0 [0, 1, -3] = true := by decide +kernel
theorem subd10_0_332 : subd10_0 [0, 1, -2] = true := by decide +kernel
theorem subd10_0_333 : subd10_0 [0, 1, -1] = true := by decide +kernel
theorem subd10_0_334 : subd10_0 [0, 1, 0] = true := by decide +kernel
theorem subd10_0_335 : subd10_0 [0, 1, 1] = true := by decide +kernel
theorem subd10_0_336 : subd10_0 [0, 1, 2] = true := by decide +kernel
theorem subd10_0_337 : subd10_0 [0, 1, 3] = true := by decide +kernel
theorem subd10_0_338 : subd10_0 [0, 1, 4] = true := by decide +kernel
theorem subd10_0_339 : subd10_0 [0, 1, 5] = true := by decide +kernel
theorem subd10_0_340 : subd10_0 [0, 1, 6] = true := by decide +kernel
theorem subd10_0_341 : subd10_0 [0, 1, 7] = true := by decide +kernel
theorem subd10_0_342 : subd10_0 [0, 1, 8] = true := by decide +kernel
theorem subd10_0_343 : subd10_0 [0, 1, 9] = true := by decide +kernel
theorem subd10_0_344 : subd10_0 [0, 2, -10] = true := by decide +kernel
theorem subd10_0_345 : subd10_0 [0, 2, -9] = true := by decide +kernel
theorem subd10_0_346 : subd10_0 [0, 2, -8] = true := by decide +kernel
theorem subd10_0_347 : subd10_0 [0, 2, -7] = true := by decide +kernel
theorem subd10_0_348 : subd10_0 [0, 2, -6] = true := by decide +kernel
theorem subd10_0_349 : subd10_0 [0, 2, -5] = true := by decide +kernel
theorem subd10_0_350 : subd10_0 [0, 2, -4] = true := by decide +kernel
theorem subd10_0_351 : subd10_0 [0, 2, -3] = true := by decide +kernel
theorem sbd10_0_10 : ∀ q ∈ blkd10_0_10, subd10_0 q = true := by
  unfold blkd10_0_10
  exact List.forall_mem_cons.2 ⟨subd10_0_320, List.forall_mem_cons.2 ⟨subd10_0_321, List.forall_mem_cons.2 ⟨subd10_0_322, List.forall_mem_cons.2 ⟨subd10_0_323, List.forall_mem_cons.2 ⟨subd10_0_324, List.forall_mem_cons.2 ⟨subd10_0_325, List.forall_mem_cons.2 ⟨subd10_0_326, List.forall_mem_cons.2 ⟨subd10_0_327, List.forall_mem_cons.2 ⟨subd10_0_328, List.forall_mem_cons.2 ⟨subd10_0_329, List.forall_mem_cons.2 ⟨subd10_0_330, List.forall_mem_cons.2 ⟨subd10_0_331, List.forall_mem_cons.2 ⟨subd10_0_332, List.forall_mem_cons.2 ⟨subd10_0_333, List.forall_mem_cons.2 ⟨subd10_0_334, List.forall_mem_cons.2 ⟨subd10_0_335, List.forall_mem_cons.2 ⟨subd10_0_336, List.forall_mem_cons.2 ⟨subd10_0_337, List.forall_mem_cons.2 ⟨subd10_0_338, List.forall_mem_cons.2 ⟨subd10_0_339, List.forall_mem_cons.2 ⟨subd10_0_340, List.forall_mem_cons.2 ⟨subd10_0_341, List.forall_mem_cons.2 ⟨subd10_0_342, List.forall_mem_cons.2 ⟨subd10_0_343, List.forall_mem_cons.2 ⟨subd10_0_344, List.forall_mem_cons.2 ⟨subd10_0_345, List.forall_mem_cons.2 ⟨subd10_0_346, List.forall_mem_cons.2 ⟨subd10_0_347, List.forall_mem_cons.2 ⟨subd10_0_348, List.forall_mem_cons.2 ⟨subd10_0_349, List.forall_mem_cons.2 ⟨subd10_0_350, List.forall_mem_cons.2 ⟨subd10_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
