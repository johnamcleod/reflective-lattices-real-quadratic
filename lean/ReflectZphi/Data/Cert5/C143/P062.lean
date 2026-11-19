import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd19_0 : ldCheck G d19_0.U d19_0.ms ldd19_0 = true := by decide +kernel
theorem pre_okd19_0 : subPre G cell19 d19_0 = true := by decide +kernel
theorem subd19_0_0 : subd19_0 [-4, -1] = true := by decide +kernel
theorem subd19_0_1 : subd19_0 [-4, 0] = true := by decide +kernel
theorem subd19_0_2 : subd19_0 [-4, 1] = true := by decide +kernel
theorem subd19_0_3 : subd19_0 [-4, 2] = true := by decide +kernel
theorem subd19_0_4 : subd19_0 [-4, 3] = true := by decide +kernel
theorem subd19_0_5 : subd19_0 [-3, -3] = true := by decide +kernel
theorem subd19_0_6 : subd19_0 [-3, -2] = true := by decide +kernel
theorem subd19_0_7 : subd19_0 [-3, -1, -8] = true := by decide +kernel
theorem subd19_0_8 : subd19_0 [-3, -1, -7] = true := by decide +kernel
theorem subd19_0_9 : subd19_0 [-3, -1, -6] = true := by decide +kernel
theorem subd19_0_10 : subd19_0 [-3, -1, -5] = true := by decide +kernel
theorem subd19_0_11 : subd19_0 [-3, -1, -4] = true := by decide +kernel
theorem subd19_0_12 : subd19_0 [-3, -1, -3] = true := by decide +kernel
theorem subd19_0_13 : subd19_0 [-3, -1, -2] = true := by decide +kernel
theorem subd19_0_14 : subd19_0 [-3, -1, -1] = true := by decide +kernel
theorem subd19_0_15 : subd19_0 [-3, -1, 0] = true := by decide +kernel
theorem subd19_0_16 : subd19_0 [-3, -1, 1] = true := by decide +kernel
theorem subd19_0_17 : subd19_0 [-3, -1, 2] = true := by decide +kernel
theorem subd19_0_18 : subd19_0 [-3, -1, 3] = true := by decide +kernel
theorem subd19_0_19 : subd19_0 [-3, -1, 4] = true := by decide +kernel
theorem subd19_0_20 : subd19_0 [-3, -1, 5] = true := by decide +kernel
theorem subd19_0_21 : subd19_0 [-3, -1, 6] = true := by decide +kernel
theorem subd19_0_22 : subd19_0 [-3, -1, 7] = true := by decide +kernel
theorem subd19_0_23 : subd19_0 [-3, -1, 8] = true := by decide +kernel
theorem subd19_0_24 : subd19_0 [-3, 0, -9] = true := by decide +kernel
theorem subd19_0_25 : subd19_0 [-3, 0, -8] = true := by decide +kernel
theorem subd19_0_26 : subd19_0 [-3, 0, -7] = true := by decide +kernel
theorem subd19_0_27 : subd19_0 [-3, 0, -6] = true := by decide +kernel
theorem subd19_0_28 : subd19_0 [-3, 0, -5] = true := by decide +kernel
theorem subd19_0_29 : subd19_0 [-3, 0, -4] = true := by decide +kernel
theorem subd19_0_30 : subd19_0 [-3, 0, -3] = true := by decide +kernel
theorem subd19_0_31 : subd19_0 [-3, 0, -2] = true := by decide +kernel
theorem sbd19_0_0 : ∀ q ∈ blkd19_0_0, subd19_0 q = true := by
  unfold blkd19_0_0
  exact List.forall_mem_cons.2 ⟨subd19_0_0, List.forall_mem_cons.2 ⟨subd19_0_1, List.forall_mem_cons.2 ⟨subd19_0_2, List.forall_mem_cons.2 ⟨subd19_0_3, List.forall_mem_cons.2 ⟨subd19_0_4, List.forall_mem_cons.2 ⟨subd19_0_5, List.forall_mem_cons.2 ⟨subd19_0_6, List.forall_mem_cons.2 ⟨subd19_0_7, List.forall_mem_cons.2 ⟨subd19_0_8, List.forall_mem_cons.2 ⟨subd19_0_9, List.forall_mem_cons.2 ⟨subd19_0_10, List.forall_mem_cons.2 ⟨subd19_0_11, List.forall_mem_cons.2 ⟨subd19_0_12, List.forall_mem_cons.2 ⟨subd19_0_13, List.forall_mem_cons.2 ⟨subd19_0_14, List.forall_mem_cons.2 ⟨subd19_0_15, List.forall_mem_cons.2 ⟨subd19_0_16, List.forall_mem_cons.2 ⟨subd19_0_17, List.forall_mem_cons.2 ⟨subd19_0_18, List.forall_mem_cons.2 ⟨subd19_0_19, List.forall_mem_cons.2 ⟨subd19_0_20, List.forall_mem_cons.2 ⟨subd19_0_21, List.forall_mem_cons.2 ⟨subd19_0_22, List.forall_mem_cons.2 ⟨subd19_0_23, List.forall_mem_cons.2 ⟨subd19_0_24, List.forall_mem_cons.2 ⟨subd19_0_25, List.forall_mem_cons.2 ⟨subd19_0_26, List.forall_mem_cons.2 ⟨subd19_0_27, List.forall_mem_cons.2 ⟨subd19_0_28, List.forall_mem_cons.2 ⟨subd19_0_29, List.forall_mem_cons.2 ⟨subd19_0_30, List.forall_mem_cons.2 ⟨subd19_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_32 : subd19_0 [-3, 0, -1] = true := by decide +kernel
theorem subd19_0_33 : subd19_0 [-3, 0, 0] = true := by decide +kernel
theorem subd19_0_34 : subd19_0 [-3, 0, 1] = true := by decide +kernel
theorem subd19_0_35 : subd19_0 [-3, 0, 2] = true := by decide +kernel
theorem subd19_0_36 : subd19_0 [-3, 0, 3] = true := by decide +kernel
theorem subd19_0_37 : subd19_0 [-3, 0, 4] = true := by decide +kernel
theorem subd19_0_38 : subd19_0 [-3, 0, 5] = true := by decide +kernel
theorem subd19_0_39 : subd19_0 [-3, 0, 6] = true := by decide +kernel
theorem subd19_0_40 : subd19_0 [-3, 0, 7] = true := by decide +kernel
theorem subd19_0_41 : subd19_0 [-3, 0, 8] = true := by decide +kernel
theorem subd19_0_42 : subd19_0 [-3, 0, 9] = true := by decide +kernel
theorem subd19_0_43 : subd19_0 [-3, 1, -10] = true := by decide +kernel
theorem subd19_0_44 : subd19_0 [-3, 1, -9] = true := by decide +kernel
theorem subd19_0_45 : subd19_0 [-3, 1, -8] = true := by decide +kernel
theorem subd19_0_46 : subd19_0 [-3, 1, -7] = true := by decide +kernel
theorem subd19_0_47 : subd19_0 [-3, 1, -6] = true := by decide +kernel
theorem subd19_0_48 : subd19_0 [-3, 1, -5] = true := by decide +kernel
theorem subd19_0_49 : subd19_0 [-3, 1, -4] = true := by decide +kernel
theorem subd19_0_50 : subd19_0 [-3, 1, -3] = true := by decide +kernel
theorem subd19_0_51 : subd19_0 [-3, 1, -2] = true := by decide +kernel
theorem subd19_0_52 : subd19_0 [-3, 1, -1] = true := by decide +kernel
theorem subd19_0_53 : subd19_0 [-3, 1, 0] = true := by decide +kernel
theorem subd19_0_54 : subd19_0 [-3, 1, 1] = true := by decide +kernel
theorem subd19_0_55 : subd19_0 [-3, 1, 2] = true := by decide +kernel
theorem subd19_0_56 : subd19_0 [-3, 1, 3] = true := by decide +kernel
theorem subd19_0_57 : subd19_0 [-3, 1, 4] = true := by decide +kernel
theorem subd19_0_58 : subd19_0 [-3, 1, 5] = true := by decide +kernel
theorem subd19_0_59 : subd19_0 [-3, 1, 6] = true := by decide +kernel
theorem subd19_0_60 : subd19_0 [-3, 1, 7] = true := by decide +kernel
theorem subd19_0_61 : subd19_0 [-3, 1, 8] = true := by decide +kernel
theorem subd19_0_62 : subd19_0 [-3, 1, 9] = true := by decide +kernel
theorem subd19_0_63 : subd19_0 [-3, 2, -10] = true := by decide +kernel
theorem sbd19_0_1 : ∀ q ∈ blkd19_0_1, subd19_0 q = true := by
  unfold blkd19_0_1
  exact List.forall_mem_cons.2 ⟨subd19_0_32, List.forall_mem_cons.2 ⟨subd19_0_33, List.forall_mem_cons.2 ⟨subd19_0_34, List.forall_mem_cons.2 ⟨subd19_0_35, List.forall_mem_cons.2 ⟨subd19_0_36, List.forall_mem_cons.2 ⟨subd19_0_37, List.forall_mem_cons.2 ⟨subd19_0_38, List.forall_mem_cons.2 ⟨subd19_0_39, List.forall_mem_cons.2 ⟨subd19_0_40, List.forall_mem_cons.2 ⟨subd19_0_41, List.forall_mem_cons.2 ⟨subd19_0_42, List.forall_mem_cons.2 ⟨subd19_0_43, List.forall_mem_cons.2 ⟨subd19_0_44, List.forall_mem_cons.2 ⟨subd19_0_45, List.forall_mem_cons.2 ⟨subd19_0_46, List.forall_mem_cons.2 ⟨subd19_0_47, List.forall_mem_cons.2 ⟨subd19_0_48, List.forall_mem_cons.2 ⟨subd19_0_49, List.forall_mem_cons.2 ⟨subd19_0_50, List.forall_mem_cons.2 ⟨subd19_0_51, List.forall_mem_cons.2 ⟨subd19_0_52, List.forall_mem_cons.2 ⟨subd19_0_53, List.forall_mem_cons.2 ⟨subd19_0_54, List.forall_mem_cons.2 ⟨subd19_0_55, List.forall_mem_cons.2 ⟨subd19_0_56, List.forall_mem_cons.2 ⟨subd19_0_57, List.forall_mem_cons.2 ⟨subd19_0_58, List.forall_mem_cons.2 ⟨subd19_0_59, List.forall_mem_cons.2 ⟨subd19_0_60, List.forall_mem_cons.2 ⟨subd19_0_61, List.forall_mem_cons.2 ⟨subd19_0_62, List.forall_mem_cons.2 ⟨subd19_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_64 : subd19_0 [-3, 2, -9] = true := by decide +kernel
theorem subd19_0_65 : subd19_0 [-3, 2, -8] = true := by decide +kernel
theorem subd19_0_66 : subd19_0 [-3, 2, -7] = true := by decide +kernel
theorem subd19_0_67 : subd19_0 [-3, 2, -6] = true := by decide +kernel
theorem subd19_0_68 : subd19_0 [-3, 2, -5] = true := by decide +kernel
theorem subd19_0_69 : subd19_0 [-3, 2, -4] = true := by decide +kernel
theorem subd19_0_70 : subd19_0 [-3, 2, -3] = true := by decide +kernel
theorem subd19_0_71 : subd19_0 [-3, 2, -2] = true := by decide +kernel
theorem subd19_0_72 : subd19_0 [-3, 2, -1] = true := by decide +kernel
theorem subd19_0_73 : subd19_0 [-3, 2, 0] = true := by decide +kernel
theorem subd19_0_74 : subd19_0 [-3, 2, 1] = true := by decide +kernel
theorem subd19_0_75 : subd19_0 [-3, 2, 2] = true := by decide +kernel
theorem subd19_0_76 : subd19_0 [-3, 2, 3] = true := by decide +kernel
theorem subd19_0_77 : subd19_0 [-3, 2, 4] = true := by decide +kernel
theorem subd19_0_78 : subd19_0 [-3, 2, 5] = true := by decide +kernel
theorem subd19_0_79 : subd19_0 [-3, 2, 6] = true := by decide +kernel
theorem subd19_0_80 : subd19_0 [-3, 2, 7] = true := by decide +kernel
theorem subd19_0_81 : subd19_0 [-3, 2, 8] = true := by decide +kernel
theorem subd19_0_82 : subd19_0 [-3, 3, -9] = true := by decide +kernel
theorem subd19_0_83 : subd19_0 [-3, 3, -8] = true := by decide +kernel
theorem subd19_0_84 : subd19_0 [-3, 3, -7] = true := by decide +kernel
theorem subd19_0_85 : subd19_0 [-3, 3, -6] = true := by decide +kernel
theorem subd19_0_86 : subd19_0 [-3, 3, -5] = true := by decide +kernel
theorem subd19_0_87 : subd19_0 [-3, 3, -4] = true := by decide +kernel
theorem subd19_0_88 : subd19_0 [-3, 3, -3] = true := by decide +kernel
theorem subd19_0_89 : subd19_0 [-3, 3, -2] = true := by decide +kernel
theorem subd19_0_90 : subd19_0 [-3, 3, -1] = true := by decide +kernel
theorem subd19_0_91 : subd19_0 [-3, 3, 0] = true := by decide +kernel
theorem subd19_0_92 : subd19_0 [-3, 3, 1] = true := by decide +kernel
theorem subd19_0_93 : subd19_0 [-3, 3, 2] = true := by decide +kernel
theorem subd19_0_94 : subd19_0 [-3, 3, 3] = true := by decide +kernel
theorem subd19_0_95 : subd19_0 [-3, 3, 4] = true := by decide +kernel
theorem sbd19_0_2 : ∀ q ∈ blkd19_0_2, subd19_0 q = true := by
  unfold blkd19_0_2
  exact List.forall_mem_cons.2 ⟨subd19_0_64, List.forall_mem_cons.2 ⟨subd19_0_65, List.forall_mem_cons.2 ⟨subd19_0_66, List.forall_mem_cons.2 ⟨subd19_0_67, List.forall_mem_cons.2 ⟨subd19_0_68, List.forall_mem_cons.2 ⟨subd19_0_69, List.forall_mem_cons.2 ⟨subd19_0_70, List.forall_mem_cons.2 ⟨subd19_0_71, List.forall_mem_cons.2 ⟨subd19_0_72, List.forall_mem_cons.2 ⟨subd19_0_73, List.forall_mem_cons.2 ⟨subd19_0_74, List.forall_mem_cons.2 ⟨subd19_0_75, List.forall_mem_cons.2 ⟨subd19_0_76, List.forall_mem_cons.2 ⟨subd19_0_77, List.forall_mem_cons.2 ⟨subd19_0_78, List.forall_mem_cons.2 ⟨subd19_0_79, List.forall_mem_cons.2 ⟨subd19_0_80, List.forall_mem_cons.2 ⟨subd19_0_81, List.forall_mem_cons.2 ⟨subd19_0_82, List.forall_mem_cons.2 ⟨subd19_0_83, List.forall_mem_cons.2 ⟨subd19_0_84, List.forall_mem_cons.2 ⟨subd19_0_85, List.forall_mem_cons.2 ⟨subd19_0_86, List.forall_mem_cons.2 ⟨subd19_0_87, List.forall_mem_cons.2 ⟨subd19_0_88, List.forall_mem_cons.2 ⟨subd19_0_89, List.forall_mem_cons.2 ⟨subd19_0_90, List.forall_mem_cons.2 ⟨subd19_0_91, List.forall_mem_cons.2 ⟨subd19_0_92, List.forall_mem_cons.2 ⟨subd19_0_93, List.forall_mem_cons.2 ⟨subd19_0_94, List.forall_mem_cons.2 ⟨subd19_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_96 : subd19_0 [-3, 3, 5] = true := by decide +kernel
theorem subd19_0_97 : subd19_0 [-3, 3, 6] = true := by decide +kernel
theorem subd19_0_98 : subd19_0 [-3, 4] = true := by decide +kernel
theorem subd19_0_99 : subd19_0 [-2, -4] = true := by decide +kernel
theorem subd19_0_100 : subd19_0 [-2, -3] = true := by decide +kernel
theorem subd19_0_101 : subd19_0 [-2, -2, -9] = true := by decide +kernel
theorem subd19_0_102 : subd19_0 [-2, -2, -8] = true := by decide +kernel
theorem subd19_0_103 : subd19_0 [-2, -2, -7] = true := by decide +kernel
theorem subd19_0_104 : subd19_0 [-2, -2, -6] = true := by decide +kernel
theorem subd19_0_105 : subd19_0 [-2, -2, -5] = true := by decide +kernel
theorem subd19_0_106 : subd19_0 [-2, -2, -4] = true := by decide +kernel
theorem subd19_0_107 : subd19_0 [-2, -2, -3] = true := by decide +kernel
theorem subd19_0_108 : subd19_0 [-2, -2, -2] = true := by decide +kernel
theorem subd19_0_109 : subd19_0 [-2, -2, -1] = true := by decide +kernel
theorem subd19_0_110 : subd19_0 [-2, -2, 0] = true := by decide +kernel
theorem subd19_0_111 : subd19_0 [-2, -2, 1] = true := by decide +kernel
theorem subd19_0_112 : subd19_0 [-2, -2, 2] = true := by decide +kernel
theorem subd19_0_113 : subd19_0 [-2, -2, 3] = true := by decide +kernel
theorem subd19_0_114 : subd19_0 [-2, -2, 4] = true := by decide +kernel
theorem subd19_0_115 : subd19_0 [-2, -2, 5] = true := by decide +kernel
theorem subd19_0_116 : subd19_0 [-2, -2, 6] = true := by decide +kernel
theorem subd19_0_117 : subd19_0 [-2, -2, 7] = true := by decide +kernel
theorem subd19_0_118 : subd19_0 [-2, -2, 8] = true := by decide +kernel
theorem subd19_0_119 : subd19_0 [-2, -2, 9] = true := by decide +kernel
theorem subd19_0_120 : subd19_0 [-2, -1, -11] = true := by decide +kernel
theorem subd19_0_121 : subd19_0 [-2, -1, -10] = true := by decide +kernel
theorem subd19_0_122 : subd19_0 [-2, -1, -9] = true := by decide +kernel
theorem subd19_0_123 : subd19_0 [-2, -1, -8] = true := by decide +kernel
theorem subd19_0_124 : subd19_0 [-2, -1, -7] = true := by decide +kernel
theorem subd19_0_125 : subd19_0 [-2, -1, -6] = true := by decide +kernel
theorem subd19_0_126 : subd19_0 [-2, -1, -5] = true := by decide +kernel
theorem subd19_0_127 : subd19_0 [-2, -1, -4] = true := by decide +kernel
theorem sbd19_0_3 : ∀ q ∈ blkd19_0_3, subd19_0 q = true := by
  unfold blkd19_0_3
  exact List.forall_mem_cons.2 ⟨subd19_0_96, List.forall_mem_cons.2 ⟨subd19_0_97, List.forall_mem_cons.2 ⟨subd19_0_98, List.forall_mem_cons.2 ⟨subd19_0_99, List.forall_mem_cons.2 ⟨subd19_0_100, List.forall_mem_cons.2 ⟨subd19_0_101, List.forall_mem_cons.2 ⟨subd19_0_102, List.forall_mem_cons.2 ⟨subd19_0_103, List.forall_mem_cons.2 ⟨subd19_0_104, List.forall_mem_cons.2 ⟨subd19_0_105, List.forall_mem_cons.2 ⟨subd19_0_106, List.forall_mem_cons.2 ⟨subd19_0_107, List.forall_mem_cons.2 ⟨subd19_0_108, List.forall_mem_cons.2 ⟨subd19_0_109, List.forall_mem_cons.2 ⟨subd19_0_110, List.forall_mem_cons.2 ⟨subd19_0_111, List.forall_mem_cons.2 ⟨subd19_0_112, List.forall_mem_cons.2 ⟨subd19_0_113, List.forall_mem_cons.2 ⟨subd19_0_114, List.forall_mem_cons.2 ⟨subd19_0_115, List.forall_mem_cons.2 ⟨subd19_0_116, List.forall_mem_cons.2 ⟨subd19_0_117, List.forall_mem_cons.2 ⟨subd19_0_118, List.forall_mem_cons.2 ⟨subd19_0_119, List.forall_mem_cons.2 ⟨subd19_0_120, List.forall_mem_cons.2 ⟨subd19_0_121, List.forall_mem_cons.2 ⟨subd19_0_122, List.forall_mem_cons.2 ⟨subd19_0_123, List.forall_mem_cons.2 ⟨subd19_0_124, List.forall_mem_cons.2 ⟨subd19_0_125, List.forall_mem_cons.2 ⟨subd19_0_126, List.forall_mem_cons.2 ⟨subd19_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_128 : subd19_0 [-2, -1, -3] = true := by decide +kernel
theorem subd19_0_129 : subd19_0 [-2, -1, -2] = true := by decide +kernel
theorem subd19_0_130 : subd19_0 [-2, -1, -1] = true := by decide +kernel
theorem subd19_0_131 : subd19_0 [-2, -1, 0] = true := by decide +kernel
theorem subd19_0_132 : subd19_0 [-2, -1, 1] = true := by decide +kernel
theorem subd19_0_133 : subd19_0 [-2, -1, 2] = true := by decide +kernel
theorem subd19_0_134 : subd19_0 [-2, -1, 3] = true := by decide +kernel
theorem subd19_0_135 : subd19_0 [-2, -1, 4] = true := by decide +kernel
theorem subd19_0_136 : subd19_0 [-2, -1, 5] = true := by decide +kernel
theorem subd19_0_137 : subd19_0 [-2, -1, 6] = true := by decide +kernel
theorem subd19_0_138 : subd19_0 [-2, -1, 7] = true := by decide +kernel
theorem subd19_0_139 : subd19_0 [-2, -1, 8] = true := by decide +kernel
theorem subd19_0_140 : subd19_0 [-2, -1, 9] = true := by decide +kernel
theorem subd19_0_141 : subd19_0 [-2, -1, 10] = true := by decide +kernel
theorem subd19_0_142 : subd19_0 [-2, 0, -12] = true := by decide +kernel
theorem subd19_0_143 : subd19_0 [-2, 0, -11] = true := by decide +kernel
theorem subd19_0_144 : subd19_0 [-2, 0, -10] = true := by decide +kernel
theorem subd19_0_145 : subd19_0 [-2, 0, -9] = true := by decide +kernel
theorem subd19_0_146 : subd19_0 [-2, 0, -8] = true := by decide +kernel
theorem subd19_0_147 : subd19_0 [-2, 0, -7] = true := by decide +kernel
theorem subd19_0_148 : subd19_0 [-2, 0, -6] = true := by decide +kernel
theorem subd19_0_149 : subd19_0 [-2, 0, -5] = true := by decide +kernel
theorem subd19_0_150 : subd19_0 [-2, 0, -4] = true := by decide +kernel
theorem subd19_0_151 : subd19_0 [-2, 0, -3] = true := by decide +kernel
theorem subd19_0_152 : subd19_0 [-2, 0, -2] = true := by decide +kernel
theorem subd19_0_153 : subd19_0 [-2, 0, -1] = true := by decide +kernel
theorem subd19_0_154 : subd19_0 [-2, 0, 0] = true := by decide +kernel
theorem subd19_0_155 : subd19_0 [-2, 0, 1] = true := by decide +kernel
theorem subd19_0_156 : subd19_0 [-2, 0, 2] = true := by decide +kernel
theorem subd19_0_157 : subd19_0 [-2, 0, 3] = true := by decide +kernel
theorem subd19_0_158 : subd19_0 [-2, 0, 4] = true := by decide +kernel
theorem subd19_0_159 : subd19_0 [-2, 0, 5] = true := by decide +kernel
theorem sbd19_0_4 : ∀ q ∈ blkd19_0_4, subd19_0 q = true := by
  unfold blkd19_0_4
  exact List.forall_mem_cons.2 ⟨subd19_0_128, List.forall_mem_cons.2 ⟨subd19_0_129, List.forall_mem_cons.2 ⟨subd19_0_130, List.forall_mem_cons.2 ⟨subd19_0_131, List.forall_mem_cons.2 ⟨subd19_0_132, List.forall_mem_cons.2 ⟨subd19_0_133, List.forall_mem_cons.2 ⟨subd19_0_134, List.forall_mem_cons.2 ⟨subd19_0_135, List.forall_mem_cons.2 ⟨subd19_0_136, List.forall_mem_cons.2 ⟨subd19_0_137, List.forall_mem_cons.2 ⟨subd19_0_138, List.forall_mem_cons.2 ⟨subd19_0_139, List.forall_mem_cons.2 ⟨subd19_0_140, List.forall_mem_cons.2 ⟨subd19_0_141, List.forall_mem_cons.2 ⟨subd19_0_142, List.forall_mem_cons.2 ⟨subd19_0_143, List.forall_mem_cons.2 ⟨subd19_0_144, List.forall_mem_cons.2 ⟨subd19_0_145, List.forall_mem_cons.2 ⟨subd19_0_146, List.forall_mem_cons.2 ⟨subd19_0_147, List.forall_mem_cons.2 ⟨subd19_0_148, List.forall_mem_cons.2 ⟨subd19_0_149, List.forall_mem_cons.2 ⟨subd19_0_150, List.forall_mem_cons.2 ⟨subd19_0_151, List.forall_mem_cons.2 ⟨subd19_0_152, List.forall_mem_cons.2 ⟨subd19_0_153, List.forall_mem_cons.2 ⟨subd19_0_154, List.forall_mem_cons.2 ⟨subd19_0_155, List.forall_mem_cons.2 ⟨subd19_0_156, List.forall_mem_cons.2 ⟨subd19_0_157, List.forall_mem_cons.2 ⟨subd19_0_158, List.forall_mem_cons.2 ⟨subd19_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_160 : subd19_0 [-2, 0, 6] = true := by decide +kernel
theorem subd19_0_161 : subd19_0 [-2, 0, 7] = true := by decide +kernel
theorem subd19_0_162 : subd19_0 [-2, 0, 8] = true := by decide +kernel
theorem subd19_0_163 : subd19_0 [-2, 0, 9] = true := by decide +kernel
theorem subd19_0_164 : subd19_0 [-2, 0, 10] = true := by decide +kernel
theorem subd19_0_165 : subd19_0 [-2, 0, 11] = true := by decide +kernel
theorem subd19_0_166 : subd19_0 [-2, 1, -12] = true := by decide +kernel
theorem subd19_0_167 : subd19_0 [-2, 1, -11] = true := by decide +kernel
theorem subd19_0_168 : subd19_0 [-2, 1, -10] = true := by decide +kernel
theorem subd19_0_169 : subd19_0 [-2, 1, -9] = true := by decide +kernel
theorem subd19_0_170 : subd19_0 [-2, 1, -8] = true := by decide +kernel
theorem subd19_0_171 : subd19_0 [-2, 1, -7] = true := by decide +kernel
theorem subd19_0_172 : subd19_0 [-2, 1, -6] = true := by decide +kernel
theorem subd19_0_173 : subd19_0 [-2, 1, -5] = true := by decide +kernel
theorem subd19_0_174 : subd19_0 [-2, 1, -4] = true := by decide +kernel
theorem subd19_0_175 : subd19_0 [-2, 1, -3] = true := by decide +kernel
theorem subd19_0_176 : subd19_0 [-2, 1, -2] = true := by decide +kernel
theorem subd19_0_177 : subd19_0 [-2, 1, -1] = true := by decide +kernel
theorem subd19_0_178 : subd19_0 [-2, 1, 0] = true := by decide +kernel
theorem subd19_0_179 : subd19_0 [-2, 1, 1] = true := by decide +kernel
theorem subd19_0_180 : subd19_0 [-2, 1, 2] = true := by decide +kernel
theorem subd19_0_181 : subd19_0 [-2, 1, 3] = true := by decide +kernel
theorem subd19_0_182 : subd19_0 [-2, 1, 4] = true := by decide +kernel
theorem subd19_0_183 : subd19_0 [-2, 1, 5] = true := by decide +kernel
theorem subd19_0_184 : subd19_0 [-2, 1, 6] = true := by decide +kernel
theorem subd19_0_185 : subd19_0 [-2, 1, 7] = true := by decide +kernel
theorem subd19_0_186 : subd19_0 [-2, 1, 8] = true := by decide +kernel
theorem subd19_0_187 : subd19_0 [-2, 1, 9] = true := by decide +kernel
theorem subd19_0_188 : subd19_0 [-2, 1, 10] = true := by decide +kernel
theorem subd19_0_189 : subd19_0 [-2, 1, 11] = true := by decide +kernel
theorem subd19_0_190 : subd19_0 [-2, 2, -12] = true := by decide +kernel
theorem subd19_0_191 : subd19_0 [-2, 2, -11] = true := by decide +kernel
theorem sbd19_0_5 : ∀ q ∈ blkd19_0_5, subd19_0 q = true := by
  unfold blkd19_0_5
  exact List.forall_mem_cons.2 ⟨subd19_0_160, List.forall_mem_cons.2 ⟨subd19_0_161, List.forall_mem_cons.2 ⟨subd19_0_162, List.forall_mem_cons.2 ⟨subd19_0_163, List.forall_mem_cons.2 ⟨subd19_0_164, List.forall_mem_cons.2 ⟨subd19_0_165, List.forall_mem_cons.2 ⟨subd19_0_166, List.forall_mem_cons.2 ⟨subd19_0_167, List.forall_mem_cons.2 ⟨subd19_0_168, List.forall_mem_cons.2 ⟨subd19_0_169, List.forall_mem_cons.2 ⟨subd19_0_170, List.forall_mem_cons.2 ⟨subd19_0_171, List.forall_mem_cons.2 ⟨subd19_0_172, List.forall_mem_cons.2 ⟨subd19_0_173, List.forall_mem_cons.2 ⟨subd19_0_174, List.forall_mem_cons.2 ⟨subd19_0_175, List.forall_mem_cons.2 ⟨subd19_0_176, List.forall_mem_cons.2 ⟨subd19_0_177, List.forall_mem_cons.2 ⟨subd19_0_178, List.forall_mem_cons.2 ⟨subd19_0_179, List.forall_mem_cons.2 ⟨subd19_0_180, List.forall_mem_cons.2 ⟨subd19_0_181, List.forall_mem_cons.2 ⟨subd19_0_182, List.forall_mem_cons.2 ⟨subd19_0_183, List.forall_mem_cons.2 ⟨subd19_0_184, List.forall_mem_cons.2 ⟨subd19_0_185, List.forall_mem_cons.2 ⟨subd19_0_186, List.forall_mem_cons.2 ⟨subd19_0_187, List.forall_mem_cons.2 ⟨subd19_0_188, List.forall_mem_cons.2 ⟨subd19_0_189, List.forall_mem_cons.2 ⟨subd19_0_190, List.forall_mem_cons.2 ⟨subd19_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_192 : subd19_0 [-2, 2, -10] = true := by decide +kernel
theorem subd19_0_193 : subd19_0 [-2, 2, -9] = true := by decide +kernel
theorem subd19_0_194 : subd19_0 [-2, 2, -8] = true := by decide +kernel
theorem subd19_0_195 : subd19_0 [-2, 2, -7] = true := by decide +kernel
theorem subd19_0_196 : subd19_0 [-2, 2, -6] = true := by decide +kernel
theorem subd19_0_197 : subd19_0 [-2, 2, -5] = true := by decide +kernel
theorem subd19_0_198 : subd19_0 [-2, 2, -4] = true := by decide +kernel
theorem subd19_0_199 : subd19_0 [-2, 2, -3] = true := by decide +kernel
theorem subd19_0_200 : subd19_0 [-2, 2, -2] = true := by decide +kernel
theorem subd19_0_201 : subd19_0 [-2, 2, -1] = true := by decide +kernel
theorem subd19_0_202 : subd19_0 [-2, 2, 0] = true := by decide +kernel
theorem subd19_0_203 : subd19_0 [-2, 2, 1] = true := by decide +kernel
theorem subd19_0_204 : subd19_0 [-2, 2, 2] = true := by decide +kernel
theorem subd19_0_205 : subd19_0 [-2, 2, 3] = true := by decide +kernel
theorem subd19_0_206 : subd19_0 [-2, 2, 4] = true := by decide +kernel
theorem subd19_0_207 : subd19_0 [-2, 2, 5] = true := by decide +kernel
theorem subd19_0_208 : subd19_0 [-2, 2, 6] = true := by decide +kernel
theorem subd19_0_209 : subd19_0 [-2, 2, 7] = true := by decide +kernel
theorem subd19_0_210 : subd19_0 [-2, 2, 8] = true := by decide +kernel
theorem subd19_0_211 : subd19_0 [-2, 2, 9] = true := by decide +kernel
theorem subd19_0_212 : subd19_0 [-2, 2, 10] = true := by decide +kernel
theorem subd19_0_213 : subd19_0 [-2, 3, -11] = true := by decide +kernel
theorem subd19_0_214 : subd19_0 [-2, 3, -10] = true := by decide +kernel
theorem subd19_0_215 : subd19_0 [-2, 3, -9] = true := by decide +kernel
theorem subd19_0_216 : subd19_0 [-2, 3, -8] = true := by decide +kernel
theorem subd19_0_217 : subd19_0 [-2, 3, -7] = true := by decide +kernel
theorem subd19_0_218 : subd19_0 [-2, 3, -6] = true := by decide +kernel
theorem subd19_0_219 : subd19_0 [-2, 3, -5] = true := by decide +kernel
theorem subd19_0_220 : subd19_0 [-2, 3, -4] = true := by decide +kernel
theorem subd19_0_221 : subd19_0 [-2, 3, -3] = true := by decide +kernel
theorem subd19_0_222 : subd19_0 [-2, 3, -2] = true := by decide +kernel
theorem subd19_0_223 : subd19_0 [-2, 3, -1] = true := by decide +kernel
theorem sbd19_0_6 : ∀ q ∈ blkd19_0_6, subd19_0 q = true := by
  unfold blkd19_0_6
  exact List.forall_mem_cons.2 ⟨subd19_0_192, List.forall_mem_cons.2 ⟨subd19_0_193, List.forall_mem_cons.2 ⟨subd19_0_194, List.forall_mem_cons.2 ⟨subd19_0_195, List.forall_mem_cons.2 ⟨subd19_0_196, List.forall_mem_cons.2 ⟨subd19_0_197, List.forall_mem_cons.2 ⟨subd19_0_198, List.forall_mem_cons.2 ⟨subd19_0_199, List.forall_mem_cons.2 ⟨subd19_0_200, List.forall_mem_cons.2 ⟨subd19_0_201, List.forall_mem_cons.2 ⟨subd19_0_202, List.forall_mem_cons.2 ⟨subd19_0_203, List.forall_mem_cons.2 ⟨subd19_0_204, List.forall_mem_cons.2 ⟨subd19_0_205, List.forall_mem_cons.2 ⟨subd19_0_206, List.forall_mem_cons.2 ⟨subd19_0_207, List.forall_mem_cons.2 ⟨subd19_0_208, List.forall_mem_cons.2 ⟨subd19_0_209, List.forall_mem_cons.2 ⟨subd19_0_210, List.forall_mem_cons.2 ⟨subd19_0_211, List.forall_mem_cons.2 ⟨subd19_0_212, List.forall_mem_cons.2 ⟨subd19_0_213, List.forall_mem_cons.2 ⟨subd19_0_214, List.forall_mem_cons.2 ⟨subd19_0_215, List.forall_mem_cons.2 ⟨subd19_0_216, List.forall_mem_cons.2 ⟨subd19_0_217, List.forall_mem_cons.2 ⟨subd19_0_218, List.forall_mem_cons.2 ⟨subd19_0_219, List.forall_mem_cons.2 ⟨subd19_0_220, List.forall_mem_cons.2 ⟨subd19_0_221, List.forall_mem_cons.2 ⟨subd19_0_222, List.forall_mem_cons.2 ⟨subd19_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_224 : subd19_0 [-2, 3, 0] = true := by decide +kernel
theorem subd19_0_225 : subd19_0 [-2, 3, 1] = true := by decide +kernel
theorem subd19_0_226 : subd19_0 [-2, 3, 2] = true := by decide +kernel
theorem subd19_0_227 : subd19_0 [-2, 3, 3] = true := by decide +kernel
theorem subd19_0_228 : subd19_0 [-2, 3, 4] = true := by decide +kernel
theorem subd19_0_229 : subd19_0 [-2, 3, 5] = true := by decide +kernel
theorem subd19_0_230 : subd19_0 [-2, 3, 6] = true := by decide +kernel
theorem subd19_0_231 : subd19_0 [-2, 3, 7] = true := by decide +kernel
theorem subd19_0_232 : subd19_0 [-2, 3, 8] = true := by decide +kernel
theorem subd19_0_233 : subd19_0 [-2, 4, -9] = true := by decide +kernel
theorem subd19_0_234 : subd19_0 [-2, 4, -8] = true := by decide +kernel
theorem subd19_0_235 : subd19_0 [-2, 4, -7] = true := by decide +kernel
theorem subd19_0_236 : subd19_0 [-2, 4, -6] = true := by decide +kernel
theorem subd19_0_237 : subd19_0 [-2, 4, -5] = true := by decide +kernel
theorem subd19_0_238 : subd19_0 [-2, 4, -4] = true := by decide +kernel
theorem subd19_0_239 : subd19_0 [-2, 4, -3] = true := by decide +kernel
theorem subd19_0_240 : subd19_0 [-2, 4, -2] = true := by decide +kernel
theorem subd19_0_241 : subd19_0 [-2, 4, -1] = true := by decide +kernel
theorem subd19_0_242 : subd19_0 [-2, 4, 0] = true := by decide +kernel
theorem subd19_0_243 : subd19_0 [-2, 4, 1] = true := by decide +kernel
theorem subd19_0_244 : subd19_0 [-2, 4, 2] = true := by decide +kernel
theorem subd19_0_245 : subd19_0 [-2, 4, 3] = true := by decide +kernel
theorem subd19_0_246 : subd19_0 [-2, 4, 4] = true := by decide +kernel
theorem subd19_0_247 : subd19_0 [-2, 4, 5] = true := by decide +kernel
theorem subd19_0_248 : subd19_0 [-2, 4, 6] = true := by decide +kernel
theorem subd19_0_249 : subd19_0 [-1, -5] = true := by decide +kernel
theorem subd19_0_250 : subd19_0 [-1, -4] = true := by decide +kernel
theorem subd19_0_251 : subd19_0 [-1, -3, -8] = true := by decide +kernel
theorem subd19_0_252 : subd19_0 [-1, -3, -7] = true := by decide +kernel
theorem subd19_0_253 : subd19_0 [-1, -3, -6] = true := by decide +kernel
theorem subd19_0_254 : subd19_0 [-1, -3, -5] = true := by decide +kernel
theorem subd19_0_255 : subd19_0 [-1, -3, -4] = true := by decide +kernel
theorem sbd19_0_7 : ∀ q ∈ blkd19_0_7, subd19_0 q = true := by
  unfold blkd19_0_7
  exact List.forall_mem_cons.2 ⟨subd19_0_224, List.forall_mem_cons.2 ⟨subd19_0_225, List.forall_mem_cons.2 ⟨subd19_0_226, List.forall_mem_cons.2 ⟨subd19_0_227, List.forall_mem_cons.2 ⟨subd19_0_228, List.forall_mem_cons.2 ⟨subd19_0_229, List.forall_mem_cons.2 ⟨subd19_0_230, List.forall_mem_cons.2 ⟨subd19_0_231, List.forall_mem_cons.2 ⟨subd19_0_232, List.forall_mem_cons.2 ⟨subd19_0_233, List.forall_mem_cons.2 ⟨subd19_0_234, List.forall_mem_cons.2 ⟨subd19_0_235, List.forall_mem_cons.2 ⟨subd19_0_236, List.forall_mem_cons.2 ⟨subd19_0_237, List.forall_mem_cons.2 ⟨subd19_0_238, List.forall_mem_cons.2 ⟨subd19_0_239, List.forall_mem_cons.2 ⟨subd19_0_240, List.forall_mem_cons.2 ⟨subd19_0_241, List.forall_mem_cons.2 ⟨subd19_0_242, List.forall_mem_cons.2 ⟨subd19_0_243, List.forall_mem_cons.2 ⟨subd19_0_244, List.forall_mem_cons.2 ⟨subd19_0_245, List.forall_mem_cons.2 ⟨subd19_0_246, List.forall_mem_cons.2 ⟨subd19_0_247, List.forall_mem_cons.2 ⟨subd19_0_248, List.forall_mem_cons.2 ⟨subd19_0_249, List.forall_mem_cons.2 ⟨subd19_0_250, List.forall_mem_cons.2 ⟨subd19_0_251, List.forall_mem_cons.2 ⟨subd19_0_252, List.forall_mem_cons.2 ⟨subd19_0_253, List.forall_mem_cons.2 ⟨subd19_0_254, List.forall_mem_cons.2 ⟨subd19_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_256 : subd19_0 [-1, -3, -3] = true := by decide +kernel
theorem subd19_0_257 : subd19_0 [-1, -3, -2] = true := by decide +kernel
theorem subd19_0_258 : subd19_0 [-1, -3, -1] = true := by decide +kernel
theorem subd19_0_259 : subd19_0 [-1, -3, 0] = true := by decide +kernel
theorem subd19_0_260 : subd19_0 [-1, -3, 1] = true := by decide +kernel
theorem subd19_0_261 : subd19_0 [-1, -3, 2] = true := by decide +kernel
theorem subd19_0_262 : subd19_0 [-1, -3, 3] = true := by decide +kernel
theorem subd19_0_263 : subd19_0 [-1, -3, 4] = true := by decide +kernel
theorem subd19_0_264 : subd19_0 [-1, -3, 5] = true := by decide +kernel
theorem subd19_0_265 : subd19_0 [-1, -3, 6] = true := by decide +kernel
theorem subd19_0_266 : subd19_0 [-1, -3, 7] = true := by decide +kernel
theorem subd19_0_267 : subd19_0 [-1, -3, 8] = true := by decide +kernel
theorem subd19_0_268 : subd19_0 [-1, -3, 9] = true := by decide +kernel
theorem subd19_0_269 : subd19_0 [-1, -2, -11] = true := by decide +kernel
theorem subd19_0_270 : subd19_0 [-1, -2, -10] = true := by decide +kernel
theorem subd19_0_271 : subd19_0 [-1, -2, -9] = true := by decide +kernel
theorem subd19_0_272 : subd19_0 [-1, -2, -8] = true := by decide +kernel
theorem subd19_0_273 : subd19_0 [-1, -2, -7] = true := by decide +kernel
theorem subd19_0_274 : subd19_0 [-1, -2, -6] = true := by decide +kernel
theorem subd19_0_275 : subd19_0 [-1, -2, -5] = true := by decide +kernel
theorem subd19_0_276 : subd19_0 [-1, -2, -4] = true := by decide +kernel
theorem subd19_0_277 : subd19_0 [-1, -2, -3] = true := by decide +kernel
theorem subd19_0_278 : subd19_0 [-1, -2, -2] = true := by decide +kernel
theorem subd19_0_279 : subd19_0 [-1, -2, -1] = true := by decide +kernel
theorem subd19_0_280 : subd19_0 [-1, -2, 0] = true := by decide +kernel
theorem subd19_0_281 : subd19_0 [-1, -2, 1] = true := by decide +kernel
theorem subd19_0_282 : subd19_0 [-1, -2, 2] = true := by decide +kernel
theorem subd19_0_283 : subd19_0 [-1, -2, 3] = true := by decide +kernel
theorem subd19_0_284 : subd19_0 [-1, -2, 4] = true := by decide +kernel
theorem subd19_0_285 : subd19_0 [-1, -2, 5] = true := by decide +kernel
theorem subd19_0_286 : subd19_0 [-1, -2, 6] = true := by decide +kernel
theorem subd19_0_287 : subd19_0 [-1, -2, 7] = true := by decide +kernel
theorem sbd19_0_8 : ∀ q ∈ blkd19_0_8, subd19_0 q = true := by
  unfold blkd19_0_8
  exact List.forall_mem_cons.2 ⟨subd19_0_256, List.forall_mem_cons.2 ⟨subd19_0_257, List.forall_mem_cons.2 ⟨subd19_0_258, List.forall_mem_cons.2 ⟨subd19_0_259, List.forall_mem_cons.2 ⟨subd19_0_260, List.forall_mem_cons.2 ⟨subd19_0_261, List.forall_mem_cons.2 ⟨subd19_0_262, List.forall_mem_cons.2 ⟨subd19_0_263, List.forall_mem_cons.2 ⟨subd19_0_264, List.forall_mem_cons.2 ⟨subd19_0_265, List.forall_mem_cons.2 ⟨subd19_0_266, List.forall_mem_cons.2 ⟨subd19_0_267, List.forall_mem_cons.2 ⟨subd19_0_268, List.forall_mem_cons.2 ⟨subd19_0_269, List.forall_mem_cons.2 ⟨subd19_0_270, List.forall_mem_cons.2 ⟨subd19_0_271, List.forall_mem_cons.2 ⟨subd19_0_272, List.forall_mem_cons.2 ⟨subd19_0_273, List.forall_mem_cons.2 ⟨subd19_0_274, List.forall_mem_cons.2 ⟨subd19_0_275, List.forall_mem_cons.2 ⟨subd19_0_276, List.forall_mem_cons.2 ⟨subd19_0_277, List.forall_mem_cons.2 ⟨subd19_0_278, List.forall_mem_cons.2 ⟨subd19_0_279, List.forall_mem_cons.2 ⟨subd19_0_280, List.forall_mem_cons.2 ⟨subd19_0_281, List.forall_mem_cons.2 ⟨subd19_0_282, List.forall_mem_cons.2 ⟨subd19_0_283, List.forall_mem_cons.2 ⟨subd19_0_284, List.forall_mem_cons.2 ⟨subd19_0_285, List.forall_mem_cons.2 ⟨subd19_0_286, List.forall_mem_cons.2 ⟨subd19_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_288 : subd19_0 [-1, -2, 8] = true := by decide +kernel
theorem subd19_0_289 : subd19_0 [-1, -2, 9] = true := by decide +kernel
theorem subd19_0_290 : subd19_0 [-1, -2, 10] = true := by decide +kernel
theorem subd19_0_291 : subd19_0 [-1, -2, 11] = true := by decide +kernel
theorem subd19_0_292 : subd19_0 [-1, -1, -12] = true := by decide +kernel
theorem subd19_0_293 : subd19_0 [-1, -1, -11] = true := by decide +kernel
theorem subd19_0_294 : subd19_0 [-1, -1, -10] = true := by decide +kernel
theorem subd19_0_295 : subd19_0 [-1, -1, -9] = true := by decide +kernel
theorem subd19_0_296 : subd19_0 [-1, -1, -8] = true := by decide +kernel
theorem subd19_0_297 : subd19_0 [-1, -1, -7] = true := by decide +kernel
theorem subd19_0_298 : subd19_0 [-1, -1, -6] = true := by decide +kernel
theorem subd19_0_299 : subd19_0 [-1, -1, -5] = true := by decide +kernel
theorem subd19_0_300 : subd19_0 [-1, -1, -4] = true := by decide +kernel
theorem subd19_0_301 : subd19_0 [-1, -1, -3] = true := by decide +kernel
theorem subd19_0_302 : subd19_0 [-1, -1, -2] = true := by decide +kernel
theorem subd19_0_303 : subd19_0 [-1, -1, -1] = true := by decide +kernel
theorem subd19_0_304 : subd19_0 [-1, -1, 0] = true := by decide +kernel
theorem subd19_0_305 : subd19_0 [-1, -1, 1] = true := by decide +kernel
theorem subd19_0_306 : subd19_0 [-1, -1, 2] = true := by decide +kernel
theorem subd19_0_307 : subd19_0 [-1, -1, 3] = true := by decide +kernel
theorem subd19_0_308 : subd19_0 [-1, -1, 4] = true := by decide +kernel
theorem subd19_0_309 : subd19_0 [-1, -1, 5] = true := by decide +kernel
theorem subd19_0_310 : subd19_0 [-1, -1, 6] = true := by decide +kernel
theorem subd19_0_311 : subd19_0 [-1, -1, 7] = true := by decide +kernel
theorem subd19_0_312 : subd19_0 [-1, -1, 8] = true := by decide +kernel
theorem subd19_0_313 : subd19_0 [-1, -1, 9] = true := by decide +kernel
theorem subd19_0_314 : subd19_0 [-1, -1, 10] = true := by decide +kernel
theorem subd19_0_315 : subd19_0 [-1, -1, 11] = true := by decide +kernel
theorem subd19_0_316 : subd19_0 [-1, -1, 12] = true := by decide +kernel
theorem subd19_0_317 : subd19_0 [-1, 0, -13] = true := by decide +kernel
theorem subd19_0_318 : subd19_0 [-1, 0, -12] = true := by decide +kernel
theorem subd19_0_319 : subd19_0 [-1, 0, -11] = true := by decide +kernel
theorem sbd19_0_9 : ∀ q ∈ blkd19_0_9, subd19_0 q = true := by
  unfold blkd19_0_9
  exact List.forall_mem_cons.2 ⟨subd19_0_288, List.forall_mem_cons.2 ⟨subd19_0_289, List.forall_mem_cons.2 ⟨subd19_0_290, List.forall_mem_cons.2 ⟨subd19_0_291, List.forall_mem_cons.2 ⟨subd19_0_292, List.forall_mem_cons.2 ⟨subd19_0_293, List.forall_mem_cons.2 ⟨subd19_0_294, List.forall_mem_cons.2 ⟨subd19_0_295, List.forall_mem_cons.2 ⟨subd19_0_296, List.forall_mem_cons.2 ⟨subd19_0_297, List.forall_mem_cons.2 ⟨subd19_0_298, List.forall_mem_cons.2 ⟨subd19_0_299, List.forall_mem_cons.2 ⟨subd19_0_300, List.forall_mem_cons.2 ⟨subd19_0_301, List.forall_mem_cons.2 ⟨subd19_0_302, List.forall_mem_cons.2 ⟨subd19_0_303, List.forall_mem_cons.2 ⟨subd19_0_304, List.forall_mem_cons.2 ⟨subd19_0_305, List.forall_mem_cons.2 ⟨subd19_0_306, List.forall_mem_cons.2 ⟨subd19_0_307, List.forall_mem_cons.2 ⟨subd19_0_308, List.forall_mem_cons.2 ⟨subd19_0_309, List.forall_mem_cons.2 ⟨subd19_0_310, List.forall_mem_cons.2 ⟨subd19_0_311, List.forall_mem_cons.2 ⟨subd19_0_312, List.forall_mem_cons.2 ⟨subd19_0_313, List.forall_mem_cons.2 ⟨subd19_0_314, List.forall_mem_cons.2 ⟨subd19_0_315, List.forall_mem_cons.2 ⟨subd19_0_316, List.forall_mem_cons.2 ⟨subd19_0_317, List.forall_mem_cons.2 ⟨subd19_0_318, List.forall_mem_cons.2 ⟨subd19_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_320 : subd19_0 [-1, 0, -10] = true := by decide +kernel
theorem subd19_0_321 : subd19_0 [-1, 0, -9] = true := by decide +kernel
theorem subd19_0_322 : subd19_0 [-1, 0, -8] = true := by decide +kernel
theorem subd19_0_323 : subd19_0 [-1, 0, -7] = true := by decide +kernel
theorem subd19_0_324 : subd19_0 [-1, 0, -6] = true := by decide +kernel
theorem subd19_0_325 : subd19_0 [-1, 0, -5] = true := by decide +kernel
theorem subd19_0_326 : subd19_0 [-1, 0, -4] = true := by decide +kernel
theorem subd19_0_327 : subd19_0 [-1, 0, -3] = true := by decide +kernel
theorem subd19_0_328 : subd19_0 [-1, 0, -2] = true := by decide +kernel
theorem subd19_0_329 : subd19_0 [-1, 0, -1] = true := by decide +kernel
theorem subd19_0_330 : subd19_0 [-1, 0, 0] = true := by decide +kernel
theorem subd19_0_331 : subd19_0 [-1, 0, 1] = true := by decide +kernel
theorem subd19_0_332 : subd19_0 [-1, 0, 2] = true := by decide +kernel
theorem subd19_0_333 : subd19_0 [-1, 0, 3] = true := by decide +kernel
theorem subd19_0_334 : subd19_0 [-1, 0, 4] = true := by decide +kernel
theorem subd19_0_335 : subd19_0 [-1, 0, 5] = true := by decide +kernel
theorem subd19_0_336 : subd19_0 [-1, 0, 6] = true := by decide +kernel
theorem subd19_0_337 : subd19_0 [-1, 0, 7] = true := by decide +kernel
theorem subd19_0_338 : subd19_0 [-1, 0, 8] = true := by decide +kernel
theorem subd19_0_339 : subd19_0 [-1, 0, 9] = true := by decide +kernel
theorem subd19_0_340 : subd19_0 [-1, 0, 10] = true := by decide +kernel
theorem subd19_0_341 : subd19_0 [-1, 0, 11] = true := by decide +kernel
theorem subd19_0_342 : subd19_0 [-1, 0, 12] = true := by decide +kernel
theorem subd19_0_343 : subd19_0 [-1, 1, -13] = true := by decide +kernel
theorem subd19_0_344 : subd19_0 [-1, 1, -12] = true := by decide +kernel
theorem subd19_0_345 : subd19_0 [-1, 1, -11] = true := by decide +kernel
theorem subd19_0_346 : subd19_0 [-1, 1, -10] = true := by decide +kernel
theorem subd19_0_347 : subd19_0 [-1, 1, -9] = true := by decide +kernel
theorem subd19_0_348 : subd19_0 [-1, 1, -8] = true := by decide +kernel
theorem subd19_0_349 : subd19_0 [-1, 1, -7] = true := by decide +kernel
theorem subd19_0_350 : subd19_0 [-1, 1, -6] = true := by decide +kernel
theorem subd19_0_351 : subd19_0 [-1, 1, -5] = true := by decide +kernel
theorem sbd19_0_10 : ∀ q ∈ blkd19_0_10, subd19_0 q = true := by
  unfold blkd19_0_10
  exact List.forall_mem_cons.2 ⟨subd19_0_320, List.forall_mem_cons.2 ⟨subd19_0_321, List.forall_mem_cons.2 ⟨subd19_0_322, List.forall_mem_cons.2 ⟨subd19_0_323, List.forall_mem_cons.2 ⟨subd19_0_324, List.forall_mem_cons.2 ⟨subd19_0_325, List.forall_mem_cons.2 ⟨subd19_0_326, List.forall_mem_cons.2 ⟨subd19_0_327, List.forall_mem_cons.2 ⟨subd19_0_328, List.forall_mem_cons.2 ⟨subd19_0_329, List.forall_mem_cons.2 ⟨subd19_0_330, List.forall_mem_cons.2 ⟨subd19_0_331, List.forall_mem_cons.2 ⟨subd19_0_332, List.forall_mem_cons.2 ⟨subd19_0_333, List.forall_mem_cons.2 ⟨subd19_0_334, List.forall_mem_cons.2 ⟨subd19_0_335, List.forall_mem_cons.2 ⟨subd19_0_336, List.forall_mem_cons.2 ⟨subd19_0_337, List.forall_mem_cons.2 ⟨subd19_0_338, List.forall_mem_cons.2 ⟨subd19_0_339, List.forall_mem_cons.2 ⟨subd19_0_340, List.forall_mem_cons.2 ⟨subd19_0_341, List.forall_mem_cons.2 ⟨subd19_0_342, List.forall_mem_cons.2 ⟨subd19_0_343, List.forall_mem_cons.2 ⟨subd19_0_344, List.forall_mem_cons.2 ⟨subd19_0_345, List.forall_mem_cons.2 ⟨subd19_0_346, List.forall_mem_cons.2 ⟨subd19_0_347, List.forall_mem_cons.2 ⟨subd19_0_348, List.forall_mem_cons.2 ⟨subd19_0_349, List.forall_mem_cons.2 ⟨subd19_0_350, List.forall_mem_cons.2 ⟨subd19_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
