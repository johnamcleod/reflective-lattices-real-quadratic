import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd17_3 : ldCheck G d17_3.U d17_3.ms ldd17_3 = true := by decide +kernel
theorem pre_okd17_3 : subPre G cell17 d17_3 = true := by decide +kernel
theorem subd17_3_0 : subd17_3 [-6, -5] = true := by decide +kernel
theorem subd17_3_1 : subd17_3 [-6, -4] = true := by decide +kernel
theorem subd17_3_2 : subd17_3 [-6, -3] = true := by decide +kernel
theorem subd17_3_3 : subd17_3 [-6, -2] = true := by decide +kernel
theorem subd17_3_4 : subd17_3 [-6, -1] = true := by decide +kernel
theorem subd17_3_5 : subd17_3 [-6, 0] = true := by decide +kernel
theorem subd17_3_6 : subd17_3 [-6, 1] = true := by decide +kernel
theorem subd17_3_7 : subd17_3 [-5, -6] = true := by decide +kernel
theorem subd17_3_8 : subd17_3 [-5, -5] = true := by decide +kernel
theorem subd17_3_9 : subd17_3 [-5, -4] = true := by decide +kernel
theorem subd17_3_10 : subd17_3 [-5, -3] = true := by decide +kernel
theorem subd17_3_11 : subd17_3 [-5, -2] = true := by decide +kernel
theorem subd17_3_12 : subd17_3 [-5, -1] = true := by decide +kernel
theorem subd17_3_13 : subd17_3 [-5, 0] = true := by decide +kernel
theorem subd17_3_14 : subd17_3 [-5, 1] = true := by decide +kernel
theorem subd17_3_15 : subd17_3 [-5, 2] = true := by decide +kernel
theorem subd17_3_16 : subd17_3 [-5, 3] = true := by decide +kernel
theorem subd17_3_17 : subd17_3 [-4, -7] = true := by decide +kernel
theorem subd17_3_18 : subd17_3 [-4, -6] = true := by decide +kernel
theorem subd17_3_19 : subd17_3 [-4, -5] = true := by decide +kernel
theorem subd17_3_20 : subd17_3 [-4, -4] = true := by decide +kernel
theorem subd17_3_21 : subd17_3 [-4, -3, -5] = true := by decide +kernel
theorem subd17_3_22 : subd17_3 [-4, -3, -4] = true := by decide +kernel
theorem subd17_3_23 : subd17_3 [-4, -3, -3] = true := by decide +kernel
theorem subd17_3_24 : subd17_3 [-4, -3, -2] = true := by decide +kernel
theorem subd17_3_25 : subd17_3 [-4, -3, -1] = true := by decide +kernel
theorem subd17_3_26 : subd17_3 [-4, -3, 0] = true := by decide +kernel
theorem subd17_3_27 : subd17_3 [-4, -3, 1] = true := by decide +kernel
theorem subd17_3_28 : subd17_3 [-4, -3, 2] = true := by decide +kernel
theorem subd17_3_29 : subd17_3 [-4, -3, 3] = true := by decide +kernel
theorem subd17_3_30 : subd17_3 [-4, -3, 4] = true := by decide +kernel
theorem subd17_3_31 : subd17_3 [-4, -3, 5] = true := by decide +kernel
theorem sbd17_3_0 : ∀ q ∈ blkd17_3_0, subd17_3 q = true := by
  unfold blkd17_3_0
  exact List.forall_mem_cons.2 ⟨subd17_3_0, List.forall_mem_cons.2 ⟨subd17_3_1, List.forall_mem_cons.2 ⟨subd17_3_2, List.forall_mem_cons.2 ⟨subd17_3_3, List.forall_mem_cons.2 ⟨subd17_3_4, List.forall_mem_cons.2 ⟨subd17_3_5, List.forall_mem_cons.2 ⟨subd17_3_6, List.forall_mem_cons.2 ⟨subd17_3_7, List.forall_mem_cons.2 ⟨subd17_3_8, List.forall_mem_cons.2 ⟨subd17_3_9, List.forall_mem_cons.2 ⟨subd17_3_10, List.forall_mem_cons.2 ⟨subd17_3_11, List.forall_mem_cons.2 ⟨subd17_3_12, List.forall_mem_cons.2 ⟨subd17_3_13, List.forall_mem_cons.2 ⟨subd17_3_14, List.forall_mem_cons.2 ⟨subd17_3_15, List.forall_mem_cons.2 ⟨subd17_3_16, List.forall_mem_cons.2 ⟨subd17_3_17, List.forall_mem_cons.2 ⟨subd17_3_18, List.forall_mem_cons.2 ⟨subd17_3_19, List.forall_mem_cons.2 ⟨subd17_3_20, List.forall_mem_cons.2 ⟨subd17_3_21, List.forall_mem_cons.2 ⟨subd17_3_22, List.forall_mem_cons.2 ⟨subd17_3_23, List.forall_mem_cons.2 ⟨subd17_3_24, List.forall_mem_cons.2 ⟨subd17_3_25, List.forall_mem_cons.2 ⟨subd17_3_26, List.forall_mem_cons.2 ⟨subd17_3_27, List.forall_mem_cons.2 ⟨subd17_3_28, List.forall_mem_cons.2 ⟨subd17_3_29, List.forall_mem_cons.2 ⟨subd17_3_30, List.forall_mem_cons.2 ⟨subd17_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_32 : subd17_3 [-4, -3, 6] = true := by decide +kernel
theorem subd17_3_33 : subd17_3 [-4, -3, 7] = true := by decide +kernel
theorem subd17_3_34 : subd17_3 [-4, -2, -5] = true := by decide +kernel
theorem subd17_3_35 : subd17_3 [-4, -2, -4] = true := by decide +kernel
theorem subd17_3_36 : subd17_3 [-4, -2, -3] = true := by decide +kernel
theorem subd17_3_37 : subd17_3 [-4, -2, -2] = true := by decide +kernel
theorem subd17_3_38 : subd17_3 [-4, -2, -1] = true := by decide +kernel
theorem subd17_3_39 : subd17_3 [-4, -2, 0] = true := by decide +kernel
theorem subd17_3_40 : subd17_3 [-4, -2, 1] = true := by decide +kernel
theorem subd17_3_41 : subd17_3 [-4, -2, 2] = true := by decide +kernel
theorem subd17_3_42 : subd17_3 [-4, -2, 3] = true := by decide +kernel
theorem subd17_3_43 : subd17_3 [-4, -2, 4] = true := by decide +kernel
theorem subd17_3_44 : subd17_3 [-4, -2, 5] = true := by decide +kernel
theorem subd17_3_45 : subd17_3 [-4, -2, 6] = true := by decide +kernel
theorem subd17_3_46 : subd17_3 [-4, -2, 7] = true := by decide +kernel
theorem subd17_3_47 : subd17_3 [-4, -2, 8] = true := by decide +kernel
theorem subd17_3_48 : subd17_3 [-4, -1, -5] = true := by decide +kernel
theorem subd17_3_49 : subd17_3 [-4, -1, -4] = true := by decide +kernel
theorem subd17_3_50 : subd17_3 [-4, -1, -3] = true := by decide +kernel
theorem subd17_3_51 : subd17_3 [-4, -1, -2] = true := by decide +kernel
theorem subd17_3_52 : subd17_3 [-4, -1, -1] = true := by decide +kernel
theorem subd17_3_53 : subd17_3 [-4, -1, 0] = true := by decide +kernel
theorem subd17_3_54 : subd17_3 [-4, -1, 1] = true := by decide +kernel
theorem subd17_3_55 : subd17_3 [-4, -1, 2] = true := by decide +kernel
theorem subd17_3_56 : subd17_3 [-4, -1, 3] = true := by decide +kernel
theorem subd17_3_57 : subd17_3 [-4, -1, 4] = true := by decide +kernel
theorem subd17_3_58 : subd17_3 [-4, -1, 5] = true := by decide +kernel
theorem subd17_3_59 : subd17_3 [-4, -1, 6] = true := by decide +kernel
theorem subd17_3_60 : subd17_3 [-4, -1, 7] = true := by decide +kernel
theorem subd17_3_61 : subd17_3 [-4, -1, 8] = true := by decide +kernel
theorem subd17_3_62 : subd17_3 [-4, 0, -5] = true := by decide +kernel
theorem subd17_3_63 : subd17_3 [-4, 0, -4] = true := by decide +kernel
theorem sbd17_3_1 : ∀ q ∈ blkd17_3_1, subd17_3 q = true := by
  unfold blkd17_3_1
  exact List.forall_mem_cons.2 ⟨subd17_3_32, List.forall_mem_cons.2 ⟨subd17_3_33, List.forall_mem_cons.2 ⟨subd17_3_34, List.forall_mem_cons.2 ⟨subd17_3_35, List.forall_mem_cons.2 ⟨subd17_3_36, List.forall_mem_cons.2 ⟨subd17_3_37, List.forall_mem_cons.2 ⟨subd17_3_38, List.forall_mem_cons.2 ⟨subd17_3_39, List.forall_mem_cons.2 ⟨subd17_3_40, List.forall_mem_cons.2 ⟨subd17_3_41, List.forall_mem_cons.2 ⟨subd17_3_42, List.forall_mem_cons.2 ⟨subd17_3_43, List.forall_mem_cons.2 ⟨subd17_3_44, List.forall_mem_cons.2 ⟨subd17_3_45, List.forall_mem_cons.2 ⟨subd17_3_46, List.forall_mem_cons.2 ⟨subd17_3_47, List.forall_mem_cons.2 ⟨subd17_3_48, List.forall_mem_cons.2 ⟨subd17_3_49, List.forall_mem_cons.2 ⟨subd17_3_50, List.forall_mem_cons.2 ⟨subd17_3_51, List.forall_mem_cons.2 ⟨subd17_3_52, List.forall_mem_cons.2 ⟨subd17_3_53, List.forall_mem_cons.2 ⟨subd17_3_54, List.forall_mem_cons.2 ⟨subd17_3_55, List.forall_mem_cons.2 ⟨subd17_3_56, List.forall_mem_cons.2 ⟨subd17_3_57, List.forall_mem_cons.2 ⟨subd17_3_58, List.forall_mem_cons.2 ⟨subd17_3_59, List.forall_mem_cons.2 ⟨subd17_3_60, List.forall_mem_cons.2 ⟨subd17_3_61, List.forall_mem_cons.2 ⟨subd17_3_62, List.forall_mem_cons.2 ⟨subd17_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_64 : subd17_3 [-4, 0, -3] = true := by decide +kernel
theorem subd17_3_65 : subd17_3 [-4, 0, -2] = true := by decide +kernel
theorem subd17_3_66 : subd17_3 [-4, 0, -1] = true := by decide +kernel
theorem subd17_3_67 : subd17_3 [-4, 0, 0] = true := by decide +kernel
theorem subd17_3_68 : subd17_3 [-4, 0, 1] = true := by decide +kernel
theorem subd17_3_69 : subd17_3 [-4, 0, 2] = true := by decide +kernel
theorem subd17_3_70 : subd17_3 [-4, 0, 3] = true := by decide +kernel
theorem subd17_3_71 : subd17_3 [-4, 0, 4] = true := by decide +kernel
theorem subd17_3_72 : subd17_3 [-4, 0, 5] = true := by decide +kernel
theorem subd17_3_73 : subd17_3 [-4, 0, 6] = true := by decide +kernel
theorem subd17_3_74 : subd17_3 [-4, 0, 7] = true := by decide +kernel
theorem subd17_3_75 : subd17_3 [-4, 0, 8] = true := by decide +kernel
theorem subd17_3_76 : subd17_3 [-4, 1, -5] = true := by decide +kernel
theorem subd17_3_77 : subd17_3 [-4, 1, -4] = true := by decide +kernel
theorem subd17_3_78 : subd17_3 [-4, 1, -3] = true := by decide +kernel
theorem subd17_3_79 : subd17_3 [-4, 1, -2] = true := by decide +kernel
theorem subd17_3_80 : subd17_3 [-4, 1, -1] = true := by decide +kernel
theorem subd17_3_81 : subd17_3 [-4, 1, 0] = true := by decide +kernel
theorem subd17_3_82 : subd17_3 [-4, 1, 1] = true := by decide +kernel
theorem subd17_3_83 : subd17_3 [-4, 1, 2] = true := by decide +kernel
theorem subd17_3_84 : subd17_3 [-4, 1, 3] = true := by decide +kernel
theorem subd17_3_85 : subd17_3 [-4, 1, 4] = true := by decide +kernel
theorem subd17_3_86 : subd17_3 [-4, 1, 5] = true := by decide +kernel
theorem subd17_3_87 : subd17_3 [-4, 1, 6] = true := by decide +kernel
theorem subd17_3_88 : subd17_3 [-4, 1, 7] = true := by decide +kernel
theorem subd17_3_89 : subd17_3 [-4, 1, 8] = true := by decide +kernel
theorem subd17_3_90 : subd17_3 [-4, 2] = true := by decide +kernel
theorem subd17_3_91 : subd17_3 [-4, 3] = true := by decide +kernel
theorem subd17_3_92 : subd17_3 [-4, 4] = true := by decide +kernel
theorem subd17_3_93 : subd17_3 [-3, -8] = true := by decide +kernel
theorem subd17_3_94 : subd17_3 [-3, -7] = true := by decide +kernel
theorem subd17_3_95 : subd17_3 [-3, -6] = true := by decide +kernel
theorem sbd17_3_2 : ∀ q ∈ blkd17_3_2, subd17_3 q = true := by
  unfold blkd17_3_2
  exact List.forall_mem_cons.2 ⟨subd17_3_64, List.forall_mem_cons.2 ⟨subd17_3_65, List.forall_mem_cons.2 ⟨subd17_3_66, List.forall_mem_cons.2 ⟨subd17_3_67, List.forall_mem_cons.2 ⟨subd17_3_68, List.forall_mem_cons.2 ⟨subd17_3_69, List.forall_mem_cons.2 ⟨subd17_3_70, List.forall_mem_cons.2 ⟨subd17_3_71, List.forall_mem_cons.2 ⟨subd17_3_72, List.forall_mem_cons.2 ⟨subd17_3_73, List.forall_mem_cons.2 ⟨subd17_3_74, List.forall_mem_cons.2 ⟨subd17_3_75, List.forall_mem_cons.2 ⟨subd17_3_76, List.forall_mem_cons.2 ⟨subd17_3_77, List.forall_mem_cons.2 ⟨subd17_3_78, List.forall_mem_cons.2 ⟨subd17_3_79, List.forall_mem_cons.2 ⟨subd17_3_80, List.forall_mem_cons.2 ⟨subd17_3_81, List.forall_mem_cons.2 ⟨subd17_3_82, List.forall_mem_cons.2 ⟨subd17_3_83, List.forall_mem_cons.2 ⟨subd17_3_84, List.forall_mem_cons.2 ⟨subd17_3_85, List.forall_mem_cons.2 ⟨subd17_3_86, List.forall_mem_cons.2 ⟨subd17_3_87, List.forall_mem_cons.2 ⟨subd17_3_88, List.forall_mem_cons.2 ⟨subd17_3_89, List.forall_mem_cons.2 ⟨subd17_3_90, List.forall_mem_cons.2 ⟨subd17_3_91, List.forall_mem_cons.2 ⟨subd17_3_92, List.forall_mem_cons.2 ⟨subd17_3_93, List.forall_mem_cons.2 ⟨subd17_3_94, List.forall_mem_cons.2 ⟨subd17_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_96 : subd17_3 [-3, -5] = true := by decide +kernel
theorem subd17_3_97 : subd17_3 [-3, -4, -6] = true := by decide +kernel
theorem subd17_3_98 : subd17_3 [-3, -4, -5] = true := by decide +kernel
theorem subd17_3_99 : subd17_3 [-3, -4, -4] = true := by decide +kernel
theorem subd17_3_100 : subd17_3 [-3, -4, -3] = true := by decide +kernel
theorem subd17_3_101 : subd17_3 [-3, -4, -2] = true := by decide +kernel
theorem subd17_3_102 : subd17_3 [-3, -4, -1] = true := by decide +kernel
theorem subd17_3_103 : subd17_3 [-3, -4, 0] = true := by decide +kernel
theorem subd17_3_104 : subd17_3 [-3, -4, 1] = true := by decide +kernel
theorem subd17_3_105 : subd17_3 [-3, -4, 2] = true := by decide +kernel
theorem subd17_3_106 : subd17_3 [-3, -4, 3] = true := by decide +kernel
theorem subd17_3_107 : subd17_3 [-3, -4, 4] = true := by decide +kernel
theorem subd17_3_108 : subd17_3 [-3, -4, 5] = true := by decide +kernel
theorem subd17_3_109 : subd17_3 [-3, -4, 6] = true := by decide +kernel
theorem subd17_3_110 : subd17_3 [-3, -4, 7] = true := by decide +kernel
theorem subd17_3_111 : subd17_3 [-3, -3, -6] = true := by decide +kernel
theorem subd17_3_112 : subd17_3 [-3, -3, -5] = true := by decide +kernel
theorem subd17_3_113 : subd17_3 [-3, -3, -4] = true := by decide +kernel
theorem subd17_3_114 : subd17_3 [-3, -3, -3] = true := by decide +kernel
theorem subd17_3_115 : subd17_3 [-3, -3, -2] = true := by decide +kernel
theorem subd17_3_116 : subd17_3 [-3, -3, -1] = true := by decide +kernel
theorem subd17_3_117 : subd17_3 [-3, -3, 0] = true := by decide +kernel
theorem subd17_3_118 : subd17_3 [-3, -3, 1] = true := by decide +kernel
theorem subd17_3_119 : subd17_3 [-3, -3, 2] = true := by decide +kernel
theorem subd17_3_120 : subd17_3 [-3, -3, 3] = true := by decide +kernel
theorem subd17_3_121 : subd17_3 [-3, -3, 4] = true := by decide +kernel
theorem subd17_3_122 : subd17_3 [-3, -3, 5] = true := by decide +kernel
theorem subd17_3_123 : subd17_3 [-3, -3, 6] = true := by decide +kernel
theorem subd17_3_124 : subd17_3 [-3, -3, 7] = true := by decide +kernel
theorem subd17_3_125 : subd17_3 [-3, -3, 8] = true := by decide +kernel
theorem subd17_3_126 : subd17_3 [-3, -2, -7] = true := by decide +kernel
theorem subd17_3_127 : subd17_3 [-3, -2, -6] = true := by decide +kernel
theorem sbd17_3_3 : ∀ q ∈ blkd17_3_3, subd17_3 q = true := by
  unfold blkd17_3_3
  exact List.forall_mem_cons.2 ⟨subd17_3_96, List.forall_mem_cons.2 ⟨subd17_3_97, List.forall_mem_cons.2 ⟨subd17_3_98, List.forall_mem_cons.2 ⟨subd17_3_99, List.forall_mem_cons.2 ⟨subd17_3_100, List.forall_mem_cons.2 ⟨subd17_3_101, List.forall_mem_cons.2 ⟨subd17_3_102, List.forall_mem_cons.2 ⟨subd17_3_103, List.forall_mem_cons.2 ⟨subd17_3_104, List.forall_mem_cons.2 ⟨subd17_3_105, List.forall_mem_cons.2 ⟨subd17_3_106, List.forall_mem_cons.2 ⟨subd17_3_107, List.forall_mem_cons.2 ⟨subd17_3_108, List.forall_mem_cons.2 ⟨subd17_3_109, List.forall_mem_cons.2 ⟨subd17_3_110, List.forall_mem_cons.2 ⟨subd17_3_111, List.forall_mem_cons.2 ⟨subd17_3_112, List.forall_mem_cons.2 ⟨subd17_3_113, List.forall_mem_cons.2 ⟨subd17_3_114, List.forall_mem_cons.2 ⟨subd17_3_115, List.forall_mem_cons.2 ⟨subd17_3_116, List.forall_mem_cons.2 ⟨subd17_3_117, List.forall_mem_cons.2 ⟨subd17_3_118, List.forall_mem_cons.2 ⟨subd17_3_119, List.forall_mem_cons.2 ⟨subd17_3_120, List.forall_mem_cons.2 ⟨subd17_3_121, List.forall_mem_cons.2 ⟨subd17_3_122, List.forall_mem_cons.2 ⟨subd17_3_123, List.forall_mem_cons.2 ⟨subd17_3_124, List.forall_mem_cons.2 ⟨subd17_3_125, List.forall_mem_cons.2 ⟨subd17_3_126, List.forall_mem_cons.2 ⟨subd17_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_128 : subd17_3 [-3, -2, -5] = true := by decide +kernel
theorem subd17_3_129 : subd17_3 [-3, -2, -4] = true := by decide +kernel
theorem subd17_3_130 : subd17_3 [-3, -2, -3] = true := by decide +kernel
theorem subd17_3_131 : subd17_3 [-3, -2, -2] = true := by decide +kernel
theorem subd17_3_132 : subd17_3 [-3, -2, -1] = true := by decide +kernel
theorem subd17_3_133 : subd17_3 [-3, -2, 0] = true := by decide +kernel
theorem subd17_3_134 : subd17_3 [-3, -2, 1] = true := by decide +kernel
theorem subd17_3_135 : subd17_3 [-3, -2, 2] = true := by decide +kernel
theorem subd17_3_136 : subd17_3 [-3, -2, 3] = true := by decide +kernel
theorem subd17_3_137 : subd17_3 [-3, -2, 4] = true := by decide +kernel
theorem subd17_3_138 : subd17_3 [-3, -2, 5] = true := by decide +kernel
theorem subd17_3_139 : subd17_3 [-3, -2, 6] = true := by decide +kernel
theorem subd17_3_140 : subd17_3 [-3, -2, 7] = true := by decide +kernel
theorem subd17_3_141 : subd17_3 [-3, -2, 8] = true := by decide +kernel
theorem subd17_3_142 : subd17_3 [-3, -1, -7] = true := by decide +kernel
theorem subd17_3_143 : subd17_3 [-3, -1, -6] = true := by decide +kernel
theorem subd17_3_144 : subd17_3 [-3, -1, -5] = true := by decide +kernel
theorem subd17_3_145 : subd17_3 [-3, -1, -4] = true := by decide +kernel
theorem subd17_3_146 : subd17_3 [-3, -1, -3] = true := by decide +kernel
theorem subd17_3_147 : subd17_3 [-3, -1, -2] = true := by decide +kernel
theorem subd17_3_148 : subd17_3 [-3, -1, -1] = true := by decide +kernel
theorem subd17_3_149 : subd17_3 [-3, -1, 0] = true := by decide +kernel
theorem subd17_3_150 : subd17_3 [-3, -1, 1] = true := by decide +kernel
theorem subd17_3_151 : subd17_3 [-3, -1, 2] = true := by decide +kernel
theorem subd17_3_152 : subd17_3 [-3, -1, 3] = true := by decide +kernel
theorem subd17_3_153 : subd17_3 [-3, -1, 4] = true := by decide +kernel
theorem subd17_3_154 : subd17_3 [-3, -1, 5] = true := by decide +kernel
theorem subd17_3_155 : subd17_3 [-3, -1, 6] = true := by decide +kernel
theorem subd17_3_156 : subd17_3 [-3, -1, 7] = true := by decide +kernel
theorem subd17_3_157 : subd17_3 [-3, -1, 8] = true := by decide +kernel
theorem subd17_3_158 : subd17_3 [-3, 0, -7] = true := by decide +kernel
theorem subd17_3_159 : subd17_3 [-3, 0, -6] = true := by decide +kernel
theorem sbd17_3_4 : ∀ q ∈ blkd17_3_4, subd17_3 q = true := by
  unfold blkd17_3_4
  exact List.forall_mem_cons.2 ⟨subd17_3_128, List.forall_mem_cons.2 ⟨subd17_3_129, List.forall_mem_cons.2 ⟨subd17_3_130, List.forall_mem_cons.2 ⟨subd17_3_131, List.forall_mem_cons.2 ⟨subd17_3_132, List.forall_mem_cons.2 ⟨subd17_3_133, List.forall_mem_cons.2 ⟨subd17_3_134, List.forall_mem_cons.2 ⟨subd17_3_135, List.forall_mem_cons.2 ⟨subd17_3_136, List.forall_mem_cons.2 ⟨subd17_3_137, List.forall_mem_cons.2 ⟨subd17_3_138, List.forall_mem_cons.2 ⟨subd17_3_139, List.forall_mem_cons.2 ⟨subd17_3_140, List.forall_mem_cons.2 ⟨subd17_3_141, List.forall_mem_cons.2 ⟨subd17_3_142, List.forall_mem_cons.2 ⟨subd17_3_143, List.forall_mem_cons.2 ⟨subd17_3_144, List.forall_mem_cons.2 ⟨subd17_3_145, List.forall_mem_cons.2 ⟨subd17_3_146, List.forall_mem_cons.2 ⟨subd17_3_147, List.forall_mem_cons.2 ⟨subd17_3_148, List.forall_mem_cons.2 ⟨subd17_3_149, List.forall_mem_cons.2 ⟨subd17_3_150, List.forall_mem_cons.2 ⟨subd17_3_151, List.forall_mem_cons.2 ⟨subd17_3_152, List.forall_mem_cons.2 ⟨subd17_3_153, List.forall_mem_cons.2 ⟨subd17_3_154, List.forall_mem_cons.2 ⟨subd17_3_155, List.forall_mem_cons.2 ⟨subd17_3_156, List.forall_mem_cons.2 ⟨subd17_3_157, List.forall_mem_cons.2 ⟨subd17_3_158, List.forall_mem_cons.2 ⟨subd17_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_160 : subd17_3 [-3, 0, -5] = true := by decide +kernel
theorem subd17_3_161 : subd17_3 [-3, 0, -4] = true := by decide +kernel
theorem subd17_3_162 : subd17_3 [-3, 0, -3] = true := by decide +kernel
theorem subd17_3_163 : subd17_3 [-3, 0, -2] = true := by decide +kernel
theorem subd17_3_164 : subd17_3 [-3, 0, -1] = true := by decide +kernel
theorem subd17_3_165 : subd17_3 [-3, 0, 0] = true := by decide +kernel
theorem subd17_3_166 : subd17_3 [-3, 0, 1] = true := by decide +kernel
theorem subd17_3_167 : subd17_3 [-3, 0, 2] = true := by decide +kernel
theorem subd17_3_168 : subd17_3 [-3, 0, 3] = true := by decide +kernel
theorem subd17_3_169 : subd17_3 [-3, 0, 4] = true := by decide +kernel
theorem subd17_3_170 : subd17_3 [-3, 0, 5] = true := by decide +kernel
theorem subd17_3_171 : subd17_3 [-3, 0, 6] = true := by decide +kernel
theorem subd17_3_172 : subd17_3 [-3, 0, 7] = true := by decide +kernel
theorem subd17_3_173 : subd17_3 [-3, 0, 8] = true := by decide +kernel
theorem subd17_3_174 : subd17_3 [-3, 1, -6] = true := by decide +kernel
theorem subd17_3_175 : subd17_3 [-3, 1, -5] = true := by decide +kernel
theorem subd17_3_176 : subd17_3 [-3, 1, -4] = true := by decide +kernel
theorem subd17_3_177 : subd17_3 [-3, 1, -3] = true := by decide +kernel
theorem subd17_3_178 : subd17_3 [-3, 1, -2] = true := by decide +kernel
theorem subd17_3_179 : subd17_3 [-3, 1, -1] = true := by decide +kernel
theorem subd17_3_180 : subd17_3 [-3, 1, 0] = true := by decide +kernel
theorem subd17_3_181 : subd17_3 [-3, 1, 1] = true := by decide +kernel
theorem subd17_3_182 : subd17_3 [-3, 1, 2] = true := by decide +kernel
theorem subd17_3_183 : subd17_3 [-3, 1, 3] = true := by decide +kernel
theorem subd17_3_184 : subd17_3 [-3, 1, 4] = true := by decide +kernel
theorem subd17_3_185 : subd17_3 [-3, 1, 5] = true := by decide +kernel
theorem subd17_3_186 : subd17_3 [-3, 1, 6] = true := by decide +kernel
theorem subd17_3_187 : subd17_3 [-3, 1, 7] = true := by decide +kernel
theorem subd17_3_188 : subd17_3 [-3, 1, 8] = true := by decide +kernel
theorem subd17_3_189 : subd17_3 [-3, 2, -6] = true := by decide +kernel
theorem subd17_3_190 : subd17_3 [-3, 2, -5] = true := by decide +kernel
theorem subd17_3_191 : subd17_3 [-3, 2, -4] = true := by decide +kernel
theorem sbd17_3_5 : ∀ q ∈ blkd17_3_5, subd17_3 q = true := by
  unfold blkd17_3_5
  exact List.forall_mem_cons.2 ⟨subd17_3_160, List.forall_mem_cons.2 ⟨subd17_3_161, List.forall_mem_cons.2 ⟨subd17_3_162, List.forall_mem_cons.2 ⟨subd17_3_163, List.forall_mem_cons.2 ⟨subd17_3_164, List.forall_mem_cons.2 ⟨subd17_3_165, List.forall_mem_cons.2 ⟨subd17_3_166, List.forall_mem_cons.2 ⟨subd17_3_167, List.forall_mem_cons.2 ⟨subd17_3_168, List.forall_mem_cons.2 ⟨subd17_3_169, List.forall_mem_cons.2 ⟨subd17_3_170, List.forall_mem_cons.2 ⟨subd17_3_171, List.forall_mem_cons.2 ⟨subd17_3_172, List.forall_mem_cons.2 ⟨subd17_3_173, List.forall_mem_cons.2 ⟨subd17_3_174, List.forall_mem_cons.2 ⟨subd17_3_175, List.forall_mem_cons.2 ⟨subd17_3_176, List.forall_mem_cons.2 ⟨subd17_3_177, List.forall_mem_cons.2 ⟨subd17_3_178, List.forall_mem_cons.2 ⟨subd17_3_179, List.forall_mem_cons.2 ⟨subd17_3_180, List.forall_mem_cons.2 ⟨subd17_3_181, List.forall_mem_cons.2 ⟨subd17_3_182, List.forall_mem_cons.2 ⟨subd17_3_183, List.forall_mem_cons.2 ⟨subd17_3_184, List.forall_mem_cons.2 ⟨subd17_3_185, List.forall_mem_cons.2 ⟨subd17_3_186, List.forall_mem_cons.2 ⟨subd17_3_187, List.forall_mem_cons.2 ⟨subd17_3_188, List.forall_mem_cons.2 ⟨subd17_3_189, List.forall_mem_cons.2 ⟨subd17_3_190, List.forall_mem_cons.2 ⟨subd17_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_192 : subd17_3 [-3, 2, -3] = true := by decide +kernel
theorem subd17_3_193 : subd17_3 [-3, 2, -2] = true := by decide +kernel
theorem subd17_3_194 : subd17_3 [-3, 2, -1] = true := by decide +kernel
theorem subd17_3_195 : subd17_3 [-3, 2, 0] = true := by decide +kernel
theorem subd17_3_196 : subd17_3 [-3, 2, 1] = true := by decide +kernel
theorem subd17_3_197 : subd17_3 [-3, 2, 2] = true := by decide +kernel
theorem subd17_3_198 : subd17_3 [-3, 2, 3] = true := by decide +kernel
theorem subd17_3_199 : subd17_3 [-3, 2, 4] = true := by decide +kernel
theorem subd17_3_200 : subd17_3 [-3, 2, 5] = true := by decide +kernel
theorem subd17_3_201 : subd17_3 [-3, 2, 6] = true := by decide +kernel
theorem subd17_3_202 : subd17_3 [-3, 2, 7] = true := by decide +kernel
theorem subd17_3_203 : subd17_3 [-3, 2, 8] = true := by decide +kernel
theorem subd17_3_204 : subd17_3 [-3, 3, -5] = true := by decide +kernel
theorem subd17_3_205 : subd17_3 [-3, 3, -4] = true := by decide +kernel
theorem subd17_3_206 : subd17_3 [-3, 3, -3] = true := by decide +kernel
theorem subd17_3_207 : subd17_3 [-3, 3, -2] = true := by decide +kernel
theorem subd17_3_208 : subd17_3 [-3, 3, -1] = true := by decide +kernel
theorem subd17_3_209 : subd17_3 [-3, 3, 0] = true := by decide +kernel
theorem subd17_3_210 : subd17_3 [-3, 3, 1] = true := by decide +kernel
theorem subd17_3_211 : subd17_3 [-3, 3, 2] = true := by decide +kernel
theorem subd17_3_212 : subd17_3 [-3, 3, 3] = true := by decide +kernel
theorem subd17_3_213 : subd17_3 [-3, 3, 4] = true := by decide +kernel
theorem subd17_3_214 : subd17_3 [-3, 3, 5] = true := by decide +kernel
theorem subd17_3_215 : subd17_3 [-3, 3, 6] = true := by decide +kernel
theorem subd17_3_216 : subd17_3 [-3, 3, 7] = true := by decide +kernel
theorem subd17_3_217 : subd17_3 [-3, 4] = true := by decide +kernel
theorem subd17_3_218 : subd17_3 [-3, 5] = true := by decide +kernel
theorem subd17_3_219 : subd17_3 [-2, -8] = true := by decide +kernel
theorem subd17_3_220 : subd17_3 [-2, -7] = true := by decide +kernel
theorem subd17_3_221 : subd17_3 [-2, -6] = true := by decide +kernel
theorem subd17_3_222 : subd17_3 [-2, -5] = true := by decide +kernel
theorem subd17_3_223 : subd17_3 [-2, -4, -7] = true := by decide +kernel
theorem sbd17_3_6 : ∀ q ∈ blkd17_3_6, subd17_3 q = true := by
  unfold blkd17_3_6
  exact List.forall_mem_cons.2 ⟨subd17_3_192, List.forall_mem_cons.2 ⟨subd17_3_193, List.forall_mem_cons.2 ⟨subd17_3_194, List.forall_mem_cons.2 ⟨subd17_3_195, List.forall_mem_cons.2 ⟨subd17_3_196, List.forall_mem_cons.2 ⟨subd17_3_197, List.forall_mem_cons.2 ⟨subd17_3_198, List.forall_mem_cons.2 ⟨subd17_3_199, List.forall_mem_cons.2 ⟨subd17_3_200, List.forall_mem_cons.2 ⟨subd17_3_201, List.forall_mem_cons.2 ⟨subd17_3_202, List.forall_mem_cons.2 ⟨subd17_3_203, List.forall_mem_cons.2 ⟨subd17_3_204, List.forall_mem_cons.2 ⟨subd17_3_205, List.forall_mem_cons.2 ⟨subd17_3_206, List.forall_mem_cons.2 ⟨subd17_3_207, List.forall_mem_cons.2 ⟨subd17_3_208, List.forall_mem_cons.2 ⟨subd17_3_209, List.forall_mem_cons.2 ⟨subd17_3_210, List.forall_mem_cons.2 ⟨subd17_3_211, List.forall_mem_cons.2 ⟨subd17_3_212, List.forall_mem_cons.2 ⟨subd17_3_213, List.forall_mem_cons.2 ⟨subd17_3_214, List.forall_mem_cons.2 ⟨subd17_3_215, List.forall_mem_cons.2 ⟨subd17_3_216, List.forall_mem_cons.2 ⟨subd17_3_217, List.forall_mem_cons.2 ⟨subd17_3_218, List.forall_mem_cons.2 ⟨subd17_3_219, List.forall_mem_cons.2 ⟨subd17_3_220, List.forall_mem_cons.2 ⟨subd17_3_221, List.forall_mem_cons.2 ⟨subd17_3_222, List.forall_mem_cons.2 ⟨subd17_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_224 : subd17_3 [-2, -4, -6] = true := by decide +kernel
theorem subd17_3_225 : subd17_3 [-2, -4, -5] = true := by decide +kernel
theorem subd17_3_226 : subd17_3 [-2, -4, -4] = true := by decide +kernel
theorem subd17_3_227 : subd17_3 [-2, -4, -3] = true := by decide +kernel
theorem subd17_3_228 : subd17_3 [-2, -4, -2] = true := by decide +kernel
theorem subd17_3_229 : subd17_3 [-2, -4, -1] = true := by decide +kernel
theorem subd17_3_230 : subd17_3 [-2, -4, 0] = true := by decide +kernel
theorem subd17_3_231 : subd17_3 [-2, -4, 1] = true := by decide +kernel
theorem subd17_3_232 : subd17_3 [-2, -4, 2] = true := by decide +kernel
theorem subd17_3_233 : subd17_3 [-2, -4, 3] = true := by decide +kernel
theorem subd17_3_234 : subd17_3 [-2, -4, 4] = true := by decide +kernel
theorem subd17_3_235 : subd17_3 [-2, -4, 5] = true := by decide +kernel
theorem subd17_3_236 : subd17_3 [-2, -4, 6] = true := by decide +kernel
theorem subd17_3_237 : subd17_3 [-2, -4, 7] = true := by decide +kernel
theorem subd17_3_238 : subd17_3 [-2, -3, -7] = true := by decide +kernel
theorem subd17_3_239 : subd17_3 [-2, -3, -6] = true := by decide +kernel
theorem subd17_3_240 : subd17_3 [-2, -3, -5] = true := by decide +kernel
theorem subd17_3_241 : subd17_3 [-2, -3, -4] = true := by decide +kernel
theorem subd17_3_242 : subd17_3 [-2, -3, -3] = true := by decide +kernel
theorem subd17_3_243 : subd17_3 [-2, -3, -2] = true := by decide +kernel
theorem subd17_3_244 : subd17_3 [-2, -3, -1] = true := by decide +kernel
theorem subd17_3_245 : subd17_3 [-2, -3, 0] = true := by decide +kernel
theorem subd17_3_246 : subd17_3 [-2, -3, 1] = true := by decide +kernel
theorem subd17_3_247 : subd17_3 [-2, -3, 2] = true := by decide +kernel
theorem subd17_3_248 : subd17_3 [-2, -3, 3] = true := by decide +kernel
theorem subd17_3_249 : subd17_3 [-2, -3, 4] = true := by decide +kernel
theorem subd17_3_250 : subd17_3 [-2, -3, 5] = true := by decide +kernel
theorem subd17_3_251 : subd17_3 [-2, -3, 6] = true := by decide +kernel
theorem subd17_3_252 : subd17_3 [-2, -3, 7] = true := by decide +kernel
theorem subd17_3_253 : subd17_3 [-2, -3, 8] = true := by decide +kernel
theorem subd17_3_254 : subd17_3 [-2, -2, -8] = true := by decide +kernel
theorem subd17_3_255 : subd17_3 [-2, -2, -7] = true := by decide +kernel
theorem sbd17_3_7 : ∀ q ∈ blkd17_3_7, subd17_3 q = true := by
  unfold blkd17_3_7
  exact List.forall_mem_cons.2 ⟨subd17_3_224, List.forall_mem_cons.2 ⟨subd17_3_225, List.forall_mem_cons.2 ⟨subd17_3_226, List.forall_mem_cons.2 ⟨subd17_3_227, List.forall_mem_cons.2 ⟨subd17_3_228, List.forall_mem_cons.2 ⟨subd17_3_229, List.forall_mem_cons.2 ⟨subd17_3_230, List.forall_mem_cons.2 ⟨subd17_3_231, List.forall_mem_cons.2 ⟨subd17_3_232, List.forall_mem_cons.2 ⟨subd17_3_233, List.forall_mem_cons.2 ⟨subd17_3_234, List.forall_mem_cons.2 ⟨subd17_3_235, List.forall_mem_cons.2 ⟨subd17_3_236, List.forall_mem_cons.2 ⟨subd17_3_237, List.forall_mem_cons.2 ⟨subd17_3_238, List.forall_mem_cons.2 ⟨subd17_3_239, List.forall_mem_cons.2 ⟨subd17_3_240, List.forall_mem_cons.2 ⟨subd17_3_241, List.forall_mem_cons.2 ⟨subd17_3_242, List.forall_mem_cons.2 ⟨subd17_3_243, List.forall_mem_cons.2 ⟨subd17_3_244, List.forall_mem_cons.2 ⟨subd17_3_245, List.forall_mem_cons.2 ⟨subd17_3_246, List.forall_mem_cons.2 ⟨subd17_3_247, List.forall_mem_cons.2 ⟨subd17_3_248, List.forall_mem_cons.2 ⟨subd17_3_249, List.forall_mem_cons.2 ⟨subd17_3_250, List.forall_mem_cons.2 ⟨subd17_3_251, List.forall_mem_cons.2 ⟨subd17_3_252, List.forall_mem_cons.2 ⟨subd17_3_253, List.forall_mem_cons.2 ⟨subd17_3_254, List.forall_mem_cons.2 ⟨subd17_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_256 : subd17_3 [-2, -2, -6] = true := by decide +kernel
theorem subd17_3_257 : subd17_3 [-2, -2, -5] = true := by decide +kernel
theorem subd17_3_258 : subd17_3 [-2, -2, -4] = true := by decide +kernel
theorem subd17_3_259 : subd17_3 [-2, -2, -3] = true := by decide +kernel
theorem subd17_3_260 : subd17_3 [-2, -2, -2] = true := by decide +kernel
theorem subd17_3_261 : subd17_3 [-2, -2, -1] = true := by decide +kernel
theorem subd17_3_262 : subd17_3 [-2, -2, 0] = true := by decide +kernel
theorem subd17_3_263 : subd17_3 [-2, -2, 1] = true := by decide +kernel
theorem subd17_3_264 : subd17_3 [-2, -2, 2] = true := by decide +kernel
theorem subd17_3_265 : subd17_3 [-2, -2, 3] = true := by decide +kernel
theorem subd17_3_266 : subd17_3 [-2, -2, 4] = true := by decide +kernel
theorem subd17_3_267 : subd17_3 [-2, -2, 5] = true := by decide +kernel
theorem subd17_3_268 : subd17_3 [-2, -2, 6] = true := by decide +kernel
theorem subd17_3_269 : subd17_3 [-2, -2, 7] = true := by decide +kernel
theorem subd17_3_270 : subd17_3 [-2, -2, 8] = true := by decide +kernel
theorem subd17_3_271 : subd17_3 [-2, -1, -8] = true := by decide +kernel
theorem subd17_3_272 : subd17_3 [-2, -1, -7] = true := by decide +kernel
theorem subd17_3_273 : subd17_3 [-2, -1, -6] = true := by decide +kernel
theorem subd17_3_274 : subd17_3 [-2, -1, -5] = true := by decide +kernel
theorem subd17_3_275 : subd17_3 [-2, -1, -4] = true := by decide +kernel
theorem subd17_3_276 : subd17_3 [-2, -1, -3] = true := by decide +kernel
theorem subd17_3_277 : subd17_3 [-2, -1, -2] = true := by decide +kernel
theorem subd17_3_278 : subd17_3 [-2, -1, -1] = true := by decide +kernel
theorem subd17_3_279 : subd17_3 [-2, -1, 0] = true := by decide +kernel
theorem subd17_3_280 : subd17_3 [-2, -1, 1] = true := by decide +kernel
theorem subd17_3_281 : subd17_3 [-2, -1, 2] = true := by decide +kernel
theorem subd17_3_282 : subd17_3 [-2, -1, 3] = true := by decide +kernel
theorem subd17_3_283 : subd17_3 [-2, -1, 4] = true := by decide +kernel
theorem subd17_3_284 : subd17_3 [-2, -1, 5] = true := by decide +kernel
theorem subd17_3_285 : subd17_3 [-2, -1, 6] = true := by decide +kernel
theorem subd17_3_286 : subd17_3 [-2, -1, 7] = true := by decide +kernel
theorem subd17_3_287 : subd17_3 [-2, -1, 8] = true := by decide +kernel
theorem sbd17_3_8 : ∀ q ∈ blkd17_3_8, subd17_3 q = true := by
  unfold blkd17_3_8
  exact List.forall_mem_cons.2 ⟨subd17_3_256, List.forall_mem_cons.2 ⟨subd17_3_257, List.forall_mem_cons.2 ⟨subd17_3_258, List.forall_mem_cons.2 ⟨subd17_3_259, List.forall_mem_cons.2 ⟨subd17_3_260, List.forall_mem_cons.2 ⟨subd17_3_261, List.forall_mem_cons.2 ⟨subd17_3_262, List.forall_mem_cons.2 ⟨subd17_3_263, List.forall_mem_cons.2 ⟨subd17_3_264, List.forall_mem_cons.2 ⟨subd17_3_265, List.forall_mem_cons.2 ⟨subd17_3_266, List.forall_mem_cons.2 ⟨subd17_3_267, List.forall_mem_cons.2 ⟨subd17_3_268, List.forall_mem_cons.2 ⟨subd17_3_269, List.forall_mem_cons.2 ⟨subd17_3_270, List.forall_mem_cons.2 ⟨subd17_3_271, List.forall_mem_cons.2 ⟨subd17_3_272, List.forall_mem_cons.2 ⟨subd17_3_273, List.forall_mem_cons.2 ⟨subd17_3_274, List.forall_mem_cons.2 ⟨subd17_3_275, List.forall_mem_cons.2 ⟨subd17_3_276, List.forall_mem_cons.2 ⟨subd17_3_277, List.forall_mem_cons.2 ⟨subd17_3_278, List.forall_mem_cons.2 ⟨subd17_3_279, List.forall_mem_cons.2 ⟨subd17_3_280, List.forall_mem_cons.2 ⟨subd17_3_281, List.forall_mem_cons.2 ⟨subd17_3_282, List.forall_mem_cons.2 ⟨subd17_3_283, List.forall_mem_cons.2 ⟨subd17_3_284, List.forall_mem_cons.2 ⟨subd17_3_285, List.forall_mem_cons.2 ⟨subd17_3_286, List.forall_mem_cons.2 ⟨subd17_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_288 : subd17_3 [-2, 0, -8] = true := by decide +kernel
theorem subd17_3_289 : subd17_3 [-2, 0, -7] = true := by decide +kernel
theorem subd17_3_290 : subd17_3 [-2, 0, -6] = true := by decide +kernel
theorem subd17_3_291 : subd17_3 [-2, 0, -5] = true := by decide +kernel
theorem subd17_3_292 : subd17_3 [-2, 0, -4] = true := by decide +kernel
theorem subd17_3_293 : subd17_3 [-2, 0, -3] = true := by decide +kernel
theorem subd17_3_294 : subd17_3 [-2, 0, -2] = true := by decide +kernel
theorem subd17_3_295 : subd17_3 [-2, 0, -1] = true := by decide +kernel
theorem subd17_3_296 : subd17_3 [-2, 0, 0] = true := by decide +kernel
theorem subd17_3_297 : subd17_3 [-2, 0, 1] = true := by decide +kernel
theorem subd17_3_298 : subd17_3 [-2, 0, 2] = true := by decide +kernel
theorem subd17_3_299 : subd17_3 [-2, 0, 3] = true := by decide +kernel
theorem subd17_3_300 : subd17_3 [-2, 0, 4] = true := by decide +kernel
theorem subd17_3_301 : subd17_3 [-2, 0, 5] = true := by decide +kernel
theorem subd17_3_302 : subd17_3 [-2, 0, 6] = true := by decide +kernel
theorem subd17_3_303 : subd17_3 [-2, 0, 7] = true := by decide +kernel
theorem subd17_3_304 : subd17_3 [-2, 0, 8] = true := by decide +kernel
theorem subd17_3_305 : subd17_3 [-2, 1, -7] = true := by decide +kernel
theorem subd17_3_306 : subd17_3 [-2, 1, -6] = true := by decide +kernel
theorem subd17_3_307 : subd17_3 [-2, 1, -5] = true := by decide +kernel
theorem subd17_3_308 : subd17_3 [-2, 1, -4] = true := by decide +kernel
theorem subd17_3_309 : subd17_3 [-2, 1, -3] = true := by decide +kernel
theorem subd17_3_310 : subd17_3 [-2, 1, -2] = true := by decide +kernel
theorem subd17_3_311 : subd17_3 [-2, 1, -1] = true := by decide +kernel
theorem subd17_3_312 : subd17_3 [-2, 1, 0] = true := by decide +kernel
theorem subd17_3_313 : subd17_3 [-2, 1, 1] = true := by decide +kernel
theorem subd17_3_314 : subd17_3 [-2, 1, 2] = true := by decide +kernel
theorem subd17_3_315 : subd17_3 [-2, 1, 3] = true := by decide +kernel
theorem subd17_3_316 : subd17_3 [-2, 1, 4] = true := by decide +kernel
theorem subd17_3_317 : subd17_3 [-2, 1, 5] = true := by decide +kernel
theorem subd17_3_318 : subd17_3 [-2, 1, 6] = true := by decide +kernel
theorem subd17_3_319 : subd17_3 [-2, 1, 7] = true := by decide +kernel
theorem sbd17_3_9 : ∀ q ∈ blkd17_3_9, subd17_3 q = true := by
  unfold blkd17_3_9
  exact List.forall_mem_cons.2 ⟨subd17_3_288, List.forall_mem_cons.2 ⟨subd17_3_289, List.forall_mem_cons.2 ⟨subd17_3_290, List.forall_mem_cons.2 ⟨subd17_3_291, List.forall_mem_cons.2 ⟨subd17_3_292, List.forall_mem_cons.2 ⟨subd17_3_293, List.forall_mem_cons.2 ⟨subd17_3_294, List.forall_mem_cons.2 ⟨subd17_3_295, List.forall_mem_cons.2 ⟨subd17_3_296, List.forall_mem_cons.2 ⟨subd17_3_297, List.forall_mem_cons.2 ⟨subd17_3_298, List.forall_mem_cons.2 ⟨subd17_3_299, List.forall_mem_cons.2 ⟨subd17_3_300, List.forall_mem_cons.2 ⟨subd17_3_301, List.forall_mem_cons.2 ⟨subd17_3_302, List.forall_mem_cons.2 ⟨subd17_3_303, List.forall_mem_cons.2 ⟨subd17_3_304, List.forall_mem_cons.2 ⟨subd17_3_305, List.forall_mem_cons.2 ⟨subd17_3_306, List.forall_mem_cons.2 ⟨subd17_3_307, List.forall_mem_cons.2 ⟨subd17_3_308, List.forall_mem_cons.2 ⟨subd17_3_309, List.forall_mem_cons.2 ⟨subd17_3_310, List.forall_mem_cons.2 ⟨subd17_3_311, List.forall_mem_cons.2 ⟨subd17_3_312, List.forall_mem_cons.2 ⟨subd17_3_313, List.forall_mem_cons.2 ⟨subd17_3_314, List.forall_mem_cons.2 ⟨subd17_3_315, List.forall_mem_cons.2 ⟨subd17_3_316, List.forall_mem_cons.2 ⟨subd17_3_317, List.forall_mem_cons.2 ⟨subd17_3_318, List.forall_mem_cons.2 ⟨subd17_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_3_320 : subd17_3 [-2, 1, 8] = true := by decide +kernel
theorem subd17_3_321 : subd17_3 [-2, 2, -7] = true := by decide +kernel
theorem subd17_3_322 : subd17_3 [-2, 2, -6] = true := by decide +kernel
theorem subd17_3_323 : subd17_3 [-2, 2, -5] = true := by decide +kernel
theorem subd17_3_324 : subd17_3 [-2, 2, -4] = true := by decide +kernel
theorem subd17_3_325 : subd17_3 [-2, 2, -3] = true := by decide +kernel
theorem subd17_3_326 : subd17_3 [-2, 2, -2] = true := by decide +kernel
theorem subd17_3_327 : subd17_3 [-2, 2, -1] = true := by decide +kernel
theorem subd17_3_328 : subd17_3 [-2, 2, 0] = true := by decide +kernel
theorem subd17_3_329 : subd17_3 [-2, 2, 1] = true := by decide +kernel
theorem subd17_3_330 : subd17_3 [-2, 2, 2] = true := by decide +kernel
theorem subd17_3_331 : subd17_3 [-2, 2, 3] = true := by decide +kernel
theorem subd17_3_332 : subd17_3 [-2, 2, 4] = true := by decide +kernel
theorem subd17_3_333 : subd17_3 [-2, 2, 5] = true := by decide +kernel
theorem subd17_3_334 : subd17_3 [-2, 2, 6] = true := by decide +kernel
theorem subd17_3_335 : subd17_3 [-2, 2, 7] = true := by decide +kernel
theorem subd17_3_336 : subd17_3 [-2, 2, 8] = true := by decide +kernel
theorem subd17_3_337 : subd17_3 [-2, 3, -6] = true := by decide +kernel
theorem subd17_3_338 : subd17_3 [-2, 3, -5] = true := by decide +kernel
theorem subd17_3_339 : subd17_3 [-2, 3, -4] = true := by decide +kernel
theorem subd17_3_340 : subd17_3 [-2, 3, -3] = true := by decide +kernel
theorem subd17_3_341 : subd17_3 [-2, 3, -2] = true := by decide +kernel
theorem subd17_3_342 : subd17_3 [-2, 3, -1] = true := by decide +kernel
theorem subd17_3_343 : subd17_3 [-2, 3, 0] = true := by decide +kernel
theorem subd17_3_344 : subd17_3 [-2, 3, 1] = true := by decide +kernel
theorem subd17_3_345 : subd17_3 [-2, 3, 2] = true := by decide +kernel
theorem subd17_3_346 : subd17_3 [-2, 3, 3] = true := by decide +kernel
theorem subd17_3_347 : subd17_3 [-2, 3, 4] = true := by decide +kernel
theorem subd17_3_348 : subd17_3 [-2, 3, 5] = true := by decide +kernel
theorem subd17_3_349 : subd17_3 [-2, 3, 6] = true := by decide +kernel
theorem subd17_3_350 : subd17_3 [-2, 3, 7] = true := by decide +kernel
theorem subd17_3_351 : subd17_3 [-2, 3, 8] = true := by decide +kernel
theorem sbd17_3_10 : ∀ q ∈ blkd17_3_10, subd17_3 q = true := by
  unfold blkd17_3_10
  exact List.forall_mem_cons.2 ⟨subd17_3_320, List.forall_mem_cons.2 ⟨subd17_3_321, List.forall_mem_cons.2 ⟨subd17_3_322, List.forall_mem_cons.2 ⟨subd17_3_323, List.forall_mem_cons.2 ⟨subd17_3_324, List.forall_mem_cons.2 ⟨subd17_3_325, List.forall_mem_cons.2 ⟨subd17_3_326, List.forall_mem_cons.2 ⟨subd17_3_327, List.forall_mem_cons.2 ⟨subd17_3_328, List.forall_mem_cons.2 ⟨subd17_3_329, List.forall_mem_cons.2 ⟨subd17_3_330, List.forall_mem_cons.2 ⟨subd17_3_331, List.forall_mem_cons.2 ⟨subd17_3_332, List.forall_mem_cons.2 ⟨subd17_3_333, List.forall_mem_cons.2 ⟨subd17_3_334, List.forall_mem_cons.2 ⟨subd17_3_335, List.forall_mem_cons.2 ⟨subd17_3_336, List.forall_mem_cons.2 ⟨subd17_3_337, List.forall_mem_cons.2 ⟨subd17_3_338, List.forall_mem_cons.2 ⟨subd17_3_339, List.forall_mem_cons.2 ⟨subd17_3_340, List.forall_mem_cons.2 ⟨subd17_3_341, List.forall_mem_cons.2 ⟨subd17_3_342, List.forall_mem_cons.2 ⟨subd17_3_343, List.forall_mem_cons.2 ⟨subd17_3_344, List.forall_mem_cons.2 ⟨subd17_3_345, List.forall_mem_cons.2 ⟨subd17_3_346, List.forall_mem_cons.2 ⟨subd17_3_347, List.forall_mem_cons.2 ⟨subd17_3_348, List.forall_mem_cons.2 ⟨subd17_3_349, List.forall_mem_cons.2 ⟨subd17_3_350, List.forall_mem_cons.2 ⟨subd17_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
