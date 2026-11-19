import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_0 : subd7_3 [-7] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-6, -6] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-6, -5] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-6, -4] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-6, -3] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-6, -2] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-6, -1] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-6, 0] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-6, 1] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-6, 2] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-6, 3] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-6, 4] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-6, 5] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-5, -7] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-5, -6] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-5, -5] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-5, -4] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-5, -3] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-5, -2] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-5, -1] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-5, 0, -9] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-5, 0, -8] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-5, 0, -7] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-5, 0, -6] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-5, 0, -5] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-5, 0, -4] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-5, 0, -3] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-5, 0, -2] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-5, 0, -1] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [-5, 0, 0] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [-5, 0, 1] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [-5, 0, 2] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [-5, 0, 3] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [-5, 1] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [-5, 2] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [-5, 3] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [-5, 4] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [-5, 5] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [-5, 6] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [-4, -8] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [-4, -7] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [-4, -6] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [-4, -5] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [-4, -4] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [-4, -3, -8] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [-4, -3, -7] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [-4, -3, -6] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [-4, -3, -5] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [-4, -3, -4] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [-4, -3, -3] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [-4, -3, -2] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [-4, -3, -1] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [-4, -3, 0] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [-4, -3, 1] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [-4, -3, 2] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [-4, -3, 3] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [-4, -3, 4] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [-4, -2, -9] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [-4, -2, -8] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [-4, -2, -7] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [-4, -2, -6] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [-4, -2, -5] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [-4, -2, -4] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [-4, -2, -3] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_64 : subd7_3 [-4, -2, -2] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [-4, -2, -1] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [-4, -2, 0] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [-4, -2, 1] = true := by decide +kernel
theorem subd7_3_68 : subd7_3 [-4, -2, 2] = true := by decide +kernel
theorem subd7_3_69 : subd7_3 [-4, -2, 3] = true := by decide +kernel
theorem subd7_3_70 : subd7_3 [-4, -2, 4] = true := by decide +kernel
theorem subd7_3_71 : subd7_3 [-4, -1, -9] = true := by decide +kernel
theorem subd7_3_72 : subd7_3 [-4, -1, -8] = true := by decide +kernel
theorem subd7_3_73 : subd7_3 [-4, -1, -7] = true := by decide +kernel
theorem subd7_3_74 : subd7_3 [-4, -1, -6] = true := by decide +kernel
theorem subd7_3_75 : subd7_3 [-4, -1, -5] = true := by decide +kernel
theorem subd7_3_76 : subd7_3 [-4, -1, -4] = true := by decide +kernel
theorem subd7_3_77 : subd7_3 [-4, -1, -3] = true := by decide +kernel
theorem subd7_3_78 : subd7_3 [-4, -1, -2] = true := by decide +kernel
theorem subd7_3_79 : subd7_3 [-4, -1, -1] = true := by decide +kernel
theorem subd7_3_80 : subd7_3 [-4, -1, 0] = true := by decide +kernel
theorem subd7_3_81 : subd7_3 [-4, -1, 1] = true := by decide +kernel
theorem subd7_3_82 : subd7_3 [-4, -1, 2] = true := by decide +kernel
theorem subd7_3_83 : subd7_3 [-4, -1, 3] = true := by decide +kernel
theorem subd7_3_84 : subd7_3 [-4, -1, 4] = true := by decide +kernel
theorem subd7_3_85 : subd7_3 [-4, 0, -9] = true := by decide +kernel
theorem subd7_3_86 : subd7_3 [-4, 0, -8] = true := by decide +kernel
theorem subd7_3_87 : subd7_3 [-4, 0, -7] = true := by decide +kernel
theorem subd7_3_88 : subd7_3 [-4, 0, -6] = true := by decide +kernel
theorem subd7_3_89 : subd7_3 [-4, 0, -5] = true := by decide +kernel
theorem subd7_3_90 : subd7_3 [-4, 0, -4] = true := by decide +kernel
theorem subd7_3_91 : subd7_3 [-4, 0, -3] = true := by decide +kernel
theorem subd7_3_92 : subd7_3 [-4, 0, -2] = true := by decide +kernel
theorem subd7_3_93 : subd7_3 [-4, 0, -1] = true := by decide +kernel
theorem subd7_3_94 : subd7_3 [-4, 0, 0] = true := by decide +kernel
theorem subd7_3_95 : subd7_3 [-4, 0, 1] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_cons.2 ⟨subd7_3_68, List.forall_mem_cons.2 ⟨subd7_3_69, List.forall_mem_cons.2 ⟨subd7_3_70, List.forall_mem_cons.2 ⟨subd7_3_71, List.forall_mem_cons.2 ⟨subd7_3_72, List.forall_mem_cons.2 ⟨subd7_3_73, List.forall_mem_cons.2 ⟨subd7_3_74, List.forall_mem_cons.2 ⟨subd7_3_75, List.forall_mem_cons.2 ⟨subd7_3_76, List.forall_mem_cons.2 ⟨subd7_3_77, List.forall_mem_cons.2 ⟨subd7_3_78, List.forall_mem_cons.2 ⟨subd7_3_79, List.forall_mem_cons.2 ⟨subd7_3_80, List.forall_mem_cons.2 ⟨subd7_3_81, List.forall_mem_cons.2 ⟨subd7_3_82, List.forall_mem_cons.2 ⟨subd7_3_83, List.forall_mem_cons.2 ⟨subd7_3_84, List.forall_mem_cons.2 ⟨subd7_3_85, List.forall_mem_cons.2 ⟨subd7_3_86, List.forall_mem_cons.2 ⟨subd7_3_87, List.forall_mem_cons.2 ⟨subd7_3_88, List.forall_mem_cons.2 ⟨subd7_3_89, List.forall_mem_cons.2 ⟨subd7_3_90, List.forall_mem_cons.2 ⟨subd7_3_91, List.forall_mem_cons.2 ⟨subd7_3_92, List.forall_mem_cons.2 ⟨subd7_3_93, List.forall_mem_cons.2 ⟨subd7_3_94, List.forall_mem_cons.2 ⟨subd7_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_96 : subd7_3 [-4, 0, 2] = true := by decide +kernel
theorem subd7_3_97 : subd7_3 [-4, 0, 3] = true := by decide +kernel
theorem subd7_3_98 : subd7_3 [-4, 0, 4] = true := by decide +kernel
theorem subd7_3_99 : subd7_3 [-4, 1, -9] = true := by decide +kernel
theorem subd7_3_100 : subd7_3 [-4, 1, -8] = true := by decide +kernel
theorem subd7_3_101 : subd7_3 [-4, 1, -7] = true := by decide +kernel
theorem subd7_3_102 : subd7_3 [-4, 1, -6] = true := by decide +kernel
theorem subd7_3_103 : subd7_3 [-4, 1, -5] = true := by decide +kernel
theorem subd7_3_104 : subd7_3 [-4, 1, -4] = true := by decide +kernel
theorem subd7_3_105 : subd7_3 [-4, 1, -3] = true := by decide +kernel
theorem subd7_3_106 : subd7_3 [-4, 1, -2] = true := by decide +kernel
theorem subd7_3_107 : subd7_3 [-4, 1, -1] = true := by decide +kernel
theorem subd7_3_108 : subd7_3 [-4, 1, 0] = true := by decide +kernel
theorem subd7_3_109 : subd7_3 [-4, 1, 1] = true := by decide +kernel
theorem subd7_3_110 : subd7_3 [-4, 1, 2] = true := by decide +kernel
theorem subd7_3_111 : subd7_3 [-4, 1, 3] = true := by decide +kernel
theorem subd7_3_112 : subd7_3 [-4, 1, 4] = true := by decide +kernel
theorem subd7_3_113 : subd7_3 [-4, 2, -9] = true := by decide +kernel
theorem subd7_3_114 : subd7_3 [-4, 2, -8] = true := by decide +kernel
theorem subd7_3_115 : subd7_3 [-4, 2, -7] = true := by decide +kernel
theorem subd7_3_116 : subd7_3 [-4, 2, -6] = true := by decide +kernel
theorem subd7_3_117 : subd7_3 [-4, 2, -5] = true := by decide +kernel
theorem subd7_3_118 : subd7_3 [-4, 2, -4] = true := by decide +kernel
theorem subd7_3_119 : subd7_3 [-4, 2, -3] = true := by decide +kernel
theorem subd7_3_120 : subd7_3 [-4, 2, -2] = true := by decide +kernel
theorem subd7_3_121 : subd7_3 [-4, 2, -1] = true := by decide +kernel
theorem subd7_3_122 : subd7_3 [-4, 2, 0] = true := by decide +kernel
theorem subd7_3_123 : subd7_3 [-4, 2, 1] = true := by decide +kernel
theorem subd7_3_124 : subd7_3 [-4, 2, 2] = true := by decide +kernel
theorem subd7_3_125 : subd7_3 [-4, 2, 3] = true := by decide +kernel
theorem subd7_3_126 : subd7_3 [-4, 2, 4] = true := by decide +kernel
theorem subd7_3_127 : subd7_3 [-4, 3, -9] = true := by decide +kernel
theorem sbd7_3_3 : ∀ q ∈ blkd7_3_3, subd7_3 q = true := by
  unfold blkd7_3_3
  exact List.forall_mem_cons.2 ⟨subd7_3_96, List.forall_mem_cons.2 ⟨subd7_3_97, List.forall_mem_cons.2 ⟨subd7_3_98, List.forall_mem_cons.2 ⟨subd7_3_99, List.forall_mem_cons.2 ⟨subd7_3_100, List.forall_mem_cons.2 ⟨subd7_3_101, List.forall_mem_cons.2 ⟨subd7_3_102, List.forall_mem_cons.2 ⟨subd7_3_103, List.forall_mem_cons.2 ⟨subd7_3_104, List.forall_mem_cons.2 ⟨subd7_3_105, List.forall_mem_cons.2 ⟨subd7_3_106, List.forall_mem_cons.2 ⟨subd7_3_107, List.forall_mem_cons.2 ⟨subd7_3_108, List.forall_mem_cons.2 ⟨subd7_3_109, List.forall_mem_cons.2 ⟨subd7_3_110, List.forall_mem_cons.2 ⟨subd7_3_111, List.forall_mem_cons.2 ⟨subd7_3_112, List.forall_mem_cons.2 ⟨subd7_3_113, List.forall_mem_cons.2 ⟨subd7_3_114, List.forall_mem_cons.2 ⟨subd7_3_115, List.forall_mem_cons.2 ⟨subd7_3_116, List.forall_mem_cons.2 ⟨subd7_3_117, List.forall_mem_cons.2 ⟨subd7_3_118, List.forall_mem_cons.2 ⟨subd7_3_119, List.forall_mem_cons.2 ⟨subd7_3_120, List.forall_mem_cons.2 ⟨subd7_3_121, List.forall_mem_cons.2 ⟨subd7_3_122, List.forall_mem_cons.2 ⟨subd7_3_123, List.forall_mem_cons.2 ⟨subd7_3_124, List.forall_mem_cons.2 ⟨subd7_3_125, List.forall_mem_cons.2 ⟨subd7_3_126, List.forall_mem_cons.2 ⟨subd7_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_128 : subd7_3 [-4, 3, -8] = true := by decide +kernel
theorem subd7_3_129 : subd7_3 [-4, 3, -7] = true := by decide +kernel
theorem subd7_3_130 : subd7_3 [-4, 3, -6] = true := by decide +kernel
theorem subd7_3_131 : subd7_3 [-4, 3, -5] = true := by decide +kernel
theorem subd7_3_132 : subd7_3 [-4, 3, -4] = true := by decide +kernel
theorem subd7_3_133 : subd7_3 [-4, 3, -3] = true := by decide +kernel
theorem subd7_3_134 : subd7_3 [-4, 3, -2] = true := by decide +kernel
theorem subd7_3_135 : subd7_3 [-4, 3, -1] = true := by decide +kernel
theorem subd7_3_136 : subd7_3 [-4, 3, 0] = true := by decide +kernel
theorem subd7_3_137 : subd7_3 [-4, 3, 1] = true := by decide +kernel
theorem subd7_3_138 : subd7_3 [-4, 3, 2] = true := by decide +kernel
theorem subd7_3_139 : subd7_3 [-4, 3, 3] = true := by decide +kernel
theorem subd7_3_140 : subd7_3 [-4, 3, 4] = true := by decide +kernel
theorem subd7_3_141 : subd7_3 [-4, 4] = true := by decide +kernel
theorem subd7_3_142 : subd7_3 [-4, 5] = true := by decide +kernel
theorem subd7_3_143 : subd7_3 [-4, 6] = true := by decide +kernel
theorem subd7_3_144 : subd7_3 [-4, 7] = true := by decide +kernel
theorem subd7_3_145 : subd7_3 [-3, -9] = true := by decide +kernel
theorem subd7_3_146 : subd7_3 [-3, -8] = true := by decide +kernel
theorem subd7_3_147 : subd7_3 [-3, -7] = true := by decide +kernel
theorem subd7_3_148 : subd7_3 [-3, -6] = true := by decide +kernel
theorem subd7_3_149 : subd7_3 [-3, -5] = true := by decide +kernel
theorem subd7_3_150 : subd7_3 [-3, -4, -8] = true := by decide +kernel
theorem subd7_3_151 : subd7_3 [-3, -4, -7] = true := by decide +kernel
theorem subd7_3_152 : subd7_3 [-3, -4, -6] = true := by decide +kernel
theorem subd7_3_153 : subd7_3 [-3, -4, -5] = true := by decide +kernel
theorem subd7_3_154 : subd7_3 [-3, -4, -4] = true := by decide +kernel
theorem subd7_3_155 : subd7_3 [-3, -4, -3] = true := by decide +kernel
theorem subd7_3_156 : subd7_3 [-3, -4, -2] = true := by decide +kernel
theorem subd7_3_157 : subd7_3 [-3, -4, -1] = true := by decide +kernel
theorem subd7_3_158 : subd7_3 [-3, -4, 0] = true := by decide +kernel
theorem subd7_3_159 : subd7_3 [-3, -4, 1] = true := by decide +kernel
theorem sbd7_3_4 : ∀ q ∈ blkd7_3_4, subd7_3 q = true := by
  unfold blkd7_3_4
  exact List.forall_mem_cons.2 ⟨subd7_3_128, List.forall_mem_cons.2 ⟨subd7_3_129, List.forall_mem_cons.2 ⟨subd7_3_130, List.forall_mem_cons.2 ⟨subd7_3_131, List.forall_mem_cons.2 ⟨subd7_3_132, List.forall_mem_cons.2 ⟨subd7_3_133, List.forall_mem_cons.2 ⟨subd7_3_134, List.forall_mem_cons.2 ⟨subd7_3_135, List.forall_mem_cons.2 ⟨subd7_3_136, List.forall_mem_cons.2 ⟨subd7_3_137, List.forall_mem_cons.2 ⟨subd7_3_138, List.forall_mem_cons.2 ⟨subd7_3_139, List.forall_mem_cons.2 ⟨subd7_3_140, List.forall_mem_cons.2 ⟨subd7_3_141, List.forall_mem_cons.2 ⟨subd7_3_142, List.forall_mem_cons.2 ⟨subd7_3_143, List.forall_mem_cons.2 ⟨subd7_3_144, List.forall_mem_cons.2 ⟨subd7_3_145, List.forall_mem_cons.2 ⟨subd7_3_146, List.forall_mem_cons.2 ⟨subd7_3_147, List.forall_mem_cons.2 ⟨subd7_3_148, List.forall_mem_cons.2 ⟨subd7_3_149, List.forall_mem_cons.2 ⟨subd7_3_150, List.forall_mem_cons.2 ⟨subd7_3_151, List.forall_mem_cons.2 ⟨subd7_3_152, List.forall_mem_cons.2 ⟨subd7_3_153, List.forall_mem_cons.2 ⟨subd7_3_154, List.forall_mem_cons.2 ⟨subd7_3_155, List.forall_mem_cons.2 ⟨subd7_3_156, List.forall_mem_cons.2 ⟨subd7_3_157, List.forall_mem_cons.2 ⟨subd7_3_158, List.forall_mem_cons.2 ⟨subd7_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_160 : subd7_3 [-3, -4, 2] = true := by decide +kernel
theorem subd7_3_161 : subd7_3 [-3, -4, 3] = true := by decide +kernel
theorem subd7_3_162 : subd7_3 [-3, -4, 4] = true := by decide +kernel
theorem subd7_3_163 : subd7_3 [-3, -4, 5] = true := by decide +kernel
theorem subd7_3_164 : subd7_3 [-3, -3, -9] = true := by decide +kernel
theorem subd7_3_165 : subd7_3 [-3, -3, -8] = true := by decide +kernel
theorem subd7_3_166 : subd7_3 [-3, -3, -7] = true := by decide +kernel
theorem subd7_3_167 : subd7_3 [-3, -3, -6] = true := by decide +kernel
theorem subd7_3_168 : subd7_3 [-3, -3, -5] = true := by decide +kernel
theorem subd7_3_169 : subd7_3 [-3, -3, -4] = true := by decide +kernel
theorem subd7_3_170 : subd7_3 [-3, -3, -3] = true := by decide +kernel
theorem subd7_3_171 : subd7_3 [-3, -3, -2] = true := by decide +kernel
theorem subd7_3_172 : subd7_3 [-3, -3, -1] = true := by decide +kernel
theorem subd7_3_173 : subd7_3 [-3, -3, 0] = true := by decide +kernel
theorem subd7_3_174 : subd7_3 [-3, -3, 1] = true := by decide +kernel
theorem subd7_3_175 : subd7_3 [-3, -3, 2] = true := by decide +kernel
theorem subd7_3_176 : subd7_3 [-3, -3, 3] = true := by decide +kernel
theorem subd7_3_177 : subd7_3 [-3, -3, 4] = true := by decide +kernel
theorem subd7_3_178 : subd7_3 [-3, -3, 5] = true := by decide +kernel
theorem subd7_3_179 : subd7_3 [-3, -2, -9] = true := by decide +kernel
theorem subd7_3_180 : subd7_3 [-3, -2, -8] = true := by decide +kernel
theorem subd7_3_181 : subd7_3 [-3, -2, -7] = true := by decide +kernel
theorem subd7_3_182 : subd7_3 [-3, -2, -6] = true := by decide +kernel
theorem subd7_3_183 : subd7_3 [-3, -2, -5] = true := by decide +kernel
theorem subd7_3_184 : subd7_3 [-3, -2, -4] = true := by decide +kernel
theorem subd7_3_185 : subd7_3 [-3, -2, -3] = true := by decide +kernel
theorem subd7_3_186 : subd7_3 [-3, -2, -2] = true := by decide +kernel
theorem subd7_3_187 : subd7_3 [-3, -2, -1] = true := by decide +kernel
theorem subd7_3_188 : subd7_3 [-3, -2, 0] = true := by decide +kernel
theorem subd7_3_189 : subd7_3 [-3, -2, 1] = true := by decide +kernel
theorem subd7_3_190 : subd7_3 [-3, -2, 2] = true := by decide +kernel
theorem subd7_3_191 : subd7_3 [-3, -2, 3] = true := by decide +kernel
theorem sbd7_3_5 : ∀ q ∈ blkd7_3_5, subd7_3 q = true := by
  unfold blkd7_3_5
  exact List.forall_mem_cons.2 ⟨subd7_3_160, List.forall_mem_cons.2 ⟨subd7_3_161, List.forall_mem_cons.2 ⟨subd7_3_162, List.forall_mem_cons.2 ⟨subd7_3_163, List.forall_mem_cons.2 ⟨subd7_3_164, List.forall_mem_cons.2 ⟨subd7_3_165, List.forall_mem_cons.2 ⟨subd7_3_166, List.forall_mem_cons.2 ⟨subd7_3_167, List.forall_mem_cons.2 ⟨subd7_3_168, List.forall_mem_cons.2 ⟨subd7_3_169, List.forall_mem_cons.2 ⟨subd7_3_170, List.forall_mem_cons.2 ⟨subd7_3_171, List.forall_mem_cons.2 ⟨subd7_3_172, List.forall_mem_cons.2 ⟨subd7_3_173, List.forall_mem_cons.2 ⟨subd7_3_174, List.forall_mem_cons.2 ⟨subd7_3_175, List.forall_mem_cons.2 ⟨subd7_3_176, List.forall_mem_cons.2 ⟨subd7_3_177, List.forall_mem_cons.2 ⟨subd7_3_178, List.forall_mem_cons.2 ⟨subd7_3_179, List.forall_mem_cons.2 ⟨subd7_3_180, List.forall_mem_cons.2 ⟨subd7_3_181, List.forall_mem_cons.2 ⟨subd7_3_182, List.forall_mem_cons.2 ⟨subd7_3_183, List.forall_mem_cons.2 ⟨subd7_3_184, List.forall_mem_cons.2 ⟨subd7_3_185, List.forall_mem_cons.2 ⟨subd7_3_186, List.forall_mem_cons.2 ⟨subd7_3_187, List.forall_mem_cons.2 ⟨subd7_3_188, List.forall_mem_cons.2 ⟨subd7_3_189, List.forall_mem_cons.2 ⟨subd7_3_190, List.forall_mem_cons.2 ⟨subd7_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_192 : subd7_3 [-3, -2, 4] = true := by decide +kernel
theorem subd7_3_193 : subd7_3 [-3, -2, 5] = true := by decide +kernel
theorem subd7_3_194 : subd7_3 [-3, -1, -9] = true := by decide +kernel
theorem subd7_3_195 : subd7_3 [-3, -1, -8] = true := by decide +kernel
theorem subd7_3_196 : subd7_3 [-3, -1, -7] = true := by decide +kernel
theorem subd7_3_197 : subd7_3 [-3, -1, -6] = true := by decide +kernel
theorem subd7_3_198 : subd7_3 [-3, -1, -5] = true := by decide +kernel
theorem subd7_3_199 : subd7_3 [-3, -1, -4] = true := by decide +kernel
theorem subd7_3_200 : subd7_3 [-3, -1, -3] = true := by decide +kernel
theorem subd7_3_201 : subd7_3 [-3, -1, -2] = true := by decide +kernel
theorem subd7_3_202 : subd7_3 [-3, -1, -1] = true := by decide +kernel
theorem subd7_3_203 : subd7_3 [-3, -1, 0] = true := by decide +kernel
theorem subd7_3_204 : subd7_3 [-3, -1, 1] = true := by decide +kernel
theorem subd7_3_205 : subd7_3 [-3, -1, 2] = true := by decide +kernel
theorem subd7_3_206 : subd7_3 [-3, -1, 3] = true := by decide +kernel
theorem subd7_3_207 : subd7_3 [-3, -1, 4] = true := by decide +kernel
theorem subd7_3_208 : subd7_3 [-3, -1, 5] = true := by decide +kernel
theorem subd7_3_209 : subd7_3 [-3, -1, 6] = true := by decide +kernel
theorem subd7_3_210 : subd7_3 [-3, 0, -9] = true := by decide +kernel
theorem subd7_3_211 : subd7_3 [-3, 0, -8] = true := by decide +kernel
theorem subd7_3_212 : subd7_3 [-3, 0, -7] = true := by decide +kernel
theorem subd7_3_213 : subd7_3 [-3, 0, -6] = true := by decide +kernel
theorem subd7_3_214 : subd7_3 [-3, 0, -5] = true := by decide +kernel
theorem subd7_3_215 : subd7_3 [-3, 0, -4] = true := by decide +kernel
theorem subd7_3_216 : subd7_3 [-3, 0, -3] = true := by decide +kernel
theorem subd7_3_217 : subd7_3 [-3, 0, -2] = true := by decide +kernel
theorem subd7_3_218 : subd7_3 [-3, 0, -1] = true := by decide +kernel
theorem subd7_3_219 : subd7_3 [-3, 0, 0] = true := by decide +kernel
theorem subd7_3_220 : subd7_3 [-3, 0, 1] = true := by decide +kernel
theorem subd7_3_221 : subd7_3 [-3, 0, 2] = true := by decide +kernel
theorem subd7_3_222 : subd7_3 [-3, 0, 3] = true := by decide +kernel
theorem subd7_3_223 : subd7_3 [-3, 0, 4] = true := by decide +kernel
theorem sbd7_3_6 : ∀ q ∈ blkd7_3_6, subd7_3 q = true := by
  unfold blkd7_3_6
  exact List.forall_mem_cons.2 ⟨subd7_3_192, List.forall_mem_cons.2 ⟨subd7_3_193, List.forall_mem_cons.2 ⟨subd7_3_194, List.forall_mem_cons.2 ⟨subd7_3_195, List.forall_mem_cons.2 ⟨subd7_3_196, List.forall_mem_cons.2 ⟨subd7_3_197, List.forall_mem_cons.2 ⟨subd7_3_198, List.forall_mem_cons.2 ⟨subd7_3_199, List.forall_mem_cons.2 ⟨subd7_3_200, List.forall_mem_cons.2 ⟨subd7_3_201, List.forall_mem_cons.2 ⟨subd7_3_202, List.forall_mem_cons.2 ⟨subd7_3_203, List.forall_mem_cons.2 ⟨subd7_3_204, List.forall_mem_cons.2 ⟨subd7_3_205, List.forall_mem_cons.2 ⟨subd7_3_206, List.forall_mem_cons.2 ⟨subd7_3_207, List.forall_mem_cons.2 ⟨subd7_3_208, List.forall_mem_cons.2 ⟨subd7_3_209, List.forall_mem_cons.2 ⟨subd7_3_210, List.forall_mem_cons.2 ⟨subd7_3_211, List.forall_mem_cons.2 ⟨subd7_3_212, List.forall_mem_cons.2 ⟨subd7_3_213, List.forall_mem_cons.2 ⟨subd7_3_214, List.forall_mem_cons.2 ⟨subd7_3_215, List.forall_mem_cons.2 ⟨subd7_3_216, List.forall_mem_cons.2 ⟨subd7_3_217, List.forall_mem_cons.2 ⟨subd7_3_218, List.forall_mem_cons.2 ⟨subd7_3_219, List.forall_mem_cons.2 ⟨subd7_3_220, List.forall_mem_cons.2 ⟨subd7_3_221, List.forall_mem_cons.2 ⟨subd7_3_222, List.forall_mem_cons.2 ⟨subd7_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_224 : subd7_3 [-3, 0, 5] = true := by decide +kernel
theorem subd7_3_225 : subd7_3 [-3, 1, -9] = true := by decide +kernel
theorem subd7_3_226 : subd7_3 [-3, 1, -8] = true := by decide +kernel
theorem subd7_3_227 : subd7_3 [-3, 1, -7] = true := by decide +kernel
theorem subd7_3_228 : subd7_3 [-3, 1, -6] = true := by decide +kernel
theorem subd7_3_229 : subd7_3 [-3, 1, -5] = true := by decide +kernel
theorem subd7_3_230 : subd7_3 [-3, 1, -4] = true := by decide +kernel
theorem subd7_3_231 : subd7_3 [-3, 1, -3] = true := by decide +kernel
theorem subd7_3_232 : subd7_3 [-3, 1, -2] = true := by decide +kernel
theorem subd7_3_233 : subd7_3 [-3, 1, -1] = true := by decide +kernel
theorem subd7_3_234 : subd7_3 [-3, 1, 0] = true := by decide +kernel
theorem subd7_3_235 : subd7_3 [-3, 1, 1] = true := by decide +kernel
theorem subd7_3_236 : subd7_3 [-3, 1, 2] = true := by decide +kernel
theorem subd7_3_237 : subd7_3 [-3, 1, 3] = true := by decide +kernel
theorem subd7_3_238 : subd7_3 [-3, 1, 4] = true := by decide +kernel
theorem subd7_3_239 : subd7_3 [-3, 1, 5] = true := by decide +kernel
theorem subd7_3_240 : subd7_3 [-3, 2, -9] = true := by decide +kernel
theorem subd7_3_241 : subd7_3 [-3, 2, -8] = true := by decide +kernel
theorem subd7_3_242 : subd7_3 [-3, 2, -7] = true := by decide +kernel
theorem subd7_3_243 : subd7_3 [-3, 2, -6] = true := by decide +kernel
theorem subd7_3_244 : subd7_3 [-3, 2, -5] = true := by decide +kernel
theorem subd7_3_245 : subd7_3 [-3, 2, -4] = true := by decide +kernel
theorem subd7_3_246 : subd7_3 [-3, 2, -3] = true := by decide +kernel
theorem subd7_3_247 : subd7_3 [-3, 2, -2] = true := by decide +kernel
theorem subd7_3_248 : subd7_3 [-3, 2, -1] = true := by decide +kernel
theorem subd7_3_249 : subd7_3 [-3, 2, 0] = true := by decide +kernel
theorem subd7_3_250 : subd7_3 [-3, 2, 1] = true := by decide +kernel
theorem subd7_3_251 : subd7_3 [-3, 2, 2] = true := by decide +kernel
theorem subd7_3_252 : subd7_3 [-3, 2, 3] = true := by decide +kernel
theorem subd7_3_253 : subd7_3 [-3, 2, 4] = true := by decide +kernel
theorem subd7_3_254 : subd7_3 [-3, 2, 5] = true := by decide +kernel
theorem subd7_3_255 : subd7_3 [-3, 3, -9] = true := by decide +kernel
theorem sbd7_3_7 : ∀ q ∈ blkd7_3_7, subd7_3 q = true := by
  unfold blkd7_3_7
  exact List.forall_mem_cons.2 ⟨subd7_3_224, List.forall_mem_cons.2 ⟨subd7_3_225, List.forall_mem_cons.2 ⟨subd7_3_226, List.forall_mem_cons.2 ⟨subd7_3_227, List.forall_mem_cons.2 ⟨subd7_3_228, List.forall_mem_cons.2 ⟨subd7_3_229, List.forall_mem_cons.2 ⟨subd7_3_230, List.forall_mem_cons.2 ⟨subd7_3_231, List.forall_mem_cons.2 ⟨subd7_3_232, List.forall_mem_cons.2 ⟨subd7_3_233, List.forall_mem_cons.2 ⟨subd7_3_234, List.forall_mem_cons.2 ⟨subd7_3_235, List.forall_mem_cons.2 ⟨subd7_3_236, List.forall_mem_cons.2 ⟨subd7_3_237, List.forall_mem_cons.2 ⟨subd7_3_238, List.forall_mem_cons.2 ⟨subd7_3_239, List.forall_mem_cons.2 ⟨subd7_3_240, List.forall_mem_cons.2 ⟨subd7_3_241, List.forall_mem_cons.2 ⟨subd7_3_242, List.forall_mem_cons.2 ⟨subd7_3_243, List.forall_mem_cons.2 ⟨subd7_3_244, List.forall_mem_cons.2 ⟨subd7_3_245, List.forall_mem_cons.2 ⟨subd7_3_246, List.forall_mem_cons.2 ⟨subd7_3_247, List.forall_mem_cons.2 ⟨subd7_3_248, List.forall_mem_cons.2 ⟨subd7_3_249, List.forall_mem_cons.2 ⟨subd7_3_250, List.forall_mem_cons.2 ⟨subd7_3_251, List.forall_mem_cons.2 ⟨subd7_3_252, List.forall_mem_cons.2 ⟨subd7_3_253, List.forall_mem_cons.2 ⟨subd7_3_254, List.forall_mem_cons.2 ⟨subd7_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_256 : subd7_3 [-3, 3, -8] = true := by decide +kernel
theorem subd7_3_257 : subd7_3 [-3, 3, -7] = true := by decide +kernel
theorem subd7_3_258 : subd7_3 [-3, 3, -6] = true := by decide +kernel
theorem subd7_3_259 : subd7_3 [-3, 3, -5] = true := by decide +kernel
theorem subd7_3_260 : subd7_3 [-3, 3, -4] = true := by decide +kernel
theorem subd7_3_261 : subd7_3 [-3, 3, -3] = true := by decide +kernel
theorem subd7_3_262 : subd7_3 [-3, 3, -2] = true := by decide +kernel
theorem subd7_3_263 : subd7_3 [-3, 3, -1] = true := by decide +kernel
theorem subd7_3_264 : subd7_3 [-3, 3, 0] = true := by decide +kernel
theorem subd7_3_265 : subd7_3 [-3, 3, 1] = true := by decide +kernel
theorem subd7_3_266 : subd7_3 [-3, 3, 2] = true := by decide +kernel
theorem subd7_3_267 : subd7_3 [-3, 3, 3] = true := by decide +kernel
theorem subd7_3_268 : subd7_3 [-3, 3, 4] = true := by decide +kernel
theorem subd7_3_269 : subd7_3 [-3, 3, 5] = true := by decide +kernel
theorem subd7_3_270 : subd7_3 [-3, 4, -9] = true := by decide +kernel
theorem subd7_3_271 : subd7_3 [-3, 4, -8] = true := by decide +kernel
theorem subd7_3_272 : subd7_3 [-3, 4, -7] = true := by decide +kernel
theorem subd7_3_273 : subd7_3 [-3, 4, -6] = true := by decide +kernel
theorem subd7_3_274 : subd7_3 [-3, 4, -5] = true := by decide +kernel
theorem subd7_3_275 : subd7_3 [-3, 4, -4] = true := by decide +kernel
theorem subd7_3_276 : subd7_3 [-3, 4, -3] = true := by decide +kernel
theorem subd7_3_277 : subd7_3 [-3, 4, -2] = true := by decide +kernel
theorem subd7_3_278 : subd7_3 [-3, 4, -1] = true := by decide +kernel
theorem subd7_3_279 : subd7_3 [-3, 4, 0] = true := by decide +kernel
theorem subd7_3_280 : subd7_3 [-3, 4, 1] = true := by decide +kernel
theorem subd7_3_281 : subd7_3 [-3, 4, 2] = true := by decide +kernel
theorem subd7_3_282 : subd7_3 [-3, 4, 3] = true := by decide +kernel
theorem subd7_3_283 : subd7_3 [-3, 4, 4] = true := by decide +kernel
theorem subd7_3_284 : subd7_3 [-3, 5] = true := by decide +kernel
theorem subd7_3_285 : subd7_3 [-3, 6] = true := by decide +kernel
theorem subd7_3_286 : subd7_3 [-3, 7] = true := by decide +kernel
theorem subd7_3_287 : subd7_3 [-3, 8] = true := by decide +kernel
theorem sbd7_3_8 : ∀ q ∈ blkd7_3_8, subd7_3 q = true := by
  unfold blkd7_3_8
  exact List.forall_mem_cons.2 ⟨subd7_3_256, List.forall_mem_cons.2 ⟨subd7_3_257, List.forall_mem_cons.2 ⟨subd7_3_258, List.forall_mem_cons.2 ⟨subd7_3_259, List.forall_mem_cons.2 ⟨subd7_3_260, List.forall_mem_cons.2 ⟨subd7_3_261, List.forall_mem_cons.2 ⟨subd7_3_262, List.forall_mem_cons.2 ⟨subd7_3_263, List.forall_mem_cons.2 ⟨subd7_3_264, List.forall_mem_cons.2 ⟨subd7_3_265, List.forall_mem_cons.2 ⟨subd7_3_266, List.forall_mem_cons.2 ⟨subd7_3_267, List.forall_mem_cons.2 ⟨subd7_3_268, List.forall_mem_cons.2 ⟨subd7_3_269, List.forall_mem_cons.2 ⟨subd7_3_270, List.forall_mem_cons.2 ⟨subd7_3_271, List.forall_mem_cons.2 ⟨subd7_3_272, List.forall_mem_cons.2 ⟨subd7_3_273, List.forall_mem_cons.2 ⟨subd7_3_274, List.forall_mem_cons.2 ⟨subd7_3_275, List.forall_mem_cons.2 ⟨subd7_3_276, List.forall_mem_cons.2 ⟨subd7_3_277, List.forall_mem_cons.2 ⟨subd7_3_278, List.forall_mem_cons.2 ⟨subd7_3_279, List.forall_mem_cons.2 ⟨subd7_3_280, List.forall_mem_cons.2 ⟨subd7_3_281, List.forall_mem_cons.2 ⟨subd7_3_282, List.forall_mem_cons.2 ⟨subd7_3_283, List.forall_mem_cons.2 ⟨subd7_3_284, List.forall_mem_cons.2 ⟨subd7_3_285, List.forall_mem_cons.2 ⟨subd7_3_286, List.forall_mem_cons.2 ⟨subd7_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_288 : subd7_3 [-2, -9] = true := by decide +kernel
theorem subd7_3_289 : subd7_3 [-2, -8] = true := by decide +kernel
theorem subd7_3_290 : subd7_3 [-2, -7] = true := by decide +kernel
theorem subd7_3_291 : subd7_3 [-2, -6] = true := by decide +kernel
theorem subd7_3_292 : subd7_3 [-2, -5, -7] = true := by decide +kernel
theorem subd7_3_293 : subd7_3 [-2, -5, -6] = true := by decide +kernel
theorem subd7_3_294 : subd7_3 [-2, -5, -5] = true := by decide +kernel
theorem subd7_3_295 : subd7_3 [-2, -5, -4] = true := by decide +kernel
theorem subd7_3_296 : subd7_3 [-2, -5, -3] = true := by decide +kernel
theorem subd7_3_297 : subd7_3 [-2, -5, -2] = true := by decide +kernel
theorem subd7_3_298 : subd7_3 [-2, -5, -1] = true := by decide +kernel
theorem subd7_3_299 : subd7_3 [-2, -5, 0] = true := by decide +kernel
theorem subd7_3_300 : subd7_3 [-2, -5, 1] = true := by decide +kernel
theorem subd7_3_301 : subd7_3 [-2, -5, 2] = true := by decide +kernel
theorem subd7_3_302 : subd7_3 [-2, -5, 3] = true := by decide +kernel
theorem subd7_3_303 : subd7_3 [-2, -5, 4] = true := by decide +kernel
theorem subd7_3_304 : subd7_3 [-2, -5, 5] = true := by decide +kernel
theorem subd7_3_305 : subd7_3 [-2, -4, -8] = true := by decide +kernel
theorem subd7_3_306 : subd7_3 [-2, -4, -7] = true := by decide +kernel
theorem subd7_3_307 : subd7_3 [-2, -4, -6] = true := by decide +kernel
theorem subd7_3_308 : subd7_3 [-2, -4, -5] = true := by decide +kernel
theorem subd7_3_309 : subd7_3 [-2, -4, -4] = true := by decide +kernel
theorem subd7_3_310 : subd7_3 [-2, -4, -3] = true := by decide +kernel
theorem subd7_3_311 : subd7_3 [-2, -4, -2] = true := by decide +kernel
theorem subd7_3_312 : subd7_3 [-2, -4, -1] = true := by decide +kernel
theorem subd7_3_313 : subd7_3 [-2, -4, 0] = true := by decide +kernel
theorem subd7_3_314 : subd7_3 [-2, -4, 1] = true := by decide +kernel
theorem subd7_3_315 : subd7_3 [-2, -4, 2] = true := by decide +kernel
theorem subd7_3_316 : subd7_3 [-2, -4, 3] = true := by decide +kernel
theorem subd7_3_317 : subd7_3 [-2, -4, 4] = true := by decide +kernel
theorem subd7_3_318 : subd7_3 [-2, -4, 5] = true := by decide +kernel
theorem subd7_3_319 : subd7_3 [-2, -4, 6] = true := by decide +kernel
theorem sbd7_3_9 : ∀ q ∈ blkd7_3_9, subd7_3 q = true := by
  unfold blkd7_3_9
  exact List.forall_mem_cons.2 ⟨subd7_3_288, List.forall_mem_cons.2 ⟨subd7_3_289, List.forall_mem_cons.2 ⟨subd7_3_290, List.forall_mem_cons.2 ⟨subd7_3_291, List.forall_mem_cons.2 ⟨subd7_3_292, List.forall_mem_cons.2 ⟨subd7_3_293, List.forall_mem_cons.2 ⟨subd7_3_294, List.forall_mem_cons.2 ⟨subd7_3_295, List.forall_mem_cons.2 ⟨subd7_3_296, List.forall_mem_cons.2 ⟨subd7_3_297, List.forall_mem_cons.2 ⟨subd7_3_298, List.forall_mem_cons.2 ⟨subd7_3_299, List.forall_mem_cons.2 ⟨subd7_3_300, List.forall_mem_cons.2 ⟨subd7_3_301, List.forall_mem_cons.2 ⟨subd7_3_302, List.forall_mem_cons.2 ⟨subd7_3_303, List.forall_mem_cons.2 ⟨subd7_3_304, List.forall_mem_cons.2 ⟨subd7_3_305, List.forall_mem_cons.2 ⟨subd7_3_306, List.forall_mem_cons.2 ⟨subd7_3_307, List.forall_mem_cons.2 ⟨subd7_3_308, List.forall_mem_cons.2 ⟨subd7_3_309, List.forall_mem_cons.2 ⟨subd7_3_310, List.forall_mem_cons.2 ⟨subd7_3_311, List.forall_mem_cons.2 ⟨subd7_3_312, List.forall_mem_cons.2 ⟨subd7_3_313, List.forall_mem_cons.2 ⟨subd7_3_314, List.forall_mem_cons.2 ⟨subd7_3_315, List.forall_mem_cons.2 ⟨subd7_3_316, List.forall_mem_cons.2 ⟨subd7_3_317, List.forall_mem_cons.2 ⟨subd7_3_318, List.forall_mem_cons.2 ⟨subd7_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
