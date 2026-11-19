import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_1_0 : subd19_1 [-9] = true := by decide +kernel
theorem subd19_1_1 : subd19_1 [-8, -5] = true := by decide +kernel
theorem subd19_1_2 : subd19_1 [-8, -4] = true := by decide +kernel
theorem subd19_1_3 : subd19_1 [-8, -3] = true := by decide +kernel
theorem subd19_1_4 : subd19_1 [-8, -2] = true := by decide +kernel
theorem subd19_1_5 : subd19_1 [-8, -1] = true := by decide +kernel
theorem subd19_1_6 : subd19_1 [-8, 0] = true := by decide +kernel
theorem subd19_1_7 : subd19_1 [-8, 1] = true := by decide +kernel
theorem subd19_1_8 : subd19_1 [-8, 2] = true := by decide +kernel
theorem subd19_1_9 : subd19_1 [-8, 3] = true := by decide +kernel
theorem subd19_1_10 : subd19_1 [-8, 4] = true := by decide +kernel
theorem subd19_1_11 : subd19_1 [-7, -6] = true := by decide +kernel
theorem subd19_1_12 : subd19_1 [-7, -5] = true := by decide +kernel
theorem subd19_1_13 : subd19_1 [-7, -4] = true := by decide +kernel
theorem subd19_1_14 : subd19_1 [-7, -3] = true := by decide +kernel
theorem subd19_1_15 : subd19_1 [-7, -2] = true := by decide +kernel
theorem subd19_1_16 : subd19_1 [-7, -1] = true := by decide +kernel
theorem subd19_1_17 : subd19_1 [-7, 0] = true := by decide +kernel
theorem subd19_1_18 : subd19_1 [-7, 1] = true := by decide +kernel
theorem subd19_1_19 : subd19_1 [-7, 2] = true := by decide +kernel
theorem subd19_1_20 : subd19_1 [-7, 3] = true := by decide +kernel
theorem subd19_1_21 : subd19_1 [-7, 4] = true := by decide +kernel
theorem subd19_1_22 : subd19_1 [-7, 5] = true := by decide +kernel
theorem subd19_1_23 : subd19_1 [-7, 6] = true := by decide +kernel
theorem subd19_1_24 : subd19_1 [-6, -7] = true := by decide +kernel
theorem subd19_1_25 : subd19_1 [-6, -6] = true := by decide +kernel
theorem subd19_1_26 : subd19_1 [-6, -5] = true := by decide +kernel
theorem subd19_1_27 : subd19_1 [-6, -4] = true := by decide +kernel
theorem subd19_1_28 : subd19_1 [-6, -3] = true := by decide +kernel
theorem subd19_1_29 : subd19_1 [-6, -2] = true := by decide +kernel
theorem subd19_1_30 : subd19_1 [-6, -1] = true := by decide +kernel
theorem subd19_1_31 : subd19_1 [-6, 0] = true := by decide +kernel
theorem sbd19_1_0 : ∀ q ∈ blkd19_1_0, subd19_1 q = true := by
  unfold blkd19_1_0
  exact List.forall_mem_cons.2 ⟨subd19_1_0, List.forall_mem_cons.2 ⟨subd19_1_1, List.forall_mem_cons.2 ⟨subd19_1_2, List.forall_mem_cons.2 ⟨subd19_1_3, List.forall_mem_cons.2 ⟨subd19_1_4, List.forall_mem_cons.2 ⟨subd19_1_5, List.forall_mem_cons.2 ⟨subd19_1_6, List.forall_mem_cons.2 ⟨subd19_1_7, List.forall_mem_cons.2 ⟨subd19_1_8, List.forall_mem_cons.2 ⟨subd19_1_9, List.forall_mem_cons.2 ⟨subd19_1_10, List.forall_mem_cons.2 ⟨subd19_1_11, List.forall_mem_cons.2 ⟨subd19_1_12, List.forall_mem_cons.2 ⟨subd19_1_13, List.forall_mem_cons.2 ⟨subd19_1_14, List.forall_mem_cons.2 ⟨subd19_1_15, List.forall_mem_cons.2 ⟨subd19_1_16, List.forall_mem_cons.2 ⟨subd19_1_17, List.forall_mem_cons.2 ⟨subd19_1_18, List.forall_mem_cons.2 ⟨subd19_1_19, List.forall_mem_cons.2 ⟨subd19_1_20, List.forall_mem_cons.2 ⟨subd19_1_21, List.forall_mem_cons.2 ⟨subd19_1_22, List.forall_mem_cons.2 ⟨subd19_1_23, List.forall_mem_cons.2 ⟨subd19_1_24, List.forall_mem_cons.2 ⟨subd19_1_25, List.forall_mem_cons.2 ⟨subd19_1_26, List.forall_mem_cons.2 ⟨subd19_1_27, List.forall_mem_cons.2 ⟨subd19_1_28, List.forall_mem_cons.2 ⟨subd19_1_29, List.forall_mem_cons.2 ⟨subd19_1_30, List.forall_mem_cons.2 ⟨subd19_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_32 : subd19_1 [-6, 1] = true := by decide +kernel
theorem subd19_1_33 : subd19_1 [-6, 2] = true := by decide +kernel
theorem subd19_1_34 : subd19_1 [-6, 3] = true := by decide +kernel
theorem subd19_1_35 : subd19_1 [-6, 4] = true := by decide +kernel
theorem subd19_1_36 : subd19_1 [-6, 5] = true := by decide +kernel
theorem subd19_1_37 : subd19_1 [-6, 6] = true := by decide +kernel
theorem subd19_1_38 : subd19_1 [-6, 7] = true := by decide +kernel
theorem subd19_1_39 : subd19_1 [-5, -8] = true := by decide +kernel
theorem subd19_1_40 : subd19_1 [-5, -7] = true := by decide +kernel
theorem subd19_1_41 : subd19_1 [-5, -6] = true := by decide +kernel
theorem subd19_1_42 : subd19_1 [-5, -5] = true := by decide +kernel
theorem subd19_1_43 : subd19_1 [-5, -4] = true := by decide +kernel
theorem subd19_1_44 : subd19_1 [-5, -3] = true := by decide +kernel
theorem subd19_1_45 : subd19_1 [-5, -2] = true := by decide +kernel
theorem subd19_1_46 : subd19_1 [-5, -1] = true := by decide +kernel
theorem subd19_1_47 : subd19_1 [-5, 0, -5] = true := by decide +kernel
theorem subd19_1_48 : subd19_1 [-5, 0, -4] = true := by decide +kernel
theorem subd19_1_49 : subd19_1 [-5, 0, -3] = true := by decide +kernel
theorem subd19_1_50 : subd19_1 [-5, 0, -2] = true := by decide +kernel
theorem subd19_1_51 : subd19_1 [-5, 0, -1] = true := by decide +kernel
theorem subd19_1_52 : subd19_1 [-5, 0, 0] = true := by decide +kernel
theorem subd19_1_53 : subd19_1 [-5, 0, 1] = true := by decide +kernel
theorem subd19_1_54 : subd19_1 [-5, 0, 2] = true := by decide +kernel
theorem subd19_1_55 : subd19_1 [-5, 0, 3] = true := by decide +kernel
theorem subd19_1_56 : subd19_1 [-5, 0, 4] = true := by decide +kernel
theorem subd19_1_57 : subd19_1 [-5, 0, 5] = true := by decide +kernel
theorem subd19_1_58 : subd19_1 [-5, 0, 6] = true := by decide +kernel
theorem subd19_1_59 : subd19_1 [-5, 0, 7] = true := by decide +kernel
theorem subd19_1_60 : subd19_1 [-5, 0, 8] = true := by decide +kernel
theorem subd19_1_61 : subd19_1 [-5, 1] = true := by decide +kernel
theorem subd19_1_62 : subd19_1 [-5, 2] = true := by decide +kernel
theorem subd19_1_63 : subd19_1 [-5, 3] = true := by decide +kernel
theorem sbd19_1_1 : ∀ q ∈ blkd19_1_1, subd19_1 q = true := by
  unfold blkd19_1_1
  exact List.forall_mem_cons.2 ⟨subd19_1_32, List.forall_mem_cons.2 ⟨subd19_1_33, List.forall_mem_cons.2 ⟨subd19_1_34, List.forall_mem_cons.2 ⟨subd19_1_35, List.forall_mem_cons.2 ⟨subd19_1_36, List.forall_mem_cons.2 ⟨subd19_1_37, List.forall_mem_cons.2 ⟨subd19_1_38, List.forall_mem_cons.2 ⟨subd19_1_39, List.forall_mem_cons.2 ⟨subd19_1_40, List.forall_mem_cons.2 ⟨subd19_1_41, List.forall_mem_cons.2 ⟨subd19_1_42, List.forall_mem_cons.2 ⟨subd19_1_43, List.forall_mem_cons.2 ⟨subd19_1_44, List.forall_mem_cons.2 ⟨subd19_1_45, List.forall_mem_cons.2 ⟨subd19_1_46, List.forall_mem_cons.2 ⟨subd19_1_47, List.forall_mem_cons.2 ⟨subd19_1_48, List.forall_mem_cons.2 ⟨subd19_1_49, List.forall_mem_cons.2 ⟨subd19_1_50, List.forall_mem_cons.2 ⟨subd19_1_51, List.forall_mem_cons.2 ⟨subd19_1_52, List.forall_mem_cons.2 ⟨subd19_1_53, List.forall_mem_cons.2 ⟨subd19_1_54, List.forall_mem_cons.2 ⟨subd19_1_55, List.forall_mem_cons.2 ⟨subd19_1_56, List.forall_mem_cons.2 ⟨subd19_1_57, List.forall_mem_cons.2 ⟨subd19_1_58, List.forall_mem_cons.2 ⟨subd19_1_59, List.forall_mem_cons.2 ⟨subd19_1_60, List.forall_mem_cons.2 ⟨subd19_1_61, List.forall_mem_cons.2 ⟨subd19_1_62, List.forall_mem_cons.2 ⟨subd19_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_64 : subd19_1 [-5, 4] = true := by decide +kernel
theorem subd19_1_65 : subd19_1 [-5, 5] = true := by decide +kernel
theorem subd19_1_66 : subd19_1 [-5, 6] = true := by decide +kernel
theorem subd19_1_67 : subd19_1 [-5, 7] = true := by decide +kernel
theorem subd19_1_68 : subd19_1 [-4, -9] = true := by decide +kernel
theorem subd19_1_69 : subd19_1 [-4, -8] = true := by decide +kernel
theorem subd19_1_70 : subd19_1 [-4, -7] = true := by decide +kernel
theorem subd19_1_71 : subd19_1 [-4, -6] = true := by decide +kernel
theorem subd19_1_72 : subd19_1 [-4, -5] = true := by decide +kernel
theorem subd19_1_73 : subd19_1 [-4, -4] = true := by decide +kernel
theorem subd19_1_74 : subd19_1 [-4, -3, -6] = true := by decide +kernel
theorem subd19_1_75 : subd19_1 [-4, -3, -5] = true := by decide +kernel
theorem subd19_1_76 : subd19_1 [-4, -3, -4] = true := by decide +kernel
theorem subd19_1_77 : subd19_1 [-4, -3, -3] = true := by decide +kernel
theorem subd19_1_78 : subd19_1 [-4, -3, -2] = true := by decide +kernel
theorem subd19_1_79 : subd19_1 [-4, -3, -1] = true := by decide +kernel
theorem subd19_1_80 : subd19_1 [-4, -3, 0] = true := by decide +kernel
theorem subd19_1_81 : subd19_1 [-4, -3, 1] = true := by decide +kernel
theorem subd19_1_82 : subd19_1 [-4, -3, 2] = true := by decide +kernel
theorem subd19_1_83 : subd19_1 [-4, -3, 3] = true := by decide +kernel
theorem subd19_1_84 : subd19_1 [-4, -3, 4] = true := by decide +kernel
theorem subd19_1_85 : subd19_1 [-4, -3, 5] = true := by decide +kernel
theorem subd19_1_86 : subd19_1 [-4, -3, 6] = true := by decide +kernel
theorem subd19_1_87 : subd19_1 [-4, -3, 7] = true := by decide +kernel
theorem subd19_1_88 : subd19_1 [-4, -2, -6] = true := by decide +kernel
theorem subd19_1_89 : subd19_1 [-4, -2, -5] = true := by decide +kernel
theorem subd19_1_90 : subd19_1 [-4, -2, -4] = true := by decide +kernel
theorem subd19_1_91 : subd19_1 [-4, -2, -3] = true := by decide +kernel
theorem subd19_1_92 : subd19_1 [-4, -2, -2] = true := by decide +kernel
theorem subd19_1_93 : subd19_1 [-4, -2, -1] = true := by decide +kernel
theorem subd19_1_94 : subd19_1 [-4, -2, 0] = true := by decide +kernel
theorem subd19_1_95 : subd19_1 [-4, -2, 1] = true := by decide +kernel
theorem sbd19_1_2 : ∀ q ∈ blkd19_1_2, subd19_1 q = true := by
  unfold blkd19_1_2
  exact List.forall_mem_cons.2 ⟨subd19_1_64, List.forall_mem_cons.2 ⟨subd19_1_65, List.forall_mem_cons.2 ⟨subd19_1_66, List.forall_mem_cons.2 ⟨subd19_1_67, List.forall_mem_cons.2 ⟨subd19_1_68, List.forall_mem_cons.2 ⟨subd19_1_69, List.forall_mem_cons.2 ⟨subd19_1_70, List.forall_mem_cons.2 ⟨subd19_1_71, List.forall_mem_cons.2 ⟨subd19_1_72, List.forall_mem_cons.2 ⟨subd19_1_73, List.forall_mem_cons.2 ⟨subd19_1_74, List.forall_mem_cons.2 ⟨subd19_1_75, List.forall_mem_cons.2 ⟨subd19_1_76, List.forall_mem_cons.2 ⟨subd19_1_77, List.forall_mem_cons.2 ⟨subd19_1_78, List.forall_mem_cons.2 ⟨subd19_1_79, List.forall_mem_cons.2 ⟨subd19_1_80, List.forall_mem_cons.2 ⟨subd19_1_81, List.forall_mem_cons.2 ⟨subd19_1_82, List.forall_mem_cons.2 ⟨subd19_1_83, List.forall_mem_cons.2 ⟨subd19_1_84, List.forall_mem_cons.2 ⟨subd19_1_85, List.forall_mem_cons.2 ⟨subd19_1_86, List.forall_mem_cons.2 ⟨subd19_1_87, List.forall_mem_cons.2 ⟨subd19_1_88, List.forall_mem_cons.2 ⟨subd19_1_89, List.forall_mem_cons.2 ⟨subd19_1_90, List.forall_mem_cons.2 ⟨subd19_1_91, List.forall_mem_cons.2 ⟨subd19_1_92, List.forall_mem_cons.2 ⟨subd19_1_93, List.forall_mem_cons.2 ⟨subd19_1_94, List.forall_mem_cons.2 ⟨subd19_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_96 : subd19_1 [-4, -2, 2] = true := by decide +kernel
theorem subd19_1_97 : subd19_1 [-4, -2, 3] = true := by decide +kernel
theorem subd19_1_98 : subd19_1 [-4, -2, 4] = true := by decide +kernel
theorem subd19_1_99 : subd19_1 [-4, -2, 5] = true := by decide +kernel
theorem subd19_1_100 : subd19_1 [-4, -2, 6] = true := by decide +kernel
theorem subd19_1_101 : subd19_1 [-4, -2, 7] = true := by decide +kernel
theorem subd19_1_102 : subd19_1 [-4, -1, -6] = true := by decide +kernel
theorem subd19_1_103 : subd19_1 [-4, -1, -5] = true := by decide +kernel
theorem subd19_1_104 : subd19_1 [-4, -1, -4] = true := by decide +kernel
theorem subd19_1_105 : subd19_1 [-4, -1, -3] = true := by decide +kernel
theorem subd19_1_106 : subd19_1 [-4, -1, -2] = true := by decide +kernel
theorem subd19_1_107 : subd19_1 [-4, -1, -1] = true := by decide +kernel
theorem subd19_1_108 : subd19_1 [-4, -1, 0] = true := by decide +kernel
theorem subd19_1_109 : subd19_1 [-4, -1, 1] = true := by decide +kernel
theorem subd19_1_110 : subd19_1 [-4, -1, 2] = true := by decide +kernel
theorem subd19_1_111 : subd19_1 [-4, -1, 3] = true := by decide +kernel
theorem subd19_1_112 : subd19_1 [-4, -1, 4] = true := by decide +kernel
theorem subd19_1_113 : subd19_1 [-4, -1, 5] = true := by decide +kernel
theorem subd19_1_114 : subd19_1 [-4, -1, 6] = true := by decide +kernel
theorem subd19_1_115 : subd19_1 [-4, -1, 7] = true := by decide +kernel
theorem subd19_1_116 : subd19_1 [-4, -1, 8] = true := by decide +kernel
theorem subd19_1_117 : subd19_1 [-4, 0, -5] = true := by decide +kernel
theorem subd19_1_118 : subd19_1 [-4, 0, -4] = true := by decide +kernel
theorem subd19_1_119 : subd19_1 [-4, 0, -3] = true := by decide +kernel
theorem subd19_1_120 : subd19_1 [-4, 0, -2] = true := by decide +kernel
theorem subd19_1_121 : subd19_1 [-4, 0, -1] = true := by decide +kernel
theorem subd19_1_122 : subd19_1 [-4, 0, 0] = true := by decide +kernel
theorem subd19_1_123 : subd19_1 [-4, 0, 1] = true := by decide +kernel
theorem subd19_1_124 : subd19_1 [-4, 0, 2] = true := by decide +kernel
theorem subd19_1_125 : subd19_1 [-4, 0, 3] = true := by decide +kernel
theorem subd19_1_126 : subd19_1 [-4, 0, 4] = true := by decide +kernel
theorem subd19_1_127 : subd19_1 [-4, 0, 5] = true := by decide +kernel
theorem sbd19_1_3 : ∀ q ∈ blkd19_1_3, subd19_1 q = true := by
  unfold blkd19_1_3
  exact List.forall_mem_cons.2 ⟨subd19_1_96, List.forall_mem_cons.2 ⟨subd19_1_97, List.forall_mem_cons.2 ⟨subd19_1_98, List.forall_mem_cons.2 ⟨subd19_1_99, List.forall_mem_cons.2 ⟨subd19_1_100, List.forall_mem_cons.2 ⟨subd19_1_101, List.forall_mem_cons.2 ⟨subd19_1_102, List.forall_mem_cons.2 ⟨subd19_1_103, List.forall_mem_cons.2 ⟨subd19_1_104, List.forall_mem_cons.2 ⟨subd19_1_105, List.forall_mem_cons.2 ⟨subd19_1_106, List.forall_mem_cons.2 ⟨subd19_1_107, List.forall_mem_cons.2 ⟨subd19_1_108, List.forall_mem_cons.2 ⟨subd19_1_109, List.forall_mem_cons.2 ⟨subd19_1_110, List.forall_mem_cons.2 ⟨subd19_1_111, List.forall_mem_cons.2 ⟨subd19_1_112, List.forall_mem_cons.2 ⟨subd19_1_113, List.forall_mem_cons.2 ⟨subd19_1_114, List.forall_mem_cons.2 ⟨subd19_1_115, List.forall_mem_cons.2 ⟨subd19_1_116, List.forall_mem_cons.2 ⟨subd19_1_117, List.forall_mem_cons.2 ⟨subd19_1_118, List.forall_mem_cons.2 ⟨subd19_1_119, List.forall_mem_cons.2 ⟨subd19_1_120, List.forall_mem_cons.2 ⟨subd19_1_121, List.forall_mem_cons.2 ⟨subd19_1_122, List.forall_mem_cons.2 ⟨subd19_1_123, List.forall_mem_cons.2 ⟨subd19_1_124, List.forall_mem_cons.2 ⟨subd19_1_125, List.forall_mem_cons.2 ⟨subd19_1_126, List.forall_mem_cons.2 ⟨subd19_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_128 : subd19_1 [-4, 0, 6] = true := by decide +kernel
theorem subd19_1_129 : subd19_1 [-4, 0, 7] = true := by decide +kernel
theorem subd19_1_130 : subd19_1 [-4, 0, 8] = true := by decide +kernel
theorem subd19_1_131 : subd19_1 [-4, 1, -5] = true := by decide +kernel
theorem subd19_1_132 : subd19_1 [-4, 1, -4] = true := by decide +kernel
theorem subd19_1_133 : subd19_1 [-4, 1, -3] = true := by decide +kernel
theorem subd19_1_134 : subd19_1 [-4, 1, -2] = true := by decide +kernel
theorem subd19_1_135 : subd19_1 [-4, 1, -1] = true := by decide +kernel
theorem subd19_1_136 : subd19_1 [-4, 1, 0] = true := by decide +kernel
theorem subd19_1_137 : subd19_1 [-4, 1, 1] = true := by decide +kernel
theorem subd19_1_138 : subd19_1 [-4, 1, 2] = true := by decide +kernel
theorem subd19_1_139 : subd19_1 [-4, 1, 3] = true := by decide +kernel
theorem subd19_1_140 : subd19_1 [-4, 1, 4] = true := by decide +kernel
theorem subd19_1_141 : subd19_1 [-4, 1, 5] = true := by decide +kernel
theorem subd19_1_142 : subd19_1 [-4, 1, 6] = true := by decide +kernel
theorem subd19_1_143 : subd19_1 [-4, 1, 7] = true := by decide +kernel
theorem subd19_1_144 : subd19_1 [-4, 1, 8] = true := by decide +kernel
theorem subd19_1_145 : subd19_1 [-4, 1, 9] = true := by decide +kernel
theorem subd19_1_146 : subd19_1 [-4, 2, -5] = true := by decide +kernel
theorem subd19_1_147 : subd19_1 [-4, 2, -4] = true := by decide +kernel
theorem subd19_1_148 : subd19_1 [-4, 2, -3] = true := by decide +kernel
theorem subd19_1_149 : subd19_1 [-4, 2, -2] = true := by decide +kernel
theorem subd19_1_150 : subd19_1 [-4, 2, -1] = true := by decide +kernel
theorem subd19_1_151 : subd19_1 [-4, 2, 0] = true := by decide +kernel
theorem subd19_1_152 : subd19_1 [-4, 2, 1] = true := by decide +kernel
theorem subd19_1_153 : subd19_1 [-4, 2, 2] = true := by decide +kernel
theorem subd19_1_154 : subd19_1 [-4, 2, 3] = true := by decide +kernel
theorem subd19_1_155 : subd19_1 [-4, 2, 4] = true := by decide +kernel
theorem subd19_1_156 : subd19_1 [-4, 2, 5] = true := by decide +kernel
theorem subd19_1_157 : subd19_1 [-4, 2, 6] = true := by decide +kernel
theorem subd19_1_158 : subd19_1 [-4, 2, 7] = true := by decide +kernel
theorem subd19_1_159 : subd19_1 [-4, 2, 8] = true := by decide +kernel
theorem sbd19_1_4 : ∀ q ∈ blkd19_1_4, subd19_1 q = true := by
  unfold blkd19_1_4
  exact List.forall_mem_cons.2 ⟨subd19_1_128, List.forall_mem_cons.2 ⟨subd19_1_129, List.forall_mem_cons.2 ⟨subd19_1_130, List.forall_mem_cons.2 ⟨subd19_1_131, List.forall_mem_cons.2 ⟨subd19_1_132, List.forall_mem_cons.2 ⟨subd19_1_133, List.forall_mem_cons.2 ⟨subd19_1_134, List.forall_mem_cons.2 ⟨subd19_1_135, List.forall_mem_cons.2 ⟨subd19_1_136, List.forall_mem_cons.2 ⟨subd19_1_137, List.forall_mem_cons.2 ⟨subd19_1_138, List.forall_mem_cons.2 ⟨subd19_1_139, List.forall_mem_cons.2 ⟨subd19_1_140, List.forall_mem_cons.2 ⟨subd19_1_141, List.forall_mem_cons.2 ⟨subd19_1_142, List.forall_mem_cons.2 ⟨subd19_1_143, List.forall_mem_cons.2 ⟨subd19_1_144, List.forall_mem_cons.2 ⟨subd19_1_145, List.forall_mem_cons.2 ⟨subd19_1_146, List.forall_mem_cons.2 ⟨subd19_1_147, List.forall_mem_cons.2 ⟨subd19_1_148, List.forall_mem_cons.2 ⟨subd19_1_149, List.forall_mem_cons.2 ⟨subd19_1_150, List.forall_mem_cons.2 ⟨subd19_1_151, List.forall_mem_cons.2 ⟨subd19_1_152, List.forall_mem_cons.2 ⟨subd19_1_153, List.forall_mem_cons.2 ⟨subd19_1_154, List.forall_mem_cons.2 ⟨subd19_1_155, List.forall_mem_cons.2 ⟨subd19_1_156, List.forall_mem_cons.2 ⟨subd19_1_157, List.forall_mem_cons.2 ⟨subd19_1_158, List.forall_mem_cons.2 ⟨subd19_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_160 : subd19_1 [-4, 2, 9] = true := by decide +kernel
theorem subd19_1_161 : subd19_1 [-4, 3, -4] = true := by decide +kernel
theorem subd19_1_162 : subd19_1 [-4, 3, -3] = true := by decide +kernel
theorem subd19_1_163 : subd19_1 [-4, 3, -2] = true := by decide +kernel
theorem subd19_1_164 : subd19_1 [-4, 3, -1] = true := by decide +kernel
theorem subd19_1_165 : subd19_1 [-4, 3, 0] = true := by decide +kernel
theorem subd19_1_166 : subd19_1 [-4, 3, 1] = true := by decide +kernel
theorem subd19_1_167 : subd19_1 [-4, 3, 2] = true := by decide +kernel
theorem subd19_1_168 : subd19_1 [-4, 3, 3] = true := by decide +kernel
theorem subd19_1_169 : subd19_1 [-4, 3, 4] = true := by decide +kernel
theorem subd19_1_170 : subd19_1 [-4, 3, 5] = true := by decide +kernel
theorem subd19_1_171 : subd19_1 [-4, 3, 6] = true := by decide +kernel
theorem subd19_1_172 : subd19_1 [-4, 3, 7] = true := by decide +kernel
theorem subd19_1_173 : subd19_1 [-4, 3, 8] = true := by decide +kernel
theorem subd19_1_174 : subd19_1 [-4, 3, 9] = true := by decide +kernel
theorem subd19_1_175 : subd19_1 [-4, 4] = true := by decide +kernel
theorem subd19_1_176 : subd19_1 [-4, 5] = true := by decide +kernel
theorem subd19_1_177 : subd19_1 [-4, 6] = true := by decide +kernel
theorem subd19_1_178 : subd19_1 [-4, 7] = true := by decide +kernel
theorem subd19_1_179 : subd19_1 [-4, 8] = true := by decide +kernel
theorem subd19_1_180 : subd19_1 [-3, -9] = true := by decide +kernel
theorem subd19_1_181 : subd19_1 [-3, -8] = true := by decide +kernel
theorem subd19_1_182 : subd19_1 [-3, -7] = true := by decide +kernel
theorem subd19_1_183 : subd19_1 [-3, -6] = true := by decide +kernel
theorem subd19_1_184 : subd19_1 [-3, -5] = true := by decide +kernel
theorem subd19_1_185 : subd19_1 [-3, -4] = true := by decide +kernel
theorem subd19_1_186 : subd19_1 [-3, -3, -7] = true := by decide +kernel
theorem subd19_1_187 : subd19_1 [-3, -3, -6] = true := by decide +kernel
theorem subd19_1_188 : subd19_1 [-3, -3, -5] = true := by decide +kernel
theorem subd19_1_189 : subd19_1 [-3, -3, -4] = true := by decide +kernel
theorem subd19_1_190 : subd19_1 [-3, -3, -3] = true := by decide +kernel
theorem subd19_1_191 : subd19_1 [-3, -3, -2] = true := by decide +kernel
theorem sbd19_1_5 : ∀ q ∈ blkd19_1_5, subd19_1 q = true := by
  unfold blkd19_1_5
  exact List.forall_mem_cons.2 ⟨subd19_1_160, List.forall_mem_cons.2 ⟨subd19_1_161, List.forall_mem_cons.2 ⟨subd19_1_162, List.forall_mem_cons.2 ⟨subd19_1_163, List.forall_mem_cons.2 ⟨subd19_1_164, List.forall_mem_cons.2 ⟨subd19_1_165, List.forall_mem_cons.2 ⟨subd19_1_166, List.forall_mem_cons.2 ⟨subd19_1_167, List.forall_mem_cons.2 ⟨subd19_1_168, List.forall_mem_cons.2 ⟨subd19_1_169, List.forall_mem_cons.2 ⟨subd19_1_170, List.forall_mem_cons.2 ⟨subd19_1_171, List.forall_mem_cons.2 ⟨subd19_1_172, List.forall_mem_cons.2 ⟨subd19_1_173, List.forall_mem_cons.2 ⟨subd19_1_174, List.forall_mem_cons.2 ⟨subd19_1_175, List.forall_mem_cons.2 ⟨subd19_1_176, List.forall_mem_cons.2 ⟨subd19_1_177, List.forall_mem_cons.2 ⟨subd19_1_178, List.forall_mem_cons.2 ⟨subd19_1_179, List.forall_mem_cons.2 ⟨subd19_1_180, List.forall_mem_cons.2 ⟨subd19_1_181, List.forall_mem_cons.2 ⟨subd19_1_182, List.forall_mem_cons.2 ⟨subd19_1_183, List.forall_mem_cons.2 ⟨subd19_1_184, List.forall_mem_cons.2 ⟨subd19_1_185, List.forall_mem_cons.2 ⟨subd19_1_186, List.forall_mem_cons.2 ⟨subd19_1_187, List.forall_mem_cons.2 ⟨subd19_1_188, List.forall_mem_cons.2 ⟨subd19_1_189, List.forall_mem_cons.2 ⟨subd19_1_190, List.forall_mem_cons.2 ⟨subd19_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_192 : subd19_1 [-3, -3, -1] = true := by decide +kernel
theorem subd19_1_193 : subd19_1 [-3, -3, 0] = true := by decide +kernel
theorem subd19_1_194 : subd19_1 [-3, -3, 1] = true := by decide +kernel
theorem subd19_1_195 : subd19_1 [-3, -3, 2] = true := by decide +kernel
theorem subd19_1_196 : subd19_1 [-3, -3, 3] = true := by decide +kernel
theorem subd19_1_197 : subd19_1 [-3, -3, 4] = true := by decide +kernel
theorem subd19_1_198 : subd19_1 [-3, -3, 5] = true := by decide +kernel
theorem subd19_1_199 : subd19_1 [-3, -3, 6] = true := by decide +kernel
theorem subd19_1_200 : subd19_1 [-3, -3, 7] = true := by decide +kernel
theorem subd19_1_201 : subd19_1 [-3, -2, -7] = true := by decide +kernel
theorem subd19_1_202 : subd19_1 [-3, -2, -6] = true := by decide +kernel
theorem subd19_1_203 : subd19_1 [-3, -2, -5] = true := by decide +kernel
theorem subd19_1_204 : subd19_1 [-3, -2, -4] = true := by decide +kernel
theorem subd19_1_205 : subd19_1 [-3, -2, -3] = true := by decide +kernel
theorem subd19_1_206 : subd19_1 [-3, -2, -2] = true := by decide +kernel
theorem subd19_1_207 : subd19_1 [-3, -2, -1] = true := by decide +kernel
theorem subd19_1_208 : subd19_1 [-3, -2, 0] = true := by decide +kernel
theorem subd19_1_209 : subd19_1 [-3, -2, 1] = true := by decide +kernel
theorem subd19_1_210 : subd19_1 [-3, -2, 2] = true := by decide +kernel
theorem subd19_1_211 : subd19_1 [-3, -2, 3] = true := by decide +kernel
theorem subd19_1_212 : subd19_1 [-3, -2, 4] = true := by decide +kernel
theorem subd19_1_213 : subd19_1 [-3, -2, 5] = true := by decide +kernel
theorem subd19_1_214 : subd19_1 [-3, -2, 6] = true := by decide +kernel
theorem subd19_1_215 : subd19_1 [-3, -2, 7] = true := by decide +kernel
theorem subd19_1_216 : subd19_1 [-3, -1, -7] = true := by decide +kernel
theorem subd19_1_217 : subd19_1 [-3, -1, -6] = true := by decide +kernel
theorem subd19_1_218 : subd19_1 [-3, -1, -5] = true := by decide +kernel
theorem subd19_1_219 : subd19_1 [-3, -1, -4] = true := by decide +kernel
theorem subd19_1_220 : subd19_1 [-3, -1, -3] = true := by decide +kernel
theorem subd19_1_221 : subd19_1 [-3, -1, -2] = true := by decide +kernel
theorem subd19_1_222 : subd19_1 [-3, -1, -1] = true := by decide +kernel
theorem subd19_1_223 : subd19_1 [-3, -1, 0] = true := by decide +kernel
theorem sbd19_1_6 : ∀ q ∈ blkd19_1_6, subd19_1 q = true := by
  unfold blkd19_1_6
  exact List.forall_mem_cons.2 ⟨subd19_1_192, List.forall_mem_cons.2 ⟨subd19_1_193, List.forall_mem_cons.2 ⟨subd19_1_194, List.forall_mem_cons.2 ⟨subd19_1_195, List.forall_mem_cons.2 ⟨subd19_1_196, List.forall_mem_cons.2 ⟨subd19_1_197, List.forall_mem_cons.2 ⟨subd19_1_198, List.forall_mem_cons.2 ⟨subd19_1_199, List.forall_mem_cons.2 ⟨subd19_1_200, List.forall_mem_cons.2 ⟨subd19_1_201, List.forall_mem_cons.2 ⟨subd19_1_202, List.forall_mem_cons.2 ⟨subd19_1_203, List.forall_mem_cons.2 ⟨subd19_1_204, List.forall_mem_cons.2 ⟨subd19_1_205, List.forall_mem_cons.2 ⟨subd19_1_206, List.forall_mem_cons.2 ⟨subd19_1_207, List.forall_mem_cons.2 ⟨subd19_1_208, List.forall_mem_cons.2 ⟨subd19_1_209, List.forall_mem_cons.2 ⟨subd19_1_210, List.forall_mem_cons.2 ⟨subd19_1_211, List.forall_mem_cons.2 ⟨subd19_1_212, List.forall_mem_cons.2 ⟨subd19_1_213, List.forall_mem_cons.2 ⟨subd19_1_214, List.forall_mem_cons.2 ⟨subd19_1_215, List.forall_mem_cons.2 ⟨subd19_1_216, List.forall_mem_cons.2 ⟨subd19_1_217, List.forall_mem_cons.2 ⟨subd19_1_218, List.forall_mem_cons.2 ⟨subd19_1_219, List.forall_mem_cons.2 ⟨subd19_1_220, List.forall_mem_cons.2 ⟨subd19_1_221, List.forall_mem_cons.2 ⟨subd19_1_222, List.forall_mem_cons.2 ⟨subd19_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_224 : subd19_1 [-3, -1, 1] = true := by decide +kernel
theorem subd19_1_225 : subd19_1 [-3, -1, 2] = true := by decide +kernel
theorem subd19_1_226 : subd19_1 [-3, -1, 3] = true := by decide +kernel
theorem subd19_1_227 : subd19_1 [-3, -1, 4] = true := by decide +kernel
theorem subd19_1_228 : subd19_1 [-3, -1, 5] = true := by decide +kernel
theorem subd19_1_229 : subd19_1 [-3, -1, 6] = true := by decide +kernel
theorem subd19_1_230 : subd19_1 [-3, -1, 7] = true := by decide +kernel
theorem subd19_1_231 : subd19_1 [-3, -1, 8] = true := by decide +kernel
theorem subd19_1_232 : subd19_1 [-3, 0, -6] = true := by decide +kernel
theorem subd19_1_233 : subd19_1 [-3, 0, -5] = true := by decide +kernel
theorem subd19_1_234 : subd19_1 [-3, 0, -4] = true := by decide +kernel
theorem subd19_1_235 : subd19_1 [-3, 0, -3] = true := by decide +kernel
theorem subd19_1_236 : subd19_1 [-3, 0, -2] = true := by decide +kernel
theorem subd19_1_237 : subd19_1 [-3, 0, -1] = true := by decide +kernel
theorem subd19_1_238 : subd19_1 [-3, 0, 0] = true := by decide +kernel
theorem subd19_1_239 : subd19_1 [-3, 0, 1] = true := by decide +kernel
theorem subd19_1_240 : subd19_1 [-3, 0, 2] = true := by decide +kernel
theorem subd19_1_241 : subd19_1 [-3, 0, 3] = true := by decide +kernel
theorem subd19_1_242 : subd19_1 [-3, 0, 4] = true := by decide +kernel
theorem subd19_1_243 : subd19_1 [-3, 0, 5] = true := by decide +kernel
theorem subd19_1_244 : subd19_1 [-3, 0, 6] = true := by decide +kernel
theorem subd19_1_245 : subd19_1 [-3, 0, 7] = true := by decide +kernel
theorem subd19_1_246 : subd19_1 [-3, 0, 8] = true := by decide +kernel
theorem subd19_1_247 : subd19_1 [-3, 1, -6] = true := by decide +kernel
theorem subd19_1_248 : subd19_1 [-3, 1, -5] = true := by decide +kernel
theorem subd19_1_249 : subd19_1 [-3, 1, -4] = true := by decide +kernel
theorem subd19_1_250 : subd19_1 [-3, 1, -3] = true := by decide +kernel
theorem subd19_1_251 : subd19_1 [-3, 1, -2] = true := by decide +kernel
theorem subd19_1_252 : subd19_1 [-3, 1, -1] = true := by decide +kernel
theorem subd19_1_253 : subd19_1 [-3, 1, 0] = true := by decide +kernel
theorem subd19_1_254 : subd19_1 [-3, 1, 1] = true := by decide +kernel
theorem subd19_1_255 : subd19_1 [-3, 1, 2] = true := by decide +kernel
theorem sbd19_1_7 : ∀ q ∈ blkd19_1_7, subd19_1 q = true := by
  unfold blkd19_1_7
  exact List.forall_mem_cons.2 ⟨subd19_1_224, List.forall_mem_cons.2 ⟨subd19_1_225, List.forall_mem_cons.2 ⟨subd19_1_226, List.forall_mem_cons.2 ⟨subd19_1_227, List.forall_mem_cons.2 ⟨subd19_1_228, List.forall_mem_cons.2 ⟨subd19_1_229, List.forall_mem_cons.2 ⟨subd19_1_230, List.forall_mem_cons.2 ⟨subd19_1_231, List.forall_mem_cons.2 ⟨subd19_1_232, List.forall_mem_cons.2 ⟨subd19_1_233, List.forall_mem_cons.2 ⟨subd19_1_234, List.forall_mem_cons.2 ⟨subd19_1_235, List.forall_mem_cons.2 ⟨subd19_1_236, List.forall_mem_cons.2 ⟨subd19_1_237, List.forall_mem_cons.2 ⟨subd19_1_238, List.forall_mem_cons.2 ⟨subd19_1_239, List.forall_mem_cons.2 ⟨subd19_1_240, List.forall_mem_cons.2 ⟨subd19_1_241, List.forall_mem_cons.2 ⟨subd19_1_242, List.forall_mem_cons.2 ⟨subd19_1_243, List.forall_mem_cons.2 ⟨subd19_1_244, List.forall_mem_cons.2 ⟨subd19_1_245, List.forall_mem_cons.2 ⟨subd19_1_246, List.forall_mem_cons.2 ⟨subd19_1_247, List.forall_mem_cons.2 ⟨subd19_1_248, List.forall_mem_cons.2 ⟨subd19_1_249, List.forall_mem_cons.2 ⟨subd19_1_250, List.forall_mem_cons.2 ⟨subd19_1_251, List.forall_mem_cons.2 ⟨subd19_1_252, List.forall_mem_cons.2 ⟨subd19_1_253, List.forall_mem_cons.2 ⟨subd19_1_254, List.forall_mem_cons.2 ⟨subd19_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_256 : subd19_1 [-3, 1, 3] = true := by decide +kernel
theorem subd19_1_257 : subd19_1 [-3, 1, 4] = true := by decide +kernel
theorem subd19_1_258 : subd19_1 [-3, 1, 5] = true := by decide +kernel
theorem subd19_1_259 : subd19_1 [-3, 1, 6] = true := by decide +kernel
theorem subd19_1_260 : subd19_1 [-3, 1, 7] = true := by decide +kernel
theorem subd19_1_261 : subd19_1 [-3, 1, 8] = true := by decide +kernel
theorem subd19_1_262 : subd19_1 [-3, 2, -5] = true := by decide +kernel
theorem subd19_1_263 : subd19_1 [-3, 2, -4] = true := by decide +kernel
theorem subd19_1_264 : subd19_1 [-3, 2, -3] = true := by decide +kernel
theorem subd19_1_265 : subd19_1 [-3, 2, -2] = true := by decide +kernel
theorem subd19_1_266 : subd19_1 [-3, 2, -1] = true := by decide +kernel
theorem subd19_1_267 : subd19_1 [-3, 2, 0] = true := by decide +kernel
theorem subd19_1_268 : subd19_1 [-3, 2, 1] = true := by decide +kernel
theorem subd19_1_269 : subd19_1 [-3, 2, 2] = true := by decide +kernel
theorem subd19_1_270 : subd19_1 [-3, 2, 3] = true := by decide +kernel
theorem subd19_1_271 : subd19_1 [-3, 2, 4] = true := by decide +kernel
theorem subd19_1_272 : subd19_1 [-3, 2, 5] = true := by decide +kernel
theorem subd19_1_273 : subd19_1 [-3, 2, 6] = true := by decide +kernel
theorem subd19_1_274 : subd19_1 [-3, 2, 7] = true := by decide +kernel
theorem subd19_1_275 : subd19_1 [-3, 2, 8] = true := by decide +kernel
theorem subd19_1_276 : subd19_1 [-3, 2, 9] = true := by decide +kernel
theorem subd19_1_277 : subd19_1 [-3, 3, -5] = true := by decide +kernel
theorem subd19_1_278 : subd19_1 [-3, 3, -4] = true := by decide +kernel
theorem subd19_1_279 : subd19_1 [-3, 3, -3] = true := by decide +kernel
theorem subd19_1_280 : subd19_1 [-3, 3, -2] = true := by decide +kernel
theorem subd19_1_281 : subd19_1 [-3, 3, -1] = true := by decide +kernel
theorem subd19_1_282 : subd19_1 [-3, 3, 0] = true := by decide +kernel
theorem subd19_1_283 : subd19_1 [-3, 3, 1] = true := by decide +kernel
theorem subd19_1_284 : subd19_1 [-3, 3, 2] = true := by decide +kernel
theorem subd19_1_285 : subd19_1 [-3, 3, 3] = true := by decide +kernel
theorem subd19_1_286 : subd19_1 [-3, 3, 4] = true := by decide +kernel
theorem subd19_1_287 : subd19_1 [-3, 3, 5] = true := by decide +kernel
theorem sbd19_1_8 : ∀ q ∈ blkd19_1_8, subd19_1 q = true := by
  unfold blkd19_1_8
  exact List.forall_mem_cons.2 ⟨subd19_1_256, List.forall_mem_cons.2 ⟨subd19_1_257, List.forall_mem_cons.2 ⟨subd19_1_258, List.forall_mem_cons.2 ⟨subd19_1_259, List.forall_mem_cons.2 ⟨subd19_1_260, List.forall_mem_cons.2 ⟨subd19_1_261, List.forall_mem_cons.2 ⟨subd19_1_262, List.forall_mem_cons.2 ⟨subd19_1_263, List.forall_mem_cons.2 ⟨subd19_1_264, List.forall_mem_cons.2 ⟨subd19_1_265, List.forall_mem_cons.2 ⟨subd19_1_266, List.forall_mem_cons.2 ⟨subd19_1_267, List.forall_mem_cons.2 ⟨subd19_1_268, List.forall_mem_cons.2 ⟨subd19_1_269, List.forall_mem_cons.2 ⟨subd19_1_270, List.forall_mem_cons.2 ⟨subd19_1_271, List.forall_mem_cons.2 ⟨subd19_1_272, List.forall_mem_cons.2 ⟨subd19_1_273, List.forall_mem_cons.2 ⟨subd19_1_274, List.forall_mem_cons.2 ⟨subd19_1_275, List.forall_mem_cons.2 ⟨subd19_1_276, List.forall_mem_cons.2 ⟨subd19_1_277, List.forall_mem_cons.2 ⟨subd19_1_278, List.forall_mem_cons.2 ⟨subd19_1_279, List.forall_mem_cons.2 ⟨subd19_1_280, List.forall_mem_cons.2 ⟨subd19_1_281, List.forall_mem_cons.2 ⟨subd19_1_282, List.forall_mem_cons.2 ⟨subd19_1_283, List.forall_mem_cons.2 ⟨subd19_1_284, List.forall_mem_cons.2 ⟨subd19_1_285, List.forall_mem_cons.2 ⟨subd19_1_286, List.forall_mem_cons.2 ⟨subd19_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
