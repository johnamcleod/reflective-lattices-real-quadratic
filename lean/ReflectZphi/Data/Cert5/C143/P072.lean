import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_3_0 : subd19_3 [-8, -3] = true := by decide +kernel
theorem subd19_3_1 : subd19_3 [-8, -2] = true := by decide +kernel
theorem subd19_3_2 : subd19_3 [-8, -1] = true := by decide +kernel
theorem subd19_3_3 : subd19_3 [-8, 0] = true := by decide +kernel
theorem subd19_3_4 : subd19_3 [-8, 1] = true := by decide +kernel
theorem subd19_3_5 : subd19_3 [-8, 2] = true := by decide +kernel
theorem subd19_3_6 : subd19_3 [-8, 3] = true := by decide +kernel
theorem subd19_3_7 : subd19_3 [-7, -5] = true := by decide +kernel
theorem subd19_3_8 : subd19_3 [-7, -4] = true := by decide +kernel
theorem subd19_3_9 : subd19_3 [-7, -3] = true := by decide +kernel
theorem subd19_3_10 : subd19_3 [-7, -2] = true := by decide +kernel
theorem subd19_3_11 : subd19_3 [-7, -1] = true := by decide +kernel
theorem subd19_3_12 : subd19_3 [-7, 0] = true := by decide +kernel
theorem subd19_3_13 : subd19_3 [-7, 1] = true := by decide +kernel
theorem subd19_3_14 : subd19_3 [-7, 2] = true := by decide +kernel
theorem subd19_3_15 : subd19_3 [-7, 3] = true := by decide +kernel
theorem subd19_3_16 : subd19_3 [-7, 4] = true := by decide +kernel
theorem subd19_3_17 : subd19_3 [-7, 5] = true := by decide +kernel
theorem subd19_3_18 : subd19_3 [-6, -6] = true := by decide +kernel
theorem subd19_3_19 : subd19_3 [-6, -5] = true := by decide +kernel
theorem subd19_3_20 : subd19_3 [-6, -4] = true := by decide +kernel
theorem subd19_3_21 : subd19_3 [-6, -3] = true := by decide +kernel
theorem subd19_3_22 : subd19_3 [-6, -2] = true := by decide +kernel
theorem subd19_3_23 : subd19_3 [-6, -1] = true := by decide +kernel
theorem subd19_3_24 : subd19_3 [-6, 0] = true := by decide +kernel
theorem subd19_3_25 : subd19_3 [-6, 1] = true := by decide +kernel
theorem subd19_3_26 : subd19_3 [-6, 2] = true := by decide +kernel
theorem subd19_3_27 : subd19_3 [-6, 3] = true := by decide +kernel
theorem subd19_3_28 : subd19_3 [-6, 4] = true := by decide +kernel
theorem subd19_3_29 : subd19_3 [-6, 5] = true := by decide +kernel
theorem subd19_3_30 : subd19_3 [-6, 6] = true := by decide +kernel
theorem subd19_3_31 : subd19_3 [-5, -7] = true := by decide +kernel
theorem sbd19_3_0 : ∀ q ∈ blkd19_3_0, subd19_3 q = true := by
  unfold blkd19_3_0
  exact List.forall_mem_cons.2 ⟨subd19_3_0, List.forall_mem_cons.2 ⟨subd19_3_1, List.forall_mem_cons.2 ⟨subd19_3_2, List.forall_mem_cons.2 ⟨subd19_3_3, List.forall_mem_cons.2 ⟨subd19_3_4, List.forall_mem_cons.2 ⟨subd19_3_5, List.forall_mem_cons.2 ⟨subd19_3_6, List.forall_mem_cons.2 ⟨subd19_3_7, List.forall_mem_cons.2 ⟨subd19_3_8, List.forall_mem_cons.2 ⟨subd19_3_9, List.forall_mem_cons.2 ⟨subd19_3_10, List.forall_mem_cons.2 ⟨subd19_3_11, List.forall_mem_cons.2 ⟨subd19_3_12, List.forall_mem_cons.2 ⟨subd19_3_13, List.forall_mem_cons.2 ⟨subd19_3_14, List.forall_mem_cons.2 ⟨subd19_3_15, List.forall_mem_cons.2 ⟨subd19_3_16, List.forall_mem_cons.2 ⟨subd19_3_17, List.forall_mem_cons.2 ⟨subd19_3_18, List.forall_mem_cons.2 ⟨subd19_3_19, List.forall_mem_cons.2 ⟨subd19_3_20, List.forall_mem_cons.2 ⟨subd19_3_21, List.forall_mem_cons.2 ⟨subd19_3_22, List.forall_mem_cons.2 ⟨subd19_3_23, List.forall_mem_cons.2 ⟨subd19_3_24, List.forall_mem_cons.2 ⟨subd19_3_25, List.forall_mem_cons.2 ⟨subd19_3_26, List.forall_mem_cons.2 ⟨subd19_3_27, List.forall_mem_cons.2 ⟨subd19_3_28, List.forall_mem_cons.2 ⟨subd19_3_29, List.forall_mem_cons.2 ⟨subd19_3_30, List.forall_mem_cons.2 ⟨subd19_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_32 : subd19_3 [-5, -6] = true := by decide +kernel
theorem subd19_3_33 : subd19_3 [-5, -5] = true := by decide +kernel
theorem subd19_3_34 : subd19_3 [-5, -4] = true := by decide +kernel
theorem subd19_3_35 : subd19_3 [-5, -3] = true := by decide +kernel
theorem subd19_3_36 : subd19_3 [-5, -2, -5] = true := by decide +kernel
theorem subd19_3_37 : subd19_3 [-5, -2, -4] = true := by decide +kernel
theorem subd19_3_38 : subd19_3 [-5, -2, -3] = true := by decide +kernel
theorem subd19_3_39 : subd19_3 [-5, -2, -2] = true := by decide +kernel
theorem subd19_3_40 : subd19_3 [-5, -2, -1] = true := by decide +kernel
theorem subd19_3_41 : subd19_3 [-5, -2, 0] = true := by decide +kernel
theorem subd19_3_42 : subd19_3 [-5, -2, 1] = true := by decide +kernel
theorem subd19_3_43 : subd19_3 [-5, -2, 2] = true := by decide +kernel
theorem subd19_3_44 : subd19_3 [-5, -2, 3] = true := by decide +kernel
theorem subd19_3_45 : subd19_3 [-5, -2, 4] = true := by decide +kernel
theorem subd19_3_46 : subd19_3 [-5, -2, 5] = true := by decide +kernel
theorem subd19_3_47 : subd19_3 [-5, -2, 6] = true := by decide +kernel
theorem subd19_3_48 : subd19_3 [-5, -2, 7] = true := by decide +kernel
theorem subd19_3_49 : subd19_3 [-5, -2, 8] = true := by decide +kernel
theorem subd19_3_50 : subd19_3 [-5, -2, 9] = true := by decide +kernel
theorem subd19_3_51 : subd19_3 [-5, -1, -5] = true := by decide +kernel
theorem subd19_3_52 : subd19_3 [-5, -1, -4] = true := by decide +kernel
theorem subd19_3_53 : subd19_3 [-5, -1, -3] = true := by decide +kernel
theorem subd19_3_54 : subd19_3 [-5, -1, -2] = true := by decide +kernel
theorem subd19_3_55 : subd19_3 [-5, -1, -1] = true := by decide +kernel
theorem subd19_3_56 : subd19_3 [-5, -1, 0] = true := by decide +kernel
theorem subd19_3_57 : subd19_3 [-5, -1, 1] = true := by decide +kernel
theorem subd19_3_58 : subd19_3 [-5, -1, 2] = true := by decide +kernel
theorem subd19_3_59 : subd19_3 [-5, -1, 3] = true := by decide +kernel
theorem subd19_3_60 : subd19_3 [-5, -1, 4] = true := by decide +kernel
theorem subd19_3_61 : subd19_3 [-5, -1, 5] = true := by decide +kernel
theorem subd19_3_62 : subd19_3 [-5, -1, 6] = true := by decide +kernel
theorem subd19_3_63 : subd19_3 [-5, -1, 7] = true := by decide +kernel
theorem sbd19_3_1 : ∀ q ∈ blkd19_3_1, subd19_3 q = true := by
  unfold blkd19_3_1
  exact List.forall_mem_cons.2 ⟨subd19_3_32, List.forall_mem_cons.2 ⟨subd19_3_33, List.forall_mem_cons.2 ⟨subd19_3_34, List.forall_mem_cons.2 ⟨subd19_3_35, List.forall_mem_cons.2 ⟨subd19_3_36, List.forall_mem_cons.2 ⟨subd19_3_37, List.forall_mem_cons.2 ⟨subd19_3_38, List.forall_mem_cons.2 ⟨subd19_3_39, List.forall_mem_cons.2 ⟨subd19_3_40, List.forall_mem_cons.2 ⟨subd19_3_41, List.forall_mem_cons.2 ⟨subd19_3_42, List.forall_mem_cons.2 ⟨subd19_3_43, List.forall_mem_cons.2 ⟨subd19_3_44, List.forall_mem_cons.2 ⟨subd19_3_45, List.forall_mem_cons.2 ⟨subd19_3_46, List.forall_mem_cons.2 ⟨subd19_3_47, List.forall_mem_cons.2 ⟨subd19_3_48, List.forall_mem_cons.2 ⟨subd19_3_49, List.forall_mem_cons.2 ⟨subd19_3_50, List.forall_mem_cons.2 ⟨subd19_3_51, List.forall_mem_cons.2 ⟨subd19_3_52, List.forall_mem_cons.2 ⟨subd19_3_53, List.forall_mem_cons.2 ⟨subd19_3_54, List.forall_mem_cons.2 ⟨subd19_3_55, List.forall_mem_cons.2 ⟨subd19_3_56, List.forall_mem_cons.2 ⟨subd19_3_57, List.forall_mem_cons.2 ⟨subd19_3_58, List.forall_mem_cons.2 ⟨subd19_3_59, List.forall_mem_cons.2 ⟨subd19_3_60, List.forall_mem_cons.2 ⟨subd19_3_61, List.forall_mem_cons.2 ⟨subd19_3_62, List.forall_mem_cons.2 ⟨subd19_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_64 : subd19_3 [-5, -1, 8] = true := by decide +kernel
theorem subd19_3_65 : subd19_3 [-5, -1, 9] = true := by decide +kernel
theorem subd19_3_66 : subd19_3 [-5, 0, -6] = true := by decide +kernel
theorem subd19_3_67 : subd19_3 [-5, 0, -5] = true := by decide +kernel
theorem subd19_3_68 : subd19_3 [-5, 0, -4] = true := by decide +kernel
theorem subd19_3_69 : subd19_3 [-5, 0, -3] = true := by decide +kernel
theorem subd19_3_70 : subd19_3 [-5, 0, -2] = true := by decide +kernel
theorem subd19_3_71 : subd19_3 [-5, 0, -1] = true := by decide +kernel
theorem subd19_3_72 : subd19_3 [-5, 0, 0] = true := by decide +kernel
theorem subd19_3_73 : subd19_3 [-5, 0, 1] = true := by decide +kernel
theorem subd19_3_74 : subd19_3 [-5, 0, 2] = true := by decide +kernel
theorem subd19_3_75 : subd19_3 [-5, 0, 3] = true := by decide +kernel
theorem subd19_3_76 : subd19_3 [-5, 0, 4] = true := by decide +kernel
theorem subd19_3_77 : subd19_3 [-5, 0, 5] = true := by decide +kernel
theorem subd19_3_78 : subd19_3 [-5, 0, 6] = true := by decide +kernel
theorem subd19_3_79 : subd19_3 [-5, 0, 7] = true := by decide +kernel
theorem subd19_3_80 : subd19_3 [-5, 0, 8] = true := by decide +kernel
theorem subd19_3_81 : subd19_3 [-5, 1, -6] = true := by decide +kernel
theorem subd19_3_82 : subd19_3 [-5, 1, -5] = true := by decide +kernel
theorem subd19_3_83 : subd19_3 [-5, 1, -4] = true := by decide +kernel
theorem subd19_3_84 : subd19_3 [-5, 1, -3] = true := by decide +kernel
theorem subd19_3_85 : subd19_3 [-5, 1, -2] = true := by decide +kernel
theorem subd19_3_86 : subd19_3 [-5, 1, -1] = true := by decide +kernel
theorem subd19_3_87 : subd19_3 [-5, 1, 0] = true := by decide +kernel
theorem subd19_3_88 : subd19_3 [-5, 1, 1] = true := by decide +kernel
theorem subd19_3_89 : subd19_3 [-5, 1, 2] = true := by decide +kernel
theorem subd19_3_90 : subd19_3 [-5, 1, 3] = true := by decide +kernel
theorem subd19_3_91 : subd19_3 [-5, 1, 4] = true := by decide +kernel
theorem subd19_3_92 : subd19_3 [-5, 1, 5] = true := by decide +kernel
theorem subd19_3_93 : subd19_3 [-5, 1, 6] = true := by decide +kernel
theorem subd19_3_94 : subd19_3 [-5, 1, 7] = true := by decide +kernel
theorem subd19_3_95 : subd19_3 [-5, 1, 8] = true := by decide +kernel
theorem sbd19_3_2 : ∀ q ∈ blkd19_3_2, subd19_3 q = true := by
  unfold blkd19_3_2
  exact List.forall_mem_cons.2 ⟨subd19_3_64, List.forall_mem_cons.2 ⟨subd19_3_65, List.forall_mem_cons.2 ⟨subd19_3_66, List.forall_mem_cons.2 ⟨subd19_3_67, List.forall_mem_cons.2 ⟨subd19_3_68, List.forall_mem_cons.2 ⟨subd19_3_69, List.forall_mem_cons.2 ⟨subd19_3_70, List.forall_mem_cons.2 ⟨subd19_3_71, List.forall_mem_cons.2 ⟨subd19_3_72, List.forall_mem_cons.2 ⟨subd19_3_73, List.forall_mem_cons.2 ⟨subd19_3_74, List.forall_mem_cons.2 ⟨subd19_3_75, List.forall_mem_cons.2 ⟨subd19_3_76, List.forall_mem_cons.2 ⟨subd19_3_77, List.forall_mem_cons.2 ⟨subd19_3_78, List.forall_mem_cons.2 ⟨subd19_3_79, List.forall_mem_cons.2 ⟨subd19_3_80, List.forall_mem_cons.2 ⟨subd19_3_81, List.forall_mem_cons.2 ⟨subd19_3_82, List.forall_mem_cons.2 ⟨subd19_3_83, List.forall_mem_cons.2 ⟨subd19_3_84, List.forall_mem_cons.2 ⟨subd19_3_85, List.forall_mem_cons.2 ⟨subd19_3_86, List.forall_mem_cons.2 ⟨subd19_3_87, List.forall_mem_cons.2 ⟨subd19_3_88, List.forall_mem_cons.2 ⟨subd19_3_89, List.forall_mem_cons.2 ⟨subd19_3_90, List.forall_mem_cons.2 ⟨subd19_3_91, List.forall_mem_cons.2 ⟨subd19_3_92, List.forall_mem_cons.2 ⟨subd19_3_93, List.forall_mem_cons.2 ⟨subd19_3_94, List.forall_mem_cons.2 ⟨subd19_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_96 : subd19_3 [-5, 2, -7] = true := by decide +kernel
theorem subd19_3_97 : subd19_3 [-5, 2, -6] = true := by decide +kernel
theorem subd19_3_98 : subd19_3 [-5, 2, -5] = true := by decide +kernel
theorem subd19_3_99 : subd19_3 [-5, 2, -4] = true := by decide +kernel
theorem subd19_3_100 : subd19_3 [-5, 2, -3] = true := by decide +kernel
theorem subd19_3_101 : subd19_3 [-5, 2, -2] = true := by decide +kernel
theorem subd19_3_102 : subd19_3 [-5, 2, -1] = true := by decide +kernel
theorem subd19_3_103 : subd19_3 [-5, 2, 0] = true := by decide +kernel
theorem subd19_3_104 : subd19_3 [-5, 2, 1] = true := by decide +kernel
theorem subd19_3_105 : subd19_3 [-5, 2, 2] = true := by decide +kernel
theorem subd19_3_106 : subd19_3 [-5, 2, 3] = true := by decide +kernel
theorem subd19_3_107 : subd19_3 [-5, 2, 4] = true := by decide +kernel
theorem subd19_3_108 : subd19_3 [-5, 2, 5] = true := by decide +kernel
theorem subd19_3_109 : subd19_3 [-5, 2, 6] = true := by decide +kernel
theorem subd19_3_110 : subd19_3 [-5, 2, 7] = true := by decide +kernel
theorem subd19_3_111 : subd19_3 [-5, 3] = true := by decide +kernel
theorem subd19_3_112 : subd19_3 [-5, 4] = true := by decide +kernel
theorem subd19_3_113 : subd19_3 [-5, 5] = true := by decide +kernel
theorem subd19_3_114 : subd19_3 [-5, 6] = true := by decide +kernel
theorem subd19_3_115 : subd19_3 [-4, -7] = true := by decide +kernel
theorem subd19_3_116 : subd19_3 [-4, -6] = true := by decide +kernel
theorem subd19_3_117 : subd19_3 [-4, -5] = true := by decide +kernel
theorem subd19_3_118 : subd19_3 [-4, -4] = true := by decide +kernel
theorem subd19_3_119 : subd19_3 [-4, -3, -5] = true := by decide +kernel
theorem subd19_3_120 : subd19_3 [-4, -3, -4] = true := by decide +kernel
theorem subd19_3_121 : subd19_3 [-4, -3, -3] = true := by decide +kernel
theorem subd19_3_122 : subd19_3 [-4, -3, -2] = true := by decide +kernel
theorem subd19_3_123 : subd19_3 [-4, -3, -1] = true := by decide +kernel
theorem subd19_3_124 : subd19_3 [-4, -3, 0] = true := by decide +kernel
theorem subd19_3_125 : subd19_3 [-4, -3, 1] = true := by decide +kernel
theorem subd19_3_126 : subd19_3 [-4, -3, 2] = true := by decide +kernel
theorem subd19_3_127 : subd19_3 [-4, -3, 3] = true := by decide +kernel
theorem sbd19_3_3 : ∀ q ∈ blkd19_3_3, subd19_3 q = true := by
  unfold blkd19_3_3
  exact List.forall_mem_cons.2 ⟨subd19_3_96, List.forall_mem_cons.2 ⟨subd19_3_97, List.forall_mem_cons.2 ⟨subd19_3_98, List.forall_mem_cons.2 ⟨subd19_3_99, List.forall_mem_cons.2 ⟨subd19_3_100, List.forall_mem_cons.2 ⟨subd19_3_101, List.forall_mem_cons.2 ⟨subd19_3_102, List.forall_mem_cons.2 ⟨subd19_3_103, List.forall_mem_cons.2 ⟨subd19_3_104, List.forall_mem_cons.2 ⟨subd19_3_105, List.forall_mem_cons.2 ⟨subd19_3_106, List.forall_mem_cons.2 ⟨subd19_3_107, List.forall_mem_cons.2 ⟨subd19_3_108, List.forall_mem_cons.2 ⟨subd19_3_109, List.forall_mem_cons.2 ⟨subd19_3_110, List.forall_mem_cons.2 ⟨subd19_3_111, List.forall_mem_cons.2 ⟨subd19_3_112, List.forall_mem_cons.2 ⟨subd19_3_113, List.forall_mem_cons.2 ⟨subd19_3_114, List.forall_mem_cons.2 ⟨subd19_3_115, List.forall_mem_cons.2 ⟨subd19_3_116, List.forall_mem_cons.2 ⟨subd19_3_117, List.forall_mem_cons.2 ⟨subd19_3_118, List.forall_mem_cons.2 ⟨subd19_3_119, List.forall_mem_cons.2 ⟨subd19_3_120, List.forall_mem_cons.2 ⟨subd19_3_121, List.forall_mem_cons.2 ⟨subd19_3_122, List.forall_mem_cons.2 ⟨subd19_3_123, List.forall_mem_cons.2 ⟨subd19_3_124, List.forall_mem_cons.2 ⟨subd19_3_125, List.forall_mem_cons.2 ⟨subd19_3_126, List.forall_mem_cons.2 ⟨subd19_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_128 : subd19_3 [-4, -3, 4] = true := by decide +kernel
theorem subd19_3_129 : subd19_3 [-4, -3, 5] = true := by decide +kernel
theorem subd19_3_130 : subd19_3 [-4, -3, 6] = true := by decide +kernel
theorem subd19_3_131 : subd19_3 [-4, -3, 7] = true := by decide +kernel
theorem subd19_3_132 : subd19_3 [-4, -3, 8] = true := by decide +kernel
theorem subd19_3_133 : subd19_3 [-4, -3, 9] = true := by decide +kernel
theorem subd19_3_134 : subd19_3 [-4, -2, -6] = true := by decide +kernel
theorem subd19_3_135 : subd19_3 [-4, -2, -5] = true := by decide +kernel
theorem subd19_3_136 : subd19_3 [-4, -2, -4] = true := by decide +kernel
theorem subd19_3_137 : subd19_3 [-4, -2, -3] = true := by decide +kernel
theorem subd19_3_138 : subd19_3 [-4, -2, -2] = true := by decide +kernel
theorem subd19_3_139 : subd19_3 [-4, -2, -1] = true := by decide +kernel
theorem subd19_3_140 : subd19_3 [-4, -2, 0] = true := by decide +kernel
theorem subd19_3_141 : subd19_3 [-4, -2, 1] = true := by decide +kernel
theorem subd19_3_142 : subd19_3 [-4, -2, 2] = true := by decide +kernel
theorem subd19_3_143 : subd19_3 [-4, -2, 3] = true := by decide +kernel
theorem subd19_3_144 : subd19_3 [-4, -2, 4] = true := by decide +kernel
theorem subd19_3_145 : subd19_3 [-4, -2, 5] = true := by decide +kernel
theorem subd19_3_146 : subd19_3 [-4, -2, 6] = true := by decide +kernel
theorem subd19_3_147 : subd19_3 [-4, -2, 7] = true := by decide +kernel
theorem subd19_3_148 : subd19_3 [-4, -2, 8] = true := by decide +kernel
theorem subd19_3_149 : subd19_3 [-4, -2, 9] = true := by decide +kernel
theorem subd19_3_150 : subd19_3 [-4, -1, -6] = true := by decide +kernel
theorem subd19_3_151 : subd19_3 [-4, -1, -5] = true := by decide +kernel
theorem subd19_3_152 : subd19_3 [-4, -1, -4] = true := by decide +kernel
theorem subd19_3_153 : subd19_3 [-4, -1, -3] = true := by decide +kernel
theorem subd19_3_154 : subd19_3 [-4, -1, -2] = true := by decide +kernel
theorem subd19_3_155 : subd19_3 [-4, -1, -1] = true := by decide +kernel
theorem subd19_3_156 : subd19_3 [-4, -1, 0] = true := by decide +kernel
theorem subd19_3_157 : subd19_3 [-4, -1, 1] = true := by decide +kernel
theorem subd19_3_158 : subd19_3 [-4, -1, 2] = true := by decide +kernel
theorem subd19_3_159 : subd19_3 [-4, -1, 3] = true := by decide +kernel
theorem sbd19_3_4 : ∀ q ∈ blkd19_3_4, subd19_3 q = true := by
  unfold blkd19_3_4
  exact List.forall_mem_cons.2 ⟨subd19_3_128, List.forall_mem_cons.2 ⟨subd19_3_129, List.forall_mem_cons.2 ⟨subd19_3_130, List.forall_mem_cons.2 ⟨subd19_3_131, List.forall_mem_cons.2 ⟨subd19_3_132, List.forall_mem_cons.2 ⟨subd19_3_133, List.forall_mem_cons.2 ⟨subd19_3_134, List.forall_mem_cons.2 ⟨subd19_3_135, List.forall_mem_cons.2 ⟨subd19_3_136, List.forall_mem_cons.2 ⟨subd19_3_137, List.forall_mem_cons.2 ⟨subd19_3_138, List.forall_mem_cons.2 ⟨subd19_3_139, List.forall_mem_cons.2 ⟨subd19_3_140, List.forall_mem_cons.2 ⟨subd19_3_141, List.forall_mem_cons.2 ⟨subd19_3_142, List.forall_mem_cons.2 ⟨subd19_3_143, List.forall_mem_cons.2 ⟨subd19_3_144, List.forall_mem_cons.2 ⟨subd19_3_145, List.forall_mem_cons.2 ⟨subd19_3_146, List.forall_mem_cons.2 ⟨subd19_3_147, List.forall_mem_cons.2 ⟨subd19_3_148, List.forall_mem_cons.2 ⟨subd19_3_149, List.forall_mem_cons.2 ⟨subd19_3_150, List.forall_mem_cons.2 ⟨subd19_3_151, List.forall_mem_cons.2 ⟨subd19_3_152, List.forall_mem_cons.2 ⟨subd19_3_153, List.forall_mem_cons.2 ⟨subd19_3_154, List.forall_mem_cons.2 ⟨subd19_3_155, List.forall_mem_cons.2 ⟨subd19_3_156, List.forall_mem_cons.2 ⟨subd19_3_157, List.forall_mem_cons.2 ⟨subd19_3_158, List.forall_mem_cons.2 ⟨subd19_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_160 : subd19_3 [-4, -1, 4] = true := by decide +kernel
theorem subd19_3_161 : subd19_3 [-4, -1, 5] = true := by decide +kernel
theorem subd19_3_162 : subd19_3 [-4, -1, 6] = true := by decide +kernel
theorem subd19_3_163 : subd19_3 [-4, -1, 7] = true := by decide +kernel
theorem subd19_3_164 : subd19_3 [-4, -1, 8] = true := by decide +kernel
theorem subd19_3_165 : subd19_3 [-4, -1, 9] = true := by decide +kernel
theorem subd19_3_166 : subd19_3 [-4, 0, -7] = true := by decide +kernel
theorem subd19_3_167 : subd19_3 [-4, 0, -6] = true := by decide +kernel
theorem subd19_3_168 : subd19_3 [-4, 0, -5] = true := by decide +kernel
theorem subd19_3_169 : subd19_3 [-4, 0, -4] = true := by decide +kernel
theorem subd19_3_170 : subd19_3 [-4, 0, -3] = true := by decide +kernel
theorem subd19_3_171 : subd19_3 [-4, 0, -2] = true := by decide +kernel
theorem subd19_3_172 : subd19_3 [-4, 0, -1] = true := by decide +kernel
theorem subd19_3_173 : subd19_3 [-4, 0, 0] = true := by decide +kernel
theorem subd19_3_174 : subd19_3 [-4, 0, 1] = true := by decide +kernel
theorem subd19_3_175 : subd19_3 [-4, 0, 2] = true := by decide +kernel
theorem subd19_3_176 : subd19_3 [-4, 0, 3] = true := by decide +kernel
theorem subd19_3_177 : subd19_3 [-4, 0, 4] = true := by decide +kernel
theorem subd19_3_178 : subd19_3 [-4, 0, 5] = true := by decide +kernel
theorem subd19_3_179 : subd19_3 [-4, 0, 6] = true := by decide +kernel
theorem subd19_3_180 : subd19_3 [-4, 0, 7] = true := by decide +kernel
theorem subd19_3_181 : subd19_3 [-4, 0, 8] = true := by decide +kernel
theorem subd19_3_182 : subd19_3 [-4, 0, 9] = true := by decide +kernel
theorem subd19_3_183 : subd19_3 [-4, 1, -7] = true := by decide +kernel
theorem subd19_3_184 : subd19_3 [-4, 1, -6] = true := by decide +kernel
theorem subd19_3_185 : subd19_3 [-4, 1, -5] = true := by decide +kernel
theorem subd19_3_186 : subd19_3 [-4, 1, -4] = true := by decide +kernel
theorem subd19_3_187 : subd19_3 [-4, 1, -3] = true := by decide +kernel
theorem subd19_3_188 : subd19_3 [-4, 1, -2] = true := by decide +kernel
theorem subd19_3_189 : subd19_3 [-4, 1, -1] = true := by decide +kernel
theorem subd19_3_190 : subd19_3 [-4, 1, 0] = true := by decide +kernel
theorem subd19_3_191 : subd19_3 [-4, 1, 1] = true := by decide +kernel
theorem sbd19_3_5 : ∀ q ∈ blkd19_3_5, subd19_3 q = true := by
  unfold blkd19_3_5
  exact List.forall_mem_cons.2 ⟨subd19_3_160, List.forall_mem_cons.2 ⟨subd19_3_161, List.forall_mem_cons.2 ⟨subd19_3_162, List.forall_mem_cons.2 ⟨subd19_3_163, List.forall_mem_cons.2 ⟨subd19_3_164, List.forall_mem_cons.2 ⟨subd19_3_165, List.forall_mem_cons.2 ⟨subd19_3_166, List.forall_mem_cons.2 ⟨subd19_3_167, List.forall_mem_cons.2 ⟨subd19_3_168, List.forall_mem_cons.2 ⟨subd19_3_169, List.forall_mem_cons.2 ⟨subd19_3_170, List.forall_mem_cons.2 ⟨subd19_3_171, List.forall_mem_cons.2 ⟨subd19_3_172, List.forall_mem_cons.2 ⟨subd19_3_173, List.forall_mem_cons.2 ⟨subd19_3_174, List.forall_mem_cons.2 ⟨subd19_3_175, List.forall_mem_cons.2 ⟨subd19_3_176, List.forall_mem_cons.2 ⟨subd19_3_177, List.forall_mem_cons.2 ⟨subd19_3_178, List.forall_mem_cons.2 ⟨subd19_3_179, List.forall_mem_cons.2 ⟨subd19_3_180, List.forall_mem_cons.2 ⟨subd19_3_181, List.forall_mem_cons.2 ⟨subd19_3_182, List.forall_mem_cons.2 ⟨subd19_3_183, List.forall_mem_cons.2 ⟨subd19_3_184, List.forall_mem_cons.2 ⟨subd19_3_185, List.forall_mem_cons.2 ⟨subd19_3_186, List.forall_mem_cons.2 ⟨subd19_3_187, List.forall_mem_cons.2 ⟨subd19_3_188, List.forall_mem_cons.2 ⟨subd19_3_189, List.forall_mem_cons.2 ⟨subd19_3_190, List.forall_mem_cons.2 ⟨subd19_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_192 : subd19_3 [-4, 1, 2] = true := by decide +kernel
theorem subd19_3_193 : subd19_3 [-4, 1, 3] = true := by decide +kernel
theorem subd19_3_194 : subd19_3 [-4, 1, 4] = true := by decide +kernel
theorem subd19_3_195 : subd19_3 [-4, 1, 5] = true := by decide +kernel
theorem subd19_3_196 : subd19_3 [-4, 1, 6] = true := by decide +kernel
theorem subd19_3_197 : subd19_3 [-4, 1, 7] = true := by decide +kernel
theorem subd19_3_198 : subd19_3 [-4, 1, 8] = true := by decide +kernel
theorem subd19_3_199 : subd19_3 [-4, 2, -8] = true := by decide +kernel
theorem subd19_3_200 : subd19_3 [-4, 2, -7] = true := by decide +kernel
theorem subd19_3_201 : subd19_3 [-4, 2, -6] = true := by decide +kernel
theorem subd19_3_202 : subd19_3 [-4, 2, -5] = true := by decide +kernel
theorem subd19_3_203 : subd19_3 [-4, 2, -4] = true := by decide +kernel
theorem subd19_3_204 : subd19_3 [-4, 2, -3] = true := by decide +kernel
theorem subd19_3_205 : subd19_3 [-4, 2, -2] = true := by decide +kernel
theorem subd19_3_206 : subd19_3 [-4, 2, -1] = true := by decide +kernel
theorem subd19_3_207 : subd19_3 [-4, 2, 0] = true := by decide +kernel
theorem subd19_3_208 : subd19_3 [-4, 2, 1] = true := by decide +kernel
theorem subd19_3_209 : subd19_3 [-4, 2, 2] = true := by decide +kernel
theorem subd19_3_210 : subd19_3 [-4, 2, 3] = true := by decide +kernel
theorem subd19_3_211 : subd19_3 [-4, 2, 4] = true := by decide +kernel
theorem subd19_3_212 : subd19_3 [-4, 2, 5] = true := by decide +kernel
theorem subd19_3_213 : subd19_3 [-4, 2, 6] = true := by decide +kernel
theorem subd19_3_214 : subd19_3 [-4, 2, 7] = true := by decide +kernel
theorem subd19_3_215 : subd19_3 [-4, 2, 8] = true := by decide +kernel
theorem subd19_3_216 : subd19_3 [-4, 3, -8] = true := by decide +kernel
theorem subd19_3_217 : subd19_3 [-4, 3, -7] = true := by decide +kernel
theorem subd19_3_218 : subd19_3 [-4, 3, -6] = true := by decide +kernel
theorem subd19_3_219 : subd19_3 [-4, 3, -5] = true := by decide +kernel
theorem subd19_3_220 : subd19_3 [-4, 3, -4] = true := by decide +kernel
theorem subd19_3_221 : subd19_3 [-4, 3, -3] = true := by decide +kernel
theorem subd19_3_222 : subd19_3 [-4, 3, -2] = true := by decide +kernel
theorem subd19_3_223 : subd19_3 [-4, 3, -1] = true := by decide +kernel
theorem sbd19_3_6 : ∀ q ∈ blkd19_3_6, subd19_3 q = true := by
  unfold blkd19_3_6
  exact List.forall_mem_cons.2 ⟨subd19_3_192, List.forall_mem_cons.2 ⟨subd19_3_193, List.forall_mem_cons.2 ⟨subd19_3_194, List.forall_mem_cons.2 ⟨subd19_3_195, List.forall_mem_cons.2 ⟨subd19_3_196, List.forall_mem_cons.2 ⟨subd19_3_197, List.forall_mem_cons.2 ⟨subd19_3_198, List.forall_mem_cons.2 ⟨subd19_3_199, List.forall_mem_cons.2 ⟨subd19_3_200, List.forall_mem_cons.2 ⟨subd19_3_201, List.forall_mem_cons.2 ⟨subd19_3_202, List.forall_mem_cons.2 ⟨subd19_3_203, List.forall_mem_cons.2 ⟨subd19_3_204, List.forall_mem_cons.2 ⟨subd19_3_205, List.forall_mem_cons.2 ⟨subd19_3_206, List.forall_mem_cons.2 ⟨subd19_3_207, List.forall_mem_cons.2 ⟨subd19_3_208, List.forall_mem_cons.2 ⟨subd19_3_209, List.forall_mem_cons.2 ⟨subd19_3_210, List.forall_mem_cons.2 ⟨subd19_3_211, List.forall_mem_cons.2 ⟨subd19_3_212, List.forall_mem_cons.2 ⟨subd19_3_213, List.forall_mem_cons.2 ⟨subd19_3_214, List.forall_mem_cons.2 ⟨subd19_3_215, List.forall_mem_cons.2 ⟨subd19_3_216, List.forall_mem_cons.2 ⟨subd19_3_217, List.forall_mem_cons.2 ⟨subd19_3_218, List.forall_mem_cons.2 ⟨subd19_3_219, List.forall_mem_cons.2 ⟨subd19_3_220, List.forall_mem_cons.2 ⟨subd19_3_221, List.forall_mem_cons.2 ⟨subd19_3_222, List.forall_mem_cons.2 ⟨subd19_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_224 : subd19_3 [-4, 3, 0] = true := by decide +kernel
theorem subd19_3_225 : subd19_3 [-4, 3, 1] = true := by decide +kernel
theorem subd19_3_226 : subd19_3 [-4, 3, 2] = true := by decide +kernel
theorem subd19_3_227 : subd19_3 [-4, 3, 3] = true := by decide +kernel
theorem subd19_3_228 : subd19_3 [-4, 3, 4] = true := by decide +kernel
theorem subd19_3_229 : subd19_3 [-4, 3, 5] = true := by decide +kernel
theorem subd19_3_230 : subd19_3 [-4, 3, 6] = true := by decide +kernel
theorem subd19_3_231 : subd19_3 [-4, 3, 7] = true := by decide +kernel
theorem subd19_3_232 : subd19_3 [-4, 4, -8] = true := by decide +kernel
theorem subd19_3_233 : subd19_3 [-4, 4, -7] = true := by decide +kernel
theorem subd19_3_234 : subd19_3 [-4, 4, -6] = true := by decide +kernel
theorem subd19_3_235 : subd19_3 [-4, 4, -5] = true := by decide +kernel
theorem subd19_3_236 : subd19_3 [-4, 4, -4] = true := by decide +kernel
theorem subd19_3_237 : subd19_3 [-4, 4, -3] = true := by decide +kernel
theorem subd19_3_238 : subd19_3 [-4, 4, -2] = true := by decide +kernel
theorem subd19_3_239 : subd19_3 [-4, 4, -1] = true := by decide +kernel
theorem subd19_3_240 : subd19_3 [-4, 4, 0] = true := by decide +kernel
theorem subd19_3_241 : subd19_3 [-4, 4, 1] = true := by decide +kernel
theorem subd19_3_242 : subd19_3 [-4, 4, 2] = true := by decide +kernel
theorem subd19_3_243 : subd19_3 [-4, 4, 3] = true := by decide +kernel
theorem subd19_3_244 : subd19_3 [-4, 4, 4] = true := by decide +kernel
theorem subd19_3_245 : subd19_3 [-4, 4, 5] = true := by decide +kernel
theorem subd19_3_246 : subd19_3 [-4, 4, 6] = true := by decide +kernel
theorem subd19_3_247 : subd19_3 [-4, 5] = true := by decide +kernel
theorem subd19_3_248 : subd19_3 [-4, 6] = true := by decide +kernel
theorem subd19_3_249 : subd19_3 [-4, 7] = true := by decide +kernel
theorem subd19_3_250 : subd19_3 [-3, -8] = true := by decide +kernel
theorem subd19_3_251 : subd19_3 [-3, -7] = true := by decide +kernel
theorem subd19_3_252 : subd19_3 [-3, -6] = true := by decide +kernel
theorem subd19_3_253 : subd19_3 [-3, -5] = true := by decide +kernel
theorem subd19_3_254 : subd19_3 [-3, -4, -4] = true := by decide +kernel
theorem subd19_3_255 : subd19_3 [-3, -4, -3] = true := by decide +kernel
theorem sbd19_3_7 : ∀ q ∈ blkd19_3_7, subd19_3 q = true := by
  unfold blkd19_3_7
  exact List.forall_mem_cons.2 ⟨subd19_3_224, List.forall_mem_cons.2 ⟨subd19_3_225, List.forall_mem_cons.2 ⟨subd19_3_226, List.forall_mem_cons.2 ⟨subd19_3_227, List.forall_mem_cons.2 ⟨subd19_3_228, List.forall_mem_cons.2 ⟨subd19_3_229, List.forall_mem_cons.2 ⟨subd19_3_230, List.forall_mem_cons.2 ⟨subd19_3_231, List.forall_mem_cons.2 ⟨subd19_3_232, List.forall_mem_cons.2 ⟨subd19_3_233, List.forall_mem_cons.2 ⟨subd19_3_234, List.forall_mem_cons.2 ⟨subd19_3_235, List.forall_mem_cons.2 ⟨subd19_3_236, List.forall_mem_cons.2 ⟨subd19_3_237, List.forall_mem_cons.2 ⟨subd19_3_238, List.forall_mem_cons.2 ⟨subd19_3_239, List.forall_mem_cons.2 ⟨subd19_3_240, List.forall_mem_cons.2 ⟨subd19_3_241, List.forall_mem_cons.2 ⟨subd19_3_242, List.forall_mem_cons.2 ⟨subd19_3_243, List.forall_mem_cons.2 ⟨subd19_3_244, List.forall_mem_cons.2 ⟨subd19_3_245, List.forall_mem_cons.2 ⟨subd19_3_246, List.forall_mem_cons.2 ⟨subd19_3_247, List.forall_mem_cons.2 ⟨subd19_3_248, List.forall_mem_cons.2 ⟨subd19_3_249, List.forall_mem_cons.2 ⟨subd19_3_250, List.forall_mem_cons.2 ⟨subd19_3_251, List.forall_mem_cons.2 ⟨subd19_3_252, List.forall_mem_cons.2 ⟨subd19_3_253, List.forall_mem_cons.2 ⟨subd19_3_254, List.forall_mem_cons.2 ⟨subd19_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_256 : subd19_3 [-3, -4, -2] = true := by decide +kernel
theorem subd19_3_257 : subd19_3 [-3, -4, -1] = true := by decide +kernel
theorem subd19_3_258 : subd19_3 [-3, -4, 0] = true := by decide +kernel
theorem subd19_3_259 : subd19_3 [-3, -4, 1] = true := by decide +kernel
theorem subd19_3_260 : subd19_3 [-3, -4, 2] = true := by decide +kernel
theorem subd19_3_261 : subd19_3 [-3, -4, 3] = true := by decide +kernel
theorem subd19_3_262 : subd19_3 [-3, -4, 4] = true := by decide +kernel
theorem subd19_3_263 : subd19_3 [-3, -4, 5] = true := by decide +kernel
theorem subd19_3_264 : subd19_3 [-3, -4, 6] = true := by decide +kernel
theorem subd19_3_265 : subd19_3 [-3, -4, 7] = true := by decide +kernel
theorem subd19_3_266 : subd19_3 [-3, -4, 8] = true := by decide +kernel
theorem subd19_3_267 : subd19_3 [-3, -4, 9] = true := by decide +kernel
theorem subd19_3_268 : subd19_3 [-3, -3, -6] = true := by decide +kernel
theorem subd19_3_269 : subd19_3 [-3, -3, -5] = true := by decide +kernel
theorem subd19_3_270 : subd19_3 [-3, -3, -4] = true := by decide +kernel
theorem subd19_3_271 : subd19_3 [-3, -3, -3] = true := by decide +kernel
theorem subd19_3_272 : subd19_3 [-3, -3, -2] = true := by decide +kernel
theorem subd19_3_273 : subd19_3 [-3, -3, -1] = true := by decide +kernel
theorem subd19_3_274 : subd19_3 [-3, -3, 0] = true := by decide +kernel
theorem subd19_3_275 : subd19_3 [-3, -3, 1] = true := by decide +kernel
theorem subd19_3_276 : subd19_3 [-3, -3, 2] = true := by decide +kernel
theorem subd19_3_277 : subd19_3 [-3, -3, 3] = true := by decide +kernel
theorem subd19_3_278 : subd19_3 [-3, -3, 4] = true := by decide +kernel
theorem subd19_3_279 : subd19_3 [-3, -3, 5] = true := by decide +kernel
theorem subd19_3_280 : subd19_3 [-3, -3, 6] = true := by decide +kernel
theorem subd19_3_281 : subd19_3 [-3, -3, 7] = true := by decide +kernel
theorem subd19_3_282 : subd19_3 [-3, -3, 8] = true := by decide +kernel
theorem subd19_3_283 : subd19_3 [-3, -3, 9] = true := by decide +kernel
theorem subd19_3_284 : subd19_3 [-3, -2, -6] = true := by decide +kernel
theorem subd19_3_285 : subd19_3 [-3, -2, -5] = true := by decide +kernel
theorem subd19_3_286 : subd19_3 [-3, -2, -4] = true := by decide +kernel
theorem subd19_3_287 : subd19_3 [-3, -2, -3] = true := by decide +kernel
theorem sbd19_3_8 : ∀ q ∈ blkd19_3_8, subd19_3 q = true := by
  unfold blkd19_3_8
  exact List.forall_mem_cons.2 ⟨subd19_3_256, List.forall_mem_cons.2 ⟨subd19_3_257, List.forall_mem_cons.2 ⟨subd19_3_258, List.forall_mem_cons.2 ⟨subd19_3_259, List.forall_mem_cons.2 ⟨subd19_3_260, List.forall_mem_cons.2 ⟨subd19_3_261, List.forall_mem_cons.2 ⟨subd19_3_262, List.forall_mem_cons.2 ⟨subd19_3_263, List.forall_mem_cons.2 ⟨subd19_3_264, List.forall_mem_cons.2 ⟨subd19_3_265, List.forall_mem_cons.2 ⟨subd19_3_266, List.forall_mem_cons.2 ⟨subd19_3_267, List.forall_mem_cons.2 ⟨subd19_3_268, List.forall_mem_cons.2 ⟨subd19_3_269, List.forall_mem_cons.2 ⟨subd19_3_270, List.forall_mem_cons.2 ⟨subd19_3_271, List.forall_mem_cons.2 ⟨subd19_3_272, List.forall_mem_cons.2 ⟨subd19_3_273, List.forall_mem_cons.2 ⟨subd19_3_274, List.forall_mem_cons.2 ⟨subd19_3_275, List.forall_mem_cons.2 ⟨subd19_3_276, List.forall_mem_cons.2 ⟨subd19_3_277, List.forall_mem_cons.2 ⟨subd19_3_278, List.forall_mem_cons.2 ⟨subd19_3_279, List.forall_mem_cons.2 ⟨subd19_3_280, List.forall_mem_cons.2 ⟨subd19_3_281, List.forall_mem_cons.2 ⟨subd19_3_282, List.forall_mem_cons.2 ⟨subd19_3_283, List.forall_mem_cons.2 ⟨subd19_3_284, List.forall_mem_cons.2 ⟨subd19_3_285, List.forall_mem_cons.2 ⟨subd19_3_286, List.forall_mem_cons.2 ⟨subd19_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_288 : subd19_3 [-3, -2, -2] = true := by decide +kernel
theorem subd19_3_289 : subd19_3 [-3, -2, -1] = true := by decide +kernel
theorem subd19_3_290 : subd19_3 [-3, -2, 0] = true := by decide +kernel
theorem subd19_3_291 : subd19_3 [-3, -2, 1] = true := by decide +kernel
theorem subd19_3_292 : subd19_3 [-3, -2, 2] = true := by decide +kernel
theorem subd19_3_293 : subd19_3 [-3, -2, 3] = true := by decide +kernel
theorem subd19_3_294 : subd19_3 [-3, -2, 4] = true := by decide +kernel
theorem subd19_3_295 : subd19_3 [-3, -2, 5] = true := by decide +kernel
theorem subd19_3_296 : subd19_3 [-3, -2, 6] = true := by decide +kernel
theorem subd19_3_297 : subd19_3 [-3, -2, 7] = true := by decide +kernel
theorem subd19_3_298 : subd19_3 [-3, -2, 8] = true := by decide +kernel
theorem subd19_3_299 : subd19_3 [-3, -2, 9] = true := by decide +kernel
theorem subd19_3_300 : subd19_3 [-3, -1, -7] = true := by decide +kernel
theorem subd19_3_301 : subd19_3 [-3, -1, -6] = true := by decide +kernel
theorem subd19_3_302 : subd19_3 [-3, -1, -5] = true := by decide +kernel
theorem subd19_3_303 : subd19_3 [-3, -1, -4] = true := by decide +kernel
theorem subd19_3_304 : subd19_3 [-3, -1, -3] = true := by decide +kernel
theorem subd19_3_305 : subd19_3 [-3, -1, -2] = true := by decide +kernel
theorem subd19_3_306 : subd19_3 [-3, -1, -1] = true := by decide +kernel
theorem subd19_3_307 : subd19_3 [-3, -1, 0] = true := by decide +kernel
theorem subd19_3_308 : subd19_3 [-3, -1, 1] = true := by decide +kernel
theorem subd19_3_309 : subd19_3 [-3, -1, 2] = true := by decide +kernel
theorem subd19_3_310 : subd19_3 [-3, -1, 3] = true := by decide +kernel
theorem subd19_3_311 : subd19_3 [-3, -1, 4] = true := by decide +kernel
theorem subd19_3_312 : subd19_3 [-3, -1, 5] = true := by decide +kernel
theorem subd19_3_313 : subd19_3 [-3, -1, 6] = true := by decide +kernel
theorem subd19_3_314 : subd19_3 [-3, -1, 7] = true := by decide +kernel
theorem subd19_3_315 : subd19_3 [-3, -1, 8] = true := by decide +kernel
theorem subd19_3_316 : subd19_3 [-3, -1, 9] = true := by decide +kernel
theorem subd19_3_317 : subd19_3 [-3, 0, -8] = true := by decide +kernel
theorem subd19_3_318 : subd19_3 [-3, 0, -7] = true := by decide +kernel
theorem subd19_3_319 : subd19_3 [-3, 0, -6] = true := by decide +kernel
theorem sbd19_3_9 : ∀ q ∈ blkd19_3_9, subd19_3 q = true := by
  unfold blkd19_3_9
  exact List.forall_mem_cons.2 ⟨subd19_3_288, List.forall_mem_cons.2 ⟨subd19_3_289, List.forall_mem_cons.2 ⟨subd19_3_290, List.forall_mem_cons.2 ⟨subd19_3_291, List.forall_mem_cons.2 ⟨subd19_3_292, List.forall_mem_cons.2 ⟨subd19_3_293, List.forall_mem_cons.2 ⟨subd19_3_294, List.forall_mem_cons.2 ⟨subd19_3_295, List.forall_mem_cons.2 ⟨subd19_3_296, List.forall_mem_cons.2 ⟨subd19_3_297, List.forall_mem_cons.2 ⟨subd19_3_298, List.forall_mem_cons.2 ⟨subd19_3_299, List.forall_mem_cons.2 ⟨subd19_3_300, List.forall_mem_cons.2 ⟨subd19_3_301, List.forall_mem_cons.2 ⟨subd19_3_302, List.forall_mem_cons.2 ⟨subd19_3_303, List.forall_mem_cons.2 ⟨subd19_3_304, List.forall_mem_cons.2 ⟨subd19_3_305, List.forall_mem_cons.2 ⟨subd19_3_306, List.forall_mem_cons.2 ⟨subd19_3_307, List.forall_mem_cons.2 ⟨subd19_3_308, List.forall_mem_cons.2 ⟨subd19_3_309, List.forall_mem_cons.2 ⟨subd19_3_310, List.forall_mem_cons.2 ⟨subd19_3_311, List.forall_mem_cons.2 ⟨subd19_3_312, List.forall_mem_cons.2 ⟨subd19_3_313, List.forall_mem_cons.2 ⟨subd19_3_314, List.forall_mem_cons.2 ⟨subd19_3_315, List.forall_mem_cons.2 ⟨subd19_3_316, List.forall_mem_cons.2 ⟨subd19_3_317, List.forall_mem_cons.2 ⟨subd19_3_318, List.forall_mem_cons.2 ⟨subd19_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_320 : subd19_3 [-3, 0, -5] = true := by decide +kernel
theorem subd19_3_321 : subd19_3 [-3, 0, -4] = true := by decide +kernel
theorem subd19_3_322 : subd19_3 [-3, 0, -3] = true := by decide +kernel
theorem subd19_3_323 : subd19_3 [-3, 0, -2] = true := by decide +kernel
theorem subd19_3_324 : subd19_3 [-3, 0, -1] = true := by decide +kernel
theorem subd19_3_325 : subd19_3 [-3, 0, 0] = true := by decide +kernel
theorem subd19_3_326 : subd19_3 [-3, 0, 1] = true := by decide +kernel
theorem subd19_3_327 : subd19_3 [-3, 0, 2] = true := by decide +kernel
theorem subd19_3_328 : subd19_3 [-3, 0, 3] = true := by decide +kernel
theorem subd19_3_329 : subd19_3 [-3, 0, 4] = true := by decide +kernel
theorem subd19_3_330 : subd19_3 [-3, 0, 5] = true := by decide +kernel
theorem subd19_3_331 : subd19_3 [-3, 0, 6] = true := by decide +kernel
theorem subd19_3_332 : subd19_3 [-3, 0, 7] = true := by decide +kernel
theorem subd19_3_333 : subd19_3 [-3, 0, 8] = true := by decide +kernel
theorem subd19_3_334 : subd19_3 [-3, 0, 9] = true := by decide +kernel
theorem subd19_3_335 : subd19_3 [-3, 1, -8] = true := by decide +kernel
theorem subd19_3_336 : subd19_3 [-3, 1, -7] = true := by decide +kernel
theorem subd19_3_337 : subd19_3 [-3, 1, -6] = true := by decide +kernel
theorem subd19_3_338 : subd19_3 [-3, 1, -5] = true := by decide +kernel
theorem subd19_3_339 : subd19_3 [-3, 1, -4] = true := by decide +kernel
theorem subd19_3_340 : subd19_3 [-3, 1, -3] = true := by decide +kernel
theorem subd19_3_341 : subd19_3 [-3, 1, -2] = true := by decide +kernel
theorem subd19_3_342 : subd19_3 [-3, 1, -1] = true := by decide +kernel
theorem subd19_3_343 : subd19_3 [-3, 1, 0] = true := by decide +kernel
theorem subd19_3_344 : subd19_3 [-3, 1, 1] = true := by decide +kernel
theorem subd19_3_345 : subd19_3 [-3, 1, 2] = true := by decide +kernel
theorem subd19_3_346 : subd19_3 [-3, 1, 3] = true := by decide +kernel
theorem subd19_3_347 : subd19_3 [-3, 1, 4] = true := by decide +kernel
theorem subd19_3_348 : subd19_3 [-3, 1, 5] = true := by decide +kernel
theorem subd19_3_349 : subd19_3 [-3, 1, 6] = true := by decide +kernel
theorem subd19_3_350 : subd19_3 [-3, 1, 7] = true := by decide +kernel
theorem subd19_3_351 : subd19_3 [-3, 1, 8] = true := by decide +kernel
theorem sbd19_3_10 : ∀ q ∈ blkd19_3_10, subd19_3 q = true := by
  unfold blkd19_3_10
  exact List.forall_mem_cons.2 ⟨subd19_3_320, List.forall_mem_cons.2 ⟨subd19_3_321, List.forall_mem_cons.2 ⟨subd19_3_322, List.forall_mem_cons.2 ⟨subd19_3_323, List.forall_mem_cons.2 ⟨subd19_3_324, List.forall_mem_cons.2 ⟨subd19_3_325, List.forall_mem_cons.2 ⟨subd19_3_326, List.forall_mem_cons.2 ⟨subd19_3_327, List.forall_mem_cons.2 ⟨subd19_3_328, List.forall_mem_cons.2 ⟨subd19_3_329, List.forall_mem_cons.2 ⟨subd19_3_330, List.forall_mem_cons.2 ⟨subd19_3_331, List.forall_mem_cons.2 ⟨subd19_3_332, List.forall_mem_cons.2 ⟨subd19_3_333, List.forall_mem_cons.2 ⟨subd19_3_334, List.forall_mem_cons.2 ⟨subd19_3_335, List.forall_mem_cons.2 ⟨subd19_3_336, List.forall_mem_cons.2 ⟨subd19_3_337, List.forall_mem_cons.2 ⟨subd19_3_338, List.forall_mem_cons.2 ⟨subd19_3_339, List.forall_mem_cons.2 ⟨subd19_3_340, List.forall_mem_cons.2 ⟨subd19_3_341, List.forall_mem_cons.2 ⟨subd19_3_342, List.forall_mem_cons.2 ⟨subd19_3_343, List.forall_mem_cons.2 ⟨subd19_3_344, List.forall_mem_cons.2 ⟨subd19_3_345, List.forall_mem_cons.2 ⟨subd19_3_346, List.forall_mem_cons.2 ⟨subd19_3_347, List.forall_mem_cons.2 ⟨subd19_3_348, List.forall_mem_cons.2 ⟨subd19_3_349, List.forall_mem_cons.2 ⟨subd19_3_350, List.forall_mem_cons.2 ⟨subd19_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_352 : subd19_3 [-3, 2, -8] = true := by decide +kernel
theorem subd19_3_353 : subd19_3 [-3, 2, -7] = true := by decide +kernel
theorem subd19_3_354 : subd19_3 [-3, 2, -6] = true := by decide +kernel
theorem subd19_3_355 : subd19_3 [-3, 2, -5] = true := by decide +kernel
theorem subd19_3_356 : subd19_3 [-3, 2, -4] = true := by decide +kernel
theorem subd19_3_357 : subd19_3 [-3, 2, -3] = true := by decide +kernel
theorem subd19_3_358 : subd19_3 [-3, 2, -2] = true := by decide +kernel
theorem subd19_3_359 : subd19_3 [-3, 2, -1] = true := by decide +kernel
theorem subd19_3_360 : subd19_3 [-3, 2, 0] = true := by decide +kernel
theorem subd19_3_361 : subd19_3 [-3, 2, 1] = true := by decide +kernel
theorem subd19_3_362 : subd19_3 [-3, 2, 2] = true := by decide +kernel
theorem subd19_3_363 : subd19_3 [-3, 2, 3] = true := by decide +kernel
theorem subd19_3_364 : subd19_3 [-3, 2, 4] = true := by decide +kernel
theorem subd19_3_365 : subd19_3 [-3, 2, 5] = true := by decide +kernel
theorem subd19_3_366 : subd19_3 [-3, 2, 6] = true := by decide +kernel
theorem subd19_3_367 : subd19_3 [-3, 2, 7] = true := by decide +kernel
theorem subd19_3_368 : subd19_3 [-3, 2, 8] = true := by decide +kernel
theorem subd19_3_369 : subd19_3 [-3, 3, -8] = true := by decide +kernel
theorem subd19_3_370 : subd19_3 [-3, 3, -7] = true := by decide +kernel
theorem subd19_3_371 : subd19_3 [-3, 3, -6] = true := by decide +kernel
theorem subd19_3_372 : subd19_3 [-3, 3, -5] = true := by decide +kernel
theorem subd19_3_373 : subd19_3 [-3, 3, -4] = true := by decide +kernel
theorem subd19_3_374 : subd19_3 [-3, 3, -3] = true := by decide +kernel
theorem subd19_3_375 : subd19_3 [-3, 3, -2] = true := by decide +kernel
theorem subd19_3_376 : subd19_3 [-3, 3, -1] = true := by decide +kernel
theorem subd19_3_377 : subd19_3 [-3, 3, 0] = true := by decide +kernel
theorem subd19_3_378 : subd19_3 [-3, 3, 1] = true := by decide +kernel
theorem subd19_3_379 : subd19_3 [-3, 3, 2] = true := by decide +kernel
theorem subd19_3_380 : subd19_3 [-3, 3, 3] = true := by decide +kernel
theorem subd19_3_381 : subd19_3 [-3, 3, 4] = true := by decide +kernel
theorem subd19_3_382 : subd19_3 [-3, 3, 5] = true := by decide +kernel
theorem subd19_3_383 : subd19_3 [-3, 3, 6] = true := by decide +kernel
theorem sbd19_3_11 : ∀ q ∈ blkd19_3_11, subd19_3 q = true := by
  unfold blkd19_3_11
  exact List.forall_mem_cons.2 ⟨subd19_3_352, List.forall_mem_cons.2 ⟨subd19_3_353, List.forall_mem_cons.2 ⟨subd19_3_354, List.forall_mem_cons.2 ⟨subd19_3_355, List.forall_mem_cons.2 ⟨subd19_3_356, List.forall_mem_cons.2 ⟨subd19_3_357, List.forall_mem_cons.2 ⟨subd19_3_358, List.forall_mem_cons.2 ⟨subd19_3_359, List.forall_mem_cons.2 ⟨subd19_3_360, List.forall_mem_cons.2 ⟨subd19_3_361, List.forall_mem_cons.2 ⟨subd19_3_362, List.forall_mem_cons.2 ⟨subd19_3_363, List.forall_mem_cons.2 ⟨subd19_3_364, List.forall_mem_cons.2 ⟨subd19_3_365, List.forall_mem_cons.2 ⟨subd19_3_366, List.forall_mem_cons.2 ⟨subd19_3_367, List.forall_mem_cons.2 ⟨subd19_3_368, List.forall_mem_cons.2 ⟨subd19_3_369, List.forall_mem_cons.2 ⟨subd19_3_370, List.forall_mem_cons.2 ⟨subd19_3_371, List.forall_mem_cons.2 ⟨subd19_3_372, List.forall_mem_cons.2 ⟨subd19_3_373, List.forall_mem_cons.2 ⟨subd19_3_374, List.forall_mem_cons.2 ⟨subd19_3_375, List.forall_mem_cons.2 ⟨subd19_3_376, List.forall_mem_cons.2 ⟨subd19_3_377, List.forall_mem_cons.2 ⟨subd19_3_378, List.forall_mem_cons.2 ⟨subd19_3_379, List.forall_mem_cons.2 ⟨subd19_3_380, List.forall_mem_cons.2 ⟨subd19_3_381, List.forall_mem_cons.2 ⟨subd19_3_382, List.forall_mem_cons.2 ⟨subd19_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
