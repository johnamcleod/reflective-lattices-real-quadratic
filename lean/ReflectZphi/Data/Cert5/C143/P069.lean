import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_2_0 : subd19_2 [-7, -1] = true := by decide +kernel
theorem subd19_2_1 : subd19_2 [-7, 0] = true := by decide +kernel
theorem subd19_2_2 : subd19_2 [-7, 1] = true := by decide +kernel
theorem subd19_2_3 : subd19_2 [-7, 2] = true := by decide +kernel
theorem subd19_2_4 : subd19_2 [-7, 3] = true := by decide +kernel
theorem subd19_2_5 : subd19_2 [-7, 4] = true := by decide +kernel
theorem subd19_2_6 : subd19_2 [-7, 5] = true := by decide +kernel
theorem subd19_2_7 : subd19_2 [-6, -3] = true := by decide +kernel
theorem subd19_2_8 : subd19_2 [-6, -2] = true := by decide +kernel
theorem subd19_2_9 : subd19_2 [-6, -1] = true := by decide +kernel
theorem subd19_2_10 : subd19_2 [-6, 0] = true := by decide +kernel
theorem subd19_2_11 : subd19_2 [-6, 1] = true := by decide +kernel
theorem subd19_2_12 : subd19_2 [-6, 2] = true := by decide +kernel
theorem subd19_2_13 : subd19_2 [-6, 3] = true := by decide +kernel
theorem subd19_2_14 : subd19_2 [-6, 4] = true := by decide +kernel
theorem subd19_2_15 : subd19_2 [-6, 5] = true := by decide +kernel
theorem subd19_2_16 : subd19_2 [-6, 6] = true := by decide +kernel
theorem subd19_2_17 : subd19_2 [-5, -4] = true := by decide +kernel
theorem subd19_2_18 : subd19_2 [-5, -3] = true := by decide +kernel
theorem subd19_2_19 : subd19_2 [-5, -2] = true := by decide +kernel
theorem subd19_2_20 : subd19_2 [-5, -1] = true := by decide +kernel
theorem subd19_2_21 : subd19_2 [-5, 0] = true := by decide +kernel
theorem subd19_2_22 : subd19_2 [-5, 1] = true := by decide +kernel
theorem subd19_2_23 : subd19_2 [-5, 2] = true := by decide +kernel
theorem subd19_2_24 : subd19_2 [-5, 3] = true := by decide +kernel
theorem subd19_2_25 : subd19_2 [-5, 4] = true := by decide +kernel
theorem subd19_2_26 : subd19_2 [-5, 5] = true := by decide +kernel
theorem subd19_2_27 : subd19_2 [-5, 6] = true := by decide +kernel
theorem subd19_2_28 : subd19_2 [-5, 7] = true := by decide +kernel
theorem subd19_2_29 : subd19_2 [-4, -5] = true := by decide +kernel
theorem subd19_2_30 : subd19_2 [-4, -4] = true := by decide +kernel
theorem subd19_2_31 : subd19_2 [-4, -3] = true := by decide +kernel
theorem sbd19_2_0 : ∀ q ∈ blkd19_2_0, subd19_2 q = true := by
  unfold blkd19_2_0
  exact List.forall_mem_cons.2 ⟨subd19_2_0, List.forall_mem_cons.2 ⟨subd19_2_1, List.forall_mem_cons.2 ⟨subd19_2_2, List.forall_mem_cons.2 ⟨subd19_2_3, List.forall_mem_cons.2 ⟨subd19_2_4, List.forall_mem_cons.2 ⟨subd19_2_5, List.forall_mem_cons.2 ⟨subd19_2_6, List.forall_mem_cons.2 ⟨subd19_2_7, List.forall_mem_cons.2 ⟨subd19_2_8, List.forall_mem_cons.2 ⟨subd19_2_9, List.forall_mem_cons.2 ⟨subd19_2_10, List.forall_mem_cons.2 ⟨subd19_2_11, List.forall_mem_cons.2 ⟨subd19_2_12, List.forall_mem_cons.2 ⟨subd19_2_13, List.forall_mem_cons.2 ⟨subd19_2_14, List.forall_mem_cons.2 ⟨subd19_2_15, List.forall_mem_cons.2 ⟨subd19_2_16, List.forall_mem_cons.2 ⟨subd19_2_17, List.forall_mem_cons.2 ⟨subd19_2_18, List.forall_mem_cons.2 ⟨subd19_2_19, List.forall_mem_cons.2 ⟨subd19_2_20, List.forall_mem_cons.2 ⟨subd19_2_21, List.forall_mem_cons.2 ⟨subd19_2_22, List.forall_mem_cons.2 ⟨subd19_2_23, List.forall_mem_cons.2 ⟨subd19_2_24, List.forall_mem_cons.2 ⟨subd19_2_25, List.forall_mem_cons.2 ⟨subd19_2_26, List.forall_mem_cons.2 ⟨subd19_2_27, List.forall_mem_cons.2 ⟨subd19_2_28, List.forall_mem_cons.2 ⟨subd19_2_29, List.forall_mem_cons.2 ⟨subd19_2_30, List.forall_mem_cons.2 ⟨subd19_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_32 : subd19_2 [-4, -2] = true := by decide +kernel
theorem subd19_2_33 : subd19_2 [-4, -1] = true := by decide +kernel
theorem subd19_2_34 : subd19_2 [-4, 0, -8] = true := by decide +kernel
theorem subd19_2_35 : subd19_2 [-4, 0, -7] = true := by decide +kernel
theorem subd19_2_36 : subd19_2 [-4, 0, -6] = true := by decide +kernel
theorem subd19_2_37 : subd19_2 [-4, 0, -5] = true := by decide +kernel
theorem subd19_2_38 : subd19_2 [-4, 0, -4] = true := by decide +kernel
theorem subd19_2_39 : subd19_2 [-4, 0, -3] = true := by decide +kernel
theorem subd19_2_40 : subd19_2 [-4, 0, -2] = true := by decide +kernel
theorem subd19_2_41 : subd19_2 [-4, 0, -1] = true := by decide +kernel
theorem subd19_2_42 : subd19_2 [-4, 0, 0] = true := by decide +kernel
theorem subd19_2_43 : subd19_2 [-4, 0, 1] = true := by decide +kernel
theorem subd19_2_44 : subd19_2 [-4, 0, 2] = true := by decide +kernel
theorem subd19_2_45 : subd19_2 [-4, 0, 3] = true := by decide +kernel
theorem subd19_2_46 : subd19_2 [-4, 0, 4] = true := by decide +kernel
theorem subd19_2_47 : subd19_2 [-4, 0, 5] = true := by decide +kernel
theorem subd19_2_48 : subd19_2 [-4, 0, 6] = true := by decide +kernel
theorem subd19_2_49 : subd19_2 [-4, 1, -8] = true := by decide +kernel
theorem subd19_2_50 : subd19_2 [-4, 1, -7] = true := by decide +kernel
theorem subd19_2_51 : subd19_2 [-4, 1, -6] = true := by decide +kernel
theorem subd19_2_52 : subd19_2 [-4, 1, -5] = true := by decide +kernel
theorem subd19_2_53 : subd19_2 [-4, 1, -4] = true := by decide +kernel
theorem subd19_2_54 : subd19_2 [-4, 1, -3] = true := by decide +kernel
theorem subd19_2_55 : subd19_2 [-4, 1, -2] = true := by decide +kernel
theorem subd19_2_56 : subd19_2 [-4, 1, -1] = true := by decide +kernel
theorem subd19_2_57 : subd19_2 [-4, 1, 0] = true := by decide +kernel
theorem subd19_2_58 : subd19_2 [-4, 1, 1] = true := by decide +kernel
theorem subd19_2_59 : subd19_2 [-4, 1, 2] = true := by decide +kernel
theorem subd19_2_60 : subd19_2 [-4, 1, 3] = true := by decide +kernel
theorem subd19_2_61 : subd19_2 [-4, 1, 4] = true := by decide +kernel
theorem subd19_2_62 : subd19_2 [-4, 1, 5] = true := by decide +kernel
theorem subd19_2_63 : subd19_2 [-4, 1, 6] = true := by decide +kernel
theorem sbd19_2_1 : ∀ q ∈ blkd19_2_1, subd19_2 q = true := by
  unfold blkd19_2_1
  exact List.forall_mem_cons.2 ⟨subd19_2_32, List.forall_mem_cons.2 ⟨subd19_2_33, List.forall_mem_cons.2 ⟨subd19_2_34, List.forall_mem_cons.2 ⟨subd19_2_35, List.forall_mem_cons.2 ⟨subd19_2_36, List.forall_mem_cons.2 ⟨subd19_2_37, List.forall_mem_cons.2 ⟨subd19_2_38, List.forall_mem_cons.2 ⟨subd19_2_39, List.forall_mem_cons.2 ⟨subd19_2_40, List.forall_mem_cons.2 ⟨subd19_2_41, List.forall_mem_cons.2 ⟨subd19_2_42, List.forall_mem_cons.2 ⟨subd19_2_43, List.forall_mem_cons.2 ⟨subd19_2_44, List.forall_mem_cons.2 ⟨subd19_2_45, List.forall_mem_cons.2 ⟨subd19_2_46, List.forall_mem_cons.2 ⟨subd19_2_47, List.forall_mem_cons.2 ⟨subd19_2_48, List.forall_mem_cons.2 ⟨subd19_2_49, List.forall_mem_cons.2 ⟨subd19_2_50, List.forall_mem_cons.2 ⟨subd19_2_51, List.forall_mem_cons.2 ⟨subd19_2_52, List.forall_mem_cons.2 ⟨subd19_2_53, List.forall_mem_cons.2 ⟨subd19_2_54, List.forall_mem_cons.2 ⟨subd19_2_55, List.forall_mem_cons.2 ⟨subd19_2_56, List.forall_mem_cons.2 ⟨subd19_2_57, List.forall_mem_cons.2 ⟨subd19_2_58, List.forall_mem_cons.2 ⟨subd19_2_59, List.forall_mem_cons.2 ⟨subd19_2_60, List.forall_mem_cons.2 ⟨subd19_2_61, List.forall_mem_cons.2 ⟨subd19_2_62, List.forall_mem_cons.2 ⟨subd19_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_64 : subd19_2 [-4, 2, -8] = true := by decide +kernel
theorem subd19_2_65 : subd19_2 [-4, 2, -7] = true := by decide +kernel
theorem subd19_2_66 : subd19_2 [-4, 2, -6] = true := by decide +kernel
theorem subd19_2_67 : subd19_2 [-4, 2, -5] = true := by decide +kernel
theorem subd19_2_68 : subd19_2 [-4, 2, -4] = true := by decide +kernel
theorem subd19_2_69 : subd19_2 [-4, 2, -3] = true := by decide +kernel
theorem subd19_2_70 : subd19_2 [-4, 2, -2] = true := by decide +kernel
theorem subd19_2_71 : subd19_2 [-4, 2, -1] = true := by decide +kernel
theorem subd19_2_72 : subd19_2 [-4, 2, 0] = true := by decide +kernel
theorem subd19_2_73 : subd19_2 [-4, 2, 1] = true := by decide +kernel
theorem subd19_2_74 : subd19_2 [-4, 2, 2] = true := by decide +kernel
theorem subd19_2_75 : subd19_2 [-4, 2, 3] = true := by decide +kernel
theorem subd19_2_76 : subd19_2 [-4, 2, 4] = true := by decide +kernel
theorem subd19_2_77 : subd19_2 [-4, 2, 5] = true := by decide +kernel
theorem subd19_2_78 : subd19_2 [-4, 2, 6] = true := by decide +kernel
theorem subd19_2_79 : subd19_2 [-4, 3, -8] = true := by decide +kernel
theorem subd19_2_80 : subd19_2 [-4, 3, -7] = true := by decide +kernel
theorem subd19_2_81 : subd19_2 [-4, 3, -6] = true := by decide +kernel
theorem subd19_2_82 : subd19_2 [-4, 3, -5] = true := by decide +kernel
theorem subd19_2_83 : subd19_2 [-4, 3, -4] = true := by decide +kernel
theorem subd19_2_84 : subd19_2 [-4, 3, -3] = true := by decide +kernel
theorem subd19_2_85 : subd19_2 [-4, 3, -2] = true := by decide +kernel
theorem subd19_2_86 : subd19_2 [-4, 3, -1] = true := by decide +kernel
theorem subd19_2_87 : subd19_2 [-4, 3, 0] = true := by decide +kernel
theorem subd19_2_88 : subd19_2 [-4, 3, 1] = true := by decide +kernel
theorem subd19_2_89 : subd19_2 [-4, 3, 2] = true := by decide +kernel
theorem subd19_2_90 : subd19_2 [-4, 3, 3] = true := by decide +kernel
theorem subd19_2_91 : subd19_2 [-4, 3, 4] = true := by decide +kernel
theorem subd19_2_92 : subd19_2 [-4, 3, 5] = true := by decide +kernel
theorem subd19_2_93 : subd19_2 [-4, 3, 6] = true := by decide +kernel
theorem subd19_2_94 : subd19_2 [-4, 4] = true := by decide +kernel
theorem subd19_2_95 : subd19_2 [-4, 5] = true := by decide +kernel
theorem sbd19_2_2 : ∀ q ∈ blkd19_2_2, subd19_2 q = true := by
  unfold blkd19_2_2
  exact List.forall_mem_cons.2 ⟨subd19_2_64, List.forall_mem_cons.2 ⟨subd19_2_65, List.forall_mem_cons.2 ⟨subd19_2_66, List.forall_mem_cons.2 ⟨subd19_2_67, List.forall_mem_cons.2 ⟨subd19_2_68, List.forall_mem_cons.2 ⟨subd19_2_69, List.forall_mem_cons.2 ⟨subd19_2_70, List.forall_mem_cons.2 ⟨subd19_2_71, List.forall_mem_cons.2 ⟨subd19_2_72, List.forall_mem_cons.2 ⟨subd19_2_73, List.forall_mem_cons.2 ⟨subd19_2_74, List.forall_mem_cons.2 ⟨subd19_2_75, List.forall_mem_cons.2 ⟨subd19_2_76, List.forall_mem_cons.2 ⟨subd19_2_77, List.forall_mem_cons.2 ⟨subd19_2_78, List.forall_mem_cons.2 ⟨subd19_2_79, List.forall_mem_cons.2 ⟨subd19_2_80, List.forall_mem_cons.2 ⟨subd19_2_81, List.forall_mem_cons.2 ⟨subd19_2_82, List.forall_mem_cons.2 ⟨subd19_2_83, List.forall_mem_cons.2 ⟨subd19_2_84, List.forall_mem_cons.2 ⟨subd19_2_85, List.forall_mem_cons.2 ⟨subd19_2_86, List.forall_mem_cons.2 ⟨subd19_2_87, List.forall_mem_cons.2 ⟨subd19_2_88, List.forall_mem_cons.2 ⟨subd19_2_89, List.forall_mem_cons.2 ⟨subd19_2_90, List.forall_mem_cons.2 ⟨subd19_2_91, List.forall_mem_cons.2 ⟨subd19_2_92, List.forall_mem_cons.2 ⟨subd19_2_93, List.forall_mem_cons.2 ⟨subd19_2_94, List.forall_mem_cons.2 ⟨subd19_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_96 : subd19_2 [-4, 6] = true := by decide +kernel
theorem subd19_2_97 : subd19_2 [-4, 7] = true := by decide +kernel
theorem subd19_2_98 : subd19_2 [-3, -6] = true := by decide +kernel
theorem subd19_2_99 : subd19_2 [-3, -5] = true := by decide +kernel
theorem subd19_2_100 : subd19_2 [-3, -4] = true := by decide +kernel
theorem subd19_2_101 : subd19_2 [-3, -3] = true := by decide +kernel
theorem subd19_2_102 : subd19_2 [-3, -2, -7] = true := by decide +kernel
theorem subd19_2_103 : subd19_2 [-3, -2, -6] = true := by decide +kernel
theorem subd19_2_104 : subd19_2 [-3, -2, -5] = true := by decide +kernel
theorem subd19_2_105 : subd19_2 [-3, -2, -4] = true := by decide +kernel
theorem subd19_2_106 : subd19_2 [-3, -2, -3] = true := by decide +kernel
theorem subd19_2_107 : subd19_2 [-3, -2, -2] = true := by decide +kernel
theorem subd19_2_108 : subd19_2 [-3, -2, -1] = true := by decide +kernel
theorem subd19_2_109 : subd19_2 [-3, -2, 0] = true := by decide +kernel
theorem subd19_2_110 : subd19_2 [-3, -2, 1] = true := by decide +kernel
theorem subd19_2_111 : subd19_2 [-3, -2, 2] = true := by decide +kernel
theorem subd19_2_112 : subd19_2 [-3, -2, 3] = true := by decide +kernel
theorem subd19_2_113 : subd19_2 [-3, -2, 4] = true := by decide +kernel
theorem subd19_2_114 : subd19_2 [-3, -2, 5] = true := by decide +kernel
theorem subd19_2_115 : subd19_2 [-3, -2, 6] = true := by decide +kernel
theorem subd19_2_116 : subd19_2 [-3, -1, -8] = true := by decide +kernel
theorem subd19_2_117 : subd19_2 [-3, -1, -7] = true := by decide +kernel
theorem subd19_2_118 : subd19_2 [-3, -1, -6] = true := by decide +kernel
theorem subd19_2_119 : subd19_2 [-3, -1, -5] = true := by decide +kernel
theorem subd19_2_120 : subd19_2 [-3, -1, -4] = true := by decide +kernel
theorem subd19_2_121 : subd19_2 [-3, -1, -3] = true := by decide +kernel
theorem subd19_2_122 : subd19_2 [-3, -1, -2] = true := by decide +kernel
theorem subd19_2_123 : subd19_2 [-3, -1, -1] = true := by decide +kernel
theorem subd19_2_124 : subd19_2 [-3, -1, 0] = true := by decide +kernel
theorem subd19_2_125 : subd19_2 [-3, -1, 1] = true := by decide +kernel
theorem subd19_2_126 : subd19_2 [-3, -1, 2] = true := by decide +kernel
theorem subd19_2_127 : subd19_2 [-3, -1, 3] = true := by decide +kernel
theorem sbd19_2_3 : ∀ q ∈ blkd19_2_3, subd19_2 q = true := by
  unfold blkd19_2_3
  exact List.forall_mem_cons.2 ⟨subd19_2_96, List.forall_mem_cons.2 ⟨subd19_2_97, List.forall_mem_cons.2 ⟨subd19_2_98, List.forall_mem_cons.2 ⟨subd19_2_99, List.forall_mem_cons.2 ⟨subd19_2_100, List.forall_mem_cons.2 ⟨subd19_2_101, List.forall_mem_cons.2 ⟨subd19_2_102, List.forall_mem_cons.2 ⟨subd19_2_103, List.forall_mem_cons.2 ⟨subd19_2_104, List.forall_mem_cons.2 ⟨subd19_2_105, List.forall_mem_cons.2 ⟨subd19_2_106, List.forall_mem_cons.2 ⟨subd19_2_107, List.forall_mem_cons.2 ⟨subd19_2_108, List.forall_mem_cons.2 ⟨subd19_2_109, List.forall_mem_cons.2 ⟨subd19_2_110, List.forall_mem_cons.2 ⟨subd19_2_111, List.forall_mem_cons.2 ⟨subd19_2_112, List.forall_mem_cons.2 ⟨subd19_2_113, List.forall_mem_cons.2 ⟨subd19_2_114, List.forall_mem_cons.2 ⟨subd19_2_115, List.forall_mem_cons.2 ⟨subd19_2_116, List.forall_mem_cons.2 ⟨subd19_2_117, List.forall_mem_cons.2 ⟨subd19_2_118, List.forall_mem_cons.2 ⟨subd19_2_119, List.forall_mem_cons.2 ⟨subd19_2_120, List.forall_mem_cons.2 ⟨subd19_2_121, List.forall_mem_cons.2 ⟨subd19_2_122, List.forall_mem_cons.2 ⟨subd19_2_123, List.forall_mem_cons.2 ⟨subd19_2_124, List.forall_mem_cons.2 ⟨subd19_2_125, List.forall_mem_cons.2 ⟨subd19_2_126, List.forall_mem_cons.2 ⟨subd19_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_128 : subd19_2 [-3, -1, 4] = true := by decide +kernel
theorem subd19_2_129 : subd19_2 [-3, -1, 5] = true := by decide +kernel
theorem subd19_2_130 : subd19_2 [-3, -1, 6] = true := by decide +kernel
theorem subd19_2_131 : subd19_2 [-3, 0, -8] = true := by decide +kernel
theorem subd19_2_132 : subd19_2 [-3, 0, -7] = true := by decide +kernel
theorem subd19_2_133 : subd19_2 [-3, 0, -6] = true := by decide +kernel
theorem subd19_2_134 : subd19_2 [-3, 0, -5] = true := by decide +kernel
theorem subd19_2_135 : subd19_2 [-3, 0, -4] = true := by decide +kernel
theorem subd19_2_136 : subd19_2 [-3, 0, -3] = true := by decide +kernel
theorem subd19_2_137 : subd19_2 [-3, 0, -2] = true := by decide +kernel
theorem subd19_2_138 : subd19_2 [-3, 0, -1] = true := by decide +kernel
theorem subd19_2_139 : subd19_2 [-3, 0, 0] = true := by decide +kernel
theorem subd19_2_140 : subd19_2 [-3, 0, 1] = true := by decide +kernel
theorem subd19_2_141 : subd19_2 [-3, 0, 2] = true := by decide +kernel
theorem subd19_2_142 : subd19_2 [-3, 0, 3] = true := by decide +kernel
theorem subd19_2_143 : subd19_2 [-3, 0, 4] = true := by decide +kernel
theorem subd19_2_144 : subd19_2 [-3, 0, 5] = true := by decide +kernel
theorem subd19_2_145 : subd19_2 [-3, 0, 6] = true := by decide +kernel
theorem subd19_2_146 : subd19_2 [-3, 1, -8] = true := by decide +kernel
theorem subd19_2_147 : subd19_2 [-3, 1, -7] = true := by decide +kernel
theorem subd19_2_148 : subd19_2 [-3, 1, -6] = true := by decide +kernel
theorem subd19_2_149 : subd19_2 [-3, 1, -5] = true := by decide +kernel
theorem subd19_2_150 : subd19_2 [-3, 1, -4] = true := by decide +kernel
theorem subd19_2_151 : subd19_2 [-3, 1, -3] = true := by decide +kernel
theorem subd19_2_152 : subd19_2 [-3, 1, -2] = true := by decide +kernel
theorem subd19_2_153 : subd19_2 [-3, 1, -1] = true := by decide +kernel
theorem subd19_2_154 : subd19_2 [-3, 1, 0] = true := by decide +kernel
theorem subd19_2_155 : subd19_2 [-3, 1, 1] = true := by decide +kernel
theorem subd19_2_156 : subd19_2 [-3, 1, 2] = true := by decide +kernel
theorem subd19_2_157 : subd19_2 [-3, 1, 3] = true := by decide +kernel
theorem subd19_2_158 : subd19_2 [-3, 1, 4] = true := by decide +kernel
theorem subd19_2_159 : subd19_2 [-3, 1, 5] = true := by decide +kernel
theorem sbd19_2_4 : ∀ q ∈ blkd19_2_4, subd19_2 q = true := by
  unfold blkd19_2_4
  exact List.forall_mem_cons.2 ⟨subd19_2_128, List.forall_mem_cons.2 ⟨subd19_2_129, List.forall_mem_cons.2 ⟨subd19_2_130, List.forall_mem_cons.2 ⟨subd19_2_131, List.forall_mem_cons.2 ⟨subd19_2_132, List.forall_mem_cons.2 ⟨subd19_2_133, List.forall_mem_cons.2 ⟨subd19_2_134, List.forall_mem_cons.2 ⟨subd19_2_135, List.forall_mem_cons.2 ⟨subd19_2_136, List.forall_mem_cons.2 ⟨subd19_2_137, List.forall_mem_cons.2 ⟨subd19_2_138, List.forall_mem_cons.2 ⟨subd19_2_139, List.forall_mem_cons.2 ⟨subd19_2_140, List.forall_mem_cons.2 ⟨subd19_2_141, List.forall_mem_cons.2 ⟨subd19_2_142, List.forall_mem_cons.2 ⟨subd19_2_143, List.forall_mem_cons.2 ⟨subd19_2_144, List.forall_mem_cons.2 ⟨subd19_2_145, List.forall_mem_cons.2 ⟨subd19_2_146, List.forall_mem_cons.2 ⟨subd19_2_147, List.forall_mem_cons.2 ⟨subd19_2_148, List.forall_mem_cons.2 ⟨subd19_2_149, List.forall_mem_cons.2 ⟨subd19_2_150, List.forall_mem_cons.2 ⟨subd19_2_151, List.forall_mem_cons.2 ⟨subd19_2_152, List.forall_mem_cons.2 ⟨subd19_2_153, List.forall_mem_cons.2 ⟨subd19_2_154, List.forall_mem_cons.2 ⟨subd19_2_155, List.forall_mem_cons.2 ⟨subd19_2_156, List.forall_mem_cons.2 ⟨subd19_2_157, List.forall_mem_cons.2 ⟨subd19_2_158, List.forall_mem_cons.2 ⟨subd19_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_160 : subd19_2 [-3, 1, 6] = true := by decide +kernel
theorem subd19_2_161 : subd19_2 [-3, 2, -8] = true := by decide +kernel
theorem subd19_2_162 : subd19_2 [-3, 2, -7] = true := by decide +kernel
theorem subd19_2_163 : subd19_2 [-3, 2, -6] = true := by decide +kernel
theorem subd19_2_164 : subd19_2 [-3, 2, -5] = true := by decide +kernel
theorem subd19_2_165 : subd19_2 [-3, 2, -4] = true := by decide +kernel
theorem subd19_2_166 : subd19_2 [-3, 2, -3] = true := by decide +kernel
theorem subd19_2_167 : subd19_2 [-3, 2, -2] = true := by decide +kernel
theorem subd19_2_168 : subd19_2 [-3, 2, -1] = true := by decide +kernel
theorem subd19_2_169 : subd19_2 [-3, 2, 0] = true := by decide +kernel
theorem subd19_2_170 : subd19_2 [-3, 2, 1] = true := by decide +kernel
theorem subd19_2_171 : subd19_2 [-3, 2, 2] = true := by decide +kernel
theorem subd19_2_172 : subd19_2 [-3, 2, 3] = true := by decide +kernel
theorem subd19_2_173 : subd19_2 [-3, 2, 4] = true := by decide +kernel
theorem subd19_2_174 : subd19_2 [-3, 2, 5] = true := by decide +kernel
theorem subd19_2_175 : subd19_2 [-3, 2, 6] = true := by decide +kernel
theorem subd19_2_176 : subd19_2 [-3, 3, -8] = true := by decide +kernel
theorem subd19_2_177 : subd19_2 [-3, 3, -7] = true := by decide +kernel
theorem subd19_2_178 : subd19_2 [-3, 3, -6] = true := by decide +kernel
theorem subd19_2_179 : subd19_2 [-3, 3, -5] = true := by decide +kernel
theorem subd19_2_180 : subd19_2 [-3, 3, -4] = true := by decide +kernel
theorem subd19_2_181 : subd19_2 [-3, 3, -3] = true := by decide +kernel
theorem subd19_2_182 : subd19_2 [-3, 3, -2] = true := by decide +kernel
theorem subd19_2_183 : subd19_2 [-3, 3, -1] = true := by decide +kernel
theorem subd19_2_184 : subd19_2 [-3, 3, 0] = true := by decide +kernel
theorem subd19_2_185 : subd19_2 [-3, 3, 1] = true := by decide +kernel
theorem subd19_2_186 : subd19_2 [-3, 3, 2] = true := by decide +kernel
theorem subd19_2_187 : subd19_2 [-3, 3, 3] = true := by decide +kernel
theorem subd19_2_188 : subd19_2 [-3, 3, 4] = true := by decide +kernel
theorem subd19_2_189 : subd19_2 [-3, 3, 5] = true := by decide +kernel
theorem subd19_2_190 : subd19_2 [-3, 3, 6] = true := by decide +kernel
theorem subd19_2_191 : subd19_2 [-3, 4, -7] = true := by decide +kernel
theorem sbd19_2_5 : ∀ q ∈ blkd19_2_5, subd19_2 q = true := by
  unfold blkd19_2_5
  exact List.forall_mem_cons.2 ⟨subd19_2_160, List.forall_mem_cons.2 ⟨subd19_2_161, List.forall_mem_cons.2 ⟨subd19_2_162, List.forall_mem_cons.2 ⟨subd19_2_163, List.forall_mem_cons.2 ⟨subd19_2_164, List.forall_mem_cons.2 ⟨subd19_2_165, List.forall_mem_cons.2 ⟨subd19_2_166, List.forall_mem_cons.2 ⟨subd19_2_167, List.forall_mem_cons.2 ⟨subd19_2_168, List.forall_mem_cons.2 ⟨subd19_2_169, List.forall_mem_cons.2 ⟨subd19_2_170, List.forall_mem_cons.2 ⟨subd19_2_171, List.forall_mem_cons.2 ⟨subd19_2_172, List.forall_mem_cons.2 ⟨subd19_2_173, List.forall_mem_cons.2 ⟨subd19_2_174, List.forall_mem_cons.2 ⟨subd19_2_175, List.forall_mem_cons.2 ⟨subd19_2_176, List.forall_mem_cons.2 ⟨subd19_2_177, List.forall_mem_cons.2 ⟨subd19_2_178, List.forall_mem_cons.2 ⟨subd19_2_179, List.forall_mem_cons.2 ⟨subd19_2_180, List.forall_mem_cons.2 ⟨subd19_2_181, List.forall_mem_cons.2 ⟨subd19_2_182, List.forall_mem_cons.2 ⟨subd19_2_183, List.forall_mem_cons.2 ⟨subd19_2_184, List.forall_mem_cons.2 ⟨subd19_2_185, List.forall_mem_cons.2 ⟨subd19_2_186, List.forall_mem_cons.2 ⟨subd19_2_187, List.forall_mem_cons.2 ⟨subd19_2_188, List.forall_mem_cons.2 ⟨subd19_2_189, List.forall_mem_cons.2 ⟨subd19_2_190, List.forall_mem_cons.2 ⟨subd19_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_192 : subd19_2 [-3, 4, -6] = true := by decide +kernel
theorem subd19_2_193 : subd19_2 [-3, 4, -5] = true := by decide +kernel
theorem subd19_2_194 : subd19_2 [-3, 4, -4] = true := by decide +kernel
theorem subd19_2_195 : subd19_2 [-3, 4, -3] = true := by decide +kernel
theorem subd19_2_196 : subd19_2 [-3, 4, -2] = true := by decide +kernel
theorem subd19_2_197 : subd19_2 [-3, 4, -1] = true := by decide +kernel
theorem subd19_2_198 : subd19_2 [-3, 4, 0] = true := by decide +kernel
theorem subd19_2_199 : subd19_2 [-3, 4, 1] = true := by decide +kernel
theorem subd19_2_200 : subd19_2 [-3, 4, 2] = true := by decide +kernel
theorem subd19_2_201 : subd19_2 [-3, 4, 3] = true := by decide +kernel
theorem subd19_2_202 : subd19_2 [-3, 4, 4] = true := by decide +kernel
theorem subd19_2_203 : subd19_2 [-3, 4, 5] = true := by decide +kernel
theorem subd19_2_204 : subd19_2 [-3, 4, 6] = true := by decide +kernel
theorem subd19_2_205 : subd19_2 [-3, 5] = true := by decide +kernel
theorem subd19_2_206 : subd19_2 [-3, 6] = true := by decide +kernel
theorem subd19_2_207 : subd19_2 [-3, 7] = true := by decide +kernel
theorem subd19_2_208 : subd19_2 [-2, -7] = true := by decide +kernel
theorem subd19_2_209 : subd19_2 [-2, -6] = true := by decide +kernel
theorem subd19_2_210 : subd19_2 [-2, -5] = true := by decide +kernel
theorem subd19_2_211 : subd19_2 [-2, -4] = true := by decide +kernel
theorem subd19_2_212 : subd19_2 [-2, -3, -7] = true := by decide +kernel
theorem subd19_2_213 : subd19_2 [-2, -3, -6] = true := by decide +kernel
theorem subd19_2_214 : subd19_2 [-2, -3, -5] = true := by decide +kernel
theorem subd19_2_215 : subd19_2 [-2, -3, -4] = true := by decide +kernel
theorem subd19_2_216 : subd19_2 [-2, -3, -3] = true := by decide +kernel
theorem subd19_2_217 : subd19_2 [-2, -3, -2] = true := by decide +kernel
theorem subd19_2_218 : subd19_2 [-2, -3, -1] = true := by decide +kernel
theorem subd19_2_219 : subd19_2 [-2, -3, 0] = true := by decide +kernel
theorem subd19_2_220 : subd19_2 [-2, -3, 1] = true := by decide +kernel
theorem subd19_2_221 : subd19_2 [-2, -3, 2] = true := by decide +kernel
theorem subd19_2_222 : subd19_2 [-2, -3, 3] = true := by decide +kernel
theorem subd19_2_223 : subd19_2 [-2, -3, 4] = true := by decide +kernel
theorem sbd19_2_6 : ∀ q ∈ blkd19_2_6, subd19_2 q = true := by
  unfold blkd19_2_6
  exact List.forall_mem_cons.2 ⟨subd19_2_192, List.forall_mem_cons.2 ⟨subd19_2_193, List.forall_mem_cons.2 ⟨subd19_2_194, List.forall_mem_cons.2 ⟨subd19_2_195, List.forall_mem_cons.2 ⟨subd19_2_196, List.forall_mem_cons.2 ⟨subd19_2_197, List.forall_mem_cons.2 ⟨subd19_2_198, List.forall_mem_cons.2 ⟨subd19_2_199, List.forall_mem_cons.2 ⟨subd19_2_200, List.forall_mem_cons.2 ⟨subd19_2_201, List.forall_mem_cons.2 ⟨subd19_2_202, List.forall_mem_cons.2 ⟨subd19_2_203, List.forall_mem_cons.2 ⟨subd19_2_204, List.forall_mem_cons.2 ⟨subd19_2_205, List.forall_mem_cons.2 ⟨subd19_2_206, List.forall_mem_cons.2 ⟨subd19_2_207, List.forall_mem_cons.2 ⟨subd19_2_208, List.forall_mem_cons.2 ⟨subd19_2_209, List.forall_mem_cons.2 ⟨subd19_2_210, List.forall_mem_cons.2 ⟨subd19_2_211, List.forall_mem_cons.2 ⟨subd19_2_212, List.forall_mem_cons.2 ⟨subd19_2_213, List.forall_mem_cons.2 ⟨subd19_2_214, List.forall_mem_cons.2 ⟨subd19_2_215, List.forall_mem_cons.2 ⟨subd19_2_216, List.forall_mem_cons.2 ⟨subd19_2_217, List.forall_mem_cons.2 ⟨subd19_2_218, List.forall_mem_cons.2 ⟨subd19_2_219, List.forall_mem_cons.2 ⟨subd19_2_220, List.forall_mem_cons.2 ⟨subd19_2_221, List.forall_mem_cons.2 ⟨subd19_2_222, List.forall_mem_cons.2 ⟨subd19_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_224 : subd19_2 [-2, -3, 5] = true := by decide +kernel
theorem subd19_2_225 : subd19_2 [-2, -3, 6] = true := by decide +kernel
theorem subd19_2_226 : subd19_2 [-2, -2, -8] = true := by decide +kernel
theorem subd19_2_227 : subd19_2 [-2, -2, -7] = true := by decide +kernel
theorem subd19_2_228 : subd19_2 [-2, -2, -6] = true := by decide +kernel
theorem subd19_2_229 : subd19_2 [-2, -2, -5] = true := by decide +kernel
theorem subd19_2_230 : subd19_2 [-2, -2, -4] = true := by decide +kernel
theorem subd19_2_231 : subd19_2 [-2, -2, -3] = true := by decide +kernel
theorem subd19_2_232 : subd19_2 [-2, -2, -2] = true := by decide +kernel
theorem subd19_2_233 : subd19_2 [-2, -2, -1] = true := by decide +kernel
theorem subd19_2_234 : subd19_2 [-2, -2, 0] = true := by decide +kernel
theorem subd19_2_235 : subd19_2 [-2, -2, 1] = true := by decide +kernel
theorem subd19_2_236 : subd19_2 [-2, -2, 2] = true := by decide +kernel
theorem subd19_2_237 : subd19_2 [-2, -2, 3] = true := by decide +kernel
theorem subd19_2_238 : subd19_2 [-2, -2, 4] = true := by decide +kernel
theorem subd19_2_239 : subd19_2 [-2, -2, 5] = true := by decide +kernel
theorem subd19_2_240 : subd19_2 [-2, -2, 6] = true := by decide +kernel
theorem subd19_2_241 : subd19_2 [-2, -1, -8] = true := by decide +kernel
theorem subd19_2_242 : subd19_2 [-2, -1, -7] = true := by decide +kernel
theorem subd19_2_243 : subd19_2 [-2, -1, -6] = true := by decide +kernel
theorem subd19_2_244 : subd19_2 [-2, -1, -5] = true := by decide +kernel
theorem subd19_2_245 : subd19_2 [-2, -1, -4] = true := by decide +kernel
theorem subd19_2_246 : subd19_2 [-2, -1, -3] = true := by decide +kernel
theorem subd19_2_247 : subd19_2 [-2, -1, -2] = true := by decide +kernel
theorem subd19_2_248 : subd19_2 [-2, -1, -1] = true := by decide +kernel
theorem subd19_2_249 : subd19_2 [-2, -1, 0] = true := by decide +kernel
theorem subd19_2_250 : subd19_2 [-2, -1, 1] = true := by decide +kernel
theorem subd19_2_251 : subd19_2 [-2, -1, 2] = true := by decide +kernel
theorem subd19_2_252 : subd19_2 [-2, -1, 3] = true := by decide +kernel
theorem subd19_2_253 : subd19_2 [-2, -1, 4] = true := by decide +kernel
theorem subd19_2_254 : subd19_2 [-2, -1, 5] = true := by decide +kernel
theorem subd19_2_255 : subd19_2 [-2, -1, 6] = true := by decide +kernel
theorem sbd19_2_7 : ∀ q ∈ blkd19_2_7, subd19_2 q = true := by
  unfold blkd19_2_7
  exact List.forall_mem_cons.2 ⟨subd19_2_224, List.forall_mem_cons.2 ⟨subd19_2_225, List.forall_mem_cons.2 ⟨subd19_2_226, List.forall_mem_cons.2 ⟨subd19_2_227, List.forall_mem_cons.2 ⟨subd19_2_228, List.forall_mem_cons.2 ⟨subd19_2_229, List.forall_mem_cons.2 ⟨subd19_2_230, List.forall_mem_cons.2 ⟨subd19_2_231, List.forall_mem_cons.2 ⟨subd19_2_232, List.forall_mem_cons.2 ⟨subd19_2_233, List.forall_mem_cons.2 ⟨subd19_2_234, List.forall_mem_cons.2 ⟨subd19_2_235, List.forall_mem_cons.2 ⟨subd19_2_236, List.forall_mem_cons.2 ⟨subd19_2_237, List.forall_mem_cons.2 ⟨subd19_2_238, List.forall_mem_cons.2 ⟨subd19_2_239, List.forall_mem_cons.2 ⟨subd19_2_240, List.forall_mem_cons.2 ⟨subd19_2_241, List.forall_mem_cons.2 ⟨subd19_2_242, List.forall_mem_cons.2 ⟨subd19_2_243, List.forall_mem_cons.2 ⟨subd19_2_244, List.forall_mem_cons.2 ⟨subd19_2_245, List.forall_mem_cons.2 ⟨subd19_2_246, List.forall_mem_cons.2 ⟨subd19_2_247, List.forall_mem_cons.2 ⟨subd19_2_248, List.forall_mem_cons.2 ⟨subd19_2_249, List.forall_mem_cons.2 ⟨subd19_2_250, List.forall_mem_cons.2 ⟨subd19_2_251, List.forall_mem_cons.2 ⟨subd19_2_252, List.forall_mem_cons.2 ⟨subd19_2_253, List.forall_mem_cons.2 ⟨subd19_2_254, List.forall_mem_cons.2 ⟨subd19_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_256 : subd19_2 [-2, -1, 7] = true := by decide +kernel
theorem subd19_2_257 : subd19_2 [-2, 0, -8] = true := by decide +kernel
theorem subd19_2_258 : subd19_2 [-2, 0, -7] = true := by decide +kernel
theorem subd19_2_259 : subd19_2 [-2, 0, -6] = true := by decide +kernel
theorem subd19_2_260 : subd19_2 [-2, 0, -5] = true := by decide +kernel
theorem subd19_2_261 : subd19_2 [-2, 0, -4] = true := by decide +kernel
theorem subd19_2_262 : subd19_2 [-2, 0, -3] = true := by decide +kernel
theorem subd19_2_263 : subd19_2 [-2, 0, -2] = true := by decide +kernel
theorem subd19_2_264 : subd19_2 [-2, 0, -1] = true := by decide +kernel
theorem subd19_2_265 : subd19_2 [-2, 0, 0] = true := by decide +kernel
theorem subd19_2_266 : subd19_2 [-2, 0, 1] = true := by decide +kernel
theorem subd19_2_267 : subd19_2 [-2, 0, 2] = true := by decide +kernel
theorem subd19_2_268 : subd19_2 [-2, 0, 3] = true := by decide +kernel
theorem subd19_2_269 : subd19_2 [-2, 0, 4] = true := by decide +kernel
theorem subd19_2_270 : subd19_2 [-2, 0, 5] = true := by decide +kernel
theorem subd19_2_271 : subd19_2 [-2, 0, 6] = true := by decide +kernel
theorem subd19_2_272 : subd19_2 [-2, 0, 7] = true := by decide +kernel
theorem subd19_2_273 : subd19_2 [-2, 1, -8] = true := by decide +kernel
theorem subd19_2_274 : subd19_2 [-2, 1, -7] = true := by decide +kernel
theorem subd19_2_275 : subd19_2 [-2, 1, -6] = true := by decide +kernel
theorem subd19_2_276 : subd19_2 [-2, 1, -5] = true := by decide +kernel
theorem subd19_2_277 : subd19_2 [-2, 1, -4] = true := by decide +kernel
theorem subd19_2_278 : subd19_2 [-2, 1, -3] = true := by decide +kernel
theorem subd19_2_279 : subd19_2 [-2, 1, -2] = true := by decide +kernel
theorem subd19_2_280 : subd19_2 [-2, 1, -1] = true := by decide +kernel
theorem subd19_2_281 : subd19_2 [-2, 1, 0] = true := by decide +kernel
theorem subd19_2_282 : subd19_2 [-2, 1, 1] = true := by decide +kernel
theorem subd19_2_283 : subd19_2 [-2, 1, 2] = true := by decide +kernel
theorem subd19_2_284 : subd19_2 [-2, 1, 3] = true := by decide +kernel
theorem subd19_2_285 : subd19_2 [-2, 1, 4] = true := by decide +kernel
theorem subd19_2_286 : subd19_2 [-2, 1, 5] = true := by decide +kernel
theorem subd19_2_287 : subd19_2 [-2, 1, 6] = true := by decide +kernel
theorem sbd19_2_8 : ∀ q ∈ blkd19_2_8, subd19_2 q = true := by
  unfold blkd19_2_8
  exact List.forall_mem_cons.2 ⟨subd19_2_256, List.forall_mem_cons.2 ⟨subd19_2_257, List.forall_mem_cons.2 ⟨subd19_2_258, List.forall_mem_cons.2 ⟨subd19_2_259, List.forall_mem_cons.2 ⟨subd19_2_260, List.forall_mem_cons.2 ⟨subd19_2_261, List.forall_mem_cons.2 ⟨subd19_2_262, List.forall_mem_cons.2 ⟨subd19_2_263, List.forall_mem_cons.2 ⟨subd19_2_264, List.forall_mem_cons.2 ⟨subd19_2_265, List.forall_mem_cons.2 ⟨subd19_2_266, List.forall_mem_cons.2 ⟨subd19_2_267, List.forall_mem_cons.2 ⟨subd19_2_268, List.forall_mem_cons.2 ⟨subd19_2_269, List.forall_mem_cons.2 ⟨subd19_2_270, List.forall_mem_cons.2 ⟨subd19_2_271, List.forall_mem_cons.2 ⟨subd19_2_272, List.forall_mem_cons.2 ⟨subd19_2_273, List.forall_mem_cons.2 ⟨subd19_2_274, List.forall_mem_cons.2 ⟨subd19_2_275, List.forall_mem_cons.2 ⟨subd19_2_276, List.forall_mem_cons.2 ⟨subd19_2_277, List.forall_mem_cons.2 ⟨subd19_2_278, List.forall_mem_cons.2 ⟨subd19_2_279, List.forall_mem_cons.2 ⟨subd19_2_280, List.forall_mem_cons.2 ⟨subd19_2_281, List.forall_mem_cons.2 ⟨subd19_2_282, List.forall_mem_cons.2 ⟨subd19_2_283, List.forall_mem_cons.2 ⟨subd19_2_284, List.forall_mem_cons.2 ⟨subd19_2_285, List.forall_mem_cons.2 ⟨subd19_2_286, List.forall_mem_cons.2 ⟨subd19_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_288 : subd19_2 [-2, 1, 7] = true := by decide +kernel
theorem subd19_2_289 : subd19_2 [-2, 2, -8] = true := by decide +kernel
theorem subd19_2_290 : subd19_2 [-2, 2, -7] = true := by decide +kernel
theorem subd19_2_291 : subd19_2 [-2, 2, -6] = true := by decide +kernel
theorem subd19_2_292 : subd19_2 [-2, 2, -5] = true := by decide +kernel
theorem subd19_2_293 : subd19_2 [-2, 2, -4] = true := by decide +kernel
theorem subd19_2_294 : subd19_2 [-2, 2, -3] = true := by decide +kernel
theorem subd19_2_295 : subd19_2 [-2, 2, -2] = true := by decide +kernel
theorem subd19_2_296 : subd19_2 [-2, 2, -1] = true := by decide +kernel
theorem subd19_2_297 : subd19_2 [-2, 2, 0] = true := by decide +kernel
theorem subd19_2_298 : subd19_2 [-2, 2, 1] = true := by decide +kernel
theorem subd19_2_299 : subd19_2 [-2, 2, 2] = true := by decide +kernel
theorem subd19_2_300 : subd19_2 [-2, 2, 3] = true := by decide +kernel
theorem subd19_2_301 : subd19_2 [-2, 2, 4] = true := by decide +kernel
theorem subd19_2_302 : subd19_2 [-2, 2, 5] = true := by decide +kernel
theorem subd19_2_303 : subd19_2 [-2, 2, 6] = true := by decide +kernel
theorem subd19_2_304 : subd19_2 [-2, 2, 7] = true := by decide +kernel
theorem subd19_2_305 : subd19_2 [-2, 3, -8] = true := by decide +kernel
theorem subd19_2_306 : subd19_2 [-2, 3, -7] = true := by decide +kernel
theorem subd19_2_307 : subd19_2 [-2, 3, -6] = true := by decide +kernel
theorem subd19_2_308 : subd19_2 [-2, 3, -5] = true := by decide +kernel
theorem subd19_2_309 : subd19_2 [-2, 3, -4] = true := by decide +kernel
theorem subd19_2_310 : subd19_2 [-2, 3, -3] = true := by decide +kernel
theorem subd19_2_311 : subd19_2 [-2, 3, -2] = true := by decide +kernel
theorem subd19_2_312 : subd19_2 [-2, 3, -1] = true := by decide +kernel
theorem subd19_2_313 : subd19_2 [-2, 3, 0] = true := by decide +kernel
theorem subd19_2_314 : subd19_2 [-2, 3, 1] = true := by decide +kernel
theorem subd19_2_315 : subd19_2 [-2, 3, 2] = true := by decide +kernel
theorem subd19_2_316 : subd19_2 [-2, 3, 3] = true := by decide +kernel
theorem subd19_2_317 : subd19_2 [-2, 3, 4] = true := by decide +kernel
theorem subd19_2_318 : subd19_2 [-2, 3, 5] = true := by decide +kernel
theorem subd19_2_319 : subd19_2 [-2, 3, 6] = true := by decide +kernel
theorem sbd19_2_9 : ∀ q ∈ blkd19_2_9, subd19_2 q = true := by
  unfold blkd19_2_9
  exact List.forall_mem_cons.2 ⟨subd19_2_288, List.forall_mem_cons.2 ⟨subd19_2_289, List.forall_mem_cons.2 ⟨subd19_2_290, List.forall_mem_cons.2 ⟨subd19_2_291, List.forall_mem_cons.2 ⟨subd19_2_292, List.forall_mem_cons.2 ⟨subd19_2_293, List.forall_mem_cons.2 ⟨subd19_2_294, List.forall_mem_cons.2 ⟨subd19_2_295, List.forall_mem_cons.2 ⟨subd19_2_296, List.forall_mem_cons.2 ⟨subd19_2_297, List.forall_mem_cons.2 ⟨subd19_2_298, List.forall_mem_cons.2 ⟨subd19_2_299, List.forall_mem_cons.2 ⟨subd19_2_300, List.forall_mem_cons.2 ⟨subd19_2_301, List.forall_mem_cons.2 ⟨subd19_2_302, List.forall_mem_cons.2 ⟨subd19_2_303, List.forall_mem_cons.2 ⟨subd19_2_304, List.forall_mem_cons.2 ⟨subd19_2_305, List.forall_mem_cons.2 ⟨subd19_2_306, List.forall_mem_cons.2 ⟨subd19_2_307, List.forall_mem_cons.2 ⟨subd19_2_308, List.forall_mem_cons.2 ⟨subd19_2_309, List.forall_mem_cons.2 ⟨subd19_2_310, List.forall_mem_cons.2 ⟨subd19_2_311, List.forall_mem_cons.2 ⟨subd19_2_312, List.forall_mem_cons.2 ⟨subd19_2_313, List.forall_mem_cons.2 ⟨subd19_2_314, List.forall_mem_cons.2 ⟨subd19_2_315, List.forall_mem_cons.2 ⟨subd19_2_316, List.forall_mem_cons.2 ⟨subd19_2_317, List.forall_mem_cons.2 ⟨subd19_2_318, List.forall_mem_cons.2 ⟨subd19_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_320 : subd19_2 [-2, 4, -8] = true := by decide +kernel
theorem subd19_2_321 : subd19_2 [-2, 4, -7] = true := by decide +kernel
theorem subd19_2_322 : subd19_2 [-2, 4, -6] = true := by decide +kernel
theorem subd19_2_323 : subd19_2 [-2, 4, -5] = true := by decide +kernel
theorem subd19_2_324 : subd19_2 [-2, 4, -4] = true := by decide +kernel
theorem subd19_2_325 : subd19_2 [-2, 4, -3] = true := by decide +kernel
theorem subd19_2_326 : subd19_2 [-2, 4, -2] = true := by decide +kernel
theorem subd19_2_327 : subd19_2 [-2, 4, -1] = true := by decide +kernel
theorem subd19_2_328 : subd19_2 [-2, 4, 0] = true := by decide +kernel
theorem subd19_2_329 : subd19_2 [-2, 4, 1] = true := by decide +kernel
theorem subd19_2_330 : subd19_2 [-2, 4, 2] = true := by decide +kernel
theorem subd19_2_331 : subd19_2 [-2, 4, 3] = true := by decide +kernel
theorem subd19_2_332 : subd19_2 [-2, 4, 4] = true := by decide +kernel
theorem subd19_2_333 : subd19_2 [-2, 4, 5] = true := by decide +kernel
theorem subd19_2_334 : subd19_2 [-2, 4, 6] = true := by decide +kernel
theorem subd19_2_335 : subd19_2 [-2, 5] = true := by decide +kernel
theorem subd19_2_336 : subd19_2 [-2, 6] = true := by decide +kernel
theorem subd19_2_337 : subd19_2 [-2, 7] = true := by decide +kernel
theorem subd19_2_338 : subd19_2 [-1, -7] = true := by decide +kernel
theorem subd19_2_339 : subd19_2 [-1, -6] = true := by decide +kernel
theorem subd19_2_340 : subd19_2 [-1, -5] = true := by decide +kernel
theorem subd19_2_341 : subd19_2 [-1, -4] = true := by decide +kernel
theorem subd19_2_342 : subd19_2 [-1, -3, -8] = true := by decide +kernel
theorem subd19_2_343 : subd19_2 [-1, -3, -7] = true := by decide +kernel
theorem subd19_2_344 : subd19_2 [-1, -3, -6] = true := by decide +kernel
theorem subd19_2_345 : subd19_2 [-1, -3, -5] = true := by decide +kernel
theorem subd19_2_346 : subd19_2 [-1, -3, -4] = true := by decide +kernel
theorem subd19_2_347 : subd19_2 [-1, -3, -3] = true := by decide +kernel
theorem subd19_2_348 : subd19_2 [-1, -3, -2] = true := by decide +kernel
theorem subd19_2_349 : subd19_2 [-1, -3, -1] = true := by decide +kernel
theorem subd19_2_350 : subd19_2 [-1, -3, 0] = true := by decide +kernel
theorem subd19_2_351 : subd19_2 [-1, -3, 1] = true := by decide +kernel
theorem sbd19_2_10 : ∀ q ∈ blkd19_2_10, subd19_2 q = true := by
  unfold blkd19_2_10
  exact List.forall_mem_cons.2 ⟨subd19_2_320, List.forall_mem_cons.2 ⟨subd19_2_321, List.forall_mem_cons.2 ⟨subd19_2_322, List.forall_mem_cons.2 ⟨subd19_2_323, List.forall_mem_cons.2 ⟨subd19_2_324, List.forall_mem_cons.2 ⟨subd19_2_325, List.forall_mem_cons.2 ⟨subd19_2_326, List.forall_mem_cons.2 ⟨subd19_2_327, List.forall_mem_cons.2 ⟨subd19_2_328, List.forall_mem_cons.2 ⟨subd19_2_329, List.forall_mem_cons.2 ⟨subd19_2_330, List.forall_mem_cons.2 ⟨subd19_2_331, List.forall_mem_cons.2 ⟨subd19_2_332, List.forall_mem_cons.2 ⟨subd19_2_333, List.forall_mem_cons.2 ⟨subd19_2_334, List.forall_mem_cons.2 ⟨subd19_2_335, List.forall_mem_cons.2 ⟨subd19_2_336, List.forall_mem_cons.2 ⟨subd19_2_337, List.forall_mem_cons.2 ⟨subd19_2_338, List.forall_mem_cons.2 ⟨subd19_2_339, List.forall_mem_cons.2 ⟨subd19_2_340, List.forall_mem_cons.2 ⟨subd19_2_341, List.forall_mem_cons.2 ⟨subd19_2_342, List.forall_mem_cons.2 ⟨subd19_2_343, List.forall_mem_cons.2 ⟨subd19_2_344, List.forall_mem_cons.2 ⟨subd19_2_345, List.forall_mem_cons.2 ⟨subd19_2_346, List.forall_mem_cons.2 ⟨subd19_2_347, List.forall_mem_cons.2 ⟨subd19_2_348, List.forall_mem_cons.2 ⟨subd19_2_349, List.forall_mem_cons.2 ⟨subd19_2_350, List.forall_mem_cons.2 ⟨subd19_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
