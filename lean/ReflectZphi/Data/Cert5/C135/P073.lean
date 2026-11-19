import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_3_0 : subd11_3 [-5, -4] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-5, -3] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-5, -2] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-5, -1] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-5, 0] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-5, 1] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-5, 2] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-4, -5] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-4, -4] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-4, -3] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-4, -2] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-4, -1] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-4, 0] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-4, 1] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [-4, 2] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [-4, 3] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [-3, -6] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [-3, -5] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [-3, -4] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [-3, -3] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [-3, -2] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [-3, -1] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [-3, 0] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [-3, 1] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [-3, 2] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [-3, 3] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [-3, 4] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [-2, -6] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [-2, -5] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [-2, -4] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [-2, -2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [-2, 0, -7] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [-2, 0, -6] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [-2, 0, -5] = true := by decide +kernel
theorem subd11_3_36 : subd11_3 [-2, 0, -4] = true := by decide +kernel
theorem subd11_3_37 : subd11_3 [-2, 0, -3] = true := by decide +kernel
theorem subd11_3_38 : subd11_3 [-2, 0, -2] = true := by decide +kernel
theorem subd11_3_39 : subd11_3 [-2, 0, -1] = true := by decide +kernel
theorem subd11_3_40 : subd11_3 [-2, 0, 0] = true := by decide +kernel
theorem subd11_3_41 : subd11_3 [-2, 0, 1] = true := by decide +kernel
theorem subd11_3_42 : subd11_3 [-2, 0, 2] = true := by decide +kernel
theorem subd11_3_43 : subd11_3 [-2, 0, 3] = true := by decide +kernel
theorem subd11_3_44 : subd11_3 [-2, 0, 4] = true := by decide +kernel
theorem subd11_3_45 : subd11_3 [-2, 0, 5] = true := by decide +kernel
theorem subd11_3_46 : subd11_3 [-2, 0, 6] = true := by decide +kernel
theorem subd11_3_47 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_48 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_49 : subd11_3 [-2, 3] = true := by decide +kernel
theorem subd11_3_50 : subd11_3 [-2, 4] = true := by decide +kernel
theorem subd11_3_51 : subd11_3 [-2, 5] = true := by decide +kernel
theorem subd11_3_52 : subd11_3 [-1, -7] = true := by decide +kernel
theorem subd11_3_53 : subd11_3 [-1, -6] = true := by decide +kernel
theorem subd11_3_54 : subd11_3 [-1, -5] = true := by decide +kernel
theorem subd11_3_55 : subd11_3 [-1, -4] = true := by decide +kernel
theorem subd11_3_56 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_57 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_58 : subd11_3 [-1, -1, -7] = true := by decide +kernel
theorem subd11_3_59 : subd11_3 [-1, -1, -6] = true := by decide +kernel
theorem subd11_3_60 : subd11_3 [-1, -1, -5] = true := by decide +kernel
theorem subd11_3_61 : subd11_3 [-1, -1, -4] = true := by decide +kernel
theorem subd11_3_62 : subd11_3 [-1, -1, -3] = true := by decide +kernel
theorem subd11_3_63 : subd11_3 [-1, -1, -2] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_cons.2 ⟨subd11_3_36, List.forall_mem_cons.2 ⟨subd11_3_37, List.forall_mem_cons.2 ⟨subd11_3_38, List.forall_mem_cons.2 ⟨subd11_3_39, List.forall_mem_cons.2 ⟨subd11_3_40, List.forall_mem_cons.2 ⟨subd11_3_41, List.forall_mem_cons.2 ⟨subd11_3_42, List.forall_mem_cons.2 ⟨subd11_3_43, List.forall_mem_cons.2 ⟨subd11_3_44, List.forall_mem_cons.2 ⟨subd11_3_45, List.forall_mem_cons.2 ⟨subd11_3_46, List.forall_mem_cons.2 ⟨subd11_3_47, List.forall_mem_cons.2 ⟨subd11_3_48, List.forall_mem_cons.2 ⟨subd11_3_49, List.forall_mem_cons.2 ⟨subd11_3_50, List.forall_mem_cons.2 ⟨subd11_3_51, List.forall_mem_cons.2 ⟨subd11_3_52, List.forall_mem_cons.2 ⟨subd11_3_53, List.forall_mem_cons.2 ⟨subd11_3_54, List.forall_mem_cons.2 ⟨subd11_3_55, List.forall_mem_cons.2 ⟨subd11_3_56, List.forall_mem_cons.2 ⟨subd11_3_57, List.forall_mem_cons.2 ⟨subd11_3_58, List.forall_mem_cons.2 ⟨subd11_3_59, List.forall_mem_cons.2 ⟨subd11_3_60, List.forall_mem_cons.2 ⟨subd11_3_61, List.forall_mem_cons.2 ⟨subd11_3_62, List.forall_mem_cons.2 ⟨subd11_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_64 : subd11_3 [-1, -1, -1] = true := by decide +kernel
theorem subd11_3_65 : subd11_3 [-1, -1, 0] = true := by decide +kernel
theorem subd11_3_66 : subd11_3 [-1, -1, 1] = true := by decide +kernel
theorem subd11_3_67 : subd11_3 [-1, -1, 2] = true := by decide +kernel
theorem subd11_3_68 : subd11_3 [-1, -1, 3] = true := by decide +kernel
theorem subd11_3_69 : subd11_3 [-1, -1, 4] = true := by decide +kernel
theorem subd11_3_70 : subd11_3 [-1, -1, 5] = true := by decide +kernel
theorem subd11_3_71 : subd11_3 [-1, -1, 6] = true := by decide +kernel
theorem subd11_3_72 : subd11_3 [-1, 0, -8] = true := by decide +kernel
theorem subd11_3_73 : subd11_3 [-1, 0, -7] = true := by decide +kernel
theorem subd11_3_74 : subd11_3 [-1, 0, -6] = true := by decide +kernel
theorem subd11_3_75 : subd11_3 [-1, 0, -5] = true := by decide +kernel
theorem subd11_3_76 : subd11_3 [-1, 0, -4] = true := by decide +kernel
theorem subd11_3_77 : subd11_3 [-1, 0, -3] = true := by decide +kernel
theorem subd11_3_78 : subd11_3 [-1, 0, -2] = true := by decide +kernel
theorem subd11_3_79 : subd11_3 [-1, 0, -1] = true := by decide +kernel
theorem subd11_3_80 : subd11_3 [-1, 0, 0] = true := by decide +kernel
theorem subd11_3_81 : subd11_3 [-1, 0, 1] = true := by decide +kernel
theorem subd11_3_82 : subd11_3 [-1, 0, 2] = true := by decide +kernel
theorem subd11_3_83 : subd11_3 [-1, 0, 3] = true := by decide +kernel
theorem subd11_3_84 : subd11_3 [-1, 0, 4] = true := by decide +kernel
theorem subd11_3_85 : subd11_3 [-1, 0, 5] = true := by decide +kernel
theorem subd11_3_86 : subd11_3 [-1, 0, 6] = true := by decide +kernel
theorem subd11_3_87 : subd11_3 [-1, 1, -7] = true := by decide +kernel
theorem subd11_3_88 : subd11_3 [-1, 1, -6] = true := by decide +kernel
theorem subd11_3_89 : subd11_3 [-1, 1, -5] = true := by decide +kernel
theorem subd11_3_90 : subd11_3 [-1, 1, -4] = true := by decide +kernel
theorem subd11_3_91 : subd11_3 [-1, 1, -3] = true := by decide +kernel
theorem subd11_3_92 : subd11_3 [-1, 1, -2] = true := by decide +kernel
theorem subd11_3_93 : subd11_3 [-1, 1, -1] = true := by decide +kernel
theorem subd11_3_94 : subd11_3 [-1, 1, 0] = true := by decide +kernel
theorem subd11_3_95 : subd11_3 [-1, 1, 1] = true := by decide +kernel
theorem sbd11_3_2 : ∀ q ∈ blkd11_3_2, subd11_3 q = true := by
  unfold blkd11_3_2
  exact List.forall_mem_cons.2 ⟨subd11_3_64, List.forall_mem_cons.2 ⟨subd11_3_65, List.forall_mem_cons.2 ⟨subd11_3_66, List.forall_mem_cons.2 ⟨subd11_3_67, List.forall_mem_cons.2 ⟨subd11_3_68, List.forall_mem_cons.2 ⟨subd11_3_69, List.forall_mem_cons.2 ⟨subd11_3_70, List.forall_mem_cons.2 ⟨subd11_3_71, List.forall_mem_cons.2 ⟨subd11_3_72, List.forall_mem_cons.2 ⟨subd11_3_73, List.forall_mem_cons.2 ⟨subd11_3_74, List.forall_mem_cons.2 ⟨subd11_3_75, List.forall_mem_cons.2 ⟨subd11_3_76, List.forall_mem_cons.2 ⟨subd11_3_77, List.forall_mem_cons.2 ⟨subd11_3_78, List.forall_mem_cons.2 ⟨subd11_3_79, List.forall_mem_cons.2 ⟨subd11_3_80, List.forall_mem_cons.2 ⟨subd11_3_81, List.forall_mem_cons.2 ⟨subd11_3_82, List.forall_mem_cons.2 ⟨subd11_3_83, List.forall_mem_cons.2 ⟨subd11_3_84, List.forall_mem_cons.2 ⟨subd11_3_85, List.forall_mem_cons.2 ⟨subd11_3_86, List.forall_mem_cons.2 ⟨subd11_3_87, List.forall_mem_cons.2 ⟨subd11_3_88, List.forall_mem_cons.2 ⟨subd11_3_89, List.forall_mem_cons.2 ⟨subd11_3_90, List.forall_mem_cons.2 ⟨subd11_3_91, List.forall_mem_cons.2 ⟨subd11_3_92, List.forall_mem_cons.2 ⟨subd11_3_93, List.forall_mem_cons.2 ⟨subd11_3_94, List.forall_mem_cons.2 ⟨subd11_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_96 : subd11_3 [-1, 1, 2] = true := by decide +kernel
theorem subd11_3_97 : subd11_3 [-1, 1, 3] = true := by decide +kernel
theorem subd11_3_98 : subd11_3 [-1, 1, 4] = true := by decide +kernel
theorem subd11_3_99 : subd11_3 [-1, 1, 5] = true := by decide +kernel
theorem subd11_3_100 : subd11_3 [-1, 1, 6] = true := by decide +kernel
theorem subd11_3_101 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_102 : subd11_3 [-1, 3] = true := by decide +kernel
theorem subd11_3_103 : subd11_3 [-1, 4] = true := by decide +kernel
theorem subd11_3_104 : subd11_3 [-1, 5] = true := by decide +kernel
theorem subd11_3_105 : subd11_3 [0, -7] = true := by decide +kernel
theorem subd11_3_106 : subd11_3 [0, -6] = true := by decide +kernel
theorem subd11_3_107 : subd11_3 [0, -5] = true := by decide +kernel
theorem subd11_3_108 : subd11_3 [0, -4] = true := by decide +kernel
theorem subd11_3_109 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_110 : subd11_3 [0, -2, -7] = true := by decide +kernel
theorem subd11_3_111 : subd11_3 [0, -2, -6] = true := by decide +kernel
theorem subd11_3_112 : subd11_3 [0, -2, -5] = true := by decide +kernel
theorem subd11_3_113 : subd11_3 [0, -2, -4] = true := by decide +kernel
theorem subd11_3_114 : subd11_3 [0, -2, -3] = true := by decide +kernel
theorem subd11_3_115 : subd11_3 [0, -2, -2] = true := by decide +kernel
theorem subd11_3_116 : subd11_3 [0, -2, -1] = true := by decide +kernel
theorem subd11_3_117 : subd11_3 [0, -2, 0] = true := by decide +kernel
theorem subd11_3_118 : subd11_3 [0, -2, 1] = true := by decide +kernel
theorem subd11_3_119 : subd11_3 [0, -2, 2] = true := by decide +kernel
theorem subd11_3_120 : subd11_3 [0, -2, 3] = true := by decide +kernel
theorem subd11_3_121 : subd11_3 [0, -2, 4] = true := by decide +kernel
theorem subd11_3_122 : subd11_3 [0, -2, 5] = true := by decide +kernel
theorem subd11_3_123 : subd11_3 [0, -2, 6] = true := by decide +kernel
theorem subd11_3_124 : subd11_3 [0, -1, -7] = true := by decide +kernel
theorem subd11_3_125 : subd11_3 [0, -1, -6] = true := by decide +kernel
theorem subd11_3_126 : subd11_3 [0, -1, -5] = true := by decide +kernel
theorem subd11_3_127 : subd11_3 [0, -1, -4] = true := by decide +kernel
theorem sbd11_3_3 : ∀ q ∈ blkd11_3_3, subd11_3 q = true := by
  unfold blkd11_3_3
  exact List.forall_mem_cons.2 ⟨subd11_3_96, List.forall_mem_cons.2 ⟨subd11_3_97, List.forall_mem_cons.2 ⟨subd11_3_98, List.forall_mem_cons.2 ⟨subd11_3_99, List.forall_mem_cons.2 ⟨subd11_3_100, List.forall_mem_cons.2 ⟨subd11_3_101, List.forall_mem_cons.2 ⟨subd11_3_102, List.forall_mem_cons.2 ⟨subd11_3_103, List.forall_mem_cons.2 ⟨subd11_3_104, List.forall_mem_cons.2 ⟨subd11_3_105, List.forall_mem_cons.2 ⟨subd11_3_106, List.forall_mem_cons.2 ⟨subd11_3_107, List.forall_mem_cons.2 ⟨subd11_3_108, List.forall_mem_cons.2 ⟨subd11_3_109, List.forall_mem_cons.2 ⟨subd11_3_110, List.forall_mem_cons.2 ⟨subd11_3_111, List.forall_mem_cons.2 ⟨subd11_3_112, List.forall_mem_cons.2 ⟨subd11_3_113, List.forall_mem_cons.2 ⟨subd11_3_114, List.forall_mem_cons.2 ⟨subd11_3_115, List.forall_mem_cons.2 ⟨subd11_3_116, List.forall_mem_cons.2 ⟨subd11_3_117, List.forall_mem_cons.2 ⟨subd11_3_118, List.forall_mem_cons.2 ⟨subd11_3_119, List.forall_mem_cons.2 ⟨subd11_3_120, List.forall_mem_cons.2 ⟨subd11_3_121, List.forall_mem_cons.2 ⟨subd11_3_122, List.forall_mem_cons.2 ⟨subd11_3_123, List.forall_mem_cons.2 ⟨subd11_3_124, List.forall_mem_cons.2 ⟨subd11_3_125, List.forall_mem_cons.2 ⟨subd11_3_126, List.forall_mem_cons.2 ⟨subd11_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_128 : subd11_3 [0, -1, -3] = true := by decide +kernel
theorem subd11_3_129 : subd11_3 [0, -1, -2] = true := by decide +kernel
theorem subd11_3_130 : subd11_3 [0, -1, -1] = true := by decide +kernel
theorem subd11_3_131 : subd11_3 [0, -1, 0] = true := by decide +kernel
theorem subd11_3_132 : subd11_3 [0, -1, 1] = true := by decide +kernel
theorem subd11_3_133 : subd11_3 [0, -1, 2] = true := by decide +kernel
theorem subd11_3_134 : subd11_3 [0, -1, 3] = true := by decide +kernel
theorem subd11_3_135 : subd11_3 [0, -1, 4] = true := by decide +kernel
theorem subd11_3_136 : subd11_3 [0, -1, 5] = true := by decide +kernel
theorem subd11_3_137 : subd11_3 [0, -1, 6] = true := by decide +kernel
theorem subd11_3_138 : subd11_3 [0, -1, 7] = true := by decide +kernel
theorem subd11_3_139 : subd11_3 [0, 0, -8] = true := by decide +kernel
theorem subd11_3_140 : subd11_3 [0, 0, -7] = true := by decide +kernel
theorem subd11_3_141 : subd11_3 [0, 0, -6] = true := by decide +kernel
theorem subd11_3_142 : subd11_3 [0, 0, -5] = true := by decide +kernel
theorem subd11_3_143 : subd11_3 [0, 0, -4] = true := by decide +kernel
theorem subd11_3_144 : subd11_3 [0, 0, -3] = true := by decide +kernel
theorem subd11_3_145 : subd11_3 [0, 0, -2] = true := by decide +kernel
theorem subd11_3_146 : subd11_3 [0, 0, -1] = true := by decide +kernel
theorem subd11_3_147 : subd11_3 [0, 0, 0] = true := by decide +kernel
theorem subd11_3_148 : subd11_3 [0, 0, 1] = true := by decide +kernel
theorem subd11_3_149 : subd11_3 [0, 0, 2] = true := by decide +kernel
theorem subd11_3_150 : subd11_3 [0, 0, 3] = true := by decide +kernel
theorem subd11_3_151 : subd11_3 [0, 0, 4] = true := by decide +kernel
theorem subd11_3_152 : subd11_3 [0, 0, 5] = true := by decide +kernel
theorem subd11_3_153 : subd11_3 [0, 0, 6] = true := by decide +kernel
theorem subd11_3_154 : subd11_3 [0, 0, 7] = true := by decide +kernel
theorem subd11_3_155 : subd11_3 [0, 1, -8] = true := by decide +kernel
theorem subd11_3_156 : subd11_3 [0, 1, -7] = true := by decide +kernel
theorem subd11_3_157 : subd11_3 [0, 1, -6] = true := by decide +kernel
theorem subd11_3_158 : subd11_3 [0, 1, -5] = true := by decide +kernel
theorem subd11_3_159 : subd11_3 [0, 1, -4] = true := by decide +kernel
theorem sbd11_3_4 : ∀ q ∈ blkd11_3_4, subd11_3 q = true := by
  unfold blkd11_3_4
  exact List.forall_mem_cons.2 ⟨subd11_3_128, List.forall_mem_cons.2 ⟨subd11_3_129, List.forall_mem_cons.2 ⟨subd11_3_130, List.forall_mem_cons.2 ⟨subd11_3_131, List.forall_mem_cons.2 ⟨subd11_3_132, List.forall_mem_cons.2 ⟨subd11_3_133, List.forall_mem_cons.2 ⟨subd11_3_134, List.forall_mem_cons.2 ⟨subd11_3_135, List.forall_mem_cons.2 ⟨subd11_3_136, List.forall_mem_cons.2 ⟨subd11_3_137, List.forall_mem_cons.2 ⟨subd11_3_138, List.forall_mem_cons.2 ⟨subd11_3_139, List.forall_mem_cons.2 ⟨subd11_3_140, List.forall_mem_cons.2 ⟨subd11_3_141, List.forall_mem_cons.2 ⟨subd11_3_142, List.forall_mem_cons.2 ⟨subd11_3_143, List.forall_mem_cons.2 ⟨subd11_3_144, List.forall_mem_cons.2 ⟨subd11_3_145, List.forall_mem_cons.2 ⟨subd11_3_146, List.forall_mem_cons.2 ⟨subd11_3_147, List.forall_mem_cons.2 ⟨subd11_3_148, List.forall_mem_cons.2 ⟨subd11_3_149, List.forall_mem_cons.2 ⟨subd11_3_150, List.forall_mem_cons.2 ⟨subd11_3_151, List.forall_mem_cons.2 ⟨subd11_3_152, List.forall_mem_cons.2 ⟨subd11_3_153, List.forall_mem_cons.2 ⟨subd11_3_154, List.forall_mem_cons.2 ⟨subd11_3_155, List.forall_mem_cons.2 ⟨subd11_3_156, List.forall_mem_cons.2 ⟨subd11_3_157, List.forall_mem_cons.2 ⟨subd11_3_158, List.forall_mem_cons.2 ⟨subd11_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_160 : subd11_3 [0, 1, -3] = true := by decide +kernel
theorem subd11_3_161 : subd11_3 [0, 1, -2] = true := by decide +kernel
theorem subd11_3_162 : subd11_3 [0, 1, -1] = true := by decide +kernel
theorem subd11_3_163 : subd11_3 [0, 1, 0] = true := by decide +kernel
theorem subd11_3_164 : subd11_3 [0, 1, 1] = true := by decide +kernel
theorem subd11_3_165 : subd11_3 [0, 1, 2] = true := by decide +kernel
theorem subd11_3_166 : subd11_3 [0, 1, 3] = true := by decide +kernel
theorem subd11_3_167 : subd11_3 [0, 1, 4] = true := by decide +kernel
theorem subd11_3_168 : subd11_3 [0, 1, 5] = true := by decide +kernel
theorem subd11_3_169 : subd11_3 [0, 1, 6] = true := by decide +kernel
theorem subd11_3_170 : subd11_3 [0, 2, -7] = true := by decide +kernel
theorem subd11_3_171 : subd11_3 [0, 2, -6] = true := by decide +kernel
theorem subd11_3_172 : subd11_3 [0, 2, -5] = true := by decide +kernel
theorem subd11_3_173 : subd11_3 [0, 2, -4] = true := by decide +kernel
theorem subd11_3_174 : subd11_3 [0, 2, -3] = true := by decide +kernel
theorem subd11_3_175 : subd11_3 [0, 2, -2] = true := by decide +kernel
theorem subd11_3_176 : subd11_3 [0, 2, -1] = true := by decide +kernel
theorem subd11_3_177 : subd11_3 [0, 2, 0] = true := by decide +kernel
theorem subd11_3_178 : subd11_3 [0, 2, 1] = true := by decide +kernel
theorem subd11_3_179 : subd11_3 [0, 2, 2] = true := by decide +kernel
theorem subd11_3_180 : subd11_3 [0, 2, 3] = true := by decide +kernel
theorem subd11_3_181 : subd11_3 [0, 2, 4] = true := by decide +kernel
theorem subd11_3_182 : subd11_3 [0, 2, 5] = true := by decide +kernel
theorem subd11_3_183 : subd11_3 [0, 2, 6] = true := by decide +kernel
theorem subd11_3_184 : subd11_3 [0, 3] = true := by decide +kernel
theorem subd11_3_185 : subd11_3 [0, 4] = true := by decide +kernel
theorem subd11_3_186 : subd11_3 [0, 5] = true := by decide +kernel
theorem subd11_3_187 : subd11_3 [0, 6] = true := by decide +kernel
theorem subd11_3_188 : subd11_3 [1, -6] = true := by decide +kernel
theorem subd11_3_189 : subd11_3 [1, -5] = true := by decide +kernel
theorem subd11_3_190 : subd11_3 [1, -4] = true := by decide +kernel
theorem subd11_3_191 : subd11_3 [1, -3] = true := by decide +kernel
theorem sbd11_3_5 : ∀ q ∈ blkd11_3_5, subd11_3 q = true := by
  unfold blkd11_3_5
  exact List.forall_mem_cons.2 ⟨subd11_3_160, List.forall_mem_cons.2 ⟨subd11_3_161, List.forall_mem_cons.2 ⟨subd11_3_162, List.forall_mem_cons.2 ⟨subd11_3_163, List.forall_mem_cons.2 ⟨subd11_3_164, List.forall_mem_cons.2 ⟨subd11_3_165, List.forall_mem_cons.2 ⟨subd11_3_166, List.forall_mem_cons.2 ⟨subd11_3_167, List.forall_mem_cons.2 ⟨subd11_3_168, List.forall_mem_cons.2 ⟨subd11_3_169, List.forall_mem_cons.2 ⟨subd11_3_170, List.forall_mem_cons.2 ⟨subd11_3_171, List.forall_mem_cons.2 ⟨subd11_3_172, List.forall_mem_cons.2 ⟨subd11_3_173, List.forall_mem_cons.2 ⟨subd11_3_174, List.forall_mem_cons.2 ⟨subd11_3_175, List.forall_mem_cons.2 ⟨subd11_3_176, List.forall_mem_cons.2 ⟨subd11_3_177, List.forall_mem_cons.2 ⟨subd11_3_178, List.forall_mem_cons.2 ⟨subd11_3_179, List.forall_mem_cons.2 ⟨subd11_3_180, List.forall_mem_cons.2 ⟨subd11_3_181, List.forall_mem_cons.2 ⟨subd11_3_182, List.forall_mem_cons.2 ⟨subd11_3_183, List.forall_mem_cons.2 ⟨subd11_3_184, List.forall_mem_cons.2 ⟨subd11_3_185, List.forall_mem_cons.2 ⟨subd11_3_186, List.forall_mem_cons.2 ⟨subd11_3_187, List.forall_mem_cons.2 ⟨subd11_3_188, List.forall_mem_cons.2 ⟨subd11_3_189, List.forall_mem_cons.2 ⟨subd11_3_190, List.forall_mem_cons.2 ⟨subd11_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_192 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_193 : subd11_3 [1, -1, -7] = true := by decide +kernel
theorem subd11_3_194 : subd11_3 [1, -1, -6] = true := by decide +kernel
theorem subd11_3_195 : subd11_3 [1, -1, -5] = true := by decide +kernel
theorem subd11_3_196 : subd11_3 [1, -1, -4] = true := by decide +kernel
theorem subd11_3_197 : subd11_3 [1, -1, -3] = true := by decide +kernel
theorem subd11_3_198 : subd11_3 [1, -1, -2] = true := by decide +kernel
theorem subd11_3_199 : subd11_3 [1, -1, -1] = true := by decide +kernel
theorem subd11_3_200 : subd11_3 [1, -1, 0] = true := by decide +kernel
theorem subd11_3_201 : subd11_3 [1, -1, 1] = true := by decide +kernel
theorem subd11_3_202 : subd11_3 [1, -1, 2] = true := by decide +kernel
theorem subd11_3_203 : subd11_3 [1, -1, 3] = true := by decide +kernel
theorem subd11_3_204 : subd11_3 [1, -1, 4] = true := by decide +kernel
theorem subd11_3_205 : subd11_3 [1, -1, 5] = true := by decide +kernel
theorem subd11_3_206 : subd11_3 [1, -1, 6] = true := by decide +kernel
theorem subd11_3_207 : subd11_3 [1, 0, -7] = true := by decide +kernel
theorem subd11_3_208 : subd11_3 [1, 0, -6] = true := by decide +kernel
theorem subd11_3_209 : subd11_3 [1, 0, -5] = true := by decide +kernel
theorem subd11_3_210 : subd11_3 [1, 0, -4] = true := by decide +kernel
theorem subd11_3_211 : subd11_3 [1, 0, -3] = true := by decide +kernel
theorem subd11_3_212 : subd11_3 [1, 0, -2] = true := by decide +kernel
theorem subd11_3_213 : subd11_3 [1, 0, -1] = true := by decide +kernel
theorem subd11_3_214 : subd11_3 [1, 0, 0] = true := by decide +kernel
theorem subd11_3_215 : subd11_3 [1, 0, 1] = true := by decide +kernel
theorem subd11_3_216 : subd11_3 [1, 0, 2] = true := by decide +kernel
theorem subd11_3_217 : subd11_3 [1, 0, 3] = true := by decide +kernel
theorem subd11_3_218 : subd11_3 [1, 0, 4] = true := by decide +kernel
theorem subd11_3_219 : subd11_3 [1, 0, 5] = true := by decide +kernel
theorem subd11_3_220 : subd11_3 [1, 0, 6] = true := by decide +kernel
theorem subd11_3_221 : subd11_3 [1, 0, 7] = true := by decide +kernel
theorem subd11_3_222 : subd11_3 [1, 1, -7] = true := by decide +kernel
theorem subd11_3_223 : subd11_3 [1, 1, -6] = true := by decide +kernel
theorem sbd11_3_6 : ∀ q ∈ blkd11_3_6, subd11_3 q = true := by
  unfold blkd11_3_6
  exact List.forall_mem_cons.2 ⟨subd11_3_192, List.forall_mem_cons.2 ⟨subd11_3_193, List.forall_mem_cons.2 ⟨subd11_3_194, List.forall_mem_cons.2 ⟨subd11_3_195, List.forall_mem_cons.2 ⟨subd11_3_196, List.forall_mem_cons.2 ⟨subd11_3_197, List.forall_mem_cons.2 ⟨subd11_3_198, List.forall_mem_cons.2 ⟨subd11_3_199, List.forall_mem_cons.2 ⟨subd11_3_200, List.forall_mem_cons.2 ⟨subd11_3_201, List.forall_mem_cons.2 ⟨subd11_3_202, List.forall_mem_cons.2 ⟨subd11_3_203, List.forall_mem_cons.2 ⟨subd11_3_204, List.forall_mem_cons.2 ⟨subd11_3_205, List.forall_mem_cons.2 ⟨subd11_3_206, List.forall_mem_cons.2 ⟨subd11_3_207, List.forall_mem_cons.2 ⟨subd11_3_208, List.forall_mem_cons.2 ⟨subd11_3_209, List.forall_mem_cons.2 ⟨subd11_3_210, List.forall_mem_cons.2 ⟨subd11_3_211, List.forall_mem_cons.2 ⟨subd11_3_212, List.forall_mem_cons.2 ⟨subd11_3_213, List.forall_mem_cons.2 ⟨subd11_3_214, List.forall_mem_cons.2 ⟨subd11_3_215, List.forall_mem_cons.2 ⟨subd11_3_216, List.forall_mem_cons.2 ⟨subd11_3_217, List.forall_mem_cons.2 ⟨subd11_3_218, List.forall_mem_cons.2 ⟨subd11_3_219, List.forall_mem_cons.2 ⟨subd11_3_220, List.forall_mem_cons.2 ⟨subd11_3_221, List.forall_mem_cons.2 ⟨subd11_3_222, List.forall_mem_cons.2 ⟨subd11_3_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_224 : subd11_3 [1, 1, -5] = true := by decide +kernel
theorem subd11_3_225 : subd11_3 [1, 1, -4] = true := by decide +kernel
theorem subd11_3_226 : subd11_3 [1, 1, -3] = true := by decide +kernel
theorem subd11_3_227 : subd11_3 [1, 1, -2] = true := by decide +kernel
theorem subd11_3_228 : subd11_3 [1, 1, -1] = true := by decide +kernel
theorem subd11_3_229 : subd11_3 [1, 1, 0] = true := by decide +kernel
theorem subd11_3_230 : subd11_3 [1, 1, 1] = true := by decide +kernel
theorem subd11_3_231 : subd11_3 [1, 1, 2] = true := by decide +kernel
theorem subd11_3_232 : subd11_3 [1, 1, 3] = true := by decide +kernel
theorem subd11_3_233 : subd11_3 [1, 1, 4] = true := by decide +kernel
theorem subd11_3_234 : subd11_3 [1, 1, 5] = true := by decide +kernel
theorem subd11_3_235 : subd11_3 [1, 1, 6] = true := by decide +kernel
theorem subd11_3_236 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_237 : subd11_3 [1, 3] = true := by decide +kernel
theorem subd11_3_238 : subd11_3 [1, 4] = true := by decide +kernel
theorem subd11_3_239 : subd11_3 [1, 5] = true := by decide +kernel
theorem subd11_3_240 : subd11_3 [1, 6] = true := by decide +kernel
theorem subd11_3_241 : subd11_3 [2, -6] = true := by decide +kernel
theorem subd11_3_242 : subd11_3 [2, -5] = true := by decide +kernel
theorem subd11_3_243 : subd11_3 [2, -4] = true := by decide +kernel
theorem subd11_3_244 : subd11_3 [2, -3] = true := by decide +kernel
theorem subd11_3_245 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_246 : subd11_3 [2, -1] = true := by decide +kernel
theorem subd11_3_247 : subd11_3 [2, 0, -7] = true := by decide +kernel
theorem subd11_3_248 : subd11_3 [2, 0, -6] = true := by decide +kernel
theorem subd11_3_249 : subd11_3 [2, 0, -5] = true := by decide +kernel
theorem subd11_3_250 : subd11_3 [2, 0, -4] = true := by decide +kernel
theorem subd11_3_251 : subd11_3 [2, 0, -3] = true := by decide +kernel
theorem subd11_3_252 : subd11_3 [2, 0, -2] = true := by decide +kernel
theorem subd11_3_253 : subd11_3 [2, 0, -1] = true := by decide +kernel
theorem subd11_3_254 : subd11_3 [2, 0, 0] = true := by decide +kernel
theorem subd11_3_255 : subd11_3 [2, 0, 1] = true := by decide +kernel
theorem sbd11_3_7 : ∀ q ∈ blkd11_3_7, subd11_3 q = true := by
  unfold blkd11_3_7
  exact List.forall_mem_cons.2 ⟨subd11_3_224, List.forall_mem_cons.2 ⟨subd11_3_225, List.forall_mem_cons.2 ⟨subd11_3_226, List.forall_mem_cons.2 ⟨subd11_3_227, List.forall_mem_cons.2 ⟨subd11_3_228, List.forall_mem_cons.2 ⟨subd11_3_229, List.forall_mem_cons.2 ⟨subd11_3_230, List.forall_mem_cons.2 ⟨subd11_3_231, List.forall_mem_cons.2 ⟨subd11_3_232, List.forall_mem_cons.2 ⟨subd11_3_233, List.forall_mem_cons.2 ⟨subd11_3_234, List.forall_mem_cons.2 ⟨subd11_3_235, List.forall_mem_cons.2 ⟨subd11_3_236, List.forall_mem_cons.2 ⟨subd11_3_237, List.forall_mem_cons.2 ⟨subd11_3_238, List.forall_mem_cons.2 ⟨subd11_3_239, List.forall_mem_cons.2 ⟨subd11_3_240, List.forall_mem_cons.2 ⟨subd11_3_241, List.forall_mem_cons.2 ⟨subd11_3_242, List.forall_mem_cons.2 ⟨subd11_3_243, List.forall_mem_cons.2 ⟨subd11_3_244, List.forall_mem_cons.2 ⟨subd11_3_245, List.forall_mem_cons.2 ⟨subd11_3_246, List.forall_mem_cons.2 ⟨subd11_3_247, List.forall_mem_cons.2 ⟨subd11_3_248, List.forall_mem_cons.2 ⟨subd11_3_249, List.forall_mem_cons.2 ⟨subd11_3_250, List.forall_mem_cons.2 ⟨subd11_3_251, List.forall_mem_cons.2 ⟨subd11_3_252, List.forall_mem_cons.2 ⟨subd11_3_253, List.forall_mem_cons.2 ⟨subd11_3_254, List.forall_mem_cons.2 ⟨subd11_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
