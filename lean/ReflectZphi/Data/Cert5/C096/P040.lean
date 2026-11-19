import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_0 : subd10_1 [-3, -2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-3, -1] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-3, 0] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-3, 1] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-3, 2] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-2, -4] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-2, -3] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-2, -2] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-2, -1] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-2, 0] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-2, 1] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-2, 2] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-2, 3] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-1, -4] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [-1, -1, -7] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [-1, -1, -6] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [-1, -1, -5] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [-1, -1, -4] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [-1, -1, -3] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [-1, -1, -2] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [-1, -1, -1] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [-1, -1, 0] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [-1, -1, 1] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [-1, -1, 2] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [-1, -1, 3] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [-1, -1, 4] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [-1, -1, 5] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [-1, -1, 6] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [-1, 0, -7] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [-1, 0, -6] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_32 : subd10_1 [-1, 0, -5] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [-1, 0, -4] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [-1, 0, -3] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [-1, 0, -2] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [-1, 0, -1] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [-1, 0, 0] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [-1, 0, 1] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [-1, 0, 2] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [-1, 0, 3] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [-1, 0, 4] = true := by decide +kernel
theorem subd10_1_42 : subd10_1 [-1, 0, 5] = true := by decide +kernel
theorem subd10_1_43 : subd10_1 [-1, 0, 6] = true := by decide +kernel
theorem subd10_1_44 : subd10_1 [-1, 1, -7] = true := by decide +kernel
theorem subd10_1_45 : subd10_1 [-1, 1, -6] = true := by decide +kernel
theorem subd10_1_46 : subd10_1 [-1, 1, -5] = true := by decide +kernel
theorem subd10_1_47 : subd10_1 [-1, 1, -4] = true := by decide +kernel
theorem subd10_1_48 : subd10_1 [-1, 1, -3] = true := by decide +kernel
theorem subd10_1_49 : subd10_1 [-1, 1, -2] = true := by decide +kernel
theorem subd10_1_50 : subd10_1 [-1, 1, -1] = true := by decide +kernel
theorem subd10_1_51 : subd10_1 [-1, 1, 0] = true := by decide +kernel
theorem subd10_1_52 : subd10_1 [-1, 1, 1] = true := by decide +kernel
theorem subd10_1_53 : subd10_1 [-1, 1, 2] = true := by decide +kernel
theorem subd10_1_54 : subd10_1 [-1, 1, 3] = true := by decide +kernel
theorem subd10_1_55 : subd10_1 [-1, 1, 4] = true := by decide +kernel
theorem subd10_1_56 : subd10_1 [-1, 1, 5] = true := by decide +kernel
theorem subd10_1_57 : subd10_1 [-1, 1, 6] = true := by decide +kernel
theorem subd10_1_58 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_59 : subd10_1 [-1, 3] = true := by decide +kernel
theorem subd10_1_60 : subd10_1 [-1, 4] = true := by decide +kernel
theorem subd10_1_61 : subd10_1 [0, -5] = true := by decide +kernel
theorem subd10_1_62 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_63 : subd10_1 [0, -3] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_cons.2 ⟨subd10_1_42, List.forall_mem_cons.2 ⟨subd10_1_43, List.forall_mem_cons.2 ⟨subd10_1_44, List.forall_mem_cons.2 ⟨subd10_1_45, List.forall_mem_cons.2 ⟨subd10_1_46, List.forall_mem_cons.2 ⟨subd10_1_47, List.forall_mem_cons.2 ⟨subd10_1_48, List.forall_mem_cons.2 ⟨subd10_1_49, List.forall_mem_cons.2 ⟨subd10_1_50, List.forall_mem_cons.2 ⟨subd10_1_51, List.forall_mem_cons.2 ⟨subd10_1_52, List.forall_mem_cons.2 ⟨subd10_1_53, List.forall_mem_cons.2 ⟨subd10_1_54, List.forall_mem_cons.2 ⟨subd10_1_55, List.forall_mem_cons.2 ⟨subd10_1_56, List.forall_mem_cons.2 ⟨subd10_1_57, List.forall_mem_cons.2 ⟨subd10_1_58, List.forall_mem_cons.2 ⟨subd10_1_59, List.forall_mem_cons.2 ⟨subd10_1_60, List.forall_mem_cons.2 ⟨subd10_1_61, List.forall_mem_cons.2 ⟨subd10_1_62, List.forall_mem_cons.2 ⟨subd10_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_64 : subd10_1 [0, -2, -6] = true := by decide +kernel
theorem subd10_1_65 : subd10_1 [0, -2, -5] = true := by decide +kernel
theorem subd10_1_66 : subd10_1 [0, -2, -4] = true := by decide +kernel
theorem subd10_1_67 : subd10_1 [0, -2, -3] = true := by decide +kernel
theorem subd10_1_68 : subd10_1 [0, -2, -2] = true := by decide +kernel
theorem subd10_1_69 : subd10_1 [0, -2, -1] = true := by decide +kernel
theorem subd10_1_70 : subd10_1 [0, -2, 0] = true := by decide +kernel
theorem subd10_1_71 : subd10_1 [0, -2, 1] = true := by decide +kernel
theorem subd10_1_72 : subd10_1 [0, -2, 2] = true := by decide +kernel
theorem subd10_1_73 : subd10_1 [0, -2, 3] = true := by decide +kernel
theorem subd10_1_74 : subd10_1 [0, -2, 4] = true := by decide +kernel
theorem subd10_1_75 : subd10_1 [0, -2, 5] = true := by decide +kernel
theorem subd10_1_76 : subd10_1 [0, -2, 6] = true := by decide +kernel
theorem subd10_1_77 : subd10_1 [0, -1, -7] = true := by decide +kernel
theorem subd10_1_78 : subd10_1 [0, -1, -6] = true := by decide +kernel
theorem subd10_1_79 : subd10_1 [0, -1, -5] = true := by decide +kernel
theorem subd10_1_80 : subd10_1 [0, -1, -4] = true := by decide +kernel
theorem subd10_1_81 : subd10_1 [0, -1, -3] = true := by decide +kernel
theorem subd10_1_82 : subd10_1 [0, -1, -2] = true := by decide +kernel
theorem subd10_1_83 : subd10_1 [0, -1, -1] = true := by decide +kernel
theorem subd10_1_84 : subd10_1 [0, -1, 0] = true := by decide +kernel
theorem subd10_1_85 : subd10_1 [0, -1, 1] = true := by decide +kernel
theorem subd10_1_86 : subd10_1 [0, -1, 2] = true := by decide +kernel
theorem subd10_1_87 : subd10_1 [0, -1, 3] = true := by decide +kernel
theorem subd10_1_88 : subd10_1 [0, -1, 4] = true := by decide +kernel
theorem subd10_1_89 : subd10_1 [0, -1, 5] = true := by decide +kernel
theorem subd10_1_90 : subd10_1 [0, -1, 6] = true := by decide +kernel
theorem subd10_1_91 : subd10_1 [0, -1, 7] = true := by decide +kernel
theorem subd10_1_92 : subd10_1 [0, 0, -8] = true := by decide +kernel
theorem subd10_1_93 : subd10_1 [0, 0, -7] = true := by decide +kernel
theorem subd10_1_94 : subd10_1 [0, 0, -6] = true := by decide +kernel
theorem subd10_1_95 : subd10_1 [0, 0, -5] = true := by decide +kernel
theorem sbd10_1_2 : ∀ q ∈ blkd10_1_2, subd10_1 q = true := by
  unfold blkd10_1_2
  exact List.forall_mem_cons.2 ⟨subd10_1_64, List.forall_mem_cons.2 ⟨subd10_1_65, List.forall_mem_cons.2 ⟨subd10_1_66, List.forall_mem_cons.2 ⟨subd10_1_67, List.forall_mem_cons.2 ⟨subd10_1_68, List.forall_mem_cons.2 ⟨subd10_1_69, List.forall_mem_cons.2 ⟨subd10_1_70, List.forall_mem_cons.2 ⟨subd10_1_71, List.forall_mem_cons.2 ⟨subd10_1_72, List.forall_mem_cons.2 ⟨subd10_1_73, List.forall_mem_cons.2 ⟨subd10_1_74, List.forall_mem_cons.2 ⟨subd10_1_75, List.forall_mem_cons.2 ⟨subd10_1_76, List.forall_mem_cons.2 ⟨subd10_1_77, List.forall_mem_cons.2 ⟨subd10_1_78, List.forall_mem_cons.2 ⟨subd10_1_79, List.forall_mem_cons.2 ⟨subd10_1_80, List.forall_mem_cons.2 ⟨subd10_1_81, List.forall_mem_cons.2 ⟨subd10_1_82, List.forall_mem_cons.2 ⟨subd10_1_83, List.forall_mem_cons.2 ⟨subd10_1_84, List.forall_mem_cons.2 ⟨subd10_1_85, List.forall_mem_cons.2 ⟨subd10_1_86, List.forall_mem_cons.2 ⟨subd10_1_87, List.forall_mem_cons.2 ⟨subd10_1_88, List.forall_mem_cons.2 ⟨subd10_1_89, List.forall_mem_cons.2 ⟨subd10_1_90, List.forall_mem_cons.2 ⟨subd10_1_91, List.forall_mem_cons.2 ⟨subd10_1_92, List.forall_mem_cons.2 ⟨subd10_1_93, List.forall_mem_cons.2 ⟨subd10_1_94, List.forall_mem_cons.2 ⟨subd10_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_96 : subd10_1 [0, 0, -4] = true := by decide +kernel
theorem subd10_1_97 : subd10_1 [0, 0, -3] = true := by decide +kernel
theorem subd10_1_98 : subd10_1 [0, 0, -2] = true := by decide +kernel
theorem subd10_1_99 : subd10_1 [0, 0, -1] = true := by decide +kernel
theorem subd10_1_100 : subd10_1 [0, 0, 0] = true := by decide +kernel
theorem subd10_1_101 : subd10_1 [0, 0, 1] = true := by decide +kernel
theorem subd10_1_102 : subd10_1 [0, 0, 2] = true := by decide +kernel
theorem subd10_1_103 : subd10_1 [0, 0, 3] = true := by decide +kernel
theorem subd10_1_104 : subd10_1 [0, 0, 4] = true := by decide +kernel
theorem subd10_1_105 : subd10_1 [0, 0, 5] = true := by decide +kernel
theorem subd10_1_106 : subd10_1 [0, 0, 6] = true := by decide +kernel
theorem subd10_1_107 : subd10_1 [0, 0, 7] = true := by decide +kernel
theorem subd10_1_108 : subd10_1 [0, 1, -8] = true := by decide +kernel
theorem subd10_1_109 : subd10_1 [0, 1, -7] = true := by decide +kernel
theorem subd10_1_110 : subd10_1 [0, 1, -6] = true := by decide +kernel
theorem subd10_1_111 : subd10_1 [0, 1, -5] = true := by decide +kernel
theorem subd10_1_112 : subd10_1 [0, 1, -4] = true := by decide +kernel
theorem subd10_1_113 : subd10_1 [0, 1, -3] = true := by decide +kernel
theorem subd10_1_114 : subd10_1 [0, 1, -2] = true := by decide +kernel
theorem subd10_1_115 : subd10_1 [0, 1, -1] = true := by decide +kernel
theorem subd10_1_116 : subd10_1 [0, 1, 0] = true := by decide +kernel
theorem subd10_1_117 : subd10_1 [0, 1, 1] = true := by decide +kernel
theorem subd10_1_118 : subd10_1 [0, 1, 2] = true := by decide +kernel
theorem subd10_1_119 : subd10_1 [0, 1, 3] = true := by decide +kernel
theorem subd10_1_120 : subd10_1 [0, 1, 4] = true := by decide +kernel
theorem subd10_1_121 : subd10_1 [0, 1, 5] = true := by decide +kernel
theorem subd10_1_122 : subd10_1 [0, 1, 6] = true := by decide +kernel
theorem subd10_1_123 : subd10_1 [0, 2, -7] = true := by decide +kernel
theorem subd10_1_124 : subd10_1 [0, 2, -6] = true := by decide +kernel
theorem subd10_1_125 : subd10_1 [0, 2, -5] = true := by decide +kernel
theorem subd10_1_126 : subd10_1 [0, 2, -4] = true := by decide +kernel
theorem subd10_1_127 : subd10_1 [0, 2, -3] = true := by decide +kernel
theorem sbd10_1_3 : ∀ q ∈ blkd10_1_3, subd10_1 q = true := by
  unfold blkd10_1_3
  exact List.forall_mem_cons.2 ⟨subd10_1_96, List.forall_mem_cons.2 ⟨subd10_1_97, List.forall_mem_cons.2 ⟨subd10_1_98, List.forall_mem_cons.2 ⟨subd10_1_99, List.forall_mem_cons.2 ⟨subd10_1_100, List.forall_mem_cons.2 ⟨subd10_1_101, List.forall_mem_cons.2 ⟨subd10_1_102, List.forall_mem_cons.2 ⟨subd10_1_103, List.forall_mem_cons.2 ⟨subd10_1_104, List.forall_mem_cons.2 ⟨subd10_1_105, List.forall_mem_cons.2 ⟨subd10_1_106, List.forall_mem_cons.2 ⟨subd10_1_107, List.forall_mem_cons.2 ⟨subd10_1_108, List.forall_mem_cons.2 ⟨subd10_1_109, List.forall_mem_cons.2 ⟨subd10_1_110, List.forall_mem_cons.2 ⟨subd10_1_111, List.forall_mem_cons.2 ⟨subd10_1_112, List.forall_mem_cons.2 ⟨subd10_1_113, List.forall_mem_cons.2 ⟨subd10_1_114, List.forall_mem_cons.2 ⟨subd10_1_115, List.forall_mem_cons.2 ⟨subd10_1_116, List.forall_mem_cons.2 ⟨subd10_1_117, List.forall_mem_cons.2 ⟨subd10_1_118, List.forall_mem_cons.2 ⟨subd10_1_119, List.forall_mem_cons.2 ⟨subd10_1_120, List.forall_mem_cons.2 ⟨subd10_1_121, List.forall_mem_cons.2 ⟨subd10_1_122, List.forall_mem_cons.2 ⟨subd10_1_123, List.forall_mem_cons.2 ⟨subd10_1_124, List.forall_mem_cons.2 ⟨subd10_1_125, List.forall_mem_cons.2 ⟨subd10_1_126, List.forall_mem_cons.2 ⟨subd10_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_128 : subd10_1 [0, 2, -2] = true := by decide +kernel
theorem subd10_1_129 : subd10_1 [0, 2, -1] = true := by decide +kernel
theorem subd10_1_130 : subd10_1 [0, 2, 0] = true := by decide +kernel
theorem subd10_1_131 : subd10_1 [0, 2, 1] = true := by decide +kernel
theorem subd10_1_132 : subd10_1 [0, 2, 2] = true := by decide +kernel
theorem subd10_1_133 : subd10_1 [0, 2, 3] = true := by decide +kernel
theorem subd10_1_134 : subd10_1 [0, 2, 4] = true := by decide +kernel
theorem subd10_1_135 : subd10_1 [0, 2, 5] = true := by decide +kernel
theorem subd10_1_136 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_137 : subd10_1 [0, 4] = true := by decide +kernel
theorem subd10_1_138 : subd10_1 [1, -5] = true := by decide +kernel
theorem subd10_1_139 : subd10_1 [1, -4] = true := by decide +kernel
theorem subd10_1_140 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_141 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_142 : subd10_1 [1, -1, -7] = true := by decide +kernel
theorem subd10_1_143 : subd10_1 [1, -1, -6] = true := by decide +kernel
theorem subd10_1_144 : subd10_1 [1, -1, -5] = true := by decide +kernel
theorem subd10_1_145 : subd10_1 [1, -1, -4] = true := by decide +kernel
theorem subd10_1_146 : subd10_1 [1, -1, -3] = true := by decide +kernel
theorem subd10_1_147 : subd10_1 [1, -1, -2] = true := by decide +kernel
theorem subd10_1_148 : subd10_1 [1, -1, -1] = true := by decide +kernel
theorem subd10_1_149 : subd10_1 [1, -1, 0] = true := by decide +kernel
theorem subd10_1_150 : subd10_1 [1, -1, 1] = true := by decide +kernel
theorem subd10_1_151 : subd10_1 [1, -1, 2] = true := by decide +kernel
theorem subd10_1_152 : subd10_1 [1, -1, 3] = true := by decide +kernel
theorem subd10_1_153 : subd10_1 [1, -1, 4] = true := by decide +kernel
theorem subd10_1_154 : subd10_1 [1, -1, 5] = true := by decide +kernel
theorem subd10_1_155 : subd10_1 [1, -1, 6] = true := by decide +kernel
theorem subd10_1_156 : subd10_1 [1, 0, -7] = true := by decide +kernel
theorem subd10_1_157 : subd10_1 [1, 0, -6] = true := by decide +kernel
theorem subd10_1_158 : subd10_1 [1, 0, -5] = true := by decide +kernel
theorem subd10_1_159 : subd10_1 [1, 0, -4] = true := by decide +kernel
theorem sbd10_1_4 : ∀ q ∈ blkd10_1_4, subd10_1 q = true := by
  unfold blkd10_1_4
  exact List.forall_mem_cons.2 ⟨subd10_1_128, List.forall_mem_cons.2 ⟨subd10_1_129, List.forall_mem_cons.2 ⟨subd10_1_130, List.forall_mem_cons.2 ⟨subd10_1_131, List.forall_mem_cons.2 ⟨subd10_1_132, List.forall_mem_cons.2 ⟨subd10_1_133, List.forall_mem_cons.2 ⟨subd10_1_134, List.forall_mem_cons.2 ⟨subd10_1_135, List.forall_mem_cons.2 ⟨subd10_1_136, List.forall_mem_cons.2 ⟨subd10_1_137, List.forall_mem_cons.2 ⟨subd10_1_138, List.forall_mem_cons.2 ⟨subd10_1_139, List.forall_mem_cons.2 ⟨subd10_1_140, List.forall_mem_cons.2 ⟨subd10_1_141, List.forall_mem_cons.2 ⟨subd10_1_142, List.forall_mem_cons.2 ⟨subd10_1_143, List.forall_mem_cons.2 ⟨subd10_1_144, List.forall_mem_cons.2 ⟨subd10_1_145, List.forall_mem_cons.2 ⟨subd10_1_146, List.forall_mem_cons.2 ⟨subd10_1_147, List.forall_mem_cons.2 ⟨subd10_1_148, List.forall_mem_cons.2 ⟨subd10_1_149, List.forall_mem_cons.2 ⟨subd10_1_150, List.forall_mem_cons.2 ⟨subd10_1_151, List.forall_mem_cons.2 ⟨subd10_1_152, List.forall_mem_cons.2 ⟨subd10_1_153, List.forall_mem_cons.2 ⟨subd10_1_154, List.forall_mem_cons.2 ⟨subd10_1_155, List.forall_mem_cons.2 ⟨subd10_1_156, List.forall_mem_cons.2 ⟨subd10_1_157, List.forall_mem_cons.2 ⟨subd10_1_158, List.forall_mem_cons.2 ⟨subd10_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_160 : subd10_1 [1, 0, -3] = true := by decide +kernel
theorem subd10_1_161 : subd10_1 [1, 0, -2] = true := by decide +kernel
theorem subd10_1_162 : subd10_1 [1, 0, -1] = true := by decide +kernel
theorem subd10_1_163 : subd10_1 [1, 0, 0] = true := by decide +kernel
theorem subd10_1_164 : subd10_1 [1, 0, 1] = true := by decide +kernel
theorem subd10_1_165 : subd10_1 [1, 0, 2] = true := by decide +kernel
theorem subd10_1_166 : subd10_1 [1, 0, 3] = true := by decide +kernel
theorem subd10_1_167 : subd10_1 [1, 0, 4] = true := by decide +kernel
theorem subd10_1_168 : subd10_1 [1, 0, 5] = true := by decide +kernel
theorem subd10_1_169 : subd10_1 [1, 0, 6] = true := by decide +kernel
theorem subd10_1_170 : subd10_1 [1, 1, -7] = true := by decide +kernel
theorem subd10_1_171 : subd10_1 [1, 1, -6] = true := by decide +kernel
theorem subd10_1_172 : subd10_1 [1, 1, -5] = true := by decide +kernel
theorem subd10_1_173 : subd10_1 [1, 1, -4] = true := by decide +kernel
theorem subd10_1_174 : subd10_1 [1, 1, -3] = true := by decide +kernel
theorem subd10_1_175 : subd10_1 [1, 1, -2] = true := by decide +kernel
theorem subd10_1_176 : subd10_1 [1, 1, -1] = true := by decide +kernel
theorem subd10_1_177 : subd10_1 [1, 1, 0] = true := by decide +kernel
theorem subd10_1_178 : subd10_1 [1, 1, 1] = true := by decide +kernel
theorem subd10_1_179 : subd10_1 [1, 1, 2] = true := by decide +kernel
theorem subd10_1_180 : subd10_1 [1, 1, 3] = true := by decide +kernel
theorem subd10_1_181 : subd10_1 [1, 1, 4] = true := by decide +kernel
theorem subd10_1_182 : subd10_1 [1, 1, 5] = true := by decide +kernel
theorem subd10_1_183 : subd10_1 [1, 1, 6] = true := by decide +kernel
theorem subd10_1_184 : subd10_1 [1, 2] = true := by decide +kernel
theorem subd10_1_185 : subd10_1 [1, 3] = true := by decide +kernel
theorem subd10_1_186 : subd10_1 [2, -4] = true := by decide +kernel
theorem subd10_1_187 : subd10_1 [2, -3] = true := by decide +kernel
theorem subd10_1_188 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_189 : subd10_1 [2, -1] = true := by decide +kernel
theorem subd10_1_190 : subd10_1 [2, 0] = true := by decide +kernel
theorem subd10_1_191 : subd10_1 [2, 1] = true := by decide +kernel
theorem sbd10_1_5 : ∀ q ∈ blkd10_1_5, subd10_1 q = true := by
  unfold blkd10_1_5
  exact List.forall_mem_cons.2 ⟨subd10_1_160, List.forall_mem_cons.2 ⟨subd10_1_161, List.forall_mem_cons.2 ⟨subd10_1_162, List.forall_mem_cons.2 ⟨subd10_1_163, List.forall_mem_cons.2 ⟨subd10_1_164, List.forall_mem_cons.2 ⟨subd10_1_165, List.forall_mem_cons.2 ⟨subd10_1_166, List.forall_mem_cons.2 ⟨subd10_1_167, List.forall_mem_cons.2 ⟨subd10_1_168, List.forall_mem_cons.2 ⟨subd10_1_169, List.forall_mem_cons.2 ⟨subd10_1_170, List.forall_mem_cons.2 ⟨subd10_1_171, List.forall_mem_cons.2 ⟨subd10_1_172, List.forall_mem_cons.2 ⟨subd10_1_173, List.forall_mem_cons.2 ⟨subd10_1_174, List.forall_mem_cons.2 ⟨subd10_1_175, List.forall_mem_cons.2 ⟨subd10_1_176, List.forall_mem_cons.2 ⟨subd10_1_177, List.forall_mem_cons.2 ⟨subd10_1_178, List.forall_mem_cons.2 ⟨subd10_1_179, List.forall_mem_cons.2 ⟨subd10_1_180, List.forall_mem_cons.2 ⟨subd10_1_181, List.forall_mem_cons.2 ⟨subd10_1_182, List.forall_mem_cons.2 ⟨subd10_1_183, List.forall_mem_cons.2 ⟨subd10_1_184, List.forall_mem_cons.2 ⟨subd10_1_185, List.forall_mem_cons.2 ⟨subd10_1_186, List.forall_mem_cons.2 ⟨subd10_1_187, List.forall_mem_cons.2 ⟨subd10_1_188, List.forall_mem_cons.2 ⟨subd10_1_189, List.forall_mem_cons.2 ⟨subd10_1_190, List.forall_mem_cons.2 ⟨subd10_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_192 : subd10_1 [2, 2] = true := by decide +kernel
theorem subd10_1_193 : subd10_1 [2, 3] = true := by decide +kernel
theorem subd10_1_194 : subd10_1 [3, -3] = true := by decide +kernel
theorem subd10_1_195 : subd10_1 [3, -2] = true := by decide +kernel
theorem subd10_1_196 : subd10_1 [3, -1] = true := by decide +kernel
theorem subd10_1_197 : subd10_1 [3, 0] = true := by decide +kernel
theorem subd10_1_198 : subd10_1 [3, 1] = true := by decide +kernel
theorem sbd10_1_6 : ∀ q ∈ blkd10_1_6, subd10_1 q = true := by
  unfold blkd10_1_6
  exact List.forall_mem_cons.2 ⟨subd10_1_192, List.forall_mem_cons.2 ⟨subd10_1_193, List.forall_mem_cons.2 ⟨subd10_1_194, List.forall_mem_cons.2 ⟨subd10_1_195, List.forall_mem_cons.2 ⟨subd10_1_196, List.forall_mem_cons.2 ⟨subd10_1_197, List.forall_mem_cons.2 ⟨subd10_1_198, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-3, -2] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-3, -1] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-3, 0] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-3, 1] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-2, -3] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-2, -2, -8] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-2, -2, -7] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-2, -2, -6] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [-2, -2, -5] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [-2, -2, -4] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [-2, -2, -3] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [-2, -2, -2] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [-2, -2, -1] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [-2, -2, 0] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [-2, -2, 1] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [-2, -2, 2] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [-2, -2, 3] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [-2, -2, 4] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [-2, -2, 5] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [-2, -1, -10] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [-2, -1, -9] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [-2, -1, -8] = true := by decide +kernel
theorem subd10_2_22 : subd10_2 [-2, -1, -7] = true := by decide +kernel
theorem subd10_2_23 : subd10_2 [-2, -1, -6] = true := by decide +kernel
theorem subd10_2_24 : subd10_2 [-2, -1, -5] = true := by decide +kernel
theorem subd10_2_25 : subd10_2 [-2, -1, -4] = true := by decide +kernel
theorem subd10_2_26 : subd10_2 [-2, -1, -3] = true := by decide +kernel
theorem subd10_2_27 : subd10_2 [-2, -1, -2] = true := by decide +kernel
theorem subd10_2_28 : subd10_2 [-2, -1, -1] = true := by decide +kernel
theorem subd10_2_29 : subd10_2 [-2, -1, 0] = true := by decide +kernel
theorem subd10_2_30 : subd10_2 [-2, -1, 1] = true := by decide +kernel
theorem subd10_2_31 : subd10_2 [-2, -1, 2] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_cons.2 ⟨subd10_2_22, List.forall_mem_cons.2 ⟨subd10_2_23, List.forall_mem_cons.2 ⟨subd10_2_24, List.forall_mem_cons.2 ⟨subd10_2_25, List.forall_mem_cons.2 ⟨subd10_2_26, List.forall_mem_cons.2 ⟨subd10_2_27, List.forall_mem_cons.2 ⟨subd10_2_28, List.forall_mem_cons.2 ⟨subd10_2_29, List.forall_mem_cons.2 ⟨subd10_2_30, List.forall_mem_cons.2 ⟨subd10_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_32 : subd10_2 [-2, -1, 3] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [-2, -1, 4] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [-2, -1, 5] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [-2, -1, 6] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [-2, -1, 7] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [-2, -1, 8] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [-2, 0, -11] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [-2, 0, -10] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [-2, 0, -9] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [-2, 0, -8] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [-2, 0, -7] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [-2, 0, -6] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [-2, 0, -5] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [-2, 0, -4] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [-2, 0, -3] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [-2, 0, -2] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [-2, 0, -1] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [-2, 0, 0] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [-2, 0, 1] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [-2, 0, 2] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [-2, 0, 3] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [-2, 0, 4] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [-2, 0, 5] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [-2, 0, 6] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [-2, 0, 7] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [-2, 0, 8] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [-2, 0, 9] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [-2, 1, -10] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [-2, 1, -9] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [-2, 1, -8] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [-2, 1, -7] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [-2, 1, -6] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [-2, 1, -5] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [-2, 1, -4] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [-2, 1, -3] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [-2, 1, -2] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [-2, 1, -1] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [-2, 1, 0] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [-2, 1, 1] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [-2, 1, 2] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [-2, 1, 3] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [-2, 1, 4] = true := by decide +kernel
theorem subd10_2_74 : subd10_2 [-2, 1, 5] = true := by decide +kernel
theorem subd10_2_75 : subd10_2 [-2, 1, 6] = true := by decide +kernel
theorem subd10_2_76 : subd10_2 [-2, 1, 7] = true := by decide +kernel
theorem subd10_2_77 : subd10_2 [-2, 1, 8] = true := by decide +kernel
theorem subd10_2_78 : subd10_2 [-2, 2, -8] = true := by decide +kernel
theorem subd10_2_79 : subd10_2 [-2, 2, -7] = true := by decide +kernel
theorem subd10_2_80 : subd10_2 [-2, 2, -6] = true := by decide +kernel
theorem subd10_2_81 : subd10_2 [-2, 2, -5] = true := by decide +kernel
theorem subd10_2_82 : subd10_2 [-2, 2, -4] = true := by decide +kernel
theorem subd10_2_83 : subd10_2 [-2, 2, -3] = true := by decide +kernel
theorem subd10_2_84 : subd10_2 [-2, 2, -2] = true := by decide +kernel
theorem subd10_2_85 : subd10_2 [-2, 2, -1] = true := by decide +kernel
theorem subd10_2_86 : subd10_2 [-2, 2, 0] = true := by decide +kernel
theorem subd10_2_87 : subd10_2 [-2, 2, 1] = true := by decide +kernel
theorem subd10_2_88 : subd10_2 [-2, 2, 2] = true := by decide +kernel
theorem subd10_2_89 : subd10_2 [-2, 2, 3] = true := by decide +kernel
theorem subd10_2_90 : subd10_2 [-2, 2, 4] = true := by decide +kernel
theorem subd10_2_91 : subd10_2 [-2, 2, 5] = true := by decide +kernel
theorem subd10_2_92 : subd10_2 [-2, 2, 6] = true := by decide +kernel
theorem subd10_2_93 : subd10_2 [-2, 2, 7] = true := by decide +kernel
theorem subd10_2_94 : subd10_2 [-1, -4] = true := by decide +kernel
theorem subd10_2_95 : subd10_2 [-1, -3] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_cons.2 ⟨subd10_2_74, List.forall_mem_cons.2 ⟨subd10_2_75, List.forall_mem_cons.2 ⟨subd10_2_76, List.forall_mem_cons.2 ⟨subd10_2_77, List.forall_mem_cons.2 ⟨subd10_2_78, List.forall_mem_cons.2 ⟨subd10_2_79, List.forall_mem_cons.2 ⟨subd10_2_80, List.forall_mem_cons.2 ⟨subd10_2_81, List.forall_mem_cons.2 ⟨subd10_2_82, List.forall_mem_cons.2 ⟨subd10_2_83, List.forall_mem_cons.2 ⟨subd10_2_84, List.forall_mem_cons.2 ⟨subd10_2_85, List.forall_mem_cons.2 ⟨subd10_2_86, List.forall_mem_cons.2 ⟨subd10_2_87, List.forall_mem_cons.2 ⟨subd10_2_88, List.forall_mem_cons.2 ⟨subd10_2_89, List.forall_mem_cons.2 ⟨subd10_2_90, List.forall_mem_cons.2 ⟨subd10_2_91, List.forall_mem_cons.2 ⟨subd10_2_92, List.forall_mem_cons.2 ⟨subd10_2_93, List.forall_mem_cons.2 ⟨subd10_2_94, List.forall_mem_cons.2 ⟨subd10_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
