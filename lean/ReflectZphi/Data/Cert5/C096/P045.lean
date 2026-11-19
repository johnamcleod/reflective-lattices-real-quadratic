import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-3, -2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-3, -1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-3, 0] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-3, 1] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-3, 2] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-3, 3] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-2, -4] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-2, -1, -8] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-2, -1, -7] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-2, -1, -6] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-2, -1, -5] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-2, -1, -4] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-2, -1, -3] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-2, -1, -2] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [-2, -1, -1] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [-2, -1, 0] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [-2, -1, 1] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [-2, -1, 2] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [-2, -1, 3] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [-2, -1, 4] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [-2, -1, 5] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [-2, -1, 6] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [-2, -1, 7] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [-2, 0, -8] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [-2, 0, -7] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [-2, 0, -6] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [-2, 0, -5] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [-2, 0, -4] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [-2, 0, -3] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [-2, 0, -2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [-2, 0, -1] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [-2, 0, 0] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [-2, 0, 1] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [-2, 0, 2] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [-2, 0, 3] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [-2, 0, 4] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [-2, 0, 5] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [-2, 0, 6] = true := by decide +kernel
theorem subd11_2_40 : subd11_2 [-2, 0, 7] = true := by decide +kernel
theorem subd11_2_41 : subd11_2 [-2, 0, 8] = true := by decide +kernel
theorem subd11_2_42 : subd11_2 [-2, 1, -9] = true := by decide +kernel
theorem subd11_2_43 : subd11_2 [-2, 1, -8] = true := by decide +kernel
theorem subd11_2_44 : subd11_2 [-2, 1, -7] = true := by decide +kernel
theorem subd11_2_45 : subd11_2 [-2, 1, -6] = true := by decide +kernel
theorem subd11_2_46 : subd11_2 [-2, 1, -5] = true := by decide +kernel
theorem subd11_2_47 : subd11_2 [-2, 1, -4] = true := by decide +kernel
theorem subd11_2_48 : subd11_2 [-2, 1, -3] = true := by decide +kernel
theorem subd11_2_49 : subd11_2 [-2, 1, -2] = true := by decide +kernel
theorem subd11_2_50 : subd11_2 [-2, 1, -1] = true := by decide +kernel
theorem subd11_2_51 : subd11_2 [-2, 1, 0] = true := by decide +kernel
theorem subd11_2_52 : subd11_2 [-2, 1, 1] = true := by decide +kernel
theorem subd11_2_53 : subd11_2 [-2, 1, 2] = true := by decide +kernel
theorem subd11_2_54 : subd11_2 [-2, 1, 3] = true := by decide +kernel
theorem subd11_2_55 : subd11_2 [-2, 1, 4] = true := by decide +kernel
theorem subd11_2_56 : subd11_2 [-2, 1, 5] = true := by decide +kernel
theorem subd11_2_57 : subd11_2 [-2, 1, 6] = true := by decide +kernel
theorem subd11_2_58 : subd11_2 [-2, 1, 7] = true := by decide +kernel
theorem subd11_2_59 : subd11_2 [-2, 1, 8] = true := by decide +kernel
theorem subd11_2_60 : subd11_2 [-2, 2, -8] = true := by decide +kernel
theorem subd11_2_61 : subd11_2 [-2, 2, -7] = true := by decide +kernel
theorem subd11_2_62 : subd11_2 [-2, 2, -6] = true := by decide +kernel
theorem subd11_2_63 : subd11_2 [-2, 2, -5] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_cons.2 ⟨subd11_2_40, List.forall_mem_cons.2 ⟨subd11_2_41, List.forall_mem_cons.2 ⟨subd11_2_42, List.forall_mem_cons.2 ⟨subd11_2_43, List.forall_mem_cons.2 ⟨subd11_2_44, List.forall_mem_cons.2 ⟨subd11_2_45, List.forall_mem_cons.2 ⟨subd11_2_46, List.forall_mem_cons.2 ⟨subd11_2_47, List.forall_mem_cons.2 ⟨subd11_2_48, List.forall_mem_cons.2 ⟨subd11_2_49, List.forall_mem_cons.2 ⟨subd11_2_50, List.forall_mem_cons.2 ⟨subd11_2_51, List.forall_mem_cons.2 ⟨subd11_2_52, List.forall_mem_cons.2 ⟨subd11_2_53, List.forall_mem_cons.2 ⟨subd11_2_54, List.forall_mem_cons.2 ⟨subd11_2_55, List.forall_mem_cons.2 ⟨subd11_2_56, List.forall_mem_cons.2 ⟨subd11_2_57, List.forall_mem_cons.2 ⟨subd11_2_58, List.forall_mem_cons.2 ⟨subd11_2_59, List.forall_mem_cons.2 ⟨subd11_2_60, List.forall_mem_cons.2 ⟨subd11_2_61, List.forall_mem_cons.2 ⟨subd11_2_62, List.forall_mem_cons.2 ⟨subd11_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_64 : subd11_2 [-2, 2, -4] = true := by decide +kernel
theorem subd11_2_65 : subd11_2 [-2, 2, -3] = true := by decide +kernel
theorem subd11_2_66 : subd11_2 [-2, 2, -2] = true := by decide +kernel
theorem subd11_2_67 : subd11_2 [-2, 2, -1] = true := by decide +kernel
theorem subd11_2_68 : subd11_2 [-2, 2, 0] = true := by decide +kernel
theorem subd11_2_69 : subd11_2 [-2, 2, 1] = true := by decide +kernel
theorem subd11_2_70 : subd11_2 [-2, 2, 2] = true := by decide +kernel
theorem subd11_2_71 : subd11_2 [-2, 2, 3] = true := by decide +kernel
theorem subd11_2_72 : subd11_2 [-2, 2, 4] = true := by decide +kernel
theorem subd11_2_73 : subd11_2 [-2, 2, 5] = true := by decide +kernel
theorem subd11_2_74 : subd11_2 [-2, 2, 6] = true := by decide +kernel
theorem subd11_2_75 : subd11_2 [-2, 2, 7] = true := by decide +kernel
theorem subd11_2_76 : subd11_2 [-2, 3, -7] = true := by decide +kernel
theorem subd11_2_77 : subd11_2 [-2, 3, -6] = true := by decide +kernel
theorem subd11_2_78 : subd11_2 [-2, 3, -5] = true := by decide +kernel
theorem subd11_2_79 : subd11_2 [-2, 3, -4] = true := by decide +kernel
theorem subd11_2_80 : subd11_2 [-2, 3, -3] = true := by decide +kernel
theorem subd11_2_81 : subd11_2 [-2, 3, -2] = true := by decide +kernel
theorem subd11_2_82 : subd11_2 [-2, 3, -1] = true := by decide +kernel
theorem subd11_2_83 : subd11_2 [-2, 3, 0] = true := by decide +kernel
theorem subd11_2_84 : subd11_2 [-2, 3, 1] = true := by decide +kernel
theorem subd11_2_85 : subd11_2 [-2, 3, 2] = true := by decide +kernel
theorem subd11_2_86 : subd11_2 [-2, 3, 3] = true := by decide +kernel
theorem subd11_2_87 : subd11_2 [-2, 3, 4] = true := by decide +kernel
theorem subd11_2_88 : subd11_2 [-2, 3, 5] = true := by decide +kernel
theorem subd11_2_89 : subd11_2 [-2, 3, 6] = true := by decide +kernel
theorem subd11_2_90 : subd11_2 [-2, 4] = true := by decide +kernel
theorem subd11_2_91 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_92 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_93 : subd11_2 [-1, -2, -8] = true := by decide +kernel
theorem subd11_2_94 : subd11_2 [-1, -2, -7] = true := by decide +kernel
theorem subd11_2_95 : subd11_2 [-1, -2, -6] = true := by decide +kernel
theorem sbd11_2_2 : ∀ q ∈ blkd11_2_2, subd11_2 q = true := by
  unfold blkd11_2_2
  exact List.forall_mem_cons.2 ⟨subd11_2_64, List.forall_mem_cons.2 ⟨subd11_2_65, List.forall_mem_cons.2 ⟨subd11_2_66, List.forall_mem_cons.2 ⟨subd11_2_67, List.forall_mem_cons.2 ⟨subd11_2_68, List.forall_mem_cons.2 ⟨subd11_2_69, List.forall_mem_cons.2 ⟨subd11_2_70, List.forall_mem_cons.2 ⟨subd11_2_71, List.forall_mem_cons.2 ⟨subd11_2_72, List.forall_mem_cons.2 ⟨subd11_2_73, List.forall_mem_cons.2 ⟨subd11_2_74, List.forall_mem_cons.2 ⟨subd11_2_75, List.forall_mem_cons.2 ⟨subd11_2_76, List.forall_mem_cons.2 ⟨subd11_2_77, List.forall_mem_cons.2 ⟨subd11_2_78, List.forall_mem_cons.2 ⟨subd11_2_79, List.forall_mem_cons.2 ⟨subd11_2_80, List.forall_mem_cons.2 ⟨subd11_2_81, List.forall_mem_cons.2 ⟨subd11_2_82, List.forall_mem_cons.2 ⟨subd11_2_83, List.forall_mem_cons.2 ⟨subd11_2_84, List.forall_mem_cons.2 ⟨subd11_2_85, List.forall_mem_cons.2 ⟨subd11_2_86, List.forall_mem_cons.2 ⟨subd11_2_87, List.forall_mem_cons.2 ⟨subd11_2_88, List.forall_mem_cons.2 ⟨subd11_2_89, List.forall_mem_cons.2 ⟨subd11_2_90, List.forall_mem_cons.2 ⟨subd11_2_91, List.forall_mem_cons.2 ⟨subd11_2_92, List.forall_mem_cons.2 ⟨subd11_2_93, List.forall_mem_cons.2 ⟨subd11_2_94, List.forall_mem_cons.2 ⟨subd11_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_96 : subd11_2 [-1, -2, -5] = true := by decide +kernel
theorem subd11_2_97 : subd11_2 [-1, -2, -4] = true := by decide +kernel
theorem subd11_2_98 : subd11_2 [-1, -2, -3] = true := by decide +kernel
theorem subd11_2_99 : subd11_2 [-1, -2, -2] = true := by decide +kernel
theorem subd11_2_100 : subd11_2 [-1, -2, -1] = true := by decide +kernel
theorem subd11_2_101 : subd11_2 [-1, -2, 0] = true := by decide +kernel
theorem subd11_2_102 : subd11_2 [-1, -2, 1] = true := by decide +kernel
theorem subd11_2_103 : subd11_2 [-1, -2, 2] = true := by decide +kernel
theorem subd11_2_104 : subd11_2 [-1, -2, 3] = true := by decide +kernel
theorem subd11_2_105 : subd11_2 [-1, -2, 4] = true := by decide +kernel
theorem subd11_2_106 : subd11_2 [-1, -2, 5] = true := by decide +kernel
theorem subd11_2_107 : subd11_2 [-1, -2, 6] = true := by decide +kernel
theorem subd11_2_108 : subd11_2 [-1, -2, 7] = true := by decide +kernel
theorem subd11_2_109 : subd11_2 [-1, -1, -9] = true := by decide +kernel
theorem subd11_2_110 : subd11_2 [-1, -1, -8] = true := by decide +kernel
theorem subd11_2_111 : subd11_2 [-1, -1, -7] = true := by decide +kernel
theorem subd11_2_112 : subd11_2 [-1, -1, -6] = true := by decide +kernel
theorem subd11_2_113 : subd11_2 [-1, -1, -5] = true := by decide +kernel
theorem subd11_2_114 : subd11_2 [-1, -1, -4] = true := by decide +kernel
theorem subd11_2_115 : subd11_2 [-1, -1, -3] = true := by decide +kernel
theorem subd11_2_116 : subd11_2 [-1, -1, -2] = true := by decide +kernel
theorem subd11_2_117 : subd11_2 [-1, -1, -1] = true := by decide +kernel
theorem subd11_2_118 : subd11_2 [-1, -1, 0] = true := by decide +kernel
theorem subd11_2_119 : subd11_2 [-1, -1, 1] = true := by decide +kernel
theorem subd11_2_120 : subd11_2 [-1, -1, 2] = true := by decide +kernel
theorem subd11_2_121 : subd11_2 [-1, -1, 3] = true := by decide +kernel
theorem subd11_2_122 : subd11_2 [-1, -1, 4] = true := by decide +kernel
theorem subd11_2_123 : subd11_2 [-1, -1, 5] = true := by decide +kernel
theorem subd11_2_124 : subd11_2 [-1, -1, 6] = true := by decide +kernel
theorem subd11_2_125 : subd11_2 [-1, -1, 7] = true := by decide +kernel
theorem subd11_2_126 : subd11_2 [-1, -1, 8] = true := by decide +kernel
theorem subd11_2_127 : subd11_2 [-1, 0, -10] = true := by decide +kernel
theorem sbd11_2_3 : ∀ q ∈ blkd11_2_3, subd11_2 q = true := by
  unfold blkd11_2_3
  exact List.forall_mem_cons.2 ⟨subd11_2_96, List.forall_mem_cons.2 ⟨subd11_2_97, List.forall_mem_cons.2 ⟨subd11_2_98, List.forall_mem_cons.2 ⟨subd11_2_99, List.forall_mem_cons.2 ⟨subd11_2_100, List.forall_mem_cons.2 ⟨subd11_2_101, List.forall_mem_cons.2 ⟨subd11_2_102, List.forall_mem_cons.2 ⟨subd11_2_103, List.forall_mem_cons.2 ⟨subd11_2_104, List.forall_mem_cons.2 ⟨subd11_2_105, List.forall_mem_cons.2 ⟨subd11_2_106, List.forall_mem_cons.2 ⟨subd11_2_107, List.forall_mem_cons.2 ⟨subd11_2_108, List.forall_mem_cons.2 ⟨subd11_2_109, List.forall_mem_cons.2 ⟨subd11_2_110, List.forall_mem_cons.2 ⟨subd11_2_111, List.forall_mem_cons.2 ⟨subd11_2_112, List.forall_mem_cons.2 ⟨subd11_2_113, List.forall_mem_cons.2 ⟨subd11_2_114, List.forall_mem_cons.2 ⟨subd11_2_115, List.forall_mem_cons.2 ⟨subd11_2_116, List.forall_mem_cons.2 ⟨subd11_2_117, List.forall_mem_cons.2 ⟨subd11_2_118, List.forall_mem_cons.2 ⟨subd11_2_119, List.forall_mem_cons.2 ⟨subd11_2_120, List.forall_mem_cons.2 ⟨subd11_2_121, List.forall_mem_cons.2 ⟨subd11_2_122, List.forall_mem_cons.2 ⟨subd11_2_123, List.forall_mem_cons.2 ⟨subd11_2_124, List.forall_mem_cons.2 ⟨subd11_2_125, List.forall_mem_cons.2 ⟨subd11_2_126, List.forall_mem_cons.2 ⟨subd11_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_128 : subd11_2 [-1, 0, -9] = true := by decide +kernel
theorem subd11_2_129 : subd11_2 [-1, 0, -8] = true := by decide +kernel
theorem subd11_2_130 : subd11_2 [-1, 0, -7] = true := by decide +kernel
theorem subd11_2_131 : subd11_2 [-1, 0, -6] = true := by decide +kernel
theorem subd11_2_132 : subd11_2 [-1, 0, -5] = true := by decide +kernel
theorem subd11_2_133 : subd11_2 [-1, 0, -4] = true := by decide +kernel
theorem subd11_2_134 : subd11_2 [-1, 0, -3] = true := by decide +kernel
theorem subd11_2_135 : subd11_2 [-1, 0, -2] = true := by decide +kernel
theorem subd11_2_136 : subd11_2 [-1, 0, -1] = true := by decide +kernel
theorem subd11_2_137 : subd11_2 [-1, 0, 0] = true := by decide +kernel
theorem subd11_2_138 : subd11_2 [-1, 0, 1] = true := by decide +kernel
theorem subd11_2_139 : subd11_2 [-1, 0, 2] = true := by decide +kernel
theorem subd11_2_140 : subd11_2 [-1, 0, 3] = true := by decide +kernel
theorem subd11_2_141 : subd11_2 [-1, 0, 4] = true := by decide +kernel
theorem subd11_2_142 : subd11_2 [-1, 0, 5] = true := by decide +kernel
theorem subd11_2_143 : subd11_2 [-1, 0, 6] = true := by decide +kernel
theorem subd11_2_144 : subd11_2 [-1, 0, 7] = true := by decide +kernel
theorem subd11_2_145 : subd11_2 [-1, 0, 8] = true := by decide +kernel
theorem subd11_2_146 : subd11_2 [-1, 0, 9] = true := by decide +kernel
theorem subd11_2_147 : subd11_2 [-1, 1, -10] = true := by decide +kernel
theorem subd11_2_148 : subd11_2 [-1, 1, -9] = true := by decide +kernel
theorem subd11_2_149 : subd11_2 [-1, 1, -8] = true := by decide +kernel
theorem subd11_2_150 : subd11_2 [-1, 1, -7] = true := by decide +kernel
theorem subd11_2_151 : subd11_2 [-1, 1, -6] = true := by decide +kernel
theorem subd11_2_152 : subd11_2 [-1, 1, -5] = true := by decide +kernel
theorem subd11_2_153 : subd11_2 [-1, 1, -4] = true := by decide +kernel
theorem subd11_2_154 : subd11_2 [-1, 1, -3] = true := by decide +kernel
theorem subd11_2_155 : subd11_2 [-1, 1, -2] = true := by decide +kernel
theorem subd11_2_156 : subd11_2 [-1, 1, -1] = true := by decide +kernel
theorem subd11_2_157 : subd11_2 [-1, 1, 0] = true := by decide +kernel
theorem subd11_2_158 : subd11_2 [-1, 1, 1] = true := by decide +kernel
theorem subd11_2_159 : subd11_2 [-1, 1, 2] = true := by decide +kernel
theorem sbd11_2_4 : ∀ q ∈ blkd11_2_4, subd11_2 q = true := by
  unfold blkd11_2_4
  exact List.forall_mem_cons.2 ⟨subd11_2_128, List.forall_mem_cons.2 ⟨subd11_2_129, List.forall_mem_cons.2 ⟨subd11_2_130, List.forall_mem_cons.2 ⟨subd11_2_131, List.forall_mem_cons.2 ⟨subd11_2_132, List.forall_mem_cons.2 ⟨subd11_2_133, List.forall_mem_cons.2 ⟨subd11_2_134, List.forall_mem_cons.2 ⟨subd11_2_135, List.forall_mem_cons.2 ⟨subd11_2_136, List.forall_mem_cons.2 ⟨subd11_2_137, List.forall_mem_cons.2 ⟨subd11_2_138, List.forall_mem_cons.2 ⟨subd11_2_139, List.forall_mem_cons.2 ⟨subd11_2_140, List.forall_mem_cons.2 ⟨subd11_2_141, List.forall_mem_cons.2 ⟨subd11_2_142, List.forall_mem_cons.2 ⟨subd11_2_143, List.forall_mem_cons.2 ⟨subd11_2_144, List.forall_mem_cons.2 ⟨subd11_2_145, List.forall_mem_cons.2 ⟨subd11_2_146, List.forall_mem_cons.2 ⟨subd11_2_147, List.forall_mem_cons.2 ⟨subd11_2_148, List.forall_mem_cons.2 ⟨subd11_2_149, List.forall_mem_cons.2 ⟨subd11_2_150, List.forall_mem_cons.2 ⟨subd11_2_151, List.forall_mem_cons.2 ⟨subd11_2_152, List.forall_mem_cons.2 ⟨subd11_2_153, List.forall_mem_cons.2 ⟨subd11_2_154, List.forall_mem_cons.2 ⟨subd11_2_155, List.forall_mem_cons.2 ⟨subd11_2_156, List.forall_mem_cons.2 ⟨subd11_2_157, List.forall_mem_cons.2 ⟨subd11_2_158, List.forall_mem_cons.2 ⟨subd11_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_160 : subd11_2 [-1, 1, 3] = true := by decide +kernel
theorem subd11_2_161 : subd11_2 [-1, 1, 4] = true := by decide +kernel
theorem subd11_2_162 : subd11_2 [-1, 1, 5] = true := by decide +kernel
theorem subd11_2_163 : subd11_2 [-1, 1, 6] = true := by decide +kernel
theorem subd11_2_164 : subd11_2 [-1, 1, 7] = true := by decide +kernel
theorem subd11_2_165 : subd11_2 [-1, 1, 8] = true := by decide +kernel
theorem subd11_2_166 : subd11_2 [-1, 2, -9] = true := by decide +kernel
theorem subd11_2_167 : subd11_2 [-1, 2, -8] = true := by decide +kernel
theorem subd11_2_168 : subd11_2 [-1, 2, -7] = true := by decide +kernel
theorem subd11_2_169 : subd11_2 [-1, 2, -6] = true := by decide +kernel
theorem subd11_2_170 : subd11_2 [-1, 2, -5] = true := by decide +kernel
theorem subd11_2_171 : subd11_2 [-1, 2, -4] = true := by decide +kernel
theorem subd11_2_172 : subd11_2 [-1, 2, -3] = true := by decide +kernel
theorem subd11_2_173 : subd11_2 [-1, 2, -2] = true := by decide +kernel
theorem subd11_2_174 : subd11_2 [-1, 2, -1] = true := by decide +kernel
theorem subd11_2_175 : subd11_2 [-1, 2, 0] = true := by decide +kernel
theorem subd11_2_176 : subd11_2 [-1, 2, 1] = true := by decide +kernel
theorem subd11_2_177 : subd11_2 [-1, 2, 2] = true := by decide +kernel
theorem subd11_2_178 : subd11_2 [-1, 2, 3] = true := by decide +kernel
theorem subd11_2_179 : subd11_2 [-1, 2, 4] = true := by decide +kernel
theorem subd11_2_180 : subd11_2 [-1, 2, 5] = true := by decide +kernel
theorem subd11_2_181 : subd11_2 [-1, 2, 6] = true := by decide +kernel
theorem subd11_2_182 : subd11_2 [-1, 2, 7] = true := by decide +kernel
theorem subd11_2_183 : subd11_2 [-1, 2, 8] = true := by decide +kernel
theorem subd11_2_184 : subd11_2 [-1, 3, -8] = true := by decide +kernel
theorem subd11_2_185 : subd11_2 [-1, 3, -7] = true := by decide +kernel
theorem subd11_2_186 : subd11_2 [-1, 3, -6] = true := by decide +kernel
theorem subd11_2_187 : subd11_2 [-1, 3, -5] = true := by decide +kernel
theorem subd11_2_188 : subd11_2 [-1, 3, -4] = true := by decide +kernel
theorem subd11_2_189 : subd11_2 [-1, 3, -3] = true := by decide +kernel
theorem subd11_2_190 : subd11_2 [-1, 3, -2] = true := by decide +kernel
theorem subd11_2_191 : subd11_2 [-1, 3, -1] = true := by decide +kernel
theorem sbd11_2_5 : ∀ q ∈ blkd11_2_5, subd11_2 q = true := by
  unfold blkd11_2_5
  exact List.forall_mem_cons.2 ⟨subd11_2_160, List.forall_mem_cons.2 ⟨subd11_2_161, List.forall_mem_cons.2 ⟨subd11_2_162, List.forall_mem_cons.2 ⟨subd11_2_163, List.forall_mem_cons.2 ⟨subd11_2_164, List.forall_mem_cons.2 ⟨subd11_2_165, List.forall_mem_cons.2 ⟨subd11_2_166, List.forall_mem_cons.2 ⟨subd11_2_167, List.forall_mem_cons.2 ⟨subd11_2_168, List.forall_mem_cons.2 ⟨subd11_2_169, List.forall_mem_cons.2 ⟨subd11_2_170, List.forall_mem_cons.2 ⟨subd11_2_171, List.forall_mem_cons.2 ⟨subd11_2_172, List.forall_mem_cons.2 ⟨subd11_2_173, List.forall_mem_cons.2 ⟨subd11_2_174, List.forall_mem_cons.2 ⟨subd11_2_175, List.forall_mem_cons.2 ⟨subd11_2_176, List.forall_mem_cons.2 ⟨subd11_2_177, List.forall_mem_cons.2 ⟨subd11_2_178, List.forall_mem_cons.2 ⟨subd11_2_179, List.forall_mem_cons.2 ⟨subd11_2_180, List.forall_mem_cons.2 ⟨subd11_2_181, List.forall_mem_cons.2 ⟨subd11_2_182, List.forall_mem_cons.2 ⟨subd11_2_183, List.forall_mem_cons.2 ⟨subd11_2_184, List.forall_mem_cons.2 ⟨subd11_2_185, List.forall_mem_cons.2 ⟨subd11_2_186, List.forall_mem_cons.2 ⟨subd11_2_187, List.forall_mem_cons.2 ⟨subd11_2_188, List.forall_mem_cons.2 ⟨subd11_2_189, List.forall_mem_cons.2 ⟨subd11_2_190, List.forall_mem_cons.2 ⟨subd11_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_192 : subd11_2 [-1, 3, 0] = true := by decide +kernel
theorem subd11_2_193 : subd11_2 [-1, 3, 1] = true := by decide +kernel
theorem subd11_2_194 : subd11_2 [-1, 3, 2] = true := by decide +kernel
theorem subd11_2_195 : subd11_2 [-1, 3, 3] = true := by decide +kernel
theorem subd11_2_196 : subd11_2 [-1, 3, 4] = true := by decide +kernel
theorem subd11_2_197 : subd11_2 [-1, 3, 5] = true := by decide +kernel
theorem subd11_2_198 : subd11_2 [-1, 3, 6] = true := by decide +kernel
theorem subd11_2_199 : subd11_2 [-1, 4] = true := by decide +kernel
theorem subd11_2_200 : subd11_2 [0, -5] = true := by decide +kernel
theorem subd11_2_201 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_202 : subd11_2 [0, -3, -7] = true := by decide +kernel
theorem subd11_2_203 : subd11_2 [0, -3, -6] = true := by decide +kernel
theorem subd11_2_204 : subd11_2 [0, -3, -5] = true := by decide +kernel
theorem subd11_2_205 : subd11_2 [0, -3, -4] = true := by decide +kernel
theorem subd11_2_206 : subd11_2 [0, -3, -3] = true := by decide +kernel
theorem subd11_2_207 : subd11_2 [0, -3, -2] = true := by decide +kernel
theorem subd11_2_208 : subd11_2 [0, -3, -1] = true := by decide +kernel
theorem subd11_2_209 : subd11_2 [0, -3, 0] = true := by decide +kernel
theorem subd11_2_210 : subd11_2 [0, -3, 1] = true := by decide +kernel
theorem subd11_2_211 : subd11_2 [0, -3, 2] = true := by decide +kernel
theorem subd11_2_212 : subd11_2 [0, -3, 3] = true := by decide +kernel
theorem subd11_2_213 : subd11_2 [0, -3, 4] = true := by decide +kernel
theorem subd11_2_214 : subd11_2 [0, -3, 5] = true := by decide +kernel
theorem subd11_2_215 : subd11_2 [0, -3, 6] = true := by decide +kernel
theorem subd11_2_216 : subd11_2 [0, -3, 7] = true := by decide +kernel
theorem subd11_2_217 : subd11_2 [0, -2, -9] = true := by decide +kernel
theorem subd11_2_218 : subd11_2 [0, -2, -8] = true := by decide +kernel
theorem subd11_2_219 : subd11_2 [0, -2, -7] = true := by decide +kernel
theorem subd11_2_220 : subd11_2 [0, -2, -6] = true := by decide +kernel
theorem subd11_2_221 : subd11_2 [0, -2, -5] = true := by decide +kernel
theorem subd11_2_222 : subd11_2 [0, -2, -4] = true := by decide +kernel
theorem subd11_2_223 : subd11_2 [0, -2, -3] = true := by decide +kernel
theorem sbd11_2_6 : ∀ q ∈ blkd11_2_6, subd11_2 q = true := by
  unfold blkd11_2_6
  exact List.forall_mem_cons.2 ⟨subd11_2_192, List.forall_mem_cons.2 ⟨subd11_2_193, List.forall_mem_cons.2 ⟨subd11_2_194, List.forall_mem_cons.2 ⟨subd11_2_195, List.forall_mem_cons.2 ⟨subd11_2_196, List.forall_mem_cons.2 ⟨subd11_2_197, List.forall_mem_cons.2 ⟨subd11_2_198, List.forall_mem_cons.2 ⟨subd11_2_199, List.forall_mem_cons.2 ⟨subd11_2_200, List.forall_mem_cons.2 ⟨subd11_2_201, List.forall_mem_cons.2 ⟨subd11_2_202, List.forall_mem_cons.2 ⟨subd11_2_203, List.forall_mem_cons.2 ⟨subd11_2_204, List.forall_mem_cons.2 ⟨subd11_2_205, List.forall_mem_cons.2 ⟨subd11_2_206, List.forall_mem_cons.2 ⟨subd11_2_207, List.forall_mem_cons.2 ⟨subd11_2_208, List.forall_mem_cons.2 ⟨subd11_2_209, List.forall_mem_cons.2 ⟨subd11_2_210, List.forall_mem_cons.2 ⟨subd11_2_211, List.forall_mem_cons.2 ⟨subd11_2_212, List.forall_mem_cons.2 ⟨subd11_2_213, List.forall_mem_cons.2 ⟨subd11_2_214, List.forall_mem_cons.2 ⟨subd11_2_215, List.forall_mem_cons.2 ⟨subd11_2_216, List.forall_mem_cons.2 ⟨subd11_2_217, List.forall_mem_cons.2 ⟨subd11_2_218, List.forall_mem_cons.2 ⟨subd11_2_219, List.forall_mem_cons.2 ⟨subd11_2_220, List.forall_mem_cons.2 ⟨subd11_2_221, List.forall_mem_cons.2 ⟨subd11_2_222, List.forall_mem_cons.2 ⟨subd11_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_224 : subd11_2 [0, -2, -2] = true := by decide +kernel
theorem subd11_2_225 : subd11_2 [0, -2, -1] = true := by decide +kernel
theorem subd11_2_226 : subd11_2 [0, -2, 0] = true := by decide +kernel
theorem subd11_2_227 : subd11_2 [0, -2, 1] = true := by decide +kernel
theorem subd11_2_228 : subd11_2 [0, -2, 2] = true := by decide +kernel
theorem subd11_2_229 : subd11_2 [0, -2, 3] = true := by decide +kernel
theorem subd11_2_230 : subd11_2 [0, -2, 4] = true := by decide +kernel
theorem subd11_2_231 : subd11_2 [0, -2, 5] = true := by decide +kernel
theorem subd11_2_232 : subd11_2 [0, -2, 6] = true := by decide +kernel
theorem subd11_2_233 : subd11_2 [0, -2, 7] = true := by decide +kernel
theorem subd11_2_234 : subd11_2 [0, -2, 8] = true := by decide +kernel
theorem subd11_2_235 : subd11_2 [0, -1, -10] = true := by decide +kernel
theorem subd11_2_236 : subd11_2 [0, -1, -9] = true := by decide +kernel
theorem subd11_2_237 : subd11_2 [0, -1, -8] = true := by decide +kernel
theorem subd11_2_238 : subd11_2 [0, -1, -7] = true := by decide +kernel
theorem subd11_2_239 : subd11_2 [0, -1, -6] = true := by decide +kernel
theorem subd11_2_240 : subd11_2 [0, -1, -5] = true := by decide +kernel
theorem subd11_2_241 : subd11_2 [0, -1, -4] = true := by decide +kernel
theorem subd11_2_242 : subd11_2 [0, -1, -3] = true := by decide +kernel
theorem subd11_2_243 : subd11_2 [0, -1, -2] = true := by decide +kernel
theorem subd11_2_244 : subd11_2 [0, -1, -1] = true := by decide +kernel
theorem subd11_2_245 : subd11_2 [0, -1, 0] = true := by decide +kernel
theorem subd11_2_246 : subd11_2 [0, -1, 1] = true := by decide +kernel
theorem subd11_2_247 : subd11_2 [0, -1, 2] = true := by decide +kernel
theorem subd11_2_248 : subd11_2 [0, -1, 3] = true := by decide +kernel
theorem subd11_2_249 : subd11_2 [0, -1, 4] = true := by decide +kernel
theorem subd11_2_250 : subd11_2 [0, -1, 5] = true := by decide +kernel
theorem subd11_2_251 : subd11_2 [0, -1, 6] = true := by decide +kernel
theorem subd11_2_252 : subd11_2 [0, -1, 7] = true := by decide +kernel
theorem subd11_2_253 : subd11_2 [0, -1, 8] = true := by decide +kernel
theorem subd11_2_254 : subd11_2 [0, -1, 9] = true := by decide +kernel
theorem subd11_2_255 : subd11_2 [0, 0, -10] = true := by decide +kernel
theorem sbd11_2_7 : ∀ q ∈ blkd11_2_7, subd11_2 q = true := by
  unfold blkd11_2_7
  exact List.forall_mem_cons.2 ⟨subd11_2_224, List.forall_mem_cons.2 ⟨subd11_2_225, List.forall_mem_cons.2 ⟨subd11_2_226, List.forall_mem_cons.2 ⟨subd11_2_227, List.forall_mem_cons.2 ⟨subd11_2_228, List.forall_mem_cons.2 ⟨subd11_2_229, List.forall_mem_cons.2 ⟨subd11_2_230, List.forall_mem_cons.2 ⟨subd11_2_231, List.forall_mem_cons.2 ⟨subd11_2_232, List.forall_mem_cons.2 ⟨subd11_2_233, List.forall_mem_cons.2 ⟨subd11_2_234, List.forall_mem_cons.2 ⟨subd11_2_235, List.forall_mem_cons.2 ⟨subd11_2_236, List.forall_mem_cons.2 ⟨subd11_2_237, List.forall_mem_cons.2 ⟨subd11_2_238, List.forall_mem_cons.2 ⟨subd11_2_239, List.forall_mem_cons.2 ⟨subd11_2_240, List.forall_mem_cons.2 ⟨subd11_2_241, List.forall_mem_cons.2 ⟨subd11_2_242, List.forall_mem_cons.2 ⟨subd11_2_243, List.forall_mem_cons.2 ⟨subd11_2_244, List.forall_mem_cons.2 ⟨subd11_2_245, List.forall_mem_cons.2 ⟨subd11_2_246, List.forall_mem_cons.2 ⟨subd11_2_247, List.forall_mem_cons.2 ⟨subd11_2_248, List.forall_mem_cons.2 ⟨subd11_2_249, List.forall_mem_cons.2 ⟨subd11_2_250, List.forall_mem_cons.2 ⟨subd11_2_251, List.forall_mem_cons.2 ⟨subd11_2_252, List.forall_mem_cons.2 ⟨subd11_2_253, List.forall_mem_cons.2 ⟨subd11_2_254, List.forall_mem_cons.2 ⟨subd11_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_256 : subd11_2 [0, 0, -9] = true := by decide +kernel
theorem subd11_2_257 : subd11_2 [0, 0, -8] = true := by decide +kernel
theorem subd11_2_258 : subd11_2 [0, 0, -7] = true := by decide +kernel
theorem subd11_2_259 : subd11_2 [0, 0, -6] = true := by decide +kernel
theorem subd11_2_260 : subd11_2 [0, 0, -5] = true := by decide +kernel
theorem subd11_2_261 : subd11_2 [0, 0, -4] = true := by decide +kernel
theorem subd11_2_262 : subd11_2 [0, 0, -3] = true := by decide +kernel
theorem subd11_2_263 : subd11_2 [0, 0, -2] = true := by decide +kernel
theorem subd11_2_264 : subd11_2 [0, 0, -1] = true := by decide +kernel
theorem subd11_2_265 : subd11_2 [0, 0, 0] = true := by decide +kernel
theorem subd11_2_266 : subd11_2 [0, 0, 1] = true := by decide +kernel
theorem subd11_2_267 : subd11_2 [0, 0, 2] = true := by decide +kernel
theorem subd11_2_268 : subd11_2 [0, 0, 3] = true := by decide +kernel
theorem subd11_2_269 : subd11_2 [0, 0, 4] = true := by decide +kernel
theorem subd11_2_270 : subd11_2 [0, 0, 5] = true := by decide +kernel
theorem subd11_2_271 : subd11_2 [0, 0, 6] = true := by decide +kernel
theorem subd11_2_272 : subd11_2 [0, 0, 7] = true := by decide +kernel
theorem subd11_2_273 : subd11_2 [0, 0, 8] = true := by decide +kernel
theorem subd11_2_274 : subd11_2 [0, 0, 9] = true := by decide +kernel
theorem subd11_2_275 : subd11_2 [0, 1, -10] = true := by decide +kernel
theorem subd11_2_276 : subd11_2 [0, 1, -9] = true := by decide +kernel
theorem subd11_2_277 : subd11_2 [0, 1, -8] = true := by decide +kernel
theorem subd11_2_278 : subd11_2 [0, 1, -7] = true := by decide +kernel
theorem subd11_2_279 : subd11_2 [0, 1, -6] = true := by decide +kernel
theorem subd11_2_280 : subd11_2 [0, 1, -5] = true := by decide +kernel
theorem subd11_2_281 : subd11_2 [0, 1, -4] = true := by decide +kernel
theorem subd11_2_282 : subd11_2 [0, 1, -3] = true := by decide +kernel
theorem subd11_2_283 : subd11_2 [0, 1, -2] = true := by decide +kernel
theorem subd11_2_284 : subd11_2 [0, 1, -1] = true := by decide +kernel
theorem subd11_2_285 : subd11_2 [0, 1, 0] = true := by decide +kernel
theorem subd11_2_286 : subd11_2 [0, 1, 1] = true := by decide +kernel
theorem subd11_2_287 : subd11_2 [0, 1, 2] = true := by decide +kernel
theorem sbd11_2_8 : ∀ q ∈ blkd11_2_8, subd11_2 q = true := by
  unfold blkd11_2_8
  exact List.forall_mem_cons.2 ⟨subd11_2_256, List.forall_mem_cons.2 ⟨subd11_2_257, List.forall_mem_cons.2 ⟨subd11_2_258, List.forall_mem_cons.2 ⟨subd11_2_259, List.forall_mem_cons.2 ⟨subd11_2_260, List.forall_mem_cons.2 ⟨subd11_2_261, List.forall_mem_cons.2 ⟨subd11_2_262, List.forall_mem_cons.2 ⟨subd11_2_263, List.forall_mem_cons.2 ⟨subd11_2_264, List.forall_mem_cons.2 ⟨subd11_2_265, List.forall_mem_cons.2 ⟨subd11_2_266, List.forall_mem_cons.2 ⟨subd11_2_267, List.forall_mem_cons.2 ⟨subd11_2_268, List.forall_mem_cons.2 ⟨subd11_2_269, List.forall_mem_cons.2 ⟨subd11_2_270, List.forall_mem_cons.2 ⟨subd11_2_271, List.forall_mem_cons.2 ⟨subd11_2_272, List.forall_mem_cons.2 ⟨subd11_2_273, List.forall_mem_cons.2 ⟨subd11_2_274, List.forall_mem_cons.2 ⟨subd11_2_275, List.forall_mem_cons.2 ⟨subd11_2_276, List.forall_mem_cons.2 ⟨subd11_2_277, List.forall_mem_cons.2 ⟨subd11_2_278, List.forall_mem_cons.2 ⟨subd11_2_279, List.forall_mem_cons.2 ⟨subd11_2_280, List.forall_mem_cons.2 ⟨subd11_2_281, List.forall_mem_cons.2 ⟨subd11_2_282, List.forall_mem_cons.2 ⟨subd11_2_283, List.forall_mem_cons.2 ⟨subd11_2_284, List.forall_mem_cons.2 ⟨subd11_2_285, List.forall_mem_cons.2 ⟨subd11_2_286, List.forall_mem_cons.2 ⟨subd11_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_288 : subd11_2 [0, 1, 3] = true := by decide +kernel
theorem subd11_2_289 : subd11_2 [0, 1, 4] = true := by decide +kernel
theorem subd11_2_290 : subd11_2 [0, 1, 5] = true := by decide +kernel
theorem subd11_2_291 : subd11_2 [0, 1, 6] = true := by decide +kernel
theorem subd11_2_292 : subd11_2 [0, 1, 7] = true := by decide +kernel
theorem subd11_2_293 : subd11_2 [0, 1, 8] = true := by decide +kernel
theorem subd11_2_294 : subd11_2 [0, 1, 9] = true := by decide +kernel
theorem subd11_2_295 : subd11_2 [0, 2, -9] = true := by decide +kernel
theorem subd11_2_296 : subd11_2 [0, 2, -8] = true := by decide +kernel
theorem subd11_2_297 : subd11_2 [0, 2, -7] = true := by decide +kernel
theorem subd11_2_298 : subd11_2 [0, 2, -6] = true := by decide +kernel
theorem subd11_2_299 : subd11_2 [0, 2, -5] = true := by decide +kernel
theorem subd11_2_300 : subd11_2 [0, 2, -4] = true := by decide +kernel
theorem subd11_2_301 : subd11_2 [0, 2, -3] = true := by decide +kernel
theorem subd11_2_302 : subd11_2 [0, 2, -2] = true := by decide +kernel
theorem subd11_2_303 : subd11_2 [0, 2, -1] = true := by decide +kernel
theorem subd11_2_304 : subd11_2 [0, 2, 0] = true := by decide +kernel
theorem subd11_2_305 : subd11_2 [0, 2, 1] = true := by decide +kernel
theorem subd11_2_306 : subd11_2 [0, 2, 2] = true := by decide +kernel
theorem subd11_2_307 : subd11_2 [0, 2, 3] = true := by decide +kernel
theorem subd11_2_308 : subd11_2 [0, 2, 4] = true := by decide +kernel
theorem subd11_2_309 : subd11_2 [0, 2, 5] = true := by decide +kernel
theorem subd11_2_310 : subd11_2 [0, 2, 6] = true := by decide +kernel
theorem subd11_2_311 : subd11_2 [0, 2, 7] = true := by decide +kernel
theorem subd11_2_312 : subd11_2 [0, 2, 8] = true := by decide +kernel
theorem subd11_2_313 : subd11_2 [0, 3, -8] = true := by decide +kernel
theorem subd11_2_314 : subd11_2 [0, 3, -7] = true := by decide +kernel
theorem subd11_2_315 : subd11_2 [0, 3, -6] = true := by decide +kernel
theorem subd11_2_316 : subd11_2 [0, 3, -5] = true := by decide +kernel
theorem subd11_2_317 : subd11_2 [0, 3, -4] = true := by decide +kernel
theorem subd11_2_318 : subd11_2 [0, 3, -3] = true := by decide +kernel
theorem subd11_2_319 : subd11_2 [0, 3, -2] = true := by decide +kernel
theorem sbd11_2_9 : ∀ q ∈ blkd11_2_9, subd11_2 q = true := by
  unfold blkd11_2_9
  exact List.forall_mem_cons.2 ⟨subd11_2_288, List.forall_mem_cons.2 ⟨subd11_2_289, List.forall_mem_cons.2 ⟨subd11_2_290, List.forall_mem_cons.2 ⟨subd11_2_291, List.forall_mem_cons.2 ⟨subd11_2_292, List.forall_mem_cons.2 ⟨subd11_2_293, List.forall_mem_cons.2 ⟨subd11_2_294, List.forall_mem_cons.2 ⟨subd11_2_295, List.forall_mem_cons.2 ⟨subd11_2_296, List.forall_mem_cons.2 ⟨subd11_2_297, List.forall_mem_cons.2 ⟨subd11_2_298, List.forall_mem_cons.2 ⟨subd11_2_299, List.forall_mem_cons.2 ⟨subd11_2_300, List.forall_mem_cons.2 ⟨subd11_2_301, List.forall_mem_cons.2 ⟨subd11_2_302, List.forall_mem_cons.2 ⟨subd11_2_303, List.forall_mem_cons.2 ⟨subd11_2_304, List.forall_mem_cons.2 ⟨subd11_2_305, List.forall_mem_cons.2 ⟨subd11_2_306, List.forall_mem_cons.2 ⟨subd11_2_307, List.forall_mem_cons.2 ⟨subd11_2_308, List.forall_mem_cons.2 ⟨subd11_2_309, List.forall_mem_cons.2 ⟨subd11_2_310, List.forall_mem_cons.2 ⟨subd11_2_311, List.forall_mem_cons.2 ⟨subd11_2_312, List.forall_mem_cons.2 ⟨subd11_2_313, List.forall_mem_cons.2 ⟨subd11_2_314, List.forall_mem_cons.2 ⟨subd11_2_315, List.forall_mem_cons.2 ⟨subd11_2_316, List.forall_mem_cons.2 ⟨subd11_2_317, List.forall_mem_cons.2 ⟨subd11_2_318, List.forall_mem_cons.2 ⟨subd11_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_320 : subd11_2 [0, 3, -1] = true := by decide +kernel
theorem subd11_2_321 : subd11_2 [0, 3, 0] = true := by decide +kernel
theorem subd11_2_322 : subd11_2 [0, 3, 1] = true := by decide +kernel
theorem subd11_2_323 : subd11_2 [0, 3, 2] = true := by decide +kernel
theorem subd11_2_324 : subd11_2 [0, 3, 3] = true := by decide +kernel
theorem subd11_2_325 : subd11_2 [0, 3, 4] = true := by decide +kernel
theorem subd11_2_326 : subd11_2 [0, 3, 5] = true := by decide +kernel
theorem subd11_2_327 : subd11_2 [0, 3, 6] = true := by decide +kernel
theorem subd11_2_328 : subd11_2 [0, 4] = true := by decide +kernel
theorem subd11_2_329 : subd11_2 [1, -5] = true := by decide +kernel
theorem subd11_2_330 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_331 : subd11_2 [1, -3, -7] = true := by decide +kernel
theorem subd11_2_332 : subd11_2 [1, -3, -6] = true := by decide +kernel
theorem subd11_2_333 : subd11_2 [1, -3, -5] = true := by decide +kernel
theorem subd11_2_334 : subd11_2 [1, -3, -4] = true := by decide +kernel
theorem subd11_2_335 : subd11_2 [1, -3, -3] = true := by decide +kernel
theorem subd11_2_336 : subd11_2 [1, -3, -2] = true := by decide +kernel
theorem subd11_2_337 : subd11_2 [1, -3, -1] = true := by decide +kernel
theorem subd11_2_338 : subd11_2 [1, -3, 0] = true := by decide +kernel
theorem subd11_2_339 : subd11_2 [1, -3, 1] = true := by decide +kernel
theorem subd11_2_340 : subd11_2 [1, -3, 2] = true := by decide +kernel
theorem subd11_2_341 : subd11_2 [1, -3, 3] = true := by decide +kernel
theorem subd11_2_342 : subd11_2 [1, -3, 4] = true := by decide +kernel
theorem subd11_2_343 : subd11_2 [1, -3, 5] = true := by decide +kernel
theorem subd11_2_344 : subd11_2 [1, -3, 6] = true := by decide +kernel
theorem subd11_2_345 : subd11_2 [1, -3, 7] = true := by decide +kernel
theorem subd11_2_346 : subd11_2 [1, -2, -9] = true := by decide +kernel
theorem subd11_2_347 : subd11_2 [1, -2, -8] = true := by decide +kernel
theorem subd11_2_348 : subd11_2 [1, -2, -7] = true := by decide +kernel
theorem subd11_2_349 : subd11_2 [1, -2, -6] = true := by decide +kernel
theorem subd11_2_350 : subd11_2 [1, -2, -5] = true := by decide +kernel
theorem subd11_2_351 : subd11_2 [1, -2, -4] = true := by decide +kernel
theorem sbd11_2_10 : ∀ q ∈ blkd11_2_10, subd11_2 q = true := by
  unfold blkd11_2_10
  exact List.forall_mem_cons.2 ⟨subd11_2_320, List.forall_mem_cons.2 ⟨subd11_2_321, List.forall_mem_cons.2 ⟨subd11_2_322, List.forall_mem_cons.2 ⟨subd11_2_323, List.forall_mem_cons.2 ⟨subd11_2_324, List.forall_mem_cons.2 ⟨subd11_2_325, List.forall_mem_cons.2 ⟨subd11_2_326, List.forall_mem_cons.2 ⟨subd11_2_327, List.forall_mem_cons.2 ⟨subd11_2_328, List.forall_mem_cons.2 ⟨subd11_2_329, List.forall_mem_cons.2 ⟨subd11_2_330, List.forall_mem_cons.2 ⟨subd11_2_331, List.forall_mem_cons.2 ⟨subd11_2_332, List.forall_mem_cons.2 ⟨subd11_2_333, List.forall_mem_cons.2 ⟨subd11_2_334, List.forall_mem_cons.2 ⟨subd11_2_335, List.forall_mem_cons.2 ⟨subd11_2_336, List.forall_mem_cons.2 ⟨subd11_2_337, List.forall_mem_cons.2 ⟨subd11_2_338, List.forall_mem_cons.2 ⟨subd11_2_339, List.forall_mem_cons.2 ⟨subd11_2_340, List.forall_mem_cons.2 ⟨subd11_2_341, List.forall_mem_cons.2 ⟨subd11_2_342, List.forall_mem_cons.2 ⟨subd11_2_343, List.forall_mem_cons.2 ⟨subd11_2_344, List.forall_mem_cons.2 ⟨subd11_2_345, List.forall_mem_cons.2 ⟨subd11_2_346, List.forall_mem_cons.2 ⟨subd11_2_347, List.forall_mem_cons.2 ⟨subd11_2_348, List.forall_mem_cons.2 ⟨subd11_2_349, List.forall_mem_cons.2 ⟨subd11_2_350, List.forall_mem_cons.2 ⟨subd11_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_352 : subd11_2 [1, -2, -3] = true := by decide +kernel
theorem subd11_2_353 : subd11_2 [1, -2, -2] = true := by decide +kernel
theorem subd11_2_354 : subd11_2 [1, -2, -1] = true := by decide +kernel
theorem subd11_2_355 : subd11_2 [1, -2, 0] = true := by decide +kernel
theorem subd11_2_356 : subd11_2 [1, -2, 1] = true := by decide +kernel
theorem subd11_2_357 : subd11_2 [1, -2, 2] = true := by decide +kernel
theorem subd11_2_358 : subd11_2 [1, -2, 3] = true := by decide +kernel
theorem subd11_2_359 : subd11_2 [1, -2, 4] = true := by decide +kernel
theorem subd11_2_360 : subd11_2 [1, -2, 5] = true := by decide +kernel
theorem subd11_2_361 : subd11_2 [1, -2, 6] = true := by decide +kernel
theorem subd11_2_362 : subd11_2 [1, -2, 7] = true := by decide +kernel
theorem subd11_2_363 : subd11_2 [1, -2, 8] = true := by decide +kernel
theorem subd11_2_364 : subd11_2 [1, -1, -9] = true := by decide +kernel
theorem subd11_2_365 : subd11_2 [1, -1, -8] = true := by decide +kernel
theorem subd11_2_366 : subd11_2 [1, -1, -7] = true := by decide +kernel
theorem subd11_2_367 : subd11_2 [1, -1, -6] = true := by decide +kernel
theorem subd11_2_368 : subd11_2 [1, -1, -5] = true := by decide +kernel
theorem subd11_2_369 : subd11_2 [1, -1, -4] = true := by decide +kernel
theorem subd11_2_370 : subd11_2 [1, -1, -3] = true := by decide +kernel
theorem subd11_2_371 : subd11_2 [1, -1, -2] = true := by decide +kernel
theorem subd11_2_372 : subd11_2 [1, -1, -1] = true := by decide +kernel
theorem subd11_2_373 : subd11_2 [1, -1, 0] = true := by decide +kernel
theorem subd11_2_374 : subd11_2 [1, -1, 1] = true := by decide +kernel
theorem subd11_2_375 : subd11_2 [1, -1, 2] = true := by decide +kernel
theorem subd11_2_376 : subd11_2 [1, -1, 3] = true := by decide +kernel
theorem subd11_2_377 : subd11_2 [1, -1, 4] = true := by decide +kernel
theorem subd11_2_378 : subd11_2 [1, -1, 5] = true := by decide +kernel
theorem subd11_2_379 : subd11_2 [1, -1, 6] = true := by decide +kernel
theorem subd11_2_380 : subd11_2 [1, -1, 7] = true := by decide +kernel
theorem subd11_2_381 : subd11_2 [1, -1, 8] = true := by decide +kernel
theorem subd11_2_382 : subd11_2 [1, -1, 9] = true := by decide +kernel
theorem subd11_2_383 : subd11_2 [1, 0, -10] = true := by decide +kernel
theorem sbd11_2_11 : ∀ q ∈ blkd11_2_11, subd11_2 q = true := by
  unfold blkd11_2_11
  exact List.forall_mem_cons.2 ⟨subd11_2_352, List.forall_mem_cons.2 ⟨subd11_2_353, List.forall_mem_cons.2 ⟨subd11_2_354, List.forall_mem_cons.2 ⟨subd11_2_355, List.forall_mem_cons.2 ⟨subd11_2_356, List.forall_mem_cons.2 ⟨subd11_2_357, List.forall_mem_cons.2 ⟨subd11_2_358, List.forall_mem_cons.2 ⟨subd11_2_359, List.forall_mem_cons.2 ⟨subd11_2_360, List.forall_mem_cons.2 ⟨subd11_2_361, List.forall_mem_cons.2 ⟨subd11_2_362, List.forall_mem_cons.2 ⟨subd11_2_363, List.forall_mem_cons.2 ⟨subd11_2_364, List.forall_mem_cons.2 ⟨subd11_2_365, List.forall_mem_cons.2 ⟨subd11_2_366, List.forall_mem_cons.2 ⟨subd11_2_367, List.forall_mem_cons.2 ⟨subd11_2_368, List.forall_mem_cons.2 ⟨subd11_2_369, List.forall_mem_cons.2 ⟨subd11_2_370, List.forall_mem_cons.2 ⟨subd11_2_371, List.forall_mem_cons.2 ⟨subd11_2_372, List.forall_mem_cons.2 ⟨subd11_2_373, List.forall_mem_cons.2 ⟨subd11_2_374, List.forall_mem_cons.2 ⟨subd11_2_375, List.forall_mem_cons.2 ⟨subd11_2_376, List.forall_mem_cons.2 ⟨subd11_2_377, List.forall_mem_cons.2 ⟨subd11_2_378, List.forall_mem_cons.2 ⟨subd11_2_379, List.forall_mem_cons.2 ⟨subd11_2_380, List.forall_mem_cons.2 ⟨subd11_2_381, List.forall_mem_cons.2 ⟨subd11_2_382, List.forall_mem_cons.2 ⟨subd11_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_384 : subd11_2 [1, 0, -9] = true := by decide +kernel
theorem subd11_2_385 : subd11_2 [1, 0, -8] = true := by decide +kernel
theorem subd11_2_386 : subd11_2 [1, 0, -7] = true := by decide +kernel
theorem subd11_2_387 : subd11_2 [1, 0, -6] = true := by decide +kernel
theorem subd11_2_388 : subd11_2 [1, 0, -5] = true := by decide +kernel
theorem subd11_2_389 : subd11_2 [1, 0, -4] = true := by decide +kernel
theorem subd11_2_390 : subd11_2 [1, 0, -3] = true := by decide +kernel
theorem subd11_2_391 : subd11_2 [1, 0, -2] = true := by decide +kernel
theorem subd11_2_392 : subd11_2 [1, 0, -1] = true := by decide +kernel
theorem subd11_2_393 : subd11_2 [1, 0, 0] = true := by decide +kernel
theorem subd11_2_394 : subd11_2 [1, 0, 1] = true := by decide +kernel
theorem subd11_2_395 : subd11_2 [1, 0, 2] = true := by decide +kernel
theorem subd11_2_396 : subd11_2 [1, 0, 3] = true := by decide +kernel
theorem subd11_2_397 : subd11_2 [1, 0, 4] = true := by decide +kernel
theorem subd11_2_398 : subd11_2 [1, 0, 5] = true := by decide +kernel
theorem subd11_2_399 : subd11_2 [1, 0, 6] = true := by decide +kernel
theorem subd11_2_400 : subd11_2 [1, 0, 7] = true := by decide +kernel
theorem subd11_2_401 : subd11_2 [1, 0, 8] = true := by decide +kernel
theorem subd11_2_402 : subd11_2 [1, 0, 9] = true := by decide +kernel
theorem subd11_2_403 : subd11_2 [1, 1, -9] = true := by decide +kernel
theorem subd11_2_404 : subd11_2 [1, 1, -8] = true := by decide +kernel
theorem subd11_2_405 : subd11_2 [1, 1, -7] = true := by decide +kernel
theorem subd11_2_406 : subd11_2 [1, 1, -6] = true := by decide +kernel
theorem subd11_2_407 : subd11_2 [1, 1, -5] = true := by decide +kernel
theorem subd11_2_408 : subd11_2 [1, 1, -4] = true := by decide +kernel
theorem subd11_2_409 : subd11_2 [1, 1, -3] = true := by decide +kernel
theorem subd11_2_410 : subd11_2 [1, 1, -2] = true := by decide +kernel
theorem subd11_2_411 : subd11_2 [1, 1, -1] = true := by decide +kernel
theorem subd11_2_412 : subd11_2 [1, 1, 0] = true := by decide +kernel
theorem subd11_2_413 : subd11_2 [1, 1, 1] = true := by decide +kernel
theorem subd11_2_414 : subd11_2 [1, 1, 2] = true := by decide +kernel
theorem subd11_2_415 : subd11_2 [1, 1, 3] = true := by decide +kernel
theorem sbd11_2_12 : ∀ q ∈ blkd11_2_12, subd11_2 q = true := by
  unfold blkd11_2_12
  exact List.forall_mem_cons.2 ⟨subd11_2_384, List.forall_mem_cons.2 ⟨subd11_2_385, List.forall_mem_cons.2 ⟨subd11_2_386, List.forall_mem_cons.2 ⟨subd11_2_387, List.forall_mem_cons.2 ⟨subd11_2_388, List.forall_mem_cons.2 ⟨subd11_2_389, List.forall_mem_cons.2 ⟨subd11_2_390, List.forall_mem_cons.2 ⟨subd11_2_391, List.forall_mem_cons.2 ⟨subd11_2_392, List.forall_mem_cons.2 ⟨subd11_2_393, List.forall_mem_cons.2 ⟨subd11_2_394, List.forall_mem_cons.2 ⟨subd11_2_395, List.forall_mem_cons.2 ⟨subd11_2_396, List.forall_mem_cons.2 ⟨subd11_2_397, List.forall_mem_cons.2 ⟨subd11_2_398, List.forall_mem_cons.2 ⟨subd11_2_399, List.forall_mem_cons.2 ⟨subd11_2_400, List.forall_mem_cons.2 ⟨subd11_2_401, List.forall_mem_cons.2 ⟨subd11_2_402, List.forall_mem_cons.2 ⟨subd11_2_403, List.forall_mem_cons.2 ⟨subd11_2_404, List.forall_mem_cons.2 ⟨subd11_2_405, List.forall_mem_cons.2 ⟨subd11_2_406, List.forall_mem_cons.2 ⟨subd11_2_407, List.forall_mem_cons.2 ⟨subd11_2_408, List.forall_mem_cons.2 ⟨subd11_2_409, List.forall_mem_cons.2 ⟨subd11_2_410, List.forall_mem_cons.2 ⟨subd11_2_411, List.forall_mem_cons.2 ⟨subd11_2_412, List.forall_mem_cons.2 ⟨subd11_2_413, List.forall_mem_cons.2 ⟨subd11_2_414, List.forall_mem_cons.2 ⟨subd11_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
