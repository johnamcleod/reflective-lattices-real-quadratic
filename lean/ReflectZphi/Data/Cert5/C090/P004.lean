import ReflectZphi.Data.Cert5.C090.Base

namespace ReflectZphi.Data.Cert5.C090

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [-1, -2] = true := by decide +kernel
theorem subd3_5_1 : subd3_5 [-1, -1, -9] = true := by decide +kernel
theorem subd3_5_2 : subd3_5 [-1, -1, -8] = true := by decide +kernel
theorem subd3_5_3 : subd3_5 [-1, -1, -7] = true := by decide +kernel
theorem subd3_5_4 : subd3_5 [-1, -1, -6] = true := by decide +kernel
theorem subd3_5_5 : subd3_5 [-1, -1, -5] = true := by decide +kernel
theorem subd3_5_6 : subd3_5 [-1, -1, -4] = true := by decide +kernel
theorem subd3_5_7 : subd3_5 [-1, -1, -3] = true := by decide +kernel
theorem subd3_5_8 : subd3_5 [-1, -1, -2] = true := by decide +kernel
theorem subd3_5_9 : subd3_5 [-1, -1, -1] = true := by decide +kernel
theorem subd3_5_10 : subd3_5 [-1, -1, 0] = true := by decide +kernel
theorem subd3_5_11 : subd3_5 [-1, -1, 1] = true := by decide +kernel
theorem subd3_5_12 : subd3_5 [-1, -1, 2] = true := by decide +kernel
theorem subd3_5_13 : subd3_5 [-1, -1, 3] = true := by decide +kernel
theorem subd3_5_14 : subd3_5 [-1, -1, 4] = true := by decide +kernel
theorem subd3_5_15 : subd3_5 [-1, -1, 5] = true := by decide +kernel
theorem subd3_5_16 : subd3_5 [-1, -1, 6] = true := by decide +kernel
theorem subd3_5_17 : subd3_5 [-1, -1, 7] = true := by decide +kernel
theorem subd3_5_18 : subd3_5 [-1, -1, 8] = true := by decide +kernel
theorem subd3_5_19 : subd3_5 [-1, 0, -10] = true := by decide +kernel
theorem subd3_5_20 : subd3_5 [-1, 0, -9] = true := by decide +kernel
theorem subd3_5_21 : subd3_5 [-1, 0, -8] = true := by decide +kernel
theorem subd3_5_22 : subd3_5 [-1, 0, -7] = true := by decide +kernel
theorem subd3_5_23 : subd3_5 [-1, 0, -6] = true := by decide +kernel
theorem subd3_5_24 : subd3_5 [-1, 0, -5] = true := by decide +kernel
theorem subd3_5_25 : subd3_5 [-1, 0, -4] = true := by decide +kernel
theorem subd3_5_26 : subd3_5 [-1, 0, -3] = true := by decide +kernel
theorem subd3_5_27 : subd3_5 [-1, 0, -2] = true := by decide +kernel
theorem subd3_5_28 : subd3_5 [-1, 0, -1] = true := by decide +kernel
theorem subd3_5_29 : subd3_5 [-1, 0, 0] = true := by decide +kernel
theorem subd3_5_30 : subd3_5 [-1, 0, 1] = true := by decide +kernel
theorem subd3_5_31 : subd3_5 [-1, 0, 2] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_cons.2 ⟨subd3_5_1, List.forall_mem_cons.2 ⟨subd3_5_2, List.forall_mem_cons.2 ⟨subd3_5_3, List.forall_mem_cons.2 ⟨subd3_5_4, List.forall_mem_cons.2 ⟨subd3_5_5, List.forall_mem_cons.2 ⟨subd3_5_6, List.forall_mem_cons.2 ⟨subd3_5_7, List.forall_mem_cons.2 ⟨subd3_5_8, List.forall_mem_cons.2 ⟨subd3_5_9, List.forall_mem_cons.2 ⟨subd3_5_10, List.forall_mem_cons.2 ⟨subd3_5_11, List.forall_mem_cons.2 ⟨subd3_5_12, List.forall_mem_cons.2 ⟨subd3_5_13, List.forall_mem_cons.2 ⟨subd3_5_14, List.forall_mem_cons.2 ⟨subd3_5_15, List.forall_mem_cons.2 ⟨subd3_5_16, List.forall_mem_cons.2 ⟨subd3_5_17, List.forall_mem_cons.2 ⟨subd3_5_18, List.forall_mem_cons.2 ⟨subd3_5_19, List.forall_mem_cons.2 ⟨subd3_5_20, List.forall_mem_cons.2 ⟨subd3_5_21, List.forall_mem_cons.2 ⟨subd3_5_22, List.forall_mem_cons.2 ⟨subd3_5_23, List.forall_mem_cons.2 ⟨subd3_5_24, List.forall_mem_cons.2 ⟨subd3_5_25, List.forall_mem_cons.2 ⟨subd3_5_26, List.forall_mem_cons.2 ⟨subd3_5_27, List.forall_mem_cons.2 ⟨subd3_5_28, List.forall_mem_cons.2 ⟨subd3_5_29, List.forall_mem_cons.2 ⟨subd3_5_30, List.forall_mem_cons.2 ⟨subd3_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_32 : subd3_5 [-1, 0, 3] = true := by decide +kernel
theorem subd3_5_33 : subd3_5 [-1, 0, 4] = true := by decide +kernel
theorem subd3_5_34 : subd3_5 [-1, 0, 5] = true := by decide +kernel
theorem subd3_5_35 : subd3_5 [-1, 0, 6] = true := by decide +kernel
theorem subd3_5_36 : subd3_5 [-1, 0, 7] = true := by decide +kernel
theorem subd3_5_37 : subd3_5 [-1, 0, 8] = true := by decide +kernel
theorem subd3_5_38 : subd3_5 [-1, 0, 9] = true := by decide +kernel
theorem subd3_5_39 : subd3_5 [0, -2] = true := by decide +kernel
theorem subd3_5_40 : subd3_5 [0, -1, -11] = true := by decide +kernel
theorem subd3_5_41 : subd3_5 [0, -1, -10] = true := by decide +kernel
theorem subd3_5_42 : subd3_5 [0, -1, -9] = true := by decide +kernel
theorem subd3_5_43 : subd3_5 [0, -1, -8] = true := by decide +kernel
theorem subd3_5_44 : subd3_5 [0, -1, -7] = true := by decide +kernel
theorem subd3_5_45 : subd3_5 [0, -1, -6] = true := by decide +kernel
theorem subd3_5_46 : subd3_5 [0, -1, -5] = true := by decide +kernel
theorem subd3_5_47 : subd3_5 [0, -1, -4] = true := by decide +kernel
theorem subd3_5_48 : subd3_5 [0, -1, -3] = true := by decide +kernel
theorem subd3_5_49 : subd3_5 [0, -1, -2] = true := by decide +kernel
theorem subd3_5_50 : subd3_5 [0, -1, -1] = true := by decide +kernel
theorem subd3_5_51 : subd3_5 [0, -1, 0] = true := by decide +kernel
theorem subd3_5_52 : subd3_5 [0, -1, 1] = true := by decide +kernel
theorem subd3_5_53 : subd3_5 [0, -1, 2] = true := by decide +kernel
theorem subd3_5_54 : subd3_5 [0, -1, 3] = true := by decide +kernel
theorem subd3_5_55 : subd3_5 [0, -1, 4] = true := by decide +kernel
theorem subd3_5_56 : subd3_5 [0, -1, 5] = true := by decide +kernel
theorem subd3_5_57 : subd3_5 [0, -1, 6] = true := by decide +kernel
theorem subd3_5_58 : subd3_5 [0, -1, 7] = true := by decide +kernel
theorem subd3_5_59 : subd3_5 [0, -1, 8] = true := by decide +kernel
theorem subd3_5_60 : subd3_5 [0, -1, 9] = true := by decide +kernel
theorem subd3_5_61 : subd3_5 [0, -1, 10] = true := by decide +kernel
theorem subd3_5_62 : subd3_5 [0, 0, -13] = true := by decide +kernel
theorem subd3_5_63 : subd3_5 [0, 0, -12] = true := by decide +kernel
theorem sbd3_5_1 : ∀ q ∈ blkd3_5_1, subd3_5 q = true := by
  unfold blkd3_5_1
  exact List.forall_mem_cons.2 ⟨subd3_5_32, List.forall_mem_cons.2 ⟨subd3_5_33, List.forall_mem_cons.2 ⟨subd3_5_34, List.forall_mem_cons.2 ⟨subd3_5_35, List.forall_mem_cons.2 ⟨subd3_5_36, List.forall_mem_cons.2 ⟨subd3_5_37, List.forall_mem_cons.2 ⟨subd3_5_38, List.forall_mem_cons.2 ⟨subd3_5_39, List.forall_mem_cons.2 ⟨subd3_5_40, List.forall_mem_cons.2 ⟨subd3_5_41, List.forall_mem_cons.2 ⟨subd3_5_42, List.forall_mem_cons.2 ⟨subd3_5_43, List.forall_mem_cons.2 ⟨subd3_5_44, List.forall_mem_cons.2 ⟨subd3_5_45, List.forall_mem_cons.2 ⟨subd3_5_46, List.forall_mem_cons.2 ⟨subd3_5_47, List.forall_mem_cons.2 ⟨subd3_5_48, List.forall_mem_cons.2 ⟨subd3_5_49, List.forall_mem_cons.2 ⟨subd3_5_50, List.forall_mem_cons.2 ⟨subd3_5_51, List.forall_mem_cons.2 ⟨subd3_5_52, List.forall_mem_cons.2 ⟨subd3_5_53, List.forall_mem_cons.2 ⟨subd3_5_54, List.forall_mem_cons.2 ⟨subd3_5_55, List.forall_mem_cons.2 ⟨subd3_5_56, List.forall_mem_cons.2 ⟨subd3_5_57, List.forall_mem_cons.2 ⟨subd3_5_58, List.forall_mem_cons.2 ⟨subd3_5_59, List.forall_mem_cons.2 ⟨subd3_5_60, List.forall_mem_cons.2 ⟨subd3_5_61, List.forall_mem_cons.2 ⟨subd3_5_62, List.forall_mem_cons.2 ⟨subd3_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_64 : subd3_5 [0, 0, -11] = true := by decide +kernel
theorem subd3_5_65 : subd3_5 [0, 0, -10] = true := by decide +kernel
theorem subd3_5_66 : subd3_5 [0, 0, -9] = true := by decide +kernel
theorem subd3_5_67 : subd3_5 [0, 0, -8] = true := by decide +kernel
theorem subd3_5_68 : subd3_5 [0, 0, -7] = true := by decide +kernel
theorem subd3_5_69 : subd3_5 [0, 0, -6] = true := by decide +kernel
theorem subd3_5_70 : subd3_5 [0, 0, -5] = true := by decide +kernel
theorem subd3_5_71 : subd3_5 [0, 0, -4] = true := by decide +kernel
theorem subd3_5_72 : subd3_5 [0, 0, -3] = true := by decide +kernel
theorem subd3_5_73 : subd3_5 [0, 0, -2] = true := by decide +kernel
theorem subd3_5_74 : subd3_5 [0, 0, -1] = true := by decide +kernel
theorem subd3_5_75 : subd3_5 [0, 0, 0] = true := by decide +kernel
theorem subd3_5_76 : subd3_5 [0, 0, 1] = true := by decide +kernel
theorem subd3_5_77 : subd3_5 [0, 0, 2] = true := by decide +kernel
theorem subd3_5_78 : subd3_5 [0, 0, 3] = true := by decide +kernel
theorem subd3_5_79 : subd3_5 [0, 0, 4] = true := by decide +kernel
theorem subd3_5_80 : subd3_5 [0, 0, 5] = true := by decide +kernel
theorem subd3_5_81 : subd3_5 [0, 0, 6] = true := by decide +kernel
theorem subd3_5_82 : subd3_5 [0, 0, 7] = true := by decide +kernel
theorem subd3_5_83 : subd3_5 [0, 0, 8] = true := by decide +kernel
theorem subd3_5_84 : subd3_5 [0, 0, 9] = true := by decide +kernel
theorem subd3_5_85 : subd3_5 [0, 0, 10] = true := by decide +kernel
theorem subd3_5_86 : subd3_5 [0, 0, 11] = true := by decide +kernel
theorem subd3_5_87 : subd3_5 [0, 0, 12] = true := by decide +kernel
theorem subd3_5_88 : subd3_5 [0, 1, -11] = true := by decide +kernel
theorem subd3_5_89 : subd3_5 [0, 1, -10] = true := by decide +kernel
theorem subd3_5_90 : subd3_5 [0, 1, -9] = true := by decide +kernel
theorem subd3_5_91 : subd3_5 [0, 1, -8] = true := by decide +kernel
theorem subd3_5_92 : subd3_5 [0, 1, -7] = true := by decide +kernel
theorem subd3_5_93 : subd3_5 [0, 1, -6] = true := by decide +kernel
theorem subd3_5_94 : subd3_5 [0, 1, -5] = true := by decide +kernel
theorem subd3_5_95 : subd3_5 [0, 1, -4] = true := by decide +kernel
theorem sbd3_5_2 : ∀ q ∈ blkd3_5_2, subd3_5 q = true := by
  unfold blkd3_5_2
  exact List.forall_mem_cons.2 ⟨subd3_5_64, List.forall_mem_cons.2 ⟨subd3_5_65, List.forall_mem_cons.2 ⟨subd3_5_66, List.forall_mem_cons.2 ⟨subd3_5_67, List.forall_mem_cons.2 ⟨subd3_5_68, List.forall_mem_cons.2 ⟨subd3_5_69, List.forall_mem_cons.2 ⟨subd3_5_70, List.forall_mem_cons.2 ⟨subd3_5_71, List.forall_mem_cons.2 ⟨subd3_5_72, List.forall_mem_cons.2 ⟨subd3_5_73, List.forall_mem_cons.2 ⟨subd3_5_74, List.forall_mem_cons.2 ⟨subd3_5_75, List.forall_mem_cons.2 ⟨subd3_5_76, List.forall_mem_cons.2 ⟨subd3_5_77, List.forall_mem_cons.2 ⟨subd3_5_78, List.forall_mem_cons.2 ⟨subd3_5_79, List.forall_mem_cons.2 ⟨subd3_5_80, List.forall_mem_cons.2 ⟨subd3_5_81, List.forall_mem_cons.2 ⟨subd3_5_82, List.forall_mem_cons.2 ⟨subd3_5_83, List.forall_mem_cons.2 ⟨subd3_5_84, List.forall_mem_cons.2 ⟨subd3_5_85, List.forall_mem_cons.2 ⟨subd3_5_86, List.forall_mem_cons.2 ⟨subd3_5_87, List.forall_mem_cons.2 ⟨subd3_5_88, List.forall_mem_cons.2 ⟨subd3_5_89, List.forall_mem_cons.2 ⟨subd3_5_90, List.forall_mem_cons.2 ⟨subd3_5_91, List.forall_mem_cons.2 ⟨subd3_5_92, List.forall_mem_cons.2 ⟨subd3_5_93, List.forall_mem_cons.2 ⟨subd3_5_94, List.forall_mem_cons.2 ⟨subd3_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_96 : subd3_5 [0, 1, -3] = true := by decide +kernel
theorem subd3_5_97 : subd3_5 [0, 1, -2] = true := by decide +kernel
theorem subd3_5_98 : subd3_5 [0, 1, -1] = true := by decide +kernel
theorem subd3_5_99 : subd3_5 [0, 1, 0] = true := by decide +kernel
theorem subd3_5_100 : subd3_5 [0, 1, 1] = true := by decide +kernel
theorem subd3_5_101 : subd3_5 [0, 1, 2] = true := by decide +kernel
theorem subd3_5_102 : subd3_5 [0, 1, 3] = true := by decide +kernel
theorem subd3_5_103 : subd3_5 [0, 1, 4] = true := by decide +kernel
theorem subd3_5_104 : subd3_5 [0, 1, 5] = true := by decide +kernel
theorem subd3_5_105 : subd3_5 [0, 1, 6] = true := by decide +kernel
theorem subd3_5_106 : subd3_5 [0, 1, 7] = true := by decide +kernel
theorem subd3_5_107 : subd3_5 [0, 1, 8] = true := by decide +kernel
theorem subd3_5_108 : subd3_5 [0, 1, 9] = true := by decide +kernel
theorem subd3_5_109 : subd3_5 [0, 1, 10] = true := by decide +kernel
theorem subd3_5_110 : subd3_5 [1, -1] = true := by decide +kernel
theorem subd3_5_111 : subd3_5 [1, 0, -10] = true := by decide +kernel
theorem subd3_5_112 : subd3_5 [1, 0, -9] = true := by decide +kernel
theorem subd3_5_113 : subd3_5 [1, 0, -8] = true := by decide +kernel
theorem subd3_5_114 : subd3_5 [1, 0, -7] = true := by decide +kernel
theorem subd3_5_115 : subd3_5 [1, 0, -6] = true := by decide +kernel
theorem subd3_5_116 : subd3_5 [1, 0, -5] = true := by decide +kernel
theorem subd3_5_117 : subd3_5 [1, 0, -4] = true := by decide +kernel
theorem subd3_5_118 : subd3_5 [1, 0, -3] = true := by decide +kernel
theorem subd3_5_119 : subd3_5 [1, 0, -2] = true := by decide +kernel
theorem subd3_5_120 : subd3_5 [1, 0, -1] = true := by decide +kernel
theorem subd3_5_121 : subd3_5 [1, 0, 0] = true := by decide +kernel
theorem subd3_5_122 : subd3_5 [1, 0, 1] = true := by decide +kernel
theorem subd3_5_123 : subd3_5 [1, 0, 2] = true := by decide +kernel
theorem subd3_5_124 : subd3_5 [1, 0, 3] = true := by decide +kernel
theorem subd3_5_125 : subd3_5 [1, 0, 4] = true := by decide +kernel
theorem subd3_5_126 : subd3_5 [1, 0, 5] = true := by decide +kernel
theorem subd3_5_127 : subd3_5 [1, 0, 6] = true := by decide +kernel
theorem sbd3_5_3 : ∀ q ∈ blkd3_5_3, subd3_5 q = true := by
  unfold blkd3_5_3
  exact List.forall_mem_cons.2 ⟨subd3_5_96, List.forall_mem_cons.2 ⟨subd3_5_97, List.forall_mem_cons.2 ⟨subd3_5_98, List.forall_mem_cons.2 ⟨subd3_5_99, List.forall_mem_cons.2 ⟨subd3_5_100, List.forall_mem_cons.2 ⟨subd3_5_101, List.forall_mem_cons.2 ⟨subd3_5_102, List.forall_mem_cons.2 ⟨subd3_5_103, List.forall_mem_cons.2 ⟨subd3_5_104, List.forall_mem_cons.2 ⟨subd3_5_105, List.forall_mem_cons.2 ⟨subd3_5_106, List.forall_mem_cons.2 ⟨subd3_5_107, List.forall_mem_cons.2 ⟨subd3_5_108, List.forall_mem_cons.2 ⟨subd3_5_109, List.forall_mem_cons.2 ⟨subd3_5_110, List.forall_mem_cons.2 ⟨subd3_5_111, List.forall_mem_cons.2 ⟨subd3_5_112, List.forall_mem_cons.2 ⟨subd3_5_113, List.forall_mem_cons.2 ⟨subd3_5_114, List.forall_mem_cons.2 ⟨subd3_5_115, List.forall_mem_cons.2 ⟨subd3_5_116, List.forall_mem_cons.2 ⟨subd3_5_117, List.forall_mem_cons.2 ⟨subd3_5_118, List.forall_mem_cons.2 ⟨subd3_5_119, List.forall_mem_cons.2 ⟨subd3_5_120, List.forall_mem_cons.2 ⟨subd3_5_121, List.forall_mem_cons.2 ⟨subd3_5_122, List.forall_mem_cons.2 ⟨subd3_5_123, List.forall_mem_cons.2 ⟨subd3_5_124, List.forall_mem_cons.2 ⟨subd3_5_125, List.forall_mem_cons.2 ⟨subd3_5_126, List.forall_mem_cons.2 ⟨subd3_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_128 : subd3_5 [1, 0, 7] = true := by decide +kernel
theorem subd3_5_129 : subd3_5 [1, 0, 8] = true := by decide +kernel
theorem subd3_5_130 : subd3_5 [1, 0, 9] = true := by decide +kernel
theorem subd3_5_131 : subd3_5 [1, 1, -9] = true := by decide +kernel
theorem subd3_5_132 : subd3_5 [1, 1, -8] = true := by decide +kernel
theorem subd3_5_133 : subd3_5 [1, 1, -7] = true := by decide +kernel
theorem subd3_5_134 : subd3_5 [1, 1, -6] = true := by decide +kernel
theorem subd3_5_135 : subd3_5 [1, 1, -5] = true := by decide +kernel
theorem subd3_5_136 : subd3_5 [1, 1, -4] = true := by decide +kernel
theorem subd3_5_137 : subd3_5 [1, 1, -3] = true := by decide +kernel
theorem subd3_5_138 : subd3_5 [1, 1, -2] = true := by decide +kernel
theorem subd3_5_139 : subd3_5 [1, 1, -1] = true := by decide +kernel
theorem subd3_5_140 : subd3_5 [1, 1, 0] = true := by decide +kernel
theorem subd3_5_141 : subd3_5 [1, 1, 1] = true := by decide +kernel
theorem subd3_5_142 : subd3_5 [1, 1, 2] = true := by decide +kernel
theorem subd3_5_143 : subd3_5 [1, 1, 3] = true := by decide +kernel
theorem subd3_5_144 : subd3_5 [1, 1, 4] = true := by decide +kernel
theorem subd3_5_145 : subd3_5 [1, 1, 5] = true := by decide +kernel
theorem subd3_5_146 : subd3_5 [1, 1, 6] = true := by decide +kernel
theorem subd3_5_147 : subd3_5 [1, 1, 7] = true := by decide +kernel
theorem subd3_5_148 : subd3_5 [1, 1, 8] = true := by decide +kernel
theorem sbd3_5_4 : ∀ q ∈ blkd3_5_4, subd3_5 q = true := by
  unfold blkd3_5_4
  exact List.forall_mem_cons.2 ⟨subd3_5_128, List.forall_mem_cons.2 ⟨subd3_5_129, List.forall_mem_cons.2 ⟨subd3_5_130, List.forall_mem_cons.2 ⟨subd3_5_131, List.forall_mem_cons.2 ⟨subd3_5_132, List.forall_mem_cons.2 ⟨subd3_5_133, List.forall_mem_cons.2 ⟨subd3_5_134, List.forall_mem_cons.2 ⟨subd3_5_135, List.forall_mem_cons.2 ⟨subd3_5_136, List.forall_mem_cons.2 ⟨subd3_5_137, List.forall_mem_cons.2 ⟨subd3_5_138, List.forall_mem_cons.2 ⟨subd3_5_139, List.forall_mem_cons.2 ⟨subd3_5_140, List.forall_mem_cons.2 ⟨subd3_5_141, List.forall_mem_cons.2 ⟨subd3_5_142, List.forall_mem_cons.2 ⟨subd3_5_143, List.forall_mem_cons.2 ⟨subd3_5_144, List.forall_mem_cons.2 ⟨subd3_5_145, List.forall_mem_cons.2 ⟨subd3_5_146, List.forall_mem_cons.2 ⟨subd3_5_147, List.forall_mem_cons.2 ⟨subd3_5_148, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel
theorem subd3_6_0 : subd3_6 [-2] = true := by decide +kernel
theorem subd3_6_1 : subd3_6 [-1] = true := by decide +kernel
theorem subd3_6_2 : subd3_6 [0] = true := by decide +kernel
theorem subd3_6_3 : subd3_6 [1] = true := by decide +kernel
theorem subd3_6_4 : subd3_6 [2] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_cons.2 ⟨subd3_6_1, List.forall_mem_cons.2 ⟨subd3_6_2, List.forall_mem_cons.2 ⟨subd3_6_3, List.forall_mem_cons.2 ⟨subd3_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [-1, -2] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [-1, -1] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [-1, 0] = true := by decide +kernel
theorem subd3_7_3 : subd3_7 [-1, 1] = true := by decide +kernel
theorem subd3_7_4 : subd3_7 [0, -3] = true := by decide +kernel
theorem subd3_7_5 : subd3_7 [0, -2] = true := by decide +kernel
theorem subd3_7_6 : subd3_7 [0, -1] = true := by decide +kernel
theorem subd3_7_7 : subd3_7 [0, 0] = true := by decide +kernel
theorem subd3_7_8 : subd3_7 [0, 1] = true := by decide +kernel
theorem subd3_7_9 : subd3_7 [0, 2] = true := by decide +kernel
theorem subd3_7_10 : subd3_7 [1, -2] = true := by decide +kernel
theorem subd3_7_11 : subd3_7 [1, -1] = true := by decide +kernel
theorem subd3_7_12 : subd3_7 [1, 0] = true := by decide +kernel
theorem subd3_7_13 : subd3_7 [1, 1] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_cons.2 ⟨subd3_7_3, List.forall_mem_cons.2 ⟨subd3_7_4, List.forall_mem_cons.2 ⟨subd3_7_5, List.forall_mem_cons.2 ⟨subd3_7_6, List.forall_mem_cons.2 ⟨subd3_7_7, List.forall_mem_cons.2 ⟨subd3_7_8, List.forall_mem_cons.2 ⟨subd3_7_9, List.forall_mem_cons.2 ⟨subd3_7_10, List.forall_mem_cons.2 ⟨subd3_7_11, List.forall_mem_cons.2 ⟨subd3_7_12, List.forall_mem_cons.2 ⟨subd3_7_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [0] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C090
