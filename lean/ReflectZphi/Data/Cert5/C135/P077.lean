import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-1, -3] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-1, -1, -10] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-1, -1, -9] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-1, -1, -8] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-1, -1, -7] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-1, -1, -6] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [-1, -1, -5] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [-1, -1, -4] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [-1, -1, -3] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [-1, -1, -2] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [-1, -1, -1] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [-1, -1, 0] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [-1, -1, 1] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [-1, -1, 2] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [-1, -1, 3] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [-1, -1, 4] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [-1, -1, 5] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [-1, -1, 6] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [-1, -1, 7] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [-1, -1, 8] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [-1, 0, -10] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [-1, 0, -9] = true := by decide +kernel
theorem subd12_1_24 : subd12_1 [-1, 0, -8] = true := by decide +kernel
theorem subd12_1_25 : subd12_1 [-1, 0, -7] = true := by decide +kernel
theorem subd12_1_26 : subd12_1 [-1, 0, -6] = true := by decide +kernel
theorem subd12_1_27 : subd12_1 [-1, 0, -5] = true := by decide +kernel
theorem subd12_1_28 : subd12_1 [-1, 0, -4] = true := by decide +kernel
theorem subd12_1_29 : subd12_1 [-1, 0, -3] = true := by decide +kernel
theorem subd12_1_30 : subd12_1 [-1, 0, -2] = true := by decide +kernel
theorem subd12_1_31 : subd12_1 [-1, 0, -1] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_cons.2 ⟨subd12_1_24, List.forall_mem_cons.2 ⟨subd12_1_25, List.forall_mem_cons.2 ⟨subd12_1_26, List.forall_mem_cons.2 ⟨subd12_1_27, List.forall_mem_cons.2 ⟨subd12_1_28, List.forall_mem_cons.2 ⟨subd12_1_29, List.forall_mem_cons.2 ⟨subd12_1_30, List.forall_mem_cons.2 ⟨subd12_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_32 : subd12_1 [-1, 0, 0] = true := by decide +kernel
theorem subd12_1_33 : subd12_1 [-1, 0, 1] = true := by decide +kernel
theorem subd12_1_34 : subd12_1 [-1, 0, 2] = true := by decide +kernel
theorem subd12_1_35 : subd12_1 [-1, 0, 3] = true := by decide +kernel
theorem subd12_1_36 : subd12_1 [-1, 0, 4] = true := by decide +kernel
theorem subd12_1_37 : subd12_1 [-1, 0, 5] = true := by decide +kernel
theorem subd12_1_38 : subd12_1 [-1, 0, 6] = true := by decide +kernel
theorem subd12_1_39 : subd12_1 [-1, 0, 7] = true := by decide +kernel
theorem subd12_1_40 : subd12_1 [-1, 0, 8] = true := by decide +kernel
theorem subd12_1_41 : subd12_1 [-1, 0, 9] = true := by decide +kernel
theorem subd12_1_42 : subd12_1 [-1, 1, -9] = true := by decide +kernel
theorem subd12_1_43 : subd12_1 [-1, 1, -8] = true := by decide +kernel
theorem subd12_1_44 : subd12_1 [-1, 1, -7] = true := by decide +kernel
theorem subd12_1_45 : subd12_1 [-1, 1, -6] = true := by decide +kernel
theorem subd12_1_46 : subd12_1 [-1, 1, -5] = true := by decide +kernel
theorem subd12_1_47 : subd12_1 [-1, 1, -4] = true := by decide +kernel
theorem subd12_1_48 : subd12_1 [-1, 1, -3] = true := by decide +kernel
theorem subd12_1_49 : subd12_1 [-1, 1, -2] = true := by decide +kernel
theorem subd12_1_50 : subd12_1 [-1, 1, -1] = true := by decide +kernel
theorem subd12_1_51 : subd12_1 [-1, 1, 0] = true := by decide +kernel
theorem subd12_1_52 : subd12_1 [-1, 1, 1] = true := by decide +kernel
theorem subd12_1_53 : subd12_1 [-1, 1, 2] = true := by decide +kernel
theorem subd12_1_54 : subd12_1 [-1, 1, 3] = true := by decide +kernel
theorem subd12_1_55 : subd12_1 [-1, 1, 4] = true := by decide +kernel
theorem subd12_1_56 : subd12_1 [-1, 1, 5] = true := by decide +kernel
theorem subd12_1_57 : subd12_1 [-1, 1, 6] = true := by decide +kernel
theorem subd12_1_58 : subd12_1 [-1, 1, 7] = true := by decide +kernel
theorem subd12_1_59 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_60 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_61 : subd12_1 [0, -1, -10] = true := by decide +kernel
theorem subd12_1_62 : subd12_1 [0, -1, -9] = true := by decide +kernel
theorem subd12_1_63 : subd12_1 [0, -1, -8] = true := by decide +kernel
theorem sbd12_1_1 : ∀ q ∈ blkd12_1_1, subd12_1 q = true := by
  unfold blkd12_1_1
  exact List.forall_mem_cons.2 ⟨subd12_1_32, List.forall_mem_cons.2 ⟨subd12_1_33, List.forall_mem_cons.2 ⟨subd12_1_34, List.forall_mem_cons.2 ⟨subd12_1_35, List.forall_mem_cons.2 ⟨subd12_1_36, List.forall_mem_cons.2 ⟨subd12_1_37, List.forall_mem_cons.2 ⟨subd12_1_38, List.forall_mem_cons.2 ⟨subd12_1_39, List.forall_mem_cons.2 ⟨subd12_1_40, List.forall_mem_cons.2 ⟨subd12_1_41, List.forall_mem_cons.2 ⟨subd12_1_42, List.forall_mem_cons.2 ⟨subd12_1_43, List.forall_mem_cons.2 ⟨subd12_1_44, List.forall_mem_cons.2 ⟨subd12_1_45, List.forall_mem_cons.2 ⟨subd12_1_46, List.forall_mem_cons.2 ⟨subd12_1_47, List.forall_mem_cons.2 ⟨subd12_1_48, List.forall_mem_cons.2 ⟨subd12_1_49, List.forall_mem_cons.2 ⟨subd12_1_50, List.forall_mem_cons.2 ⟨subd12_1_51, List.forall_mem_cons.2 ⟨subd12_1_52, List.forall_mem_cons.2 ⟨subd12_1_53, List.forall_mem_cons.2 ⟨subd12_1_54, List.forall_mem_cons.2 ⟨subd12_1_55, List.forall_mem_cons.2 ⟨subd12_1_56, List.forall_mem_cons.2 ⟨subd12_1_57, List.forall_mem_cons.2 ⟨subd12_1_58, List.forall_mem_cons.2 ⟨subd12_1_59, List.forall_mem_cons.2 ⟨subd12_1_60, List.forall_mem_cons.2 ⟨subd12_1_61, List.forall_mem_cons.2 ⟨subd12_1_62, List.forall_mem_cons.2 ⟨subd12_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_64 : subd12_1 [0, -1, -7] = true := by decide +kernel
theorem subd12_1_65 : subd12_1 [0, -1, -6] = true := by decide +kernel
theorem subd12_1_66 : subd12_1 [0, -1, -5] = true := by decide +kernel
theorem subd12_1_67 : subd12_1 [0, -1, -4] = true := by decide +kernel
theorem subd12_1_68 : subd12_1 [0, -1, -3] = true := by decide +kernel
theorem subd12_1_69 : subd12_1 [0, -1, -2] = true := by decide +kernel
theorem subd12_1_70 : subd12_1 [0, -1, -1] = true := by decide +kernel
theorem subd12_1_71 : subd12_1 [0, -1, 0] = true := by decide +kernel
theorem subd12_1_72 : subd12_1 [0, -1, 1] = true := by decide +kernel
theorem subd12_1_73 : subd12_1 [0, -1, 2] = true := by decide +kernel
theorem subd12_1_74 : subd12_1 [0, -1, 3] = true := by decide +kernel
theorem subd12_1_75 : subd12_1 [0, -1, 4] = true := by decide +kernel
theorem subd12_1_76 : subd12_1 [0, -1, 5] = true := by decide +kernel
theorem subd12_1_77 : subd12_1 [0, -1, 6] = true := by decide +kernel
theorem subd12_1_78 : subd12_1 [0, -1, 7] = true := by decide +kernel
theorem subd12_1_79 : subd12_1 [0, -1, 8] = true := by decide +kernel
theorem subd12_1_80 : subd12_1 [0, -1, 9] = true := by decide +kernel
theorem subd12_1_81 : subd12_1 [0, 0, -11] = true := by decide +kernel
theorem subd12_1_82 : subd12_1 [0, 0, -10] = true := by decide +kernel
theorem subd12_1_83 : subd12_1 [0, 0, -9] = true := by decide +kernel
theorem subd12_1_84 : subd12_1 [0, 0, -8] = true := by decide +kernel
theorem subd12_1_85 : subd12_1 [0, 0, -7] = true := by decide +kernel
theorem subd12_1_86 : subd12_1 [0, 0, -6] = true := by decide +kernel
theorem subd12_1_87 : subd12_1 [0, 0, -5] = true := by decide +kernel
theorem subd12_1_88 : subd12_1 [0, 0, -4] = true := by decide +kernel
theorem subd12_1_89 : subd12_1 [0, 0, -3] = true := by decide +kernel
theorem subd12_1_90 : subd12_1 [0, 0, -2] = true := by decide +kernel
theorem subd12_1_91 : subd12_1 [0, 0, -1] = true := by decide +kernel
theorem subd12_1_92 : subd12_1 [0, 0, 0] = true := by decide +kernel
theorem subd12_1_93 : subd12_1 [0, 0, 1] = true := by decide +kernel
theorem subd12_1_94 : subd12_1 [0, 0, 2] = true := by decide +kernel
theorem subd12_1_95 : subd12_1 [0, 0, 3] = true := by decide +kernel
theorem sbd12_1_2 : ∀ q ∈ blkd12_1_2, subd12_1 q = true := by
  unfold blkd12_1_2
  exact List.forall_mem_cons.2 ⟨subd12_1_64, List.forall_mem_cons.2 ⟨subd12_1_65, List.forall_mem_cons.2 ⟨subd12_1_66, List.forall_mem_cons.2 ⟨subd12_1_67, List.forall_mem_cons.2 ⟨subd12_1_68, List.forall_mem_cons.2 ⟨subd12_1_69, List.forall_mem_cons.2 ⟨subd12_1_70, List.forall_mem_cons.2 ⟨subd12_1_71, List.forall_mem_cons.2 ⟨subd12_1_72, List.forall_mem_cons.2 ⟨subd12_1_73, List.forall_mem_cons.2 ⟨subd12_1_74, List.forall_mem_cons.2 ⟨subd12_1_75, List.forall_mem_cons.2 ⟨subd12_1_76, List.forall_mem_cons.2 ⟨subd12_1_77, List.forall_mem_cons.2 ⟨subd12_1_78, List.forall_mem_cons.2 ⟨subd12_1_79, List.forall_mem_cons.2 ⟨subd12_1_80, List.forall_mem_cons.2 ⟨subd12_1_81, List.forall_mem_cons.2 ⟨subd12_1_82, List.forall_mem_cons.2 ⟨subd12_1_83, List.forall_mem_cons.2 ⟨subd12_1_84, List.forall_mem_cons.2 ⟨subd12_1_85, List.forall_mem_cons.2 ⟨subd12_1_86, List.forall_mem_cons.2 ⟨subd12_1_87, List.forall_mem_cons.2 ⟨subd12_1_88, List.forall_mem_cons.2 ⟨subd12_1_89, List.forall_mem_cons.2 ⟨subd12_1_90, List.forall_mem_cons.2 ⟨subd12_1_91, List.forall_mem_cons.2 ⟨subd12_1_92, List.forall_mem_cons.2 ⟨subd12_1_93, List.forall_mem_cons.2 ⟨subd12_1_94, List.forall_mem_cons.2 ⟨subd12_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_96 : subd12_1 [0, 0, 4] = true := by decide +kernel
theorem subd12_1_97 : subd12_1 [0, 0, 5] = true := by decide +kernel
theorem subd12_1_98 : subd12_1 [0, 0, 6] = true := by decide +kernel
theorem subd12_1_99 : subd12_1 [0, 0, 7] = true := by decide +kernel
theorem subd12_1_100 : subd12_1 [0, 0, 8] = true := by decide +kernel
theorem subd12_1_101 : subd12_1 [0, 0, 9] = true := by decide +kernel
theorem subd12_1_102 : subd12_1 [0, 0, 10] = true := by decide +kernel
theorem subd12_1_103 : subd12_1 [0, 1, -10] = true := by decide +kernel
theorem subd12_1_104 : subd12_1 [0, 1, -9] = true := by decide +kernel
theorem subd12_1_105 : subd12_1 [0, 1, -8] = true := by decide +kernel
theorem subd12_1_106 : subd12_1 [0, 1, -7] = true := by decide +kernel
theorem subd12_1_107 : subd12_1 [0, 1, -6] = true := by decide +kernel
theorem subd12_1_108 : subd12_1 [0, 1, -5] = true := by decide +kernel
theorem subd12_1_109 : subd12_1 [0, 1, -4] = true := by decide +kernel
theorem subd12_1_110 : subd12_1 [0, 1, -3] = true := by decide +kernel
theorem subd12_1_111 : subd12_1 [0, 1, -2] = true := by decide +kernel
theorem subd12_1_112 : subd12_1 [0, 1, -1] = true := by decide +kernel
theorem subd12_1_113 : subd12_1 [0, 1, 0] = true := by decide +kernel
theorem subd12_1_114 : subd12_1 [0, 1, 1] = true := by decide +kernel
theorem subd12_1_115 : subd12_1 [0, 1, 2] = true := by decide +kernel
theorem subd12_1_116 : subd12_1 [0, 1, 3] = true := by decide +kernel
theorem subd12_1_117 : subd12_1 [0, 1, 4] = true := by decide +kernel
theorem subd12_1_118 : subd12_1 [0, 1, 5] = true := by decide +kernel
theorem subd12_1_119 : subd12_1 [0, 1, 6] = true := by decide +kernel
theorem subd12_1_120 : subd12_1 [0, 1, 7] = true := by decide +kernel
theorem subd12_1_121 : subd12_1 [0, 1, 8] = true := by decide +kernel
theorem subd12_1_122 : subd12_1 [0, 1, 9] = true := by decide +kernel
theorem subd12_1_123 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_124 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_125 : subd12_1 [1, -1, -8] = true := by decide +kernel
theorem subd12_1_126 : subd12_1 [1, -1, -7] = true := by decide +kernel
theorem subd12_1_127 : subd12_1 [1, -1, -6] = true := by decide +kernel
theorem sbd12_1_3 : ∀ q ∈ blkd12_1_3, subd12_1 q = true := by
  unfold blkd12_1_3
  exact List.forall_mem_cons.2 ⟨subd12_1_96, List.forall_mem_cons.2 ⟨subd12_1_97, List.forall_mem_cons.2 ⟨subd12_1_98, List.forall_mem_cons.2 ⟨subd12_1_99, List.forall_mem_cons.2 ⟨subd12_1_100, List.forall_mem_cons.2 ⟨subd12_1_101, List.forall_mem_cons.2 ⟨subd12_1_102, List.forall_mem_cons.2 ⟨subd12_1_103, List.forall_mem_cons.2 ⟨subd12_1_104, List.forall_mem_cons.2 ⟨subd12_1_105, List.forall_mem_cons.2 ⟨subd12_1_106, List.forall_mem_cons.2 ⟨subd12_1_107, List.forall_mem_cons.2 ⟨subd12_1_108, List.forall_mem_cons.2 ⟨subd12_1_109, List.forall_mem_cons.2 ⟨subd12_1_110, List.forall_mem_cons.2 ⟨subd12_1_111, List.forall_mem_cons.2 ⟨subd12_1_112, List.forall_mem_cons.2 ⟨subd12_1_113, List.forall_mem_cons.2 ⟨subd12_1_114, List.forall_mem_cons.2 ⟨subd12_1_115, List.forall_mem_cons.2 ⟨subd12_1_116, List.forall_mem_cons.2 ⟨subd12_1_117, List.forall_mem_cons.2 ⟨subd12_1_118, List.forall_mem_cons.2 ⟨subd12_1_119, List.forall_mem_cons.2 ⟨subd12_1_120, List.forall_mem_cons.2 ⟨subd12_1_121, List.forall_mem_cons.2 ⟨subd12_1_122, List.forall_mem_cons.2 ⟨subd12_1_123, List.forall_mem_cons.2 ⟨subd12_1_124, List.forall_mem_cons.2 ⟨subd12_1_125, List.forall_mem_cons.2 ⟨subd12_1_126, List.forall_mem_cons.2 ⟨subd12_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_128 : subd12_1 [1, -1, -5] = true := by decide +kernel
theorem subd12_1_129 : subd12_1 [1, -1, -4] = true := by decide +kernel
theorem subd12_1_130 : subd12_1 [1, -1, -3] = true := by decide +kernel
theorem subd12_1_131 : subd12_1 [1, -1, -2] = true := by decide +kernel
theorem subd12_1_132 : subd12_1 [1, -1, -1] = true := by decide +kernel
theorem subd12_1_133 : subd12_1 [1, -1, 0] = true := by decide +kernel
theorem subd12_1_134 : subd12_1 [1, -1, 1] = true := by decide +kernel
theorem subd12_1_135 : subd12_1 [1, -1, 2] = true := by decide +kernel
theorem subd12_1_136 : subd12_1 [1, -1, 3] = true := by decide +kernel
theorem subd12_1_137 : subd12_1 [1, -1, 4] = true := by decide +kernel
theorem subd12_1_138 : subd12_1 [1, -1, 5] = true := by decide +kernel
theorem subd12_1_139 : subd12_1 [1, -1, 6] = true := by decide +kernel
theorem subd12_1_140 : subd12_1 [1, -1, 7] = true := by decide +kernel
theorem subd12_1_141 : subd12_1 [1, -1, 8] = true := by decide +kernel
theorem subd12_1_142 : subd12_1 [1, 0, -10] = true := by decide +kernel
theorem subd12_1_143 : subd12_1 [1, 0, -9] = true := by decide +kernel
theorem subd12_1_144 : subd12_1 [1, 0, -8] = true := by decide +kernel
theorem subd12_1_145 : subd12_1 [1, 0, -7] = true := by decide +kernel
theorem subd12_1_146 : subd12_1 [1, 0, -6] = true := by decide +kernel
theorem subd12_1_147 : subd12_1 [1, 0, -5] = true := by decide +kernel
theorem subd12_1_148 : subd12_1 [1, 0, -4] = true := by decide +kernel
theorem subd12_1_149 : subd12_1 [1, 0, -3] = true := by decide +kernel
theorem subd12_1_150 : subd12_1 [1, 0, -2] = true := by decide +kernel
theorem subd12_1_151 : subd12_1 [1, 0, -1] = true := by decide +kernel
theorem subd12_1_152 : subd12_1 [1, 0, 0] = true := by decide +kernel
theorem subd12_1_153 : subd12_1 [1, 0, 1] = true := by decide +kernel
theorem subd12_1_154 : subd12_1 [1, 0, 2] = true := by decide +kernel
theorem subd12_1_155 : subd12_1 [1, 0, 3] = true := by decide +kernel
theorem subd12_1_156 : subd12_1 [1, 0, 4] = true := by decide +kernel
theorem subd12_1_157 : subd12_1 [1, 0, 5] = true := by decide +kernel
theorem subd12_1_158 : subd12_1 [1, 0, 6] = true := by decide +kernel
theorem subd12_1_159 : subd12_1 [1, 0, 7] = true := by decide +kernel
theorem sbd12_1_4 : ∀ q ∈ blkd12_1_4, subd12_1 q = true := by
  unfold blkd12_1_4
  exact List.forall_mem_cons.2 ⟨subd12_1_128, List.forall_mem_cons.2 ⟨subd12_1_129, List.forall_mem_cons.2 ⟨subd12_1_130, List.forall_mem_cons.2 ⟨subd12_1_131, List.forall_mem_cons.2 ⟨subd12_1_132, List.forall_mem_cons.2 ⟨subd12_1_133, List.forall_mem_cons.2 ⟨subd12_1_134, List.forall_mem_cons.2 ⟨subd12_1_135, List.forall_mem_cons.2 ⟨subd12_1_136, List.forall_mem_cons.2 ⟨subd12_1_137, List.forall_mem_cons.2 ⟨subd12_1_138, List.forall_mem_cons.2 ⟨subd12_1_139, List.forall_mem_cons.2 ⟨subd12_1_140, List.forall_mem_cons.2 ⟨subd12_1_141, List.forall_mem_cons.2 ⟨subd12_1_142, List.forall_mem_cons.2 ⟨subd12_1_143, List.forall_mem_cons.2 ⟨subd12_1_144, List.forall_mem_cons.2 ⟨subd12_1_145, List.forall_mem_cons.2 ⟨subd12_1_146, List.forall_mem_cons.2 ⟨subd12_1_147, List.forall_mem_cons.2 ⟨subd12_1_148, List.forall_mem_cons.2 ⟨subd12_1_149, List.forall_mem_cons.2 ⟨subd12_1_150, List.forall_mem_cons.2 ⟨subd12_1_151, List.forall_mem_cons.2 ⟨subd12_1_152, List.forall_mem_cons.2 ⟨subd12_1_153, List.forall_mem_cons.2 ⟨subd12_1_154, List.forall_mem_cons.2 ⟨subd12_1_155, List.forall_mem_cons.2 ⟨subd12_1_156, List.forall_mem_cons.2 ⟨subd12_1_157, List.forall_mem_cons.2 ⟨subd12_1_158, List.forall_mem_cons.2 ⟨subd12_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_160 : subd12_1 [1, 0, 8] = true := by decide +kernel
theorem subd12_1_161 : subd12_1 [1, 0, 9] = true := by decide +kernel
theorem subd12_1_162 : subd12_1 [1, 1, -9] = true := by decide +kernel
theorem subd12_1_163 : subd12_1 [1, 1, -8] = true := by decide +kernel
theorem subd12_1_164 : subd12_1 [1, 1, -7] = true := by decide +kernel
theorem subd12_1_165 : subd12_1 [1, 1, -6] = true := by decide +kernel
theorem subd12_1_166 : subd12_1 [1, 1, -5] = true := by decide +kernel
theorem subd12_1_167 : subd12_1 [1, 1, -4] = true := by decide +kernel
theorem subd12_1_168 : subd12_1 [1, 1, -3] = true := by decide +kernel
theorem subd12_1_169 : subd12_1 [1, 1, -2] = true := by decide +kernel
theorem subd12_1_170 : subd12_1 [1, 1, -1] = true := by decide +kernel
theorem subd12_1_171 : subd12_1 [1, 1, 0] = true := by decide +kernel
theorem subd12_1_172 : subd12_1 [1, 1, 1] = true := by decide +kernel
theorem subd12_1_173 : subd12_1 [1, 1, 2] = true := by decide +kernel
theorem subd12_1_174 : subd12_1 [1, 1, 3] = true := by decide +kernel
theorem subd12_1_175 : subd12_1 [1, 1, 4] = true := by decide +kernel
theorem subd12_1_176 : subd12_1 [1, 1, 5] = true := by decide +kernel
theorem subd12_1_177 : subd12_1 [1, 1, 6] = true := by decide +kernel
theorem subd12_1_178 : subd12_1 [1, 1, 7] = true := by decide +kernel
theorem subd12_1_179 : subd12_1 [1, 1, 8] = true := by decide +kernel
theorem subd12_1_180 : subd12_1 [1, 1, 9] = true := by decide +kernel
theorem subd12_1_181 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_182 : subd12_1 [2] = true := by decide +kernel
theorem sbd12_1_5 : ∀ q ∈ blkd12_1_5, subd12_1 q = true := by
  unfold blkd12_1_5
  exact List.forall_mem_cons.2 ⟨subd12_1_160, List.forall_mem_cons.2 ⟨subd12_1_161, List.forall_mem_cons.2 ⟨subd12_1_162, List.forall_mem_cons.2 ⟨subd12_1_163, List.forall_mem_cons.2 ⟨subd12_1_164, List.forall_mem_cons.2 ⟨subd12_1_165, List.forall_mem_cons.2 ⟨subd12_1_166, List.forall_mem_cons.2 ⟨subd12_1_167, List.forall_mem_cons.2 ⟨subd12_1_168, List.forall_mem_cons.2 ⟨subd12_1_169, List.forall_mem_cons.2 ⟨subd12_1_170, List.forall_mem_cons.2 ⟨subd12_1_171, List.forall_mem_cons.2 ⟨subd12_1_172, List.forall_mem_cons.2 ⟨subd12_1_173, List.forall_mem_cons.2 ⟨subd12_1_174, List.forall_mem_cons.2 ⟨subd12_1_175, List.forall_mem_cons.2 ⟨subd12_1_176, List.forall_mem_cons.2 ⟨subd12_1_177, List.forall_mem_cons.2 ⟨subd12_1_178, List.forall_mem_cons.2 ⟨subd12_1_179, List.forall_mem_cons.2 ⟨subd12_1_180, List.forall_mem_cons.2 ⟨subd12_1_181, List.forall_mem_cons.2 ⟨subd12_1_182, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-3] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-2, -2] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [-2, -1] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [-2, 0, -7] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [-2, 0, -6] = true := by decide +kernel
theorem subd12_2_5 : subd12_2 [-2, 0, -5] = true := by decide +kernel
theorem subd12_2_6 : subd12_2 [-2, 0, -4] = true := by decide +kernel
theorem subd12_2_7 : subd12_2 [-2, 0, -3] = true := by decide +kernel
theorem subd12_2_8 : subd12_2 [-2, 0, -2] = true := by decide +kernel
theorem subd12_2_9 : subd12_2 [-2, 0, -1] = true := by decide +kernel
theorem subd12_2_10 : subd12_2 [-2, 0, 0] = true := by decide +kernel
theorem subd12_2_11 : subd12_2 [-2, 0, 1] = true := by decide +kernel
theorem subd12_2_12 : subd12_2 [-2, 0, 2] = true := by decide +kernel
theorem subd12_2_13 : subd12_2 [-2, 0, 3] = true := by decide +kernel
theorem subd12_2_14 : subd12_2 [-2, 0, 4] = true := by decide +kernel
theorem subd12_2_15 : subd12_2 [-2, 0, 5] = true := by decide +kernel
theorem subd12_2_16 : subd12_2 [-2, 0, 6] = true := by decide +kernel
theorem subd12_2_17 : subd12_2 [-2, 0, 7] = true := by decide +kernel
theorem subd12_2_18 : subd12_2 [-2, 1, -7] = true := by decide +kernel
theorem subd12_2_19 : subd12_2 [-2, 1, -6] = true := by decide +kernel
theorem subd12_2_20 : subd12_2 [-2, 1, -5] = true := by decide +kernel
theorem subd12_2_21 : subd12_2 [-2, 1, -4] = true := by decide +kernel
theorem subd12_2_22 : subd12_2 [-2, 1, -3] = true := by decide +kernel
theorem subd12_2_23 : subd12_2 [-2, 1, -2] = true := by decide +kernel
theorem subd12_2_24 : subd12_2 [-2, 1, -1] = true := by decide +kernel
theorem subd12_2_25 : subd12_2 [-2, 1, 0] = true := by decide +kernel
theorem subd12_2_26 : subd12_2 [-2, 1, 1] = true := by decide +kernel
theorem subd12_2_27 : subd12_2 [-2, 1, 2] = true := by decide +kernel
theorem subd12_2_28 : subd12_2 [-2, 1, 3] = true := by decide +kernel
theorem subd12_2_29 : subd12_2 [-2, 1, 4] = true := by decide +kernel
theorem subd12_2_30 : subd12_2 [-2, 1, 5] = true := by decide +kernel
theorem subd12_2_31 : subd12_2 [-2, 1, 6] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_cons.2 ⟨subd12_2_5, List.forall_mem_cons.2 ⟨subd12_2_6, List.forall_mem_cons.2 ⟨subd12_2_7, List.forall_mem_cons.2 ⟨subd12_2_8, List.forall_mem_cons.2 ⟨subd12_2_9, List.forall_mem_cons.2 ⟨subd12_2_10, List.forall_mem_cons.2 ⟨subd12_2_11, List.forall_mem_cons.2 ⟨subd12_2_12, List.forall_mem_cons.2 ⟨subd12_2_13, List.forall_mem_cons.2 ⟨subd12_2_14, List.forall_mem_cons.2 ⟨subd12_2_15, List.forall_mem_cons.2 ⟨subd12_2_16, List.forall_mem_cons.2 ⟨subd12_2_17, List.forall_mem_cons.2 ⟨subd12_2_18, List.forall_mem_cons.2 ⟨subd12_2_19, List.forall_mem_cons.2 ⟨subd12_2_20, List.forall_mem_cons.2 ⟨subd12_2_21, List.forall_mem_cons.2 ⟨subd12_2_22, List.forall_mem_cons.2 ⟨subd12_2_23, List.forall_mem_cons.2 ⟨subd12_2_24, List.forall_mem_cons.2 ⟨subd12_2_25, List.forall_mem_cons.2 ⟨subd12_2_26, List.forall_mem_cons.2 ⟨subd12_2_27, List.forall_mem_cons.2 ⟨subd12_2_28, List.forall_mem_cons.2 ⟨subd12_2_29, List.forall_mem_cons.2 ⟨subd12_2_30, List.forall_mem_cons.2 ⟨subd12_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_32 : subd12_2 [-2, 2] = true := by decide +kernel
theorem subd12_2_33 : subd12_2 [-1, -3] = true := by decide +kernel
theorem subd12_2_34 : subd12_2 [-1, -2] = true := by decide +kernel
theorem subd12_2_35 : subd12_2 [-1, -1, -7] = true := by decide +kernel
theorem subd12_2_36 : subd12_2 [-1, -1, -6] = true := by decide +kernel
theorem subd12_2_37 : subd12_2 [-1, -1, -5] = true := by decide +kernel
theorem subd12_2_38 : subd12_2 [-1, -1, -4] = true := by decide +kernel
theorem subd12_2_39 : subd12_2 [-1, -1, -3] = true := by decide +kernel
theorem subd12_2_40 : subd12_2 [-1, -1, -2] = true := by decide +kernel
theorem subd12_2_41 : subd12_2 [-1, -1, -1] = true := by decide +kernel
theorem subd12_2_42 : subd12_2 [-1, -1, 0] = true := by decide +kernel
theorem subd12_2_43 : subd12_2 [-1, -1, 1] = true := by decide +kernel
theorem subd12_2_44 : subd12_2 [-1, -1, 2] = true := by decide +kernel
theorem subd12_2_45 : subd12_2 [-1, -1, 3] = true := by decide +kernel
theorem subd12_2_46 : subd12_2 [-1, -1, 4] = true := by decide +kernel
theorem subd12_2_47 : subd12_2 [-1, -1, 5] = true := by decide +kernel
theorem subd12_2_48 : subd12_2 [-1, -1, 6] = true := by decide +kernel
theorem subd12_2_49 : subd12_2 [-1, -1, 7] = true := by decide +kernel
theorem subd12_2_50 : subd12_2 [-1, -1, 8] = true := by decide +kernel
theorem subd12_2_51 : subd12_2 [-1, 0, -9] = true := by decide +kernel
theorem subd12_2_52 : subd12_2 [-1, 0, -8] = true := by decide +kernel
theorem subd12_2_53 : subd12_2 [-1, 0, -7] = true := by decide +kernel
theorem subd12_2_54 : subd12_2 [-1, 0, -6] = true := by decide +kernel
theorem subd12_2_55 : subd12_2 [-1, 0, -5] = true := by decide +kernel
theorem subd12_2_56 : subd12_2 [-1, 0, -4] = true := by decide +kernel
theorem subd12_2_57 : subd12_2 [-1, 0, -3] = true := by decide +kernel
theorem subd12_2_58 : subd12_2 [-1, 0, -2] = true := by decide +kernel
theorem subd12_2_59 : subd12_2 [-1, 0, -1] = true := by decide +kernel
theorem subd12_2_60 : subd12_2 [-1, 0, 0] = true := by decide +kernel
theorem subd12_2_61 : subd12_2 [-1, 0, 1] = true := by decide +kernel
theorem subd12_2_62 : subd12_2 [-1, 0, 2] = true := by decide +kernel
theorem subd12_2_63 : subd12_2 [-1, 0, 3] = true := by decide +kernel
theorem sbd12_2_1 : ∀ q ∈ blkd12_2_1, subd12_2 q = true := by
  unfold blkd12_2_1
  exact List.forall_mem_cons.2 ⟨subd12_2_32, List.forall_mem_cons.2 ⟨subd12_2_33, List.forall_mem_cons.2 ⟨subd12_2_34, List.forall_mem_cons.2 ⟨subd12_2_35, List.forall_mem_cons.2 ⟨subd12_2_36, List.forall_mem_cons.2 ⟨subd12_2_37, List.forall_mem_cons.2 ⟨subd12_2_38, List.forall_mem_cons.2 ⟨subd12_2_39, List.forall_mem_cons.2 ⟨subd12_2_40, List.forall_mem_cons.2 ⟨subd12_2_41, List.forall_mem_cons.2 ⟨subd12_2_42, List.forall_mem_cons.2 ⟨subd12_2_43, List.forall_mem_cons.2 ⟨subd12_2_44, List.forall_mem_cons.2 ⟨subd12_2_45, List.forall_mem_cons.2 ⟨subd12_2_46, List.forall_mem_cons.2 ⟨subd12_2_47, List.forall_mem_cons.2 ⟨subd12_2_48, List.forall_mem_cons.2 ⟨subd12_2_49, List.forall_mem_cons.2 ⟨subd12_2_50, List.forall_mem_cons.2 ⟨subd12_2_51, List.forall_mem_cons.2 ⟨subd12_2_52, List.forall_mem_cons.2 ⟨subd12_2_53, List.forall_mem_cons.2 ⟨subd12_2_54, List.forall_mem_cons.2 ⟨subd12_2_55, List.forall_mem_cons.2 ⟨subd12_2_56, List.forall_mem_cons.2 ⟨subd12_2_57, List.forall_mem_cons.2 ⟨subd12_2_58, List.forall_mem_cons.2 ⟨subd12_2_59, List.forall_mem_cons.2 ⟨subd12_2_60, List.forall_mem_cons.2 ⟨subd12_2_61, List.forall_mem_cons.2 ⟨subd12_2_62, List.forall_mem_cons.2 ⟨subd12_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_64 : subd12_2 [-1, 0, 4] = true := by decide +kernel
theorem subd12_2_65 : subd12_2 [-1, 0, 5] = true := by decide +kernel
theorem subd12_2_66 : subd12_2 [-1, 0, 6] = true := by decide +kernel
theorem subd12_2_67 : subd12_2 [-1, 0, 7] = true := by decide +kernel
theorem subd12_2_68 : subd12_2 [-1, 0, 8] = true := by decide +kernel
theorem subd12_2_69 : subd12_2 [-1, 1, -9] = true := by decide +kernel
theorem subd12_2_70 : subd12_2 [-1, 1, -8] = true := by decide +kernel
theorem subd12_2_71 : subd12_2 [-1, 1, -7] = true := by decide +kernel
theorem subd12_2_72 : subd12_2 [-1, 1, -6] = true := by decide +kernel
theorem subd12_2_73 : subd12_2 [-1, 1, -5] = true := by decide +kernel
theorem subd12_2_74 : subd12_2 [-1, 1, -4] = true := by decide +kernel
theorem subd12_2_75 : subd12_2 [-1, 1, -3] = true := by decide +kernel
theorem subd12_2_76 : subd12_2 [-1, 1, -2] = true := by decide +kernel
theorem subd12_2_77 : subd12_2 [-1, 1, -1] = true := by decide +kernel
theorem subd12_2_78 : subd12_2 [-1, 1, 0] = true := by decide +kernel
theorem subd12_2_79 : subd12_2 [-1, 1, 1] = true := by decide +kernel
theorem subd12_2_80 : subd12_2 [-1, 1, 2] = true := by decide +kernel
theorem subd12_2_81 : subd12_2 [-1, 1, 3] = true := by decide +kernel
theorem subd12_2_82 : subd12_2 [-1, 1, 4] = true := by decide +kernel
theorem subd12_2_83 : subd12_2 [-1, 1, 5] = true := by decide +kernel
theorem subd12_2_84 : subd12_2 [-1, 1, 6] = true := by decide +kernel
theorem subd12_2_85 : subd12_2 [-1, 1, 7] = true := by decide +kernel
theorem subd12_2_86 : subd12_2 [-1, 2] = true := by decide +kernel
theorem subd12_2_87 : subd12_2 [0, -3] = true := by decide +kernel
theorem subd12_2_88 : subd12_2 [0, -2, -6] = true := by decide +kernel
theorem subd12_2_89 : subd12_2 [0, -2, -5] = true := by decide +kernel
theorem subd12_2_90 : subd12_2 [0, -2, -4] = true := by decide +kernel
theorem subd12_2_91 : subd12_2 [0, -2, -3] = true := by decide +kernel
theorem subd12_2_92 : subd12_2 [0, -2, -2] = true := by decide +kernel
theorem subd12_2_93 : subd12_2 [0, -2, -1] = true := by decide +kernel
theorem subd12_2_94 : subd12_2 [0, -2, 0] = true := by decide +kernel
theorem subd12_2_95 : subd12_2 [0, -2, 1] = true := by decide +kernel
theorem sbd12_2_2 : ∀ q ∈ blkd12_2_2, subd12_2 q = true := by
  unfold blkd12_2_2
  exact List.forall_mem_cons.2 ⟨subd12_2_64, List.forall_mem_cons.2 ⟨subd12_2_65, List.forall_mem_cons.2 ⟨subd12_2_66, List.forall_mem_cons.2 ⟨subd12_2_67, List.forall_mem_cons.2 ⟨subd12_2_68, List.forall_mem_cons.2 ⟨subd12_2_69, List.forall_mem_cons.2 ⟨subd12_2_70, List.forall_mem_cons.2 ⟨subd12_2_71, List.forall_mem_cons.2 ⟨subd12_2_72, List.forall_mem_cons.2 ⟨subd12_2_73, List.forall_mem_cons.2 ⟨subd12_2_74, List.forall_mem_cons.2 ⟨subd12_2_75, List.forall_mem_cons.2 ⟨subd12_2_76, List.forall_mem_cons.2 ⟨subd12_2_77, List.forall_mem_cons.2 ⟨subd12_2_78, List.forall_mem_cons.2 ⟨subd12_2_79, List.forall_mem_cons.2 ⟨subd12_2_80, List.forall_mem_cons.2 ⟨subd12_2_81, List.forall_mem_cons.2 ⟨subd12_2_82, List.forall_mem_cons.2 ⟨subd12_2_83, List.forall_mem_cons.2 ⟨subd12_2_84, List.forall_mem_cons.2 ⟨subd12_2_85, List.forall_mem_cons.2 ⟨subd12_2_86, List.forall_mem_cons.2 ⟨subd12_2_87, List.forall_mem_cons.2 ⟨subd12_2_88, List.forall_mem_cons.2 ⟨subd12_2_89, List.forall_mem_cons.2 ⟨subd12_2_90, List.forall_mem_cons.2 ⟨subd12_2_91, List.forall_mem_cons.2 ⟨subd12_2_92, List.forall_mem_cons.2 ⟨subd12_2_93, List.forall_mem_cons.2 ⟨subd12_2_94, List.forall_mem_cons.2 ⟨subd12_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_96 : subd12_2 [0, -2, 2] = true := by decide +kernel
theorem subd12_2_97 : subd12_2 [0, -2, 3] = true := by decide +kernel
theorem subd12_2_98 : subd12_2 [0, -2, 4] = true := by decide +kernel
theorem subd12_2_99 : subd12_2 [0, -2, 5] = true := by decide +kernel
theorem subd12_2_100 : subd12_2 [0, -2, 6] = true := by decide +kernel
theorem subd12_2_101 : subd12_2 [0, -2, 7] = true := by decide +kernel
theorem subd12_2_102 : subd12_2 [0, -1, -8] = true := by decide +kernel
theorem subd12_2_103 : subd12_2 [0, -1, -7] = true := by decide +kernel
theorem subd12_2_104 : subd12_2 [0, -1, -6] = true := by decide +kernel
theorem subd12_2_105 : subd12_2 [0, -1, -5] = true := by decide +kernel
theorem subd12_2_106 : subd12_2 [0, -1, -4] = true := by decide +kernel
theorem subd12_2_107 : subd12_2 [0, -1, -3] = true := by decide +kernel
theorem subd12_2_108 : subd12_2 [0, -1, -2] = true := by decide +kernel
theorem subd12_2_109 : subd12_2 [0, -1, -1] = true := by decide +kernel
theorem subd12_2_110 : subd12_2 [0, -1, 0] = true := by decide +kernel
theorem subd12_2_111 : subd12_2 [0, -1, 1] = true := by decide +kernel
theorem subd12_2_112 : subd12_2 [0, -1, 2] = true := by decide +kernel
theorem subd12_2_113 : subd12_2 [0, -1, 3] = true := by decide +kernel
theorem subd12_2_114 : subd12_2 [0, -1, 4] = true := by decide +kernel
theorem subd12_2_115 : subd12_2 [0, -1, 5] = true := by decide +kernel
theorem subd12_2_116 : subd12_2 [0, -1, 6] = true := by decide +kernel
theorem subd12_2_117 : subd12_2 [0, -1, 7] = true := by decide +kernel
theorem subd12_2_118 : subd12_2 [0, -1, 8] = true := by decide +kernel
theorem subd12_2_119 : subd12_2 [0, 0, -9] = true := by decide +kernel
theorem subd12_2_120 : subd12_2 [0, 0, -8] = true := by decide +kernel
theorem subd12_2_121 : subd12_2 [0, 0, -7] = true := by decide +kernel
theorem subd12_2_122 : subd12_2 [0, 0, -6] = true := by decide +kernel
theorem subd12_2_123 : subd12_2 [0, 0, -5] = true := by decide +kernel
theorem subd12_2_124 : subd12_2 [0, 0, -4] = true := by decide +kernel
theorem subd12_2_125 : subd12_2 [0, 0, -3] = true := by decide +kernel
theorem subd12_2_126 : subd12_2 [0, 0, -2] = true := by decide +kernel
theorem subd12_2_127 : subd12_2 [0, 0, -1] = true := by decide +kernel
theorem sbd12_2_3 : ∀ q ∈ blkd12_2_3, subd12_2 q = true := by
  unfold blkd12_2_3
  exact List.forall_mem_cons.2 ⟨subd12_2_96, List.forall_mem_cons.2 ⟨subd12_2_97, List.forall_mem_cons.2 ⟨subd12_2_98, List.forall_mem_cons.2 ⟨subd12_2_99, List.forall_mem_cons.2 ⟨subd12_2_100, List.forall_mem_cons.2 ⟨subd12_2_101, List.forall_mem_cons.2 ⟨subd12_2_102, List.forall_mem_cons.2 ⟨subd12_2_103, List.forall_mem_cons.2 ⟨subd12_2_104, List.forall_mem_cons.2 ⟨subd12_2_105, List.forall_mem_cons.2 ⟨subd12_2_106, List.forall_mem_cons.2 ⟨subd12_2_107, List.forall_mem_cons.2 ⟨subd12_2_108, List.forall_mem_cons.2 ⟨subd12_2_109, List.forall_mem_cons.2 ⟨subd12_2_110, List.forall_mem_cons.2 ⟨subd12_2_111, List.forall_mem_cons.2 ⟨subd12_2_112, List.forall_mem_cons.2 ⟨subd12_2_113, List.forall_mem_cons.2 ⟨subd12_2_114, List.forall_mem_cons.2 ⟨subd12_2_115, List.forall_mem_cons.2 ⟨subd12_2_116, List.forall_mem_cons.2 ⟨subd12_2_117, List.forall_mem_cons.2 ⟨subd12_2_118, List.forall_mem_cons.2 ⟨subd12_2_119, List.forall_mem_cons.2 ⟨subd12_2_120, List.forall_mem_cons.2 ⟨subd12_2_121, List.forall_mem_cons.2 ⟨subd12_2_122, List.forall_mem_cons.2 ⟨subd12_2_123, List.forall_mem_cons.2 ⟨subd12_2_124, List.forall_mem_cons.2 ⟨subd12_2_125, List.forall_mem_cons.2 ⟨subd12_2_126, List.forall_mem_cons.2 ⟨subd12_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_128 : subd12_2 [0, 0, 0] = true := by decide +kernel
theorem subd12_2_129 : subd12_2 [0, 0, 1] = true := by decide +kernel
theorem subd12_2_130 : subd12_2 [0, 0, 2] = true := by decide +kernel
theorem subd12_2_131 : subd12_2 [0, 0, 3] = true := by decide +kernel
theorem subd12_2_132 : subd12_2 [0, 0, 4] = true := by decide +kernel
theorem subd12_2_133 : subd12_2 [0, 0, 5] = true := by decide +kernel
theorem subd12_2_134 : subd12_2 [0, 0, 6] = true := by decide +kernel
theorem subd12_2_135 : subd12_2 [0, 0, 7] = true := by decide +kernel
theorem subd12_2_136 : subd12_2 [0, 0, 8] = true := by decide +kernel
theorem subd12_2_137 : subd12_2 [0, 1, -9] = true := by decide +kernel
theorem subd12_2_138 : subd12_2 [0, 1, -8] = true := by decide +kernel
theorem subd12_2_139 : subd12_2 [0, 1, -7] = true := by decide +kernel
theorem subd12_2_140 : subd12_2 [0, 1, -6] = true := by decide +kernel
theorem subd12_2_141 : subd12_2 [0, 1, -5] = true := by decide +kernel
theorem subd12_2_142 : subd12_2 [0, 1, -4] = true := by decide +kernel
theorem subd12_2_143 : subd12_2 [0, 1, -3] = true := by decide +kernel
theorem subd12_2_144 : subd12_2 [0, 1, -2] = true := by decide +kernel
theorem subd12_2_145 : subd12_2 [0, 1, -1] = true := by decide +kernel
theorem subd12_2_146 : subd12_2 [0, 1, 0] = true := by decide +kernel
theorem subd12_2_147 : subd12_2 [0, 1, 1] = true := by decide +kernel
theorem subd12_2_148 : subd12_2 [0, 1, 2] = true := by decide +kernel
theorem subd12_2_149 : subd12_2 [0, 1, 3] = true := by decide +kernel
theorem subd12_2_150 : subd12_2 [0, 1, 4] = true := by decide +kernel
theorem subd12_2_151 : subd12_2 [0, 1, 5] = true := by decide +kernel
theorem subd12_2_152 : subd12_2 [0, 1, 6] = true := by decide +kernel
theorem subd12_2_153 : subd12_2 [0, 1, 7] = true := by decide +kernel
theorem subd12_2_154 : subd12_2 [0, 2, -8] = true := by decide +kernel
theorem subd12_2_155 : subd12_2 [0, 2, -7] = true := by decide +kernel
theorem subd12_2_156 : subd12_2 [0, 2, -6] = true := by decide +kernel
theorem subd12_2_157 : subd12_2 [0, 2, -5] = true := by decide +kernel
theorem subd12_2_158 : subd12_2 [0, 2, -4] = true := by decide +kernel
theorem subd12_2_159 : subd12_2 [0, 2, -3] = true := by decide +kernel
theorem sbd12_2_4 : ∀ q ∈ blkd12_2_4, subd12_2 q = true := by
  unfold blkd12_2_4
  exact List.forall_mem_cons.2 ⟨subd12_2_128, List.forall_mem_cons.2 ⟨subd12_2_129, List.forall_mem_cons.2 ⟨subd12_2_130, List.forall_mem_cons.2 ⟨subd12_2_131, List.forall_mem_cons.2 ⟨subd12_2_132, List.forall_mem_cons.2 ⟨subd12_2_133, List.forall_mem_cons.2 ⟨subd12_2_134, List.forall_mem_cons.2 ⟨subd12_2_135, List.forall_mem_cons.2 ⟨subd12_2_136, List.forall_mem_cons.2 ⟨subd12_2_137, List.forall_mem_cons.2 ⟨subd12_2_138, List.forall_mem_cons.2 ⟨subd12_2_139, List.forall_mem_cons.2 ⟨subd12_2_140, List.forall_mem_cons.2 ⟨subd12_2_141, List.forall_mem_cons.2 ⟨subd12_2_142, List.forall_mem_cons.2 ⟨subd12_2_143, List.forall_mem_cons.2 ⟨subd12_2_144, List.forall_mem_cons.2 ⟨subd12_2_145, List.forall_mem_cons.2 ⟨subd12_2_146, List.forall_mem_cons.2 ⟨subd12_2_147, List.forall_mem_cons.2 ⟨subd12_2_148, List.forall_mem_cons.2 ⟨subd12_2_149, List.forall_mem_cons.2 ⟨subd12_2_150, List.forall_mem_cons.2 ⟨subd12_2_151, List.forall_mem_cons.2 ⟨subd12_2_152, List.forall_mem_cons.2 ⟨subd12_2_153, List.forall_mem_cons.2 ⟨subd12_2_154, List.forall_mem_cons.2 ⟨subd12_2_155, List.forall_mem_cons.2 ⟨subd12_2_156, List.forall_mem_cons.2 ⟨subd12_2_157, List.forall_mem_cons.2 ⟨subd12_2_158, List.forall_mem_cons.2 ⟨subd12_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
