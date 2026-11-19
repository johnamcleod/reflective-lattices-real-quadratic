import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_7_64 : subd7_7 [0, 1] = true := by decide +kernel
theorem subd7_7_65 : subd7_7 [0, 2] = true := by decide +kernel
theorem subd7_7_66 : subd7_7 [0, 3] = true := by decide +kernel
theorem subd7_7_67 : subd7_7 [0, 4] = true := by decide +kernel
theorem subd7_7_68 : subd7_7 [0, 5] = true := by decide +kernel
theorem subd7_7_69 : subd7_7 [0, 6] = true := by decide +kernel
theorem subd7_7_70 : subd7_7 [1, -7] = true := by decide +kernel
theorem subd7_7_71 : subd7_7 [1, -6] = true := by decide +kernel
theorem subd7_7_72 : subd7_7 [1, -5] = true := by decide +kernel
theorem subd7_7_73 : subd7_7 [1, -4] = true := by decide +kernel
theorem subd7_7_74 : subd7_7 [1, -3] = true := by decide +kernel
theorem subd7_7_75 : subd7_7 [1, -2] = true := by decide +kernel
theorem subd7_7_76 : subd7_7 [1, -1] = true := by decide +kernel
theorem subd7_7_77 : subd7_7 [1, 0] = true := by decide +kernel
theorem subd7_7_78 : subd7_7 [1, 1] = true := by decide +kernel
theorem subd7_7_79 : subd7_7 [1, 2] = true := by decide +kernel
theorem subd7_7_80 : subd7_7 [1, 3] = true := by decide +kernel
theorem subd7_7_81 : subd7_7 [1, 4] = true := by decide +kernel
theorem subd7_7_82 : subd7_7 [1, 5] = true := by decide +kernel
theorem subd7_7_83 : subd7_7 [1, 6] = true := by decide +kernel
theorem subd7_7_84 : subd7_7 [2, -7] = true := by decide +kernel
theorem subd7_7_85 : subd7_7 [2, -6] = true := by decide +kernel
theorem subd7_7_86 : subd7_7 [2, -5] = true := by decide +kernel
theorem subd7_7_87 : subd7_7 [2, -4] = true := by decide +kernel
theorem subd7_7_88 : subd7_7 [2, -3] = true := by decide +kernel
theorem subd7_7_89 : subd7_7 [2, -2] = true := by decide +kernel
theorem subd7_7_90 : subd7_7 [2, -1] = true := by decide +kernel
theorem subd7_7_91 : subd7_7 [2, 0] = true := by decide +kernel
theorem subd7_7_92 : subd7_7 [2, 1] = true := by decide +kernel
theorem subd7_7_93 : subd7_7 [2, 2] = true := by decide +kernel
theorem subd7_7_94 : subd7_7 [2, 3] = true := by decide +kernel
theorem subd7_7_95 : subd7_7 [2, 4] = true := by decide +kernel
theorem sbd7_7_2 : ∀ q ∈ blkd7_7_2, subd7_7 q = true := by
  unfold blkd7_7_2
  exact List.forall_mem_cons.2 ⟨subd7_7_64, List.forall_mem_cons.2 ⟨subd7_7_65, List.forall_mem_cons.2 ⟨subd7_7_66, List.forall_mem_cons.2 ⟨subd7_7_67, List.forall_mem_cons.2 ⟨subd7_7_68, List.forall_mem_cons.2 ⟨subd7_7_69, List.forall_mem_cons.2 ⟨subd7_7_70, List.forall_mem_cons.2 ⟨subd7_7_71, List.forall_mem_cons.2 ⟨subd7_7_72, List.forall_mem_cons.2 ⟨subd7_7_73, List.forall_mem_cons.2 ⟨subd7_7_74, List.forall_mem_cons.2 ⟨subd7_7_75, List.forall_mem_cons.2 ⟨subd7_7_76, List.forall_mem_cons.2 ⟨subd7_7_77, List.forall_mem_cons.2 ⟨subd7_7_78, List.forall_mem_cons.2 ⟨subd7_7_79, List.forall_mem_cons.2 ⟨subd7_7_80, List.forall_mem_cons.2 ⟨subd7_7_81, List.forall_mem_cons.2 ⟨subd7_7_82, List.forall_mem_cons.2 ⟨subd7_7_83, List.forall_mem_cons.2 ⟨subd7_7_84, List.forall_mem_cons.2 ⟨subd7_7_85, List.forall_mem_cons.2 ⟨subd7_7_86, List.forall_mem_cons.2 ⟨subd7_7_87, List.forall_mem_cons.2 ⟨subd7_7_88, List.forall_mem_cons.2 ⟨subd7_7_89, List.forall_mem_cons.2 ⟨subd7_7_90, List.forall_mem_cons.2 ⟨subd7_7_91, List.forall_mem_cons.2 ⟨subd7_7_92, List.forall_mem_cons.2 ⟨subd7_7_93, List.forall_mem_cons.2 ⟨subd7_7_94, List.forall_mem_cons.2 ⟨subd7_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_96 : subd7_7 [2, 5] = true := by decide +kernel
theorem subd7_7_97 : subd7_7 [3, -6] = true := by decide +kernel
theorem subd7_7_98 : subd7_7 [3, -5] = true := by decide +kernel
theorem subd7_7_99 : subd7_7 [3, -4] = true := by decide +kernel
theorem subd7_7_100 : subd7_7 [3, -3] = true := by decide +kernel
theorem subd7_7_101 : subd7_7 [3, -2] = true := by decide +kernel
theorem subd7_7_102 : subd7_7 [3, -1] = true := by decide +kernel
theorem subd7_7_103 : subd7_7 [3, 0] = true := by decide +kernel
theorem subd7_7_104 : subd7_7 [3, 1] = true := by decide +kernel
theorem subd7_7_105 : subd7_7 [3, 2] = true := by decide +kernel
theorem subd7_7_106 : subd7_7 [3, 3] = true := by decide +kernel
theorem subd7_7_107 : subd7_7 [3, 4] = true := by decide +kernel
theorem subd7_7_108 : subd7_7 [3, 5] = true := by decide +kernel
theorem subd7_7_109 : subd7_7 [4, -5] = true := by decide +kernel
theorem subd7_7_110 : subd7_7 [4, -4] = true := by decide +kernel
theorem subd7_7_111 : subd7_7 [4, -3] = true := by decide +kernel
theorem subd7_7_112 : subd7_7 [4, -2] = true := by decide +kernel
theorem subd7_7_113 : subd7_7 [4, -1] = true := by decide +kernel
theorem subd7_7_114 : subd7_7 [4, 0] = true := by decide +kernel
theorem subd7_7_115 : subd7_7 [4, 1] = true := by decide +kernel
theorem subd7_7_116 : subd7_7 [4, 2] = true := by decide +kernel
theorem subd7_7_117 : subd7_7 [4, 3] = true := by decide +kernel
theorem subd7_7_118 : subd7_7 [4, 4] = true := by decide +kernel
theorem subd7_7_119 : subd7_7 [5, -4] = true := by decide +kernel
theorem subd7_7_120 : subd7_7 [5, -3] = true := by decide +kernel
theorem subd7_7_121 : subd7_7 [5, -2] = true := by decide +kernel
theorem subd7_7_122 : subd7_7 [5, -1] = true := by decide +kernel
theorem subd7_7_123 : subd7_7 [5, 0] = true := by decide +kernel
theorem subd7_7_124 : subd7_7 [5, 1] = true := by decide +kernel
theorem subd7_7_125 : subd7_7 [5, 2] = true := by decide +kernel
theorem sbd7_7_3 : ∀ q ∈ blkd7_7_3, subd7_7 q = true := by
  unfold blkd7_7_3
  exact List.forall_mem_cons.2 ⟨subd7_7_96, List.forall_mem_cons.2 ⟨subd7_7_97, List.forall_mem_cons.2 ⟨subd7_7_98, List.forall_mem_cons.2 ⟨subd7_7_99, List.forall_mem_cons.2 ⟨subd7_7_100, List.forall_mem_cons.2 ⟨subd7_7_101, List.forall_mem_cons.2 ⟨subd7_7_102, List.forall_mem_cons.2 ⟨subd7_7_103, List.forall_mem_cons.2 ⟨subd7_7_104, List.forall_mem_cons.2 ⟨subd7_7_105, List.forall_mem_cons.2 ⟨subd7_7_106, List.forall_mem_cons.2 ⟨subd7_7_107, List.forall_mem_cons.2 ⟨subd7_7_108, List.forall_mem_cons.2 ⟨subd7_7_109, List.forall_mem_cons.2 ⟨subd7_7_110, List.forall_mem_cons.2 ⟨subd7_7_111, List.forall_mem_cons.2 ⟨subd7_7_112, List.forall_mem_cons.2 ⟨subd7_7_113, List.forall_mem_cons.2 ⟨subd7_7_114, List.forall_mem_cons.2 ⟨subd7_7_115, List.forall_mem_cons.2 ⟨subd7_7_116, List.forall_mem_cons.2 ⟨subd7_7_117, List.forall_mem_cons.2 ⟨subd7_7_118, List.forall_mem_cons.2 ⟨subd7_7_119, List.forall_mem_cons.2 ⟨subd7_7_120, List.forall_mem_cons.2 ⟨subd7_7_121, List.forall_mem_cons.2 ⟨subd7_7_122, List.forall_mem_cons.2 ⟨subd7_7_123, List.forall_mem_cons.2 ⟨subd7_7_124, List.forall_mem_cons.2 ⟨subd7_7_125, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_8 : ldCheck G d7_8.U d7_8.ms ldd7_8 = true := by decide +kernel
theorem pre_okd7_8 : subPre G cell7 d7_8 = true := by decide +kernel
theorem subd7_8_0 : subd7_8 [-1, -1] = true := by decide +kernel
theorem subd7_8_1 : subd7_8 [-1, 0, -15] = true := by decide +kernel
theorem subd7_8_2 : subd7_8 [-1, 0, -14] = true := by decide +kernel
theorem subd7_8_3 : subd7_8 [-1, 0, -13] = true := by decide +kernel
theorem subd7_8_4 : subd7_8 [-1, 0, -12] = true := by decide +kernel
theorem subd7_8_5 : subd7_8 [-1, 0, -11] = true := by decide +kernel
theorem subd7_8_6 : subd7_8 [-1, 0, -10] = true := by decide +kernel
theorem subd7_8_7 : subd7_8 [-1, 0, -9] = true := by decide +kernel
theorem subd7_8_8 : subd7_8 [-1, 0, -8] = true := by decide +kernel
theorem subd7_8_9 : subd7_8 [-1, 0, -7] = true := by decide +kernel
theorem subd7_8_10 : subd7_8 [-1, 0, -6] = true := by decide +kernel
theorem subd7_8_11 : subd7_8 [-1, 0, -5] = true := by decide +kernel
theorem subd7_8_12 : subd7_8 [-1, 0, -4] = true := by decide +kernel
theorem subd7_8_13 : subd7_8 [-1, 0, -3] = true := by decide +kernel
theorem subd7_8_14 : subd7_8 [-1, 0, -2] = true := by decide +kernel
theorem subd7_8_15 : subd7_8 [-1, 0, -1] = true := by decide +kernel
theorem subd7_8_16 : subd7_8 [-1, 0, 0] = true := by decide +kernel
theorem subd7_8_17 : subd7_8 [-1, 0, 1] = true := by decide +kernel
theorem subd7_8_18 : subd7_8 [-1, 0, 2] = true := by decide +kernel
theorem subd7_8_19 : subd7_8 [-1, 0, 3] = true := by decide +kernel
theorem subd7_8_20 : subd7_8 [-1, 0, 4] = true := by decide +kernel
theorem subd7_8_21 : subd7_8 [-1, 0, 5] = true := by decide +kernel
theorem subd7_8_22 : subd7_8 [-1, 0, 6] = true := by decide +kernel
theorem subd7_8_23 : subd7_8 [-1, 0, 7] = true := by decide +kernel
theorem subd7_8_24 : subd7_8 [-1, 0, 8] = true := by decide +kernel
theorem subd7_8_25 : subd7_8 [-1, 0, 9] = true := by decide +kernel
theorem subd7_8_26 : subd7_8 [-1, 0, 10] = true := by decide +kernel
theorem subd7_8_27 : subd7_8 [-1, 0, 11] = true := by decide +kernel
theorem subd7_8_28 : subd7_8 [-1, 0, 12] = true := by decide +kernel
theorem subd7_8_29 : subd7_8 [-1, 0, 13] = true := by decide +kernel
theorem subd7_8_30 : subd7_8 [-1, 0, 14] = true := by decide +kernel
theorem subd7_8_31 : subd7_8 [0, -2] = true := by decide +kernel
theorem sbd7_8_0 : ∀ q ∈ blkd7_8_0, subd7_8 q = true := by
  unfold blkd7_8_0
  exact List.forall_mem_cons.2 ⟨subd7_8_0, List.forall_mem_cons.2 ⟨subd7_8_1, List.forall_mem_cons.2 ⟨subd7_8_2, List.forall_mem_cons.2 ⟨subd7_8_3, List.forall_mem_cons.2 ⟨subd7_8_4, List.forall_mem_cons.2 ⟨subd7_8_5, List.forall_mem_cons.2 ⟨subd7_8_6, List.forall_mem_cons.2 ⟨subd7_8_7, List.forall_mem_cons.2 ⟨subd7_8_8, List.forall_mem_cons.2 ⟨subd7_8_9, List.forall_mem_cons.2 ⟨subd7_8_10, List.forall_mem_cons.2 ⟨subd7_8_11, List.forall_mem_cons.2 ⟨subd7_8_12, List.forall_mem_cons.2 ⟨subd7_8_13, List.forall_mem_cons.2 ⟨subd7_8_14, List.forall_mem_cons.2 ⟨subd7_8_15, List.forall_mem_cons.2 ⟨subd7_8_16, List.forall_mem_cons.2 ⟨subd7_8_17, List.forall_mem_cons.2 ⟨subd7_8_18, List.forall_mem_cons.2 ⟨subd7_8_19, List.forall_mem_cons.2 ⟨subd7_8_20, List.forall_mem_cons.2 ⟨subd7_8_21, List.forall_mem_cons.2 ⟨subd7_8_22, List.forall_mem_cons.2 ⟨subd7_8_23, List.forall_mem_cons.2 ⟨subd7_8_24, List.forall_mem_cons.2 ⟨subd7_8_25, List.forall_mem_cons.2 ⟨subd7_8_26, List.forall_mem_cons.2 ⟨subd7_8_27, List.forall_mem_cons.2 ⟨subd7_8_28, List.forall_mem_cons.2 ⟨subd7_8_29, List.forall_mem_cons.2 ⟨subd7_8_30, List.forall_mem_cons.2 ⟨subd7_8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_8_32 : subd7_8 [0, -1, -23] = true := by decide +kernel
theorem subd7_8_33 : subd7_8 [0, -1, -22] = true := by decide +kernel
theorem subd7_8_34 : subd7_8 [0, -1, -21] = true := by decide +kernel
theorem subd7_8_35 : subd7_8 [0, -1, -20] = true := by decide +kernel
theorem subd7_8_36 : subd7_8 [0, -1, -19] = true := by decide +kernel
theorem subd7_8_37 : subd7_8 [0, -1, -18] = true := by decide +kernel
theorem subd7_8_38 : subd7_8 [0, -1, -17] = true := by decide +kernel
theorem subd7_8_39 : subd7_8 [0, -1, -16] = true := by decide +kernel
theorem subd7_8_40 : subd7_8 [0, -1, -15] = true := by decide +kernel
theorem subd7_8_41 : subd7_8 [0, -1, -14] = true := by decide +kernel
theorem subd7_8_42 : subd7_8 [0, -1, -13] = true := by decide +kernel
theorem subd7_8_43 : subd7_8 [0, -1, -12] = true := by decide +kernel
theorem subd7_8_44 : subd7_8 [0, -1, -11] = true := by decide +kernel
theorem subd7_8_45 : subd7_8 [0, -1, -10] = true := by decide +kernel
theorem subd7_8_46 : subd7_8 [0, -1, -9] = true := by decide +kernel
theorem subd7_8_47 : subd7_8 [0, -1, -8] = true := by decide +kernel
theorem subd7_8_48 : subd7_8 [0, -1, -7] = true := by decide +kernel
theorem subd7_8_49 : subd7_8 [0, -1, -6] = true := by decide +kernel
theorem subd7_8_50 : subd7_8 [0, -1, -5] = true := by decide +kernel
theorem subd7_8_51 : subd7_8 [0, -1, -4] = true := by decide +kernel
theorem subd7_8_52 : subd7_8 [0, -1, -3] = true := by decide +kernel
theorem subd7_8_53 : subd7_8 [0, -1, -2] = true := by decide +kernel
theorem subd7_8_54 : subd7_8 [0, -1, -1] = true := by decide +kernel
theorem subd7_8_55 : subd7_8 [0, -1, 0] = true := by decide +kernel
theorem subd7_8_56 : subd7_8 [0, -1, 1] = true := by decide +kernel
theorem subd7_8_57 : subd7_8 [0, -1, 2] = true := by decide +kernel
theorem subd7_8_58 : subd7_8 [0, -1, 3] = true := by decide +kernel
theorem subd7_8_59 : subd7_8 [0, -1, 4] = true := by decide +kernel
theorem subd7_8_60 : subd7_8 [0, -1, 5] = true := by decide +kernel
theorem subd7_8_61 : subd7_8 [0, -1, 6] = true := by decide +kernel
theorem subd7_8_62 : subd7_8 [0, -1, 7] = true := by decide +kernel
theorem subd7_8_63 : subd7_8 [0, -1, 8] = true := by decide +kernel
theorem sbd7_8_1 : ∀ q ∈ blkd7_8_1, subd7_8 q = true := by
  unfold blkd7_8_1
  exact List.forall_mem_cons.2 ⟨subd7_8_32, List.forall_mem_cons.2 ⟨subd7_8_33, List.forall_mem_cons.2 ⟨subd7_8_34, List.forall_mem_cons.2 ⟨subd7_8_35, List.forall_mem_cons.2 ⟨subd7_8_36, List.forall_mem_cons.2 ⟨subd7_8_37, List.forall_mem_cons.2 ⟨subd7_8_38, List.forall_mem_cons.2 ⟨subd7_8_39, List.forall_mem_cons.2 ⟨subd7_8_40, List.forall_mem_cons.2 ⟨subd7_8_41, List.forall_mem_cons.2 ⟨subd7_8_42, List.forall_mem_cons.2 ⟨subd7_8_43, List.forall_mem_cons.2 ⟨subd7_8_44, List.forall_mem_cons.2 ⟨subd7_8_45, List.forall_mem_cons.2 ⟨subd7_8_46, List.forall_mem_cons.2 ⟨subd7_8_47, List.forall_mem_cons.2 ⟨subd7_8_48, List.forall_mem_cons.2 ⟨subd7_8_49, List.forall_mem_cons.2 ⟨subd7_8_50, List.forall_mem_cons.2 ⟨subd7_8_51, List.forall_mem_cons.2 ⟨subd7_8_52, List.forall_mem_cons.2 ⟨subd7_8_53, List.forall_mem_cons.2 ⟨subd7_8_54, List.forall_mem_cons.2 ⟨subd7_8_55, List.forall_mem_cons.2 ⟨subd7_8_56, List.forall_mem_cons.2 ⟨subd7_8_57, List.forall_mem_cons.2 ⟨subd7_8_58, List.forall_mem_cons.2 ⟨subd7_8_59, List.forall_mem_cons.2 ⟨subd7_8_60, List.forall_mem_cons.2 ⟨subd7_8_61, List.forall_mem_cons.2 ⟨subd7_8_62, List.forall_mem_cons.2 ⟨subd7_8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
