import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_7_64 : subd8_7 [2, 0] = true := by decide +kernel
theorem subd8_7_65 : subd8_7 [2, 1] = true := by decide +kernel
theorem subd8_7_66 : subd8_7 [2, 2] = true := by decide +kernel
theorem subd8_7_67 : subd8_7 [2, 3] = true := by decide +kernel
theorem subd8_7_68 : subd8_7 [2, 4] = true := by decide +kernel
theorem subd8_7_69 : subd8_7 [2, 5] = true := by decide +kernel
theorem subd8_7_70 : subd8_7 [3, -3] = true := by decide +kernel
theorem subd8_7_71 : subd8_7 [3, -2] = true := by decide +kernel
theorem subd8_7_72 : subd8_7 [3, -1] = true := by decide +kernel
theorem subd8_7_73 : subd8_7 [3, 0] = true := by decide +kernel
theorem subd8_7_74 : subd8_7 [3, 1] = true := by decide +kernel
theorem subd8_7_75 : subd8_7 [3, 2] = true := by decide +kernel
theorem subd8_7_76 : subd8_7 [3, 3] = true := by decide +kernel
theorem subd8_7_77 : subd8_7 [3, 4] = true := by decide +kernel
theorem subd8_7_78 : subd8_7 [3, 5] = true := by decide +kernel
theorem subd8_7_79 : subd8_7 [4, -2] = true := by decide +kernel
theorem subd8_7_80 : subd8_7 [4, -1] = true := by decide +kernel
theorem subd8_7_81 : subd8_7 [4, 0] = true := by decide +kernel
theorem subd8_7_82 : subd8_7 [4, 1] = true := by decide +kernel
theorem subd8_7_83 : subd8_7 [4, 2] = true := by decide +kernel
theorem subd8_7_84 : subd8_7 [4, 3] = true := by decide +kernel
theorem subd8_7_85 : subd8_7 [4, 4] = true := by decide +kernel
theorem subd8_7_86 : subd8_7 [4, 5] = true := by decide +kernel
theorem subd8_7_87 : subd8_7 [5] = true := by decide +kernel
theorem sbd8_7_2 : ∀ q ∈ blkd8_7_2, subd8_7 q = true := by
  unfold blkd8_7_2
  exact List.forall_mem_cons.2 ⟨subd8_7_64, List.forall_mem_cons.2 ⟨subd8_7_65, List.forall_mem_cons.2 ⟨subd8_7_66, List.forall_mem_cons.2 ⟨subd8_7_67, List.forall_mem_cons.2 ⟨subd8_7_68, List.forall_mem_cons.2 ⟨subd8_7_69, List.forall_mem_cons.2 ⟨subd8_7_70, List.forall_mem_cons.2 ⟨subd8_7_71, List.forall_mem_cons.2 ⟨subd8_7_72, List.forall_mem_cons.2 ⟨subd8_7_73, List.forall_mem_cons.2 ⟨subd8_7_74, List.forall_mem_cons.2 ⟨subd8_7_75, List.forall_mem_cons.2 ⟨subd8_7_76, List.forall_mem_cons.2 ⟨subd8_7_77, List.forall_mem_cons.2 ⟨subd8_7_78, List.forall_mem_cons.2 ⟨subd8_7_79, List.forall_mem_cons.2 ⟨subd8_7_80, List.forall_mem_cons.2 ⟨subd8_7_81, List.forall_mem_cons.2 ⟨subd8_7_82, List.forall_mem_cons.2 ⟨subd8_7_83, List.forall_mem_cons.2 ⟨subd8_7_84, List.forall_mem_cons.2 ⟨subd8_7_85, List.forall_mem_cons.2 ⟨subd8_7_86, List.forall_mem_cons.2 ⟨subd8_7_87, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_8 : ldCheck G d8_8.U d8_8.ms ldd8_8 = true := by decide +kernel
theorem pre_okd8_8 : subPre G cell8 d8_8 = true := by decide +kernel
theorem subd8_8_0 : subd8_8 [-1, -1] = true := by decide +kernel
theorem subd8_8_1 : subd8_8 [-1, 0, -14] = true := by decide +kernel
theorem subd8_8_2 : subd8_8 [-1, 0, -13] = true := by decide +kernel
theorem subd8_8_3 : subd8_8 [-1, 0, -12] = true := by decide +kernel
theorem subd8_8_4 : subd8_8 [-1, 0, -11] = true := by decide +kernel
theorem subd8_8_5 : subd8_8 [-1, 0, -10] = true := by decide +kernel
theorem subd8_8_6 : subd8_8 [-1, 0, -9] = true := by decide +kernel
theorem subd8_8_7 : subd8_8 [-1, 0, -8] = true := by decide +kernel
theorem subd8_8_8 : subd8_8 [-1, 0, -7] = true := by decide +kernel
theorem subd8_8_9 : subd8_8 [-1, 0, -6] = true := by decide +kernel
theorem subd8_8_10 : subd8_8 [-1, 0, -5] = true := by decide +kernel
theorem subd8_8_11 : subd8_8 [-1, 0, -4] = true := by decide +kernel
theorem subd8_8_12 : subd8_8 [-1, 0, -3] = true := by decide +kernel
theorem subd8_8_13 : subd8_8 [-1, 0, -2] = true := by decide +kernel
theorem subd8_8_14 : subd8_8 [-1, 0, -1] = true := by decide +kernel
theorem subd8_8_15 : subd8_8 [-1, 0, 0] = true := by decide +kernel
theorem subd8_8_16 : subd8_8 [-1, 0, 1] = true := by decide +kernel
theorem subd8_8_17 : subd8_8 [-1, 0, 2] = true := by decide +kernel
theorem subd8_8_18 : subd8_8 [-1, 0, 3] = true := by decide +kernel
theorem subd8_8_19 : subd8_8 [-1, 0, 4] = true := by decide +kernel
theorem subd8_8_20 : subd8_8 [-1, 0, 5] = true := by decide +kernel
theorem subd8_8_21 : subd8_8 [-1, 0, 6] = true := by decide +kernel
theorem subd8_8_22 : subd8_8 [-1, 0, 7] = true := by decide +kernel
theorem subd8_8_23 : subd8_8 [-1, 0, 8] = true := by decide +kernel
theorem subd8_8_24 : subd8_8 [-1, 0, 9] = true := by decide +kernel
theorem subd8_8_25 : subd8_8 [-1, 0, 10] = true := by decide +kernel
theorem subd8_8_26 : subd8_8 [-1, 0, 11] = true := by decide +kernel
theorem subd8_8_27 : subd8_8 [-1, 0, 12] = true := by decide +kernel
theorem subd8_8_28 : subd8_8 [-1, 0, 13] = true := by decide +kernel
theorem subd8_8_29 : subd8_8 [-1, 1, -13] = true := by decide +kernel
theorem subd8_8_30 : subd8_8 [-1, 1, -12] = true := by decide +kernel
theorem subd8_8_31 : subd8_8 [-1, 1, -11] = true := by decide +kernel
theorem sbd8_8_0 : ∀ q ∈ blkd8_8_0, subd8_8 q = true := by
  unfold blkd8_8_0
  exact List.forall_mem_cons.2 ⟨subd8_8_0, List.forall_mem_cons.2 ⟨subd8_8_1, List.forall_mem_cons.2 ⟨subd8_8_2, List.forall_mem_cons.2 ⟨subd8_8_3, List.forall_mem_cons.2 ⟨subd8_8_4, List.forall_mem_cons.2 ⟨subd8_8_5, List.forall_mem_cons.2 ⟨subd8_8_6, List.forall_mem_cons.2 ⟨subd8_8_7, List.forall_mem_cons.2 ⟨subd8_8_8, List.forall_mem_cons.2 ⟨subd8_8_9, List.forall_mem_cons.2 ⟨subd8_8_10, List.forall_mem_cons.2 ⟨subd8_8_11, List.forall_mem_cons.2 ⟨subd8_8_12, List.forall_mem_cons.2 ⟨subd8_8_13, List.forall_mem_cons.2 ⟨subd8_8_14, List.forall_mem_cons.2 ⟨subd8_8_15, List.forall_mem_cons.2 ⟨subd8_8_16, List.forall_mem_cons.2 ⟨subd8_8_17, List.forall_mem_cons.2 ⟨subd8_8_18, List.forall_mem_cons.2 ⟨subd8_8_19, List.forall_mem_cons.2 ⟨subd8_8_20, List.forall_mem_cons.2 ⟨subd8_8_21, List.forall_mem_cons.2 ⟨subd8_8_22, List.forall_mem_cons.2 ⟨subd8_8_23, List.forall_mem_cons.2 ⟨subd8_8_24, List.forall_mem_cons.2 ⟨subd8_8_25, List.forall_mem_cons.2 ⟨subd8_8_26, List.forall_mem_cons.2 ⟨subd8_8_27, List.forall_mem_cons.2 ⟨subd8_8_28, List.forall_mem_cons.2 ⟨subd8_8_29, List.forall_mem_cons.2 ⟨subd8_8_30, List.forall_mem_cons.2 ⟨subd8_8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_32 : subd8_8 [-1, 1, -10] = true := by decide +kernel
theorem subd8_8_33 : subd8_8 [-1, 1, -9] = true := by decide +kernel
theorem subd8_8_34 : subd8_8 [-1, 1, -8] = true := by decide +kernel
theorem subd8_8_35 : subd8_8 [-1, 1, -7] = true := by decide +kernel
theorem subd8_8_36 : subd8_8 [-1, 1, -6] = true := by decide +kernel
theorem subd8_8_37 : subd8_8 [-1, 1, -5] = true := by decide +kernel
theorem subd8_8_38 : subd8_8 [-1, 1, -4] = true := by decide +kernel
theorem subd8_8_39 : subd8_8 [-1, 1, -3] = true := by decide +kernel
theorem subd8_8_40 : subd8_8 [-1, 1, -2] = true := by decide +kernel
theorem subd8_8_41 : subd8_8 [-1, 1, -1] = true := by decide +kernel
theorem subd8_8_42 : subd8_8 [-1, 1, 0] = true := by decide +kernel
theorem subd8_8_43 : subd8_8 [-1, 1, 1] = true := by decide +kernel
theorem subd8_8_44 : subd8_8 [-1, 1, 2] = true := by decide +kernel
theorem subd8_8_45 : subd8_8 [-1, 1, 3] = true := by decide +kernel
theorem subd8_8_46 : subd8_8 [-1, 1, 4] = true := by decide +kernel
theorem subd8_8_47 : subd8_8 [-1, 1, 5] = true := by decide +kernel
theorem subd8_8_48 : subd8_8 [-1, 1, 6] = true := by decide +kernel
theorem subd8_8_49 : subd8_8 [-1, 1, 7] = true := by decide +kernel
theorem subd8_8_50 : subd8_8 [-1, 1, 8] = true := by decide +kernel
theorem subd8_8_51 : subd8_8 [-1, 1, 9] = true := by decide +kernel
theorem subd8_8_52 : subd8_8 [-1, 1, 10] = true := by decide +kernel
theorem subd8_8_53 : subd8_8 [-1, 1, 11] = true := by decide +kernel
theorem subd8_8_54 : subd8_8 [-1, 1, 12] = true := by decide +kernel
theorem subd8_8_55 : subd8_8 [-1, 1, 13] = true := by decide +kernel
theorem subd8_8_56 : subd8_8 [0, -2] = true := by decide +kernel
theorem subd8_8_57 : subd8_8 [0, -1, -22] = true := by decide +kernel
theorem subd8_8_58 : subd8_8 [0, -1, -21] = true := by decide +kernel
theorem subd8_8_59 : subd8_8 [0, -1, -20] = true := by decide +kernel
theorem subd8_8_60 : subd8_8 [0, -1, -19] = true := by decide +kernel
theorem subd8_8_61 : subd8_8 [0, -1, -18] = true := by decide +kernel
theorem subd8_8_62 : subd8_8 [0, -1, -17] = true := by decide +kernel
theorem subd8_8_63 : subd8_8 [0, -1, -16] = true := by decide +kernel
theorem sbd8_8_1 : ∀ q ∈ blkd8_8_1, subd8_8 q = true := by
  unfold blkd8_8_1
  exact List.forall_mem_cons.2 ⟨subd8_8_32, List.forall_mem_cons.2 ⟨subd8_8_33, List.forall_mem_cons.2 ⟨subd8_8_34, List.forall_mem_cons.2 ⟨subd8_8_35, List.forall_mem_cons.2 ⟨subd8_8_36, List.forall_mem_cons.2 ⟨subd8_8_37, List.forall_mem_cons.2 ⟨subd8_8_38, List.forall_mem_cons.2 ⟨subd8_8_39, List.forall_mem_cons.2 ⟨subd8_8_40, List.forall_mem_cons.2 ⟨subd8_8_41, List.forall_mem_cons.2 ⟨subd8_8_42, List.forall_mem_cons.2 ⟨subd8_8_43, List.forall_mem_cons.2 ⟨subd8_8_44, List.forall_mem_cons.2 ⟨subd8_8_45, List.forall_mem_cons.2 ⟨subd8_8_46, List.forall_mem_cons.2 ⟨subd8_8_47, List.forall_mem_cons.2 ⟨subd8_8_48, List.forall_mem_cons.2 ⟨subd8_8_49, List.forall_mem_cons.2 ⟨subd8_8_50, List.forall_mem_cons.2 ⟨subd8_8_51, List.forall_mem_cons.2 ⟨subd8_8_52, List.forall_mem_cons.2 ⟨subd8_8_53, List.forall_mem_cons.2 ⟨subd8_8_54, List.forall_mem_cons.2 ⟨subd8_8_55, List.forall_mem_cons.2 ⟨subd8_8_56, List.forall_mem_cons.2 ⟨subd8_8_57, List.forall_mem_cons.2 ⟨subd8_8_58, List.forall_mem_cons.2 ⟨subd8_8_59, List.forall_mem_cons.2 ⟨subd8_8_60, List.forall_mem_cons.2 ⟨subd8_8_61, List.forall_mem_cons.2 ⟨subd8_8_62, List.forall_mem_cons.2 ⟨subd8_8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_64 : subd8_8 [0, -1, -15] = true := by decide +kernel
theorem subd8_8_65 : subd8_8 [0, -1, -14] = true := by decide +kernel
theorem subd8_8_66 : subd8_8 [0, -1, -13] = true := by decide +kernel
theorem subd8_8_67 : subd8_8 [0, -1, -12] = true := by decide +kernel
theorem subd8_8_68 : subd8_8 [0, -1, -11] = true := by decide +kernel
theorem subd8_8_69 : subd8_8 [0, -1, -10] = true := by decide +kernel
theorem subd8_8_70 : subd8_8 [0, -1, -9] = true := by decide +kernel
theorem subd8_8_71 : subd8_8 [0, -1, -8] = true := by decide +kernel
theorem subd8_8_72 : subd8_8 [0, -1, -7] = true := by decide +kernel
theorem subd8_8_73 : subd8_8 [0, -1, -6] = true := by decide +kernel
theorem subd8_8_74 : subd8_8 [0, -1, -5] = true := by decide +kernel
theorem subd8_8_75 : subd8_8 [0, -1, -4] = true := by decide +kernel
theorem subd8_8_76 : subd8_8 [0, -1, -3] = true := by decide +kernel
theorem subd8_8_77 : subd8_8 [0, -1, -2] = true := by decide +kernel
theorem subd8_8_78 : subd8_8 [0, -1, -1] = true := by decide +kernel
theorem subd8_8_79 : subd8_8 [0, -1, 0] = true := by decide +kernel
theorem subd8_8_80 : subd8_8 [0, -1, 1] = true := by decide +kernel
theorem subd8_8_81 : subd8_8 [0, -1, 2] = true := by decide +kernel
theorem subd8_8_82 : subd8_8 [0, -1, 3] = true := by decide +kernel
theorem subd8_8_83 : subd8_8 [0, -1, 4] = true := by decide +kernel
theorem subd8_8_84 : subd8_8 [0, -1, 5] = true := by decide +kernel
theorem subd8_8_85 : subd8_8 [0, -1, 6] = true := by decide +kernel
theorem subd8_8_86 : subd8_8 [0, -1, 7] = true := by decide +kernel
theorem subd8_8_87 : subd8_8 [0, -1, 8] = true := by decide +kernel
theorem subd8_8_88 : subd8_8 [0, -1, 9] = true := by decide +kernel
theorem subd8_8_89 : subd8_8 [0, -1, 10] = true := by decide +kernel
theorem subd8_8_90 : subd8_8 [0, -1, 11] = true := by decide +kernel
theorem subd8_8_91 : subd8_8 [0, -1, 12] = true := by decide +kernel
theorem subd8_8_92 : subd8_8 [0, -1, 13] = true := by decide +kernel
theorem subd8_8_93 : subd8_8 [0, -1, 14] = true := by decide +kernel
theorem subd8_8_94 : subd8_8 [0, -1, 15] = true := by decide +kernel
theorem subd8_8_95 : subd8_8 [0, -1, 16] = true := by decide +kernel
theorem sbd8_8_2 : ∀ q ∈ blkd8_8_2, subd8_8 q = true := by
  unfold blkd8_8_2
  exact List.forall_mem_cons.2 ⟨subd8_8_64, List.forall_mem_cons.2 ⟨subd8_8_65, List.forall_mem_cons.2 ⟨subd8_8_66, List.forall_mem_cons.2 ⟨subd8_8_67, List.forall_mem_cons.2 ⟨subd8_8_68, List.forall_mem_cons.2 ⟨subd8_8_69, List.forall_mem_cons.2 ⟨subd8_8_70, List.forall_mem_cons.2 ⟨subd8_8_71, List.forall_mem_cons.2 ⟨subd8_8_72, List.forall_mem_cons.2 ⟨subd8_8_73, List.forall_mem_cons.2 ⟨subd8_8_74, List.forall_mem_cons.2 ⟨subd8_8_75, List.forall_mem_cons.2 ⟨subd8_8_76, List.forall_mem_cons.2 ⟨subd8_8_77, List.forall_mem_cons.2 ⟨subd8_8_78, List.forall_mem_cons.2 ⟨subd8_8_79, List.forall_mem_cons.2 ⟨subd8_8_80, List.forall_mem_cons.2 ⟨subd8_8_81, List.forall_mem_cons.2 ⟨subd8_8_82, List.forall_mem_cons.2 ⟨subd8_8_83, List.forall_mem_cons.2 ⟨subd8_8_84, List.forall_mem_cons.2 ⟨subd8_8_85, List.forall_mem_cons.2 ⟨subd8_8_86, List.forall_mem_cons.2 ⟨subd8_8_87, List.forall_mem_cons.2 ⟨subd8_8_88, List.forall_mem_cons.2 ⟨subd8_8_89, List.forall_mem_cons.2 ⟨subd8_8_90, List.forall_mem_cons.2 ⟨subd8_8_91, List.forall_mem_cons.2 ⟨subd8_8_92, List.forall_mem_cons.2 ⟨subd8_8_93, List.forall_mem_cons.2 ⟨subd8_8_94, List.forall_mem_cons.2 ⟨subd8_8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_8_96 : subd8_8 [0, -1, 17] = true := by decide +kernel
theorem subd8_8_97 : subd8_8 [0, -1, 18] = true := by decide +kernel
theorem subd8_8_98 : subd8_8 [0, -1, 19] = true := by decide +kernel
theorem subd8_8_99 : subd8_8 [0, -1, 20] = true := by decide +kernel
theorem subd8_8_100 : subd8_8 [0, 0, -31] = true := by decide +kernel
theorem subd8_8_101 : subd8_8 [0, 0, -30] = true := by decide +kernel
theorem subd8_8_102 : subd8_8 [0, 0, -29] = true := by decide +kernel
theorem subd8_8_103 : subd8_8 [0, 0, -28] = true := by decide +kernel
theorem subd8_8_104 : subd8_8 [0, 0, -27] = true := by decide +kernel
theorem subd8_8_105 : subd8_8 [0, 0, -26] = true := by decide +kernel
theorem subd8_8_106 : subd8_8 [0, 0, -25] = true := by decide +kernel
theorem subd8_8_107 : subd8_8 [0, 0, -24] = true := by decide +kernel
theorem subd8_8_108 : subd8_8 [0, 0, -23] = true := by decide +kernel
theorem subd8_8_109 : subd8_8 [0, 0, -22] = true := by decide +kernel
theorem subd8_8_110 : subd8_8 [0, 0, -21] = true := by decide +kernel
theorem subd8_8_111 : subd8_8 [0, 0, -20] = true := by decide +kernel
theorem subd8_8_112 : subd8_8 [0, 0, -19] = true := by decide +kernel
theorem subd8_8_113 : subd8_8 [0, 0, -18] = true := by decide +kernel
theorem subd8_8_114 : subd8_8 [0, 0, -17] = true := by decide +kernel
theorem subd8_8_115 : subd8_8 [0, 0, -16] = true := by decide +kernel
theorem subd8_8_116 : subd8_8 [0, 0, -15] = true := by decide +kernel
theorem subd8_8_117 : subd8_8 [0, 0, -14] = true := by decide +kernel
theorem subd8_8_118 : subd8_8 [0, 0, -13] = true := by decide +kernel
theorem subd8_8_119 : subd8_8 [0, 0, -12] = true := by decide +kernel
theorem subd8_8_120 : subd8_8 [0, 0, -11] = true := by decide +kernel
theorem subd8_8_121 : subd8_8 [0, 0, -10] = true := by decide +kernel
theorem subd8_8_122 : subd8_8 [0, 0, -9] = true := by decide +kernel
theorem subd8_8_123 : subd8_8 [0, 0, -8] = true := by decide +kernel
theorem subd8_8_124 : subd8_8 [0, 0, -7] = true := by decide +kernel
theorem subd8_8_125 : subd8_8 [0, 0, -6] = true := by decide +kernel
theorem subd8_8_126 : subd8_8 [0, 0, -5] = true := by decide +kernel
theorem subd8_8_127 : subd8_8 [0, 0, -4] = true := by decide +kernel
theorem sbd8_8_3 : ∀ q ∈ blkd8_8_3, subd8_8 q = true := by
  unfold blkd8_8_3
  exact List.forall_mem_cons.2 ⟨subd8_8_96, List.forall_mem_cons.2 ⟨subd8_8_97, List.forall_mem_cons.2 ⟨subd8_8_98, List.forall_mem_cons.2 ⟨subd8_8_99, List.forall_mem_cons.2 ⟨subd8_8_100, List.forall_mem_cons.2 ⟨subd8_8_101, List.forall_mem_cons.2 ⟨subd8_8_102, List.forall_mem_cons.2 ⟨subd8_8_103, List.forall_mem_cons.2 ⟨subd8_8_104, List.forall_mem_cons.2 ⟨subd8_8_105, List.forall_mem_cons.2 ⟨subd8_8_106, List.forall_mem_cons.2 ⟨subd8_8_107, List.forall_mem_cons.2 ⟨subd8_8_108, List.forall_mem_cons.2 ⟨subd8_8_109, List.forall_mem_cons.2 ⟨subd8_8_110, List.forall_mem_cons.2 ⟨subd8_8_111, List.forall_mem_cons.2 ⟨subd8_8_112, List.forall_mem_cons.2 ⟨subd8_8_113, List.forall_mem_cons.2 ⟨subd8_8_114, List.forall_mem_cons.2 ⟨subd8_8_115, List.forall_mem_cons.2 ⟨subd8_8_116, List.forall_mem_cons.2 ⟨subd8_8_117, List.forall_mem_cons.2 ⟨subd8_8_118, List.forall_mem_cons.2 ⟨subd8_8_119, List.forall_mem_cons.2 ⟨subd8_8_120, List.forall_mem_cons.2 ⟨subd8_8_121, List.forall_mem_cons.2 ⟨subd8_8_122, List.forall_mem_cons.2 ⟨subd8_8_123, List.forall_mem_cons.2 ⟨subd8_8_124, List.forall_mem_cons.2 ⟨subd8_8_125, List.forall_mem_cons.2 ⟨subd8_8_126, List.forall_mem_cons.2 ⟨subd8_8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
