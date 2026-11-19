import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_4_0 : subd1_4 [-3] = true := by decide +kernel
theorem subd1_4_1 : subd1_4 [-2, -3] = true := by decide +kernel
theorem subd1_4_2 : subd1_4 [-2, -2] = true := by decide +kernel
theorem subd1_4_3 : subd1_4 [-2, -1] = true := by decide +kernel
theorem subd1_4_4 : subd1_4 [-2, 0] = true := by decide +kernel
theorem subd1_4_5 : subd1_4 [-2, 1] = true := by decide +kernel
theorem subd1_4_6 : subd1_4 [-2, 2] = true := by decide +kernel
theorem subd1_4_7 : subd1_4 [-1, -3] = true := by decide +kernel
theorem subd1_4_8 : subd1_4 [-1, -2] = true := by decide +kernel
theorem subd1_4_9 : subd1_4 [-1, -1] = true := by decide +kernel
theorem subd1_4_10 : subd1_4 [-1, 0, -7] = true := by decide +kernel
theorem subd1_4_11 : subd1_4 [-1, 0, -6] = true := by decide +kernel
theorem subd1_4_12 : subd1_4 [-1, 0, -5] = true := by decide +kernel
theorem subd1_4_13 : subd1_4 [-1, 0, -4] = true := by decide +kernel
theorem subd1_4_14 : subd1_4 [-1, 0, -3] = true := by decide +kernel
theorem subd1_4_15 : subd1_4 [-1, 0, -2] = true := by decide +kernel
theorem subd1_4_16 : subd1_4 [-1, 0, -1] = true := by decide +kernel
theorem subd1_4_17 : subd1_4 [-1, 0, 0] = true := by decide +kernel
theorem subd1_4_18 : subd1_4 [-1, 0, 1] = true := by decide +kernel
theorem subd1_4_19 : subd1_4 [-1, 0, 2] = true := by decide +kernel
theorem subd1_4_20 : subd1_4 [-1, 0, 3] = true := by decide +kernel
theorem subd1_4_21 : subd1_4 [-1, 0, 4] = true := by decide +kernel
theorem subd1_4_22 : subd1_4 [-1, 0, 5] = true := by decide +kernel
theorem subd1_4_23 : subd1_4 [-1, 0, 6] = true := by decide +kernel
theorem subd1_4_24 : subd1_4 [-1, 1, -7] = true := by decide +kernel
theorem subd1_4_25 : subd1_4 [-1, 1, -6] = true := by decide +kernel
theorem subd1_4_26 : subd1_4 [-1, 1, -5] = true := by decide +kernel
theorem subd1_4_27 : subd1_4 [-1, 1, -4] = true := by decide +kernel
theorem subd1_4_28 : subd1_4 [-1, 1, -3] = true := by decide +kernel
theorem subd1_4_29 : subd1_4 [-1, 1, -2] = true := by decide +kernel
theorem subd1_4_30 : subd1_4 [-1, 1, -1] = true := by decide +kernel
theorem subd1_4_31 : subd1_4 [-1, 1, 0] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_cons.2 ⟨subd1_4_1, List.forall_mem_cons.2 ⟨subd1_4_2, List.forall_mem_cons.2 ⟨subd1_4_3, List.forall_mem_cons.2 ⟨subd1_4_4, List.forall_mem_cons.2 ⟨subd1_4_5, List.forall_mem_cons.2 ⟨subd1_4_6, List.forall_mem_cons.2 ⟨subd1_4_7, List.forall_mem_cons.2 ⟨subd1_4_8, List.forall_mem_cons.2 ⟨subd1_4_9, List.forall_mem_cons.2 ⟨subd1_4_10, List.forall_mem_cons.2 ⟨subd1_4_11, List.forall_mem_cons.2 ⟨subd1_4_12, List.forall_mem_cons.2 ⟨subd1_4_13, List.forall_mem_cons.2 ⟨subd1_4_14, List.forall_mem_cons.2 ⟨subd1_4_15, List.forall_mem_cons.2 ⟨subd1_4_16, List.forall_mem_cons.2 ⟨subd1_4_17, List.forall_mem_cons.2 ⟨subd1_4_18, List.forall_mem_cons.2 ⟨subd1_4_19, List.forall_mem_cons.2 ⟨subd1_4_20, List.forall_mem_cons.2 ⟨subd1_4_21, List.forall_mem_cons.2 ⟨subd1_4_22, List.forall_mem_cons.2 ⟨subd1_4_23, List.forall_mem_cons.2 ⟨subd1_4_24, List.forall_mem_cons.2 ⟨subd1_4_25, List.forall_mem_cons.2 ⟨subd1_4_26, List.forall_mem_cons.2 ⟨subd1_4_27, List.forall_mem_cons.2 ⟨subd1_4_28, List.forall_mem_cons.2 ⟨subd1_4_29, List.forall_mem_cons.2 ⟨subd1_4_30, List.forall_mem_cons.2 ⟨subd1_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_4_32 : subd1_4 [-1, 1, 1] = true := by decide +kernel
theorem subd1_4_33 : subd1_4 [-1, 1, 2] = true := by decide +kernel
theorem subd1_4_34 : subd1_4 [-1, 1, 3] = true := by decide +kernel
theorem subd1_4_35 : subd1_4 [-1, 1, 4] = true := by decide +kernel
theorem subd1_4_36 : subd1_4 [-1, 1, 5] = true := by decide +kernel
theorem subd1_4_37 : subd1_4 [-1, 1, 6] = true := by decide +kernel
theorem subd1_4_38 : subd1_4 [-1, 2] = true := by decide +kernel
theorem subd1_4_39 : subd1_4 [-1, 3] = true := by decide +kernel
theorem subd1_4_40 : subd1_4 [0, -4] = true := by decide +kernel
theorem subd1_4_41 : subd1_4 [0, -3] = true := by decide +kernel
theorem subd1_4_42 : subd1_4 [0, -2] = true := by decide +kernel
theorem subd1_4_43 : subd1_4 [0, -1, -7] = true := by decide +kernel
theorem subd1_4_44 : subd1_4 [0, -1, -6] = true := by decide +kernel
theorem subd1_4_45 : subd1_4 [0, -1, -5] = true := by decide +kernel
theorem subd1_4_46 : subd1_4 [0, -1, -4] = true := by decide +kernel
theorem subd1_4_47 : subd1_4 [0, -1, -3] = true := by decide +kernel
theorem subd1_4_48 : subd1_4 [0, -1, -2] = true := by decide +kernel
theorem subd1_4_49 : subd1_4 [0, -1, -1] = true := by decide +kernel
theorem subd1_4_50 : subd1_4 [0, -1, 0] = true := by decide +kernel
theorem subd1_4_51 : subd1_4 [0, -1, 1] = true := by decide +kernel
theorem subd1_4_52 : subd1_4 [0, -1, 2] = true := by decide +kernel
theorem subd1_4_53 : subd1_4 [0, -1, 3] = true := by decide +kernel
theorem subd1_4_54 : subd1_4 [0, -1, 4] = true := by decide +kernel
theorem subd1_4_55 : subd1_4 [0, -1, 5] = true := by decide +kernel
theorem subd1_4_56 : subd1_4 [0, -1, 6] = true := by decide +kernel
theorem subd1_4_57 : subd1_4 [0, 0, -8] = true := by decide +kernel
theorem subd1_4_58 : subd1_4 [0, 0, -7] = true := by decide +kernel
theorem subd1_4_59 : subd1_4 [0, 0, -6] = true := by decide +kernel
theorem subd1_4_60 : subd1_4 [0, 0, -5] = true := by decide +kernel
theorem subd1_4_61 : subd1_4 [0, 0, -4] = true := by decide +kernel
theorem subd1_4_62 : subd1_4 [0, 0, -3] = true := by decide +kernel
theorem subd1_4_63 : subd1_4 [0, 0, -2] = true := by decide +kernel
theorem sbd1_4_1 : ∀ q ∈ blkd1_4_1, subd1_4 q = true := by
  unfold blkd1_4_1
  exact List.forall_mem_cons.2 ⟨subd1_4_32, List.forall_mem_cons.2 ⟨subd1_4_33, List.forall_mem_cons.2 ⟨subd1_4_34, List.forall_mem_cons.2 ⟨subd1_4_35, List.forall_mem_cons.2 ⟨subd1_4_36, List.forall_mem_cons.2 ⟨subd1_4_37, List.forall_mem_cons.2 ⟨subd1_4_38, List.forall_mem_cons.2 ⟨subd1_4_39, List.forall_mem_cons.2 ⟨subd1_4_40, List.forall_mem_cons.2 ⟨subd1_4_41, List.forall_mem_cons.2 ⟨subd1_4_42, List.forall_mem_cons.2 ⟨subd1_4_43, List.forall_mem_cons.2 ⟨subd1_4_44, List.forall_mem_cons.2 ⟨subd1_4_45, List.forall_mem_cons.2 ⟨subd1_4_46, List.forall_mem_cons.2 ⟨subd1_4_47, List.forall_mem_cons.2 ⟨subd1_4_48, List.forall_mem_cons.2 ⟨subd1_4_49, List.forall_mem_cons.2 ⟨subd1_4_50, List.forall_mem_cons.2 ⟨subd1_4_51, List.forall_mem_cons.2 ⟨subd1_4_52, List.forall_mem_cons.2 ⟨subd1_4_53, List.forall_mem_cons.2 ⟨subd1_4_54, List.forall_mem_cons.2 ⟨subd1_4_55, List.forall_mem_cons.2 ⟨subd1_4_56, List.forall_mem_cons.2 ⟨subd1_4_57, List.forall_mem_cons.2 ⟨subd1_4_58, List.forall_mem_cons.2 ⟨subd1_4_59, List.forall_mem_cons.2 ⟨subd1_4_60, List.forall_mem_cons.2 ⟨subd1_4_61, List.forall_mem_cons.2 ⟨subd1_4_62, List.forall_mem_cons.2 ⟨subd1_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_4_64 : subd1_4 [0, 0, -1] = true := by decide +kernel
theorem subd1_4_65 : subd1_4 [0, 0, 0] = true := by decide +kernel
theorem subd1_4_66 : subd1_4 [0, 0, 1] = true := by decide +kernel
theorem subd1_4_67 : subd1_4 [0, 0, 2] = true := by decide +kernel
theorem subd1_4_68 : subd1_4 [0, 0, 3] = true := by decide +kernel
theorem subd1_4_69 : subd1_4 [0, 0, 4] = true := by decide +kernel
theorem subd1_4_70 : subd1_4 [0, 0, 5] = true := by decide +kernel
theorem subd1_4_71 : subd1_4 [0, 0, 6] = true := by decide +kernel
theorem subd1_4_72 : subd1_4 [0, 0, 7] = true := by decide +kernel
theorem subd1_4_73 : subd1_4 [0, 1, -7] = true := by decide +kernel
theorem subd1_4_74 : subd1_4 [0, 1, -6] = true := by decide +kernel
theorem subd1_4_75 : subd1_4 [0, 1, -5] = true := by decide +kernel
theorem subd1_4_76 : subd1_4 [0, 1, -4] = true := by decide +kernel
theorem subd1_4_77 : subd1_4 [0, 1, -3] = true := by decide +kernel
theorem subd1_4_78 : subd1_4 [0, 1, -2] = true := by decide +kernel
theorem subd1_4_79 : subd1_4 [0, 1, -1] = true := by decide +kernel
theorem subd1_4_80 : subd1_4 [0, 1, 0] = true := by decide +kernel
theorem subd1_4_81 : subd1_4 [0, 1, 1] = true := by decide +kernel
theorem subd1_4_82 : subd1_4 [0, 1, 2] = true := by decide +kernel
theorem subd1_4_83 : subd1_4 [0, 1, 3] = true := by decide +kernel
theorem subd1_4_84 : subd1_4 [0, 1, 4] = true := by decide +kernel
theorem subd1_4_85 : subd1_4 [0, 1, 5] = true := by decide +kernel
theorem subd1_4_86 : subd1_4 [0, 1, 6] = true := by decide +kernel
theorem subd1_4_87 : subd1_4 [0, 2] = true := by decide +kernel
theorem subd1_4_88 : subd1_4 [0, 3] = true := by decide +kernel
theorem subd1_4_89 : subd1_4 [1, -4] = true := by decide +kernel
theorem subd1_4_90 : subd1_4 [1, -3] = true := by decide +kernel
theorem subd1_4_91 : subd1_4 [1, -2] = true := by decide +kernel
theorem subd1_4_92 : subd1_4 [1, -1, -7] = true := by decide +kernel
theorem subd1_4_93 : subd1_4 [1, -1, -6] = true := by decide +kernel
theorem subd1_4_94 : subd1_4 [1, -1, -5] = true := by decide +kernel
theorem subd1_4_95 : subd1_4 [1, -1, -4] = true := by decide +kernel
theorem sbd1_4_2 : ∀ q ∈ blkd1_4_2, subd1_4 q = true := by
  unfold blkd1_4_2
  exact List.forall_mem_cons.2 ⟨subd1_4_64, List.forall_mem_cons.2 ⟨subd1_4_65, List.forall_mem_cons.2 ⟨subd1_4_66, List.forall_mem_cons.2 ⟨subd1_4_67, List.forall_mem_cons.2 ⟨subd1_4_68, List.forall_mem_cons.2 ⟨subd1_4_69, List.forall_mem_cons.2 ⟨subd1_4_70, List.forall_mem_cons.2 ⟨subd1_4_71, List.forall_mem_cons.2 ⟨subd1_4_72, List.forall_mem_cons.2 ⟨subd1_4_73, List.forall_mem_cons.2 ⟨subd1_4_74, List.forall_mem_cons.2 ⟨subd1_4_75, List.forall_mem_cons.2 ⟨subd1_4_76, List.forall_mem_cons.2 ⟨subd1_4_77, List.forall_mem_cons.2 ⟨subd1_4_78, List.forall_mem_cons.2 ⟨subd1_4_79, List.forall_mem_cons.2 ⟨subd1_4_80, List.forall_mem_cons.2 ⟨subd1_4_81, List.forall_mem_cons.2 ⟨subd1_4_82, List.forall_mem_cons.2 ⟨subd1_4_83, List.forall_mem_cons.2 ⟨subd1_4_84, List.forall_mem_cons.2 ⟨subd1_4_85, List.forall_mem_cons.2 ⟨subd1_4_86, List.forall_mem_cons.2 ⟨subd1_4_87, List.forall_mem_cons.2 ⟨subd1_4_88, List.forall_mem_cons.2 ⟨subd1_4_89, List.forall_mem_cons.2 ⟨subd1_4_90, List.forall_mem_cons.2 ⟨subd1_4_91, List.forall_mem_cons.2 ⟨subd1_4_92, List.forall_mem_cons.2 ⟨subd1_4_93, List.forall_mem_cons.2 ⟨subd1_4_94, List.forall_mem_cons.2 ⟨subd1_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_4_96 : subd1_4 [1, -1, -3] = true := by decide +kernel
theorem subd1_4_97 : subd1_4 [1, -1, -2] = true := by decide +kernel
theorem subd1_4_98 : subd1_4 [1, -1, -1] = true := by decide +kernel
theorem subd1_4_99 : subd1_4 [1, -1, 0] = true := by decide +kernel
theorem subd1_4_100 : subd1_4 [1, -1, 1] = true := by decide +kernel
theorem subd1_4_101 : subd1_4 [1, -1, 2] = true := by decide +kernel
theorem subd1_4_102 : subd1_4 [1, -1, 3] = true := by decide +kernel
theorem subd1_4_103 : subd1_4 [1, -1, 4] = true := by decide +kernel
theorem subd1_4_104 : subd1_4 [1, -1, 5] = true := by decide +kernel
theorem subd1_4_105 : subd1_4 [1, -1, 6] = true := by decide +kernel
theorem subd1_4_106 : subd1_4 [1, 0, -7] = true := by decide +kernel
theorem subd1_4_107 : subd1_4 [1, 0, -6] = true := by decide +kernel
theorem subd1_4_108 : subd1_4 [1, 0, -5] = true := by decide +kernel
theorem subd1_4_109 : subd1_4 [1, 0, -4] = true := by decide +kernel
theorem subd1_4_110 : subd1_4 [1, 0, -3] = true := by decide +kernel
theorem subd1_4_111 : subd1_4 [1, 0, -2] = true := by decide +kernel
theorem subd1_4_112 : subd1_4 [1, 0, -1] = true := by decide +kernel
theorem subd1_4_113 : subd1_4 [1, 0, 0] = true := by decide +kernel
theorem subd1_4_114 : subd1_4 [1, 0, 1] = true := by decide +kernel
theorem subd1_4_115 : subd1_4 [1, 0, 2] = true := by decide +kernel
theorem subd1_4_116 : subd1_4 [1, 0, 3] = true := by decide +kernel
theorem subd1_4_117 : subd1_4 [1, 0, 4] = true := by decide +kernel
theorem subd1_4_118 : subd1_4 [1, 0, 5] = true := by decide +kernel
theorem subd1_4_119 : subd1_4 [1, 0, 6] = true := by decide +kernel
theorem subd1_4_120 : subd1_4 [1, 1] = true := by decide +kernel
theorem subd1_4_121 : subd1_4 [1, 2] = true := by decide +kernel
theorem subd1_4_122 : subd1_4 [2, -3] = true := by decide +kernel
theorem subd1_4_123 : subd1_4 [2, -2] = true := by decide +kernel
theorem subd1_4_124 : subd1_4 [2, -1] = true := by decide +kernel
theorem subd1_4_125 : subd1_4 [2, 0] = true := by decide +kernel
theorem subd1_4_126 : subd1_4 [2, 1] = true := by decide +kernel
theorem subd1_4_127 : subd1_4 [2, 2] = true := by decide +kernel
theorem sbd1_4_3 : ∀ q ∈ blkd1_4_3, subd1_4 q = true := by
  unfold blkd1_4_3
  exact List.forall_mem_cons.2 ⟨subd1_4_96, List.forall_mem_cons.2 ⟨subd1_4_97, List.forall_mem_cons.2 ⟨subd1_4_98, List.forall_mem_cons.2 ⟨subd1_4_99, List.forall_mem_cons.2 ⟨subd1_4_100, List.forall_mem_cons.2 ⟨subd1_4_101, List.forall_mem_cons.2 ⟨subd1_4_102, List.forall_mem_cons.2 ⟨subd1_4_103, List.forall_mem_cons.2 ⟨subd1_4_104, List.forall_mem_cons.2 ⟨subd1_4_105, List.forall_mem_cons.2 ⟨subd1_4_106, List.forall_mem_cons.2 ⟨subd1_4_107, List.forall_mem_cons.2 ⟨subd1_4_108, List.forall_mem_cons.2 ⟨subd1_4_109, List.forall_mem_cons.2 ⟨subd1_4_110, List.forall_mem_cons.2 ⟨subd1_4_111, List.forall_mem_cons.2 ⟨subd1_4_112, List.forall_mem_cons.2 ⟨subd1_4_113, List.forall_mem_cons.2 ⟨subd1_4_114, List.forall_mem_cons.2 ⟨subd1_4_115, List.forall_mem_cons.2 ⟨subd1_4_116, List.forall_mem_cons.2 ⟨subd1_4_117, List.forall_mem_cons.2 ⟨subd1_4_118, List.forall_mem_cons.2 ⟨subd1_4_119, List.forall_mem_cons.2 ⟨subd1_4_120, List.forall_mem_cons.2 ⟨subd1_4_121, List.forall_mem_cons.2 ⟨subd1_4_122, List.forall_mem_cons.2 ⟨subd1_4_123, List.forall_mem_cons.2 ⟨subd1_4_124, List.forall_mem_cons.2 ⟨subd1_4_125, List.forall_mem_cons.2 ⟨subd1_4_126, List.forall_mem_cons.2 ⟨subd1_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_4_128 : subd1_4 [3] = true := by decide +kernel
theorem sbd1_4_4 : ∀ q ∈ blkd1_4_4, subd1_4 q = true := by
  unfold blkd1_4_4
  exact List.forall_mem_cons.2 ⟨subd1_4_128, List.forall_mem_nil _⟩
theorem ld_okd1_5 : ldCheck G d1_5.U d1_5.ms ldd1_5 = true := by decide +kernel
theorem pre_okd1_5 : subPre G cell1 d1_5 = true := by decide +kernel
theorem subd1_5_0 : subd1_5 [-2, -4] = true := by decide +kernel
theorem subd1_5_1 : subd1_5 [-2, -3] = true := by decide +kernel
theorem subd1_5_2 : subd1_5 [-2, -2] = true := by decide +kernel
theorem subd1_5_3 : subd1_5 [-2, -1] = true := by decide +kernel
theorem subd1_5_4 : subd1_5 [-2, 0] = true := by decide +kernel
theorem subd1_5_5 : subd1_5 [-2, 1] = true := by decide +kernel
theorem subd1_5_6 : subd1_5 [-1, -4] = true := by decide +kernel
theorem subd1_5_7 : subd1_5 [-1, -3] = true := by decide +kernel
theorem subd1_5_8 : subd1_5 [-1, -2] = true := by decide +kernel
theorem subd1_5_9 : subd1_5 [-1, -1] = true := by decide +kernel
theorem subd1_5_10 : subd1_5 [-1, 0] = true := by decide +kernel
theorem subd1_5_11 : subd1_5 [-1, 1] = true := by decide +kernel
theorem subd1_5_12 : subd1_5 [-1, 2] = true := by decide +kernel
theorem subd1_5_13 : subd1_5 [0, -4] = true := by decide +kernel
theorem subd1_5_14 : subd1_5 [0, -3] = true := by decide +kernel
theorem subd1_5_15 : subd1_5 [0, -2] = true := by decide +kernel
theorem subd1_5_16 : subd1_5 [0, -1] = true := by decide +kernel
theorem subd1_5_17 : subd1_5 [0, 0] = true := by decide +kernel
theorem subd1_5_18 : subd1_5 [0, 1] = true := by decide +kernel
theorem subd1_5_19 : subd1_5 [0, 2] = true := by decide +kernel
theorem subd1_5_20 : subd1_5 [0, 3] = true := by decide +kernel
theorem subd1_5_21 : subd1_5 [1, -3] = true := by decide +kernel
theorem subd1_5_22 : subd1_5 [1, -2] = true := by decide +kernel
theorem subd1_5_23 : subd1_5 [1, -1] = true := by decide +kernel
theorem subd1_5_24 : subd1_5 [1, 0] = true := by decide +kernel
theorem subd1_5_25 : subd1_5 [1, 1] = true := by decide +kernel
theorem subd1_5_26 : subd1_5 [1, 2] = true := by decide +kernel
theorem subd1_5_27 : subd1_5 [1, 3] = true := by decide +kernel
theorem subd1_5_28 : subd1_5 [2, -2] = true := by decide +kernel
theorem subd1_5_29 : subd1_5 [2, -1] = true := by decide +kernel
theorem subd1_5_30 : subd1_5 [2, 0] = true := by decide +kernel
theorem subd1_5_31 : subd1_5 [2, 1] = true := by decide +kernel
theorem sbd1_5_0 : ∀ q ∈ blkd1_5_0, subd1_5 q = true := by
  unfold blkd1_5_0
  exact List.forall_mem_cons.2 ⟨subd1_5_0, List.forall_mem_cons.2 ⟨subd1_5_1, List.forall_mem_cons.2 ⟨subd1_5_2, List.forall_mem_cons.2 ⟨subd1_5_3, List.forall_mem_cons.2 ⟨subd1_5_4, List.forall_mem_cons.2 ⟨subd1_5_5, List.forall_mem_cons.2 ⟨subd1_5_6, List.forall_mem_cons.2 ⟨subd1_5_7, List.forall_mem_cons.2 ⟨subd1_5_8, List.forall_mem_cons.2 ⟨subd1_5_9, List.forall_mem_cons.2 ⟨subd1_5_10, List.forall_mem_cons.2 ⟨subd1_5_11, List.forall_mem_cons.2 ⟨subd1_5_12, List.forall_mem_cons.2 ⟨subd1_5_13, List.forall_mem_cons.2 ⟨subd1_5_14, List.forall_mem_cons.2 ⟨subd1_5_15, List.forall_mem_cons.2 ⟨subd1_5_16, List.forall_mem_cons.2 ⟨subd1_5_17, List.forall_mem_cons.2 ⟨subd1_5_18, List.forall_mem_cons.2 ⟨subd1_5_19, List.forall_mem_cons.2 ⟨subd1_5_20, List.forall_mem_cons.2 ⟨subd1_5_21, List.forall_mem_cons.2 ⟨subd1_5_22, List.forall_mem_cons.2 ⟨subd1_5_23, List.forall_mem_cons.2 ⟨subd1_5_24, List.forall_mem_cons.2 ⟨subd1_5_25, List.forall_mem_cons.2 ⟨subd1_5_26, List.forall_mem_cons.2 ⟨subd1_5_27, List.forall_mem_cons.2 ⟨subd1_5_28, List.forall_mem_cons.2 ⟨subd1_5_29, List.forall_mem_cons.2 ⟨subd1_5_30, List.forall_mem_cons.2 ⟨subd1_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_5_32 : subd1_5 [2, 2] = true := by decide +kernel
theorem subd1_5_33 : subd1_5 [2, 3] = true := by decide +kernel
theorem sbd1_5_1 : ∀ q ∈ blkd1_5_1, subd1_5 q = true := by
  unfold blkd1_5_1
  exact List.forall_mem_cons.2 ⟨subd1_5_32, List.forall_mem_cons.2 ⟨subd1_5_33, List.forall_mem_nil _⟩⟩
theorem ld_okd1_6 : ldCheck G d1_6.U d1_6.ms ldd1_6 = true := by decide +kernel
theorem pre_okd1_6 : subPre G cell1 d1_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
