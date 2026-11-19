import ReflectZphi.Data.Cert5.C043.Base

namespace ReflectZphi.Data.Cert5.C043
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub1_992 : sub1 [4, 1, 4] = true := by decide +kernel
theorem sub1_993 : sub1 [4, 1, 5] = true := by decide +kernel
theorem sub1_994 : sub1 [4, 1, 6] = true := by decide +kernel
theorem sub1_995 : sub1 [4, 2] = true := by decide +kernel
theorem sub1_996 : sub1 [4, 3] = true := by decide +kernel
theorem sub1_997 : sub1 [4, 4] = true := by decide +kernel
theorem sub1_998 : sub1 [4, 5] = true := by decide +kernel
theorem sub1_999 : sub1 [5, -6] = true := by decide +kernel
theorem sub1_1000 : sub1 [5, -5] = true := by decide +kernel
theorem sub1_1001 : sub1 [5, -4] = true := by decide +kernel
theorem sub1_1002 : sub1 [5, -3] = true := by decide +kernel
theorem sub1_1003 : sub1 [5, -2] = true := by decide +kernel
theorem sub1_1004 : sub1 [5, -1] = true := by decide +kernel
theorem sub1_1005 : sub1 [5, 0] = true := by decide +kernel
theorem sub1_1006 : sub1 [5, 1] = true := by decide +kernel
theorem sub1_1007 : sub1 [5, 2] = true := by decide +kernel
theorem sub1_1008 : sub1 [5, 3] = true := by decide +kernel
theorem sub1_1009 : sub1 [5, 4] = true := by decide +kernel
theorem sub1_1010 : sub1 [6, -5] = true := by decide +kernel
theorem sub1_1011 : sub1 [6, -4] = true := by decide +kernel
theorem sub1_1012 : sub1 [6, -3] = true := by decide +kernel
theorem sub1_1013 : sub1 [6, -2] = true := by decide +kernel
theorem sub1_1014 : sub1 [6, -1] = true := by decide +kernel
theorem sub1_1015 : sub1 [6, 0] = true := by decide +kernel
theorem sub1_1016 : sub1 [6, 1] = true := by decide +kernel
theorem sub1_1017 : sub1 [6, 2] = true := by decide +kernel
theorem sub1_1018 : sub1 [7] = true := by decide +kernel
theorem sb1_31 : ∀ q ∈ blk1_31, sub1 q = true := by
  unfold blk1_31
  exact List.forall_mem_cons.2 ⟨sub1_992, List.forall_mem_cons.2 ⟨sub1_993, List.forall_mem_cons.2 ⟨sub1_994, List.forall_mem_cons.2 ⟨sub1_995, List.forall_mem_cons.2 ⟨sub1_996, List.forall_mem_cons.2 ⟨sub1_997, List.forall_mem_cons.2 ⟨sub1_998, List.forall_mem_cons.2 ⟨sub1_999, List.forall_mem_cons.2 ⟨sub1_1000, List.forall_mem_cons.2 ⟨sub1_1001, List.forall_mem_cons.2 ⟨sub1_1002, List.forall_mem_cons.2 ⟨sub1_1003, List.forall_mem_cons.2 ⟨sub1_1004, List.forall_mem_cons.2 ⟨sub1_1005, List.forall_mem_cons.2 ⟨sub1_1006, List.forall_mem_cons.2 ⟨sub1_1007, List.forall_mem_cons.2 ⟨sub1_1008, List.forall_mem_cons.2 ⟨sub1_1009, List.forall_mem_cons.2 ⟨sub1_1010, List.forall_mem_cons.2 ⟨sub1_1011, List.forall_mem_cons.2 ⟨sub1_1012, List.forall_mem_cons.2 ⟨sub1_1013, List.forall_mem_cons.2 ⟨sub1_1014, List.forall_mem_cons.2 ⟨sub1_1015, List.forall_mem_cons.2 ⟨sub1_1016, List.forall_mem_cons.2 ⟨sub1_1017, List.forall_mem_cons.2 ⟨sub1_1018, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_0 : sub2 [-2] = true := by decide +kernel
theorem sub2_1 : sub2 [-1, -2] = true := by decide +kernel
theorem sub2_2 : sub2 [-1, -1, -7] = true := by decide +kernel
theorem sub2_3 : sub2 [-1, -1, -6] = true := by decide +kernel
theorem sub2_4 : sub2 [-1, -1, -5] = true := by decide +kernel
theorem sub2_5 : sub2 [-1, -1, -4] = true := by decide +kernel
theorem sub2_6 : sub2 [-1, -1, -3] = true := by decide +kernel
theorem sub2_7 : sub2 [-1, -1, -2] = true := by decide +kernel
theorem sub2_8 : sub2 [-1, -1, -1] = true := by decide +kernel
theorem sub2_9 : sub2 [-1, -1, 0] = true := by decide +kernel
theorem sub2_10 : sub2 [-1, -1, 1] = true := by decide +kernel
theorem sub2_11 : sub2 [-1, -1, 2] = true := by decide +kernel
theorem sub2_12 : sub2 [-1, -1, 3] = true := by decide +kernel
theorem sub2_13 : sub2 [-1, -1, 4] = true := by decide +kernel
theorem sub2_14 : sub2 [-1, -1, 5] = true := by decide +kernel
theorem sub2_15 : sub2 [-1, -1, 6] = true := by decide +kernel
theorem sub2_16 : sub2 [-1, 0, -8] = true := by decide +kernel
theorem sub2_17 : sub2 [-1, 0, -7] = true := by decide +kernel
theorem sub2_18 : sub2 [-1, 0, -6] = true := by decide +kernel
theorem sub2_19 : sub2 [-1, 0, -5] = true := by decide +kernel
theorem sub2_20 : sub2 [-1, 0, -4] = true := by decide +kernel
theorem sub2_21 : sub2 [-1, 0, -3] = true := by decide +kernel
theorem sub2_22 : sub2 [-1, 0, -2] = true := by decide +kernel
theorem sub2_23 : sub2 [-1, 0, -1] = true := by decide +kernel
theorem sub2_24 : sub2 [-1, 0, 0] = true := by decide +kernel
theorem sub2_25 : sub2 [-1, 0, 1] = true := by decide +kernel
theorem sub2_26 : sub2 [-1, 0, 2] = true := by decide +kernel
theorem sub2_27 : sub2 [-1, 0, 3] = true := by decide +kernel
theorem sub2_28 : sub2 [-1, 0, 4] = true := by decide +kernel
theorem sub2_29 : sub2 [-1, 0, 5] = true := by decide +kernel
theorem sub2_30 : sub2 [-1, 0, 6] = true := by decide +kernel
theorem sub2_31 : sub2 [-1, 0, 7] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_cons.2 ⟨sub2_10, List.forall_mem_cons.2 ⟨sub2_11, List.forall_mem_cons.2 ⟨sub2_12, List.forall_mem_cons.2 ⟨sub2_13, List.forall_mem_cons.2 ⟨sub2_14, List.forall_mem_cons.2 ⟨sub2_15, List.forall_mem_cons.2 ⟨sub2_16, List.forall_mem_cons.2 ⟨sub2_17, List.forall_mem_cons.2 ⟨sub2_18, List.forall_mem_cons.2 ⟨sub2_19, List.forall_mem_cons.2 ⟨sub2_20, List.forall_mem_cons.2 ⟨sub2_21, List.forall_mem_cons.2 ⟨sub2_22, List.forall_mem_cons.2 ⟨sub2_23, List.forall_mem_cons.2 ⟨sub2_24, List.forall_mem_cons.2 ⟨sub2_25, List.forall_mem_cons.2 ⟨sub2_26, List.forall_mem_cons.2 ⟨sub2_27, List.forall_mem_cons.2 ⟨sub2_28, List.forall_mem_cons.2 ⟨sub2_29, List.forall_mem_cons.2 ⟨sub2_30, List.forall_mem_cons.2 ⟨sub2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_32 : sub2 [-1, 0, 8] = true := by decide +kernel
theorem sub2_33 : sub2 [-1, 1, -7] = true := by decide +kernel
theorem sub2_34 : sub2 [-1, 1, -6] = true := by decide +kernel
theorem sub2_35 : sub2 [-1, 1, -5] = true := by decide +kernel
theorem sub2_36 : sub2 [-1, 1, -4] = true := by decide +kernel
theorem sub2_37 : sub2 [-1, 1, -3] = true := by decide +kernel
theorem sub2_38 : sub2 [-1, 1, -2] = true := by decide +kernel
theorem sub2_39 : sub2 [-1, 1, -1] = true := by decide +kernel
theorem sub2_40 : sub2 [-1, 1, 0] = true := by decide +kernel
theorem sub2_41 : sub2 [-1, 1, 1] = true := by decide +kernel
theorem sub2_42 : sub2 [-1, 1, 2] = true := by decide +kernel
theorem sub2_43 : sub2 [-1, 1, 3] = true := by decide +kernel
theorem sub2_44 : sub2 [-1, 1, 4] = true := by decide +kernel
theorem sub2_45 : sub2 [-1, 1, 5] = true := by decide +kernel
theorem sub2_46 : sub2 [-1, 1, 6] = true := by decide +kernel
theorem sub2_47 : sub2 [-1, 1, 7] = true := by decide +kernel
theorem sub2_48 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_49 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_50 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_51 : sub2 [0, -1, -9] = true := by decide +kernel
theorem sub2_52 : sub2 [0, -1, -8] = true := by decide +kernel
theorem sub2_53 : sub2 [0, -1, -7] = true := by decide +kernel
theorem sub2_54 : sub2 [0, -1, -6] = true := by decide +kernel
theorem sub2_55 : sub2 [0, -1, -5] = true := by decide +kernel
theorem sub2_56 : sub2 [0, -1, -4] = true := by decide +kernel
theorem sub2_57 : sub2 [0, -1, -3] = true := by decide +kernel
theorem sub2_58 : sub2 [0, -1, -2] = true := by decide +kernel
theorem sub2_59 : sub2 [0, -1, -1] = true := by decide +kernel
theorem sub2_60 : sub2 [0, -1, 0] = true := by decide +kernel
theorem sub2_61 : sub2 [0, -1, 1] = true := by decide +kernel
theorem sub2_62 : sub2 [0, -1, 2] = true := by decide +kernel
theorem sub2_63 : sub2 [0, -1, 3] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_cons.2 ⟨sub2_60, List.forall_mem_cons.2 ⟨sub2_61, List.forall_mem_cons.2 ⟨sub2_62, List.forall_mem_cons.2 ⟨sub2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_64 : sub2 [0, -1, 4] = true := by decide +kernel
theorem sub2_65 : sub2 [0, -1, 5] = true := by decide +kernel
theorem sub2_66 : sub2 [0, -1, 6] = true := by decide +kernel
theorem sub2_67 : sub2 [0, -1, 7] = true := by decide +kernel
theorem sub2_68 : sub2 [0, 0, -9] = true := by decide +kernel
theorem sub2_69 : sub2 [0, 0, -8] = true := by decide +kernel
theorem sub2_70 : sub2 [0, 0, -7] = true := by decide +kernel
theorem sub2_71 : sub2 [0, 0, -6] = true := by decide +kernel
theorem sub2_72 : sub2 [0, 0, -5] = true := by decide +kernel
theorem sub2_73 : sub2 [0, 0, -4] = true := by decide +kernel
theorem sub2_74 : sub2 [0, 0, -3] = true := by decide +kernel
theorem sub2_75 : sub2 [0, 0, -2] = true := by decide +kernel
theorem sub2_76 : sub2 [0, 0, -1] = true := by decide +kernel
theorem sub2_77 : sub2 [0, 0, 0] = true := by decide +kernel
theorem sub2_78 : sub2 [0, 0, 1] = true := by decide +kernel
theorem sub2_79 : sub2 [0, 0, 2] = true := by decide +kernel
theorem sub2_80 : sub2 [0, 0, 3] = true := by decide +kernel
theorem sub2_81 : sub2 [0, 0, 4] = true := by decide +kernel
theorem sub2_82 : sub2 [0, 0, 5] = true := by decide +kernel
theorem sub2_83 : sub2 [0, 0, 6] = true := by decide +kernel
theorem sub2_84 : sub2 [0, 0, 7] = true := by decide +kernel
theorem sub2_85 : sub2 [0, 0, 8] = true := by decide +kernel
theorem sub2_86 : sub2 [0, 1, -8] = true := by decide +kernel
theorem sub2_87 : sub2 [0, 1, -7] = true := by decide +kernel
theorem sub2_88 : sub2 [0, 1, -6] = true := by decide +kernel
theorem sub2_89 : sub2 [0, 1, -5] = true := by decide +kernel
theorem sub2_90 : sub2 [0, 1, -4] = true := by decide +kernel
theorem sub2_91 : sub2 [0, 1, -3] = true := by decide +kernel
theorem sub2_92 : sub2 [0, 1, -2] = true := by decide +kernel
theorem sub2_93 : sub2 [0, 1, -1] = true := by decide +kernel
theorem sub2_94 : sub2 [0, 1, 0] = true := by decide +kernel
theorem sub2_95 : sub2 [0, 1, 1] = true := by decide +kernel
theorem sb2_2 : ∀ q ∈ blk2_2, sub2 q = true := by
  unfold blk2_2
  exact List.forall_mem_cons.2 ⟨sub2_64, List.forall_mem_cons.2 ⟨sub2_65, List.forall_mem_cons.2 ⟨sub2_66, List.forall_mem_cons.2 ⟨sub2_67, List.forall_mem_cons.2 ⟨sub2_68, List.forall_mem_cons.2 ⟨sub2_69, List.forall_mem_cons.2 ⟨sub2_70, List.forall_mem_cons.2 ⟨sub2_71, List.forall_mem_cons.2 ⟨sub2_72, List.forall_mem_cons.2 ⟨sub2_73, List.forall_mem_cons.2 ⟨sub2_74, List.forall_mem_cons.2 ⟨sub2_75, List.forall_mem_cons.2 ⟨sub2_76, List.forall_mem_cons.2 ⟨sub2_77, List.forall_mem_cons.2 ⟨sub2_78, List.forall_mem_cons.2 ⟨sub2_79, List.forall_mem_cons.2 ⟨sub2_80, List.forall_mem_cons.2 ⟨sub2_81, List.forall_mem_cons.2 ⟨sub2_82, List.forall_mem_cons.2 ⟨sub2_83, List.forall_mem_cons.2 ⟨sub2_84, List.forall_mem_cons.2 ⟨sub2_85, List.forall_mem_cons.2 ⟨sub2_86, List.forall_mem_cons.2 ⟨sub2_87, List.forall_mem_cons.2 ⟨sub2_88, List.forall_mem_cons.2 ⟨sub2_89, List.forall_mem_cons.2 ⟨sub2_90, List.forall_mem_cons.2 ⟨sub2_91, List.forall_mem_cons.2 ⟨sub2_92, List.forall_mem_cons.2 ⟨sub2_93, List.forall_mem_cons.2 ⟨sub2_94, List.forall_mem_cons.2 ⟨sub2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_96 : sub2 [0, 1, 2] = true := by decide +kernel
theorem sub2_97 : sub2 [0, 1, 3] = true := by decide +kernel
theorem sub2_98 : sub2 [0, 1, 4] = true := by decide +kernel
theorem sub2_99 : sub2 [0, 1, 5] = true := by decide +kernel
theorem sub2_100 : sub2 [0, 1, 6] = true := by decide +kernel
theorem sub2_101 : sub2 [0, 1, 7] = true := by decide +kernel
theorem sub2_102 : sub2 [0, 1, 8] = true := by decide +kernel
theorem sub2_103 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_104 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_105 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_106 : sub2 [1, -1, -8] = true := by decide +kernel
theorem sub2_107 : sub2 [1, -1, -7] = true := by decide +kernel
theorem sub2_108 : sub2 [1, -1, -6] = true := by decide +kernel
theorem sub2_109 : sub2 [1, -1, -5] = true := by decide +kernel
theorem sub2_110 : sub2 [1, -1, -4] = true := by decide +kernel
theorem sub2_111 : sub2 [1, -1, -3] = true := by decide +kernel
theorem sub2_112 : sub2 [1, -1, -2] = true := by decide +kernel
theorem sub2_113 : sub2 [1, -1, -1] = true := by decide +kernel
theorem sub2_114 : sub2 [1, -1, 0] = true := by decide +kernel
theorem sub2_115 : sub2 [1, -1, 1] = true := by decide +kernel
theorem sub2_116 : sub2 [1, -1, 2] = true := by decide +kernel
theorem sub2_117 : sub2 [1, -1, 3] = true := by decide +kernel
theorem sub2_118 : sub2 [1, -1, 4] = true := by decide +kernel
theorem sub2_119 : sub2 [1, -1, 5] = true := by decide +kernel
theorem sub2_120 : sub2 [1, -1, 6] = true := by decide +kernel
theorem sub2_121 : sub2 [1, 0, -9] = true := by decide +kernel
theorem sub2_122 : sub2 [1, 0, -8] = true := by decide +kernel
theorem sub2_123 : sub2 [1, 0, -7] = true := by decide +kernel
theorem sub2_124 : sub2 [1, 0, -6] = true := by decide +kernel
theorem sub2_125 : sub2 [1, 0, -5] = true := by decide +kernel
theorem sub2_126 : sub2 [1, 0, -4] = true := by decide +kernel
theorem sub2_127 : sub2 [1, 0, -3] = true := by decide +kernel
theorem sb2_3 : ∀ q ∈ blk2_3, sub2 q = true := by
  unfold blk2_3
  exact List.forall_mem_cons.2 ⟨sub2_96, List.forall_mem_cons.2 ⟨sub2_97, List.forall_mem_cons.2 ⟨sub2_98, List.forall_mem_cons.2 ⟨sub2_99, List.forall_mem_cons.2 ⟨sub2_100, List.forall_mem_cons.2 ⟨sub2_101, List.forall_mem_cons.2 ⟨sub2_102, List.forall_mem_cons.2 ⟨sub2_103, List.forall_mem_cons.2 ⟨sub2_104, List.forall_mem_cons.2 ⟨sub2_105, List.forall_mem_cons.2 ⟨sub2_106, List.forall_mem_cons.2 ⟨sub2_107, List.forall_mem_cons.2 ⟨sub2_108, List.forall_mem_cons.2 ⟨sub2_109, List.forall_mem_cons.2 ⟨sub2_110, List.forall_mem_cons.2 ⟨sub2_111, List.forall_mem_cons.2 ⟨sub2_112, List.forall_mem_cons.2 ⟨sub2_113, List.forall_mem_cons.2 ⟨sub2_114, List.forall_mem_cons.2 ⟨sub2_115, List.forall_mem_cons.2 ⟨sub2_116, List.forall_mem_cons.2 ⟨sub2_117, List.forall_mem_cons.2 ⟨sub2_118, List.forall_mem_cons.2 ⟨sub2_119, List.forall_mem_cons.2 ⟨sub2_120, List.forall_mem_cons.2 ⟨sub2_121, List.forall_mem_cons.2 ⟨sub2_122, List.forall_mem_cons.2 ⟨sub2_123, List.forall_mem_cons.2 ⟨sub2_124, List.forall_mem_cons.2 ⟨sub2_125, List.forall_mem_cons.2 ⟨sub2_126, List.forall_mem_cons.2 ⟨sub2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_128 : sub2 [1, 0, -2] = true := by decide +kernel
theorem sub2_129 : sub2 [1, 0, -1] = true := by decide +kernel
theorem sub2_130 : sub2 [1, 0, 0] = true := by decide +kernel
theorem sub2_131 : sub2 [1, 0, 1] = true := by decide +kernel
theorem sub2_132 : sub2 [1, 0, 2] = true := by decide +kernel
theorem sub2_133 : sub2 [1, 0, 3] = true := by decide +kernel
theorem sub2_134 : sub2 [1, 0, 4] = true := by decide +kernel
theorem sub2_135 : sub2 [1, 0, 5] = true := by decide +kernel
theorem sub2_136 : sub2 [1, 0, 6] = true := by decide +kernel
theorem sub2_137 : sub2 [1, 0, 7] = true := by decide +kernel
theorem sub2_138 : sub2 [1, 1, -7] = true := by decide +kernel
theorem sub2_139 : sub2 [1, 1, -6] = true := by decide +kernel
theorem sub2_140 : sub2 [1, 1, -5] = true := by decide +kernel
theorem sub2_141 : sub2 [1, 1, -4] = true := by decide +kernel
theorem sub2_142 : sub2 [1, 1, -3] = true := by decide +kernel
theorem sub2_143 : sub2 [1, 1, -2] = true := by decide +kernel
theorem sub2_144 : sub2 [1, 1, -1] = true := by decide +kernel
theorem sub2_145 : sub2 [1, 1, 0] = true := by decide +kernel
theorem sub2_146 : sub2 [1, 1, 1] = true := by decide +kernel
theorem sub2_147 : sub2 [1, 1, 2] = true := by decide +kernel
theorem sub2_148 : sub2 [1, 1, 3] = true := by decide +kernel
theorem sub2_149 : sub2 [1, 1, 4] = true := by decide +kernel
theorem sub2_150 : sub2 [1, 1, 5] = true := by decide +kernel
theorem sub2_151 : sub2 [1, 1, 6] = true := by decide +kernel
theorem sub2_152 : sub2 [2] = true := by decide +kernel
theorem sb2_4 : ∀ q ∈ blk2_4, sub2 q = true := by
  unfold blk2_4
  exact List.forall_mem_cons.2 ⟨sub2_128, List.forall_mem_cons.2 ⟨sub2_129, List.forall_mem_cons.2 ⟨sub2_130, List.forall_mem_cons.2 ⟨sub2_131, List.forall_mem_cons.2 ⟨sub2_132, List.forall_mem_cons.2 ⟨sub2_133, List.forall_mem_cons.2 ⟨sub2_134, List.forall_mem_cons.2 ⟨sub2_135, List.forall_mem_cons.2 ⟨sub2_136, List.forall_mem_cons.2 ⟨sub2_137, List.forall_mem_cons.2 ⟨sub2_138, List.forall_mem_cons.2 ⟨sub2_139, List.forall_mem_cons.2 ⟨sub2_140, List.forall_mem_cons.2 ⟨sub2_141, List.forall_mem_cons.2 ⟨sub2_142, List.forall_mem_cons.2 ⟨sub2_143, List.forall_mem_cons.2 ⟨sub2_144, List.forall_mem_cons.2 ⟨sub2_145, List.forall_mem_cons.2 ⟨sub2_146, List.forall_mem_cons.2 ⟨sub2_147, List.forall_mem_cons.2 ⟨sub2_148, List.forall_mem_cons.2 ⟨sub2_149, List.forall_mem_cons.2 ⟨sub2_150, List.forall_mem_cons.2 ⟨sub2_151, List.forall_mem_cons.2 ⟨sub2_152, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_1 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_2 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_3 : sub3 [-2, 0] = true := by decide +kernel
theorem sub3_4 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_5 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_6 : sub3 [-1, -2, -6] = true := by decide +kernel
theorem sub3_7 : sub3 [-1, -2, -5] = true := by decide +kernel
theorem sub3_8 : sub3 [-1, -2, -4] = true := by decide +kernel
theorem sub3_9 : sub3 [-1, -2, -3] = true := by decide +kernel
theorem sub3_10 : sub3 [-1, -2, -2] = true := by decide +kernel
theorem sub3_11 : sub3 [-1, -2, -1] = true := by decide +kernel
theorem sub3_12 : sub3 [-1, -2, 0] = true := by decide +kernel
theorem sub3_13 : sub3 [-1, -2, 1] = true := by decide +kernel
theorem sub3_14 : sub3 [-1, -2, 2] = true := by decide +kernel
theorem sub3_15 : sub3 [-1, -2, 3] = true := by decide +kernel
theorem sub3_16 : sub3 [-1, -2, 4] = true := by decide +kernel
theorem sub3_17 : sub3 [-1, -2, 5] = true := by decide +kernel
theorem sub3_18 : sub3 [-1, -2, 6] = true := by decide +kernel
theorem sub3_19 : sub3 [-1, -2, 7] = true := by decide +kernel
theorem sub3_20 : sub3 [-1, -1, -8] = true := by decide +kernel
theorem sub3_21 : sub3 [-1, -1, -7] = true := by decide +kernel
theorem sub3_22 : sub3 [-1, -1, -6] = true := by decide +kernel
theorem sub3_23 : sub3 [-1, -1, -5] = true := by decide +kernel
theorem sub3_24 : sub3 [-1, -1, -4] = true := by decide +kernel
theorem sub3_25 : sub3 [-1, -1, -3] = true := by decide +kernel
theorem sub3_26 : sub3 [-1, -1, -2] = true := by decide +kernel
theorem sub3_27 : sub3 [-1, -1, -1] = true := by decide +kernel
theorem sub3_28 : sub3 [-1, -1, 0] = true := by decide +kernel
theorem sub3_29 : sub3 [-1, -1, 1] = true := by decide +kernel
theorem sub3_30 : sub3 [-1, -1, 2] = true := by decide +kernel
theorem sub3_31 : sub3 [-1, -1, 3] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-1, -1, 4] = true := by decide +kernel
theorem sub3_33 : sub3 [-1, -1, 5] = true := by decide +kernel
theorem sub3_34 : sub3 [-1, -1, 6] = true := by decide +kernel
theorem sub3_35 : sub3 [-1, -1, 7] = true := by decide +kernel
theorem sub3_36 : sub3 [-1, -1, 8] = true := by decide +kernel
theorem sub3_37 : sub3 [-1, 0, -8] = true := by decide +kernel
theorem sub3_38 : sub3 [-1, 0, -7] = true := by decide +kernel
theorem sub3_39 : sub3 [-1, 0, -6] = true := by decide +kernel
theorem sub3_40 : sub3 [-1, 0, -5] = true := by decide +kernel
theorem sub3_41 : sub3 [-1, 0, -4] = true := by decide +kernel
theorem sub3_42 : sub3 [-1, 0, -3] = true := by decide +kernel
theorem sub3_43 : sub3 [-1, 0, -2] = true := by decide +kernel
theorem sub3_44 : sub3 [-1, 0, -1] = true := by decide +kernel
theorem sub3_45 : sub3 [-1, 0, 0] = true := by decide +kernel
theorem sub3_46 : sub3 [-1, 0, 1] = true := by decide +kernel
theorem sub3_47 : sub3 [-1, 0, 2] = true := by decide +kernel
theorem sub3_48 : sub3 [-1, 0, 3] = true := by decide +kernel
theorem sub3_49 : sub3 [-1, 0, 4] = true := by decide +kernel
theorem sub3_50 : sub3 [-1, 0, 5] = true := by decide +kernel
theorem sub3_51 : sub3 [-1, 0, 6] = true := by decide +kernel
theorem sub3_52 : sub3 [-1, 0, 7] = true := by decide +kernel
theorem sub3_53 : sub3 [-1, 1, -7] = true := by decide +kernel
theorem sub3_54 : sub3 [-1, 1, -6] = true := by decide +kernel
theorem sub3_55 : sub3 [-1, 1, -5] = true := by decide +kernel
theorem sub3_56 : sub3 [-1, 1, -4] = true := by decide +kernel
theorem sub3_57 : sub3 [-1, 1, -3] = true := by decide +kernel
theorem sub3_58 : sub3 [-1, 1, -2] = true := by decide +kernel
theorem sub3_59 : sub3 [-1, 1, -1] = true := by decide +kernel
theorem sub3_60 : sub3 [-1, 1, 0] = true := by decide +kernel
theorem sub3_61 : sub3 [-1, 1, 1] = true := by decide +kernel
theorem sub3_62 : sub3 [-1, 1, 2] = true := by decide +kernel
theorem sub3_63 : sub3 [-1, 1, 3] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [-1, 1, 4] = true := by decide +kernel
theorem sub3_65 : sub3 [-1, 1, 5] = true := by decide +kernel
theorem sub3_66 : sub3 [-1, 1, 6] = true := by decide +kernel
theorem sub3_67 : sub3 [-1, 2] = true := by decide +kernel
theorem sub3_68 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_69 : sub3 [0, -2] = true := by decide +kernel
theorem sub3_70 : sub3 [0, -1, -8] = true := by decide +kernel
theorem sub3_71 : sub3 [0, -1, -7] = true := by decide +kernel
theorem sub3_72 : sub3 [0, -1, -6] = true := by decide +kernel
theorem sub3_73 : sub3 [0, -1, -5] = true := by decide +kernel
theorem sub3_74 : sub3 [0, -1, -4] = true := by decide +kernel
theorem sub3_75 : sub3 [0, -1, -3] = true := by decide +kernel
theorem sub3_76 : sub3 [0, -1, -2] = true := by decide +kernel
theorem sub3_77 : sub3 [0, -1, -1] = true := by decide +kernel
theorem sub3_78 : sub3 [0, -1, 0] = true := by decide +kernel
theorem sub3_79 : sub3 [0, -1, 1] = true := by decide +kernel
theorem sub3_80 : sub3 [0, -1, 2] = true := by decide +kernel
theorem sub3_81 : sub3 [0, -1, 3] = true := by decide +kernel
theorem sub3_82 : sub3 [0, -1, 4] = true := by decide +kernel
theorem sub3_83 : sub3 [0, -1, 5] = true := by decide +kernel
theorem sub3_84 : sub3 [0, -1, 6] = true := by decide +kernel
theorem sub3_85 : sub3 [0, -1, 7] = true := by decide +kernel
theorem sub3_86 : sub3 [0, -1, 8] = true := by decide +kernel
theorem sub3_87 : sub3 [0, 0, -9] = true := by decide +kernel
theorem sub3_88 : sub3 [0, 0, -8] = true := by decide +kernel
theorem sub3_89 : sub3 [0, 0, -7] = true := by decide +kernel
theorem sub3_90 : sub3 [0, 0, -6] = true := by decide +kernel
theorem sub3_91 : sub3 [0, 0, -5] = true := by decide +kernel
theorem sub3_92 : sub3 [0, 0, -4] = true := by decide +kernel
theorem sub3_93 : sub3 [0, 0, -3] = true := by decide +kernel
theorem sub3_94 : sub3 [0, 0, -2] = true := by decide +kernel
theorem sub3_95 : sub3 [0, 0, -1] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [0, 0, 0] = true := by decide +kernel
theorem sub3_97 : sub3 [0, 0, 1] = true := by decide +kernel
theorem sub3_98 : sub3 [0, 0, 2] = true := by decide +kernel
theorem sub3_99 : sub3 [0, 0, 3] = true := by decide +kernel
theorem sub3_100 : sub3 [0, 0, 4] = true := by decide +kernel
theorem sub3_101 : sub3 [0, 0, 5] = true := by decide +kernel
theorem sub3_102 : sub3 [0, 0, 6] = true := by decide +kernel
theorem sub3_103 : sub3 [0, 0, 7] = true := by decide +kernel
theorem sub3_104 : sub3 [0, 0, 8] = true := by decide +kernel
theorem sub3_105 : sub3 [0, 1, -9] = true := by decide +kernel
theorem sub3_106 : sub3 [0, 1, -8] = true := by decide +kernel
theorem sub3_107 : sub3 [0, 1, -7] = true := by decide +kernel
theorem sub3_108 : sub3 [0, 1, -6] = true := by decide +kernel
theorem sub3_109 : sub3 [0, 1, -5] = true := by decide +kernel
theorem sub3_110 : sub3 [0, 1, -4] = true := by decide +kernel
theorem sub3_111 : sub3 [0, 1, -3] = true := by decide +kernel
theorem sub3_112 : sub3 [0, 1, -2] = true := by decide +kernel
theorem sub3_113 : sub3 [0, 1, -1] = true := by decide +kernel
theorem sub3_114 : sub3 [0, 1, 0] = true := by decide +kernel
theorem sub3_115 : sub3 [0, 1, 1] = true := by decide +kernel
theorem sub3_116 : sub3 [0, 1, 2] = true := by decide +kernel
theorem sub3_117 : sub3 [0, 1, 3] = true := by decide +kernel
theorem sub3_118 : sub3 [0, 1, 4] = true := by decide +kernel
theorem sub3_119 : sub3 [0, 1, 5] = true := by decide +kernel
theorem sub3_120 : sub3 [0, 1, 6] = true := by decide +kernel
theorem sub3_121 : sub3 [0, 1, 7] = true := by decide +kernel
theorem sub3_122 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_123 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_124 : sub3 [1, -2] = true := by decide +kernel
theorem sub3_125 : sub3 [1, -1, -7] = true := by decide +kernel
theorem sub3_126 : sub3 [1, -1, -6] = true := by decide +kernel
theorem sub3_127 : sub3 [1, -1, -5] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_128 : sub3 [1, -1, -4] = true := by decide +kernel
theorem sub3_129 : sub3 [1, -1, -3] = true := by decide +kernel
theorem sub3_130 : sub3 [1, -1, -2] = true := by decide +kernel
theorem sub3_131 : sub3 [1, -1, -1] = true := by decide +kernel
theorem sub3_132 : sub3 [1, -1, 0] = true := by decide +kernel
theorem sub3_133 : sub3 [1, -1, 1] = true := by decide +kernel
theorem sub3_134 : sub3 [1, -1, 2] = true := by decide +kernel
theorem sub3_135 : sub3 [1, -1, 3] = true := by decide +kernel
theorem sub3_136 : sub3 [1, -1, 4] = true := by decide +kernel
theorem sub3_137 : sub3 [1, -1, 5] = true := by decide +kernel
theorem sub3_138 : sub3 [1, -1, 6] = true := by decide +kernel
theorem sub3_139 : sub3 [1, 0, -8] = true := by decide +kernel
theorem sub3_140 : sub3 [1, 0, -7] = true := by decide +kernel
theorem sub3_141 : sub3 [1, 0, -6] = true := by decide +kernel
theorem sub3_142 : sub3 [1, 0, -5] = true := by decide +kernel
theorem sub3_143 : sub3 [1, 0, -4] = true := by decide +kernel
theorem sub3_144 : sub3 [1, 0, -3] = true := by decide +kernel
theorem sub3_145 : sub3 [1, 0, -2] = true := by decide +kernel
theorem sub3_146 : sub3 [1, 0, -1] = true := by decide +kernel
theorem sub3_147 : sub3 [1, 0, 0] = true := by decide +kernel
theorem sub3_148 : sub3 [1, 0, 1] = true := by decide +kernel
theorem sub3_149 : sub3 [1, 0, 2] = true := by decide +kernel
theorem sub3_150 : sub3 [1, 0, 3] = true := by decide +kernel
theorem sub3_151 : sub3 [1, 0, 4] = true := by decide +kernel
theorem sub3_152 : sub3 [1, 0, 5] = true := by decide +kernel
theorem sub3_153 : sub3 [1, 0, 6] = true := by decide +kernel
theorem sub3_154 : sub3 [1, 0, 7] = true := by decide +kernel
theorem sub3_155 : sub3 [1, 1, -9] = true := by decide +kernel
theorem sub3_156 : sub3 [1, 1, -8] = true := by decide +kernel
theorem sub3_157 : sub3 [1, 1, -7] = true := by decide +kernel
theorem sub3_158 : sub3 [1, 1, -6] = true := by decide +kernel
theorem sub3_159 : sub3 [1, 1, -5] = true := by decide +kernel
theorem sb3_4 : ∀ q ∈ blk3_4, sub3 q = true := by
  unfold blk3_4
  exact List.forall_mem_cons.2 ⟨sub3_128, List.forall_mem_cons.2 ⟨sub3_129, List.forall_mem_cons.2 ⟨sub3_130, List.forall_mem_cons.2 ⟨sub3_131, List.forall_mem_cons.2 ⟨sub3_132, List.forall_mem_cons.2 ⟨sub3_133, List.forall_mem_cons.2 ⟨sub3_134, List.forall_mem_cons.2 ⟨sub3_135, List.forall_mem_cons.2 ⟨sub3_136, List.forall_mem_cons.2 ⟨sub3_137, List.forall_mem_cons.2 ⟨sub3_138, List.forall_mem_cons.2 ⟨sub3_139, List.forall_mem_cons.2 ⟨sub3_140, List.forall_mem_cons.2 ⟨sub3_141, List.forall_mem_cons.2 ⟨sub3_142, List.forall_mem_cons.2 ⟨sub3_143, List.forall_mem_cons.2 ⟨sub3_144, List.forall_mem_cons.2 ⟨sub3_145, List.forall_mem_cons.2 ⟨sub3_146, List.forall_mem_cons.2 ⟨sub3_147, List.forall_mem_cons.2 ⟨sub3_148, List.forall_mem_cons.2 ⟨sub3_149, List.forall_mem_cons.2 ⟨sub3_150, List.forall_mem_cons.2 ⟨sub3_151, List.forall_mem_cons.2 ⟨sub3_152, List.forall_mem_cons.2 ⟨sub3_153, List.forall_mem_cons.2 ⟨sub3_154, List.forall_mem_cons.2 ⟨sub3_155, List.forall_mem_cons.2 ⟨sub3_156, List.forall_mem_cons.2 ⟨sub3_157, List.forall_mem_cons.2 ⟨sub3_158, List.forall_mem_cons.2 ⟨sub3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_160 : sub3 [1, 1, -4] = true := by decide +kernel
theorem sub3_161 : sub3 [1, 1, -3] = true := by decide +kernel
theorem sub3_162 : sub3 [1, 1, -2] = true := by decide +kernel
theorem sub3_163 : sub3 [1, 1, -1] = true := by decide +kernel
theorem sub3_164 : sub3 [1, 1, 0] = true := by decide +kernel
theorem sub3_165 : sub3 [1, 1, 1] = true := by decide +kernel
theorem sub3_166 : sub3 [1, 1, 2] = true := by decide +kernel
theorem sub3_167 : sub3 [1, 1, 3] = true := by decide +kernel
theorem sub3_168 : sub3 [1, 1, 4] = true := by decide +kernel
theorem sub3_169 : sub3 [1, 1, 5] = true := by decide +kernel
theorem sub3_170 : sub3 [1, 1, 6] = true := by decide +kernel
theorem sub3_171 : sub3 [1, 1, 7] = true := by decide +kernel
theorem sub3_172 : sub3 [1, 2, -8] = true := by decide +kernel
theorem sub3_173 : sub3 [1, 2, -7] = true := by decide +kernel
theorem sub3_174 : sub3 [1, 2, -6] = true := by decide +kernel
theorem sub3_175 : sub3 [1, 2, -5] = true := by decide +kernel
theorem sub3_176 : sub3 [1, 2, -4] = true := by decide +kernel
theorem sub3_177 : sub3 [1, 2, -3] = true := by decide +kernel
theorem sub3_178 : sub3 [1, 2, -2] = true := by decide +kernel
theorem sub3_179 : sub3 [1, 2, -1] = true := by decide +kernel
theorem sub3_180 : sub3 [1, 2, 0] = true := by decide +kernel
theorem sub3_181 : sub3 [1, 2, 1] = true := by decide +kernel
theorem sub3_182 : sub3 [1, 2, 2] = true := by decide +kernel
theorem sub3_183 : sub3 [1, 2, 3] = true := by decide +kernel
theorem sub3_184 : sub3 [1, 2, 4] = true := by decide +kernel
theorem sub3_185 : sub3 [1, 2, 5] = true := by decide +kernel
theorem sub3_186 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_187 : sub3 [2, -1] = true := by decide +kernel
theorem sub3_188 : sub3 [2, 0] = true := by decide +kernel
theorem sub3_189 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_190 : sub3 [2, 2] = true := by decide +kernel
theorem sb3_5 : ∀ q ∈ blk3_5, sub3 q = true := by
  unfold blk3_5
  exact List.forall_mem_cons.2 ⟨sub3_160, List.forall_mem_cons.2 ⟨sub3_161, List.forall_mem_cons.2 ⟨sub3_162, List.forall_mem_cons.2 ⟨sub3_163, List.forall_mem_cons.2 ⟨sub3_164, List.forall_mem_cons.2 ⟨sub3_165, List.forall_mem_cons.2 ⟨sub3_166, List.forall_mem_cons.2 ⟨sub3_167, List.forall_mem_cons.2 ⟨sub3_168, List.forall_mem_cons.2 ⟨sub3_169, List.forall_mem_cons.2 ⟨sub3_170, List.forall_mem_cons.2 ⟨sub3_171, List.forall_mem_cons.2 ⟨sub3_172, List.forall_mem_cons.2 ⟨sub3_173, List.forall_mem_cons.2 ⟨sub3_174, List.forall_mem_cons.2 ⟨sub3_175, List.forall_mem_cons.2 ⟨sub3_176, List.forall_mem_cons.2 ⟨sub3_177, List.forall_mem_cons.2 ⟨sub3_178, List.forall_mem_cons.2 ⟨sub3_179, List.forall_mem_cons.2 ⟨sub3_180, List.forall_mem_cons.2 ⟨sub3_181, List.forall_mem_cons.2 ⟨sub3_182, List.forall_mem_cons.2 ⟨sub3_183, List.forall_mem_cons.2 ⟨sub3_184, List.forall_mem_cons.2 ⟨sub3_185, List.forall_mem_cons.2 ⟨sub3_186, List.forall_mem_cons.2 ⟨sub3_187, List.forall_mem_cons.2 ⟨sub3_188, List.forall_mem_cons.2 ⟨sub3_189, List.forall_mem_cons.2 ⟨sub3_190, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C043
