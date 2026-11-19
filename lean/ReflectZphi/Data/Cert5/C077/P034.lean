import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-3] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-2] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [-1, -4] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [-1, -3] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [-1, -2] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [-1, -1] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [-1, 0] = true := by decide +kernel
theorem subd13_2_7 : subd13_2 [-1, 1] = true := by decide +kernel
theorem subd13_2_8 : subd13_2 [-1, 2] = true := by decide +kernel
theorem subd13_2_9 : subd13_2 [-1, 3] = true := by decide +kernel
theorem subd13_2_10 : subd13_2 [0, -4] = true := by decide +kernel
theorem subd13_2_11 : subd13_2 [0, -3] = true := by decide +kernel
theorem subd13_2_12 : subd13_2 [0, -2] = true := by decide +kernel
theorem subd13_2_13 : subd13_2 [0, -1] = true := by decide +kernel
theorem subd13_2_14 : subd13_2 [0, 0] = true := by decide +kernel
theorem subd13_2_15 : subd13_2 [0, 1] = true := by decide +kernel
theorem subd13_2_16 : subd13_2 [0, 2] = true := by decide +kernel
theorem subd13_2_17 : subd13_2 [0, 3] = true := by decide +kernel
theorem subd13_2_18 : subd13_2 [1, -4] = true := by decide +kernel
theorem subd13_2_19 : subd13_2 [1, -3] = true := by decide +kernel
theorem subd13_2_20 : subd13_2 [1, -2] = true := by decide +kernel
theorem subd13_2_21 : subd13_2 [1, -1] = true := by decide +kernel
theorem subd13_2_22 : subd13_2 [1, 0] = true := by decide +kernel
theorem subd13_2_23 : subd13_2 [1, 1] = true := by decide +kernel
theorem subd13_2_24 : subd13_2 [1, 2] = true := by decide +kernel
theorem subd13_2_25 : subd13_2 [1, 3] = true := by decide +kernel
theorem subd13_2_26 : subd13_2 [2] = true := by decide +kernel
theorem subd13_2_27 : subd13_2 [3] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_cons.2 ⟨subd13_2_7, List.forall_mem_cons.2 ⟨subd13_2_8, List.forall_mem_cons.2 ⟨subd13_2_9, List.forall_mem_cons.2 ⟨subd13_2_10, List.forall_mem_cons.2 ⟨subd13_2_11, List.forall_mem_cons.2 ⟨subd13_2_12, List.forall_mem_cons.2 ⟨subd13_2_13, List.forall_mem_cons.2 ⟨subd13_2_14, List.forall_mem_cons.2 ⟨subd13_2_15, List.forall_mem_cons.2 ⟨subd13_2_16, List.forall_mem_cons.2 ⟨subd13_2_17, List.forall_mem_cons.2 ⟨subd13_2_18, List.forall_mem_cons.2 ⟨subd13_2_19, List.forall_mem_cons.2 ⟨subd13_2_20, List.forall_mem_cons.2 ⟨subd13_2_21, List.forall_mem_cons.2 ⟨subd13_2_22, List.forall_mem_cons.2 ⟨subd13_2_23, List.forall_mem_cons.2 ⟨subd13_2_24, List.forall_mem_cons.2 ⟨subd13_2_25, List.forall_mem_cons.2 ⟨subd13_2_26, List.forall_mem_cons.2 ⟨subd13_2_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-2, -4] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2, -3] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-2, -2] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-2, -1] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-2, 0] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-2, 1] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-1, -4] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [-1, -3] = true := by decide +kernel
theorem subd13_3_8 : subd13_3 [-1, -2] = true := by decide +kernel
theorem subd13_3_9 : subd13_3 [-1, -1, -8] = true := by decide +kernel
theorem subd13_3_10 : subd13_3 [-1, -1, -7] = true := by decide +kernel
theorem subd13_3_11 : subd13_3 [-1, -1, -6] = true := by decide +kernel
theorem subd13_3_12 : subd13_3 [-1, -1, -5] = true := by decide +kernel
theorem subd13_3_13 : subd13_3 [-1, -1, -4] = true := by decide +kernel
theorem subd13_3_14 : subd13_3 [-1, -1, -3] = true := by decide +kernel
theorem subd13_3_15 : subd13_3 [-1, -1, -2] = true := by decide +kernel
theorem subd13_3_16 : subd13_3 [-1, -1, -1] = true := by decide +kernel
theorem subd13_3_17 : subd13_3 [-1, -1, 0] = true := by decide +kernel
theorem subd13_3_18 : subd13_3 [-1, -1, 1] = true := by decide +kernel
theorem subd13_3_19 : subd13_3 [-1, -1, 2] = true := by decide +kernel
theorem subd13_3_20 : subd13_3 [-1, -1, 3] = true := by decide +kernel
theorem subd13_3_21 : subd13_3 [-1, -1, 4] = true := by decide +kernel
theorem subd13_3_22 : subd13_3 [-1, -1, 5] = true := by decide +kernel
theorem subd13_3_23 : subd13_3 [-1, -1, 6] = true := by decide +kernel
theorem subd13_3_24 : subd13_3 [-1, -1, 7] = true := by decide +kernel
theorem subd13_3_25 : subd13_3 [-1, 0, -8] = true := by decide +kernel
theorem subd13_3_26 : subd13_3 [-1, 0, -7] = true := by decide +kernel
theorem subd13_3_27 : subd13_3 [-1, 0, -6] = true := by decide +kernel
theorem subd13_3_28 : subd13_3 [-1, 0, -5] = true := by decide +kernel
theorem subd13_3_29 : subd13_3 [-1, 0, -4] = true := by decide +kernel
theorem subd13_3_30 : subd13_3 [-1, 0, -3] = true := by decide +kernel
theorem subd13_3_31 : subd13_3 [-1, 0, -2] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_cons.2 ⟨subd13_3_7, List.forall_mem_cons.2 ⟨subd13_3_8, List.forall_mem_cons.2 ⟨subd13_3_9, List.forall_mem_cons.2 ⟨subd13_3_10, List.forall_mem_cons.2 ⟨subd13_3_11, List.forall_mem_cons.2 ⟨subd13_3_12, List.forall_mem_cons.2 ⟨subd13_3_13, List.forall_mem_cons.2 ⟨subd13_3_14, List.forall_mem_cons.2 ⟨subd13_3_15, List.forall_mem_cons.2 ⟨subd13_3_16, List.forall_mem_cons.2 ⟨subd13_3_17, List.forall_mem_cons.2 ⟨subd13_3_18, List.forall_mem_cons.2 ⟨subd13_3_19, List.forall_mem_cons.2 ⟨subd13_3_20, List.forall_mem_cons.2 ⟨subd13_3_21, List.forall_mem_cons.2 ⟨subd13_3_22, List.forall_mem_cons.2 ⟨subd13_3_23, List.forall_mem_cons.2 ⟨subd13_3_24, List.forall_mem_cons.2 ⟨subd13_3_25, List.forall_mem_cons.2 ⟨subd13_3_26, List.forall_mem_cons.2 ⟨subd13_3_27, List.forall_mem_cons.2 ⟨subd13_3_28, List.forall_mem_cons.2 ⟨subd13_3_29, List.forall_mem_cons.2 ⟨subd13_3_30, List.forall_mem_cons.2 ⟨subd13_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_32 : subd13_3 [-1, 0, -1] = true := by decide +kernel
theorem subd13_3_33 : subd13_3 [-1, 0, 0] = true := by decide +kernel
theorem subd13_3_34 : subd13_3 [-1, 0, 1] = true := by decide +kernel
theorem subd13_3_35 : subd13_3 [-1, 0, 2] = true := by decide +kernel
theorem subd13_3_36 : subd13_3 [-1, 0, 3] = true := by decide +kernel
theorem subd13_3_37 : subd13_3 [-1, 0, 4] = true := by decide +kernel
theorem subd13_3_38 : subd13_3 [-1, 0, 5] = true := by decide +kernel
theorem subd13_3_39 : subd13_3 [-1, 0, 6] = true := by decide +kernel
theorem subd13_3_40 : subd13_3 [-1, 0, 7] = true := by decide +kernel
theorem subd13_3_41 : subd13_3 [-1, 1] = true := by decide +kernel
theorem subd13_3_42 : subd13_3 [-1, 2] = true := by decide +kernel
theorem subd13_3_43 : subd13_3 [0, -4] = true := by decide +kernel
theorem subd13_3_44 : subd13_3 [0, -3] = true := by decide +kernel
theorem subd13_3_45 : subd13_3 [0, -2] = true := by decide +kernel
theorem subd13_3_46 : subd13_3 [0, -1, -8] = true := by decide +kernel
theorem subd13_3_47 : subd13_3 [0, -1, -7] = true := by decide +kernel
theorem subd13_3_48 : subd13_3 [0, -1, -6] = true := by decide +kernel
theorem subd13_3_49 : subd13_3 [0, -1, -5] = true := by decide +kernel
theorem subd13_3_50 : subd13_3 [0, -1, -4] = true := by decide +kernel
theorem subd13_3_51 : subd13_3 [0, -1, -3] = true := by decide +kernel
theorem subd13_3_52 : subd13_3 [0, -1, -2] = true := by decide +kernel
theorem subd13_3_53 : subd13_3 [0, -1, -1] = true := by decide +kernel
theorem subd13_3_54 : subd13_3 [0, -1, 0] = true := by decide +kernel
theorem subd13_3_55 : subd13_3 [0, -1, 1] = true := by decide +kernel
theorem subd13_3_56 : subd13_3 [0, -1, 2] = true := by decide +kernel
theorem subd13_3_57 : subd13_3 [0, -1, 3] = true := by decide +kernel
theorem subd13_3_58 : subd13_3 [0, -1, 4] = true := by decide +kernel
theorem subd13_3_59 : subd13_3 [0, -1, 5] = true := by decide +kernel
theorem subd13_3_60 : subd13_3 [0, -1, 6] = true := by decide +kernel
theorem subd13_3_61 : subd13_3 [0, -1, 7] = true := by decide +kernel
theorem subd13_3_62 : subd13_3 [0, 0, -9] = true := by decide +kernel
theorem subd13_3_63 : subd13_3 [0, 0, -8] = true := by decide +kernel
theorem sbd13_3_1 : ∀ q ∈ blkd13_3_1, subd13_3 q = true := by
  unfold blkd13_3_1
  exact List.forall_mem_cons.2 ⟨subd13_3_32, List.forall_mem_cons.2 ⟨subd13_3_33, List.forall_mem_cons.2 ⟨subd13_3_34, List.forall_mem_cons.2 ⟨subd13_3_35, List.forall_mem_cons.2 ⟨subd13_3_36, List.forall_mem_cons.2 ⟨subd13_3_37, List.forall_mem_cons.2 ⟨subd13_3_38, List.forall_mem_cons.2 ⟨subd13_3_39, List.forall_mem_cons.2 ⟨subd13_3_40, List.forall_mem_cons.2 ⟨subd13_3_41, List.forall_mem_cons.2 ⟨subd13_3_42, List.forall_mem_cons.2 ⟨subd13_3_43, List.forall_mem_cons.2 ⟨subd13_3_44, List.forall_mem_cons.2 ⟨subd13_3_45, List.forall_mem_cons.2 ⟨subd13_3_46, List.forall_mem_cons.2 ⟨subd13_3_47, List.forall_mem_cons.2 ⟨subd13_3_48, List.forall_mem_cons.2 ⟨subd13_3_49, List.forall_mem_cons.2 ⟨subd13_3_50, List.forall_mem_cons.2 ⟨subd13_3_51, List.forall_mem_cons.2 ⟨subd13_3_52, List.forall_mem_cons.2 ⟨subd13_3_53, List.forall_mem_cons.2 ⟨subd13_3_54, List.forall_mem_cons.2 ⟨subd13_3_55, List.forall_mem_cons.2 ⟨subd13_3_56, List.forall_mem_cons.2 ⟨subd13_3_57, List.forall_mem_cons.2 ⟨subd13_3_58, List.forall_mem_cons.2 ⟨subd13_3_59, List.forall_mem_cons.2 ⟨subd13_3_60, List.forall_mem_cons.2 ⟨subd13_3_61, List.forall_mem_cons.2 ⟨subd13_3_62, List.forall_mem_cons.2 ⟨subd13_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_64 : subd13_3 [0, 0, -7] = true := by decide +kernel
theorem subd13_3_65 : subd13_3 [0, 0, -6] = true := by decide +kernel
theorem subd13_3_66 : subd13_3 [0, 0, -5] = true := by decide +kernel
theorem subd13_3_67 : subd13_3 [0, 0, -4] = true := by decide +kernel
theorem subd13_3_68 : subd13_3 [0, 0, -3] = true := by decide +kernel
theorem subd13_3_69 : subd13_3 [0, 0, -2] = true := by decide +kernel
theorem subd13_3_70 : subd13_3 [0, 0, -1] = true := by decide +kernel
theorem subd13_3_71 : subd13_3 [0, 0, 0] = true := by decide +kernel
theorem subd13_3_72 : subd13_3 [0, 0, 1] = true := by decide +kernel
theorem subd13_3_73 : subd13_3 [0, 0, 2] = true := by decide +kernel
theorem subd13_3_74 : subd13_3 [0, 0, 3] = true := by decide +kernel
theorem subd13_3_75 : subd13_3 [0, 0, 4] = true := by decide +kernel
theorem subd13_3_76 : subd13_3 [0, 0, 5] = true := by decide +kernel
theorem subd13_3_77 : subd13_3 [0, 0, 6] = true := by decide +kernel
theorem subd13_3_78 : subd13_3 [0, 0, 7] = true := by decide +kernel
theorem subd13_3_79 : subd13_3 [0, 0, 8] = true := by decide +kernel
theorem subd13_3_80 : subd13_3 [0, 1, -8] = true := by decide +kernel
theorem subd13_3_81 : subd13_3 [0, 1, -7] = true := by decide +kernel
theorem subd13_3_82 : subd13_3 [0, 1, -6] = true := by decide +kernel
theorem subd13_3_83 : subd13_3 [0, 1, -5] = true := by decide +kernel
theorem subd13_3_84 : subd13_3 [0, 1, -4] = true := by decide +kernel
theorem subd13_3_85 : subd13_3 [0, 1, -3] = true := by decide +kernel
theorem subd13_3_86 : subd13_3 [0, 1, -2] = true := by decide +kernel
theorem subd13_3_87 : subd13_3 [0, 1, -1] = true := by decide +kernel
theorem subd13_3_88 : subd13_3 [0, 1, 0] = true := by decide +kernel
theorem subd13_3_89 : subd13_3 [0, 1, 1] = true := by decide +kernel
theorem subd13_3_90 : subd13_3 [0, 1, 2] = true := by decide +kernel
theorem subd13_3_91 : subd13_3 [0, 1, 3] = true := by decide +kernel
theorem subd13_3_92 : subd13_3 [0, 1, 4] = true := by decide +kernel
theorem subd13_3_93 : subd13_3 [0, 1, 5] = true := by decide +kernel
theorem subd13_3_94 : subd13_3 [0, 1, 6] = true := by decide +kernel
theorem subd13_3_95 : subd13_3 [0, 1, 7] = true := by decide +kernel
theorem sbd13_3_2 : ∀ q ∈ blkd13_3_2, subd13_3 q = true := by
  unfold blkd13_3_2
  exact List.forall_mem_cons.2 ⟨subd13_3_64, List.forall_mem_cons.2 ⟨subd13_3_65, List.forall_mem_cons.2 ⟨subd13_3_66, List.forall_mem_cons.2 ⟨subd13_3_67, List.forall_mem_cons.2 ⟨subd13_3_68, List.forall_mem_cons.2 ⟨subd13_3_69, List.forall_mem_cons.2 ⟨subd13_3_70, List.forall_mem_cons.2 ⟨subd13_3_71, List.forall_mem_cons.2 ⟨subd13_3_72, List.forall_mem_cons.2 ⟨subd13_3_73, List.forall_mem_cons.2 ⟨subd13_3_74, List.forall_mem_cons.2 ⟨subd13_3_75, List.forall_mem_cons.2 ⟨subd13_3_76, List.forall_mem_cons.2 ⟨subd13_3_77, List.forall_mem_cons.2 ⟨subd13_3_78, List.forall_mem_cons.2 ⟨subd13_3_79, List.forall_mem_cons.2 ⟨subd13_3_80, List.forall_mem_cons.2 ⟨subd13_3_81, List.forall_mem_cons.2 ⟨subd13_3_82, List.forall_mem_cons.2 ⟨subd13_3_83, List.forall_mem_cons.2 ⟨subd13_3_84, List.forall_mem_cons.2 ⟨subd13_3_85, List.forall_mem_cons.2 ⟨subd13_3_86, List.forall_mem_cons.2 ⟨subd13_3_87, List.forall_mem_cons.2 ⟨subd13_3_88, List.forall_mem_cons.2 ⟨subd13_3_89, List.forall_mem_cons.2 ⟨subd13_3_90, List.forall_mem_cons.2 ⟨subd13_3_91, List.forall_mem_cons.2 ⟨subd13_3_92, List.forall_mem_cons.2 ⟨subd13_3_93, List.forall_mem_cons.2 ⟨subd13_3_94, List.forall_mem_cons.2 ⟨subd13_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_96 : subd13_3 [0, 2] = true := by decide +kernel
theorem subd13_3_97 : subd13_3 [0, 3] = true := by decide +kernel
theorem subd13_3_98 : subd13_3 [1, -3] = true := by decide +kernel
theorem subd13_3_99 : subd13_3 [1, -2] = true := by decide +kernel
theorem subd13_3_100 : subd13_3 [1, -1] = true := by decide +kernel
theorem subd13_3_101 : subd13_3 [1, 0, -8] = true := by decide +kernel
theorem subd13_3_102 : subd13_3 [1, 0, -7] = true := by decide +kernel
theorem subd13_3_103 : subd13_3 [1, 0, -6] = true := by decide +kernel
theorem subd13_3_104 : subd13_3 [1, 0, -5] = true := by decide +kernel
theorem subd13_3_105 : subd13_3 [1, 0, -4] = true := by decide +kernel
theorem subd13_3_106 : subd13_3 [1, 0, -3] = true := by decide +kernel
theorem subd13_3_107 : subd13_3 [1, 0, -2] = true := by decide +kernel
theorem subd13_3_108 : subd13_3 [1, 0, -1] = true := by decide +kernel
theorem subd13_3_109 : subd13_3 [1, 0, 0] = true := by decide +kernel
theorem subd13_3_110 : subd13_3 [1, 0, 1] = true := by decide +kernel
theorem subd13_3_111 : subd13_3 [1, 0, 2] = true := by decide +kernel
theorem subd13_3_112 : subd13_3 [1, 0, 3] = true := by decide +kernel
theorem subd13_3_113 : subd13_3 [1, 0, 4] = true := by decide +kernel
theorem subd13_3_114 : subd13_3 [1, 0, 5] = true := by decide +kernel
theorem subd13_3_115 : subd13_3 [1, 0, 6] = true := by decide +kernel
theorem subd13_3_116 : subd13_3 [1, 0, 7] = true := by decide +kernel
theorem subd13_3_117 : subd13_3 [1, 1, -8] = true := by decide +kernel
theorem subd13_3_118 : subd13_3 [1, 1, -7] = true := by decide +kernel
theorem subd13_3_119 : subd13_3 [1, 1, -6] = true := by decide +kernel
theorem subd13_3_120 : subd13_3 [1, 1, -5] = true := by decide +kernel
theorem subd13_3_121 : subd13_3 [1, 1, -4] = true := by decide +kernel
theorem subd13_3_122 : subd13_3 [1, 1, -3] = true := by decide +kernel
theorem subd13_3_123 : subd13_3 [1, 1, -2] = true := by decide +kernel
theorem subd13_3_124 : subd13_3 [1, 1, -1] = true := by decide +kernel
theorem subd13_3_125 : subd13_3 [1, 1, 0] = true := by decide +kernel
theorem subd13_3_126 : subd13_3 [1, 1, 1] = true := by decide +kernel
theorem subd13_3_127 : subd13_3 [1, 1, 2] = true := by decide +kernel
theorem sbd13_3_3 : ∀ q ∈ blkd13_3_3, subd13_3 q = true := by
  unfold blkd13_3_3
  exact List.forall_mem_cons.2 ⟨subd13_3_96, List.forall_mem_cons.2 ⟨subd13_3_97, List.forall_mem_cons.2 ⟨subd13_3_98, List.forall_mem_cons.2 ⟨subd13_3_99, List.forall_mem_cons.2 ⟨subd13_3_100, List.forall_mem_cons.2 ⟨subd13_3_101, List.forall_mem_cons.2 ⟨subd13_3_102, List.forall_mem_cons.2 ⟨subd13_3_103, List.forall_mem_cons.2 ⟨subd13_3_104, List.forall_mem_cons.2 ⟨subd13_3_105, List.forall_mem_cons.2 ⟨subd13_3_106, List.forall_mem_cons.2 ⟨subd13_3_107, List.forall_mem_cons.2 ⟨subd13_3_108, List.forall_mem_cons.2 ⟨subd13_3_109, List.forall_mem_cons.2 ⟨subd13_3_110, List.forall_mem_cons.2 ⟨subd13_3_111, List.forall_mem_cons.2 ⟨subd13_3_112, List.forall_mem_cons.2 ⟨subd13_3_113, List.forall_mem_cons.2 ⟨subd13_3_114, List.forall_mem_cons.2 ⟨subd13_3_115, List.forall_mem_cons.2 ⟨subd13_3_116, List.forall_mem_cons.2 ⟨subd13_3_117, List.forall_mem_cons.2 ⟨subd13_3_118, List.forall_mem_cons.2 ⟨subd13_3_119, List.forall_mem_cons.2 ⟨subd13_3_120, List.forall_mem_cons.2 ⟨subd13_3_121, List.forall_mem_cons.2 ⟨subd13_3_122, List.forall_mem_cons.2 ⟨subd13_3_123, List.forall_mem_cons.2 ⟨subd13_3_124, List.forall_mem_cons.2 ⟨subd13_3_125, List.forall_mem_cons.2 ⟨subd13_3_126, List.forall_mem_cons.2 ⟨subd13_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_128 : subd13_3 [1, 1, 3] = true := by decide +kernel
theorem subd13_3_129 : subd13_3 [1, 1, 4] = true := by decide +kernel
theorem subd13_3_130 : subd13_3 [1, 1, 5] = true := by decide +kernel
theorem subd13_3_131 : subd13_3 [1, 1, 6] = true := by decide +kernel
theorem subd13_3_132 : subd13_3 [1, 1, 7] = true := by decide +kernel
theorem subd13_3_133 : subd13_3 [1, 2] = true := by decide +kernel
theorem subd13_3_134 : subd13_3 [1, 3] = true := by decide +kernel
theorem subd13_3_135 : subd13_3 [2, -2] = true := by decide +kernel
theorem subd13_3_136 : subd13_3 [2, -1] = true := by decide +kernel
theorem subd13_3_137 : subd13_3 [2, 0] = true := by decide +kernel
theorem subd13_3_138 : subd13_3 [2, 1] = true := by decide +kernel
theorem subd13_3_139 : subd13_3 [2, 2] = true := by decide +kernel
theorem subd13_3_140 : subd13_3 [2, 3] = true := by decide +kernel
theorem sbd13_3_4 : ∀ q ∈ blkd13_3_4, subd13_3 q = true := by
  unfold blkd13_3_4
  exact List.forall_mem_cons.2 ⟨subd13_3_128, List.forall_mem_cons.2 ⟨subd13_3_129, List.forall_mem_cons.2 ⟨subd13_3_130, List.forall_mem_cons.2 ⟨subd13_3_131, List.forall_mem_cons.2 ⟨subd13_3_132, List.forall_mem_cons.2 ⟨subd13_3_133, List.forall_mem_cons.2 ⟨subd13_3_134, List.forall_mem_cons.2 ⟨subd13_3_135, List.forall_mem_cons.2 ⟨subd13_3_136, List.forall_mem_cons.2 ⟨subd13_3_137, List.forall_mem_cons.2 ⟨subd13_3_138, List.forall_mem_cons.2 ⟨subd13_3_139, List.forall_mem_cons.2 ⟨subd13_3_140, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-1] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [0] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [1] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
