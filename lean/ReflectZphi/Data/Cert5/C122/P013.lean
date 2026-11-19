import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-3] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-2, -3] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-2, -2] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-2, -1] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-2, 0] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-2, 1] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-1, -2] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-1, -1] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-1, 0] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-1, 1] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-1, 2] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [0, -1] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [0, 0] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [0, 1] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [1, -3] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [1, -2] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [1, -1] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [1, 0] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [1, 1] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [1, 2] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [2, -2] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [2, -1] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [2, 0] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [2, 1] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [2, 2] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [3] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-1, -2] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-1, -1, -7] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-1, -1, -6] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-1, -1, -5] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-1, -1, -4] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [-1, -1, -3] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [-1, -1, -2] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [-1, -1, -1] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [-1, -1, 0] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [-1, -1, 1] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [-1, -1, 2] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [-1, -1, 3] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [-1, -1, 4] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [-1, -1, 5] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [-1, -1, 6] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [-1, -1, 7] = true := by decide +kernel
theorem subd7_4_16 : subd7_4 [-1, 0, -11] = true := by decide +kernel
theorem subd7_4_17 : subd7_4 [-1, 0, -10] = true := by decide +kernel
theorem subd7_4_18 : subd7_4 [-1, 0, -9] = true := by decide +kernel
theorem subd7_4_19 : subd7_4 [-1, 0, -8] = true := by decide +kernel
theorem subd7_4_20 : subd7_4 [-1, 0, -7] = true := by decide +kernel
theorem subd7_4_21 : subd7_4 [-1, 0, -6] = true := by decide +kernel
theorem subd7_4_22 : subd7_4 [-1, 0, -5] = true := by decide +kernel
theorem subd7_4_23 : subd7_4 [-1, 0, -4] = true := by decide +kernel
theorem subd7_4_24 : subd7_4 [-1, 0, -3] = true := by decide +kernel
theorem subd7_4_25 : subd7_4 [-1, 0, -2] = true := by decide +kernel
theorem subd7_4_26 : subd7_4 [-1, 0, -1] = true := by decide +kernel
theorem subd7_4_27 : subd7_4 [-1, 0, 0] = true := by decide +kernel
theorem subd7_4_28 : subd7_4 [-1, 0, 1] = true := by decide +kernel
theorem subd7_4_29 : subd7_4 [-1, 0, 2] = true := by decide +kernel
theorem subd7_4_30 : subd7_4 [-1, 0, 3] = true := by decide +kernel
theorem subd7_4_31 : subd7_4 [-1, 0, 4] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_cons.2 ⟨subd7_4_16, List.forall_mem_cons.2 ⟨subd7_4_17, List.forall_mem_cons.2 ⟨subd7_4_18, List.forall_mem_cons.2 ⟨subd7_4_19, List.forall_mem_cons.2 ⟨subd7_4_20, List.forall_mem_cons.2 ⟨subd7_4_21, List.forall_mem_cons.2 ⟨subd7_4_22, List.forall_mem_cons.2 ⟨subd7_4_23, List.forall_mem_cons.2 ⟨subd7_4_24, List.forall_mem_cons.2 ⟨subd7_4_25, List.forall_mem_cons.2 ⟨subd7_4_26, List.forall_mem_cons.2 ⟨subd7_4_27, List.forall_mem_cons.2 ⟨subd7_4_28, List.forall_mem_cons.2 ⟨subd7_4_29, List.forall_mem_cons.2 ⟨subd7_4_30, List.forall_mem_cons.2 ⟨subd7_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_32 : subd7_4 [-1, 0, 5] = true := by decide +kernel
theorem subd7_4_33 : subd7_4 [-1, 0, 6] = true := by decide +kernel
theorem subd7_4_34 : subd7_4 [-1, 0, 7] = true := by decide +kernel
theorem subd7_4_35 : subd7_4 [-1, 0, 8] = true := by decide +kernel
theorem subd7_4_36 : subd7_4 [-1, 0, 9] = true := by decide +kernel
theorem subd7_4_37 : subd7_4 [-1, 0, 10] = true := by decide +kernel
theorem subd7_4_38 : subd7_4 [-1, 1, -10] = true := by decide +kernel
theorem subd7_4_39 : subd7_4 [-1, 1, -9] = true := by decide +kernel
theorem subd7_4_40 : subd7_4 [-1, 1, -8] = true := by decide +kernel
theorem subd7_4_41 : subd7_4 [-1, 1, -7] = true := by decide +kernel
theorem subd7_4_42 : subd7_4 [-1, 1, -6] = true := by decide +kernel
theorem subd7_4_43 : subd7_4 [-1, 1, -5] = true := by decide +kernel
theorem subd7_4_44 : subd7_4 [-1, 1, -4] = true := by decide +kernel
theorem subd7_4_45 : subd7_4 [-1, 1, -3] = true := by decide +kernel
theorem subd7_4_46 : subd7_4 [-1, 1, -2] = true := by decide +kernel
theorem subd7_4_47 : subd7_4 [-1, 1, -1] = true := by decide +kernel
theorem subd7_4_48 : subd7_4 [-1, 1, 0] = true := by decide +kernel
theorem subd7_4_49 : subd7_4 [-1, 1, 1] = true := by decide +kernel
theorem subd7_4_50 : subd7_4 [-1, 1, 2] = true := by decide +kernel
theorem subd7_4_51 : subd7_4 [-1, 1, 3] = true := by decide +kernel
theorem subd7_4_52 : subd7_4 [-1, 1, 4] = true := by decide +kernel
theorem subd7_4_53 : subd7_4 [-1, 1, 5] = true := by decide +kernel
theorem subd7_4_54 : subd7_4 [-1, 1, 6] = true := by decide +kernel
theorem subd7_4_55 : subd7_4 [-1, 1, 7] = true := by decide +kernel
theorem subd7_4_56 : subd7_4 [-1, 1, 8] = true := by decide +kernel
theorem subd7_4_57 : subd7_4 [-1, 1, 9] = true := by decide +kernel
theorem subd7_4_58 : subd7_4 [-1, 1, 10] = true := by decide +kernel
theorem subd7_4_59 : subd7_4 [-1, 2] = true := by decide +kernel
theorem subd7_4_60 : subd7_4 [0, -3] = true := by decide +kernel
theorem subd7_4_61 : subd7_4 [0, -2] = true := by decide +kernel
theorem subd7_4_62 : subd7_4 [0, -1, -12] = true := by decide +kernel
theorem subd7_4_63 : subd7_4 [0, -1, -11] = true := by decide +kernel
theorem sbd7_4_1 : ∀ q ∈ blkd7_4_1, subd7_4 q = true := by
  unfold blkd7_4_1
  exact List.forall_mem_cons.2 ⟨subd7_4_32, List.forall_mem_cons.2 ⟨subd7_4_33, List.forall_mem_cons.2 ⟨subd7_4_34, List.forall_mem_cons.2 ⟨subd7_4_35, List.forall_mem_cons.2 ⟨subd7_4_36, List.forall_mem_cons.2 ⟨subd7_4_37, List.forall_mem_cons.2 ⟨subd7_4_38, List.forall_mem_cons.2 ⟨subd7_4_39, List.forall_mem_cons.2 ⟨subd7_4_40, List.forall_mem_cons.2 ⟨subd7_4_41, List.forall_mem_cons.2 ⟨subd7_4_42, List.forall_mem_cons.2 ⟨subd7_4_43, List.forall_mem_cons.2 ⟨subd7_4_44, List.forall_mem_cons.2 ⟨subd7_4_45, List.forall_mem_cons.2 ⟨subd7_4_46, List.forall_mem_cons.2 ⟨subd7_4_47, List.forall_mem_cons.2 ⟨subd7_4_48, List.forall_mem_cons.2 ⟨subd7_4_49, List.forall_mem_cons.2 ⟨subd7_4_50, List.forall_mem_cons.2 ⟨subd7_4_51, List.forall_mem_cons.2 ⟨subd7_4_52, List.forall_mem_cons.2 ⟨subd7_4_53, List.forall_mem_cons.2 ⟨subd7_4_54, List.forall_mem_cons.2 ⟨subd7_4_55, List.forall_mem_cons.2 ⟨subd7_4_56, List.forall_mem_cons.2 ⟨subd7_4_57, List.forall_mem_cons.2 ⟨subd7_4_58, List.forall_mem_cons.2 ⟨subd7_4_59, List.forall_mem_cons.2 ⟨subd7_4_60, List.forall_mem_cons.2 ⟨subd7_4_61, List.forall_mem_cons.2 ⟨subd7_4_62, List.forall_mem_cons.2 ⟨subd7_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_64 : subd7_4 [0, -1, -10] = true := by decide +kernel
theorem subd7_4_65 : subd7_4 [0, -1, -9] = true := by decide +kernel
theorem subd7_4_66 : subd7_4 [0, -1, -8] = true := by decide +kernel
theorem subd7_4_67 : subd7_4 [0, -1, -7] = true := by decide +kernel
theorem subd7_4_68 : subd7_4 [0, -1, -6] = true := by decide +kernel
theorem subd7_4_69 : subd7_4 [0, -1, -5] = true := by decide +kernel
theorem subd7_4_70 : subd7_4 [0, -1, -4] = true := by decide +kernel
theorem subd7_4_71 : subd7_4 [0, -1, -3] = true := by decide +kernel
theorem subd7_4_72 : subd7_4 [0, -1, -2] = true := by decide +kernel
theorem subd7_4_73 : subd7_4 [0, -1, -1] = true := by decide +kernel
theorem subd7_4_74 : subd7_4 [0, -1, 0] = true := by decide +kernel
theorem subd7_4_75 : subd7_4 [0, -1, 1] = true := by decide +kernel
theorem subd7_4_76 : subd7_4 [0, -1, 2] = true := by decide +kernel
theorem subd7_4_77 : subd7_4 [0, -1, 3] = true := by decide +kernel
theorem subd7_4_78 : subd7_4 [0, -1, 4] = true := by decide +kernel
theorem subd7_4_79 : subd7_4 [0, -1, 5] = true := by decide +kernel
theorem subd7_4_80 : subd7_4 [0, -1, 6] = true := by decide +kernel
theorem subd7_4_81 : subd7_4 [0, -1, 7] = true := by decide +kernel
theorem subd7_4_82 : subd7_4 [0, -1, 8] = true := by decide +kernel
theorem subd7_4_83 : subd7_4 [0, -1, 9] = true := by decide +kernel
theorem subd7_4_84 : subd7_4 [0, -1, 10] = true := by decide +kernel
theorem subd7_4_85 : subd7_4 [0, 0, -13] = true := by decide +kernel
theorem subd7_4_86 : subd7_4 [0, 0, -12] = true := by decide +kernel
theorem subd7_4_87 : subd7_4 [0, 0, -11] = true := by decide +kernel
theorem subd7_4_88 : subd7_4 [0, 0, -10] = true := by decide +kernel
theorem subd7_4_89 : subd7_4 [0, 0, -9] = true := by decide +kernel
theorem subd7_4_90 : subd7_4 [0, 0, -8] = true := by decide +kernel
theorem subd7_4_91 : subd7_4 [0, 0, -7] = true := by decide +kernel
theorem subd7_4_92 : subd7_4 [0, 0, -6] = true := by decide +kernel
theorem subd7_4_93 : subd7_4 [0, 0, -5] = true := by decide +kernel
theorem subd7_4_94 : subd7_4 [0, 0, -4] = true := by decide +kernel
theorem subd7_4_95 : subd7_4 [0, 0, -3] = true := by decide +kernel
theorem sbd7_4_2 : ∀ q ∈ blkd7_4_2, subd7_4 q = true := by
  unfold blkd7_4_2
  exact List.forall_mem_cons.2 ⟨subd7_4_64, List.forall_mem_cons.2 ⟨subd7_4_65, List.forall_mem_cons.2 ⟨subd7_4_66, List.forall_mem_cons.2 ⟨subd7_4_67, List.forall_mem_cons.2 ⟨subd7_4_68, List.forall_mem_cons.2 ⟨subd7_4_69, List.forall_mem_cons.2 ⟨subd7_4_70, List.forall_mem_cons.2 ⟨subd7_4_71, List.forall_mem_cons.2 ⟨subd7_4_72, List.forall_mem_cons.2 ⟨subd7_4_73, List.forall_mem_cons.2 ⟨subd7_4_74, List.forall_mem_cons.2 ⟨subd7_4_75, List.forall_mem_cons.2 ⟨subd7_4_76, List.forall_mem_cons.2 ⟨subd7_4_77, List.forall_mem_cons.2 ⟨subd7_4_78, List.forall_mem_cons.2 ⟨subd7_4_79, List.forall_mem_cons.2 ⟨subd7_4_80, List.forall_mem_cons.2 ⟨subd7_4_81, List.forall_mem_cons.2 ⟨subd7_4_82, List.forall_mem_cons.2 ⟨subd7_4_83, List.forall_mem_cons.2 ⟨subd7_4_84, List.forall_mem_cons.2 ⟨subd7_4_85, List.forall_mem_cons.2 ⟨subd7_4_86, List.forall_mem_cons.2 ⟨subd7_4_87, List.forall_mem_cons.2 ⟨subd7_4_88, List.forall_mem_cons.2 ⟨subd7_4_89, List.forall_mem_cons.2 ⟨subd7_4_90, List.forall_mem_cons.2 ⟨subd7_4_91, List.forall_mem_cons.2 ⟨subd7_4_92, List.forall_mem_cons.2 ⟨subd7_4_93, List.forall_mem_cons.2 ⟨subd7_4_94, List.forall_mem_cons.2 ⟨subd7_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_96 : subd7_4 [0, 0, -2] = true := by decide +kernel
theorem subd7_4_97 : subd7_4 [0, 0, -1] = true := by decide +kernel
theorem subd7_4_98 : subd7_4 [0, 0, 0] = true := by decide +kernel
theorem subd7_4_99 : subd7_4 [0, 0, 1] = true := by decide +kernel
theorem subd7_4_100 : subd7_4 [0, 0, 2] = true := by decide +kernel
theorem subd7_4_101 : subd7_4 [0, 0, 3] = true := by decide +kernel
theorem subd7_4_102 : subd7_4 [0, 0, 4] = true := by decide +kernel
theorem subd7_4_103 : subd7_4 [0, 0, 5] = true := by decide +kernel
theorem subd7_4_104 : subd7_4 [0, 0, 6] = true := by decide +kernel
theorem subd7_4_105 : subd7_4 [0, 0, 7] = true := by decide +kernel
theorem subd7_4_106 : subd7_4 [0, 0, 8] = true := by decide +kernel
theorem subd7_4_107 : subd7_4 [0, 0, 9] = true := by decide +kernel
theorem subd7_4_108 : subd7_4 [0, 0, 10] = true := by decide +kernel
theorem subd7_4_109 : subd7_4 [0, 0, 11] = true := by decide +kernel
theorem subd7_4_110 : subd7_4 [0, 0, 12] = true := by decide +kernel
theorem subd7_4_111 : subd7_4 [0, 1, -11] = true := by decide +kernel
theorem subd7_4_112 : subd7_4 [0, 1, -10] = true := by decide +kernel
theorem subd7_4_113 : subd7_4 [0, 1, -9] = true := by decide +kernel
theorem subd7_4_114 : subd7_4 [0, 1, -8] = true := by decide +kernel
theorem subd7_4_115 : subd7_4 [0, 1, -7] = true := by decide +kernel
theorem subd7_4_116 : subd7_4 [0, 1, -6] = true := by decide +kernel
theorem subd7_4_117 : subd7_4 [0, 1, -5] = true := by decide +kernel
theorem subd7_4_118 : subd7_4 [0, 1, -4] = true := by decide +kernel
theorem subd7_4_119 : subd7_4 [0, 1, -3] = true := by decide +kernel
theorem subd7_4_120 : subd7_4 [0, 1, -2] = true := by decide +kernel
theorem subd7_4_121 : subd7_4 [0, 1, -1] = true := by decide +kernel
theorem subd7_4_122 : subd7_4 [0, 1, 0] = true := by decide +kernel
theorem subd7_4_123 : subd7_4 [0, 1, 1] = true := by decide +kernel
theorem subd7_4_124 : subd7_4 [0, 1, 2] = true := by decide +kernel
theorem subd7_4_125 : subd7_4 [0, 1, 3] = true := by decide +kernel
theorem subd7_4_126 : subd7_4 [0, 1, 4] = true := by decide +kernel
theorem subd7_4_127 : subd7_4 [0, 1, 5] = true := by decide +kernel
theorem sbd7_4_3 : ∀ q ∈ blkd7_4_3, subd7_4 q = true := by
  unfold blkd7_4_3
  exact List.forall_mem_cons.2 ⟨subd7_4_96, List.forall_mem_cons.2 ⟨subd7_4_97, List.forall_mem_cons.2 ⟨subd7_4_98, List.forall_mem_cons.2 ⟨subd7_4_99, List.forall_mem_cons.2 ⟨subd7_4_100, List.forall_mem_cons.2 ⟨subd7_4_101, List.forall_mem_cons.2 ⟨subd7_4_102, List.forall_mem_cons.2 ⟨subd7_4_103, List.forall_mem_cons.2 ⟨subd7_4_104, List.forall_mem_cons.2 ⟨subd7_4_105, List.forall_mem_cons.2 ⟨subd7_4_106, List.forall_mem_cons.2 ⟨subd7_4_107, List.forall_mem_cons.2 ⟨subd7_4_108, List.forall_mem_cons.2 ⟨subd7_4_109, List.forall_mem_cons.2 ⟨subd7_4_110, List.forall_mem_cons.2 ⟨subd7_4_111, List.forall_mem_cons.2 ⟨subd7_4_112, List.forall_mem_cons.2 ⟨subd7_4_113, List.forall_mem_cons.2 ⟨subd7_4_114, List.forall_mem_cons.2 ⟨subd7_4_115, List.forall_mem_cons.2 ⟨subd7_4_116, List.forall_mem_cons.2 ⟨subd7_4_117, List.forall_mem_cons.2 ⟨subd7_4_118, List.forall_mem_cons.2 ⟨subd7_4_119, List.forall_mem_cons.2 ⟨subd7_4_120, List.forall_mem_cons.2 ⟨subd7_4_121, List.forall_mem_cons.2 ⟨subd7_4_122, List.forall_mem_cons.2 ⟨subd7_4_123, List.forall_mem_cons.2 ⟨subd7_4_124, List.forall_mem_cons.2 ⟨subd7_4_125, List.forall_mem_cons.2 ⟨subd7_4_126, List.forall_mem_cons.2 ⟨subd7_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_128 : subd7_4 [0, 1, 6] = true := by decide +kernel
theorem subd7_4_129 : subd7_4 [0, 1, 7] = true := by decide +kernel
theorem subd7_4_130 : subd7_4 [0, 1, 8] = true := by decide +kernel
theorem subd7_4_131 : subd7_4 [0, 1, 9] = true := by decide +kernel
theorem subd7_4_132 : subd7_4 [0, 1, 10] = true := by decide +kernel
theorem subd7_4_133 : subd7_4 [0, 1, 11] = true := by decide +kernel
theorem subd7_4_134 : subd7_4 [0, 2] = true := by decide +kernel
theorem subd7_4_135 : subd7_4 [1, -3] = true := by decide +kernel
theorem subd7_4_136 : subd7_4 [1, -2] = true := by decide +kernel
theorem subd7_4_137 : subd7_4 [1, -1, -11] = true := by decide +kernel
theorem subd7_4_138 : subd7_4 [1, -1, -10] = true := by decide +kernel
theorem subd7_4_139 : subd7_4 [1, -1, -9] = true := by decide +kernel
theorem subd7_4_140 : subd7_4 [1, -1, -8] = true := by decide +kernel
theorem subd7_4_141 : subd7_4 [1, -1, -7] = true := by decide +kernel
theorem subd7_4_142 : subd7_4 [1, -1, -6] = true := by decide +kernel
theorem subd7_4_143 : subd7_4 [1, -1, -5] = true := by decide +kernel
theorem subd7_4_144 : subd7_4 [1, -1, -4] = true := by decide +kernel
theorem subd7_4_145 : subd7_4 [1, -1, -3] = true := by decide +kernel
theorem subd7_4_146 : subd7_4 [1, -1, -2] = true := by decide +kernel
theorem subd7_4_147 : subd7_4 [1, -1, -1] = true := by decide +kernel
theorem subd7_4_148 : subd7_4 [1, -1, 0] = true := by decide +kernel
theorem subd7_4_149 : subd7_4 [1, -1, 1] = true := by decide +kernel
theorem subd7_4_150 : subd7_4 [1, -1, 2] = true := by decide +kernel
theorem subd7_4_151 : subd7_4 [1, -1, 3] = true := by decide +kernel
theorem subd7_4_152 : subd7_4 [1, -1, 4] = true := by decide +kernel
theorem subd7_4_153 : subd7_4 [1, -1, 5] = true := by decide +kernel
theorem subd7_4_154 : subd7_4 [1, -1, 6] = true := by decide +kernel
theorem subd7_4_155 : subd7_4 [1, -1, 7] = true := by decide +kernel
theorem subd7_4_156 : subd7_4 [1, -1, 8] = true := by decide +kernel
theorem subd7_4_157 : subd7_4 [1, -1, 9] = true := by decide +kernel
theorem subd7_4_158 : subd7_4 [1, 0, -11] = true := by decide +kernel
theorem subd7_4_159 : subd7_4 [1, 0, -10] = true := by decide +kernel
theorem sbd7_4_4 : ∀ q ∈ blkd7_4_4, subd7_4 q = true := by
  unfold blkd7_4_4
  exact List.forall_mem_cons.2 ⟨subd7_4_128, List.forall_mem_cons.2 ⟨subd7_4_129, List.forall_mem_cons.2 ⟨subd7_4_130, List.forall_mem_cons.2 ⟨subd7_4_131, List.forall_mem_cons.2 ⟨subd7_4_132, List.forall_mem_cons.2 ⟨subd7_4_133, List.forall_mem_cons.2 ⟨subd7_4_134, List.forall_mem_cons.2 ⟨subd7_4_135, List.forall_mem_cons.2 ⟨subd7_4_136, List.forall_mem_cons.2 ⟨subd7_4_137, List.forall_mem_cons.2 ⟨subd7_4_138, List.forall_mem_cons.2 ⟨subd7_4_139, List.forall_mem_cons.2 ⟨subd7_4_140, List.forall_mem_cons.2 ⟨subd7_4_141, List.forall_mem_cons.2 ⟨subd7_4_142, List.forall_mem_cons.2 ⟨subd7_4_143, List.forall_mem_cons.2 ⟨subd7_4_144, List.forall_mem_cons.2 ⟨subd7_4_145, List.forall_mem_cons.2 ⟨subd7_4_146, List.forall_mem_cons.2 ⟨subd7_4_147, List.forall_mem_cons.2 ⟨subd7_4_148, List.forall_mem_cons.2 ⟨subd7_4_149, List.forall_mem_cons.2 ⟨subd7_4_150, List.forall_mem_cons.2 ⟨subd7_4_151, List.forall_mem_cons.2 ⟨subd7_4_152, List.forall_mem_cons.2 ⟨subd7_4_153, List.forall_mem_cons.2 ⟨subd7_4_154, List.forall_mem_cons.2 ⟨subd7_4_155, List.forall_mem_cons.2 ⟨subd7_4_156, List.forall_mem_cons.2 ⟨subd7_4_157, List.forall_mem_cons.2 ⟨subd7_4_158, List.forall_mem_cons.2 ⟨subd7_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_160 : subd7_4 [1, 0, -9] = true := by decide +kernel
theorem subd7_4_161 : subd7_4 [1, 0, -8] = true := by decide +kernel
theorem subd7_4_162 : subd7_4 [1, 0, -7] = true := by decide +kernel
theorem subd7_4_163 : subd7_4 [1, 0, -6] = true := by decide +kernel
theorem subd7_4_164 : subd7_4 [1, 0, -5] = true := by decide +kernel
theorem subd7_4_165 : subd7_4 [1, 0, -4] = true := by decide +kernel
theorem subd7_4_166 : subd7_4 [1, 0, -3] = true := by decide +kernel
theorem subd7_4_167 : subd7_4 [1, 0, -2] = true := by decide +kernel
theorem subd7_4_168 : subd7_4 [1, 0, -1] = true := by decide +kernel
theorem subd7_4_169 : subd7_4 [1, 0, 0] = true := by decide +kernel
theorem subd7_4_170 : subd7_4 [1, 0, 1] = true := by decide +kernel
theorem subd7_4_171 : subd7_4 [1, 0, 2] = true := by decide +kernel
theorem subd7_4_172 : subd7_4 [1, 0, 3] = true := by decide +kernel
theorem subd7_4_173 : subd7_4 [1, 0, 4] = true := by decide +kernel
theorem subd7_4_174 : subd7_4 [1, 0, 5] = true := by decide +kernel
theorem subd7_4_175 : subd7_4 [1, 0, 6] = true := by decide +kernel
theorem subd7_4_176 : subd7_4 [1, 0, 7] = true := by decide +kernel
theorem subd7_4_177 : subd7_4 [1, 0, 8] = true := by decide +kernel
theorem subd7_4_178 : subd7_4 [1, 0, 9] = true := by decide +kernel
theorem subd7_4_179 : subd7_4 [1, 0, 10] = true := by decide +kernel
theorem subd7_4_180 : subd7_4 [1, 1, -8] = true := by decide +kernel
theorem subd7_4_181 : subd7_4 [1, 1, -7] = true := by decide +kernel
theorem subd7_4_182 : subd7_4 [1, 1, -6] = true := by decide +kernel
theorem subd7_4_183 : subd7_4 [1, 1, -5] = true := by decide +kernel
theorem subd7_4_184 : subd7_4 [1, 1, -4] = true := by decide +kernel
theorem subd7_4_185 : subd7_4 [1, 1, -3] = true := by decide +kernel
theorem subd7_4_186 : subd7_4 [1, 1, -2] = true := by decide +kernel
theorem subd7_4_187 : subd7_4 [1, 1, -1] = true := by decide +kernel
theorem subd7_4_188 : subd7_4 [1, 1, 0] = true := by decide +kernel
theorem subd7_4_189 : subd7_4 [1, 1, 1] = true := by decide +kernel
theorem subd7_4_190 : subd7_4 [1, 1, 2] = true := by decide +kernel
theorem subd7_4_191 : subd7_4 [1, 1, 3] = true := by decide +kernel
theorem sbd7_4_5 : ∀ q ∈ blkd7_4_5, subd7_4 q = true := by
  unfold blkd7_4_5
  exact List.forall_mem_cons.2 ⟨subd7_4_160, List.forall_mem_cons.2 ⟨subd7_4_161, List.forall_mem_cons.2 ⟨subd7_4_162, List.forall_mem_cons.2 ⟨subd7_4_163, List.forall_mem_cons.2 ⟨subd7_4_164, List.forall_mem_cons.2 ⟨subd7_4_165, List.forall_mem_cons.2 ⟨subd7_4_166, List.forall_mem_cons.2 ⟨subd7_4_167, List.forall_mem_cons.2 ⟨subd7_4_168, List.forall_mem_cons.2 ⟨subd7_4_169, List.forall_mem_cons.2 ⟨subd7_4_170, List.forall_mem_cons.2 ⟨subd7_4_171, List.forall_mem_cons.2 ⟨subd7_4_172, List.forall_mem_cons.2 ⟨subd7_4_173, List.forall_mem_cons.2 ⟨subd7_4_174, List.forall_mem_cons.2 ⟨subd7_4_175, List.forall_mem_cons.2 ⟨subd7_4_176, List.forall_mem_cons.2 ⟨subd7_4_177, List.forall_mem_cons.2 ⟨subd7_4_178, List.forall_mem_cons.2 ⟨subd7_4_179, List.forall_mem_cons.2 ⟨subd7_4_180, List.forall_mem_cons.2 ⟨subd7_4_181, List.forall_mem_cons.2 ⟨subd7_4_182, List.forall_mem_cons.2 ⟨subd7_4_183, List.forall_mem_cons.2 ⟨subd7_4_184, List.forall_mem_cons.2 ⟨subd7_4_185, List.forall_mem_cons.2 ⟨subd7_4_186, List.forall_mem_cons.2 ⟨subd7_4_187, List.forall_mem_cons.2 ⟨subd7_4_188, List.forall_mem_cons.2 ⟨subd7_4_189, List.forall_mem_cons.2 ⟨subd7_4_190, List.forall_mem_cons.2 ⟨subd7_4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_192 : subd7_4 [1, 1, 4] = true := by decide +kernel
theorem subd7_4_193 : subd7_4 [1, 1, 5] = true := by decide +kernel
theorem subd7_4_194 : subd7_4 [1, 1, 6] = true := by decide +kernel
theorem sbd7_4_6 : ∀ q ∈ blkd7_4_6, subd7_4 q = true := by
  unfold blkd7_4_6
  exact List.forall_mem_cons.2 ⟨subd7_4_192, List.forall_mem_cons.2 ⟨subd7_4_193, List.forall_mem_cons.2 ⟨subd7_4_194, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
