import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_0 : subd6_0 [-2, -3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-2, -2] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-2, -1] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-2, 0] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-2, 1] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-1, -4] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [1, 3] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [2, -2] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [2, -1] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [2, 0] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [2, 1] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [2, 2] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-9] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-8, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-8, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-8, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-8, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-8, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-8, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-8, 3] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-8, 4] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-8, 5] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-8, 6] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-8, 7] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [-7, -5] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [-7, -4] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [-7, -3] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [-7, -2] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [-7, -1] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [-7, 0] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [-7, 1] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [-7, 2] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [-7, 3] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [-7, 4] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [-7, 5] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [-7, 6] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [-7, 7] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [-7, 8] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [-6, -6] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [-6, -5] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [-6, -4] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [-6, -3] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [-6, -2, -5] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [-6, -2, -4] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [-6, -2, -3] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [-6, -2, -2] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [-6, -2, -1] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [-6, -2, 0] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [-6, -2, 1] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [-6, -2, 2] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [-6, -2, 3] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [-6, -2, 4] = true := by decide +kernel
theorem subd6_1_40 : subd6_1 [-6, -2, 5] = true := by decide +kernel
theorem subd6_1_41 : subd6_1 [-6, -2, 6] = true := by decide +kernel
theorem subd6_1_42 : subd6_1 [-6, -2, 7] = true := by decide +kernel
theorem subd6_1_43 : subd6_1 [-6, -2, 8] = true := by decide +kernel
theorem subd6_1_44 : subd6_1 [-6, -2, 9] = true := by decide +kernel
theorem subd6_1_45 : subd6_1 [-6, -1, -5] = true := by decide +kernel
theorem subd6_1_46 : subd6_1 [-6, -1, -4] = true := by decide +kernel
theorem subd6_1_47 : subd6_1 [-6, -1, -3] = true := by decide +kernel
theorem subd6_1_48 : subd6_1 [-6, -1, -2] = true := by decide +kernel
theorem subd6_1_49 : subd6_1 [-6, -1, -1] = true := by decide +kernel
theorem subd6_1_50 : subd6_1 [-6, -1, 0] = true := by decide +kernel
theorem subd6_1_51 : subd6_1 [-6, -1, 1] = true := by decide +kernel
theorem subd6_1_52 : subd6_1 [-6, -1, 2] = true := by decide +kernel
theorem subd6_1_53 : subd6_1 [-6, -1, 3] = true := by decide +kernel
theorem subd6_1_54 : subd6_1 [-6, -1, 4] = true := by decide +kernel
theorem subd6_1_55 : subd6_1 [-6, -1, 5] = true := by decide +kernel
theorem subd6_1_56 : subd6_1 [-6, -1, 6] = true := by decide +kernel
theorem subd6_1_57 : subd6_1 [-6, -1, 7] = true := by decide +kernel
theorem subd6_1_58 : subd6_1 [-6, -1, 8] = true := by decide +kernel
theorem subd6_1_59 : subd6_1 [-6, -1, 9] = true := by decide +kernel
theorem subd6_1_60 : subd6_1 [-6, 0, -6] = true := by decide +kernel
theorem subd6_1_61 : subd6_1 [-6, 0, -5] = true := by decide +kernel
theorem subd6_1_62 : subd6_1 [-6, 0, -4] = true := by decide +kernel
theorem subd6_1_63 : subd6_1 [-6, 0, -3] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_cons.2 ⟨subd6_1_40, List.forall_mem_cons.2 ⟨subd6_1_41, List.forall_mem_cons.2 ⟨subd6_1_42, List.forall_mem_cons.2 ⟨subd6_1_43, List.forall_mem_cons.2 ⟨subd6_1_44, List.forall_mem_cons.2 ⟨subd6_1_45, List.forall_mem_cons.2 ⟨subd6_1_46, List.forall_mem_cons.2 ⟨subd6_1_47, List.forall_mem_cons.2 ⟨subd6_1_48, List.forall_mem_cons.2 ⟨subd6_1_49, List.forall_mem_cons.2 ⟨subd6_1_50, List.forall_mem_cons.2 ⟨subd6_1_51, List.forall_mem_cons.2 ⟨subd6_1_52, List.forall_mem_cons.2 ⟨subd6_1_53, List.forall_mem_cons.2 ⟨subd6_1_54, List.forall_mem_cons.2 ⟨subd6_1_55, List.forall_mem_cons.2 ⟨subd6_1_56, List.forall_mem_cons.2 ⟨subd6_1_57, List.forall_mem_cons.2 ⟨subd6_1_58, List.forall_mem_cons.2 ⟨subd6_1_59, List.forall_mem_cons.2 ⟨subd6_1_60, List.forall_mem_cons.2 ⟨subd6_1_61, List.forall_mem_cons.2 ⟨subd6_1_62, List.forall_mem_cons.2 ⟨subd6_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_64 : subd6_1 [-6, 0, -2] = true := by decide +kernel
theorem subd6_1_65 : subd6_1 [-6, 0, -1] = true := by decide +kernel
theorem subd6_1_66 : subd6_1 [-6, 0, 0] = true := by decide +kernel
theorem subd6_1_67 : subd6_1 [-6, 0, 1] = true := by decide +kernel
theorem subd6_1_68 : subd6_1 [-6, 0, 2] = true := by decide +kernel
theorem subd6_1_69 : subd6_1 [-6, 0, 3] = true := by decide +kernel
theorem subd6_1_70 : subd6_1 [-6, 0, 4] = true := by decide +kernel
theorem subd6_1_71 : subd6_1 [-6, 0, 5] = true := by decide +kernel
theorem subd6_1_72 : subd6_1 [-6, 0, 6] = true := by decide +kernel
theorem subd6_1_73 : subd6_1 [-6, 0, 7] = true := by decide +kernel
theorem subd6_1_74 : subd6_1 [-6, 0, 8] = true := by decide +kernel
theorem subd6_1_75 : subd6_1 [-6, 0, 9] = true := by decide +kernel
theorem subd6_1_76 : subd6_1 [-6, 1, -6] = true := by decide +kernel
theorem subd6_1_77 : subd6_1 [-6, 1, -5] = true := by decide +kernel
theorem subd6_1_78 : subd6_1 [-6, 1, -4] = true := by decide +kernel
theorem subd6_1_79 : subd6_1 [-6, 1, -3] = true := by decide +kernel
theorem subd6_1_80 : subd6_1 [-6, 1, -2] = true := by decide +kernel
theorem subd6_1_81 : subd6_1 [-6, 1, -1] = true := by decide +kernel
theorem subd6_1_82 : subd6_1 [-6, 1, 0] = true := by decide +kernel
theorem subd6_1_83 : subd6_1 [-6, 1, 1] = true := by decide +kernel
theorem subd6_1_84 : subd6_1 [-6, 1, 2] = true := by decide +kernel
theorem subd6_1_85 : subd6_1 [-6, 1, 3] = true := by decide +kernel
theorem subd6_1_86 : subd6_1 [-6, 1, 4] = true := by decide +kernel
theorem subd6_1_87 : subd6_1 [-6, 1, 5] = true := by decide +kernel
theorem subd6_1_88 : subd6_1 [-6, 1, 6] = true := by decide +kernel
theorem subd6_1_89 : subd6_1 [-6, 1, 7] = true := by decide +kernel
theorem subd6_1_90 : subd6_1 [-6, 1, 8] = true := by decide +kernel
theorem subd6_1_91 : subd6_1 [-6, 1, 9] = true := by decide +kernel
theorem subd6_1_92 : subd6_1 [-6, 2, -6] = true := by decide +kernel
theorem subd6_1_93 : subd6_1 [-6, 2, -5] = true := by decide +kernel
theorem subd6_1_94 : subd6_1 [-6, 2, -4] = true := by decide +kernel
theorem subd6_1_95 : subd6_1 [-6, 2, -3] = true := by decide +kernel
theorem sbd6_1_2 : ∀ q ∈ blkd6_1_2, subd6_1 q = true := by
  unfold blkd6_1_2
  exact List.forall_mem_cons.2 ⟨subd6_1_64, List.forall_mem_cons.2 ⟨subd6_1_65, List.forall_mem_cons.2 ⟨subd6_1_66, List.forall_mem_cons.2 ⟨subd6_1_67, List.forall_mem_cons.2 ⟨subd6_1_68, List.forall_mem_cons.2 ⟨subd6_1_69, List.forall_mem_cons.2 ⟨subd6_1_70, List.forall_mem_cons.2 ⟨subd6_1_71, List.forall_mem_cons.2 ⟨subd6_1_72, List.forall_mem_cons.2 ⟨subd6_1_73, List.forall_mem_cons.2 ⟨subd6_1_74, List.forall_mem_cons.2 ⟨subd6_1_75, List.forall_mem_cons.2 ⟨subd6_1_76, List.forall_mem_cons.2 ⟨subd6_1_77, List.forall_mem_cons.2 ⟨subd6_1_78, List.forall_mem_cons.2 ⟨subd6_1_79, List.forall_mem_cons.2 ⟨subd6_1_80, List.forall_mem_cons.2 ⟨subd6_1_81, List.forall_mem_cons.2 ⟨subd6_1_82, List.forall_mem_cons.2 ⟨subd6_1_83, List.forall_mem_cons.2 ⟨subd6_1_84, List.forall_mem_cons.2 ⟨subd6_1_85, List.forall_mem_cons.2 ⟨subd6_1_86, List.forall_mem_cons.2 ⟨subd6_1_87, List.forall_mem_cons.2 ⟨subd6_1_88, List.forall_mem_cons.2 ⟨subd6_1_89, List.forall_mem_cons.2 ⟨subd6_1_90, List.forall_mem_cons.2 ⟨subd6_1_91, List.forall_mem_cons.2 ⟨subd6_1_92, List.forall_mem_cons.2 ⟨subd6_1_93, List.forall_mem_cons.2 ⟨subd6_1_94, List.forall_mem_cons.2 ⟨subd6_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_96 : subd6_1 [-6, 2, -2] = true := by decide +kernel
theorem subd6_1_97 : subd6_1 [-6, 2, -1] = true := by decide +kernel
theorem subd6_1_98 : subd6_1 [-6, 2, 0] = true := by decide +kernel
theorem subd6_1_99 : subd6_1 [-6, 2, 1] = true := by decide +kernel
theorem subd6_1_100 : subd6_1 [-6, 2, 2] = true := by decide +kernel
theorem subd6_1_101 : subd6_1 [-6, 2, 3] = true := by decide +kernel
theorem subd6_1_102 : subd6_1 [-6, 2, 4] = true := by decide +kernel
theorem subd6_1_103 : subd6_1 [-6, 2, 5] = true := by decide +kernel
theorem subd6_1_104 : subd6_1 [-6, 2, 6] = true := by decide +kernel
theorem subd6_1_105 : subd6_1 [-6, 2, 7] = true := by decide +kernel
theorem subd6_1_106 : subd6_1 [-6, 2, 8] = true := by decide +kernel
theorem subd6_1_107 : subd6_1 [-6, 2, 9] = true := by decide +kernel
theorem subd6_1_108 : subd6_1 [-6, 3, -6] = true := by decide +kernel
theorem subd6_1_109 : subd6_1 [-6, 3, -5] = true := by decide +kernel
theorem subd6_1_110 : subd6_1 [-6, 3, -4] = true := by decide +kernel
theorem subd6_1_111 : subd6_1 [-6, 3, -3] = true := by decide +kernel
theorem subd6_1_112 : subd6_1 [-6, 3, -2] = true := by decide +kernel
theorem subd6_1_113 : subd6_1 [-6, 3, -1] = true := by decide +kernel
theorem subd6_1_114 : subd6_1 [-6, 3, 0] = true := by decide +kernel
theorem subd6_1_115 : subd6_1 [-6, 3, 1] = true := by decide +kernel
theorem subd6_1_116 : subd6_1 [-6, 3, 2] = true := by decide +kernel
theorem subd6_1_117 : subd6_1 [-6, 3, 3] = true := by decide +kernel
theorem subd6_1_118 : subd6_1 [-6, 3, 4] = true := by decide +kernel
theorem subd6_1_119 : subd6_1 [-6, 3, 5] = true := by decide +kernel
theorem subd6_1_120 : subd6_1 [-6, 3, 6] = true := by decide +kernel
theorem subd6_1_121 : subd6_1 [-6, 3, 7] = true := by decide +kernel
theorem subd6_1_122 : subd6_1 [-6, 3, 8] = true := by decide +kernel
theorem subd6_1_123 : subd6_1 [-6, 3, 9] = true := by decide +kernel
theorem subd6_1_124 : subd6_1 [-6, 4, -6] = true := by decide +kernel
theorem subd6_1_125 : subd6_1 [-6, 4, -5] = true := by decide +kernel
theorem subd6_1_126 : subd6_1 [-6, 4, -4] = true := by decide +kernel
theorem subd6_1_127 : subd6_1 [-6, 4, -3] = true := by decide +kernel
theorem sbd6_1_3 : ∀ q ∈ blkd6_1_3, subd6_1 q = true := by
  unfold blkd6_1_3
  exact List.forall_mem_cons.2 ⟨subd6_1_96, List.forall_mem_cons.2 ⟨subd6_1_97, List.forall_mem_cons.2 ⟨subd6_1_98, List.forall_mem_cons.2 ⟨subd6_1_99, List.forall_mem_cons.2 ⟨subd6_1_100, List.forall_mem_cons.2 ⟨subd6_1_101, List.forall_mem_cons.2 ⟨subd6_1_102, List.forall_mem_cons.2 ⟨subd6_1_103, List.forall_mem_cons.2 ⟨subd6_1_104, List.forall_mem_cons.2 ⟨subd6_1_105, List.forall_mem_cons.2 ⟨subd6_1_106, List.forall_mem_cons.2 ⟨subd6_1_107, List.forall_mem_cons.2 ⟨subd6_1_108, List.forall_mem_cons.2 ⟨subd6_1_109, List.forall_mem_cons.2 ⟨subd6_1_110, List.forall_mem_cons.2 ⟨subd6_1_111, List.forall_mem_cons.2 ⟨subd6_1_112, List.forall_mem_cons.2 ⟨subd6_1_113, List.forall_mem_cons.2 ⟨subd6_1_114, List.forall_mem_cons.2 ⟨subd6_1_115, List.forall_mem_cons.2 ⟨subd6_1_116, List.forall_mem_cons.2 ⟨subd6_1_117, List.forall_mem_cons.2 ⟨subd6_1_118, List.forall_mem_cons.2 ⟨subd6_1_119, List.forall_mem_cons.2 ⟨subd6_1_120, List.forall_mem_cons.2 ⟨subd6_1_121, List.forall_mem_cons.2 ⟨subd6_1_122, List.forall_mem_cons.2 ⟨subd6_1_123, List.forall_mem_cons.2 ⟨subd6_1_124, List.forall_mem_cons.2 ⟨subd6_1_125, List.forall_mem_cons.2 ⟨subd6_1_126, List.forall_mem_cons.2 ⟨subd6_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_128 : subd6_1 [-6, 4, -2] = true := by decide +kernel
theorem subd6_1_129 : subd6_1 [-6, 4, -1] = true := by decide +kernel
theorem subd6_1_130 : subd6_1 [-6, 4, 0] = true := by decide +kernel
theorem subd6_1_131 : subd6_1 [-6, 4, 1] = true := by decide +kernel
theorem subd6_1_132 : subd6_1 [-6, 4, 2] = true := by decide +kernel
theorem subd6_1_133 : subd6_1 [-6, 4, 3] = true := by decide +kernel
theorem subd6_1_134 : subd6_1 [-6, 4, 4] = true := by decide +kernel
theorem subd6_1_135 : subd6_1 [-6, 4, 5] = true := by decide +kernel
theorem subd6_1_136 : subd6_1 [-6, 4, 6] = true := by decide +kernel
theorem subd6_1_137 : subd6_1 [-6, 4, 7] = true := by decide +kernel
theorem subd6_1_138 : subd6_1 [-6, 4, 8] = true := by decide +kernel
theorem subd6_1_139 : subd6_1 [-6, 4, 9] = true := by decide +kernel
theorem subd6_1_140 : subd6_1 [-6, 5, -6] = true := by decide +kernel
theorem subd6_1_141 : subd6_1 [-6, 5, -5] = true := by decide +kernel
theorem subd6_1_142 : subd6_1 [-6, 5, -4] = true := by decide +kernel
theorem subd6_1_143 : subd6_1 [-6, 5, -3] = true := by decide +kernel
theorem subd6_1_144 : subd6_1 [-6, 5, -2] = true := by decide +kernel
theorem subd6_1_145 : subd6_1 [-6, 5, -1] = true := by decide +kernel
theorem subd6_1_146 : subd6_1 [-6, 5, 0] = true := by decide +kernel
theorem subd6_1_147 : subd6_1 [-6, 5, 1] = true := by decide +kernel
theorem subd6_1_148 : subd6_1 [-6, 5, 2] = true := by decide +kernel
theorem subd6_1_149 : subd6_1 [-6, 5, 3] = true := by decide +kernel
theorem subd6_1_150 : subd6_1 [-6, 5, 4] = true := by decide +kernel
theorem subd6_1_151 : subd6_1 [-6, 5, 5] = true := by decide +kernel
theorem subd6_1_152 : subd6_1 [-6, 5, 6] = true := by decide +kernel
theorem subd6_1_153 : subd6_1 [-6, 5, 7] = true := by decide +kernel
theorem subd6_1_154 : subd6_1 [-6, 5, 8] = true := by decide +kernel
theorem subd6_1_155 : subd6_1 [-6, 6] = true := by decide +kernel
theorem subd6_1_156 : subd6_1 [-6, 7] = true := by decide +kernel
theorem subd6_1_157 : subd6_1 [-6, 8] = true := by decide +kernel
theorem subd6_1_158 : subd6_1 [-6, 9] = true := by decide +kernel
theorem subd6_1_159 : subd6_1 [-5, -8] = true := by decide +kernel
theorem sbd6_1_4 : ∀ q ∈ blkd6_1_4, subd6_1 q = true := by
  unfold blkd6_1_4
  exact List.forall_mem_cons.2 ⟨subd6_1_128, List.forall_mem_cons.2 ⟨subd6_1_129, List.forall_mem_cons.2 ⟨subd6_1_130, List.forall_mem_cons.2 ⟨subd6_1_131, List.forall_mem_cons.2 ⟨subd6_1_132, List.forall_mem_cons.2 ⟨subd6_1_133, List.forall_mem_cons.2 ⟨subd6_1_134, List.forall_mem_cons.2 ⟨subd6_1_135, List.forall_mem_cons.2 ⟨subd6_1_136, List.forall_mem_cons.2 ⟨subd6_1_137, List.forall_mem_cons.2 ⟨subd6_1_138, List.forall_mem_cons.2 ⟨subd6_1_139, List.forall_mem_cons.2 ⟨subd6_1_140, List.forall_mem_cons.2 ⟨subd6_1_141, List.forall_mem_cons.2 ⟨subd6_1_142, List.forall_mem_cons.2 ⟨subd6_1_143, List.forall_mem_cons.2 ⟨subd6_1_144, List.forall_mem_cons.2 ⟨subd6_1_145, List.forall_mem_cons.2 ⟨subd6_1_146, List.forall_mem_cons.2 ⟨subd6_1_147, List.forall_mem_cons.2 ⟨subd6_1_148, List.forall_mem_cons.2 ⟨subd6_1_149, List.forall_mem_cons.2 ⟨subd6_1_150, List.forall_mem_cons.2 ⟨subd6_1_151, List.forall_mem_cons.2 ⟨subd6_1_152, List.forall_mem_cons.2 ⟨subd6_1_153, List.forall_mem_cons.2 ⟨subd6_1_154, List.forall_mem_cons.2 ⟨subd6_1_155, List.forall_mem_cons.2 ⟨subd6_1_156, List.forall_mem_cons.2 ⟨subd6_1_157, List.forall_mem_cons.2 ⟨subd6_1_158, List.forall_mem_cons.2 ⟨subd6_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
