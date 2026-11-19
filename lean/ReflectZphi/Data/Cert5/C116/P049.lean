import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1, -4] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [0, -4] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [0, 3] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-7, -1] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-7, 0] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-7, 1] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-7, 2] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-7, 3] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-7, 4] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-7, 5] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-7, 6] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-6, -3] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-6, -2] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-6, -1] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-6, 0] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-6, 1] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-6, 2] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-6, 3] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-6, 4] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [-6, 5] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [-6, 6] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [-6, 7] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [-5, -5] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [-5, -4] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [-5, -3] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [-5, -2] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [-5, -1] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [-5, 0] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [-5, 1] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [-5, 2] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [-5, 3] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [-5, 4] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [-5, 5] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [-5, 6] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [-5, 7] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_32 : subd10_1 [-5, 8] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [-4, -6] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [-4, -5] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [-4, -4] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [-4, -3] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [-4, -2] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [-4, -1, -6] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [-4, -1, -5] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [-4, -1, -4] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [-4, -1, -3] = true := by decide +kernel
theorem subd10_1_42 : subd10_1 [-4, -1, -2] = true := by decide +kernel
theorem subd10_1_43 : subd10_1 [-4, -1, -1] = true := by decide +kernel
theorem subd10_1_44 : subd10_1 [-4, -1, 0] = true := by decide +kernel
theorem subd10_1_45 : subd10_1 [-4, -1, 1] = true := by decide +kernel
theorem subd10_1_46 : subd10_1 [-4, -1, 2] = true := by decide +kernel
theorem subd10_1_47 : subd10_1 [-4, -1, 3] = true := by decide +kernel
theorem subd10_1_48 : subd10_1 [-4, -1, 4] = true := by decide +kernel
theorem subd10_1_49 : subd10_1 [-4, -1, 5] = true := by decide +kernel
theorem subd10_1_50 : subd10_1 [-4, -1, 6] = true := by decide +kernel
theorem subd10_1_51 : subd10_1 [-4, -1, 7] = true := by decide +kernel
theorem subd10_1_52 : subd10_1 [-4, 0, -7] = true := by decide +kernel
theorem subd10_1_53 : subd10_1 [-4, 0, -6] = true := by decide +kernel
theorem subd10_1_54 : subd10_1 [-4, 0, -5] = true := by decide +kernel
theorem subd10_1_55 : subd10_1 [-4, 0, -4] = true := by decide +kernel
theorem subd10_1_56 : subd10_1 [-4, 0, -3] = true := by decide +kernel
theorem subd10_1_57 : subd10_1 [-4, 0, -2] = true := by decide +kernel
theorem subd10_1_58 : subd10_1 [-4, 0, -1] = true := by decide +kernel
theorem subd10_1_59 : subd10_1 [-4, 0, 0] = true := by decide +kernel
theorem subd10_1_60 : subd10_1 [-4, 0, 1] = true := by decide +kernel
theorem subd10_1_61 : subd10_1 [-4, 0, 2] = true := by decide +kernel
theorem subd10_1_62 : subd10_1 [-4, 0, 3] = true := by decide +kernel
theorem subd10_1_63 : subd10_1 [-4, 0, 4] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_cons.2 ⟨subd10_1_42, List.forall_mem_cons.2 ⟨subd10_1_43, List.forall_mem_cons.2 ⟨subd10_1_44, List.forall_mem_cons.2 ⟨subd10_1_45, List.forall_mem_cons.2 ⟨subd10_1_46, List.forall_mem_cons.2 ⟨subd10_1_47, List.forall_mem_cons.2 ⟨subd10_1_48, List.forall_mem_cons.2 ⟨subd10_1_49, List.forall_mem_cons.2 ⟨subd10_1_50, List.forall_mem_cons.2 ⟨subd10_1_51, List.forall_mem_cons.2 ⟨subd10_1_52, List.forall_mem_cons.2 ⟨subd10_1_53, List.forall_mem_cons.2 ⟨subd10_1_54, List.forall_mem_cons.2 ⟨subd10_1_55, List.forall_mem_cons.2 ⟨subd10_1_56, List.forall_mem_cons.2 ⟨subd10_1_57, List.forall_mem_cons.2 ⟨subd10_1_58, List.forall_mem_cons.2 ⟨subd10_1_59, List.forall_mem_cons.2 ⟨subd10_1_60, List.forall_mem_cons.2 ⟨subd10_1_61, List.forall_mem_cons.2 ⟨subd10_1_62, List.forall_mem_cons.2 ⟨subd10_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_64 : subd10_1 [-4, 0, 5] = true := by decide +kernel
theorem subd10_1_65 : subd10_1 [-4, 0, 6] = true := by decide +kernel
theorem subd10_1_66 : subd10_1 [-4, 0, 7] = true := by decide +kernel
theorem subd10_1_67 : subd10_1 [-4, 1, -7] = true := by decide +kernel
theorem subd10_1_68 : subd10_1 [-4, 1, -6] = true := by decide +kernel
theorem subd10_1_69 : subd10_1 [-4, 1, -5] = true := by decide +kernel
theorem subd10_1_70 : subd10_1 [-4, 1, -4] = true := by decide +kernel
theorem subd10_1_71 : subd10_1 [-4, 1, -3] = true := by decide +kernel
theorem subd10_1_72 : subd10_1 [-4, 1, -2] = true := by decide +kernel
theorem subd10_1_73 : subd10_1 [-4, 1, -1] = true := by decide +kernel
theorem subd10_1_74 : subd10_1 [-4, 1, 0] = true := by decide +kernel
theorem subd10_1_75 : subd10_1 [-4, 1, 1] = true := by decide +kernel
theorem subd10_1_76 : subd10_1 [-4, 1, 2] = true := by decide +kernel
theorem subd10_1_77 : subd10_1 [-4, 1, 3] = true := by decide +kernel
theorem subd10_1_78 : subd10_1 [-4, 1, 4] = true := by decide +kernel
theorem subd10_1_79 : subd10_1 [-4, 1, 5] = true := by decide +kernel
theorem subd10_1_80 : subd10_1 [-4, 1, 6] = true := by decide +kernel
theorem subd10_1_81 : subd10_1 [-4, 1, 7] = true := by decide +kernel
theorem subd10_1_82 : subd10_1 [-4, 2, -7] = true := by decide +kernel
theorem subd10_1_83 : subd10_1 [-4, 2, -6] = true := by decide +kernel
theorem subd10_1_84 : subd10_1 [-4, 2, -5] = true := by decide +kernel
theorem subd10_1_85 : subd10_1 [-4, 2, -4] = true := by decide +kernel
theorem subd10_1_86 : subd10_1 [-4, 2, -3] = true := by decide +kernel
theorem subd10_1_87 : subd10_1 [-4, 2, -2] = true := by decide +kernel
theorem subd10_1_88 : subd10_1 [-4, 2, -1] = true := by decide +kernel
theorem subd10_1_89 : subd10_1 [-4, 2, 0] = true := by decide +kernel
theorem subd10_1_90 : subd10_1 [-4, 2, 1] = true := by decide +kernel
theorem subd10_1_91 : subd10_1 [-4, 2, 2] = true := by decide +kernel
theorem subd10_1_92 : subd10_1 [-4, 2, 3] = true := by decide +kernel
theorem subd10_1_93 : subd10_1 [-4, 2, 4] = true := by decide +kernel
theorem subd10_1_94 : subd10_1 [-4, 2, 5] = true := by decide +kernel
theorem subd10_1_95 : subd10_1 [-4, 2, 6] = true := by decide +kernel
theorem sbd10_1_2 : ∀ q ∈ blkd10_1_2, subd10_1 q = true := by
  unfold blkd10_1_2
  exact List.forall_mem_cons.2 ⟨subd10_1_64, List.forall_mem_cons.2 ⟨subd10_1_65, List.forall_mem_cons.2 ⟨subd10_1_66, List.forall_mem_cons.2 ⟨subd10_1_67, List.forall_mem_cons.2 ⟨subd10_1_68, List.forall_mem_cons.2 ⟨subd10_1_69, List.forall_mem_cons.2 ⟨subd10_1_70, List.forall_mem_cons.2 ⟨subd10_1_71, List.forall_mem_cons.2 ⟨subd10_1_72, List.forall_mem_cons.2 ⟨subd10_1_73, List.forall_mem_cons.2 ⟨subd10_1_74, List.forall_mem_cons.2 ⟨subd10_1_75, List.forall_mem_cons.2 ⟨subd10_1_76, List.forall_mem_cons.2 ⟨subd10_1_77, List.forall_mem_cons.2 ⟨subd10_1_78, List.forall_mem_cons.2 ⟨subd10_1_79, List.forall_mem_cons.2 ⟨subd10_1_80, List.forall_mem_cons.2 ⟨subd10_1_81, List.forall_mem_cons.2 ⟨subd10_1_82, List.forall_mem_cons.2 ⟨subd10_1_83, List.forall_mem_cons.2 ⟨subd10_1_84, List.forall_mem_cons.2 ⟨subd10_1_85, List.forall_mem_cons.2 ⟨subd10_1_86, List.forall_mem_cons.2 ⟨subd10_1_87, List.forall_mem_cons.2 ⟨subd10_1_88, List.forall_mem_cons.2 ⟨subd10_1_89, List.forall_mem_cons.2 ⟨subd10_1_90, List.forall_mem_cons.2 ⟨subd10_1_91, List.forall_mem_cons.2 ⟨subd10_1_92, List.forall_mem_cons.2 ⟨subd10_1_93, List.forall_mem_cons.2 ⟨subd10_1_94, List.forall_mem_cons.2 ⟨subd10_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_96 : subd10_1 [-4, 2, 7] = true := by decide +kernel
theorem subd10_1_97 : subd10_1 [-4, 3, -7] = true := by decide +kernel
theorem subd10_1_98 : subd10_1 [-4, 3, -6] = true := by decide +kernel
theorem subd10_1_99 : subd10_1 [-4, 3, -5] = true := by decide +kernel
theorem subd10_1_100 : subd10_1 [-4, 3, -4] = true := by decide +kernel
theorem subd10_1_101 : subd10_1 [-4, 3, -3] = true := by decide +kernel
theorem subd10_1_102 : subd10_1 [-4, 3, -2] = true := by decide +kernel
theorem subd10_1_103 : subd10_1 [-4, 3, -1] = true := by decide +kernel
theorem subd10_1_104 : subd10_1 [-4, 3, 0] = true := by decide +kernel
theorem subd10_1_105 : subd10_1 [-4, 3, 1] = true := by decide +kernel
theorem subd10_1_106 : subd10_1 [-4, 3, 2] = true := by decide +kernel
theorem subd10_1_107 : subd10_1 [-4, 3, 3] = true := by decide +kernel
theorem subd10_1_108 : subd10_1 [-4, 3, 4] = true := by decide +kernel
theorem subd10_1_109 : subd10_1 [-4, 3, 5] = true := by decide +kernel
theorem subd10_1_110 : subd10_1 [-4, 3, 6] = true := by decide +kernel
theorem subd10_1_111 : subd10_1 [-4, 4, -7] = true := by decide +kernel
theorem subd10_1_112 : subd10_1 [-4, 4, -6] = true := by decide +kernel
theorem subd10_1_113 : subd10_1 [-4, 4, -5] = true := by decide +kernel
theorem subd10_1_114 : subd10_1 [-4, 4, -4] = true := by decide +kernel
theorem subd10_1_115 : subd10_1 [-4, 4, -3] = true := by decide +kernel
theorem subd10_1_116 : subd10_1 [-4, 4, -2] = true := by decide +kernel
theorem subd10_1_117 : subd10_1 [-4, 4, -1] = true := by decide +kernel
theorem subd10_1_118 : subd10_1 [-4, 4, 0] = true := by decide +kernel
theorem subd10_1_119 : subd10_1 [-4, 4, 1] = true := by decide +kernel
theorem subd10_1_120 : subd10_1 [-4, 4, 2] = true := by decide +kernel
theorem subd10_1_121 : subd10_1 [-4, 4, 3] = true := by decide +kernel
theorem subd10_1_122 : subd10_1 [-4, 4, 4] = true := by decide +kernel
theorem subd10_1_123 : subd10_1 [-4, 4, 5] = true := by decide +kernel
theorem subd10_1_124 : subd10_1 [-4, 4, 6] = true := by decide +kernel
theorem subd10_1_125 : subd10_1 [-4, 5] = true := by decide +kernel
theorem subd10_1_126 : subd10_1 [-4, 6] = true := by decide +kernel
theorem subd10_1_127 : subd10_1 [-4, 7] = true := by decide +kernel
theorem sbd10_1_3 : ∀ q ∈ blkd10_1_3, subd10_1 q = true := by
  unfold blkd10_1_3
  exact List.forall_mem_cons.2 ⟨subd10_1_96, List.forall_mem_cons.2 ⟨subd10_1_97, List.forall_mem_cons.2 ⟨subd10_1_98, List.forall_mem_cons.2 ⟨subd10_1_99, List.forall_mem_cons.2 ⟨subd10_1_100, List.forall_mem_cons.2 ⟨subd10_1_101, List.forall_mem_cons.2 ⟨subd10_1_102, List.forall_mem_cons.2 ⟨subd10_1_103, List.forall_mem_cons.2 ⟨subd10_1_104, List.forall_mem_cons.2 ⟨subd10_1_105, List.forall_mem_cons.2 ⟨subd10_1_106, List.forall_mem_cons.2 ⟨subd10_1_107, List.forall_mem_cons.2 ⟨subd10_1_108, List.forall_mem_cons.2 ⟨subd10_1_109, List.forall_mem_cons.2 ⟨subd10_1_110, List.forall_mem_cons.2 ⟨subd10_1_111, List.forall_mem_cons.2 ⟨subd10_1_112, List.forall_mem_cons.2 ⟨subd10_1_113, List.forall_mem_cons.2 ⟨subd10_1_114, List.forall_mem_cons.2 ⟨subd10_1_115, List.forall_mem_cons.2 ⟨subd10_1_116, List.forall_mem_cons.2 ⟨subd10_1_117, List.forall_mem_cons.2 ⟨subd10_1_118, List.forall_mem_cons.2 ⟨subd10_1_119, List.forall_mem_cons.2 ⟨subd10_1_120, List.forall_mem_cons.2 ⟨subd10_1_121, List.forall_mem_cons.2 ⟨subd10_1_122, List.forall_mem_cons.2 ⟨subd10_1_123, List.forall_mem_cons.2 ⟨subd10_1_124, List.forall_mem_cons.2 ⟨subd10_1_125, List.forall_mem_cons.2 ⟨subd10_1_126, List.forall_mem_cons.2 ⟨subd10_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_128 : subd10_1 [-4, 8] = true := by decide +kernel
theorem subd10_1_129 : subd10_1 [-4, 9] = true := by decide +kernel
theorem subd10_1_130 : subd10_1 [-3, -7] = true := by decide +kernel
theorem subd10_1_131 : subd10_1 [-3, -6] = true := by decide +kernel
theorem subd10_1_132 : subd10_1 [-3, -5] = true := by decide +kernel
theorem subd10_1_133 : subd10_1 [-3, -4] = true := by decide +kernel
theorem subd10_1_134 : subd10_1 [-3, -3, -6] = true := by decide +kernel
theorem subd10_1_135 : subd10_1 [-3, -3, -5] = true := by decide +kernel
theorem subd10_1_136 : subd10_1 [-3, -3, -4] = true := by decide +kernel
theorem subd10_1_137 : subd10_1 [-3, -3, -3] = true := by decide +kernel
theorem subd10_1_138 : subd10_1 [-3, -3, -2] = true := by decide +kernel
theorem subd10_1_139 : subd10_1 [-3, -3, -1] = true := by decide +kernel
theorem subd10_1_140 : subd10_1 [-3, -3, 0] = true := by decide +kernel
theorem subd10_1_141 : subd10_1 [-3, -3, 1] = true := by decide +kernel
theorem subd10_1_142 : subd10_1 [-3, -3, 2] = true := by decide +kernel
theorem subd10_1_143 : subd10_1 [-3, -3, 3] = true := by decide +kernel
theorem subd10_1_144 : subd10_1 [-3, -3, 4] = true := by decide +kernel
theorem subd10_1_145 : subd10_1 [-3, -3, 5] = true := by decide +kernel
theorem subd10_1_146 : subd10_1 [-3, -3, 6] = true := by decide +kernel
theorem subd10_1_147 : subd10_1 [-3, -3, 7] = true := by decide +kernel
theorem subd10_1_148 : subd10_1 [-3, -2, -6] = true := by decide +kernel
theorem subd10_1_149 : subd10_1 [-3, -2, -5] = true := by decide +kernel
theorem subd10_1_150 : subd10_1 [-3, -2, -4] = true := by decide +kernel
theorem subd10_1_151 : subd10_1 [-3, -2, -3] = true := by decide +kernel
theorem subd10_1_152 : subd10_1 [-3, -2, -2] = true := by decide +kernel
theorem subd10_1_153 : subd10_1 [-3, -2, -1] = true := by decide +kernel
theorem subd10_1_154 : subd10_1 [-3, -2, 0] = true := by decide +kernel
theorem subd10_1_155 : subd10_1 [-3, -2, 1] = true := by decide +kernel
theorem subd10_1_156 : subd10_1 [-3, -2, 2] = true := by decide +kernel
theorem subd10_1_157 : subd10_1 [-3, -2, 3] = true := by decide +kernel
theorem subd10_1_158 : subd10_1 [-3, -2, 4] = true := by decide +kernel
theorem subd10_1_159 : subd10_1 [-3, -2, 5] = true := by decide +kernel
theorem sbd10_1_4 : ∀ q ∈ blkd10_1_4, subd10_1 q = true := by
  unfold blkd10_1_4
  exact List.forall_mem_cons.2 ⟨subd10_1_128, List.forall_mem_cons.2 ⟨subd10_1_129, List.forall_mem_cons.2 ⟨subd10_1_130, List.forall_mem_cons.2 ⟨subd10_1_131, List.forall_mem_cons.2 ⟨subd10_1_132, List.forall_mem_cons.2 ⟨subd10_1_133, List.forall_mem_cons.2 ⟨subd10_1_134, List.forall_mem_cons.2 ⟨subd10_1_135, List.forall_mem_cons.2 ⟨subd10_1_136, List.forall_mem_cons.2 ⟨subd10_1_137, List.forall_mem_cons.2 ⟨subd10_1_138, List.forall_mem_cons.2 ⟨subd10_1_139, List.forall_mem_cons.2 ⟨subd10_1_140, List.forall_mem_cons.2 ⟨subd10_1_141, List.forall_mem_cons.2 ⟨subd10_1_142, List.forall_mem_cons.2 ⟨subd10_1_143, List.forall_mem_cons.2 ⟨subd10_1_144, List.forall_mem_cons.2 ⟨subd10_1_145, List.forall_mem_cons.2 ⟨subd10_1_146, List.forall_mem_cons.2 ⟨subd10_1_147, List.forall_mem_cons.2 ⟨subd10_1_148, List.forall_mem_cons.2 ⟨subd10_1_149, List.forall_mem_cons.2 ⟨subd10_1_150, List.forall_mem_cons.2 ⟨subd10_1_151, List.forall_mem_cons.2 ⟨subd10_1_152, List.forall_mem_cons.2 ⟨subd10_1_153, List.forall_mem_cons.2 ⟨subd10_1_154, List.forall_mem_cons.2 ⟨subd10_1_155, List.forall_mem_cons.2 ⟨subd10_1_156, List.forall_mem_cons.2 ⟨subd10_1_157, List.forall_mem_cons.2 ⟨subd10_1_158, List.forall_mem_cons.2 ⟨subd10_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
