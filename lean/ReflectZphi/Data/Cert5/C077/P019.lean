import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_32 : subd10_2 [0, 4] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [1, -5] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [1, -4] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [1, -3] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [1, -2] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [1, -1] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [1, 0] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [1, 1] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [1, 2] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [1, 3] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [2, -5] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [2, -4] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [2, -3] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [2, -2] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [2, -1] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [2, 0] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [2, 1] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [2, 2] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [3, -4] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [3, -3] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [3, -2] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [3, -1] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [3, 0] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [3, 1] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-6] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-5, -4] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-5, -3] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-5, -2] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-5, -1] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-5, 0] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-5, 1] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-5, 2] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-5, 3] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-5, 4] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-5, 5] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-4, -6] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-4, -5] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-4, -4] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-4, -3] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-4, -2] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-4, -1] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [-4, 0] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [-4, 1] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [-4, 2] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [-4, 3] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [-4, 4] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [-4, 5] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [-4, 6] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [-3, -6] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [-3, -5] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [-3, -4] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [-3, -3] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [-3, -2] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [-3, -1] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [-3, 0] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [-3, 1] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_32 : subd10_3 [-3, 2] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [-3, 3] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [-3, 4] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [-3, 5] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [-3, 6] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [-2, -7] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [-2, -6] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [-2, -5] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [-2, -4] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [-2, -3] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [-2, -1, -8] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [-2, -1, -7] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [-2, -1, -6] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [-2, -1, -5] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [-2, -1, -4] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [-2, -1, -3] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [-2, -1, -2] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [-2, -1, -1] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [-2, -1, 0] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [-2, -1, 1] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [-2, -1, 2] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [-2, -1, 3] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [-2, -1, 4] = true := by decide +kernel
theorem subd10_3_56 : subd10_3 [-2, -1, 5] = true := by decide +kernel
theorem subd10_3_57 : subd10_3 [-2, -1, 6] = true := by decide +kernel
theorem subd10_3_58 : subd10_3 [-2, 0, -8] = true := by decide +kernel
theorem subd10_3_59 : subd10_3 [-2, 0, -7] = true := by decide +kernel
theorem subd10_3_60 : subd10_3 [-2, 0, -6] = true := by decide +kernel
theorem subd10_3_61 : subd10_3 [-2, 0, -5] = true := by decide +kernel
theorem subd10_3_62 : subd10_3 [-2, 0, -4] = true := by decide +kernel
theorem subd10_3_63 : subd10_3 [-2, 0, -3] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_cons.2 ⟨subd10_3_56, List.forall_mem_cons.2 ⟨subd10_3_57, List.forall_mem_cons.2 ⟨subd10_3_58, List.forall_mem_cons.2 ⟨subd10_3_59, List.forall_mem_cons.2 ⟨subd10_3_60, List.forall_mem_cons.2 ⟨subd10_3_61, List.forall_mem_cons.2 ⟨subd10_3_62, List.forall_mem_cons.2 ⟨subd10_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_64 : subd10_3 [-2, 0, -2] = true := by decide +kernel
theorem subd10_3_65 : subd10_3 [-2, 0, -1] = true := by decide +kernel
theorem subd10_3_66 : subd10_3 [-2, 0, 0] = true := by decide +kernel
theorem subd10_3_67 : subd10_3 [-2, 0, 1] = true := by decide +kernel
theorem subd10_3_68 : subd10_3 [-2, 0, 2] = true := by decide +kernel
theorem subd10_3_69 : subd10_3 [-2, 0, 3] = true := by decide +kernel
theorem subd10_3_70 : subd10_3 [-2, 0, 4] = true := by decide +kernel
theorem subd10_3_71 : subd10_3 [-2, 0, 5] = true := by decide +kernel
theorem subd10_3_72 : subd10_3 [-2, 0, 6] = true := by decide +kernel
theorem subd10_3_73 : subd10_3 [-2, 1, -8] = true := by decide +kernel
theorem subd10_3_74 : subd10_3 [-2, 1, -7] = true := by decide +kernel
theorem subd10_3_75 : subd10_3 [-2, 1, -6] = true := by decide +kernel
theorem subd10_3_76 : subd10_3 [-2, 1, -5] = true := by decide +kernel
theorem subd10_3_77 : subd10_3 [-2, 1, -4] = true := by decide +kernel
theorem subd10_3_78 : subd10_3 [-2, 1, -3] = true := by decide +kernel
theorem subd10_3_79 : subd10_3 [-2, 1, -2] = true := by decide +kernel
theorem subd10_3_80 : subd10_3 [-2, 1, -1] = true := by decide +kernel
theorem subd10_3_81 : subd10_3 [-2, 1, 0] = true := by decide +kernel
theorem subd10_3_82 : subd10_3 [-2, 1, 1] = true := by decide +kernel
theorem subd10_3_83 : subd10_3 [-2, 1, 2] = true := by decide +kernel
theorem subd10_3_84 : subd10_3 [-2, 1, 3] = true := by decide +kernel
theorem subd10_3_85 : subd10_3 [-2, 1, 4] = true := by decide +kernel
theorem subd10_3_86 : subd10_3 [-2, 1, 5] = true := by decide +kernel
theorem subd10_3_87 : subd10_3 [-2, 2] = true := by decide +kernel
theorem subd10_3_88 : subd10_3 [-2, 3] = true := by decide +kernel
theorem subd10_3_89 : subd10_3 [-2, 4] = true := by decide +kernel
theorem subd10_3_90 : subd10_3 [-2, 5] = true := by decide +kernel
theorem subd10_3_91 : subd10_3 [-2, 6] = true := by decide +kernel
theorem subd10_3_92 : subd10_3 [-1, -7] = true := by decide +kernel
theorem subd10_3_93 : subd10_3 [-1, -6] = true := by decide +kernel
theorem subd10_3_94 : subd10_3 [-1, -5] = true := by decide +kernel
theorem subd10_3_95 : subd10_3 [-1, -4] = true := by decide +kernel
theorem sbd10_3_2 : ∀ q ∈ blkd10_3_2, subd10_3 q = true := by
  unfold blkd10_3_2
  exact List.forall_mem_cons.2 ⟨subd10_3_64, List.forall_mem_cons.2 ⟨subd10_3_65, List.forall_mem_cons.2 ⟨subd10_3_66, List.forall_mem_cons.2 ⟨subd10_3_67, List.forall_mem_cons.2 ⟨subd10_3_68, List.forall_mem_cons.2 ⟨subd10_3_69, List.forall_mem_cons.2 ⟨subd10_3_70, List.forall_mem_cons.2 ⟨subd10_3_71, List.forall_mem_cons.2 ⟨subd10_3_72, List.forall_mem_cons.2 ⟨subd10_3_73, List.forall_mem_cons.2 ⟨subd10_3_74, List.forall_mem_cons.2 ⟨subd10_3_75, List.forall_mem_cons.2 ⟨subd10_3_76, List.forall_mem_cons.2 ⟨subd10_3_77, List.forall_mem_cons.2 ⟨subd10_3_78, List.forall_mem_cons.2 ⟨subd10_3_79, List.forall_mem_cons.2 ⟨subd10_3_80, List.forall_mem_cons.2 ⟨subd10_3_81, List.forall_mem_cons.2 ⟨subd10_3_82, List.forall_mem_cons.2 ⟨subd10_3_83, List.forall_mem_cons.2 ⟨subd10_3_84, List.forall_mem_cons.2 ⟨subd10_3_85, List.forall_mem_cons.2 ⟨subd10_3_86, List.forall_mem_cons.2 ⟨subd10_3_87, List.forall_mem_cons.2 ⟨subd10_3_88, List.forall_mem_cons.2 ⟨subd10_3_89, List.forall_mem_cons.2 ⟨subd10_3_90, List.forall_mem_cons.2 ⟨subd10_3_91, List.forall_mem_cons.2 ⟨subd10_3_92, List.forall_mem_cons.2 ⟨subd10_3_93, List.forall_mem_cons.2 ⟨subd10_3_94, List.forall_mem_cons.2 ⟨subd10_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_96 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_97 : subd10_3 [-1, -2, -7] = true := by decide +kernel
theorem subd10_3_98 : subd10_3 [-1, -2, -6] = true := by decide +kernel
theorem subd10_3_99 : subd10_3 [-1, -2, -5] = true := by decide +kernel
theorem subd10_3_100 : subd10_3 [-1, -2, -4] = true := by decide +kernel
theorem subd10_3_101 : subd10_3 [-1, -2, -3] = true := by decide +kernel
theorem subd10_3_102 : subd10_3 [-1, -2, -2] = true := by decide +kernel
theorem subd10_3_103 : subd10_3 [-1, -2, -1] = true := by decide +kernel
theorem subd10_3_104 : subd10_3 [-1, -2, 0] = true := by decide +kernel
theorem subd10_3_105 : subd10_3 [-1, -2, 1] = true := by decide +kernel
theorem subd10_3_106 : subd10_3 [-1, -2, 2] = true := by decide +kernel
theorem subd10_3_107 : subd10_3 [-1, -2, 3] = true := by decide +kernel
theorem subd10_3_108 : subd10_3 [-1, -2, 4] = true := by decide +kernel
theorem subd10_3_109 : subd10_3 [-1, -2, 5] = true := by decide +kernel
theorem subd10_3_110 : subd10_3 [-1, -2, 6] = true := by decide +kernel
theorem subd10_3_111 : subd10_3 [-1, -1, -8] = true := by decide +kernel
theorem subd10_3_112 : subd10_3 [-1, -1, -7] = true := by decide +kernel
theorem subd10_3_113 : subd10_3 [-1, -1, -6] = true := by decide +kernel
theorem subd10_3_114 : subd10_3 [-1, -1, -5] = true := by decide +kernel
theorem subd10_3_115 : subd10_3 [-1, -1, -4] = true := by decide +kernel
theorem subd10_3_116 : subd10_3 [-1, -1, -3] = true := by decide +kernel
theorem subd10_3_117 : subd10_3 [-1, -1, -2] = true := by decide +kernel
theorem subd10_3_118 : subd10_3 [-1, -1, -1] = true := by decide +kernel
theorem subd10_3_119 : subd10_3 [-1, -1, 0] = true := by decide +kernel
theorem subd10_3_120 : subd10_3 [-1, -1, 1] = true := by decide +kernel
theorem subd10_3_121 : subd10_3 [-1, -1, 2] = true := by decide +kernel
theorem subd10_3_122 : subd10_3 [-1, -1, 3] = true := by decide +kernel
theorem subd10_3_123 : subd10_3 [-1, -1, 4] = true := by decide +kernel
theorem subd10_3_124 : subd10_3 [-1, -1, 5] = true := by decide +kernel
theorem subd10_3_125 : subd10_3 [-1, -1, 6] = true := by decide +kernel
theorem subd10_3_126 : subd10_3 [-1, 0, -8] = true := by decide +kernel
theorem subd10_3_127 : subd10_3 [-1, 0, -7] = true := by decide +kernel
theorem sbd10_3_3 : ∀ q ∈ blkd10_3_3, subd10_3 q = true := by
  unfold blkd10_3_3
  exact List.forall_mem_cons.2 ⟨subd10_3_96, List.forall_mem_cons.2 ⟨subd10_3_97, List.forall_mem_cons.2 ⟨subd10_3_98, List.forall_mem_cons.2 ⟨subd10_3_99, List.forall_mem_cons.2 ⟨subd10_3_100, List.forall_mem_cons.2 ⟨subd10_3_101, List.forall_mem_cons.2 ⟨subd10_3_102, List.forall_mem_cons.2 ⟨subd10_3_103, List.forall_mem_cons.2 ⟨subd10_3_104, List.forall_mem_cons.2 ⟨subd10_3_105, List.forall_mem_cons.2 ⟨subd10_3_106, List.forall_mem_cons.2 ⟨subd10_3_107, List.forall_mem_cons.2 ⟨subd10_3_108, List.forall_mem_cons.2 ⟨subd10_3_109, List.forall_mem_cons.2 ⟨subd10_3_110, List.forall_mem_cons.2 ⟨subd10_3_111, List.forall_mem_cons.2 ⟨subd10_3_112, List.forall_mem_cons.2 ⟨subd10_3_113, List.forall_mem_cons.2 ⟨subd10_3_114, List.forall_mem_cons.2 ⟨subd10_3_115, List.forall_mem_cons.2 ⟨subd10_3_116, List.forall_mem_cons.2 ⟨subd10_3_117, List.forall_mem_cons.2 ⟨subd10_3_118, List.forall_mem_cons.2 ⟨subd10_3_119, List.forall_mem_cons.2 ⟨subd10_3_120, List.forall_mem_cons.2 ⟨subd10_3_121, List.forall_mem_cons.2 ⟨subd10_3_122, List.forall_mem_cons.2 ⟨subd10_3_123, List.forall_mem_cons.2 ⟨subd10_3_124, List.forall_mem_cons.2 ⟨subd10_3_125, List.forall_mem_cons.2 ⟨subd10_3_126, List.forall_mem_cons.2 ⟨subd10_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_128 : subd10_3 [-1, 0, -6] = true := by decide +kernel
theorem subd10_3_129 : subd10_3 [-1, 0, -5] = true := by decide +kernel
theorem subd10_3_130 : subd10_3 [-1, 0, -4] = true := by decide +kernel
theorem subd10_3_131 : subd10_3 [-1, 0, -3] = true := by decide +kernel
theorem subd10_3_132 : subd10_3 [-1, 0, -2] = true := by decide +kernel
theorem subd10_3_133 : subd10_3 [-1, 0, -1] = true := by decide +kernel
theorem subd10_3_134 : subd10_3 [-1, 0, 0] = true := by decide +kernel
theorem subd10_3_135 : subd10_3 [-1, 0, 1] = true := by decide +kernel
theorem subd10_3_136 : subd10_3 [-1, 0, 2] = true := by decide +kernel
theorem subd10_3_137 : subd10_3 [-1, 0, 3] = true := by decide +kernel
theorem subd10_3_138 : subd10_3 [-1, 0, 4] = true := by decide +kernel
theorem subd10_3_139 : subd10_3 [-1, 0, 5] = true := by decide +kernel
theorem subd10_3_140 : subd10_3 [-1, 0, 6] = true := by decide +kernel
theorem subd10_3_141 : subd10_3 [-1, 1, -8] = true := by decide +kernel
theorem subd10_3_142 : subd10_3 [-1, 1, -7] = true := by decide +kernel
theorem subd10_3_143 : subd10_3 [-1, 1, -6] = true := by decide +kernel
theorem subd10_3_144 : subd10_3 [-1, 1, -5] = true := by decide +kernel
theorem subd10_3_145 : subd10_3 [-1, 1, -4] = true := by decide +kernel
theorem subd10_3_146 : subd10_3 [-1, 1, -3] = true := by decide +kernel
theorem subd10_3_147 : subd10_3 [-1, 1, -2] = true := by decide +kernel
theorem subd10_3_148 : subd10_3 [-1, 1, -1] = true := by decide +kernel
theorem subd10_3_149 : subd10_3 [-1, 1, 0] = true := by decide +kernel
theorem subd10_3_150 : subd10_3 [-1, 1, 1] = true := by decide +kernel
theorem subd10_3_151 : subd10_3 [-1, 1, 2] = true := by decide +kernel
theorem subd10_3_152 : subd10_3 [-1, 1, 3] = true := by decide +kernel
theorem subd10_3_153 : subd10_3 [-1, 1, 4] = true := by decide +kernel
theorem subd10_3_154 : subd10_3 [-1, 1, 5] = true := by decide +kernel
theorem subd10_3_155 : subd10_3 [-1, 1, 6] = true := by decide +kernel
theorem subd10_3_156 : subd10_3 [-1, 2, -8] = true := by decide +kernel
theorem subd10_3_157 : subd10_3 [-1, 2, -7] = true := by decide +kernel
theorem subd10_3_158 : subd10_3 [-1, 2, -6] = true := by decide +kernel
theorem subd10_3_159 : subd10_3 [-1, 2, -5] = true := by decide +kernel
theorem sbd10_3_4 : ∀ q ∈ blkd10_3_4, subd10_3 q = true := by
  unfold blkd10_3_4
  exact List.forall_mem_cons.2 ⟨subd10_3_128, List.forall_mem_cons.2 ⟨subd10_3_129, List.forall_mem_cons.2 ⟨subd10_3_130, List.forall_mem_cons.2 ⟨subd10_3_131, List.forall_mem_cons.2 ⟨subd10_3_132, List.forall_mem_cons.2 ⟨subd10_3_133, List.forall_mem_cons.2 ⟨subd10_3_134, List.forall_mem_cons.2 ⟨subd10_3_135, List.forall_mem_cons.2 ⟨subd10_3_136, List.forall_mem_cons.2 ⟨subd10_3_137, List.forall_mem_cons.2 ⟨subd10_3_138, List.forall_mem_cons.2 ⟨subd10_3_139, List.forall_mem_cons.2 ⟨subd10_3_140, List.forall_mem_cons.2 ⟨subd10_3_141, List.forall_mem_cons.2 ⟨subd10_3_142, List.forall_mem_cons.2 ⟨subd10_3_143, List.forall_mem_cons.2 ⟨subd10_3_144, List.forall_mem_cons.2 ⟨subd10_3_145, List.forall_mem_cons.2 ⟨subd10_3_146, List.forall_mem_cons.2 ⟨subd10_3_147, List.forall_mem_cons.2 ⟨subd10_3_148, List.forall_mem_cons.2 ⟨subd10_3_149, List.forall_mem_cons.2 ⟨subd10_3_150, List.forall_mem_cons.2 ⟨subd10_3_151, List.forall_mem_cons.2 ⟨subd10_3_152, List.forall_mem_cons.2 ⟨subd10_3_153, List.forall_mem_cons.2 ⟨subd10_3_154, List.forall_mem_cons.2 ⟨subd10_3_155, List.forall_mem_cons.2 ⟨subd10_3_156, List.forall_mem_cons.2 ⟨subd10_3_157, List.forall_mem_cons.2 ⟨subd10_3_158, List.forall_mem_cons.2 ⟨subd10_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
