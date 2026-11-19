import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [0, -4] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [0, 3] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-1] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [1] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-3, -2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-3, -1] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-3, 0] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-3, 1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-3, 2] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-2, -2] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-2, -1, -7] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-2, -1, -6] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-2, -1, -5] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-2, -1, -4] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-2, -1, -3] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-2, -1, -2] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-2, -1, -1] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-2, -1, 0] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-2, -1, 1] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-2, -1, 2] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-2, -1, 3] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-2, -1, 4] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [-2, -1, 5] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [-2, -1, 6] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [-2, 0, -9] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [-2, 0, -8] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [-2, 0, -7] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [-2, 0, -6] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [-2, 0, -5] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [-2, 0, -4] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [-2, 0, -3] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [-2, 0, -2] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [-2, 0, -1] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [-2, 0, 0] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [-2, 0, 1] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [-2, 0, 2] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [-2, 0, 3] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [-2, 0, 4] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [-2, 0, 5] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [-2, 0, 6] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [-2, 0, 7] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [-2, 1, -9] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [-2, 1, -8] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [-2, 1, -7] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [-2, 1, -6] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [-2, 1, -5] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [-2, 1, -4] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [-2, 1, -3] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [-2, 1, -2] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [-2, 1, -1] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [-2, 1, 0] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [-2, 1, 1] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [-2, 1, 2] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [-2, 1, 3] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [-2, 1, 4] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [-2, 1, 5] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [-2, 1, 6] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [-2, 2, -8] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [-2, 2, -7] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [-2, 2, -6] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [-2, 2, -5] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [-2, 2, -4] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [-2, 2, -3] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [-2, 2, -2] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [-2, 2, -1] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [-2, 2, 0] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [-2, 2, 1] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [-2, 2, 2] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [-2, 2, 3] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [-2, 2, 4] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [-2, 2, 5] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [-2, 3] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [-1, -4] = true := by decide +kernel
theorem subd11_0_70 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_71 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_72 : subd11_0 [-1, -1, -9] = true := by decide +kernel
theorem subd11_0_73 : subd11_0 [-1, -1, -8] = true := by decide +kernel
theorem subd11_0_74 : subd11_0 [-1, -1, -7] = true := by decide +kernel
theorem subd11_0_75 : subd11_0 [-1, -1, -6] = true := by decide +kernel
theorem subd11_0_76 : subd11_0 [-1, -1, -5] = true := by decide +kernel
theorem subd11_0_77 : subd11_0 [-1, -1, -4] = true := by decide +kernel
theorem subd11_0_78 : subd11_0 [-1, -1, -3] = true := by decide +kernel
theorem subd11_0_79 : subd11_0 [-1, -1, -2] = true := by decide +kernel
theorem subd11_0_80 : subd11_0 [-1, -1, -1] = true := by decide +kernel
theorem subd11_0_81 : subd11_0 [-1, -1, 0] = true := by decide +kernel
theorem subd11_0_82 : subd11_0 [-1, -1, 1] = true := by decide +kernel
theorem subd11_0_83 : subd11_0 [-1, -1, 2] = true := by decide +kernel
theorem subd11_0_84 : subd11_0 [-1, -1, 3] = true := by decide +kernel
theorem subd11_0_85 : subd11_0 [-1, -1, 4] = true := by decide +kernel
theorem subd11_0_86 : subd11_0 [-1, -1, 5] = true := by decide +kernel
theorem subd11_0_87 : subd11_0 [-1, -1, 6] = true := by decide +kernel
theorem subd11_0_88 : subd11_0 [-1, -1, 7] = true := by decide +kernel
theorem subd11_0_89 : subd11_0 [-1, -1, 8] = true := by decide +kernel
theorem subd11_0_90 : subd11_0 [-1, 0, -9] = true := by decide +kernel
theorem subd11_0_91 : subd11_0 [-1, 0, -8] = true := by decide +kernel
theorem subd11_0_92 : subd11_0 [-1, 0, -7] = true := by decide +kernel
theorem subd11_0_93 : subd11_0 [-1, 0, -6] = true := by decide +kernel
theorem subd11_0_94 : subd11_0 [-1, 0, -5] = true := by decide +kernel
theorem subd11_0_95 : subd11_0 [-1, 0, -4] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_cons.2 ⟨subd11_0_70, List.forall_mem_cons.2 ⟨subd11_0_71, List.forall_mem_cons.2 ⟨subd11_0_72, List.forall_mem_cons.2 ⟨subd11_0_73, List.forall_mem_cons.2 ⟨subd11_0_74, List.forall_mem_cons.2 ⟨subd11_0_75, List.forall_mem_cons.2 ⟨subd11_0_76, List.forall_mem_cons.2 ⟨subd11_0_77, List.forall_mem_cons.2 ⟨subd11_0_78, List.forall_mem_cons.2 ⟨subd11_0_79, List.forall_mem_cons.2 ⟨subd11_0_80, List.forall_mem_cons.2 ⟨subd11_0_81, List.forall_mem_cons.2 ⟨subd11_0_82, List.forall_mem_cons.2 ⟨subd11_0_83, List.forall_mem_cons.2 ⟨subd11_0_84, List.forall_mem_cons.2 ⟨subd11_0_85, List.forall_mem_cons.2 ⟨subd11_0_86, List.forall_mem_cons.2 ⟨subd11_0_87, List.forall_mem_cons.2 ⟨subd11_0_88, List.forall_mem_cons.2 ⟨subd11_0_89, List.forall_mem_cons.2 ⟨subd11_0_90, List.forall_mem_cons.2 ⟨subd11_0_91, List.forall_mem_cons.2 ⟨subd11_0_92, List.forall_mem_cons.2 ⟨subd11_0_93, List.forall_mem_cons.2 ⟨subd11_0_94, List.forall_mem_cons.2 ⟨subd11_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_96 : subd11_0 [-1, 0, -3] = true := by decide +kernel
theorem subd11_0_97 : subd11_0 [-1, 0, -2] = true := by decide +kernel
theorem subd11_0_98 : subd11_0 [-1, 0, -1] = true := by decide +kernel
theorem subd11_0_99 : subd11_0 [-1, 0, 0] = true := by decide +kernel
theorem subd11_0_100 : subd11_0 [-1, 0, 1] = true := by decide +kernel
theorem subd11_0_101 : subd11_0 [-1, 0, 2] = true := by decide +kernel
theorem subd11_0_102 : subd11_0 [-1, 0, 3] = true := by decide +kernel
theorem subd11_0_103 : subd11_0 [-1, 0, 4] = true := by decide +kernel
theorem subd11_0_104 : subd11_0 [-1, 0, 5] = true := by decide +kernel
theorem subd11_0_105 : subd11_0 [-1, 0, 6] = true := by decide +kernel
theorem subd11_0_106 : subd11_0 [-1, 0, 7] = true := by decide +kernel
theorem subd11_0_107 : subd11_0 [-1, 0, 8] = true := by decide +kernel
theorem subd11_0_108 : subd11_0 [-1, 1, -9] = true := by decide +kernel
theorem subd11_0_109 : subd11_0 [-1, 1, -8] = true := by decide +kernel
theorem subd11_0_110 : subd11_0 [-1, 1, -7] = true := by decide +kernel
theorem subd11_0_111 : subd11_0 [-1, 1, -6] = true := by decide +kernel
theorem subd11_0_112 : subd11_0 [-1, 1, -5] = true := by decide +kernel
theorem subd11_0_113 : subd11_0 [-1, 1, -4] = true := by decide +kernel
theorem subd11_0_114 : subd11_0 [-1, 1, -3] = true := by decide +kernel
theorem subd11_0_115 : subd11_0 [-1, 1, -2] = true := by decide +kernel
theorem subd11_0_116 : subd11_0 [-1, 1, -1] = true := by decide +kernel
theorem subd11_0_117 : subd11_0 [-1, 1, 0] = true := by decide +kernel
theorem subd11_0_118 : subd11_0 [-1, 1, 1] = true := by decide +kernel
theorem subd11_0_119 : subd11_0 [-1, 1, 2] = true := by decide +kernel
theorem subd11_0_120 : subd11_0 [-1, 1, 3] = true := by decide +kernel
theorem subd11_0_121 : subd11_0 [-1, 1, 4] = true := by decide +kernel
theorem subd11_0_122 : subd11_0 [-1, 1, 5] = true := by decide +kernel
theorem subd11_0_123 : subd11_0 [-1, 1, 6] = true := by decide +kernel
theorem subd11_0_124 : subd11_0 [-1, 1, 7] = true := by decide +kernel
theorem subd11_0_125 : subd11_0 [-1, 2, -9] = true := by decide +kernel
theorem subd11_0_126 : subd11_0 [-1, 2, -8] = true := by decide +kernel
theorem subd11_0_127 : subd11_0 [-1, 2, -7] = true := by decide +kernel
theorem sbd11_0_3 : ∀ q ∈ blkd11_0_3, subd11_0 q = true := by
  unfold blkd11_0_3
  exact List.forall_mem_cons.2 ⟨subd11_0_96, List.forall_mem_cons.2 ⟨subd11_0_97, List.forall_mem_cons.2 ⟨subd11_0_98, List.forall_mem_cons.2 ⟨subd11_0_99, List.forall_mem_cons.2 ⟨subd11_0_100, List.forall_mem_cons.2 ⟨subd11_0_101, List.forall_mem_cons.2 ⟨subd11_0_102, List.forall_mem_cons.2 ⟨subd11_0_103, List.forall_mem_cons.2 ⟨subd11_0_104, List.forall_mem_cons.2 ⟨subd11_0_105, List.forall_mem_cons.2 ⟨subd11_0_106, List.forall_mem_cons.2 ⟨subd11_0_107, List.forall_mem_cons.2 ⟨subd11_0_108, List.forall_mem_cons.2 ⟨subd11_0_109, List.forall_mem_cons.2 ⟨subd11_0_110, List.forall_mem_cons.2 ⟨subd11_0_111, List.forall_mem_cons.2 ⟨subd11_0_112, List.forall_mem_cons.2 ⟨subd11_0_113, List.forall_mem_cons.2 ⟨subd11_0_114, List.forall_mem_cons.2 ⟨subd11_0_115, List.forall_mem_cons.2 ⟨subd11_0_116, List.forall_mem_cons.2 ⟨subd11_0_117, List.forall_mem_cons.2 ⟨subd11_0_118, List.forall_mem_cons.2 ⟨subd11_0_119, List.forall_mem_cons.2 ⟨subd11_0_120, List.forall_mem_cons.2 ⟨subd11_0_121, List.forall_mem_cons.2 ⟨subd11_0_122, List.forall_mem_cons.2 ⟨subd11_0_123, List.forall_mem_cons.2 ⟨subd11_0_124, List.forall_mem_cons.2 ⟨subd11_0_125, List.forall_mem_cons.2 ⟨subd11_0_126, List.forall_mem_cons.2 ⟨subd11_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_128 : subd11_0 [-1, 2, -6] = true := by decide +kernel
theorem subd11_0_129 : subd11_0 [-1, 2, -5] = true := by decide +kernel
theorem subd11_0_130 : subd11_0 [-1, 2, -4] = true := by decide +kernel
theorem subd11_0_131 : subd11_0 [-1, 2, -3] = true := by decide +kernel
theorem subd11_0_132 : subd11_0 [-1, 2, -2] = true := by decide +kernel
theorem subd11_0_133 : subd11_0 [-1, 2, -1] = true := by decide +kernel
theorem subd11_0_134 : subd11_0 [-1, 2, 0] = true := by decide +kernel
theorem subd11_0_135 : subd11_0 [-1, 2, 1] = true := by decide +kernel
theorem subd11_0_136 : subd11_0 [-1, 2, 2] = true := by decide +kernel
theorem subd11_0_137 : subd11_0 [-1, 2, 3] = true := by decide +kernel
theorem subd11_0_138 : subd11_0 [-1, 2, 4] = true := by decide +kernel
theorem subd11_0_139 : subd11_0 [-1, 2, 5] = true := by decide +kernel
theorem subd11_0_140 : subd11_0 [-1, 2, 6] = true := by decide +kernel
theorem subd11_0_141 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_142 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_143 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_144 : subd11_0 [0, -2, -7] = true := by decide +kernel
theorem subd11_0_145 : subd11_0 [0, -2, -6] = true := by decide +kernel
theorem subd11_0_146 : subd11_0 [0, -2, -5] = true := by decide +kernel
theorem subd11_0_147 : subd11_0 [0, -2, -4] = true := by decide +kernel
theorem subd11_0_148 : subd11_0 [0, -2, -3] = true := by decide +kernel
theorem subd11_0_149 : subd11_0 [0, -2, -2] = true := by decide +kernel
theorem subd11_0_150 : subd11_0 [0, -2, -1] = true := by decide +kernel
theorem subd11_0_151 : subd11_0 [0, -2, 0] = true := by decide +kernel
theorem subd11_0_152 : subd11_0 [0, -2, 1] = true := by decide +kernel
theorem subd11_0_153 : subd11_0 [0, -2, 2] = true := by decide +kernel
theorem subd11_0_154 : subd11_0 [0, -2, 3] = true := by decide +kernel
theorem subd11_0_155 : subd11_0 [0, -2, 4] = true := by decide +kernel
theorem subd11_0_156 : subd11_0 [0, -2, 5] = true := by decide +kernel
theorem subd11_0_157 : subd11_0 [0, -2, 6] = true := by decide +kernel
theorem subd11_0_158 : subd11_0 [0, -2, 7] = true := by decide +kernel
theorem subd11_0_159 : subd11_0 [0, -1, -9] = true := by decide +kernel
theorem sbd11_0_4 : ∀ q ∈ blkd11_0_4, subd11_0 q = true := by
  unfold blkd11_0_4
  exact List.forall_mem_cons.2 ⟨subd11_0_128, List.forall_mem_cons.2 ⟨subd11_0_129, List.forall_mem_cons.2 ⟨subd11_0_130, List.forall_mem_cons.2 ⟨subd11_0_131, List.forall_mem_cons.2 ⟨subd11_0_132, List.forall_mem_cons.2 ⟨subd11_0_133, List.forall_mem_cons.2 ⟨subd11_0_134, List.forall_mem_cons.2 ⟨subd11_0_135, List.forall_mem_cons.2 ⟨subd11_0_136, List.forall_mem_cons.2 ⟨subd11_0_137, List.forall_mem_cons.2 ⟨subd11_0_138, List.forall_mem_cons.2 ⟨subd11_0_139, List.forall_mem_cons.2 ⟨subd11_0_140, List.forall_mem_cons.2 ⟨subd11_0_141, List.forall_mem_cons.2 ⟨subd11_0_142, List.forall_mem_cons.2 ⟨subd11_0_143, List.forall_mem_cons.2 ⟨subd11_0_144, List.forall_mem_cons.2 ⟨subd11_0_145, List.forall_mem_cons.2 ⟨subd11_0_146, List.forall_mem_cons.2 ⟨subd11_0_147, List.forall_mem_cons.2 ⟨subd11_0_148, List.forall_mem_cons.2 ⟨subd11_0_149, List.forall_mem_cons.2 ⟨subd11_0_150, List.forall_mem_cons.2 ⟨subd11_0_151, List.forall_mem_cons.2 ⟨subd11_0_152, List.forall_mem_cons.2 ⟨subd11_0_153, List.forall_mem_cons.2 ⟨subd11_0_154, List.forall_mem_cons.2 ⟨subd11_0_155, List.forall_mem_cons.2 ⟨subd11_0_156, List.forall_mem_cons.2 ⟨subd11_0_157, List.forall_mem_cons.2 ⟨subd11_0_158, List.forall_mem_cons.2 ⟨subd11_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_160 : subd11_0 [0, -1, -8] = true := by decide +kernel
theorem subd11_0_161 : subd11_0 [0, -1, -7] = true := by decide +kernel
theorem subd11_0_162 : subd11_0 [0, -1, -6] = true := by decide +kernel
theorem subd11_0_163 : subd11_0 [0, -1, -5] = true := by decide +kernel
theorem subd11_0_164 : subd11_0 [0, -1, -4] = true := by decide +kernel
theorem subd11_0_165 : subd11_0 [0, -1, -3] = true := by decide +kernel
theorem subd11_0_166 : subd11_0 [0, -1, -2] = true := by decide +kernel
theorem subd11_0_167 : subd11_0 [0, -1, -1] = true := by decide +kernel
theorem subd11_0_168 : subd11_0 [0, -1, 0] = true := by decide +kernel
theorem subd11_0_169 : subd11_0 [0, -1, 1] = true := by decide +kernel
theorem subd11_0_170 : subd11_0 [0, -1, 2] = true := by decide +kernel
theorem subd11_0_171 : subd11_0 [0, -1, 3] = true := by decide +kernel
theorem subd11_0_172 : subd11_0 [0, -1, 4] = true := by decide +kernel
theorem subd11_0_173 : subd11_0 [0, -1, 5] = true := by decide +kernel
theorem subd11_0_174 : subd11_0 [0, -1, 6] = true := by decide +kernel
theorem subd11_0_175 : subd11_0 [0, -1, 7] = true := by decide +kernel
theorem subd11_0_176 : subd11_0 [0, -1, 8] = true := by decide +kernel
theorem subd11_0_177 : subd11_0 [0, 0, -9] = true := by decide +kernel
theorem subd11_0_178 : subd11_0 [0, 0, -8] = true := by decide +kernel
theorem subd11_0_179 : subd11_0 [0, 0, -7] = true := by decide +kernel
theorem subd11_0_180 : subd11_0 [0, 0, -6] = true := by decide +kernel
theorem subd11_0_181 : subd11_0 [0, 0, -5] = true := by decide +kernel
theorem subd11_0_182 : subd11_0 [0, 0, -4] = true := by decide +kernel
theorem subd11_0_183 : subd11_0 [0, 0, -3] = true := by decide +kernel
theorem subd11_0_184 : subd11_0 [0, 0, -2] = true := by decide +kernel
theorem subd11_0_185 : subd11_0 [0, 0, -1] = true := by decide +kernel
theorem subd11_0_186 : subd11_0 [0, 0, 0] = true := by decide +kernel
theorem subd11_0_187 : subd11_0 [0, 0, 1] = true := by decide +kernel
theorem subd11_0_188 : subd11_0 [0, 0, 2] = true := by decide +kernel
theorem subd11_0_189 : subd11_0 [0, 0, 3] = true := by decide +kernel
theorem subd11_0_190 : subd11_0 [0, 0, 4] = true := by decide +kernel
theorem subd11_0_191 : subd11_0 [0, 0, 5] = true := by decide +kernel
theorem sbd11_0_5 : ∀ q ∈ blkd11_0_5, subd11_0 q = true := by
  unfold blkd11_0_5
  exact List.forall_mem_cons.2 ⟨subd11_0_160, List.forall_mem_cons.2 ⟨subd11_0_161, List.forall_mem_cons.2 ⟨subd11_0_162, List.forall_mem_cons.2 ⟨subd11_0_163, List.forall_mem_cons.2 ⟨subd11_0_164, List.forall_mem_cons.2 ⟨subd11_0_165, List.forall_mem_cons.2 ⟨subd11_0_166, List.forall_mem_cons.2 ⟨subd11_0_167, List.forall_mem_cons.2 ⟨subd11_0_168, List.forall_mem_cons.2 ⟨subd11_0_169, List.forall_mem_cons.2 ⟨subd11_0_170, List.forall_mem_cons.2 ⟨subd11_0_171, List.forall_mem_cons.2 ⟨subd11_0_172, List.forall_mem_cons.2 ⟨subd11_0_173, List.forall_mem_cons.2 ⟨subd11_0_174, List.forall_mem_cons.2 ⟨subd11_0_175, List.forall_mem_cons.2 ⟨subd11_0_176, List.forall_mem_cons.2 ⟨subd11_0_177, List.forall_mem_cons.2 ⟨subd11_0_178, List.forall_mem_cons.2 ⟨subd11_0_179, List.forall_mem_cons.2 ⟨subd11_0_180, List.forall_mem_cons.2 ⟨subd11_0_181, List.forall_mem_cons.2 ⟨subd11_0_182, List.forall_mem_cons.2 ⟨subd11_0_183, List.forall_mem_cons.2 ⟨subd11_0_184, List.forall_mem_cons.2 ⟨subd11_0_185, List.forall_mem_cons.2 ⟨subd11_0_186, List.forall_mem_cons.2 ⟨subd11_0_187, List.forall_mem_cons.2 ⟨subd11_0_188, List.forall_mem_cons.2 ⟨subd11_0_189, List.forall_mem_cons.2 ⟨subd11_0_190, List.forall_mem_cons.2 ⟨subd11_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_192 : subd11_0 [0, 0, 6] = true := by decide +kernel
theorem subd11_0_193 : subd11_0 [0, 0, 7] = true := by decide +kernel
theorem subd11_0_194 : subd11_0 [0, 0, 8] = true := by decide +kernel
theorem subd11_0_195 : subd11_0 [0, 1, -9] = true := by decide +kernel
theorem subd11_0_196 : subd11_0 [0, 1, -8] = true := by decide +kernel
theorem subd11_0_197 : subd11_0 [0, 1, -7] = true := by decide +kernel
theorem subd11_0_198 : subd11_0 [0, 1, -6] = true := by decide +kernel
theorem subd11_0_199 : subd11_0 [0, 1, -5] = true := by decide +kernel
theorem subd11_0_200 : subd11_0 [0, 1, -4] = true := by decide +kernel
theorem subd11_0_201 : subd11_0 [0, 1, -3] = true := by decide +kernel
theorem subd11_0_202 : subd11_0 [0, 1, -2] = true := by decide +kernel
theorem subd11_0_203 : subd11_0 [0, 1, -1] = true := by decide +kernel
theorem subd11_0_204 : subd11_0 [0, 1, 0] = true := by decide +kernel
theorem subd11_0_205 : subd11_0 [0, 1, 1] = true := by decide +kernel
theorem subd11_0_206 : subd11_0 [0, 1, 2] = true := by decide +kernel
theorem subd11_0_207 : subd11_0 [0, 1, 3] = true := by decide +kernel
theorem subd11_0_208 : subd11_0 [0, 1, 4] = true := by decide +kernel
theorem subd11_0_209 : subd11_0 [0, 1, 5] = true := by decide +kernel
theorem subd11_0_210 : subd11_0 [0, 1, 6] = true := by decide +kernel
theorem subd11_0_211 : subd11_0 [0, 1, 7] = true := by decide +kernel
theorem subd11_0_212 : subd11_0 [0, 1, 8] = true := by decide +kernel
theorem subd11_0_213 : subd11_0 [0, 2, -8] = true := by decide +kernel
theorem subd11_0_214 : subd11_0 [0, 2, -7] = true := by decide +kernel
theorem subd11_0_215 : subd11_0 [0, 2, -6] = true := by decide +kernel
theorem subd11_0_216 : subd11_0 [0, 2, -5] = true := by decide +kernel
theorem subd11_0_217 : subd11_0 [0, 2, -4] = true := by decide +kernel
theorem subd11_0_218 : subd11_0 [0, 2, -3] = true := by decide +kernel
theorem subd11_0_219 : subd11_0 [0, 2, -2] = true := by decide +kernel
theorem subd11_0_220 : subd11_0 [0, 2, -1] = true := by decide +kernel
theorem subd11_0_221 : subd11_0 [0, 2, 0] = true := by decide +kernel
theorem subd11_0_222 : subd11_0 [0, 2, 1] = true := by decide +kernel
theorem subd11_0_223 : subd11_0 [0, 2, 2] = true := by decide +kernel
theorem sbd11_0_6 : ∀ q ∈ blkd11_0_6, subd11_0 q = true := by
  unfold blkd11_0_6
  exact List.forall_mem_cons.2 ⟨subd11_0_192, List.forall_mem_cons.2 ⟨subd11_0_193, List.forall_mem_cons.2 ⟨subd11_0_194, List.forall_mem_cons.2 ⟨subd11_0_195, List.forall_mem_cons.2 ⟨subd11_0_196, List.forall_mem_cons.2 ⟨subd11_0_197, List.forall_mem_cons.2 ⟨subd11_0_198, List.forall_mem_cons.2 ⟨subd11_0_199, List.forall_mem_cons.2 ⟨subd11_0_200, List.forall_mem_cons.2 ⟨subd11_0_201, List.forall_mem_cons.2 ⟨subd11_0_202, List.forall_mem_cons.2 ⟨subd11_0_203, List.forall_mem_cons.2 ⟨subd11_0_204, List.forall_mem_cons.2 ⟨subd11_0_205, List.forall_mem_cons.2 ⟨subd11_0_206, List.forall_mem_cons.2 ⟨subd11_0_207, List.forall_mem_cons.2 ⟨subd11_0_208, List.forall_mem_cons.2 ⟨subd11_0_209, List.forall_mem_cons.2 ⟨subd11_0_210, List.forall_mem_cons.2 ⟨subd11_0_211, List.forall_mem_cons.2 ⟨subd11_0_212, List.forall_mem_cons.2 ⟨subd11_0_213, List.forall_mem_cons.2 ⟨subd11_0_214, List.forall_mem_cons.2 ⟨subd11_0_215, List.forall_mem_cons.2 ⟨subd11_0_216, List.forall_mem_cons.2 ⟨subd11_0_217, List.forall_mem_cons.2 ⟨subd11_0_218, List.forall_mem_cons.2 ⟨subd11_0_219, List.forall_mem_cons.2 ⟨subd11_0_220, List.forall_mem_cons.2 ⟨subd11_0_221, List.forall_mem_cons.2 ⟨subd11_0_222, List.forall_mem_cons.2 ⟨subd11_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_224 : subd11_0 [0, 2, 3] = true := by decide +kernel
theorem subd11_0_225 : subd11_0 [0, 2, 4] = true := by decide +kernel
theorem subd11_0_226 : subd11_0 [0, 2, 5] = true := by decide +kernel
theorem subd11_0_227 : subd11_0 [0, 2, 6] = true := by decide +kernel
theorem subd11_0_228 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_229 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_230 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_231 : subd11_0 [1, -2, -7] = true := by decide +kernel
theorem subd11_0_232 : subd11_0 [1, -2, -6] = true := by decide +kernel
theorem subd11_0_233 : subd11_0 [1, -2, -5] = true := by decide +kernel
theorem subd11_0_234 : subd11_0 [1, -2, -4] = true := by decide +kernel
theorem subd11_0_235 : subd11_0 [1, -2, -3] = true := by decide +kernel
theorem subd11_0_236 : subd11_0 [1, -2, -2] = true := by decide +kernel
theorem subd11_0_237 : subd11_0 [1, -2, -1] = true := by decide +kernel
theorem subd11_0_238 : subd11_0 [1, -2, 0] = true := by decide +kernel
theorem subd11_0_239 : subd11_0 [1, -2, 1] = true := by decide +kernel
theorem subd11_0_240 : subd11_0 [1, -2, 2] = true := by decide +kernel
theorem subd11_0_241 : subd11_0 [1, -2, 3] = true := by decide +kernel
theorem subd11_0_242 : subd11_0 [1, -2, 4] = true := by decide +kernel
theorem subd11_0_243 : subd11_0 [1, -2, 5] = true := by decide +kernel
theorem subd11_0_244 : subd11_0 [1, -2, 6] = true := by decide +kernel
theorem subd11_0_245 : subd11_0 [1, -2, 7] = true := by decide +kernel
theorem subd11_0_246 : subd11_0 [1, -2, 8] = true := by decide +kernel
theorem subd11_0_247 : subd11_0 [1, -1, -8] = true := by decide +kernel
theorem subd11_0_248 : subd11_0 [1, -1, -7] = true := by decide +kernel
theorem subd11_0_249 : subd11_0 [1, -1, -6] = true := by decide +kernel
theorem subd11_0_250 : subd11_0 [1, -1, -5] = true := by decide +kernel
theorem subd11_0_251 : subd11_0 [1, -1, -4] = true := by decide +kernel
theorem subd11_0_252 : subd11_0 [1, -1, -3] = true := by decide +kernel
theorem subd11_0_253 : subd11_0 [1, -1, -2] = true := by decide +kernel
theorem subd11_0_254 : subd11_0 [1, -1, -1] = true := by decide +kernel
theorem subd11_0_255 : subd11_0 [1, -1, 0] = true := by decide +kernel
theorem sbd11_0_7 : ∀ q ∈ blkd11_0_7, subd11_0 q = true := by
  unfold blkd11_0_7
  exact List.forall_mem_cons.2 ⟨subd11_0_224, List.forall_mem_cons.2 ⟨subd11_0_225, List.forall_mem_cons.2 ⟨subd11_0_226, List.forall_mem_cons.2 ⟨subd11_0_227, List.forall_mem_cons.2 ⟨subd11_0_228, List.forall_mem_cons.2 ⟨subd11_0_229, List.forall_mem_cons.2 ⟨subd11_0_230, List.forall_mem_cons.2 ⟨subd11_0_231, List.forall_mem_cons.2 ⟨subd11_0_232, List.forall_mem_cons.2 ⟨subd11_0_233, List.forall_mem_cons.2 ⟨subd11_0_234, List.forall_mem_cons.2 ⟨subd11_0_235, List.forall_mem_cons.2 ⟨subd11_0_236, List.forall_mem_cons.2 ⟨subd11_0_237, List.forall_mem_cons.2 ⟨subd11_0_238, List.forall_mem_cons.2 ⟨subd11_0_239, List.forall_mem_cons.2 ⟨subd11_0_240, List.forall_mem_cons.2 ⟨subd11_0_241, List.forall_mem_cons.2 ⟨subd11_0_242, List.forall_mem_cons.2 ⟨subd11_0_243, List.forall_mem_cons.2 ⟨subd11_0_244, List.forall_mem_cons.2 ⟨subd11_0_245, List.forall_mem_cons.2 ⟨subd11_0_246, List.forall_mem_cons.2 ⟨subd11_0_247, List.forall_mem_cons.2 ⟨subd11_0_248, List.forall_mem_cons.2 ⟨subd11_0_249, List.forall_mem_cons.2 ⟨subd11_0_250, List.forall_mem_cons.2 ⟨subd11_0_251, List.forall_mem_cons.2 ⟨subd11_0_252, List.forall_mem_cons.2 ⟨subd11_0_253, List.forall_mem_cons.2 ⟨subd11_0_254, List.forall_mem_cons.2 ⟨subd11_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
