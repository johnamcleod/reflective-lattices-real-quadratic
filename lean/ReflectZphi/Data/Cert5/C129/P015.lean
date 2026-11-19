import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_1_64 : subd7_1 [0, 5] = true := by decide +kernel
theorem subd7_1_65 : subd7_1 [1, -6] = true := by decide +kernel
theorem subd7_1_66 : subd7_1 [1, -5] = true := by decide +kernel
theorem subd7_1_67 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_68 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_69 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_70 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_71 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_72 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_73 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_74 : subd7_1 [1, 3] = true := by decide +kernel
theorem subd7_1_75 : subd7_1 [1, 4] = true := by decide +kernel
theorem subd7_1_76 : subd7_1 [1, 5] = true := by decide +kernel
theorem subd7_1_77 : subd7_1 [2, -5] = true := by decide +kernel
theorem subd7_1_78 : subd7_1 [2, -4] = true := by decide +kernel
theorem subd7_1_79 : subd7_1 [2, -3] = true := by decide +kernel
theorem subd7_1_80 : subd7_1 [2, -2] = true := by decide +kernel
theorem subd7_1_81 : subd7_1 [2, -1] = true := by decide +kernel
theorem subd7_1_82 : subd7_1 [2, 0] = true := by decide +kernel
theorem subd7_1_83 : subd7_1 [2, 1] = true := by decide +kernel
theorem subd7_1_84 : subd7_1 [2, 2] = true := by decide +kernel
theorem subd7_1_85 : subd7_1 [2, 3] = true := by decide +kernel
theorem subd7_1_86 : subd7_1 [2, 4] = true := by decide +kernel
theorem subd7_1_87 : subd7_1 [2, 5] = true := by decide +kernel
theorem subd7_1_88 : subd7_1 [3, -5] = true := by decide +kernel
theorem subd7_1_89 : subd7_1 [3, -4] = true := by decide +kernel
theorem subd7_1_90 : subd7_1 [3, -3] = true := by decide +kernel
theorem subd7_1_91 : subd7_1 [3, -2] = true := by decide +kernel
theorem subd7_1_92 : subd7_1 [3, -1] = true := by decide +kernel
theorem subd7_1_93 : subd7_1 [3, 0] = true := by decide +kernel
theorem subd7_1_94 : subd7_1 [3, 1] = true := by decide +kernel
theorem subd7_1_95 : subd7_1 [3, 2] = true := by decide +kernel
theorem sbd7_1_2 : ∀ q ∈ blkd7_1_2, subd7_1 q = true := by
  unfold blkd7_1_2
  exact List.forall_mem_cons.2 ⟨subd7_1_64, List.forall_mem_cons.2 ⟨subd7_1_65, List.forall_mem_cons.2 ⟨subd7_1_66, List.forall_mem_cons.2 ⟨subd7_1_67, List.forall_mem_cons.2 ⟨subd7_1_68, List.forall_mem_cons.2 ⟨subd7_1_69, List.forall_mem_cons.2 ⟨subd7_1_70, List.forall_mem_cons.2 ⟨subd7_1_71, List.forall_mem_cons.2 ⟨subd7_1_72, List.forall_mem_cons.2 ⟨subd7_1_73, List.forall_mem_cons.2 ⟨subd7_1_74, List.forall_mem_cons.2 ⟨subd7_1_75, List.forall_mem_cons.2 ⟨subd7_1_76, List.forall_mem_cons.2 ⟨subd7_1_77, List.forall_mem_cons.2 ⟨subd7_1_78, List.forall_mem_cons.2 ⟨subd7_1_79, List.forall_mem_cons.2 ⟨subd7_1_80, List.forall_mem_cons.2 ⟨subd7_1_81, List.forall_mem_cons.2 ⟨subd7_1_82, List.forall_mem_cons.2 ⟨subd7_1_83, List.forall_mem_cons.2 ⟨subd7_1_84, List.forall_mem_cons.2 ⟨subd7_1_85, List.forall_mem_cons.2 ⟨subd7_1_86, List.forall_mem_cons.2 ⟨subd7_1_87, List.forall_mem_cons.2 ⟨subd7_1_88, List.forall_mem_cons.2 ⟨subd7_1_89, List.forall_mem_cons.2 ⟨subd7_1_90, List.forall_mem_cons.2 ⟨subd7_1_91, List.forall_mem_cons.2 ⟨subd7_1_92, List.forall_mem_cons.2 ⟨subd7_1_93, List.forall_mem_cons.2 ⟨subd7_1_94, List.forall_mem_cons.2 ⟨subd7_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_96 : subd7_1 [3, 3] = true := by decide +kernel
theorem subd7_1_97 : subd7_1 [3, 4] = true := by decide +kernel
theorem subd7_1_98 : subd7_1 [3, 5] = true := by decide +kernel
theorem subd7_1_99 : subd7_1 [4, -4] = true := by decide +kernel
theorem subd7_1_100 : subd7_1 [4, -3] = true := by decide +kernel
theorem subd7_1_101 : subd7_1 [4, -2] = true := by decide +kernel
theorem subd7_1_102 : subd7_1 [4, -1] = true := by decide +kernel
theorem subd7_1_103 : subd7_1 [4, 0] = true := by decide +kernel
theorem subd7_1_104 : subd7_1 [4, 1] = true := by decide +kernel
theorem subd7_1_105 : subd7_1 [4, 2] = true := by decide +kernel
theorem subd7_1_106 : subd7_1 [4, 3] = true := by decide +kernel
theorem subd7_1_107 : subd7_1 [4, 4] = true := by decide +kernel
theorem subd7_1_108 : subd7_1 [4, 5] = true := by decide +kernel
theorem subd7_1_109 : subd7_1 [5, -3] = true := by decide +kernel
theorem subd7_1_110 : subd7_1 [5, -2] = true := by decide +kernel
theorem subd7_1_111 : subd7_1 [5, -1] = true := by decide +kernel
theorem subd7_1_112 : subd7_1 [5, 0] = true := by decide +kernel
theorem subd7_1_113 : subd7_1 [5, 1] = true := by decide +kernel
theorem subd7_1_114 : subd7_1 [5, 2] = true := by decide +kernel
theorem subd7_1_115 : subd7_1 [5, 3] = true := by decide +kernel
theorem subd7_1_116 : subd7_1 [5, 4] = true := by decide +kernel
theorem subd7_1_117 : subd7_1 [6] = true := by decide +kernel
theorem sbd7_1_3 : ∀ q ∈ blkd7_1_3, subd7_1 q = true := by
  unfold blkd7_1_3
  exact List.forall_mem_cons.2 ⟨subd7_1_96, List.forall_mem_cons.2 ⟨subd7_1_97, List.forall_mem_cons.2 ⟨subd7_1_98, List.forall_mem_cons.2 ⟨subd7_1_99, List.forall_mem_cons.2 ⟨subd7_1_100, List.forall_mem_cons.2 ⟨subd7_1_101, List.forall_mem_cons.2 ⟨subd7_1_102, List.forall_mem_cons.2 ⟨subd7_1_103, List.forall_mem_cons.2 ⟨subd7_1_104, List.forall_mem_cons.2 ⟨subd7_1_105, List.forall_mem_cons.2 ⟨subd7_1_106, List.forall_mem_cons.2 ⟨subd7_1_107, List.forall_mem_cons.2 ⟨subd7_1_108, List.forall_mem_cons.2 ⟨subd7_1_109, List.forall_mem_cons.2 ⟨subd7_1_110, List.forall_mem_cons.2 ⟨subd7_1_111, List.forall_mem_cons.2 ⟨subd7_1_112, List.forall_mem_cons.2 ⟨subd7_1_113, List.forall_mem_cons.2 ⟨subd7_1_114, List.forall_mem_cons.2 ⟨subd7_1_115, List.forall_mem_cons.2 ⟨subd7_1_116, List.forall_mem_cons.2 ⟨subd7_1_117, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-4, -3] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-4, -2] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-4, -1] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-4, 0] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-4, 1] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-4, 2] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-3, -4] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-3, -3] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-3, -2] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [-3, -1, -6] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [-3, -1, -5] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [-3, -1, -4] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [-3, -1, -3] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [-3, -1, -2] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [-3, -1, -1] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [-3, -1, 0] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [-3, -1, 1] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [-3, -1, 2] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [-3, -1, 3] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [-3, -1, 4] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [-3, -1, 5] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [-3, -1, 6] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [-3, -1, 7] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [-3, 0, -6] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [-3, 0, -5] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [-3, 0, -4] = true := by decide +kernel
theorem subd7_2_26 : subd7_2 [-3, 0, -3] = true := by decide +kernel
theorem subd7_2_27 : subd7_2 [-3, 0, -2] = true := by decide +kernel
theorem subd7_2_28 : subd7_2 [-3, 0, -1] = true := by decide +kernel
theorem subd7_2_29 : subd7_2 [-3, 0, 0] = true := by decide +kernel
theorem subd7_2_30 : subd7_2 [-3, 0, 1] = true := by decide +kernel
theorem subd7_2_31 : subd7_2 [-3, 0, 2] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_cons.2 ⟨subd7_2_26, List.forall_mem_cons.2 ⟨subd7_2_27, List.forall_mem_cons.2 ⟨subd7_2_28, List.forall_mem_cons.2 ⟨subd7_2_29, List.forall_mem_cons.2 ⟨subd7_2_30, List.forall_mem_cons.2 ⟨subd7_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_32 : subd7_2 [-3, 0, 3] = true := by decide +kernel
theorem subd7_2_33 : subd7_2 [-3, 0, 4] = true := by decide +kernel
theorem subd7_2_34 : subd7_2 [-3, 0, 5] = true := by decide +kernel
theorem subd7_2_35 : subd7_2 [-3, 0, 6] = true := by decide +kernel
theorem subd7_2_36 : subd7_2 [-3, 0, 7] = true := by decide +kernel
theorem subd7_2_37 : subd7_2 [-3, 0, 8] = true := by decide +kernel
theorem subd7_2_38 : subd7_2 [-3, 1, -6] = true := by decide +kernel
theorem subd7_2_39 : subd7_2 [-3, 1, -5] = true := by decide +kernel
theorem subd7_2_40 : subd7_2 [-3, 1, -4] = true := by decide +kernel
theorem subd7_2_41 : subd7_2 [-3, 1, -3] = true := by decide +kernel
theorem subd7_2_42 : subd7_2 [-3, 1, -2] = true := by decide +kernel
theorem subd7_2_43 : subd7_2 [-3, 1, -1] = true := by decide +kernel
theorem subd7_2_44 : subd7_2 [-3, 1, 0] = true := by decide +kernel
theorem subd7_2_45 : subd7_2 [-3, 1, 1] = true := by decide +kernel
theorem subd7_2_46 : subd7_2 [-3, 1, 2] = true := by decide +kernel
theorem subd7_2_47 : subd7_2 [-3, 1, 3] = true := by decide +kernel
theorem subd7_2_48 : subd7_2 [-3, 1, 4] = true := by decide +kernel
theorem subd7_2_49 : subd7_2 [-3, 1, 5] = true := by decide +kernel
theorem subd7_2_50 : subd7_2 [-3, 1, 6] = true := by decide +kernel
theorem subd7_2_51 : subd7_2 [-3, 1, 7] = true := by decide +kernel
theorem subd7_2_52 : subd7_2 [-3, 1, 8] = true := by decide +kernel
theorem subd7_2_53 : subd7_2 [-3, 2] = true := by decide +kernel
theorem subd7_2_54 : subd7_2 [-3, 3] = true := by decide +kernel
theorem subd7_2_55 : subd7_2 [-2, -5] = true := by decide +kernel
theorem subd7_2_56 : subd7_2 [-2, -4] = true := by decide +kernel
theorem subd7_2_57 : subd7_2 [-2, -3] = true := by decide +kernel
theorem subd7_2_58 : subd7_2 [-2, -2, -8] = true := by decide +kernel
theorem subd7_2_59 : subd7_2 [-2, -2, -7] = true := by decide +kernel
theorem subd7_2_60 : subd7_2 [-2, -2, -6] = true := by decide +kernel
theorem subd7_2_61 : subd7_2 [-2, -2, -5] = true := by decide +kernel
theorem subd7_2_62 : subd7_2 [-2, -2, -4] = true := by decide +kernel
theorem subd7_2_63 : subd7_2 [-2, -2, -3] = true := by decide +kernel
theorem sbd7_2_1 : ∀ q ∈ blkd7_2_1, subd7_2 q = true := by
  unfold blkd7_2_1
  exact List.forall_mem_cons.2 ⟨subd7_2_32, List.forall_mem_cons.2 ⟨subd7_2_33, List.forall_mem_cons.2 ⟨subd7_2_34, List.forall_mem_cons.2 ⟨subd7_2_35, List.forall_mem_cons.2 ⟨subd7_2_36, List.forall_mem_cons.2 ⟨subd7_2_37, List.forall_mem_cons.2 ⟨subd7_2_38, List.forall_mem_cons.2 ⟨subd7_2_39, List.forall_mem_cons.2 ⟨subd7_2_40, List.forall_mem_cons.2 ⟨subd7_2_41, List.forall_mem_cons.2 ⟨subd7_2_42, List.forall_mem_cons.2 ⟨subd7_2_43, List.forall_mem_cons.2 ⟨subd7_2_44, List.forall_mem_cons.2 ⟨subd7_2_45, List.forall_mem_cons.2 ⟨subd7_2_46, List.forall_mem_cons.2 ⟨subd7_2_47, List.forall_mem_cons.2 ⟨subd7_2_48, List.forall_mem_cons.2 ⟨subd7_2_49, List.forall_mem_cons.2 ⟨subd7_2_50, List.forall_mem_cons.2 ⟨subd7_2_51, List.forall_mem_cons.2 ⟨subd7_2_52, List.forall_mem_cons.2 ⟨subd7_2_53, List.forall_mem_cons.2 ⟨subd7_2_54, List.forall_mem_cons.2 ⟨subd7_2_55, List.forall_mem_cons.2 ⟨subd7_2_56, List.forall_mem_cons.2 ⟨subd7_2_57, List.forall_mem_cons.2 ⟨subd7_2_58, List.forall_mem_cons.2 ⟨subd7_2_59, List.forall_mem_cons.2 ⟨subd7_2_60, List.forall_mem_cons.2 ⟨subd7_2_61, List.forall_mem_cons.2 ⟨subd7_2_62, List.forall_mem_cons.2 ⟨subd7_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_64 : subd7_2 [-2, -2, -2] = true := by decide +kernel
theorem subd7_2_65 : subd7_2 [-2, -2, -1] = true := by decide +kernel
theorem subd7_2_66 : subd7_2 [-2, -2, 0] = true := by decide +kernel
theorem subd7_2_67 : subd7_2 [-2, -2, 1] = true := by decide +kernel
theorem subd7_2_68 : subd7_2 [-2, -2, 2] = true := by decide +kernel
theorem subd7_2_69 : subd7_2 [-2, -2, 3] = true := by decide +kernel
theorem subd7_2_70 : subd7_2 [-2, -2, 4] = true := by decide +kernel
theorem subd7_2_71 : subd7_2 [-2, -2, 5] = true := by decide +kernel
theorem subd7_2_72 : subd7_2 [-2, -2, 6] = true := by decide +kernel
theorem subd7_2_73 : subd7_2 [-2, -2, 7] = true := by decide +kernel
theorem subd7_2_74 : subd7_2 [-2, -1, -8] = true := by decide +kernel
theorem subd7_2_75 : subd7_2 [-2, -1, -7] = true := by decide +kernel
theorem subd7_2_76 : subd7_2 [-2, -1, -6] = true := by decide +kernel
theorem subd7_2_77 : subd7_2 [-2, -1, -5] = true := by decide +kernel
theorem subd7_2_78 : subd7_2 [-2, -1, -4] = true := by decide +kernel
theorem subd7_2_79 : subd7_2 [-2, -1, -3] = true := by decide +kernel
theorem subd7_2_80 : subd7_2 [-2, -1, -2] = true := by decide +kernel
theorem subd7_2_81 : subd7_2 [-2, -1, -1] = true := by decide +kernel
theorem subd7_2_82 : subd7_2 [-2, -1, 0] = true := by decide +kernel
theorem subd7_2_83 : subd7_2 [-2, -1, 1] = true := by decide +kernel
theorem subd7_2_84 : subd7_2 [-2, -1, 2] = true := by decide +kernel
theorem subd7_2_85 : subd7_2 [-2, -1, 3] = true := by decide +kernel
theorem subd7_2_86 : subd7_2 [-2, -1, 4] = true := by decide +kernel
theorem subd7_2_87 : subd7_2 [-2, -1, 5] = true := by decide +kernel
theorem subd7_2_88 : subd7_2 [-2, -1, 6] = true := by decide +kernel
theorem subd7_2_89 : subd7_2 [-2, -1, 7] = true := by decide +kernel
theorem subd7_2_90 : subd7_2 [-2, -1, 8] = true := by decide +kernel
theorem subd7_2_91 : subd7_2 [-2, 0, -8] = true := by decide +kernel
theorem subd7_2_92 : subd7_2 [-2, 0, -7] = true := by decide +kernel
theorem subd7_2_93 : subd7_2 [-2, 0, -6] = true := by decide +kernel
theorem subd7_2_94 : subd7_2 [-2, 0, -5] = true := by decide +kernel
theorem subd7_2_95 : subd7_2 [-2, 0, -4] = true := by decide +kernel
theorem sbd7_2_2 : ∀ q ∈ blkd7_2_2, subd7_2 q = true := by
  unfold blkd7_2_2
  exact List.forall_mem_cons.2 ⟨subd7_2_64, List.forall_mem_cons.2 ⟨subd7_2_65, List.forall_mem_cons.2 ⟨subd7_2_66, List.forall_mem_cons.2 ⟨subd7_2_67, List.forall_mem_cons.2 ⟨subd7_2_68, List.forall_mem_cons.2 ⟨subd7_2_69, List.forall_mem_cons.2 ⟨subd7_2_70, List.forall_mem_cons.2 ⟨subd7_2_71, List.forall_mem_cons.2 ⟨subd7_2_72, List.forall_mem_cons.2 ⟨subd7_2_73, List.forall_mem_cons.2 ⟨subd7_2_74, List.forall_mem_cons.2 ⟨subd7_2_75, List.forall_mem_cons.2 ⟨subd7_2_76, List.forall_mem_cons.2 ⟨subd7_2_77, List.forall_mem_cons.2 ⟨subd7_2_78, List.forall_mem_cons.2 ⟨subd7_2_79, List.forall_mem_cons.2 ⟨subd7_2_80, List.forall_mem_cons.2 ⟨subd7_2_81, List.forall_mem_cons.2 ⟨subd7_2_82, List.forall_mem_cons.2 ⟨subd7_2_83, List.forall_mem_cons.2 ⟨subd7_2_84, List.forall_mem_cons.2 ⟨subd7_2_85, List.forall_mem_cons.2 ⟨subd7_2_86, List.forall_mem_cons.2 ⟨subd7_2_87, List.forall_mem_cons.2 ⟨subd7_2_88, List.forall_mem_cons.2 ⟨subd7_2_89, List.forall_mem_cons.2 ⟨subd7_2_90, List.forall_mem_cons.2 ⟨subd7_2_91, List.forall_mem_cons.2 ⟨subd7_2_92, List.forall_mem_cons.2 ⟨subd7_2_93, List.forall_mem_cons.2 ⟨subd7_2_94, List.forall_mem_cons.2 ⟨subd7_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_96 : subd7_2 [-2, 0, -3] = true := by decide +kernel
theorem subd7_2_97 : subd7_2 [-2, 0, -2] = true := by decide +kernel
theorem subd7_2_98 : subd7_2 [-2, 0, -1] = true := by decide +kernel
theorem subd7_2_99 : subd7_2 [-2, 0, 0] = true := by decide +kernel
theorem subd7_2_100 : subd7_2 [-2, 0, 1] = true := by decide +kernel
theorem subd7_2_101 : subd7_2 [-2, 0, 2] = true := by decide +kernel
theorem subd7_2_102 : subd7_2 [-2, 0, 3] = true := by decide +kernel
theorem subd7_2_103 : subd7_2 [-2, 0, 4] = true := by decide +kernel
theorem subd7_2_104 : subd7_2 [-2, 0, 5] = true := by decide +kernel
theorem subd7_2_105 : subd7_2 [-2, 0, 6] = true := by decide +kernel
theorem subd7_2_106 : subd7_2 [-2, 0, 7] = true := by decide +kernel
theorem subd7_2_107 : subd7_2 [-2, 0, 8] = true := by decide +kernel
theorem subd7_2_108 : subd7_2 [-2, 1, -7] = true := by decide +kernel
theorem subd7_2_109 : subd7_2 [-2, 1, -6] = true := by decide +kernel
theorem subd7_2_110 : subd7_2 [-2, 1, -5] = true := by decide +kernel
theorem subd7_2_111 : subd7_2 [-2, 1, -4] = true := by decide +kernel
theorem subd7_2_112 : subd7_2 [-2, 1, -3] = true := by decide +kernel
theorem subd7_2_113 : subd7_2 [-2, 1, -2] = true := by decide +kernel
theorem subd7_2_114 : subd7_2 [-2, 1, -1] = true := by decide +kernel
theorem subd7_2_115 : subd7_2 [-2, 1, 0] = true := by decide +kernel
theorem subd7_2_116 : subd7_2 [-2, 1, 1] = true := by decide +kernel
theorem subd7_2_117 : subd7_2 [-2, 1, 2] = true := by decide +kernel
theorem subd7_2_118 : subd7_2 [-2, 1, 3] = true := by decide +kernel
theorem subd7_2_119 : subd7_2 [-2, 1, 4] = true := by decide +kernel
theorem subd7_2_120 : subd7_2 [-2, 1, 5] = true := by decide +kernel
theorem subd7_2_121 : subd7_2 [-2, 1, 6] = true := by decide +kernel
theorem subd7_2_122 : subd7_2 [-2, 1, 7] = true := by decide +kernel
theorem subd7_2_123 : subd7_2 [-2, 1, 8] = true := by decide +kernel
theorem subd7_2_124 : subd7_2 [-2, 1, 9] = true := by decide +kernel
theorem subd7_2_125 : subd7_2 [-2, 2, -6] = true := by decide +kernel
theorem subd7_2_126 : subd7_2 [-2, 2, -5] = true := by decide +kernel
theorem subd7_2_127 : subd7_2 [-2, 2, -4] = true := by decide +kernel
theorem sbd7_2_3 : ∀ q ∈ blkd7_2_3, subd7_2 q = true := by
  unfold blkd7_2_3
  exact List.forall_mem_cons.2 ⟨subd7_2_96, List.forall_mem_cons.2 ⟨subd7_2_97, List.forall_mem_cons.2 ⟨subd7_2_98, List.forall_mem_cons.2 ⟨subd7_2_99, List.forall_mem_cons.2 ⟨subd7_2_100, List.forall_mem_cons.2 ⟨subd7_2_101, List.forall_mem_cons.2 ⟨subd7_2_102, List.forall_mem_cons.2 ⟨subd7_2_103, List.forall_mem_cons.2 ⟨subd7_2_104, List.forall_mem_cons.2 ⟨subd7_2_105, List.forall_mem_cons.2 ⟨subd7_2_106, List.forall_mem_cons.2 ⟨subd7_2_107, List.forall_mem_cons.2 ⟨subd7_2_108, List.forall_mem_cons.2 ⟨subd7_2_109, List.forall_mem_cons.2 ⟨subd7_2_110, List.forall_mem_cons.2 ⟨subd7_2_111, List.forall_mem_cons.2 ⟨subd7_2_112, List.forall_mem_cons.2 ⟨subd7_2_113, List.forall_mem_cons.2 ⟨subd7_2_114, List.forall_mem_cons.2 ⟨subd7_2_115, List.forall_mem_cons.2 ⟨subd7_2_116, List.forall_mem_cons.2 ⟨subd7_2_117, List.forall_mem_cons.2 ⟨subd7_2_118, List.forall_mem_cons.2 ⟨subd7_2_119, List.forall_mem_cons.2 ⟨subd7_2_120, List.forall_mem_cons.2 ⟨subd7_2_121, List.forall_mem_cons.2 ⟨subd7_2_122, List.forall_mem_cons.2 ⟨subd7_2_123, List.forall_mem_cons.2 ⟨subd7_2_124, List.forall_mem_cons.2 ⟨subd7_2_125, List.forall_mem_cons.2 ⟨subd7_2_126, List.forall_mem_cons.2 ⟨subd7_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
