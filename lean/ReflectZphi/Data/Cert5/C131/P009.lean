import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_32 : subd9_1 [-2, -4] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [-2, -3] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [-2, -2] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [-2, -1] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [-2, 0] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [-2, 1] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [-2, 2] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [-2, 3] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [-2, 4] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [-1, -6] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [-1, -5] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [-1, -4] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [-1, -1] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [-1, 0] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [-1, 1] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [-1, 3] = true := by decide +kernel
theorem subd9_1_51 : subd9_1 [-1, 4] = true := by decide +kernel
theorem subd9_1_52 : subd9_1 [-1, 5] = true := by decide +kernel
theorem subd9_1_53 : subd9_1 [0, -6] = true := by decide +kernel
theorem subd9_1_54 : subd9_1 [0, -5] = true := by decide +kernel
theorem subd9_1_55 : subd9_1 [0, -4] = true := by decide +kernel
theorem subd9_1_56 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_57 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_58 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_59 : subd9_1 [0, 0] = true := by decide +kernel
theorem subd9_1_60 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_61 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_62 : subd9_1 [0, 3] = true := by decide +kernel
theorem subd9_1_63 : subd9_1 [0, 4] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_cons.2 ⟨subd9_1_51, List.forall_mem_cons.2 ⟨subd9_1_52, List.forall_mem_cons.2 ⟨subd9_1_53, List.forall_mem_cons.2 ⟨subd9_1_54, List.forall_mem_cons.2 ⟨subd9_1_55, List.forall_mem_cons.2 ⟨subd9_1_56, List.forall_mem_cons.2 ⟨subd9_1_57, List.forall_mem_cons.2 ⟨subd9_1_58, List.forall_mem_cons.2 ⟨subd9_1_59, List.forall_mem_cons.2 ⟨subd9_1_60, List.forall_mem_cons.2 ⟨subd9_1_61, List.forall_mem_cons.2 ⟨subd9_1_62, List.forall_mem_cons.2 ⟨subd9_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_64 : subd9_1 [0, 5] = true := by decide +kernel
theorem subd9_1_65 : subd9_1 [1, -6] = true := by decide +kernel
theorem subd9_1_66 : subd9_1 [1, -5] = true := by decide +kernel
theorem subd9_1_67 : subd9_1 [1, -4] = true := by decide +kernel
theorem subd9_1_68 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_69 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_70 : subd9_1 [1, -1] = true := by decide +kernel
theorem subd9_1_71 : subd9_1 [1, 0] = true := by decide +kernel
theorem subd9_1_72 : subd9_1 [1, 1] = true := by decide +kernel
theorem subd9_1_73 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_74 : subd9_1 [1, 3] = true := by decide +kernel
theorem subd9_1_75 : subd9_1 [1, 4] = true := by decide +kernel
theorem subd9_1_76 : subd9_1 [1, 5] = true := by decide +kernel
theorem subd9_1_77 : subd9_1 [2, -5] = true := by decide +kernel
theorem subd9_1_78 : subd9_1 [2, -4] = true := by decide +kernel
theorem subd9_1_79 : subd9_1 [2, -3] = true := by decide +kernel
theorem subd9_1_80 : subd9_1 [2, -2] = true := by decide +kernel
theorem subd9_1_81 : subd9_1 [2, -1] = true := by decide +kernel
theorem subd9_1_82 : subd9_1 [2, 0] = true := by decide +kernel
theorem subd9_1_83 : subd9_1 [2, 1] = true := by decide +kernel
theorem subd9_1_84 : subd9_1 [2, 2] = true := by decide +kernel
theorem subd9_1_85 : subd9_1 [2, 3] = true := by decide +kernel
theorem subd9_1_86 : subd9_1 [2, 4] = true := by decide +kernel
theorem subd9_1_87 : subd9_1 [2, 5] = true := by decide +kernel
theorem subd9_1_88 : subd9_1 [3, -5] = true := by decide +kernel
theorem subd9_1_89 : subd9_1 [3, -4] = true := by decide +kernel
theorem subd9_1_90 : subd9_1 [3, -3] = true := by decide +kernel
theorem subd9_1_91 : subd9_1 [3, -2] = true := by decide +kernel
theorem subd9_1_92 : subd9_1 [3, -1] = true := by decide +kernel
theorem subd9_1_93 : subd9_1 [3, 0] = true := by decide +kernel
theorem subd9_1_94 : subd9_1 [3, 1] = true := by decide +kernel
theorem subd9_1_95 : subd9_1 [3, 2] = true := by decide +kernel
theorem sbd9_1_2 : ∀ q ∈ blkd9_1_2, subd9_1 q = true := by
  unfold blkd9_1_2
  exact List.forall_mem_cons.2 ⟨subd9_1_64, List.forall_mem_cons.2 ⟨subd9_1_65, List.forall_mem_cons.2 ⟨subd9_1_66, List.forall_mem_cons.2 ⟨subd9_1_67, List.forall_mem_cons.2 ⟨subd9_1_68, List.forall_mem_cons.2 ⟨subd9_1_69, List.forall_mem_cons.2 ⟨subd9_1_70, List.forall_mem_cons.2 ⟨subd9_1_71, List.forall_mem_cons.2 ⟨subd9_1_72, List.forall_mem_cons.2 ⟨subd9_1_73, List.forall_mem_cons.2 ⟨subd9_1_74, List.forall_mem_cons.2 ⟨subd9_1_75, List.forall_mem_cons.2 ⟨subd9_1_76, List.forall_mem_cons.2 ⟨subd9_1_77, List.forall_mem_cons.2 ⟨subd9_1_78, List.forall_mem_cons.2 ⟨subd9_1_79, List.forall_mem_cons.2 ⟨subd9_1_80, List.forall_mem_cons.2 ⟨subd9_1_81, List.forall_mem_cons.2 ⟨subd9_1_82, List.forall_mem_cons.2 ⟨subd9_1_83, List.forall_mem_cons.2 ⟨subd9_1_84, List.forall_mem_cons.2 ⟨subd9_1_85, List.forall_mem_cons.2 ⟨subd9_1_86, List.forall_mem_cons.2 ⟨subd9_1_87, List.forall_mem_cons.2 ⟨subd9_1_88, List.forall_mem_cons.2 ⟨subd9_1_89, List.forall_mem_cons.2 ⟨subd9_1_90, List.forall_mem_cons.2 ⟨subd9_1_91, List.forall_mem_cons.2 ⟨subd9_1_92, List.forall_mem_cons.2 ⟨subd9_1_93, List.forall_mem_cons.2 ⟨subd9_1_94, List.forall_mem_cons.2 ⟨subd9_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_96 : subd9_1 [3, 3] = true := by decide +kernel
theorem subd9_1_97 : subd9_1 [3, 4] = true := by decide +kernel
theorem subd9_1_98 : subd9_1 [3, 5] = true := by decide +kernel
theorem subd9_1_99 : subd9_1 [4, -4] = true := by decide +kernel
theorem subd9_1_100 : subd9_1 [4, -3] = true := by decide +kernel
theorem subd9_1_101 : subd9_1 [4, -2] = true := by decide +kernel
theorem subd9_1_102 : subd9_1 [4, -1] = true := by decide +kernel
theorem subd9_1_103 : subd9_1 [4, 0] = true := by decide +kernel
theorem subd9_1_104 : subd9_1 [4, 1] = true := by decide +kernel
theorem subd9_1_105 : subd9_1 [4, 2] = true := by decide +kernel
theorem subd9_1_106 : subd9_1 [4, 3] = true := by decide +kernel
theorem subd9_1_107 : subd9_1 [4, 4] = true := by decide +kernel
theorem subd9_1_108 : subd9_1 [4, 5] = true := by decide +kernel
theorem subd9_1_109 : subd9_1 [5, -3] = true := by decide +kernel
theorem subd9_1_110 : subd9_1 [5, -2] = true := by decide +kernel
theorem subd9_1_111 : subd9_1 [5, -1] = true := by decide +kernel
theorem subd9_1_112 : subd9_1 [5, 0] = true := by decide +kernel
theorem subd9_1_113 : subd9_1 [5, 1] = true := by decide +kernel
theorem subd9_1_114 : subd9_1 [5, 2] = true := by decide +kernel
theorem subd9_1_115 : subd9_1 [5, 3] = true := by decide +kernel
theorem subd9_1_116 : subd9_1 [5, 4] = true := by decide +kernel
theorem subd9_1_117 : subd9_1 [6] = true := by decide +kernel
theorem sbd9_1_3 : ∀ q ∈ blkd9_1_3, subd9_1 q = true := by
  unfold blkd9_1_3
  exact List.forall_mem_cons.2 ⟨subd9_1_96, List.forall_mem_cons.2 ⟨subd9_1_97, List.forall_mem_cons.2 ⟨subd9_1_98, List.forall_mem_cons.2 ⟨subd9_1_99, List.forall_mem_cons.2 ⟨subd9_1_100, List.forall_mem_cons.2 ⟨subd9_1_101, List.forall_mem_cons.2 ⟨subd9_1_102, List.forall_mem_cons.2 ⟨subd9_1_103, List.forall_mem_cons.2 ⟨subd9_1_104, List.forall_mem_cons.2 ⟨subd9_1_105, List.forall_mem_cons.2 ⟨subd9_1_106, List.forall_mem_cons.2 ⟨subd9_1_107, List.forall_mem_cons.2 ⟨subd9_1_108, List.forall_mem_cons.2 ⟨subd9_1_109, List.forall_mem_cons.2 ⟨subd9_1_110, List.forall_mem_cons.2 ⟨subd9_1_111, List.forall_mem_cons.2 ⟨subd9_1_112, List.forall_mem_cons.2 ⟨subd9_1_113, List.forall_mem_cons.2 ⟨subd9_1_114, List.forall_mem_cons.2 ⟨subd9_1_115, List.forall_mem_cons.2 ⟨subd9_1_116, List.forall_mem_cons.2 ⟨subd9_1_117, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-7, -3] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-7, -2] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-7, -1] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-7, 0] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-7, 1] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-7, 2] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-7, 3] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-6, -5] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [-6, -4] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [-6, -3] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [-6, -2] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [-6, -1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [-6, 0] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [-6, 1] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [-6, 2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [-6, 3] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [-6, 4] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [-6, 5] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [-5, -6] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [-5, -5] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [-5, -4] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [-5, -3] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [-5, -2] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [-5, -1, -8] = true := by decide +kernel
theorem subd10_0_24 : subd10_0 [-5, -1, -7] = true := by decide +kernel
theorem subd10_0_25 : subd10_0 [-5, -1, -6] = true := by decide +kernel
theorem subd10_0_26 : subd10_0 [-5, -1, -5] = true := by decide +kernel
theorem subd10_0_27 : subd10_0 [-5, -1, -4] = true := by decide +kernel
theorem subd10_0_28 : subd10_0 [-5, -1, -3] = true := by decide +kernel
theorem subd10_0_29 : subd10_0 [-5, -1, -2] = true := by decide +kernel
theorem subd10_0_30 : subd10_0 [-5, -1, -1] = true := by decide +kernel
theorem subd10_0_31 : subd10_0 [-5, -1, 0] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_cons.2 ⟨subd10_0_24, List.forall_mem_cons.2 ⟨subd10_0_25, List.forall_mem_cons.2 ⟨subd10_0_26, List.forall_mem_cons.2 ⟨subd10_0_27, List.forall_mem_cons.2 ⟨subd10_0_28, List.forall_mem_cons.2 ⟨subd10_0_29, List.forall_mem_cons.2 ⟨subd10_0_30, List.forall_mem_cons.2 ⟨subd10_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_32 : subd10_0 [-5, -1, 1] = true := by decide +kernel
theorem subd10_0_33 : subd10_0 [-5, -1, 2] = true := by decide +kernel
theorem subd10_0_34 : subd10_0 [-5, -1, 3] = true := by decide +kernel
theorem subd10_0_35 : subd10_0 [-5, -1, 4] = true := by decide +kernel
theorem subd10_0_36 : subd10_0 [-5, -1, 5] = true := by decide +kernel
theorem subd10_0_37 : subd10_0 [-5, 0, -8] = true := by decide +kernel
theorem subd10_0_38 : subd10_0 [-5, 0, -7] = true := by decide +kernel
theorem subd10_0_39 : subd10_0 [-5, 0, -6] = true := by decide +kernel
theorem subd10_0_40 : subd10_0 [-5, 0, -5] = true := by decide +kernel
theorem subd10_0_41 : subd10_0 [-5, 0, -4] = true := by decide +kernel
theorem subd10_0_42 : subd10_0 [-5, 0, -3] = true := by decide +kernel
theorem subd10_0_43 : subd10_0 [-5, 0, -2] = true := by decide +kernel
theorem subd10_0_44 : subd10_0 [-5, 0, -1] = true := by decide +kernel
theorem subd10_0_45 : subd10_0 [-5, 0, 0] = true := by decide +kernel
theorem subd10_0_46 : subd10_0 [-5, 0, 1] = true := by decide +kernel
theorem subd10_0_47 : subd10_0 [-5, 0, 2] = true := by decide +kernel
theorem subd10_0_48 : subd10_0 [-5, 0, 3] = true := by decide +kernel
theorem subd10_0_49 : subd10_0 [-5, 0, 4] = true := by decide +kernel
theorem subd10_0_50 : subd10_0 [-5, 0, 5] = true := by decide +kernel
theorem subd10_0_51 : subd10_0 [-5, 1, -8] = true := by decide +kernel
theorem subd10_0_52 : subd10_0 [-5, 1, -7] = true := by decide +kernel
theorem subd10_0_53 : subd10_0 [-5, 1, -6] = true := by decide +kernel
theorem subd10_0_54 : subd10_0 [-5, 1, -5] = true := by decide +kernel
theorem subd10_0_55 : subd10_0 [-5, 1, -4] = true := by decide +kernel
theorem subd10_0_56 : subd10_0 [-5, 1, -3] = true := by decide +kernel
theorem subd10_0_57 : subd10_0 [-5, 1, -2] = true := by decide +kernel
theorem subd10_0_58 : subd10_0 [-5, 1, -1] = true := by decide +kernel
theorem subd10_0_59 : subd10_0 [-5, 1, 0] = true := by decide +kernel
theorem subd10_0_60 : subd10_0 [-5, 1, 1] = true := by decide +kernel
theorem subd10_0_61 : subd10_0 [-5, 1, 2] = true := by decide +kernel
theorem subd10_0_62 : subd10_0 [-5, 1, 3] = true := by decide +kernel
theorem subd10_0_63 : subd10_0 [-5, 1, 4] = true := by decide +kernel
theorem sbd10_0_1 : ∀ q ∈ blkd10_0_1, subd10_0 q = true := by
  unfold blkd10_0_1
  exact List.forall_mem_cons.2 ⟨subd10_0_32, List.forall_mem_cons.2 ⟨subd10_0_33, List.forall_mem_cons.2 ⟨subd10_0_34, List.forall_mem_cons.2 ⟨subd10_0_35, List.forall_mem_cons.2 ⟨subd10_0_36, List.forall_mem_cons.2 ⟨subd10_0_37, List.forall_mem_cons.2 ⟨subd10_0_38, List.forall_mem_cons.2 ⟨subd10_0_39, List.forall_mem_cons.2 ⟨subd10_0_40, List.forall_mem_cons.2 ⟨subd10_0_41, List.forall_mem_cons.2 ⟨subd10_0_42, List.forall_mem_cons.2 ⟨subd10_0_43, List.forall_mem_cons.2 ⟨subd10_0_44, List.forall_mem_cons.2 ⟨subd10_0_45, List.forall_mem_cons.2 ⟨subd10_0_46, List.forall_mem_cons.2 ⟨subd10_0_47, List.forall_mem_cons.2 ⟨subd10_0_48, List.forall_mem_cons.2 ⟨subd10_0_49, List.forall_mem_cons.2 ⟨subd10_0_50, List.forall_mem_cons.2 ⟨subd10_0_51, List.forall_mem_cons.2 ⟨subd10_0_52, List.forall_mem_cons.2 ⟨subd10_0_53, List.forall_mem_cons.2 ⟨subd10_0_54, List.forall_mem_cons.2 ⟨subd10_0_55, List.forall_mem_cons.2 ⟨subd10_0_56, List.forall_mem_cons.2 ⟨subd10_0_57, List.forall_mem_cons.2 ⟨subd10_0_58, List.forall_mem_cons.2 ⟨subd10_0_59, List.forall_mem_cons.2 ⟨subd10_0_60, List.forall_mem_cons.2 ⟨subd10_0_61, List.forall_mem_cons.2 ⟨subd10_0_62, List.forall_mem_cons.2 ⟨subd10_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
