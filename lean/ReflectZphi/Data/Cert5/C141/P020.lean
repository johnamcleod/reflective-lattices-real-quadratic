import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_64 : subd10_0 [1, -5] = true := by decide +kernel
theorem subd10_0_65 : subd10_0 [1, -4] = true := by decide +kernel
theorem subd10_0_66 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_67 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_68 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_69 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_70 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_71 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_72 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_73 : subd10_0 [1, 4] = true := by decide +kernel
theorem subd10_0_74 : subd10_0 [1, 5] = true := by decide +kernel
theorem subd10_0_75 : subd10_0 [2, -6] = true := by decide +kernel
theorem subd10_0_76 : subd10_0 [2, -5] = true := by decide +kernel
theorem subd10_0_77 : subd10_0 [2, -4] = true := by decide +kernel
theorem subd10_0_78 : subd10_0 [2, -3] = true := by decide +kernel
theorem subd10_0_79 : subd10_0 [2, -2] = true := by decide +kernel
theorem subd10_0_80 : subd10_0 [2, -1] = true := by decide +kernel
theorem subd10_0_81 : subd10_0 [2, 0] = true := by decide +kernel
theorem subd10_0_82 : subd10_0 [2, 1] = true := by decide +kernel
theorem subd10_0_83 : subd10_0 [2, 2] = true := by decide +kernel
theorem subd10_0_84 : subd10_0 [2, 3] = true := by decide +kernel
theorem subd10_0_85 : subd10_0 [2, 4] = true := by decide +kernel
theorem subd10_0_86 : subd10_0 [2, 5] = true := by decide +kernel
theorem subd10_0_87 : subd10_0 [3, -5] = true := by decide +kernel
theorem subd10_0_88 : subd10_0 [3, -4] = true := by decide +kernel
theorem subd10_0_89 : subd10_0 [3, -3] = true := by decide +kernel
theorem subd10_0_90 : subd10_0 [3, -2] = true := by decide +kernel
theorem subd10_0_91 : subd10_0 [3, -1] = true := by decide +kernel
theorem subd10_0_92 : subd10_0 [3, 0] = true := by decide +kernel
theorem subd10_0_93 : subd10_0 [3, 1] = true := by decide +kernel
theorem subd10_0_94 : subd10_0 [3, 2] = true := by decide +kernel
theorem subd10_0_95 : subd10_0 [3, 3] = true := by decide +kernel
theorem sbd10_0_2 : ∀ q ∈ blkd10_0_2, subd10_0 q = true := by
  unfold blkd10_0_2
  exact List.forall_mem_cons.2 ⟨subd10_0_64, List.forall_mem_cons.2 ⟨subd10_0_65, List.forall_mem_cons.2 ⟨subd10_0_66, List.forall_mem_cons.2 ⟨subd10_0_67, List.forall_mem_cons.2 ⟨subd10_0_68, List.forall_mem_cons.2 ⟨subd10_0_69, List.forall_mem_cons.2 ⟨subd10_0_70, List.forall_mem_cons.2 ⟨subd10_0_71, List.forall_mem_cons.2 ⟨subd10_0_72, List.forall_mem_cons.2 ⟨subd10_0_73, List.forall_mem_cons.2 ⟨subd10_0_74, List.forall_mem_cons.2 ⟨subd10_0_75, List.forall_mem_cons.2 ⟨subd10_0_76, List.forall_mem_cons.2 ⟨subd10_0_77, List.forall_mem_cons.2 ⟨subd10_0_78, List.forall_mem_cons.2 ⟨subd10_0_79, List.forall_mem_cons.2 ⟨subd10_0_80, List.forall_mem_cons.2 ⟨subd10_0_81, List.forall_mem_cons.2 ⟨subd10_0_82, List.forall_mem_cons.2 ⟨subd10_0_83, List.forall_mem_cons.2 ⟨subd10_0_84, List.forall_mem_cons.2 ⟨subd10_0_85, List.forall_mem_cons.2 ⟨subd10_0_86, List.forall_mem_cons.2 ⟨subd10_0_87, List.forall_mem_cons.2 ⟨subd10_0_88, List.forall_mem_cons.2 ⟨subd10_0_89, List.forall_mem_cons.2 ⟨subd10_0_90, List.forall_mem_cons.2 ⟨subd10_0_91, List.forall_mem_cons.2 ⟨subd10_0_92, List.forall_mem_cons.2 ⟨subd10_0_93, List.forall_mem_cons.2 ⟨subd10_0_94, List.forall_mem_cons.2 ⟨subd10_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_96 : subd10_0 [3, 4] = true := by decide +kernel
theorem subd10_0_97 : subd10_0 [4, -4] = true := by decide +kernel
theorem subd10_0_98 : subd10_0 [4, -3] = true := by decide +kernel
theorem subd10_0_99 : subd10_0 [4, -2] = true := by decide +kernel
theorem subd10_0_100 : subd10_0 [4, -1] = true := by decide +kernel
theorem subd10_0_101 : subd10_0 [4, 0] = true := by decide +kernel
theorem subd10_0_102 : subd10_0 [4, 1] = true := by decide +kernel
theorem subd10_0_103 : subd10_0 [4, 2] = true := by decide +kernel
theorem subd10_0_104 : subd10_0 [4, 3] = true := by decide +kernel
theorem subd10_0_105 : subd10_0 [4, 4] = true := by decide +kernel
theorem subd10_0_106 : subd10_0 [5, -3] = true := by decide +kernel
theorem subd10_0_107 : subd10_0 [5, -2] = true := by decide +kernel
theorem subd10_0_108 : subd10_0 [5, -1] = true := by decide +kernel
theorem subd10_0_109 : subd10_0 [5, 0] = true := by decide +kernel
theorem subd10_0_110 : subd10_0 [5, 1] = true := by decide +kernel
theorem subd10_0_111 : subd10_0 [5, 2] = true := by decide +kernel
theorem subd10_0_112 : subd10_0 [5, 3] = true := by decide +kernel
theorem subd10_0_113 : subd10_0 [6] = true := by decide +kernel
theorem sbd10_0_3 : ∀ q ∈ blkd10_0_3, subd10_0 q = true := by
  unfold blkd10_0_3
  exact List.forall_mem_cons.2 ⟨subd10_0_96, List.forall_mem_cons.2 ⟨subd10_0_97, List.forall_mem_cons.2 ⟨subd10_0_98, List.forall_mem_cons.2 ⟨subd10_0_99, List.forall_mem_cons.2 ⟨subd10_0_100, List.forall_mem_cons.2 ⟨subd10_0_101, List.forall_mem_cons.2 ⟨subd10_0_102, List.forall_mem_cons.2 ⟨subd10_0_103, List.forall_mem_cons.2 ⟨subd10_0_104, List.forall_mem_cons.2 ⟨subd10_0_105, List.forall_mem_cons.2 ⟨subd10_0_106, List.forall_mem_cons.2 ⟨subd10_0_107, List.forall_mem_cons.2 ⟨subd10_0_108, List.forall_mem_cons.2 ⟨subd10_0_109, List.forall_mem_cons.2 ⟨subd10_0_110, List.forall_mem_cons.2 ⟨subd10_0_111, List.forall_mem_cons.2 ⟨subd10_0_112, List.forall_mem_cons.2 ⟨subd10_0_113, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-4] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-3] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-2, -3] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-2, -2] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-2, -1] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-2, 0] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-2, 1] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-2, 2] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-2, 3] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-1, -4] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-1, 0] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-1, 1] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [-1, 3] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [0, 0] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [1, -4] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [1, -1] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [1, 0] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [1, 1] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [1, 2] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_32 : subd10_1 [1, 3] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [2, -4] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [2, -3] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [2, -1] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [2, 0] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [2, 1] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [2, 2] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [3] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [4] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-3] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-2, -3] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-2, -2] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-2, -1] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-2, 0, -8] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-2, 0, -7] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-2, 0, -6] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-2, 0, -5] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [-2, 0, -4] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [-2, 0, -3] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [-2, 0, -2] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [-2, 0, -1] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [-2, 0, 0] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [-2, 0, 1] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [-2, 0, 2] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [-2, 0, 3] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [-2, 0, 4] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [-2, 0, 5] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [-2, 0, 6] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [-2, 0, 7] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [-2, 1, -8] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [-2, 1, -7] = true := by decide +kernel
theorem subd10_2_22 : subd10_2 [-2, 1, -6] = true := by decide +kernel
theorem subd10_2_23 : subd10_2 [-2, 1, -5] = true := by decide +kernel
theorem subd10_2_24 : subd10_2 [-2, 1, -4] = true := by decide +kernel
theorem subd10_2_25 : subd10_2 [-2, 1, -3] = true := by decide +kernel
theorem subd10_2_26 : subd10_2 [-2, 1, -2] = true := by decide +kernel
theorem subd10_2_27 : subd10_2 [-2, 1, -1] = true := by decide +kernel
theorem subd10_2_28 : subd10_2 [-2, 1, 0] = true := by decide +kernel
theorem subd10_2_29 : subd10_2 [-2, 1, 1] = true := by decide +kernel
theorem subd10_2_30 : subd10_2 [-2, 1, 2] = true := by decide +kernel
theorem subd10_2_31 : subd10_2 [-2, 1, 3] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_cons.2 ⟨subd10_2_22, List.forall_mem_cons.2 ⟨subd10_2_23, List.forall_mem_cons.2 ⟨subd10_2_24, List.forall_mem_cons.2 ⟨subd10_2_25, List.forall_mem_cons.2 ⟨subd10_2_26, List.forall_mem_cons.2 ⟨subd10_2_27, List.forall_mem_cons.2 ⟨subd10_2_28, List.forall_mem_cons.2 ⟨subd10_2_29, List.forall_mem_cons.2 ⟨subd10_2_30, List.forall_mem_cons.2 ⟨subd10_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_32 : subd10_2 [-2, 1, 4] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [-2, 1, 5] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [-2, 1, 6] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [-2, 1, 7] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [-2, 2] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [-1, -4] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [-1, -3] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [-1, -2, -7] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [-1, -2, -6] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [-1, -2, -5] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [-1, -2, -4] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [-1, -2, -3] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [-1, -2, -2] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [-1, -2, -1] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [-1, -2, 0] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [-1, -2, 1] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [-1, -2, 2] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [-1, -2, 3] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [-1, -2, 4] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [-1, -2, 5] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [-1, -2, 6] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [-1, -2, 7] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [-1, -1, -9] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [-1, -1, -8] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [-1, -1, -7] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [-1, -1, -6] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [-1, -1, -5] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [-1, -1, -4] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [-1, -1, -3] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [-1, -1, -2] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [-1, -1, -1] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [-1, -1, 0] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [-1, -1, 1] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [-1, -1, 2] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [-1, -1, 3] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [-1, -1, 4] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [-1, -1, 5] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [-1, -1, 6] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [-1, -1, 7] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [-1, -1, 8] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [-1, 0, -9] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [-1, 0, -8] = true := by decide +kernel
theorem subd10_2_74 : subd10_2 [-1, 0, -7] = true := by decide +kernel
theorem subd10_2_75 : subd10_2 [-1, 0, -6] = true := by decide +kernel
theorem subd10_2_76 : subd10_2 [-1, 0, -5] = true := by decide +kernel
theorem subd10_2_77 : subd10_2 [-1, 0, -4] = true := by decide +kernel
theorem subd10_2_78 : subd10_2 [-1, 0, -3] = true := by decide +kernel
theorem subd10_2_79 : subd10_2 [-1, 0, -2] = true := by decide +kernel
theorem subd10_2_80 : subd10_2 [-1, 0, -1] = true := by decide +kernel
theorem subd10_2_81 : subd10_2 [-1, 0, 0] = true := by decide +kernel
theorem subd10_2_82 : subd10_2 [-1, 0, 1] = true := by decide +kernel
theorem subd10_2_83 : subd10_2 [-1, 0, 2] = true := by decide +kernel
theorem subd10_2_84 : subd10_2 [-1, 0, 3] = true := by decide +kernel
theorem subd10_2_85 : subd10_2 [-1, 0, 4] = true := by decide +kernel
theorem subd10_2_86 : subd10_2 [-1, 0, 5] = true := by decide +kernel
theorem subd10_2_87 : subd10_2 [-1, 0, 6] = true := by decide +kernel
theorem subd10_2_88 : subd10_2 [-1, 0, 7] = true := by decide +kernel
theorem subd10_2_89 : subd10_2 [-1, 0, 8] = true := by decide +kernel
theorem subd10_2_90 : subd10_2 [-1, 0, 9] = true := by decide +kernel
theorem subd10_2_91 : subd10_2 [-1, 1, -9] = true := by decide +kernel
theorem subd10_2_92 : subd10_2 [-1, 1, -8] = true := by decide +kernel
theorem subd10_2_93 : subd10_2 [-1, 1, -7] = true := by decide +kernel
theorem subd10_2_94 : subd10_2 [-1, 1, -6] = true := by decide +kernel
theorem subd10_2_95 : subd10_2 [-1, 1, -5] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_cons.2 ⟨subd10_2_74, List.forall_mem_cons.2 ⟨subd10_2_75, List.forall_mem_cons.2 ⟨subd10_2_76, List.forall_mem_cons.2 ⟨subd10_2_77, List.forall_mem_cons.2 ⟨subd10_2_78, List.forall_mem_cons.2 ⟨subd10_2_79, List.forall_mem_cons.2 ⟨subd10_2_80, List.forall_mem_cons.2 ⟨subd10_2_81, List.forall_mem_cons.2 ⟨subd10_2_82, List.forall_mem_cons.2 ⟨subd10_2_83, List.forall_mem_cons.2 ⟨subd10_2_84, List.forall_mem_cons.2 ⟨subd10_2_85, List.forall_mem_cons.2 ⟨subd10_2_86, List.forall_mem_cons.2 ⟨subd10_2_87, List.forall_mem_cons.2 ⟨subd10_2_88, List.forall_mem_cons.2 ⟨subd10_2_89, List.forall_mem_cons.2 ⟨subd10_2_90, List.forall_mem_cons.2 ⟨subd10_2_91, List.forall_mem_cons.2 ⟨subd10_2_92, List.forall_mem_cons.2 ⟨subd10_2_93, List.forall_mem_cons.2 ⟨subd10_2_94, List.forall_mem_cons.2 ⟨subd10_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_96 : subd10_2 [-1, 1, -4] = true := by decide +kernel
theorem subd10_2_97 : subd10_2 [-1, 1, -3] = true := by decide +kernel
theorem subd10_2_98 : subd10_2 [-1, 1, -2] = true := by decide +kernel
theorem subd10_2_99 : subd10_2 [-1, 1, -1] = true := by decide +kernel
theorem subd10_2_100 : subd10_2 [-1, 1, 0] = true := by decide +kernel
theorem subd10_2_101 : subd10_2 [-1, 1, 1] = true := by decide +kernel
theorem subd10_2_102 : subd10_2 [-1, 1, 2] = true := by decide +kernel
theorem subd10_2_103 : subd10_2 [-1, 1, 3] = true := by decide +kernel
theorem subd10_2_104 : subd10_2 [-1, 1, 4] = true := by decide +kernel
theorem subd10_2_105 : subd10_2 [-1, 1, 5] = true := by decide +kernel
theorem subd10_2_106 : subd10_2 [-1, 1, 6] = true := by decide +kernel
theorem subd10_2_107 : subd10_2 [-1, 1, 7] = true := by decide +kernel
theorem subd10_2_108 : subd10_2 [-1, 1, 8] = true := by decide +kernel
theorem subd10_2_109 : subd10_2 [-1, 2, -8] = true := by decide +kernel
theorem subd10_2_110 : subd10_2 [-1, 2, -7] = true := by decide +kernel
theorem subd10_2_111 : subd10_2 [-1, 2, -6] = true := by decide +kernel
theorem subd10_2_112 : subd10_2 [-1, 2, -5] = true := by decide +kernel
theorem subd10_2_113 : subd10_2 [-1, 2, -4] = true := by decide +kernel
theorem subd10_2_114 : subd10_2 [-1, 2, -3] = true := by decide +kernel
theorem subd10_2_115 : subd10_2 [-1, 2, -2] = true := by decide +kernel
theorem subd10_2_116 : subd10_2 [-1, 2, -1] = true := by decide +kernel
theorem subd10_2_117 : subd10_2 [-1, 2, 0] = true := by decide +kernel
theorem subd10_2_118 : subd10_2 [-1, 2, 1] = true := by decide +kernel
theorem subd10_2_119 : subd10_2 [-1, 2, 2] = true := by decide +kernel
theorem subd10_2_120 : subd10_2 [-1, 2, 3] = true := by decide +kernel
theorem subd10_2_121 : subd10_2 [-1, 2, 4] = true := by decide +kernel
theorem subd10_2_122 : subd10_2 [-1, 2, 5] = true := by decide +kernel
theorem subd10_2_123 : subd10_2 [-1, 2, 6] = true := by decide +kernel
theorem subd10_2_124 : subd10_2 [-1, 2, 7] = true := by decide +kernel
theorem subd10_2_125 : subd10_2 [-1, 3] = true := by decide +kernel
theorem subd10_2_126 : subd10_2 [0, -4] = true := by decide +kernel
theorem subd10_2_127 : subd10_2 [0, -3] = true := by decide +kernel
theorem sbd10_2_3 : ∀ q ∈ blkd10_2_3, subd10_2 q = true := by
  unfold blkd10_2_3
  exact List.forall_mem_cons.2 ⟨subd10_2_96, List.forall_mem_cons.2 ⟨subd10_2_97, List.forall_mem_cons.2 ⟨subd10_2_98, List.forall_mem_cons.2 ⟨subd10_2_99, List.forall_mem_cons.2 ⟨subd10_2_100, List.forall_mem_cons.2 ⟨subd10_2_101, List.forall_mem_cons.2 ⟨subd10_2_102, List.forall_mem_cons.2 ⟨subd10_2_103, List.forall_mem_cons.2 ⟨subd10_2_104, List.forall_mem_cons.2 ⟨subd10_2_105, List.forall_mem_cons.2 ⟨subd10_2_106, List.forall_mem_cons.2 ⟨subd10_2_107, List.forall_mem_cons.2 ⟨subd10_2_108, List.forall_mem_cons.2 ⟨subd10_2_109, List.forall_mem_cons.2 ⟨subd10_2_110, List.forall_mem_cons.2 ⟨subd10_2_111, List.forall_mem_cons.2 ⟨subd10_2_112, List.forall_mem_cons.2 ⟨subd10_2_113, List.forall_mem_cons.2 ⟨subd10_2_114, List.forall_mem_cons.2 ⟨subd10_2_115, List.forall_mem_cons.2 ⟨subd10_2_116, List.forall_mem_cons.2 ⟨subd10_2_117, List.forall_mem_cons.2 ⟨subd10_2_118, List.forall_mem_cons.2 ⟨subd10_2_119, List.forall_mem_cons.2 ⟨subd10_2_120, List.forall_mem_cons.2 ⟨subd10_2_121, List.forall_mem_cons.2 ⟨subd10_2_122, List.forall_mem_cons.2 ⟨subd10_2_123, List.forall_mem_cons.2 ⟨subd10_2_124, List.forall_mem_cons.2 ⟨subd10_2_125, List.forall_mem_cons.2 ⟨subd10_2_126, List.forall_mem_cons.2 ⟨subd10_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
