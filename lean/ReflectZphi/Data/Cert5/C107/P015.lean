import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_6_64 : subd7_6 [1, -3] = true := by decide +kernel
theorem subd7_6_65 : subd7_6 [1, -2] = true := by decide +kernel
theorem subd7_6_66 : subd7_6 [1, -1] = true := by decide +kernel
theorem subd7_6_67 : subd7_6 [1, 0] = true := by decide +kernel
theorem subd7_6_68 : subd7_6 [1, 1] = true := by decide +kernel
theorem subd7_6_69 : subd7_6 [1, 2] = true := by decide +kernel
theorem subd7_6_70 : subd7_6 [1, 3] = true := by decide +kernel
theorem subd7_6_71 : subd7_6 [1, 4] = true := by decide +kernel
theorem subd7_6_72 : subd7_6 [1, 5] = true := by decide +kernel
theorem subd7_6_73 : subd7_6 [1, 6] = true := by decide +kernel
theorem subd7_6_74 : subd7_6 [2, -5] = true := by decide +kernel
theorem subd7_6_75 : subd7_6 [2, -4] = true := by decide +kernel
theorem subd7_6_76 : subd7_6 [2, -3] = true := by decide +kernel
theorem subd7_6_77 : subd7_6 [2, -2] = true := by decide +kernel
theorem subd7_6_78 : subd7_6 [2, -1] = true := by decide +kernel
theorem subd7_6_79 : subd7_6 [2, 0] = true := by decide +kernel
theorem subd7_6_80 : subd7_6 [2, 1] = true := by decide +kernel
theorem subd7_6_81 : subd7_6 [2, 2] = true := by decide +kernel
theorem subd7_6_82 : subd7_6 [2, 3] = true := by decide +kernel
theorem subd7_6_83 : subd7_6 [2, 4] = true := by decide +kernel
theorem subd7_6_84 : subd7_6 [2, 5] = true := by decide +kernel
theorem subd7_6_85 : subd7_6 [2, 6] = true := by decide +kernel
theorem subd7_6_86 : subd7_6 [3, -4] = true := by decide +kernel
theorem subd7_6_87 : subd7_6 [3, -3] = true := by decide +kernel
theorem subd7_6_88 : subd7_6 [3, -2] = true := by decide +kernel
theorem subd7_6_89 : subd7_6 [3, -1] = true := by decide +kernel
theorem subd7_6_90 : subd7_6 [3, 0] = true := by decide +kernel
theorem subd7_6_91 : subd7_6 [3, 1] = true := by decide +kernel
theorem subd7_6_92 : subd7_6 [3, 2] = true := by decide +kernel
theorem subd7_6_93 : subd7_6 [3, 3] = true := by decide +kernel
theorem subd7_6_94 : subd7_6 [3, 4] = true := by decide +kernel
theorem subd7_6_95 : subd7_6 [3, 5] = true := by decide +kernel
theorem sbd7_6_2 : ∀ q ∈ blkd7_6_2, subd7_6 q = true := by
  unfold blkd7_6_2
  exact List.forall_mem_cons.2 ⟨subd7_6_64, List.forall_mem_cons.2 ⟨subd7_6_65, List.forall_mem_cons.2 ⟨subd7_6_66, List.forall_mem_cons.2 ⟨subd7_6_67, List.forall_mem_cons.2 ⟨subd7_6_68, List.forall_mem_cons.2 ⟨subd7_6_69, List.forall_mem_cons.2 ⟨subd7_6_70, List.forall_mem_cons.2 ⟨subd7_6_71, List.forall_mem_cons.2 ⟨subd7_6_72, List.forall_mem_cons.2 ⟨subd7_6_73, List.forall_mem_cons.2 ⟨subd7_6_74, List.forall_mem_cons.2 ⟨subd7_6_75, List.forall_mem_cons.2 ⟨subd7_6_76, List.forall_mem_cons.2 ⟨subd7_6_77, List.forall_mem_cons.2 ⟨subd7_6_78, List.forall_mem_cons.2 ⟨subd7_6_79, List.forall_mem_cons.2 ⟨subd7_6_80, List.forall_mem_cons.2 ⟨subd7_6_81, List.forall_mem_cons.2 ⟨subd7_6_82, List.forall_mem_cons.2 ⟨subd7_6_83, List.forall_mem_cons.2 ⟨subd7_6_84, List.forall_mem_cons.2 ⟨subd7_6_85, List.forall_mem_cons.2 ⟨subd7_6_86, List.forall_mem_cons.2 ⟨subd7_6_87, List.forall_mem_cons.2 ⟨subd7_6_88, List.forall_mem_cons.2 ⟨subd7_6_89, List.forall_mem_cons.2 ⟨subd7_6_90, List.forall_mem_cons.2 ⟨subd7_6_91, List.forall_mem_cons.2 ⟨subd7_6_92, List.forall_mem_cons.2 ⟨subd7_6_93, List.forall_mem_cons.2 ⟨subd7_6_94, List.forall_mem_cons.2 ⟨subd7_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_96 : subd7_6 [3, 6] = true := by decide +kernel
theorem subd7_6_97 : subd7_6 [4, -3] = true := by decide +kernel
theorem subd7_6_98 : subd7_6 [4, -2] = true := by decide +kernel
theorem subd7_6_99 : subd7_6 [4, -1] = true := by decide +kernel
theorem subd7_6_100 : subd7_6 [4, 0] = true := by decide +kernel
theorem subd7_6_101 : subd7_6 [4, 1] = true := by decide +kernel
theorem subd7_6_102 : subd7_6 [4, 2] = true := by decide +kernel
theorem subd7_6_103 : subd7_6 [4, 3] = true := by decide +kernel
theorem subd7_6_104 : subd7_6 [4, 4] = true := by decide +kernel
theorem subd7_6_105 : subd7_6 [4, 5] = true := by decide +kernel
theorem subd7_6_106 : subd7_6 [4, 6] = true := by decide +kernel
theorem subd7_6_107 : subd7_6 [5] = true := by decide +kernel
theorem sbd7_6_3 : ∀ q ∈ blkd7_6_3, subd7_6 q = true := by
  unfold blkd7_6_3
  exact List.forall_mem_cons.2 ⟨subd7_6_96, List.forall_mem_cons.2 ⟨subd7_6_97, List.forall_mem_cons.2 ⟨subd7_6_98, List.forall_mem_cons.2 ⟨subd7_6_99, List.forall_mem_cons.2 ⟨subd7_6_100, List.forall_mem_cons.2 ⟨subd7_6_101, List.forall_mem_cons.2 ⟨subd7_6_102, List.forall_mem_cons.2 ⟨subd7_6_103, List.forall_mem_cons.2 ⟨subd7_6_104, List.forall_mem_cons.2 ⟨subd7_6_105, List.forall_mem_cons.2 ⟨subd7_6_106, List.forall_mem_cons.2 ⟨subd7_6_107, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel
theorem subd7_7_0 : subd7_7 [-2, -2] = true := by decide +kernel
theorem subd7_7_1 : subd7_7 [-2, -1] = true := by decide +kernel
theorem subd7_7_2 : subd7_7 [-2, 0] = true := by decide +kernel
theorem subd7_7_3 : subd7_7 [-2, 1] = true := by decide +kernel
theorem subd7_7_4 : subd7_7 [-2, 2] = true := by decide +kernel
theorem subd7_7_5 : subd7_7 [-1, -3] = true := by decide +kernel
theorem subd7_7_6 : subd7_7 [-1, -2] = true := by decide +kernel
theorem subd7_7_7 : subd7_7 [-1, -1] = true := by decide +kernel
theorem subd7_7_8 : subd7_7 [-1, 0] = true := by decide +kernel
theorem subd7_7_9 : subd7_7 [-1, 1] = true := by decide +kernel
theorem subd7_7_10 : subd7_7 [-1, 2] = true := by decide +kernel
theorem subd7_7_11 : subd7_7 [-1, 3] = true := by decide +kernel
theorem subd7_7_12 : subd7_7 [0, -4] = true := by decide +kernel
theorem subd7_7_13 : subd7_7 [0, -3] = true := by decide +kernel
theorem subd7_7_14 : subd7_7 [0, -2] = true := by decide +kernel
theorem subd7_7_15 : subd7_7 [0, -1] = true := by decide +kernel
theorem subd7_7_16 : subd7_7 [0, 0] = true := by decide +kernel
theorem subd7_7_17 : subd7_7 [0, 1] = true := by decide +kernel
theorem subd7_7_18 : subd7_7 [0, 2] = true := by decide +kernel
theorem subd7_7_19 : subd7_7 [0, 3] = true := by decide +kernel
theorem subd7_7_20 : subd7_7 [1, -4] = true := by decide +kernel
theorem subd7_7_21 : subd7_7 [1, -3] = true := by decide +kernel
theorem subd7_7_22 : subd7_7 [1, -2] = true := by decide +kernel
theorem subd7_7_23 : subd7_7 [1, -1] = true := by decide +kernel
theorem subd7_7_24 : subd7_7 [1, 0] = true := by decide +kernel
theorem subd7_7_25 : subd7_7 [1, 1] = true := by decide +kernel
theorem subd7_7_26 : subd7_7 [1, 2] = true := by decide +kernel
theorem subd7_7_27 : subd7_7 [2, -3] = true := by decide +kernel
theorem subd7_7_28 : subd7_7 [2, -2] = true := by decide +kernel
theorem subd7_7_29 : subd7_7 [2, -1] = true := by decide +kernel
theorem subd7_7_30 : subd7_7 [2, 0] = true := by decide +kernel
theorem subd7_7_31 : subd7_7 [2, 1] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_cons.2 ⟨subd7_7_1, List.forall_mem_cons.2 ⟨subd7_7_2, List.forall_mem_cons.2 ⟨subd7_7_3, List.forall_mem_cons.2 ⟨subd7_7_4, List.forall_mem_cons.2 ⟨subd7_7_5, List.forall_mem_cons.2 ⟨subd7_7_6, List.forall_mem_cons.2 ⟨subd7_7_7, List.forall_mem_cons.2 ⟨subd7_7_8, List.forall_mem_cons.2 ⟨subd7_7_9, List.forall_mem_cons.2 ⟨subd7_7_10, List.forall_mem_cons.2 ⟨subd7_7_11, List.forall_mem_cons.2 ⟨subd7_7_12, List.forall_mem_cons.2 ⟨subd7_7_13, List.forall_mem_cons.2 ⟨subd7_7_14, List.forall_mem_cons.2 ⟨subd7_7_15, List.forall_mem_cons.2 ⟨subd7_7_16, List.forall_mem_cons.2 ⟨subd7_7_17, List.forall_mem_cons.2 ⟨subd7_7_18, List.forall_mem_cons.2 ⟨subd7_7_19, List.forall_mem_cons.2 ⟨subd7_7_20, List.forall_mem_cons.2 ⟨subd7_7_21, List.forall_mem_cons.2 ⟨subd7_7_22, List.forall_mem_cons.2 ⟨subd7_7_23, List.forall_mem_cons.2 ⟨subd7_7_24, List.forall_mem_cons.2 ⟨subd7_7_25, List.forall_mem_cons.2 ⟨subd7_7_26, List.forall_mem_cons.2 ⟨subd7_7_27, List.forall_mem_cons.2 ⟨subd7_7_28, List.forall_mem_cons.2 ⟨subd7_7_29, List.forall_mem_cons.2 ⟨subd7_7_30, List.forall_mem_cons.2 ⟨subd7_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-2, -2] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-2, -1] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-2, 0] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-2, 1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-2, 2] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_22 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_23 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_24 : subd8_0 [2, -3] = true := by decide +kernel
theorem subd8_0_25 : subd8_0 [2, -2] = true := by decide +kernel
theorem subd8_0_26 : subd8_0 [2, -1] = true := by decide +kernel
theorem subd8_0_27 : subd8_0 [2, 0] = true := by decide +kernel
theorem subd8_0_28 : subd8_0 [2, 1] = true := by decide +kernel
theorem subd8_0_29 : subd8_0 [3] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_cons.2 ⟨subd8_0_22, List.forall_mem_cons.2 ⟨subd8_0_23, List.forall_mem_cons.2 ⟨subd8_0_24, List.forall_mem_cons.2 ⟨subd8_0_25, List.forall_mem_cons.2 ⟨subd8_0_26, List.forall_mem_cons.2 ⟨subd8_0_27, List.forall_mem_cons.2 ⟨subd8_0_28, List.forall_mem_cons.2 ⟨subd8_0_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
