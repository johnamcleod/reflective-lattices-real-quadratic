import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_64 : subd8_3 [2, -5] = true := by decide +kernel
theorem subd8_3_65 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_66 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_67 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_68 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_69 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_70 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_71 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_72 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_73 : subd8_3 [2, 4] = true := by decide +kernel
theorem subd8_3_74 : subd8_3 [2, 5] = true := by decide +kernel
theorem subd8_3_75 : subd8_3 [3, -4] = true := by decide +kernel
theorem subd8_3_76 : subd8_3 [3, -3] = true := by decide +kernel
theorem subd8_3_77 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_78 : subd8_3 [3, -1] = true := by decide +kernel
theorem subd8_3_79 : subd8_3 [3, 0] = true := by decide +kernel
theorem subd8_3_80 : subd8_3 [3, 1] = true := by decide +kernel
theorem subd8_3_81 : subd8_3 [3, 2] = true := by decide +kernel
theorem subd8_3_82 : subd8_3 [3, 3] = true := by decide +kernel
theorem subd8_3_83 : subd8_3 [3, 4] = true := by decide +kernel
theorem subd8_3_84 : subd8_3 [3, 5] = true := by decide +kernel
theorem subd8_3_85 : subd8_3 [4, -2] = true := by decide +kernel
theorem subd8_3_86 : subd8_3 [4, -1] = true := by decide +kernel
theorem subd8_3_87 : subd8_3 [4, 0] = true := by decide +kernel
theorem subd8_3_88 : subd8_3 [4, 1] = true := by decide +kernel
theorem subd8_3_89 : subd8_3 [4, 2] = true := by decide +kernel
theorem subd8_3_90 : subd8_3 [4, 3] = true := by decide +kernel
theorem subd8_3_91 : subd8_3 [4, 4] = true := by decide +kernel
theorem subd8_3_92 : subd8_3 [4, 5] = true := by decide +kernel
theorem subd8_3_93 : subd8_3 [5] = true := by decide +kernel
theorem sbd8_3_2 : ∀ q ∈ blkd8_3_2, subd8_3 q = true := by
  unfold blkd8_3_2
  exact List.forall_mem_cons.2 ⟨subd8_3_64, List.forall_mem_cons.2 ⟨subd8_3_65, List.forall_mem_cons.2 ⟨subd8_3_66, List.forall_mem_cons.2 ⟨subd8_3_67, List.forall_mem_cons.2 ⟨subd8_3_68, List.forall_mem_cons.2 ⟨subd8_3_69, List.forall_mem_cons.2 ⟨subd8_3_70, List.forall_mem_cons.2 ⟨subd8_3_71, List.forall_mem_cons.2 ⟨subd8_3_72, List.forall_mem_cons.2 ⟨subd8_3_73, List.forall_mem_cons.2 ⟨subd8_3_74, List.forall_mem_cons.2 ⟨subd8_3_75, List.forall_mem_cons.2 ⟨subd8_3_76, List.forall_mem_cons.2 ⟨subd8_3_77, List.forall_mem_cons.2 ⟨subd8_3_78, List.forall_mem_cons.2 ⟨subd8_3_79, List.forall_mem_cons.2 ⟨subd8_3_80, List.forall_mem_cons.2 ⟨subd8_3_81, List.forall_mem_cons.2 ⟨subd8_3_82, List.forall_mem_cons.2 ⟨subd8_3_83, List.forall_mem_cons.2 ⟨subd8_3_84, List.forall_mem_cons.2 ⟨subd8_3_85, List.forall_mem_cons.2 ⟨subd8_3_86, List.forall_mem_cons.2 ⟨subd8_3_87, List.forall_mem_cons.2 ⟨subd8_3_88, List.forall_mem_cons.2 ⟨subd8_3_89, List.forall_mem_cons.2 ⟨subd8_3_90, List.forall_mem_cons.2 ⟨subd8_3_91, List.forall_mem_cons.2 ⟨subd8_3_92, List.forall_mem_cons.2 ⟨subd8_3_93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-1] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [0] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [1] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-3] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-2, -3] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-2, -2] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-2, -1] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-2, 0] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-2, 1] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-2, 2] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-1, -4] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-1, -1] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-1, 0] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-1, 1] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-1, 3] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [0, -4] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_32 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [0, 3] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [1, -4] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [1, -1] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [1, 0] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [1, 1] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [1, 3] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [2, -3] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [2, -2] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [2, -1] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [2, 0] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [2, 1] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [2, 2] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [3] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C136
