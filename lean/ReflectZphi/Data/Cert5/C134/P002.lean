import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_5_64 : subd0_5 [0, 1, -1] = true := by decide +kernel
theorem subd0_5_65 : subd0_5 [0, 1, 0] = true := by decide +kernel
theorem subd0_5_66 : subd0_5 [0, 1, 1] = true := by decide +kernel
theorem subd0_5_67 : subd0_5 [0, 1, 2] = true := by decide +kernel
theorem subd0_5_68 : subd0_5 [0, 1, 3] = true := by decide +kernel
theorem subd0_5_69 : subd0_5 [0, 1, 4] = true := by decide +kernel
theorem subd0_5_70 : subd0_5 [0, 1, 5] = true := by decide +kernel
theorem subd0_5_71 : subd0_5 [0, 1, 6] = true := by decide +kernel
theorem subd0_5_72 : subd0_5 [0, 1, 7] = true := by decide +kernel
theorem subd0_5_73 : subd0_5 [1, -2] = true := by decide +kernel
theorem subd0_5_74 : subd0_5 [1, -1] = true := by decide +kernel
theorem subd0_5_75 : subd0_5 [1, 0, -9] = true := by decide +kernel
theorem subd0_5_76 : subd0_5 [1, 0, -8] = true := by decide +kernel
theorem subd0_5_77 : subd0_5 [1, 0, -7] = true := by decide +kernel
theorem subd0_5_78 : subd0_5 [1, 0, -6] = true := by decide +kernel
theorem subd0_5_79 : subd0_5 [1, 0, -5] = true := by decide +kernel
theorem subd0_5_80 : subd0_5 [1, 0, -4] = true := by decide +kernel
theorem subd0_5_81 : subd0_5 [1, 0, -3] = true := by decide +kernel
theorem subd0_5_82 : subd0_5 [1, 0, -2] = true := by decide +kernel
theorem subd0_5_83 : subd0_5 [1, 0, -1] = true := by decide +kernel
theorem subd0_5_84 : subd0_5 [1, 0, 0] = true := by decide +kernel
theorem subd0_5_85 : subd0_5 [1, 0, 1] = true := by decide +kernel
theorem subd0_5_86 : subd0_5 [1, 0, 2] = true := by decide +kernel
theorem subd0_5_87 : subd0_5 [1, 0, 3] = true := by decide +kernel
theorem subd0_5_88 : subd0_5 [1, 0, 4] = true := by decide +kernel
theorem subd0_5_89 : subd0_5 [1, 0, 5] = true := by decide +kernel
theorem subd0_5_90 : subd0_5 [1, 0, 6] = true := by decide +kernel
theorem subd0_5_91 : subd0_5 [1, 0, 7] = true := by decide +kernel
theorem subd0_5_92 : subd0_5 [1, 1] = true := by decide +kernel
theorem sbd0_5_2 : ∀ q ∈ blkd0_5_2, subd0_5 q = true := by
  unfold blkd0_5_2
  exact List.forall_mem_cons.2 ⟨subd0_5_64, List.forall_mem_cons.2 ⟨subd0_5_65, List.forall_mem_cons.2 ⟨subd0_5_66, List.forall_mem_cons.2 ⟨subd0_5_67, List.forall_mem_cons.2 ⟨subd0_5_68, List.forall_mem_cons.2 ⟨subd0_5_69, List.forall_mem_cons.2 ⟨subd0_5_70, List.forall_mem_cons.2 ⟨subd0_5_71, List.forall_mem_cons.2 ⟨subd0_5_72, List.forall_mem_cons.2 ⟨subd0_5_73, List.forall_mem_cons.2 ⟨subd0_5_74, List.forall_mem_cons.2 ⟨subd0_5_75, List.forall_mem_cons.2 ⟨subd0_5_76, List.forall_mem_cons.2 ⟨subd0_5_77, List.forall_mem_cons.2 ⟨subd0_5_78, List.forall_mem_cons.2 ⟨subd0_5_79, List.forall_mem_cons.2 ⟨subd0_5_80, List.forall_mem_cons.2 ⟨subd0_5_81, List.forall_mem_cons.2 ⟨subd0_5_82, List.forall_mem_cons.2 ⟨subd0_5_83, List.forall_mem_cons.2 ⟨subd0_5_84, List.forall_mem_cons.2 ⟨subd0_5_85, List.forall_mem_cons.2 ⟨subd0_5_86, List.forall_mem_cons.2 ⟨subd0_5_87, List.forall_mem_cons.2 ⟨subd0_5_88, List.forall_mem_cons.2 ⟨subd0_5_89, List.forall_mem_cons.2 ⟨subd0_5_90, List.forall_mem_cons.2 ⟨subd0_5_91, List.forall_mem_cons.2 ⟨subd0_5_92, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_6 : ldCheck G d0_6.U d0_6.ms ldd0_6 = true := by decide +kernel
theorem pre_okd0_6 : subPre G cell0 d0_6 = true := by decide +kernel
theorem subd0_6_0 : subd0_6 [-3] = true := by decide +kernel
theorem subd0_6_1 : subd0_6 [-2, -4] = true := by decide +kernel
theorem subd0_6_2 : subd0_6 [-2, -3] = true := by decide +kernel
theorem subd0_6_3 : subd0_6 [-2, -2] = true := by decide +kernel
theorem subd0_6_4 : subd0_6 [-2, -1] = true := by decide +kernel
theorem subd0_6_5 : subd0_6 [-2, 0] = true := by decide +kernel
theorem subd0_6_6 : subd0_6 [-2, 1] = true := by decide +kernel
theorem subd0_6_7 : subd0_6 [-1, -4] = true := by decide +kernel
theorem subd0_6_8 : subd0_6 [-1, -3] = true := by decide +kernel
theorem subd0_6_9 : subd0_6 [-1, -2] = true := by decide +kernel
theorem subd0_6_10 : subd0_6 [-1, -1] = true := by decide +kernel
theorem subd0_6_11 : subd0_6 [-1, 0] = true := by decide +kernel
theorem subd0_6_12 : subd0_6 [-1, 1] = true := by decide +kernel
theorem subd0_6_13 : subd0_6 [-1, 2] = true := by decide +kernel
theorem subd0_6_14 : subd0_6 [0, -4] = true := by decide +kernel
theorem subd0_6_15 : subd0_6 [0, -3] = true := by decide +kernel
theorem subd0_6_16 : subd0_6 [0, -2] = true := by decide +kernel
theorem subd0_6_17 : subd0_6 [0, -1] = true := by decide +kernel
theorem subd0_6_18 : subd0_6 [0, 0] = true := by decide +kernel
theorem subd0_6_19 : subd0_6 [0, 1] = true := by decide +kernel
theorem subd0_6_20 : subd0_6 [0, 2] = true := by decide +kernel
theorem subd0_6_21 : subd0_6 [0, 3] = true := by decide +kernel
theorem subd0_6_22 : subd0_6 [1, -3] = true := by decide +kernel
theorem subd0_6_23 : subd0_6 [1, -2] = true := by decide +kernel
theorem subd0_6_24 : subd0_6 [1, -1] = true := by decide +kernel
theorem subd0_6_25 : subd0_6 [1, 0] = true := by decide +kernel
theorem subd0_6_26 : subd0_6 [1, 1] = true := by decide +kernel
theorem subd0_6_27 : subd0_6 [1, 2] = true := by decide +kernel
theorem subd0_6_28 : subd0_6 [1, 3] = true := by decide +kernel
theorem subd0_6_29 : subd0_6 [2, -2] = true := by decide +kernel
theorem subd0_6_30 : subd0_6 [2, -1] = true := by decide +kernel
theorem subd0_6_31 : subd0_6 [2, 0] = true := by decide +kernel
theorem sbd0_6_0 : ∀ q ∈ blkd0_6_0, subd0_6 q = true := by
  unfold blkd0_6_0
  exact List.forall_mem_cons.2 ⟨subd0_6_0, List.forall_mem_cons.2 ⟨subd0_6_1, List.forall_mem_cons.2 ⟨subd0_6_2, List.forall_mem_cons.2 ⟨subd0_6_3, List.forall_mem_cons.2 ⟨subd0_6_4, List.forall_mem_cons.2 ⟨subd0_6_5, List.forall_mem_cons.2 ⟨subd0_6_6, List.forall_mem_cons.2 ⟨subd0_6_7, List.forall_mem_cons.2 ⟨subd0_6_8, List.forall_mem_cons.2 ⟨subd0_6_9, List.forall_mem_cons.2 ⟨subd0_6_10, List.forall_mem_cons.2 ⟨subd0_6_11, List.forall_mem_cons.2 ⟨subd0_6_12, List.forall_mem_cons.2 ⟨subd0_6_13, List.forall_mem_cons.2 ⟨subd0_6_14, List.forall_mem_cons.2 ⟨subd0_6_15, List.forall_mem_cons.2 ⟨subd0_6_16, List.forall_mem_cons.2 ⟨subd0_6_17, List.forall_mem_cons.2 ⟨subd0_6_18, List.forall_mem_cons.2 ⟨subd0_6_19, List.forall_mem_cons.2 ⟨subd0_6_20, List.forall_mem_cons.2 ⟨subd0_6_21, List.forall_mem_cons.2 ⟨subd0_6_22, List.forall_mem_cons.2 ⟨subd0_6_23, List.forall_mem_cons.2 ⟨subd0_6_24, List.forall_mem_cons.2 ⟨subd0_6_25, List.forall_mem_cons.2 ⟨subd0_6_26, List.forall_mem_cons.2 ⟨subd0_6_27, List.forall_mem_cons.2 ⟨subd0_6_28, List.forall_mem_cons.2 ⟨subd0_6_29, List.forall_mem_cons.2 ⟨subd0_6_30, List.forall_mem_cons.2 ⟨subd0_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_6_32 : subd0_6 [2, 1] = true := by decide +kernel
theorem subd0_6_33 : subd0_6 [2, 2] = true := by decide +kernel
theorem subd0_6_34 : subd0_6 [2, 3] = true := by decide +kernel
theorem subd0_6_35 : subd0_6 [3] = true := by decide +kernel
theorem sbd0_6_1 : ∀ q ∈ blkd0_6_1, subd0_6 q = true := by
  unfold blkd0_6_1
  exact List.forall_mem_cons.2 ⟨subd0_6_32, List.forall_mem_cons.2 ⟨subd0_6_33, List.forall_mem_cons.2 ⟨subd0_6_34, List.forall_mem_cons.2 ⟨subd0_6_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd0_7 : ldCheck G d0_7.U d0_7.ms ldd0_7 = true := by decide +kernel
theorem pre_okd0_7 : subPre G cell0 d0_7 = true := by decide +kernel
theorem subd0_7_0 : subd0_7 [-4] = true := by decide +kernel
theorem subd0_7_1 : subd0_7 [-3, -3] = true := by decide +kernel
theorem subd0_7_2 : subd0_7 [-3, -2] = true := by decide +kernel
theorem subd0_7_3 : subd0_7 [-3, -1] = true := by decide +kernel
theorem subd0_7_4 : subd0_7 [-3, 0] = true := by decide +kernel
theorem subd0_7_5 : subd0_7 [-3, 1] = true := by decide +kernel
theorem subd0_7_6 : subd0_7 [-3, 2] = true := by decide +kernel
theorem subd0_7_7 : subd0_7 [-3, 3] = true := by decide +kernel
theorem subd0_7_8 : subd0_7 [-2, -4] = true := by decide +kernel
theorem subd0_7_9 : subd0_7 [-2, -3] = true := by decide +kernel
theorem subd0_7_10 : subd0_7 [-2, -2] = true := by decide +kernel
theorem subd0_7_11 : subd0_7 [-2, -1] = true := by decide +kernel
theorem subd0_7_12 : subd0_7 [-2, 0] = true := by decide +kernel
theorem subd0_7_13 : subd0_7 [-2, 1] = true := by decide +kernel
theorem subd0_7_14 : subd0_7 [-2, 2] = true := by decide +kernel
theorem subd0_7_15 : subd0_7 [-2, 3] = true := by decide +kernel
theorem subd0_7_16 : subd0_7 [-1, -4] = true := by decide +kernel
theorem subd0_7_17 : subd0_7 [-1, -3] = true := by decide +kernel
theorem subd0_7_18 : subd0_7 [-1, -2] = true := by decide +kernel
theorem subd0_7_19 : subd0_7 [-1, -1] = true := by decide +kernel
theorem subd0_7_20 : subd0_7 [-1, 0] = true := by decide +kernel
theorem subd0_7_21 : subd0_7 [-1, 1] = true := by decide +kernel
theorem subd0_7_22 : subd0_7 [-1, 2] = true := by decide +kernel
theorem subd0_7_23 : subd0_7 [-1, 3] = true := by decide +kernel
theorem subd0_7_24 : subd0_7 [-1, 4] = true := by decide +kernel
theorem subd0_7_25 : subd0_7 [0, -5] = true := by decide +kernel
theorem subd0_7_26 : subd0_7 [0, -4] = true := by decide +kernel
theorem subd0_7_27 : subd0_7 [0, -3] = true := by decide +kernel
theorem subd0_7_28 : subd0_7 [0, -2] = true := by decide +kernel
theorem subd0_7_29 : subd0_7 [0, -1] = true := by decide +kernel
theorem subd0_7_30 : subd0_7 [0, 0] = true := by decide +kernel
theorem subd0_7_31 : subd0_7 [0, 1] = true := by decide +kernel
theorem sbd0_7_0 : ∀ q ∈ blkd0_7_0, subd0_7 q = true := by
  unfold blkd0_7_0
  exact List.forall_mem_cons.2 ⟨subd0_7_0, List.forall_mem_cons.2 ⟨subd0_7_1, List.forall_mem_cons.2 ⟨subd0_7_2, List.forall_mem_cons.2 ⟨subd0_7_3, List.forall_mem_cons.2 ⟨subd0_7_4, List.forall_mem_cons.2 ⟨subd0_7_5, List.forall_mem_cons.2 ⟨subd0_7_6, List.forall_mem_cons.2 ⟨subd0_7_7, List.forall_mem_cons.2 ⟨subd0_7_8, List.forall_mem_cons.2 ⟨subd0_7_9, List.forall_mem_cons.2 ⟨subd0_7_10, List.forall_mem_cons.2 ⟨subd0_7_11, List.forall_mem_cons.2 ⟨subd0_7_12, List.forall_mem_cons.2 ⟨subd0_7_13, List.forall_mem_cons.2 ⟨subd0_7_14, List.forall_mem_cons.2 ⟨subd0_7_15, List.forall_mem_cons.2 ⟨subd0_7_16, List.forall_mem_cons.2 ⟨subd0_7_17, List.forall_mem_cons.2 ⟨subd0_7_18, List.forall_mem_cons.2 ⟨subd0_7_19, List.forall_mem_cons.2 ⟨subd0_7_20, List.forall_mem_cons.2 ⟨subd0_7_21, List.forall_mem_cons.2 ⟨subd0_7_22, List.forall_mem_cons.2 ⟨subd0_7_23, List.forall_mem_cons.2 ⟨subd0_7_24, List.forall_mem_cons.2 ⟨subd0_7_25, List.forall_mem_cons.2 ⟨subd0_7_26, List.forall_mem_cons.2 ⟨subd0_7_27, List.forall_mem_cons.2 ⟨subd0_7_28, List.forall_mem_cons.2 ⟨subd0_7_29, List.forall_mem_cons.2 ⟨subd0_7_30, List.forall_mem_cons.2 ⟨subd0_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_7_32 : subd0_7 [0, 2] = true := by decide +kernel
theorem subd0_7_33 : subd0_7 [0, 3] = true := by decide +kernel
theorem subd0_7_34 : subd0_7 [0, 4] = true := by decide +kernel
theorem subd0_7_35 : subd0_7 [1, -5] = true := by decide +kernel
theorem subd0_7_36 : subd0_7 [1, -4] = true := by decide +kernel
theorem subd0_7_37 : subd0_7 [1, -3] = true := by decide +kernel
theorem subd0_7_38 : subd0_7 [1, -2] = true := by decide +kernel
theorem subd0_7_39 : subd0_7 [1, -1] = true := by decide +kernel
theorem subd0_7_40 : subd0_7 [1, 0] = true := by decide +kernel
theorem subd0_7_41 : subd0_7 [1, 1] = true := by decide +kernel
theorem subd0_7_42 : subd0_7 [1, 2] = true := by decide +kernel
theorem subd0_7_43 : subd0_7 [1, 3] = true := by decide +kernel
theorem subd0_7_44 : subd0_7 [2, -4] = true := by decide +kernel
theorem subd0_7_45 : subd0_7 [2, -3] = true := by decide +kernel
theorem subd0_7_46 : subd0_7 [2, -2] = true := by decide +kernel
theorem subd0_7_47 : subd0_7 [2, -1] = true := by decide +kernel
theorem subd0_7_48 : subd0_7 [2, 0] = true := by decide +kernel
theorem subd0_7_49 : subd0_7 [2, 1] = true := by decide +kernel
theorem subd0_7_50 : subd0_7 [2, 2] = true := by decide +kernel
theorem subd0_7_51 : subd0_7 [2, 3] = true := by decide +kernel
theorem subd0_7_52 : subd0_7 [3, -4] = true := by decide +kernel
theorem subd0_7_53 : subd0_7 [3, -3] = true := by decide +kernel
theorem subd0_7_54 : subd0_7 [3, -2] = true := by decide +kernel
theorem subd0_7_55 : subd0_7 [3, -1] = true := by decide +kernel
theorem subd0_7_56 : subd0_7 [3, 0] = true := by decide +kernel
theorem subd0_7_57 : subd0_7 [3, 1] = true := by decide +kernel
theorem subd0_7_58 : subd0_7 [3, 2] = true := by decide +kernel
theorem subd0_7_59 : subd0_7 [4] = true := by decide +kernel
theorem sbd0_7_1 : ∀ q ∈ blkd0_7_1, subd0_7 q = true := by
  unfold blkd0_7_1
  exact List.forall_mem_cons.2 ⟨subd0_7_32, List.forall_mem_cons.2 ⟨subd0_7_33, List.forall_mem_cons.2 ⟨subd0_7_34, List.forall_mem_cons.2 ⟨subd0_7_35, List.forall_mem_cons.2 ⟨subd0_7_36, List.forall_mem_cons.2 ⟨subd0_7_37, List.forall_mem_cons.2 ⟨subd0_7_38, List.forall_mem_cons.2 ⟨subd0_7_39, List.forall_mem_cons.2 ⟨subd0_7_40, List.forall_mem_cons.2 ⟨subd0_7_41, List.forall_mem_cons.2 ⟨subd0_7_42, List.forall_mem_cons.2 ⟨subd0_7_43, List.forall_mem_cons.2 ⟨subd0_7_44, List.forall_mem_cons.2 ⟨subd0_7_45, List.forall_mem_cons.2 ⟨subd0_7_46, List.forall_mem_cons.2 ⟨subd0_7_47, List.forall_mem_cons.2 ⟨subd0_7_48, List.forall_mem_cons.2 ⟨subd0_7_49, List.forall_mem_cons.2 ⟨subd0_7_50, List.forall_mem_cons.2 ⟨subd0_7_51, List.forall_mem_cons.2 ⟨subd0_7_52, List.forall_mem_cons.2 ⟨subd0_7_53, List.forall_mem_cons.2 ⟨subd0_7_54, List.forall_mem_cons.2 ⟨subd0_7_55, List.forall_mem_cons.2 ⟨subd0_7_56, List.forall_mem_cons.2 ⟨subd0_7_57, List.forall_mem_cons.2 ⟨subd0_7_58, List.forall_mem_cons.2 ⟨subd0_7_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
