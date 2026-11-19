import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-1] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [1] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [2] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-2, -3] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-2, -1] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-2, 0] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-2, 1] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [2, -2] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [2, -1] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [2, 0] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [2, 1] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [2, 2] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-3, -2] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-3, -1] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-3, 0] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-3, 1] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-2, -3] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-2, -2] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-2, -1] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-2, 0] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-2, 1] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-2, 2] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [-1, -4] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [-1, -1, -7] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [-1, -1, -6] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [-1, -1, -5] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [-1, -1, -4] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [-1, -1, -3] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [-1, -1, -2] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [-1, -1, -1] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [-1, -1, 0] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [-1, -1, 1] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [-1, -1, 2] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [-1, -1, 3] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [-1, -1, 4] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [-1, -1, 5] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [-1, -1, 6] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [-1, 0, -7] = true := by decide +kernel
theorem subd6_2_28 : subd6_2 [-1, 0, -6] = true := by decide +kernel
theorem subd6_2_29 : subd6_2 [-1, 0, -5] = true := by decide +kernel
theorem subd6_2_30 : subd6_2 [-1, 0, -4] = true := by decide +kernel
theorem subd6_2_31 : subd6_2 [-1, 0, -3] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_cons.2 ⟨subd6_2_28, List.forall_mem_cons.2 ⟨subd6_2_29, List.forall_mem_cons.2 ⟨subd6_2_30, List.forall_mem_cons.2 ⟨subd6_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_32 : subd6_2 [-1, 0, -2] = true := by decide +kernel
theorem subd6_2_33 : subd6_2 [-1, 0, -1] = true := by decide +kernel
theorem subd6_2_34 : subd6_2 [-1, 0, 0] = true := by decide +kernel
theorem subd6_2_35 : subd6_2 [-1, 0, 1] = true := by decide +kernel
theorem subd6_2_36 : subd6_2 [-1, 0, 2] = true := by decide +kernel
theorem subd6_2_37 : subd6_2 [-1, 0, 3] = true := by decide +kernel
theorem subd6_2_38 : subd6_2 [-1, 0, 4] = true := by decide +kernel
theorem subd6_2_39 : subd6_2 [-1, 0, 5] = true := by decide +kernel
theorem subd6_2_40 : subd6_2 [-1, 0, 6] = true := by decide +kernel
theorem subd6_2_41 : subd6_2 [-1, 1, -7] = true := by decide +kernel
theorem subd6_2_42 : subd6_2 [-1, 1, -6] = true := by decide +kernel
theorem subd6_2_43 : subd6_2 [-1, 1, -5] = true := by decide +kernel
theorem subd6_2_44 : subd6_2 [-1, 1, -4] = true := by decide +kernel
theorem subd6_2_45 : subd6_2 [-1, 1, -3] = true := by decide +kernel
theorem subd6_2_46 : subd6_2 [-1, 1, -2] = true := by decide +kernel
theorem subd6_2_47 : subd6_2 [-1, 1, -1] = true := by decide +kernel
theorem subd6_2_48 : subd6_2 [-1, 1, 0] = true := by decide +kernel
theorem subd6_2_49 : subd6_2 [-1, 1, 1] = true := by decide +kernel
theorem subd6_2_50 : subd6_2 [-1, 1, 2] = true := by decide +kernel
theorem subd6_2_51 : subd6_2 [-1, 1, 3] = true := by decide +kernel
theorem subd6_2_52 : subd6_2 [-1, 1, 4] = true := by decide +kernel
theorem subd6_2_53 : subd6_2 [-1, 1, 5] = true := by decide +kernel
theorem subd6_2_54 : subd6_2 [-1, 1, 6] = true := by decide +kernel
theorem subd6_2_55 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_56 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_57 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_58 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_59 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_60 : subd6_2 [0, -1, -7] = true := by decide +kernel
theorem subd6_2_61 : subd6_2 [0, -1, -6] = true := by decide +kernel
theorem subd6_2_62 : subd6_2 [0, -1, -5] = true := by decide +kernel
theorem subd6_2_63 : subd6_2 [0, -1, -4] = true := by decide +kernel
theorem sbd6_2_1 : ∀ q ∈ blkd6_2_1, subd6_2 q = true := by
  unfold blkd6_2_1
  exact List.forall_mem_cons.2 ⟨subd6_2_32, List.forall_mem_cons.2 ⟨subd6_2_33, List.forall_mem_cons.2 ⟨subd6_2_34, List.forall_mem_cons.2 ⟨subd6_2_35, List.forall_mem_cons.2 ⟨subd6_2_36, List.forall_mem_cons.2 ⟨subd6_2_37, List.forall_mem_cons.2 ⟨subd6_2_38, List.forall_mem_cons.2 ⟨subd6_2_39, List.forall_mem_cons.2 ⟨subd6_2_40, List.forall_mem_cons.2 ⟨subd6_2_41, List.forall_mem_cons.2 ⟨subd6_2_42, List.forall_mem_cons.2 ⟨subd6_2_43, List.forall_mem_cons.2 ⟨subd6_2_44, List.forall_mem_cons.2 ⟨subd6_2_45, List.forall_mem_cons.2 ⟨subd6_2_46, List.forall_mem_cons.2 ⟨subd6_2_47, List.forall_mem_cons.2 ⟨subd6_2_48, List.forall_mem_cons.2 ⟨subd6_2_49, List.forall_mem_cons.2 ⟨subd6_2_50, List.forall_mem_cons.2 ⟨subd6_2_51, List.forall_mem_cons.2 ⟨subd6_2_52, List.forall_mem_cons.2 ⟨subd6_2_53, List.forall_mem_cons.2 ⟨subd6_2_54, List.forall_mem_cons.2 ⟨subd6_2_55, List.forall_mem_cons.2 ⟨subd6_2_56, List.forall_mem_cons.2 ⟨subd6_2_57, List.forall_mem_cons.2 ⟨subd6_2_58, List.forall_mem_cons.2 ⟨subd6_2_59, List.forall_mem_cons.2 ⟨subd6_2_60, List.forall_mem_cons.2 ⟨subd6_2_61, List.forall_mem_cons.2 ⟨subd6_2_62, List.forall_mem_cons.2 ⟨subd6_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_64 : subd6_2 [0, -1, -3] = true := by decide +kernel
theorem subd6_2_65 : subd6_2 [0, -1, -2] = true := by decide +kernel
theorem subd6_2_66 : subd6_2 [0, -1, -1] = true := by decide +kernel
theorem subd6_2_67 : subd6_2 [0, -1, 0] = true := by decide +kernel
theorem subd6_2_68 : subd6_2 [0, -1, 1] = true := by decide +kernel
theorem subd6_2_69 : subd6_2 [0, -1, 2] = true := by decide +kernel
theorem subd6_2_70 : subd6_2 [0, -1, 3] = true := by decide +kernel
theorem subd6_2_71 : subd6_2 [0, -1, 4] = true := by decide +kernel
theorem subd6_2_72 : subd6_2 [0, -1, 5] = true := by decide +kernel
theorem subd6_2_73 : subd6_2 [0, -1, 6] = true := by decide +kernel
theorem subd6_2_74 : subd6_2 [0, 0, -7] = true := by decide +kernel
theorem subd6_2_75 : subd6_2 [0, 0, -6] = true := by decide +kernel
theorem subd6_2_76 : subd6_2 [0, 0, -5] = true := by decide +kernel
theorem subd6_2_77 : subd6_2 [0, 0, -4] = true := by decide +kernel
theorem subd6_2_78 : subd6_2 [0, 0, -3] = true := by decide +kernel
theorem subd6_2_79 : subd6_2 [0, 0, -2] = true := by decide +kernel
theorem subd6_2_80 : subd6_2 [0, 0, -1] = true := by decide +kernel
theorem subd6_2_81 : subd6_2 [0, 0, 0] = true := by decide +kernel
theorem subd6_2_82 : subd6_2 [0, 0, 1] = true := by decide +kernel
theorem subd6_2_83 : subd6_2 [0, 0, 2] = true := by decide +kernel
theorem subd6_2_84 : subd6_2 [0, 0, 3] = true := by decide +kernel
theorem subd6_2_85 : subd6_2 [0, 0, 4] = true := by decide +kernel
theorem subd6_2_86 : subd6_2 [0, 0, 5] = true := by decide +kernel
theorem subd6_2_87 : subd6_2 [0, 0, 6] = true := by decide +kernel
theorem subd6_2_88 : subd6_2 [0, 1, -7] = true := by decide +kernel
theorem subd6_2_89 : subd6_2 [0, 1, -6] = true := by decide +kernel
theorem subd6_2_90 : subd6_2 [0, 1, -5] = true := by decide +kernel
theorem subd6_2_91 : subd6_2 [0, 1, -4] = true := by decide +kernel
theorem subd6_2_92 : subd6_2 [0, 1, -3] = true := by decide +kernel
theorem subd6_2_93 : subd6_2 [0, 1, -2] = true := by decide +kernel
theorem subd6_2_94 : subd6_2 [0, 1, -1] = true := by decide +kernel
theorem subd6_2_95 : subd6_2 [0, 1, 0] = true := by decide +kernel
theorem sbd6_2_2 : ∀ q ∈ blkd6_2_2, subd6_2 q = true := by
  unfold blkd6_2_2
  exact List.forall_mem_cons.2 ⟨subd6_2_64, List.forall_mem_cons.2 ⟨subd6_2_65, List.forall_mem_cons.2 ⟨subd6_2_66, List.forall_mem_cons.2 ⟨subd6_2_67, List.forall_mem_cons.2 ⟨subd6_2_68, List.forall_mem_cons.2 ⟨subd6_2_69, List.forall_mem_cons.2 ⟨subd6_2_70, List.forall_mem_cons.2 ⟨subd6_2_71, List.forall_mem_cons.2 ⟨subd6_2_72, List.forall_mem_cons.2 ⟨subd6_2_73, List.forall_mem_cons.2 ⟨subd6_2_74, List.forall_mem_cons.2 ⟨subd6_2_75, List.forall_mem_cons.2 ⟨subd6_2_76, List.forall_mem_cons.2 ⟨subd6_2_77, List.forall_mem_cons.2 ⟨subd6_2_78, List.forall_mem_cons.2 ⟨subd6_2_79, List.forall_mem_cons.2 ⟨subd6_2_80, List.forall_mem_cons.2 ⟨subd6_2_81, List.forall_mem_cons.2 ⟨subd6_2_82, List.forall_mem_cons.2 ⟨subd6_2_83, List.forall_mem_cons.2 ⟨subd6_2_84, List.forall_mem_cons.2 ⟨subd6_2_85, List.forall_mem_cons.2 ⟨subd6_2_86, List.forall_mem_cons.2 ⟨subd6_2_87, List.forall_mem_cons.2 ⟨subd6_2_88, List.forall_mem_cons.2 ⟨subd6_2_89, List.forall_mem_cons.2 ⟨subd6_2_90, List.forall_mem_cons.2 ⟨subd6_2_91, List.forall_mem_cons.2 ⟨subd6_2_92, List.forall_mem_cons.2 ⟨subd6_2_93, List.forall_mem_cons.2 ⟨subd6_2_94, List.forall_mem_cons.2 ⟨subd6_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_96 : subd6_2 [0, 1, 1] = true := by decide +kernel
theorem subd6_2_97 : subd6_2 [0, 1, 2] = true := by decide +kernel
theorem subd6_2_98 : subd6_2 [0, 1, 3] = true := by decide +kernel
theorem subd6_2_99 : subd6_2 [0, 1, 4] = true := by decide +kernel
theorem subd6_2_100 : subd6_2 [0, 1, 5] = true := by decide +kernel
theorem subd6_2_101 : subd6_2 [0, 1, 6] = true := by decide +kernel
theorem subd6_2_102 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_103 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_104 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_105 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_106 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_107 : subd6_2 [1, -1, -7] = true := by decide +kernel
theorem subd6_2_108 : subd6_2 [1, -1, -6] = true := by decide +kernel
theorem subd6_2_109 : subd6_2 [1, -1, -5] = true := by decide +kernel
theorem subd6_2_110 : subd6_2 [1, -1, -4] = true := by decide +kernel
theorem subd6_2_111 : subd6_2 [1, -1, -3] = true := by decide +kernel
theorem subd6_2_112 : subd6_2 [1, -1, -2] = true := by decide +kernel
theorem subd6_2_113 : subd6_2 [1, -1, -1] = true := by decide +kernel
theorem subd6_2_114 : subd6_2 [1, -1, 0] = true := by decide +kernel
theorem subd6_2_115 : subd6_2 [1, -1, 1] = true := by decide +kernel
theorem subd6_2_116 : subd6_2 [1, -1, 2] = true := by decide +kernel
theorem subd6_2_117 : subd6_2 [1, -1, 3] = true := by decide +kernel
theorem subd6_2_118 : subd6_2 [1, -1, 4] = true := by decide +kernel
theorem subd6_2_119 : subd6_2 [1, -1, 5] = true := by decide +kernel
theorem subd6_2_120 : subd6_2 [1, -1, 6] = true := by decide +kernel
theorem subd6_2_121 : subd6_2 [1, 0, -7] = true := by decide +kernel
theorem subd6_2_122 : subd6_2 [1, 0, -6] = true := by decide +kernel
theorem subd6_2_123 : subd6_2 [1, 0, -5] = true := by decide +kernel
theorem subd6_2_124 : subd6_2 [1, 0, -4] = true := by decide +kernel
theorem subd6_2_125 : subd6_2 [1, 0, -3] = true := by decide +kernel
theorem subd6_2_126 : subd6_2 [1, 0, -2] = true := by decide +kernel
theorem subd6_2_127 : subd6_2 [1, 0, -1] = true := by decide +kernel
theorem sbd6_2_3 : ∀ q ∈ blkd6_2_3, subd6_2 q = true := by
  unfold blkd6_2_3
  exact List.forall_mem_cons.2 ⟨subd6_2_96, List.forall_mem_cons.2 ⟨subd6_2_97, List.forall_mem_cons.2 ⟨subd6_2_98, List.forall_mem_cons.2 ⟨subd6_2_99, List.forall_mem_cons.2 ⟨subd6_2_100, List.forall_mem_cons.2 ⟨subd6_2_101, List.forall_mem_cons.2 ⟨subd6_2_102, List.forall_mem_cons.2 ⟨subd6_2_103, List.forall_mem_cons.2 ⟨subd6_2_104, List.forall_mem_cons.2 ⟨subd6_2_105, List.forall_mem_cons.2 ⟨subd6_2_106, List.forall_mem_cons.2 ⟨subd6_2_107, List.forall_mem_cons.2 ⟨subd6_2_108, List.forall_mem_cons.2 ⟨subd6_2_109, List.forall_mem_cons.2 ⟨subd6_2_110, List.forall_mem_cons.2 ⟨subd6_2_111, List.forall_mem_cons.2 ⟨subd6_2_112, List.forall_mem_cons.2 ⟨subd6_2_113, List.forall_mem_cons.2 ⟨subd6_2_114, List.forall_mem_cons.2 ⟨subd6_2_115, List.forall_mem_cons.2 ⟨subd6_2_116, List.forall_mem_cons.2 ⟨subd6_2_117, List.forall_mem_cons.2 ⟨subd6_2_118, List.forall_mem_cons.2 ⟨subd6_2_119, List.forall_mem_cons.2 ⟨subd6_2_120, List.forall_mem_cons.2 ⟨subd6_2_121, List.forall_mem_cons.2 ⟨subd6_2_122, List.forall_mem_cons.2 ⟨subd6_2_123, List.forall_mem_cons.2 ⟨subd6_2_124, List.forall_mem_cons.2 ⟨subd6_2_125, List.forall_mem_cons.2 ⟨subd6_2_126, List.forall_mem_cons.2 ⟨subd6_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
