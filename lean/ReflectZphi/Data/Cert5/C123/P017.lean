import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [0] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [1] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [1, 1] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-1] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [0] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [1] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [-3] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [-2, -3] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [-2, -2] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [-2, -1] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [-2, 0] = true := by decide +kernel
theorem subd8_4_5 : subd8_4 [-2, 1] = true := by decide +kernel
theorem subd8_4_6 : subd8_4 [-2, 2] = true := by decide +kernel
theorem subd8_4_7 : subd8_4 [-2, 3] = true := by decide +kernel
theorem subd8_4_8 : subd8_4 [-1, -4] = true := by decide +kernel
theorem subd8_4_9 : subd8_4 [-1, -3] = true := by decide +kernel
theorem subd8_4_10 : subd8_4 [-1, -2] = true := by decide +kernel
theorem subd8_4_11 : subd8_4 [-1, -1, -8] = true := by decide +kernel
theorem subd8_4_12 : subd8_4 [-1, -1, -7] = true := by decide +kernel
theorem subd8_4_13 : subd8_4 [-1, -1, -6] = true := by decide +kernel
theorem subd8_4_14 : subd8_4 [-1, -1, -5] = true := by decide +kernel
theorem subd8_4_15 : subd8_4 [-1, -1, -4] = true := by decide +kernel
theorem subd8_4_16 : subd8_4 [-1, -1, -3] = true := by decide +kernel
theorem subd8_4_17 : subd8_4 [-1, -1, -2] = true := by decide +kernel
theorem subd8_4_18 : subd8_4 [-1, -1, -1] = true := by decide +kernel
theorem subd8_4_19 : subd8_4 [-1, -1, 0] = true := by decide +kernel
theorem subd8_4_20 : subd8_4 [-1, -1, 1] = true := by decide +kernel
theorem subd8_4_21 : subd8_4 [-1, -1, 2] = true := by decide +kernel
theorem subd8_4_22 : subd8_4 [-1, -1, 3] = true := by decide +kernel
theorem subd8_4_23 : subd8_4 [-1, -1, 4] = true := by decide +kernel
theorem subd8_4_24 : subd8_4 [-1, -1, 5] = true := by decide +kernel
theorem subd8_4_25 : subd8_4 [-1, 0, -8] = true := by decide +kernel
theorem subd8_4_26 : subd8_4 [-1, 0, -7] = true := by decide +kernel
theorem subd8_4_27 : subd8_4 [-1, 0, -6] = true := by decide +kernel
theorem subd8_4_28 : subd8_4 [-1, 0, -5] = true := by decide +kernel
theorem subd8_4_29 : subd8_4 [-1, 0, -4] = true := by decide +kernel
theorem subd8_4_30 : subd8_4 [-1, 0, -3] = true := by decide +kernel
theorem subd8_4_31 : subd8_4 [-1, 0, -2] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_cons.2 ⟨subd8_4_5, List.forall_mem_cons.2 ⟨subd8_4_6, List.forall_mem_cons.2 ⟨subd8_4_7, List.forall_mem_cons.2 ⟨subd8_4_8, List.forall_mem_cons.2 ⟨subd8_4_9, List.forall_mem_cons.2 ⟨subd8_4_10, List.forall_mem_cons.2 ⟨subd8_4_11, List.forall_mem_cons.2 ⟨subd8_4_12, List.forall_mem_cons.2 ⟨subd8_4_13, List.forall_mem_cons.2 ⟨subd8_4_14, List.forall_mem_cons.2 ⟨subd8_4_15, List.forall_mem_cons.2 ⟨subd8_4_16, List.forall_mem_cons.2 ⟨subd8_4_17, List.forall_mem_cons.2 ⟨subd8_4_18, List.forall_mem_cons.2 ⟨subd8_4_19, List.forall_mem_cons.2 ⟨subd8_4_20, List.forall_mem_cons.2 ⟨subd8_4_21, List.forall_mem_cons.2 ⟨subd8_4_22, List.forall_mem_cons.2 ⟨subd8_4_23, List.forall_mem_cons.2 ⟨subd8_4_24, List.forall_mem_cons.2 ⟨subd8_4_25, List.forall_mem_cons.2 ⟨subd8_4_26, List.forall_mem_cons.2 ⟨subd8_4_27, List.forall_mem_cons.2 ⟨subd8_4_28, List.forall_mem_cons.2 ⟨subd8_4_29, List.forall_mem_cons.2 ⟨subd8_4_30, List.forall_mem_cons.2 ⟨subd8_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_32 : subd8_4 [-1, 0, -1] = true := by decide +kernel
theorem subd8_4_33 : subd8_4 [-1, 0, 0] = true := by decide +kernel
theorem subd8_4_34 : subd8_4 [-1, 0, 1] = true := by decide +kernel
theorem subd8_4_35 : subd8_4 [-1, 0, 2] = true := by decide +kernel
theorem subd8_4_36 : subd8_4 [-1, 0, 3] = true := by decide +kernel
theorem subd8_4_37 : subd8_4 [-1, 0, 4] = true := by decide +kernel
theorem subd8_4_38 : subd8_4 [-1, 0, 5] = true := by decide +kernel
theorem subd8_4_39 : subd8_4 [-1, 0, 6] = true := by decide +kernel
theorem subd8_4_40 : subd8_4 [-1, 1, -7] = true := by decide +kernel
theorem subd8_4_41 : subd8_4 [-1, 1, -6] = true := by decide +kernel
theorem subd8_4_42 : subd8_4 [-1, 1, -5] = true := by decide +kernel
theorem subd8_4_43 : subd8_4 [-1, 1, -4] = true := by decide +kernel
theorem subd8_4_44 : subd8_4 [-1, 1, -3] = true := by decide +kernel
theorem subd8_4_45 : subd8_4 [-1, 1, -2] = true := by decide +kernel
theorem subd8_4_46 : subd8_4 [-1, 1, -1] = true := by decide +kernel
theorem subd8_4_47 : subd8_4 [-1, 1, 0] = true := by decide +kernel
theorem subd8_4_48 : subd8_4 [-1, 1, 1] = true := by decide +kernel
theorem subd8_4_49 : subd8_4 [-1, 1, 2] = true := by decide +kernel
theorem subd8_4_50 : subd8_4 [-1, 1, 3] = true := by decide +kernel
theorem subd8_4_51 : subd8_4 [-1, 1, 4] = true := by decide +kernel
theorem subd8_4_52 : subd8_4 [-1, 1, 5] = true := by decide +kernel
theorem subd8_4_53 : subd8_4 [-1, 1, 6] = true := by decide +kernel
theorem subd8_4_54 : subd8_4 [-1, 1, 7] = true := by decide +kernel
theorem subd8_4_55 : subd8_4 [-1, 2] = true := by decide +kernel
theorem subd8_4_56 : subd8_4 [-1, 3] = true := by decide +kernel
theorem subd8_4_57 : subd8_4 [0, -4] = true := by decide +kernel
theorem subd8_4_58 : subd8_4 [0, -3] = true := by decide +kernel
theorem subd8_4_59 : subd8_4 [0, -2] = true := by decide +kernel
theorem subd8_4_60 : subd8_4 [0, -1, -8] = true := by decide +kernel
theorem subd8_4_61 : subd8_4 [0, -1, -7] = true := by decide +kernel
theorem subd8_4_62 : subd8_4 [0, -1, -6] = true := by decide +kernel
theorem subd8_4_63 : subd8_4 [0, -1, -5] = true := by decide +kernel
theorem sbd8_4_1 : ∀ q ∈ blkd8_4_1, subd8_4 q = true := by
  unfold blkd8_4_1
  exact List.forall_mem_cons.2 ⟨subd8_4_32, List.forall_mem_cons.2 ⟨subd8_4_33, List.forall_mem_cons.2 ⟨subd8_4_34, List.forall_mem_cons.2 ⟨subd8_4_35, List.forall_mem_cons.2 ⟨subd8_4_36, List.forall_mem_cons.2 ⟨subd8_4_37, List.forall_mem_cons.2 ⟨subd8_4_38, List.forall_mem_cons.2 ⟨subd8_4_39, List.forall_mem_cons.2 ⟨subd8_4_40, List.forall_mem_cons.2 ⟨subd8_4_41, List.forall_mem_cons.2 ⟨subd8_4_42, List.forall_mem_cons.2 ⟨subd8_4_43, List.forall_mem_cons.2 ⟨subd8_4_44, List.forall_mem_cons.2 ⟨subd8_4_45, List.forall_mem_cons.2 ⟨subd8_4_46, List.forall_mem_cons.2 ⟨subd8_4_47, List.forall_mem_cons.2 ⟨subd8_4_48, List.forall_mem_cons.2 ⟨subd8_4_49, List.forall_mem_cons.2 ⟨subd8_4_50, List.forall_mem_cons.2 ⟨subd8_4_51, List.forall_mem_cons.2 ⟨subd8_4_52, List.forall_mem_cons.2 ⟨subd8_4_53, List.forall_mem_cons.2 ⟨subd8_4_54, List.forall_mem_cons.2 ⟨subd8_4_55, List.forall_mem_cons.2 ⟨subd8_4_56, List.forall_mem_cons.2 ⟨subd8_4_57, List.forall_mem_cons.2 ⟨subd8_4_58, List.forall_mem_cons.2 ⟨subd8_4_59, List.forall_mem_cons.2 ⟨subd8_4_60, List.forall_mem_cons.2 ⟨subd8_4_61, List.forall_mem_cons.2 ⟨subd8_4_62, List.forall_mem_cons.2 ⟨subd8_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_64 : subd8_4 [0, -1, -4] = true := by decide +kernel
theorem subd8_4_65 : subd8_4 [0, -1, -3] = true := by decide +kernel
theorem subd8_4_66 : subd8_4 [0, -1, -2] = true := by decide +kernel
theorem subd8_4_67 : subd8_4 [0, -1, -1] = true := by decide +kernel
theorem subd8_4_68 : subd8_4 [0, -1, 0] = true := by decide +kernel
theorem subd8_4_69 : subd8_4 [0, -1, 1] = true := by decide +kernel
theorem subd8_4_70 : subd8_4 [0, -1, 2] = true := by decide +kernel
theorem subd8_4_71 : subd8_4 [0, -1, 3] = true := by decide +kernel
theorem subd8_4_72 : subd8_4 [0, -1, 4] = true := by decide +kernel
theorem subd8_4_73 : subd8_4 [0, -1, 5] = true := by decide +kernel
theorem subd8_4_74 : subd8_4 [0, -1, 6] = true := by decide +kernel
theorem subd8_4_75 : subd8_4 [0, 0, -8] = true := by decide +kernel
theorem subd8_4_76 : subd8_4 [0, 0, -7] = true := by decide +kernel
theorem subd8_4_77 : subd8_4 [0, 0, -6] = true := by decide +kernel
theorem subd8_4_78 : subd8_4 [0, 0, -5] = true := by decide +kernel
theorem subd8_4_79 : subd8_4 [0, 0, -4] = true := by decide +kernel
theorem subd8_4_80 : subd8_4 [0, 0, -3] = true := by decide +kernel
theorem subd8_4_81 : subd8_4 [0, 0, -2] = true := by decide +kernel
theorem subd8_4_82 : subd8_4 [0, 0, -1] = true := by decide +kernel
theorem subd8_4_83 : subd8_4 [0, 0, 0] = true := by decide +kernel
theorem subd8_4_84 : subd8_4 [0, 0, 1] = true := by decide +kernel
theorem subd8_4_85 : subd8_4 [0, 0, 2] = true := by decide +kernel
theorem subd8_4_86 : subd8_4 [0, 0, 3] = true := by decide +kernel
theorem subd8_4_87 : subd8_4 [0, 0, 4] = true := by decide +kernel
theorem subd8_4_88 : subd8_4 [0, 0, 5] = true := by decide +kernel
theorem subd8_4_89 : subd8_4 [0, 0, 6] = true := by decide +kernel
theorem subd8_4_90 : subd8_4 [0, 0, 7] = true := by decide +kernel
theorem subd8_4_91 : subd8_4 [0, 1, -7] = true := by decide +kernel
theorem subd8_4_92 : subd8_4 [0, 1, -6] = true := by decide +kernel
theorem subd8_4_93 : subd8_4 [0, 1, -5] = true := by decide +kernel
theorem subd8_4_94 : subd8_4 [0, 1, -4] = true := by decide +kernel
theorem subd8_4_95 : subd8_4 [0, 1, -3] = true := by decide +kernel
theorem sbd8_4_2 : ∀ q ∈ blkd8_4_2, subd8_4 q = true := by
  unfold blkd8_4_2
  exact List.forall_mem_cons.2 ⟨subd8_4_64, List.forall_mem_cons.2 ⟨subd8_4_65, List.forall_mem_cons.2 ⟨subd8_4_66, List.forall_mem_cons.2 ⟨subd8_4_67, List.forall_mem_cons.2 ⟨subd8_4_68, List.forall_mem_cons.2 ⟨subd8_4_69, List.forall_mem_cons.2 ⟨subd8_4_70, List.forall_mem_cons.2 ⟨subd8_4_71, List.forall_mem_cons.2 ⟨subd8_4_72, List.forall_mem_cons.2 ⟨subd8_4_73, List.forall_mem_cons.2 ⟨subd8_4_74, List.forall_mem_cons.2 ⟨subd8_4_75, List.forall_mem_cons.2 ⟨subd8_4_76, List.forall_mem_cons.2 ⟨subd8_4_77, List.forall_mem_cons.2 ⟨subd8_4_78, List.forall_mem_cons.2 ⟨subd8_4_79, List.forall_mem_cons.2 ⟨subd8_4_80, List.forall_mem_cons.2 ⟨subd8_4_81, List.forall_mem_cons.2 ⟨subd8_4_82, List.forall_mem_cons.2 ⟨subd8_4_83, List.forall_mem_cons.2 ⟨subd8_4_84, List.forall_mem_cons.2 ⟨subd8_4_85, List.forall_mem_cons.2 ⟨subd8_4_86, List.forall_mem_cons.2 ⟨subd8_4_87, List.forall_mem_cons.2 ⟨subd8_4_88, List.forall_mem_cons.2 ⟨subd8_4_89, List.forall_mem_cons.2 ⟨subd8_4_90, List.forall_mem_cons.2 ⟨subd8_4_91, List.forall_mem_cons.2 ⟨subd8_4_92, List.forall_mem_cons.2 ⟨subd8_4_93, List.forall_mem_cons.2 ⟨subd8_4_94, List.forall_mem_cons.2 ⟨subd8_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
