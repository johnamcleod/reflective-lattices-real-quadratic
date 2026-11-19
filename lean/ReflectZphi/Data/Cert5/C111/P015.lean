import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_0 : subd8_1 [-3] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-2, 3] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [1, 2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [3] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-3] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-2, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-2, -1, -9] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-2, -1, -8] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-2, -1, -7] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-2, -1, -6] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-2, -1, -5] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-2, -1, -4] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-2, -1, -3] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-2, -1, -2] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-2, -1, -1] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-2, -1, 0] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-2, -1, 1] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-2, -1, 2] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-2, -1, 3] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-2, -1, 4] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-2, -1, 5] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-2, -1, 6] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-2, 0, -9] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-2, 0, -8] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-2, 0, -7] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-2, 0, -6] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-2, 0, -5] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-2, 0, -4] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-2, 0, -3] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-2, 0, -2] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-2, 0, -1] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-2, 0, 0] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-2, 0, 1] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-2, 0, 2] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-2, 0, 3] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-2, 0, 4] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-2, 0, 5] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-2, 0, 6] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-2, 0, 7] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-2, 1, -8] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-2, 1, -7] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-2, 1, -6] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-2, 1, -5] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-2, 1, -4] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-2, 1, -3] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-2, 1, -2] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-2, 1, -1] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-2, 1, 0] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-2, 1, 1] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-2, 1, 2] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-2, 1, 3] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-2, 1, 4] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-2, 1, 5] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-2, 1, 6] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-2, 1, 7] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-2, 2] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-1, -2, -9] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-1, -2, -8] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [-1, -2, -7] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [-1, -2, -6] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [-1, -2, -5] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [-1, -2, -4] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [-1, -2, -3] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [-1, -2, -2] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [-1, -2, -1] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [-1, -2, 0] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_64 : subd8_2 [-1, -2, 1] = true := by decide +kernel
theorem subd8_2_65 : subd8_2 [-1, -2, 2] = true := by decide +kernel
theorem subd8_2_66 : subd8_2 [-1, -2, 3] = true := by decide +kernel
theorem subd8_2_67 : subd8_2 [-1, -2, 4] = true := by decide +kernel
theorem subd8_2_68 : subd8_2 [-1, -2, 5] = true := by decide +kernel
theorem subd8_2_69 : subd8_2 [-1, -2, 6] = true := by decide +kernel
theorem subd8_2_70 : subd8_2 [-1, -1, -11] = true := by decide +kernel
theorem subd8_2_71 : subd8_2 [-1, -1, -10] = true := by decide +kernel
theorem subd8_2_72 : subd8_2 [-1, -1, -9] = true := by decide +kernel
theorem subd8_2_73 : subd8_2 [-1, -1, -8] = true := by decide +kernel
theorem subd8_2_74 : subd8_2 [-1, -1, -7] = true := by decide +kernel
theorem subd8_2_75 : subd8_2 [-1, -1, -6] = true := by decide +kernel
theorem subd8_2_76 : subd8_2 [-1, -1, -5] = true := by decide +kernel
theorem subd8_2_77 : subd8_2 [-1, -1, -4] = true := by decide +kernel
theorem subd8_2_78 : subd8_2 [-1, -1, -3] = true := by decide +kernel
theorem subd8_2_79 : subd8_2 [-1, -1, -2] = true := by decide +kernel
theorem subd8_2_80 : subd8_2 [-1, -1, -1] = true := by decide +kernel
theorem subd8_2_81 : subd8_2 [-1, -1, 0] = true := by decide +kernel
theorem subd8_2_82 : subd8_2 [-1, -1, 1] = true := by decide +kernel
theorem subd8_2_83 : subd8_2 [-1, -1, 2] = true := by decide +kernel
theorem subd8_2_84 : subd8_2 [-1, -1, 3] = true := by decide +kernel
theorem subd8_2_85 : subd8_2 [-1, -1, 4] = true := by decide +kernel
theorem subd8_2_86 : subd8_2 [-1, -1, 5] = true := by decide +kernel
theorem subd8_2_87 : subd8_2 [-1, -1, 6] = true := by decide +kernel
theorem subd8_2_88 : subd8_2 [-1, -1, 7] = true := by decide +kernel
theorem subd8_2_89 : subd8_2 [-1, -1, 8] = true := by decide +kernel
theorem subd8_2_90 : subd8_2 [-1, -1, 9] = true := by decide +kernel
theorem subd8_2_91 : subd8_2 [-1, 0, -11] = true := by decide +kernel
theorem subd8_2_92 : subd8_2 [-1, 0, -10] = true := by decide +kernel
theorem subd8_2_93 : subd8_2 [-1, 0, -9] = true := by decide +kernel
theorem subd8_2_94 : subd8_2 [-1, 0, -8] = true := by decide +kernel
theorem subd8_2_95 : subd8_2 [-1, 0, -7] = true := by decide +kernel
theorem sbd8_2_2 : ∀ q ∈ blkd8_2_2, subd8_2 q = true := by
  unfold blkd8_2_2
  exact List.forall_mem_cons.2 ⟨subd8_2_64, List.forall_mem_cons.2 ⟨subd8_2_65, List.forall_mem_cons.2 ⟨subd8_2_66, List.forall_mem_cons.2 ⟨subd8_2_67, List.forall_mem_cons.2 ⟨subd8_2_68, List.forall_mem_cons.2 ⟨subd8_2_69, List.forall_mem_cons.2 ⟨subd8_2_70, List.forall_mem_cons.2 ⟨subd8_2_71, List.forall_mem_cons.2 ⟨subd8_2_72, List.forall_mem_cons.2 ⟨subd8_2_73, List.forall_mem_cons.2 ⟨subd8_2_74, List.forall_mem_cons.2 ⟨subd8_2_75, List.forall_mem_cons.2 ⟨subd8_2_76, List.forall_mem_cons.2 ⟨subd8_2_77, List.forall_mem_cons.2 ⟨subd8_2_78, List.forall_mem_cons.2 ⟨subd8_2_79, List.forall_mem_cons.2 ⟨subd8_2_80, List.forall_mem_cons.2 ⟨subd8_2_81, List.forall_mem_cons.2 ⟨subd8_2_82, List.forall_mem_cons.2 ⟨subd8_2_83, List.forall_mem_cons.2 ⟨subd8_2_84, List.forall_mem_cons.2 ⟨subd8_2_85, List.forall_mem_cons.2 ⟨subd8_2_86, List.forall_mem_cons.2 ⟨subd8_2_87, List.forall_mem_cons.2 ⟨subd8_2_88, List.forall_mem_cons.2 ⟨subd8_2_89, List.forall_mem_cons.2 ⟨subd8_2_90, List.forall_mem_cons.2 ⟨subd8_2_91, List.forall_mem_cons.2 ⟨subd8_2_92, List.forall_mem_cons.2 ⟨subd8_2_93, List.forall_mem_cons.2 ⟨subd8_2_94, List.forall_mem_cons.2 ⟨subd8_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_96 : subd8_2 [-1, 0, -6] = true := by decide +kernel
theorem subd8_2_97 : subd8_2 [-1, 0, -5] = true := by decide +kernel
theorem subd8_2_98 : subd8_2 [-1, 0, -4] = true := by decide +kernel
theorem subd8_2_99 : subd8_2 [-1, 0, -3] = true := by decide +kernel
theorem subd8_2_100 : subd8_2 [-1, 0, -2] = true := by decide +kernel
theorem subd8_2_101 : subd8_2 [-1, 0, -1] = true := by decide +kernel
theorem subd8_2_102 : subd8_2 [-1, 0, 0] = true := by decide +kernel
theorem subd8_2_103 : subd8_2 [-1, 0, 1] = true := by decide +kernel
theorem subd8_2_104 : subd8_2 [-1, 0, 2] = true := by decide +kernel
theorem subd8_2_105 : subd8_2 [-1, 0, 3] = true := by decide +kernel
theorem subd8_2_106 : subd8_2 [-1, 0, 4] = true := by decide +kernel
theorem subd8_2_107 : subd8_2 [-1, 0, 5] = true := by decide +kernel
theorem subd8_2_108 : subd8_2 [-1, 0, 6] = true := by decide +kernel
theorem subd8_2_109 : subd8_2 [-1, 0, 7] = true := by decide +kernel
theorem subd8_2_110 : subd8_2 [-1, 0, 8] = true := by decide +kernel
theorem subd8_2_111 : subd8_2 [-1, 0, 9] = true := by decide +kernel
theorem subd8_2_112 : subd8_2 [-1, 0, 10] = true := by decide +kernel
theorem subd8_2_113 : subd8_2 [-1, 1, -10] = true := by decide +kernel
theorem subd8_2_114 : subd8_2 [-1, 1, -9] = true := by decide +kernel
theorem subd8_2_115 : subd8_2 [-1, 1, -8] = true := by decide +kernel
theorem subd8_2_116 : subd8_2 [-1, 1, -7] = true := by decide +kernel
theorem subd8_2_117 : subd8_2 [-1, 1, -6] = true := by decide +kernel
theorem subd8_2_118 : subd8_2 [-1, 1, -5] = true := by decide +kernel
theorem subd8_2_119 : subd8_2 [-1, 1, -4] = true := by decide +kernel
theorem subd8_2_120 : subd8_2 [-1, 1, -3] = true := by decide +kernel
theorem subd8_2_121 : subd8_2 [-1, 1, -2] = true := by decide +kernel
theorem subd8_2_122 : subd8_2 [-1, 1, -1] = true := by decide +kernel
theorem subd8_2_123 : subd8_2 [-1, 1, 0] = true := by decide +kernel
theorem subd8_2_124 : subd8_2 [-1, 1, 1] = true := by decide +kernel
theorem subd8_2_125 : subd8_2 [-1, 1, 2] = true := by decide +kernel
theorem subd8_2_126 : subd8_2 [-1, 1, 3] = true := by decide +kernel
theorem subd8_2_127 : subd8_2 [-1, 1, 4] = true := by decide +kernel
theorem sbd8_2_3 : ∀ q ∈ blkd8_2_3, subd8_2 q = true := by
  unfold blkd8_2_3
  exact List.forall_mem_cons.2 ⟨subd8_2_96, List.forall_mem_cons.2 ⟨subd8_2_97, List.forall_mem_cons.2 ⟨subd8_2_98, List.forall_mem_cons.2 ⟨subd8_2_99, List.forall_mem_cons.2 ⟨subd8_2_100, List.forall_mem_cons.2 ⟨subd8_2_101, List.forall_mem_cons.2 ⟨subd8_2_102, List.forall_mem_cons.2 ⟨subd8_2_103, List.forall_mem_cons.2 ⟨subd8_2_104, List.forall_mem_cons.2 ⟨subd8_2_105, List.forall_mem_cons.2 ⟨subd8_2_106, List.forall_mem_cons.2 ⟨subd8_2_107, List.forall_mem_cons.2 ⟨subd8_2_108, List.forall_mem_cons.2 ⟨subd8_2_109, List.forall_mem_cons.2 ⟨subd8_2_110, List.forall_mem_cons.2 ⟨subd8_2_111, List.forall_mem_cons.2 ⟨subd8_2_112, List.forall_mem_cons.2 ⟨subd8_2_113, List.forall_mem_cons.2 ⟨subd8_2_114, List.forall_mem_cons.2 ⟨subd8_2_115, List.forall_mem_cons.2 ⟨subd8_2_116, List.forall_mem_cons.2 ⟨subd8_2_117, List.forall_mem_cons.2 ⟨subd8_2_118, List.forall_mem_cons.2 ⟨subd8_2_119, List.forall_mem_cons.2 ⟨subd8_2_120, List.forall_mem_cons.2 ⟨subd8_2_121, List.forall_mem_cons.2 ⟨subd8_2_122, List.forall_mem_cons.2 ⟨subd8_2_123, List.forall_mem_cons.2 ⟨subd8_2_124, List.forall_mem_cons.2 ⟨subd8_2_125, List.forall_mem_cons.2 ⟨subd8_2_126, List.forall_mem_cons.2 ⟨subd8_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_128 : subd8_2 [-1, 1, 5] = true := by decide +kernel
theorem subd8_2_129 : subd8_2 [-1, 1, 6] = true := by decide +kernel
theorem subd8_2_130 : subd8_2 [-1, 1, 7] = true := by decide +kernel
theorem subd8_2_131 : subd8_2 [-1, 1, 8] = true := by decide +kernel
theorem subd8_2_132 : subd8_2 [-1, 1, 9] = true := by decide +kernel
theorem subd8_2_133 : subd8_2 [-1, 1, 10] = true := by decide +kernel
theorem subd8_2_134 : subd8_2 [-1, 2, -8] = true := by decide +kernel
theorem subd8_2_135 : subd8_2 [-1, 2, -7] = true := by decide +kernel
theorem subd8_2_136 : subd8_2 [-1, 2, -6] = true := by decide +kernel
theorem subd8_2_137 : subd8_2 [-1, 2, -5] = true := by decide +kernel
theorem subd8_2_138 : subd8_2 [-1, 2, -4] = true := by decide +kernel
theorem subd8_2_139 : subd8_2 [-1, 2, -3] = true := by decide +kernel
theorem subd8_2_140 : subd8_2 [-1, 2, -2] = true := by decide +kernel
theorem subd8_2_141 : subd8_2 [-1, 2, -1] = true := by decide +kernel
theorem subd8_2_142 : subd8_2 [-1, 2, 0] = true := by decide +kernel
theorem subd8_2_143 : subd8_2 [-1, 2, 1] = true := by decide +kernel
theorem subd8_2_144 : subd8_2 [-1, 2, 2] = true := by decide +kernel
theorem subd8_2_145 : subd8_2 [-1, 2, 3] = true := by decide +kernel
theorem subd8_2_146 : subd8_2 [-1, 2, 4] = true := by decide +kernel
theorem subd8_2_147 : subd8_2 [-1, 2, 5] = true := by decide +kernel
theorem subd8_2_148 : subd8_2 [-1, 2, 6] = true := by decide +kernel
theorem subd8_2_149 : subd8_2 [-1, 2, 7] = true := by decide +kernel
theorem subd8_2_150 : subd8_2 [0, -4] = true := by decide +kernel
theorem subd8_2_151 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_152 : subd8_2 [0, -2, -10] = true := by decide +kernel
theorem subd8_2_153 : subd8_2 [0, -2, -9] = true := by decide +kernel
theorem subd8_2_154 : subd8_2 [0, -2, -8] = true := by decide +kernel
theorem subd8_2_155 : subd8_2 [0, -2, -7] = true := by decide +kernel
theorem subd8_2_156 : subd8_2 [0, -2, -6] = true := by decide +kernel
theorem subd8_2_157 : subd8_2 [0, -2, -5] = true := by decide +kernel
theorem subd8_2_158 : subd8_2 [0, -2, -4] = true := by decide +kernel
theorem subd8_2_159 : subd8_2 [0, -2, -3] = true := by decide +kernel
theorem sbd8_2_4 : ∀ q ∈ blkd8_2_4, subd8_2 q = true := by
  unfold blkd8_2_4
  exact List.forall_mem_cons.2 ⟨subd8_2_128, List.forall_mem_cons.2 ⟨subd8_2_129, List.forall_mem_cons.2 ⟨subd8_2_130, List.forall_mem_cons.2 ⟨subd8_2_131, List.forall_mem_cons.2 ⟨subd8_2_132, List.forall_mem_cons.2 ⟨subd8_2_133, List.forall_mem_cons.2 ⟨subd8_2_134, List.forall_mem_cons.2 ⟨subd8_2_135, List.forall_mem_cons.2 ⟨subd8_2_136, List.forall_mem_cons.2 ⟨subd8_2_137, List.forall_mem_cons.2 ⟨subd8_2_138, List.forall_mem_cons.2 ⟨subd8_2_139, List.forall_mem_cons.2 ⟨subd8_2_140, List.forall_mem_cons.2 ⟨subd8_2_141, List.forall_mem_cons.2 ⟨subd8_2_142, List.forall_mem_cons.2 ⟨subd8_2_143, List.forall_mem_cons.2 ⟨subd8_2_144, List.forall_mem_cons.2 ⟨subd8_2_145, List.forall_mem_cons.2 ⟨subd8_2_146, List.forall_mem_cons.2 ⟨subd8_2_147, List.forall_mem_cons.2 ⟨subd8_2_148, List.forall_mem_cons.2 ⟨subd8_2_149, List.forall_mem_cons.2 ⟨subd8_2_150, List.forall_mem_cons.2 ⟨subd8_2_151, List.forall_mem_cons.2 ⟨subd8_2_152, List.forall_mem_cons.2 ⟨subd8_2_153, List.forall_mem_cons.2 ⟨subd8_2_154, List.forall_mem_cons.2 ⟨subd8_2_155, List.forall_mem_cons.2 ⟨subd8_2_156, List.forall_mem_cons.2 ⟨subd8_2_157, List.forall_mem_cons.2 ⟨subd8_2_158, List.forall_mem_cons.2 ⟨subd8_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_160 : subd8_2 [0, -2, -2] = true := by decide +kernel
theorem subd8_2_161 : subd8_2 [0, -2, -1] = true := by decide +kernel
theorem subd8_2_162 : subd8_2 [0, -2, 0] = true := by decide +kernel
theorem subd8_2_163 : subd8_2 [0, -2, 1] = true := by decide +kernel
theorem subd8_2_164 : subd8_2 [0, -2, 2] = true := by decide +kernel
theorem subd8_2_165 : subd8_2 [0, -2, 3] = true := by decide +kernel
theorem subd8_2_166 : subd8_2 [0, -2, 4] = true := by decide +kernel
theorem subd8_2_167 : subd8_2 [0, -2, 5] = true := by decide +kernel
theorem subd8_2_168 : subd8_2 [0, -2, 6] = true := by decide +kernel
theorem subd8_2_169 : subd8_2 [0, -2, 7] = true := by decide +kernel
theorem subd8_2_170 : subd8_2 [0, -1, -11] = true := by decide +kernel
theorem subd8_2_171 : subd8_2 [0, -1, -10] = true := by decide +kernel
theorem subd8_2_172 : subd8_2 [0, -1, -9] = true := by decide +kernel
theorem subd8_2_173 : subd8_2 [0, -1, -8] = true := by decide +kernel
theorem subd8_2_174 : subd8_2 [0, -1, -7] = true := by decide +kernel
theorem subd8_2_175 : subd8_2 [0, -1, -6] = true := by decide +kernel
theorem subd8_2_176 : subd8_2 [0, -1, -5] = true := by decide +kernel
theorem subd8_2_177 : subd8_2 [0, -1, -4] = true := by decide +kernel
theorem subd8_2_178 : subd8_2 [0, -1, -3] = true := by decide +kernel
theorem subd8_2_179 : subd8_2 [0, -1, -2] = true := by decide +kernel
theorem subd8_2_180 : subd8_2 [0, -1, -1] = true := by decide +kernel
theorem subd8_2_181 : subd8_2 [0, -1, 0] = true := by decide +kernel
theorem subd8_2_182 : subd8_2 [0, -1, 1] = true := by decide +kernel
theorem subd8_2_183 : subd8_2 [0, -1, 2] = true := by decide +kernel
theorem subd8_2_184 : subd8_2 [0, -1, 3] = true := by decide +kernel
theorem subd8_2_185 : subd8_2 [0, -1, 4] = true := by decide +kernel
theorem subd8_2_186 : subd8_2 [0, -1, 5] = true := by decide +kernel
theorem subd8_2_187 : subd8_2 [0, -1, 6] = true := by decide +kernel
theorem subd8_2_188 : subd8_2 [0, -1, 7] = true := by decide +kernel
theorem subd8_2_189 : subd8_2 [0, -1, 8] = true := by decide +kernel
theorem subd8_2_190 : subd8_2 [0, -1, 9] = true := by decide +kernel
theorem subd8_2_191 : subd8_2 [0, -1, 10] = true := by decide +kernel
theorem sbd8_2_5 : ∀ q ∈ blkd8_2_5, subd8_2 q = true := by
  unfold blkd8_2_5
  exact List.forall_mem_cons.2 ⟨subd8_2_160, List.forall_mem_cons.2 ⟨subd8_2_161, List.forall_mem_cons.2 ⟨subd8_2_162, List.forall_mem_cons.2 ⟨subd8_2_163, List.forall_mem_cons.2 ⟨subd8_2_164, List.forall_mem_cons.2 ⟨subd8_2_165, List.forall_mem_cons.2 ⟨subd8_2_166, List.forall_mem_cons.2 ⟨subd8_2_167, List.forall_mem_cons.2 ⟨subd8_2_168, List.forall_mem_cons.2 ⟨subd8_2_169, List.forall_mem_cons.2 ⟨subd8_2_170, List.forall_mem_cons.2 ⟨subd8_2_171, List.forall_mem_cons.2 ⟨subd8_2_172, List.forall_mem_cons.2 ⟨subd8_2_173, List.forall_mem_cons.2 ⟨subd8_2_174, List.forall_mem_cons.2 ⟨subd8_2_175, List.forall_mem_cons.2 ⟨subd8_2_176, List.forall_mem_cons.2 ⟨subd8_2_177, List.forall_mem_cons.2 ⟨subd8_2_178, List.forall_mem_cons.2 ⟨subd8_2_179, List.forall_mem_cons.2 ⟨subd8_2_180, List.forall_mem_cons.2 ⟨subd8_2_181, List.forall_mem_cons.2 ⟨subd8_2_182, List.forall_mem_cons.2 ⟨subd8_2_183, List.forall_mem_cons.2 ⟨subd8_2_184, List.forall_mem_cons.2 ⟨subd8_2_185, List.forall_mem_cons.2 ⟨subd8_2_186, List.forall_mem_cons.2 ⟨subd8_2_187, List.forall_mem_cons.2 ⟨subd8_2_188, List.forall_mem_cons.2 ⟨subd8_2_189, List.forall_mem_cons.2 ⟨subd8_2_190, List.forall_mem_cons.2 ⟨subd8_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_192 : subd8_2 [0, 0, -12] = true := by decide +kernel
theorem subd8_2_193 : subd8_2 [0, 0, -11] = true := by decide +kernel
theorem subd8_2_194 : subd8_2 [0, 0, -10] = true := by decide +kernel
theorem subd8_2_195 : subd8_2 [0, 0, -9] = true := by decide +kernel
theorem subd8_2_196 : subd8_2 [0, 0, -8] = true := by decide +kernel
theorem subd8_2_197 : subd8_2 [0, 0, -7] = true := by decide +kernel
theorem subd8_2_198 : subd8_2 [0, 0, -6] = true := by decide +kernel
theorem subd8_2_199 : subd8_2 [0, 0, -5] = true := by decide +kernel
theorem subd8_2_200 : subd8_2 [0, 0, -4] = true := by decide +kernel
theorem subd8_2_201 : subd8_2 [0, 0, -3] = true := by decide +kernel
theorem subd8_2_202 : subd8_2 [0, 0, -2] = true := by decide +kernel
theorem subd8_2_203 : subd8_2 [0, 0, -1] = true := by decide +kernel
theorem subd8_2_204 : subd8_2 [0, 0, 0] = true := by decide +kernel
theorem subd8_2_205 : subd8_2 [0, 0, 1] = true := by decide +kernel
theorem subd8_2_206 : subd8_2 [0, 0, 2] = true := by decide +kernel
theorem subd8_2_207 : subd8_2 [0, 0, 3] = true := by decide +kernel
theorem subd8_2_208 : subd8_2 [0, 0, 4] = true := by decide +kernel
theorem subd8_2_209 : subd8_2 [0, 0, 5] = true := by decide +kernel
theorem subd8_2_210 : subd8_2 [0, 0, 6] = true := by decide +kernel
theorem subd8_2_211 : subd8_2 [0, 0, 7] = true := by decide +kernel
theorem subd8_2_212 : subd8_2 [0, 0, 8] = true := by decide +kernel
theorem subd8_2_213 : subd8_2 [0, 0, 9] = true := by decide +kernel
theorem subd8_2_214 : subd8_2 [0, 0, 10] = true := by decide +kernel
theorem subd8_2_215 : subd8_2 [0, 0, 11] = true := by decide +kernel
theorem subd8_2_216 : subd8_2 [0, 1, -11] = true := by decide +kernel
theorem subd8_2_217 : subd8_2 [0, 1, -10] = true := by decide +kernel
theorem subd8_2_218 : subd8_2 [0, 1, -9] = true := by decide +kernel
theorem subd8_2_219 : subd8_2 [0, 1, -8] = true := by decide +kernel
theorem subd8_2_220 : subd8_2 [0, 1, -7] = true := by decide +kernel
theorem subd8_2_221 : subd8_2 [0, 1, -6] = true := by decide +kernel
theorem subd8_2_222 : subd8_2 [0, 1, -5] = true := by decide +kernel
theorem subd8_2_223 : subd8_2 [0, 1, -4] = true := by decide +kernel
theorem sbd8_2_6 : ∀ q ∈ blkd8_2_6, subd8_2 q = true := by
  unfold blkd8_2_6
  exact List.forall_mem_cons.2 ⟨subd8_2_192, List.forall_mem_cons.2 ⟨subd8_2_193, List.forall_mem_cons.2 ⟨subd8_2_194, List.forall_mem_cons.2 ⟨subd8_2_195, List.forall_mem_cons.2 ⟨subd8_2_196, List.forall_mem_cons.2 ⟨subd8_2_197, List.forall_mem_cons.2 ⟨subd8_2_198, List.forall_mem_cons.2 ⟨subd8_2_199, List.forall_mem_cons.2 ⟨subd8_2_200, List.forall_mem_cons.2 ⟨subd8_2_201, List.forall_mem_cons.2 ⟨subd8_2_202, List.forall_mem_cons.2 ⟨subd8_2_203, List.forall_mem_cons.2 ⟨subd8_2_204, List.forall_mem_cons.2 ⟨subd8_2_205, List.forall_mem_cons.2 ⟨subd8_2_206, List.forall_mem_cons.2 ⟨subd8_2_207, List.forall_mem_cons.2 ⟨subd8_2_208, List.forall_mem_cons.2 ⟨subd8_2_209, List.forall_mem_cons.2 ⟨subd8_2_210, List.forall_mem_cons.2 ⟨subd8_2_211, List.forall_mem_cons.2 ⟨subd8_2_212, List.forall_mem_cons.2 ⟨subd8_2_213, List.forall_mem_cons.2 ⟨subd8_2_214, List.forall_mem_cons.2 ⟨subd8_2_215, List.forall_mem_cons.2 ⟨subd8_2_216, List.forall_mem_cons.2 ⟨subd8_2_217, List.forall_mem_cons.2 ⟨subd8_2_218, List.forall_mem_cons.2 ⟨subd8_2_219, List.forall_mem_cons.2 ⟨subd8_2_220, List.forall_mem_cons.2 ⟨subd8_2_221, List.forall_mem_cons.2 ⟨subd8_2_222, List.forall_mem_cons.2 ⟨subd8_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_224 : subd8_2 [0, 1, -3] = true := by decide +kernel
theorem subd8_2_225 : subd8_2 [0, 1, -2] = true := by decide +kernel
theorem subd8_2_226 : subd8_2 [0, 1, -1] = true := by decide +kernel
theorem subd8_2_227 : subd8_2 [0, 1, 0] = true := by decide +kernel
theorem subd8_2_228 : subd8_2 [0, 1, 1] = true := by decide +kernel
theorem subd8_2_229 : subd8_2 [0, 1, 2] = true := by decide +kernel
theorem subd8_2_230 : subd8_2 [0, 1, 3] = true := by decide +kernel
theorem subd8_2_231 : subd8_2 [0, 1, 4] = true := by decide +kernel
theorem subd8_2_232 : subd8_2 [0, 1, 5] = true := by decide +kernel
theorem subd8_2_233 : subd8_2 [0, 1, 6] = true := by decide +kernel
theorem subd8_2_234 : subd8_2 [0, 1, 7] = true := by decide +kernel
theorem subd8_2_235 : subd8_2 [0, 1, 8] = true := by decide +kernel
theorem subd8_2_236 : subd8_2 [0, 1, 9] = true := by decide +kernel
theorem subd8_2_237 : subd8_2 [0, 1, 10] = true := by decide +kernel
theorem subd8_2_238 : subd8_2 [0, 2, -8] = true := by decide +kernel
theorem subd8_2_239 : subd8_2 [0, 2, -7] = true := by decide +kernel
theorem subd8_2_240 : subd8_2 [0, 2, -6] = true := by decide +kernel
theorem subd8_2_241 : subd8_2 [0, 2, -5] = true := by decide +kernel
theorem subd8_2_242 : subd8_2 [0, 2, -4] = true := by decide +kernel
theorem subd8_2_243 : subd8_2 [0, 2, -3] = true := by decide +kernel
theorem subd8_2_244 : subd8_2 [0, 2, -2] = true := by decide +kernel
theorem subd8_2_245 : subd8_2 [0, 2, -1] = true := by decide +kernel
theorem subd8_2_246 : subd8_2 [0, 2, 0] = true := by decide +kernel
theorem subd8_2_247 : subd8_2 [0, 2, 1] = true := by decide +kernel
theorem subd8_2_248 : subd8_2 [0, 2, 2] = true := by decide +kernel
theorem subd8_2_249 : subd8_2 [0, 2, 3] = true := by decide +kernel
theorem subd8_2_250 : subd8_2 [0, 2, 4] = true := by decide +kernel
theorem subd8_2_251 : subd8_2 [0, 2, 5] = true := by decide +kernel
theorem subd8_2_252 : subd8_2 [0, 2, 6] = true := by decide +kernel
theorem subd8_2_253 : subd8_2 [0, 2, 7] = true := by decide +kernel
theorem subd8_2_254 : subd8_2 [0, 2, 8] = true := by decide +kernel
theorem subd8_2_255 : subd8_2 [0, 2, 9] = true := by decide +kernel
theorem sbd8_2_7 : ∀ q ∈ blkd8_2_7, subd8_2 q = true := by
  unfold blkd8_2_7
  exact List.forall_mem_cons.2 ⟨subd8_2_224, List.forall_mem_cons.2 ⟨subd8_2_225, List.forall_mem_cons.2 ⟨subd8_2_226, List.forall_mem_cons.2 ⟨subd8_2_227, List.forall_mem_cons.2 ⟨subd8_2_228, List.forall_mem_cons.2 ⟨subd8_2_229, List.forall_mem_cons.2 ⟨subd8_2_230, List.forall_mem_cons.2 ⟨subd8_2_231, List.forall_mem_cons.2 ⟨subd8_2_232, List.forall_mem_cons.2 ⟨subd8_2_233, List.forall_mem_cons.2 ⟨subd8_2_234, List.forall_mem_cons.2 ⟨subd8_2_235, List.forall_mem_cons.2 ⟨subd8_2_236, List.forall_mem_cons.2 ⟨subd8_2_237, List.forall_mem_cons.2 ⟨subd8_2_238, List.forall_mem_cons.2 ⟨subd8_2_239, List.forall_mem_cons.2 ⟨subd8_2_240, List.forall_mem_cons.2 ⟨subd8_2_241, List.forall_mem_cons.2 ⟨subd8_2_242, List.forall_mem_cons.2 ⟨subd8_2_243, List.forall_mem_cons.2 ⟨subd8_2_244, List.forall_mem_cons.2 ⟨subd8_2_245, List.forall_mem_cons.2 ⟨subd8_2_246, List.forall_mem_cons.2 ⟨subd8_2_247, List.forall_mem_cons.2 ⟨subd8_2_248, List.forall_mem_cons.2 ⟨subd8_2_249, List.forall_mem_cons.2 ⟨subd8_2_250, List.forall_mem_cons.2 ⟨subd8_2_251, List.forall_mem_cons.2 ⟨subd8_2_252, List.forall_mem_cons.2 ⟨subd8_2_253, List.forall_mem_cons.2 ⟨subd8_2_254, List.forall_mem_cons.2 ⟨subd8_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_256 : subd8_2 [0, 3] = true := by decide +kernel
theorem subd8_2_257 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_258 : subd8_2 [1, -2, -8] = true := by decide +kernel
theorem subd8_2_259 : subd8_2 [1, -2, -7] = true := by decide +kernel
theorem subd8_2_260 : subd8_2 [1, -2, -6] = true := by decide +kernel
theorem subd8_2_261 : subd8_2 [1, -2, -5] = true := by decide +kernel
theorem subd8_2_262 : subd8_2 [1, -2, -4] = true := by decide +kernel
theorem subd8_2_263 : subd8_2 [1, -2, -3] = true := by decide +kernel
theorem subd8_2_264 : subd8_2 [1, -2, -2] = true := by decide +kernel
theorem subd8_2_265 : subd8_2 [1, -2, -1] = true := by decide +kernel
theorem subd8_2_266 : subd8_2 [1, -2, 0] = true := by decide +kernel
theorem subd8_2_267 : subd8_2 [1, -2, 1] = true := by decide +kernel
theorem subd8_2_268 : subd8_2 [1, -2, 2] = true := by decide +kernel
theorem subd8_2_269 : subd8_2 [1, -2, 3] = true := by decide +kernel
theorem subd8_2_270 : subd8_2 [1, -2, 4] = true := by decide +kernel
theorem subd8_2_271 : subd8_2 [1, -2, 5] = true := by decide +kernel
theorem subd8_2_272 : subd8_2 [1, -2, 6] = true := by decide +kernel
theorem subd8_2_273 : subd8_2 [1, -2, 7] = true := by decide +kernel
theorem subd8_2_274 : subd8_2 [1, -1, -11] = true := by decide +kernel
theorem subd8_2_275 : subd8_2 [1, -1, -10] = true := by decide +kernel
theorem subd8_2_276 : subd8_2 [1, -1, -9] = true := by decide +kernel
theorem subd8_2_277 : subd8_2 [1, -1, -8] = true := by decide +kernel
theorem subd8_2_278 : subd8_2 [1, -1, -7] = true := by decide +kernel
theorem subd8_2_279 : subd8_2 [1, -1, -6] = true := by decide +kernel
theorem subd8_2_280 : subd8_2 [1, -1, -5] = true := by decide +kernel
theorem subd8_2_281 : subd8_2 [1, -1, -4] = true := by decide +kernel
theorem subd8_2_282 : subd8_2 [1, -1, -3] = true := by decide +kernel
theorem subd8_2_283 : subd8_2 [1, -1, -2] = true := by decide +kernel
theorem subd8_2_284 : subd8_2 [1, -1, -1] = true := by decide +kernel
theorem subd8_2_285 : subd8_2 [1, -1, 0] = true := by decide +kernel
theorem subd8_2_286 : subd8_2 [1, -1, 1] = true := by decide +kernel
theorem subd8_2_287 : subd8_2 [1, -1, 2] = true := by decide +kernel
theorem sbd8_2_8 : ∀ q ∈ blkd8_2_8, subd8_2 q = true := by
  unfold blkd8_2_8
  exact List.forall_mem_cons.2 ⟨subd8_2_256, List.forall_mem_cons.2 ⟨subd8_2_257, List.forall_mem_cons.2 ⟨subd8_2_258, List.forall_mem_cons.2 ⟨subd8_2_259, List.forall_mem_cons.2 ⟨subd8_2_260, List.forall_mem_cons.2 ⟨subd8_2_261, List.forall_mem_cons.2 ⟨subd8_2_262, List.forall_mem_cons.2 ⟨subd8_2_263, List.forall_mem_cons.2 ⟨subd8_2_264, List.forall_mem_cons.2 ⟨subd8_2_265, List.forall_mem_cons.2 ⟨subd8_2_266, List.forall_mem_cons.2 ⟨subd8_2_267, List.forall_mem_cons.2 ⟨subd8_2_268, List.forall_mem_cons.2 ⟨subd8_2_269, List.forall_mem_cons.2 ⟨subd8_2_270, List.forall_mem_cons.2 ⟨subd8_2_271, List.forall_mem_cons.2 ⟨subd8_2_272, List.forall_mem_cons.2 ⟨subd8_2_273, List.forall_mem_cons.2 ⟨subd8_2_274, List.forall_mem_cons.2 ⟨subd8_2_275, List.forall_mem_cons.2 ⟨subd8_2_276, List.forall_mem_cons.2 ⟨subd8_2_277, List.forall_mem_cons.2 ⟨subd8_2_278, List.forall_mem_cons.2 ⟨subd8_2_279, List.forall_mem_cons.2 ⟨subd8_2_280, List.forall_mem_cons.2 ⟨subd8_2_281, List.forall_mem_cons.2 ⟨subd8_2_282, List.forall_mem_cons.2 ⟨subd8_2_283, List.forall_mem_cons.2 ⟨subd8_2_284, List.forall_mem_cons.2 ⟨subd8_2_285, List.forall_mem_cons.2 ⟨subd8_2_286, List.forall_mem_cons.2 ⟨subd8_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C111
