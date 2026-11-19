import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-4] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-3] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-2, -3] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-2, -2] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-2, -1] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-2, 0] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [-2, 1] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [-2, 2] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [-2, 3] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [-2, 4] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [-1, -4] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [-1, -3] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [-1, -1] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [-1, 0] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [-1, 3] = true := by decide +kernel
theorem subd5_7_18 : subd5_7 [-1, 4] = true := by decide +kernel
theorem subd5_7_19 : subd5_7 [0, -4] = true := by decide +kernel
theorem subd5_7_20 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_21 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_22 : subd5_7 [0, -1] = true := by decide +kernel
theorem subd5_7_23 : subd5_7 [0, 0] = true := by decide +kernel
theorem subd5_7_24 : subd5_7 [0, 1] = true := by decide +kernel
theorem subd5_7_25 : subd5_7 [0, 2] = true := by decide +kernel
theorem subd5_7_26 : subd5_7 [0, 3] = true := by decide +kernel
theorem subd5_7_27 : subd5_7 [1, -5] = true := by decide +kernel
theorem subd5_7_28 : subd5_7 [1, -4] = true := by decide +kernel
theorem subd5_7_29 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_30 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_31 : subd5_7 [1, -1] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_cons.2 ⟨subd5_7_18, List.forall_mem_cons.2 ⟨subd5_7_19, List.forall_mem_cons.2 ⟨subd5_7_20, List.forall_mem_cons.2 ⟨subd5_7_21, List.forall_mem_cons.2 ⟨subd5_7_22, List.forall_mem_cons.2 ⟨subd5_7_23, List.forall_mem_cons.2 ⟨subd5_7_24, List.forall_mem_cons.2 ⟨subd5_7_25, List.forall_mem_cons.2 ⟨subd5_7_26, List.forall_mem_cons.2 ⟨subd5_7_27, List.forall_mem_cons.2 ⟨subd5_7_28, List.forall_mem_cons.2 ⟨subd5_7_29, List.forall_mem_cons.2 ⟨subd5_7_30, List.forall_mem_cons.2 ⟨subd5_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_32 : subd5_7 [1, 0] = true := by decide +kernel
theorem subd5_7_33 : subd5_7 [1, 1] = true := by decide +kernel
theorem subd5_7_34 : subd5_7 [1, 2] = true := by decide +kernel
theorem subd5_7_35 : subd5_7 [1, 3] = true := by decide +kernel
theorem subd5_7_36 : subd5_7 [2, -5] = true := by decide +kernel
theorem subd5_7_37 : subd5_7 [2, -4] = true := by decide +kernel
theorem subd5_7_38 : subd5_7 [2, -3] = true := by decide +kernel
theorem subd5_7_39 : subd5_7 [2, -2] = true := by decide +kernel
theorem subd5_7_40 : subd5_7 [2, -1] = true := by decide +kernel
theorem subd5_7_41 : subd5_7 [2, 0] = true := by decide +kernel
theorem subd5_7_42 : subd5_7 [2, 1] = true := by decide +kernel
theorem subd5_7_43 : subd5_7 [2, 2] = true := by decide +kernel
theorem subd5_7_44 : subd5_7 [3] = true := by decide +kernel
theorem subd5_7_45 : subd5_7 [4] = true := by decide +kernel
theorem sbd5_7_1 : ∀ q ∈ blkd5_7_1, subd5_7 q = true := by
  unfold blkd5_7_1
  exact List.forall_mem_cons.2 ⟨subd5_7_32, List.forall_mem_cons.2 ⟨subd5_7_33, List.forall_mem_cons.2 ⟨subd5_7_34, List.forall_mem_cons.2 ⟨subd5_7_35, List.forall_mem_cons.2 ⟨subd5_7_36, List.forall_mem_cons.2 ⟨subd5_7_37, List.forall_mem_cons.2 ⟨subd5_7_38, List.forall_mem_cons.2 ⟨subd5_7_39, List.forall_mem_cons.2 ⟨subd5_7_40, List.forall_mem_cons.2 ⟨subd5_7_41, List.forall_mem_cons.2 ⟨subd5_7_42, List.forall_mem_cons.2 ⟨subd5_7_43, List.forall_mem_cons.2 ⟨subd5_7_44, List.forall_mem_cons.2 ⟨subd5_7_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_8 : ldCheck G d5_8.U d5_8.ms ldd5_8 = true := by decide +kernel
theorem pre_okd5_8 : subPre G cell5 d5_8 = true := by decide +kernel
theorem subd5_8_0 : subd5_8 [-1, -2] = true := by decide +kernel
theorem subd5_8_1 : subd5_8 [-1, -1, -8] = true := by decide +kernel
theorem subd5_8_2 : subd5_8 [-1, -1, -7] = true := by decide +kernel
theorem subd5_8_3 : subd5_8 [-1, -1, -6] = true := by decide +kernel
theorem subd5_8_4 : subd5_8 [-1, -1, -5] = true := by decide +kernel
theorem subd5_8_5 : subd5_8 [-1, -1, -4] = true := by decide +kernel
theorem subd5_8_6 : subd5_8 [-1, -1, -3] = true := by decide +kernel
theorem subd5_8_7 : subd5_8 [-1, -1, -2] = true := by decide +kernel
theorem subd5_8_8 : subd5_8 [-1, -1, -1] = true := by decide +kernel
theorem subd5_8_9 : subd5_8 [-1, -1, 0] = true := by decide +kernel
theorem subd5_8_10 : subd5_8 [-1, -1, 1] = true := by decide +kernel
theorem subd5_8_11 : subd5_8 [-1, -1, 2] = true := by decide +kernel
theorem subd5_8_12 : subd5_8 [-1, -1, 3] = true := by decide +kernel
theorem subd5_8_13 : subd5_8 [-1, -1, 4] = true := by decide +kernel
theorem subd5_8_14 : subd5_8 [-1, -1, 5] = true := by decide +kernel
theorem subd5_8_15 : subd5_8 [-1, -1, 6] = true := by decide +kernel
theorem subd5_8_16 : subd5_8 [-1, -1, 7] = true := by decide +kernel
theorem subd5_8_17 : subd5_8 [-1, 0, -11] = true := by decide +kernel
theorem subd5_8_18 : subd5_8 [-1, 0, -10] = true := by decide +kernel
theorem subd5_8_19 : subd5_8 [-1, 0, -9] = true := by decide +kernel
theorem subd5_8_20 : subd5_8 [-1, 0, -8] = true := by decide +kernel
theorem subd5_8_21 : subd5_8 [-1, 0, -7] = true := by decide +kernel
theorem subd5_8_22 : subd5_8 [-1, 0, -6] = true := by decide +kernel
theorem subd5_8_23 : subd5_8 [-1, 0, -5] = true := by decide +kernel
theorem subd5_8_24 : subd5_8 [-1, 0, -4] = true := by decide +kernel
theorem subd5_8_25 : subd5_8 [-1, 0, -3] = true := by decide +kernel
theorem subd5_8_26 : subd5_8 [-1, 0, -2] = true := by decide +kernel
theorem subd5_8_27 : subd5_8 [-1, 0, -1] = true := by decide +kernel
theorem subd5_8_28 : subd5_8 [-1, 0, 0] = true := by decide +kernel
theorem subd5_8_29 : subd5_8 [-1, 0, 1] = true := by decide +kernel
theorem subd5_8_30 : subd5_8 [-1, 0, 2] = true := by decide +kernel
theorem subd5_8_31 : subd5_8 [-1, 0, 3] = true := by decide +kernel
theorem sbd5_8_0 : ∀ q ∈ blkd5_8_0, subd5_8 q = true := by
  unfold blkd5_8_0
  exact List.forall_mem_cons.2 ⟨subd5_8_0, List.forall_mem_cons.2 ⟨subd5_8_1, List.forall_mem_cons.2 ⟨subd5_8_2, List.forall_mem_cons.2 ⟨subd5_8_3, List.forall_mem_cons.2 ⟨subd5_8_4, List.forall_mem_cons.2 ⟨subd5_8_5, List.forall_mem_cons.2 ⟨subd5_8_6, List.forall_mem_cons.2 ⟨subd5_8_7, List.forall_mem_cons.2 ⟨subd5_8_8, List.forall_mem_cons.2 ⟨subd5_8_9, List.forall_mem_cons.2 ⟨subd5_8_10, List.forall_mem_cons.2 ⟨subd5_8_11, List.forall_mem_cons.2 ⟨subd5_8_12, List.forall_mem_cons.2 ⟨subd5_8_13, List.forall_mem_cons.2 ⟨subd5_8_14, List.forall_mem_cons.2 ⟨subd5_8_15, List.forall_mem_cons.2 ⟨subd5_8_16, List.forall_mem_cons.2 ⟨subd5_8_17, List.forall_mem_cons.2 ⟨subd5_8_18, List.forall_mem_cons.2 ⟨subd5_8_19, List.forall_mem_cons.2 ⟨subd5_8_20, List.forall_mem_cons.2 ⟨subd5_8_21, List.forall_mem_cons.2 ⟨subd5_8_22, List.forall_mem_cons.2 ⟨subd5_8_23, List.forall_mem_cons.2 ⟨subd5_8_24, List.forall_mem_cons.2 ⟨subd5_8_25, List.forall_mem_cons.2 ⟨subd5_8_26, List.forall_mem_cons.2 ⟨subd5_8_27, List.forall_mem_cons.2 ⟨subd5_8_28, List.forall_mem_cons.2 ⟨subd5_8_29, List.forall_mem_cons.2 ⟨subd5_8_30, List.forall_mem_cons.2 ⟨subd5_8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_8_32 : subd5_8 [-1, 0, 4] = true := by decide +kernel
theorem subd5_8_33 : subd5_8 [-1, 0, 5] = true := by decide +kernel
theorem subd5_8_34 : subd5_8 [-1, 0, 6] = true := by decide +kernel
theorem subd5_8_35 : subd5_8 [-1, 0, 7] = true := by decide +kernel
theorem subd5_8_36 : subd5_8 [-1, 0, 8] = true := by decide +kernel
theorem subd5_8_37 : subd5_8 [-1, 0, 9] = true := by decide +kernel
theorem subd5_8_38 : subd5_8 [-1, 0, 10] = true := by decide +kernel
theorem subd5_8_39 : subd5_8 [-1, 0, 11] = true := by decide +kernel
theorem subd5_8_40 : subd5_8 [0, -2] = true := by decide +kernel
theorem subd5_8_41 : subd5_8 [0, -1, -13] = true := by decide +kernel
theorem subd5_8_42 : subd5_8 [0, -1, -12] = true := by decide +kernel
theorem subd5_8_43 : subd5_8 [0, -1, -11] = true := by decide +kernel
theorem subd5_8_44 : subd5_8 [0, -1, -10] = true := by decide +kernel
theorem subd5_8_45 : subd5_8 [0, -1, -9] = true := by decide +kernel
theorem subd5_8_46 : subd5_8 [0, -1, -8] = true := by decide +kernel
theorem subd5_8_47 : subd5_8 [0, -1, -7] = true := by decide +kernel
theorem subd5_8_48 : subd5_8 [0, -1, -6] = true := by decide +kernel
theorem subd5_8_49 : subd5_8 [0, -1, -5] = true := by decide +kernel
theorem subd5_8_50 : subd5_8 [0, -1, -4] = true := by decide +kernel
theorem subd5_8_51 : subd5_8 [0, -1, -3] = true := by decide +kernel
theorem subd5_8_52 : subd5_8 [0, -1, -2] = true := by decide +kernel
theorem subd5_8_53 : subd5_8 [0, -1, -1] = true := by decide +kernel
theorem subd5_8_54 : subd5_8 [0, -1, 0] = true := by decide +kernel
theorem subd5_8_55 : subd5_8 [0, -1, 1] = true := by decide +kernel
theorem subd5_8_56 : subd5_8 [0, -1, 2] = true := by decide +kernel
theorem subd5_8_57 : subd5_8 [0, -1, 3] = true := by decide +kernel
theorem subd5_8_58 : subd5_8 [0, -1, 4] = true := by decide +kernel
theorem subd5_8_59 : subd5_8 [0, -1, 5] = true := by decide +kernel
theorem subd5_8_60 : subd5_8 [0, -1, 6] = true := by decide +kernel
theorem subd5_8_61 : subd5_8 [0, -1, 7] = true := by decide +kernel
theorem subd5_8_62 : subd5_8 [0, -1, 8] = true := by decide +kernel
theorem subd5_8_63 : subd5_8 [0, -1, 9] = true := by decide +kernel
theorem sbd5_8_1 : ∀ q ∈ blkd5_8_1, subd5_8 q = true := by
  unfold blkd5_8_1
  exact List.forall_mem_cons.2 ⟨subd5_8_32, List.forall_mem_cons.2 ⟨subd5_8_33, List.forall_mem_cons.2 ⟨subd5_8_34, List.forall_mem_cons.2 ⟨subd5_8_35, List.forall_mem_cons.2 ⟨subd5_8_36, List.forall_mem_cons.2 ⟨subd5_8_37, List.forall_mem_cons.2 ⟨subd5_8_38, List.forall_mem_cons.2 ⟨subd5_8_39, List.forall_mem_cons.2 ⟨subd5_8_40, List.forall_mem_cons.2 ⟨subd5_8_41, List.forall_mem_cons.2 ⟨subd5_8_42, List.forall_mem_cons.2 ⟨subd5_8_43, List.forall_mem_cons.2 ⟨subd5_8_44, List.forall_mem_cons.2 ⟨subd5_8_45, List.forall_mem_cons.2 ⟨subd5_8_46, List.forall_mem_cons.2 ⟨subd5_8_47, List.forall_mem_cons.2 ⟨subd5_8_48, List.forall_mem_cons.2 ⟨subd5_8_49, List.forall_mem_cons.2 ⟨subd5_8_50, List.forall_mem_cons.2 ⟨subd5_8_51, List.forall_mem_cons.2 ⟨subd5_8_52, List.forall_mem_cons.2 ⟨subd5_8_53, List.forall_mem_cons.2 ⟨subd5_8_54, List.forall_mem_cons.2 ⟨subd5_8_55, List.forall_mem_cons.2 ⟨subd5_8_56, List.forall_mem_cons.2 ⟨subd5_8_57, List.forall_mem_cons.2 ⟨subd5_8_58, List.forall_mem_cons.2 ⟨subd5_8_59, List.forall_mem_cons.2 ⟨subd5_8_60, List.forall_mem_cons.2 ⟨subd5_8_61, List.forall_mem_cons.2 ⟨subd5_8_62, List.forall_mem_cons.2 ⟨subd5_8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_8_64 : subd5_8 [0, -1, 10] = true := by decide +kernel
theorem subd5_8_65 : subd5_8 [0, -1, 11] = true := by decide +kernel
theorem subd5_8_66 : subd5_8 [0, 0, -16] = true := by decide +kernel
theorem subd5_8_67 : subd5_8 [0, 0, -15] = true := by decide +kernel
theorem subd5_8_68 : subd5_8 [0, 0, -14] = true := by decide +kernel
theorem subd5_8_69 : subd5_8 [0, 0, -13] = true := by decide +kernel
theorem subd5_8_70 : subd5_8 [0, 0, -12] = true := by decide +kernel
theorem subd5_8_71 : subd5_8 [0, 0, -11] = true := by decide +kernel
theorem subd5_8_72 : subd5_8 [0, 0, -10] = true := by decide +kernel
theorem subd5_8_73 : subd5_8 [0, 0, -9] = true := by decide +kernel
theorem subd5_8_74 : subd5_8 [0, 0, -8] = true := by decide +kernel
theorem subd5_8_75 : subd5_8 [0, 0, -7] = true := by decide +kernel
theorem subd5_8_76 : subd5_8 [0, 0, -6] = true := by decide +kernel
theorem subd5_8_77 : subd5_8 [0, 0, -5] = true := by decide +kernel
theorem subd5_8_78 : subd5_8 [0, 0, -4] = true := by decide +kernel
theorem subd5_8_79 : subd5_8 [0, 0, -3] = true := by decide +kernel
theorem subd5_8_80 : subd5_8 [0, 0, -2] = true := by decide +kernel
theorem subd5_8_81 : subd5_8 [0, 0, -1] = true := by decide +kernel
theorem subd5_8_82 : subd5_8 [0, 0, 0] = true := by decide +kernel
theorem subd5_8_83 : subd5_8 [0, 0, 1] = true := by decide +kernel
theorem subd5_8_84 : subd5_8 [0, 0, 2] = true := by decide +kernel
theorem subd5_8_85 : subd5_8 [0, 0, 3] = true := by decide +kernel
theorem subd5_8_86 : subd5_8 [0, 0, 4] = true := by decide +kernel
theorem subd5_8_87 : subd5_8 [0, 0, 5] = true := by decide +kernel
theorem subd5_8_88 : subd5_8 [0, 0, 6] = true := by decide +kernel
theorem subd5_8_89 : subd5_8 [0, 0, 7] = true := by decide +kernel
theorem subd5_8_90 : subd5_8 [0, 0, 8] = true := by decide +kernel
theorem subd5_8_91 : subd5_8 [0, 0, 9] = true := by decide +kernel
theorem subd5_8_92 : subd5_8 [0, 0, 10] = true := by decide +kernel
theorem subd5_8_93 : subd5_8 [0, 0, 11] = true := by decide +kernel
theorem subd5_8_94 : subd5_8 [0, 0, 12] = true := by decide +kernel
theorem subd5_8_95 : subd5_8 [0, 0, 13] = true := by decide +kernel
theorem sbd5_8_2 : ∀ q ∈ blkd5_8_2, subd5_8 q = true := by
  unfold blkd5_8_2
  exact List.forall_mem_cons.2 ⟨subd5_8_64, List.forall_mem_cons.2 ⟨subd5_8_65, List.forall_mem_cons.2 ⟨subd5_8_66, List.forall_mem_cons.2 ⟨subd5_8_67, List.forall_mem_cons.2 ⟨subd5_8_68, List.forall_mem_cons.2 ⟨subd5_8_69, List.forall_mem_cons.2 ⟨subd5_8_70, List.forall_mem_cons.2 ⟨subd5_8_71, List.forall_mem_cons.2 ⟨subd5_8_72, List.forall_mem_cons.2 ⟨subd5_8_73, List.forall_mem_cons.2 ⟨subd5_8_74, List.forall_mem_cons.2 ⟨subd5_8_75, List.forall_mem_cons.2 ⟨subd5_8_76, List.forall_mem_cons.2 ⟨subd5_8_77, List.forall_mem_cons.2 ⟨subd5_8_78, List.forall_mem_cons.2 ⟨subd5_8_79, List.forall_mem_cons.2 ⟨subd5_8_80, List.forall_mem_cons.2 ⟨subd5_8_81, List.forall_mem_cons.2 ⟨subd5_8_82, List.forall_mem_cons.2 ⟨subd5_8_83, List.forall_mem_cons.2 ⟨subd5_8_84, List.forall_mem_cons.2 ⟨subd5_8_85, List.forall_mem_cons.2 ⟨subd5_8_86, List.forall_mem_cons.2 ⟨subd5_8_87, List.forall_mem_cons.2 ⟨subd5_8_88, List.forall_mem_cons.2 ⟨subd5_8_89, List.forall_mem_cons.2 ⟨subd5_8_90, List.forall_mem_cons.2 ⟨subd5_8_91, List.forall_mem_cons.2 ⟨subd5_8_92, List.forall_mem_cons.2 ⟨subd5_8_93, List.forall_mem_cons.2 ⟨subd5_8_94, List.forall_mem_cons.2 ⟨subd5_8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_8_96 : subd5_8 [0, 0, 14] = true := by decide +kernel
theorem subd5_8_97 : subd5_8 [0, 0, 15] = true := by decide +kernel
theorem subd5_8_98 : subd5_8 [0, 1, -12] = true := by decide +kernel
theorem subd5_8_99 : subd5_8 [0, 1, -11] = true := by decide +kernel
theorem subd5_8_100 : subd5_8 [0, 1, -10] = true := by decide +kernel
theorem subd5_8_101 : subd5_8 [0, 1, -9] = true := by decide +kernel
theorem subd5_8_102 : subd5_8 [0, 1, -8] = true := by decide +kernel
theorem subd5_8_103 : subd5_8 [0, 1, -7] = true := by decide +kernel
theorem subd5_8_104 : subd5_8 [0, 1, -6] = true := by decide +kernel
theorem subd5_8_105 : subd5_8 [0, 1, -5] = true := by decide +kernel
theorem subd5_8_106 : subd5_8 [0, 1, -4] = true := by decide +kernel
theorem subd5_8_107 : subd5_8 [0, 1, -3] = true := by decide +kernel
theorem subd5_8_108 : subd5_8 [0, 1, -2] = true := by decide +kernel
theorem subd5_8_109 : subd5_8 [0, 1, -1] = true := by decide +kernel
theorem subd5_8_110 : subd5_8 [0, 1, 0] = true := by decide +kernel
theorem subd5_8_111 : subd5_8 [0, 1, 1] = true := by decide +kernel
theorem subd5_8_112 : subd5_8 [0, 1, 2] = true := by decide +kernel
theorem subd5_8_113 : subd5_8 [0, 1, 3] = true := by decide +kernel
theorem subd5_8_114 : subd5_8 [0, 1, 4] = true := by decide +kernel
theorem subd5_8_115 : subd5_8 [0, 1, 5] = true := by decide +kernel
theorem subd5_8_116 : subd5_8 [0, 1, 6] = true := by decide +kernel
theorem subd5_8_117 : subd5_8 [0, 1, 7] = true := by decide +kernel
theorem subd5_8_118 : subd5_8 [0, 1, 8] = true := by decide +kernel
theorem subd5_8_119 : subd5_8 [0, 1, 9] = true := by decide +kernel
theorem subd5_8_120 : subd5_8 [0, 1, 10] = true := by decide +kernel
theorem subd5_8_121 : subd5_8 [0, 1, 11] = true := by decide +kernel
theorem subd5_8_122 : subd5_8 [0, 1, 12] = true := by decide +kernel
theorem subd5_8_123 : subd5_8 [1, -1] = true := by decide +kernel
theorem subd5_8_124 : subd5_8 [1, 0, -12] = true := by decide +kernel
theorem subd5_8_125 : subd5_8 [1, 0, -11] = true := by decide +kernel
theorem subd5_8_126 : subd5_8 [1, 0, -10] = true := by decide +kernel
theorem subd5_8_127 : subd5_8 [1, 0, -9] = true := by decide +kernel
theorem sbd5_8_3 : ∀ q ∈ blkd5_8_3, subd5_8 q = true := by
  unfold blkd5_8_3
  exact List.forall_mem_cons.2 ⟨subd5_8_96, List.forall_mem_cons.2 ⟨subd5_8_97, List.forall_mem_cons.2 ⟨subd5_8_98, List.forall_mem_cons.2 ⟨subd5_8_99, List.forall_mem_cons.2 ⟨subd5_8_100, List.forall_mem_cons.2 ⟨subd5_8_101, List.forall_mem_cons.2 ⟨subd5_8_102, List.forall_mem_cons.2 ⟨subd5_8_103, List.forall_mem_cons.2 ⟨subd5_8_104, List.forall_mem_cons.2 ⟨subd5_8_105, List.forall_mem_cons.2 ⟨subd5_8_106, List.forall_mem_cons.2 ⟨subd5_8_107, List.forall_mem_cons.2 ⟨subd5_8_108, List.forall_mem_cons.2 ⟨subd5_8_109, List.forall_mem_cons.2 ⟨subd5_8_110, List.forall_mem_cons.2 ⟨subd5_8_111, List.forall_mem_cons.2 ⟨subd5_8_112, List.forall_mem_cons.2 ⟨subd5_8_113, List.forall_mem_cons.2 ⟨subd5_8_114, List.forall_mem_cons.2 ⟨subd5_8_115, List.forall_mem_cons.2 ⟨subd5_8_116, List.forall_mem_cons.2 ⟨subd5_8_117, List.forall_mem_cons.2 ⟨subd5_8_118, List.forall_mem_cons.2 ⟨subd5_8_119, List.forall_mem_cons.2 ⟨subd5_8_120, List.forall_mem_cons.2 ⟨subd5_8_121, List.forall_mem_cons.2 ⟨subd5_8_122, List.forall_mem_cons.2 ⟨subd5_8_123, List.forall_mem_cons.2 ⟨subd5_8_124, List.forall_mem_cons.2 ⟨subd5_8_125, List.forall_mem_cons.2 ⟨subd5_8_126, List.forall_mem_cons.2 ⟨subd5_8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_8_128 : subd5_8 [1, 0, -8] = true := by decide +kernel
theorem subd5_8_129 : subd5_8 [1, 0, -7] = true := by decide +kernel
theorem subd5_8_130 : subd5_8 [1, 0, -6] = true := by decide +kernel
theorem subd5_8_131 : subd5_8 [1, 0, -5] = true := by decide +kernel
theorem subd5_8_132 : subd5_8 [1, 0, -4] = true := by decide +kernel
theorem subd5_8_133 : subd5_8 [1, 0, -3] = true := by decide +kernel
theorem subd5_8_134 : subd5_8 [1, 0, -2] = true := by decide +kernel
theorem subd5_8_135 : subd5_8 [1, 0, -1] = true := by decide +kernel
theorem subd5_8_136 : subd5_8 [1, 0, 0] = true := by decide +kernel
theorem subd5_8_137 : subd5_8 [1, 0, 1] = true := by decide +kernel
theorem subd5_8_138 : subd5_8 [1, 0, 2] = true := by decide +kernel
theorem subd5_8_139 : subd5_8 [1, 0, 3] = true := by decide +kernel
theorem subd5_8_140 : subd5_8 [1, 0, 4] = true := by decide +kernel
theorem subd5_8_141 : subd5_8 [1, 0, 5] = true := by decide +kernel
theorem subd5_8_142 : subd5_8 [1, 0, 6] = true := by decide +kernel
theorem subd5_8_143 : subd5_8 [1, 0, 7] = true := by decide +kernel
theorem subd5_8_144 : subd5_8 [1, 0, 8] = true := by decide +kernel
theorem subd5_8_145 : subd5_8 [1, 0, 9] = true := by decide +kernel
theorem subd5_8_146 : subd5_8 [1, 0, 10] = true := by decide +kernel
theorem subd5_8_147 : subd5_8 [1, 1, -8] = true := by decide +kernel
theorem subd5_8_148 : subd5_8 [1, 1, -7] = true := by decide +kernel
theorem subd5_8_149 : subd5_8 [1, 1, -6] = true := by decide +kernel
theorem subd5_8_150 : subd5_8 [1, 1, -5] = true := by decide +kernel
theorem subd5_8_151 : subd5_8 [1, 1, -4] = true := by decide +kernel
theorem subd5_8_152 : subd5_8 [1, 1, -3] = true := by decide +kernel
theorem subd5_8_153 : subd5_8 [1, 1, -2] = true := by decide +kernel
theorem subd5_8_154 : subd5_8 [1, 1, -1] = true := by decide +kernel
theorem subd5_8_155 : subd5_8 [1, 1, 0] = true := by decide +kernel
theorem subd5_8_156 : subd5_8 [1, 1, 1] = true := by decide +kernel
theorem subd5_8_157 : subd5_8 [1, 1, 2] = true := by decide +kernel
theorem subd5_8_158 : subd5_8 [1, 1, 3] = true := by decide +kernel
theorem subd5_8_159 : subd5_8 [1, 1, 4] = true := by decide +kernel
theorem sbd5_8_4 : ∀ q ∈ blkd5_8_4, subd5_8 q = true := by
  unfold blkd5_8_4
  exact List.forall_mem_cons.2 ⟨subd5_8_128, List.forall_mem_cons.2 ⟨subd5_8_129, List.forall_mem_cons.2 ⟨subd5_8_130, List.forall_mem_cons.2 ⟨subd5_8_131, List.forall_mem_cons.2 ⟨subd5_8_132, List.forall_mem_cons.2 ⟨subd5_8_133, List.forall_mem_cons.2 ⟨subd5_8_134, List.forall_mem_cons.2 ⟨subd5_8_135, List.forall_mem_cons.2 ⟨subd5_8_136, List.forall_mem_cons.2 ⟨subd5_8_137, List.forall_mem_cons.2 ⟨subd5_8_138, List.forall_mem_cons.2 ⟨subd5_8_139, List.forall_mem_cons.2 ⟨subd5_8_140, List.forall_mem_cons.2 ⟨subd5_8_141, List.forall_mem_cons.2 ⟨subd5_8_142, List.forall_mem_cons.2 ⟨subd5_8_143, List.forall_mem_cons.2 ⟨subd5_8_144, List.forall_mem_cons.2 ⟨subd5_8_145, List.forall_mem_cons.2 ⟨subd5_8_146, List.forall_mem_cons.2 ⟨subd5_8_147, List.forall_mem_cons.2 ⟨subd5_8_148, List.forall_mem_cons.2 ⟨subd5_8_149, List.forall_mem_cons.2 ⟨subd5_8_150, List.forall_mem_cons.2 ⟨subd5_8_151, List.forall_mem_cons.2 ⟨subd5_8_152, List.forall_mem_cons.2 ⟨subd5_8_153, List.forall_mem_cons.2 ⟨subd5_8_154, List.forall_mem_cons.2 ⟨subd5_8_155, List.forall_mem_cons.2 ⟨subd5_8_156, List.forall_mem_cons.2 ⟨subd5_8_157, List.forall_mem_cons.2 ⟨subd5_8_158, List.forall_mem_cons.2 ⟨subd5_8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_8_160 : subd5_8 [1, 1, 5] = true := by decide +kernel
theorem subd5_8_161 : subd5_8 [1, 1, 6] = true := by decide +kernel
theorem subd5_8_162 : subd5_8 [1, 1, 7] = true := by decide +kernel
theorem sbd5_8_5 : ∀ q ∈ blkd5_8_5, subd5_8 q = true := by
  unfold blkd5_8_5
  exact List.forall_mem_cons.2 ⟨subd5_8_160, List.forall_mem_cons.2 ⟨subd5_8_161, List.forall_mem_cons.2 ⟨subd5_8_162, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd5_9 : ldCheck G d5_9.U d5_9.ms ldd5_9 = true := by decide +kernel
theorem pre_okd5_9 : subPre G cell5 d5_9 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
