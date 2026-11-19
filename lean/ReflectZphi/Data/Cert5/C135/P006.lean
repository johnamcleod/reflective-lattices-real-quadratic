import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_0 : subd5_1 [-3] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-2, -3] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-2, -2] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-2, -1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-2, 0] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-2, 1] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-2, 2] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-2, 3] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-1, -4] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [-1, 3] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [0, -4] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [0, 3] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [1, -4] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [1, 2] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [1, 3] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [2, -4] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [2, -3] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [2, -2] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [2, -1] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [2, 0] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [2, 1] = true := by decide +kernel
theorem subd5_1_38 : subd5_1 [2, 2] = true := by decide +kernel
theorem subd5_1_39 : subd5_1 [3] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_cons.2 ⟨subd5_1_38, List.forall_mem_cons.2 ⟨subd5_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-1, 0, -7] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-1, 0, -6] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-1, 0, -5] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-1, 0, -4] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-1, 0, -3] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-1, 0, -2] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-1, 0, -1] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-1, 0, 0] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-1, 0, 1] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [-1, 0, 2] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [-1, 0, 3] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [-1, 0, 4] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [-1, 0, 5] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [-1, 0, 6] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [0, -1, -7] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [0, -1, -6] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [0, -1, -5] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [0, -1, -4] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [0, -1, -3] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [0, -1, -2] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [0, -1, -1] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [0, -1, 0] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [0, -1, 1] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [0, -1, 2] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [0, -1, 3] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [0, -1, 4] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [0, -1, 5] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [0, -1, 6] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [0, -1, 7] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [0, 0, -8] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [0, 0, -7] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [0, 0, -6] = true := by decide +kernel
theorem subd5_2_44 : subd5_2 [0, 0, -5] = true := by decide +kernel
theorem subd5_2_45 : subd5_2 [0, 0, -4] = true := by decide +kernel
theorem subd5_2_46 : subd5_2 [0, 0, -3] = true := by decide +kernel
theorem subd5_2_47 : subd5_2 [0, 0, -2] = true := by decide +kernel
theorem subd5_2_48 : subd5_2 [0, 0, -1] = true := by decide +kernel
theorem subd5_2_49 : subd5_2 [0, 0, 0] = true := by decide +kernel
theorem subd5_2_50 : subd5_2 [0, 0, 1] = true := by decide +kernel
theorem subd5_2_51 : subd5_2 [0, 0, 2] = true := by decide +kernel
theorem subd5_2_52 : subd5_2 [0, 0, 3] = true := by decide +kernel
theorem subd5_2_53 : subd5_2 [0, 0, 4] = true := by decide +kernel
theorem subd5_2_54 : subd5_2 [0, 0, 5] = true := by decide +kernel
theorem subd5_2_55 : subd5_2 [0, 0, 6] = true := by decide +kernel
theorem subd5_2_56 : subd5_2 [0, 0, 7] = true := by decide +kernel
theorem subd5_2_57 : subd5_2 [0, 1, -8] = true := by decide +kernel
theorem subd5_2_58 : subd5_2 [0, 1, -7] = true := by decide +kernel
theorem subd5_2_59 : subd5_2 [0, 1, -6] = true := by decide +kernel
theorem subd5_2_60 : subd5_2 [0, 1, -5] = true := by decide +kernel
theorem subd5_2_61 : subd5_2 [0, 1, -4] = true := by decide +kernel
theorem subd5_2_62 : subd5_2 [0, 1, -3] = true := by decide +kernel
theorem subd5_2_63 : subd5_2 [0, 1, -2] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_cons.2 ⟨subd5_2_44, List.forall_mem_cons.2 ⟨subd5_2_45, List.forall_mem_cons.2 ⟨subd5_2_46, List.forall_mem_cons.2 ⟨subd5_2_47, List.forall_mem_cons.2 ⟨subd5_2_48, List.forall_mem_cons.2 ⟨subd5_2_49, List.forall_mem_cons.2 ⟨subd5_2_50, List.forall_mem_cons.2 ⟨subd5_2_51, List.forall_mem_cons.2 ⟨subd5_2_52, List.forall_mem_cons.2 ⟨subd5_2_53, List.forall_mem_cons.2 ⟨subd5_2_54, List.forall_mem_cons.2 ⟨subd5_2_55, List.forall_mem_cons.2 ⟨subd5_2_56, List.forall_mem_cons.2 ⟨subd5_2_57, List.forall_mem_cons.2 ⟨subd5_2_58, List.forall_mem_cons.2 ⟨subd5_2_59, List.forall_mem_cons.2 ⟨subd5_2_60, List.forall_mem_cons.2 ⟨subd5_2_61, List.forall_mem_cons.2 ⟨subd5_2_62, List.forall_mem_cons.2 ⟨subd5_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_64 : subd5_2 [0, 1, -1] = true := by decide +kernel
theorem subd5_2_65 : subd5_2 [0, 1, 0] = true := by decide +kernel
theorem subd5_2_66 : subd5_2 [0, 1, 1] = true := by decide +kernel
theorem subd5_2_67 : subd5_2 [0, 1, 2] = true := by decide +kernel
theorem subd5_2_68 : subd5_2 [0, 1, 3] = true := by decide +kernel
theorem subd5_2_69 : subd5_2 [0, 1, 4] = true := by decide +kernel
theorem subd5_2_70 : subd5_2 [0, 1, 5] = true := by decide +kernel
theorem subd5_2_71 : subd5_2 [0, 1, 6] = true := by decide +kernel
theorem subd5_2_72 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_73 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_74 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_75 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_76 : subd5_2 [1, 0, -7] = true := by decide +kernel
theorem subd5_2_77 : subd5_2 [1, 0, -6] = true := by decide +kernel
theorem subd5_2_78 : subd5_2 [1, 0, -5] = true := by decide +kernel
theorem subd5_2_79 : subd5_2 [1, 0, -4] = true := by decide +kernel
theorem subd5_2_80 : subd5_2 [1, 0, -3] = true := by decide +kernel
theorem subd5_2_81 : subd5_2 [1, 0, -2] = true := by decide +kernel
theorem subd5_2_82 : subd5_2 [1, 0, -1] = true := by decide +kernel
theorem subd5_2_83 : subd5_2 [1, 0, 0] = true := by decide +kernel
theorem subd5_2_84 : subd5_2 [1, 0, 1] = true := by decide +kernel
theorem subd5_2_85 : subd5_2 [1, 0, 2] = true := by decide +kernel
theorem subd5_2_86 : subd5_2 [1, 0, 3] = true := by decide +kernel
theorem subd5_2_87 : subd5_2 [1, 0, 4] = true := by decide +kernel
theorem subd5_2_88 : subd5_2 [1, 0, 5] = true := by decide +kernel
theorem subd5_2_89 : subd5_2 [1, 0, 6] = true := by decide +kernel
theorem subd5_2_90 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_91 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_92 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_93 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_94 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_95 : subd5_2 [2, 0] = true := by decide +kernel
theorem sbd5_2_2 : ∀ q ∈ blkd5_2_2, subd5_2 q = true := by
  unfold blkd5_2_2
  exact List.forall_mem_cons.2 ⟨subd5_2_64, List.forall_mem_cons.2 ⟨subd5_2_65, List.forall_mem_cons.2 ⟨subd5_2_66, List.forall_mem_cons.2 ⟨subd5_2_67, List.forall_mem_cons.2 ⟨subd5_2_68, List.forall_mem_cons.2 ⟨subd5_2_69, List.forall_mem_cons.2 ⟨subd5_2_70, List.forall_mem_cons.2 ⟨subd5_2_71, List.forall_mem_cons.2 ⟨subd5_2_72, List.forall_mem_cons.2 ⟨subd5_2_73, List.forall_mem_cons.2 ⟨subd5_2_74, List.forall_mem_cons.2 ⟨subd5_2_75, List.forall_mem_cons.2 ⟨subd5_2_76, List.forall_mem_cons.2 ⟨subd5_2_77, List.forall_mem_cons.2 ⟨subd5_2_78, List.forall_mem_cons.2 ⟨subd5_2_79, List.forall_mem_cons.2 ⟨subd5_2_80, List.forall_mem_cons.2 ⟨subd5_2_81, List.forall_mem_cons.2 ⟨subd5_2_82, List.forall_mem_cons.2 ⟨subd5_2_83, List.forall_mem_cons.2 ⟨subd5_2_84, List.forall_mem_cons.2 ⟨subd5_2_85, List.forall_mem_cons.2 ⟨subd5_2_86, List.forall_mem_cons.2 ⟨subd5_2_87, List.forall_mem_cons.2 ⟨subd5_2_88, List.forall_mem_cons.2 ⟨subd5_2_89, List.forall_mem_cons.2 ⟨subd5_2_90, List.forall_mem_cons.2 ⟨subd5_2_91, List.forall_mem_cons.2 ⟨subd5_2_92, List.forall_mem_cons.2 ⟨subd5_2_93, List.forall_mem_cons.2 ⟨subd5_2_94, List.forall_mem_cons.2 ⟨subd5_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_96 : subd5_2 [2, 1] = true := by decide +kernel
theorem sbd5_2_3 : ∀ q ∈ blkd5_2_3, subd5_2 q = true := by
  unfold blkd5_2_3
  exact List.forall_mem_cons.2 ⟨subd5_2_96, List.forall_mem_nil _⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-4] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-3, -6] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-3, -5] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-3, -4] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-3, -3] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-3, -2] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-3, -1] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-3, 0] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-3, 1] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-3, 2] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-3, 3] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-2, -6] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-2, -5] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-2, -4] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [-2, 3] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [-2, 4] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [-1, -6] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [-1, -5] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [-1, 3] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
