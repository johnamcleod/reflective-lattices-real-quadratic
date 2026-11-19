import ReflectZphi.Data.Cert5.C084.Base

namespace ReflectZphi.Data.Cert5.C084

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_0_32 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_33 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_34 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_35 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_36 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_37 : subd4_0 [0, 3] = true := by decide +kernel
theorem subd4_0_38 : subd4_0 [0, 4] = true := by decide +kernel
theorem subd4_0_39 : subd4_0 [1, -6] = true := by decide +kernel
theorem subd4_0_40 : subd4_0 [1, -5] = true := by decide +kernel
theorem subd4_0_41 : subd4_0 [1, -4] = true := by decide +kernel
theorem subd4_0_42 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_43 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_44 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_45 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_46 : subd4_0 [1, 1] = true := by decide +kernel
theorem subd4_0_47 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_48 : subd4_0 [1, 3] = true := by decide +kernel
theorem subd4_0_49 : subd4_0 [1, 4] = true := by decide +kernel
theorem subd4_0_50 : subd4_0 [2, -6] = true := by decide +kernel
theorem subd4_0_51 : subd4_0 [2, -5] = true := by decide +kernel
theorem subd4_0_52 : subd4_0 [2, -4] = true := by decide +kernel
theorem subd4_0_53 : subd4_0 [2, -3] = true := by decide +kernel
theorem subd4_0_54 : subd4_0 [2, -2] = true := by decide +kernel
theorem subd4_0_55 : subd4_0 [2, -1] = true := by decide +kernel
theorem subd4_0_56 : subd4_0 [2, 0] = true := by decide +kernel
theorem subd4_0_57 : subd4_0 [2, 1] = true := by decide +kernel
theorem subd4_0_58 : subd4_0 [2, 2] = true := by decide +kernel
theorem subd4_0_59 : subd4_0 [2, 3] = true := by decide +kernel
theorem subd4_0_60 : subd4_0 [3, -5] = true := by decide +kernel
theorem subd4_0_61 : subd4_0 [3, -4] = true := by decide +kernel
theorem subd4_0_62 : subd4_0 [3, -3] = true := by decide +kernel
theorem subd4_0_63 : subd4_0 [3, -2] = true := by decide +kernel
theorem sbd4_0_1 : ∀ q ∈ blkd4_0_1, subd4_0 q = true := by
  unfold blkd4_0_1
  exact List.forall_mem_cons.2 ⟨subd4_0_32, List.forall_mem_cons.2 ⟨subd4_0_33, List.forall_mem_cons.2 ⟨subd4_0_34, List.forall_mem_cons.2 ⟨subd4_0_35, List.forall_mem_cons.2 ⟨subd4_0_36, List.forall_mem_cons.2 ⟨subd4_0_37, List.forall_mem_cons.2 ⟨subd4_0_38, List.forall_mem_cons.2 ⟨subd4_0_39, List.forall_mem_cons.2 ⟨subd4_0_40, List.forall_mem_cons.2 ⟨subd4_0_41, List.forall_mem_cons.2 ⟨subd4_0_42, List.forall_mem_cons.2 ⟨subd4_0_43, List.forall_mem_cons.2 ⟨subd4_0_44, List.forall_mem_cons.2 ⟨subd4_0_45, List.forall_mem_cons.2 ⟨subd4_0_46, List.forall_mem_cons.2 ⟨subd4_0_47, List.forall_mem_cons.2 ⟨subd4_0_48, List.forall_mem_cons.2 ⟨subd4_0_49, List.forall_mem_cons.2 ⟨subd4_0_50, List.forall_mem_cons.2 ⟨subd4_0_51, List.forall_mem_cons.2 ⟨subd4_0_52, List.forall_mem_cons.2 ⟨subd4_0_53, List.forall_mem_cons.2 ⟨subd4_0_54, List.forall_mem_cons.2 ⟨subd4_0_55, List.forall_mem_cons.2 ⟨subd4_0_56, List.forall_mem_cons.2 ⟨subd4_0_57, List.forall_mem_cons.2 ⟨subd4_0_58, List.forall_mem_cons.2 ⟨subd4_0_59, List.forall_mem_cons.2 ⟨subd4_0_60, List.forall_mem_cons.2 ⟨subd4_0_61, List.forall_mem_cons.2 ⟨subd4_0_62, List.forall_mem_cons.2 ⟨subd4_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_64 : subd4_0 [3, -1] = true := by decide +kernel
theorem subd4_0_65 : subd4_0 [3, 0] = true := by decide +kernel
theorem subd4_0_66 : subd4_0 [3, 1] = true := by decide +kernel
theorem subd4_0_67 : subd4_0 [4] = true := by decide +kernel
theorem sbd4_0_2 : ∀ q ∈ blkd4_0_2, subd4_0 q = true := by
  unfold blkd4_0_2
  exact List.forall_mem_cons.2 ⟨subd4_0_64, List.forall_mem_cons.2 ⟨subd4_0_65, List.forall_mem_cons.2 ⟨subd4_0_66, List.forall_mem_cons.2 ⟨subd4_0_67, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_nil _⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-2, -3] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-2, -2] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-2, -1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-2, 0] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-2, 1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-2, 2] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [-1, -1, -7] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [-1, -1, -6] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [-1, -1, -5] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [-1, -1, -4] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [-1, -1, -3] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [-1, -1, -2] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [-1, -1, -1] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [-1, -1, 0] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [-1, -1, 1] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [-1, -1, 2] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [-1, -1, 3] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [-1, -1, 4] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [-1, -1, 5] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [-1, -1, 6] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [-1, 0, -8] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [-1, 0, -7] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [-1, 0, -6] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [-1, 0, -5] = true := by decide +kernel
theorem subd5_0_28 : subd5_0 [-1, 0, -4] = true := by decide +kernel
theorem subd5_0_29 : subd5_0 [-1, 0, -3] = true := by decide +kernel
theorem subd5_0_30 : subd5_0 [-1, 0, -2] = true := by decide +kernel
theorem subd5_0_31 : subd5_0 [-1, 0, -1] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_cons.2 ⟨subd5_0_28, List.forall_mem_cons.2 ⟨subd5_0_29, List.forall_mem_cons.2 ⟨subd5_0_30, List.forall_mem_cons.2 ⟨subd5_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_32 : subd5_0 [-1, 0, 0] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [-1, 0, 1] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [-1, 0, 2] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [-1, 0, 3] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [-1, 0, 4] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [-1, 0, 5] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [-1, 0, 6] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [-1, 0, 7] = true := by decide +kernel
theorem subd5_0_40 : subd5_0 [-1, 1, -7] = true := by decide +kernel
theorem subd5_0_41 : subd5_0 [-1, 1, -6] = true := by decide +kernel
theorem subd5_0_42 : subd5_0 [-1, 1, -5] = true := by decide +kernel
theorem subd5_0_43 : subd5_0 [-1, 1, -4] = true := by decide +kernel
theorem subd5_0_44 : subd5_0 [-1, 1, -3] = true := by decide +kernel
theorem subd5_0_45 : subd5_0 [-1, 1, -2] = true := by decide +kernel
theorem subd5_0_46 : subd5_0 [-1, 1, -1] = true := by decide +kernel
theorem subd5_0_47 : subd5_0 [-1, 1, 0] = true := by decide +kernel
theorem subd5_0_48 : subd5_0 [-1, 1, 1] = true := by decide +kernel
theorem subd5_0_49 : subd5_0 [-1, 1, 2] = true := by decide +kernel
theorem subd5_0_50 : subd5_0 [-1, 1, 3] = true := by decide +kernel
theorem subd5_0_51 : subd5_0 [-1, 1, 4] = true := by decide +kernel
theorem subd5_0_52 : subd5_0 [-1, 1, 5] = true := by decide +kernel
theorem subd5_0_53 : subd5_0 [-1, 1, 6] = true := by decide +kernel
theorem subd5_0_54 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_55 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_56 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_57 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_58 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_59 : subd5_0 [0, -1, -8] = true := by decide +kernel
theorem subd5_0_60 : subd5_0 [0, -1, -7] = true := by decide +kernel
theorem subd5_0_61 : subd5_0 [0, -1, -6] = true := by decide +kernel
theorem subd5_0_62 : subd5_0 [0, -1, -5] = true := by decide +kernel
theorem subd5_0_63 : subd5_0 [0, -1, -4] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_cons.2 ⟨subd5_0_40, List.forall_mem_cons.2 ⟨subd5_0_41, List.forall_mem_cons.2 ⟨subd5_0_42, List.forall_mem_cons.2 ⟨subd5_0_43, List.forall_mem_cons.2 ⟨subd5_0_44, List.forall_mem_cons.2 ⟨subd5_0_45, List.forall_mem_cons.2 ⟨subd5_0_46, List.forall_mem_cons.2 ⟨subd5_0_47, List.forall_mem_cons.2 ⟨subd5_0_48, List.forall_mem_cons.2 ⟨subd5_0_49, List.forall_mem_cons.2 ⟨subd5_0_50, List.forall_mem_cons.2 ⟨subd5_0_51, List.forall_mem_cons.2 ⟨subd5_0_52, List.forall_mem_cons.2 ⟨subd5_0_53, List.forall_mem_cons.2 ⟨subd5_0_54, List.forall_mem_cons.2 ⟨subd5_0_55, List.forall_mem_cons.2 ⟨subd5_0_56, List.forall_mem_cons.2 ⟨subd5_0_57, List.forall_mem_cons.2 ⟨subd5_0_58, List.forall_mem_cons.2 ⟨subd5_0_59, List.forall_mem_cons.2 ⟨subd5_0_60, List.forall_mem_cons.2 ⟨subd5_0_61, List.forall_mem_cons.2 ⟨subd5_0_62, List.forall_mem_cons.2 ⟨subd5_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_64 : subd5_0 [0, -1, -3] = true := by decide +kernel
theorem subd5_0_65 : subd5_0 [0, -1, -2] = true := by decide +kernel
theorem subd5_0_66 : subd5_0 [0, -1, -1] = true := by decide +kernel
theorem subd5_0_67 : subd5_0 [0, -1, 0] = true := by decide +kernel
theorem subd5_0_68 : subd5_0 [0, -1, 1] = true := by decide +kernel
theorem subd5_0_69 : subd5_0 [0, -1, 2] = true := by decide +kernel
theorem subd5_0_70 : subd5_0 [0, -1, 3] = true := by decide +kernel
theorem subd5_0_71 : subd5_0 [0, -1, 4] = true := by decide +kernel
theorem subd5_0_72 : subd5_0 [0, -1, 5] = true := by decide +kernel
theorem subd5_0_73 : subd5_0 [0, -1, 6] = true := by decide +kernel
theorem subd5_0_74 : subd5_0 [0, -1, 7] = true := by decide +kernel
theorem subd5_0_75 : subd5_0 [0, 0, -8] = true := by decide +kernel
theorem subd5_0_76 : subd5_0 [0, 0, -7] = true := by decide +kernel
theorem subd5_0_77 : subd5_0 [0, 0, -6] = true := by decide +kernel
theorem subd5_0_78 : subd5_0 [0, 0, -5] = true := by decide +kernel
theorem subd5_0_79 : subd5_0 [0, 0, -4] = true := by decide +kernel
theorem subd5_0_80 : subd5_0 [0, 0, -3] = true := by decide +kernel
theorem subd5_0_81 : subd5_0 [0, 0, -2] = true := by decide +kernel
theorem subd5_0_82 : subd5_0 [0, 0, -1] = true := by decide +kernel
theorem subd5_0_83 : subd5_0 [0, 0, 0] = true := by decide +kernel
theorem subd5_0_84 : subd5_0 [0, 0, 1] = true := by decide +kernel
theorem subd5_0_85 : subd5_0 [0, 0, 2] = true := by decide +kernel
theorem subd5_0_86 : subd5_0 [0, 0, 3] = true := by decide +kernel
theorem subd5_0_87 : subd5_0 [0, 0, 4] = true := by decide +kernel
theorem subd5_0_88 : subd5_0 [0, 0, 5] = true := by decide +kernel
theorem subd5_0_89 : subd5_0 [0, 0, 6] = true := by decide +kernel
theorem subd5_0_90 : subd5_0 [0, 0, 7] = true := by decide +kernel
theorem subd5_0_91 : subd5_0 [0, 1, -8] = true := by decide +kernel
theorem subd5_0_92 : subd5_0 [0, 1, -7] = true := by decide +kernel
theorem subd5_0_93 : subd5_0 [0, 1, -6] = true := by decide +kernel
theorem subd5_0_94 : subd5_0 [0, 1, -5] = true := by decide +kernel
theorem subd5_0_95 : subd5_0 [0, 1, -4] = true := by decide +kernel
theorem sbd5_0_2 : ∀ q ∈ blkd5_0_2, subd5_0 q = true := by
  unfold blkd5_0_2
  exact List.forall_mem_cons.2 ⟨subd5_0_64, List.forall_mem_cons.2 ⟨subd5_0_65, List.forall_mem_cons.2 ⟨subd5_0_66, List.forall_mem_cons.2 ⟨subd5_0_67, List.forall_mem_cons.2 ⟨subd5_0_68, List.forall_mem_cons.2 ⟨subd5_0_69, List.forall_mem_cons.2 ⟨subd5_0_70, List.forall_mem_cons.2 ⟨subd5_0_71, List.forall_mem_cons.2 ⟨subd5_0_72, List.forall_mem_cons.2 ⟨subd5_0_73, List.forall_mem_cons.2 ⟨subd5_0_74, List.forall_mem_cons.2 ⟨subd5_0_75, List.forall_mem_cons.2 ⟨subd5_0_76, List.forall_mem_cons.2 ⟨subd5_0_77, List.forall_mem_cons.2 ⟨subd5_0_78, List.forall_mem_cons.2 ⟨subd5_0_79, List.forall_mem_cons.2 ⟨subd5_0_80, List.forall_mem_cons.2 ⟨subd5_0_81, List.forall_mem_cons.2 ⟨subd5_0_82, List.forall_mem_cons.2 ⟨subd5_0_83, List.forall_mem_cons.2 ⟨subd5_0_84, List.forall_mem_cons.2 ⟨subd5_0_85, List.forall_mem_cons.2 ⟨subd5_0_86, List.forall_mem_cons.2 ⟨subd5_0_87, List.forall_mem_cons.2 ⟨subd5_0_88, List.forall_mem_cons.2 ⟨subd5_0_89, List.forall_mem_cons.2 ⟨subd5_0_90, List.forall_mem_cons.2 ⟨subd5_0_91, List.forall_mem_cons.2 ⟨subd5_0_92, List.forall_mem_cons.2 ⟨subd5_0_93, List.forall_mem_cons.2 ⟨subd5_0_94, List.forall_mem_cons.2 ⟨subd5_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_96 : subd5_0 [0, 1, -3] = true := by decide +kernel
theorem subd5_0_97 : subd5_0 [0, 1, -2] = true := by decide +kernel
theorem subd5_0_98 : subd5_0 [0, 1, -1] = true := by decide +kernel
theorem subd5_0_99 : subd5_0 [0, 1, 0] = true := by decide +kernel
theorem subd5_0_100 : subd5_0 [0, 1, 1] = true := by decide +kernel
theorem subd5_0_101 : subd5_0 [0, 1, 2] = true := by decide +kernel
theorem subd5_0_102 : subd5_0 [0, 1, 3] = true := by decide +kernel
theorem subd5_0_103 : subd5_0 [0, 1, 4] = true := by decide +kernel
theorem subd5_0_104 : subd5_0 [0, 1, 5] = true := by decide +kernel
theorem subd5_0_105 : subd5_0 [0, 1, 6] = true := by decide +kernel
theorem subd5_0_106 : subd5_0 [0, 1, 7] = true := by decide +kernel
theorem subd5_0_107 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_108 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_109 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_110 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_111 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_112 : subd5_0 [1, -1, -7] = true := by decide +kernel
theorem subd5_0_113 : subd5_0 [1, -1, -6] = true := by decide +kernel
theorem subd5_0_114 : subd5_0 [1, -1, -5] = true := by decide +kernel
theorem subd5_0_115 : subd5_0 [1, -1, -4] = true := by decide +kernel
theorem subd5_0_116 : subd5_0 [1, -1, -3] = true := by decide +kernel
theorem subd5_0_117 : subd5_0 [1, -1, -2] = true := by decide +kernel
theorem subd5_0_118 : subd5_0 [1, -1, -1] = true := by decide +kernel
theorem subd5_0_119 : subd5_0 [1, -1, 0] = true := by decide +kernel
theorem subd5_0_120 : subd5_0 [1, -1, 1] = true := by decide +kernel
theorem subd5_0_121 : subd5_0 [1, -1, 2] = true := by decide +kernel
theorem subd5_0_122 : subd5_0 [1, -1, 3] = true := by decide +kernel
theorem subd5_0_123 : subd5_0 [1, -1, 4] = true := by decide +kernel
theorem subd5_0_124 : subd5_0 [1, -1, 5] = true := by decide +kernel
theorem subd5_0_125 : subd5_0 [1, -1, 6] = true := by decide +kernel
theorem subd5_0_126 : subd5_0 [1, 0, -8] = true := by decide +kernel
theorem subd5_0_127 : subd5_0 [1, 0, -7] = true := by decide +kernel
theorem sbd5_0_3 : ∀ q ∈ blkd5_0_3, subd5_0 q = true := by
  unfold blkd5_0_3
  exact List.forall_mem_cons.2 ⟨subd5_0_96, List.forall_mem_cons.2 ⟨subd5_0_97, List.forall_mem_cons.2 ⟨subd5_0_98, List.forall_mem_cons.2 ⟨subd5_0_99, List.forall_mem_cons.2 ⟨subd5_0_100, List.forall_mem_cons.2 ⟨subd5_0_101, List.forall_mem_cons.2 ⟨subd5_0_102, List.forall_mem_cons.2 ⟨subd5_0_103, List.forall_mem_cons.2 ⟨subd5_0_104, List.forall_mem_cons.2 ⟨subd5_0_105, List.forall_mem_cons.2 ⟨subd5_0_106, List.forall_mem_cons.2 ⟨subd5_0_107, List.forall_mem_cons.2 ⟨subd5_0_108, List.forall_mem_cons.2 ⟨subd5_0_109, List.forall_mem_cons.2 ⟨subd5_0_110, List.forall_mem_cons.2 ⟨subd5_0_111, List.forall_mem_cons.2 ⟨subd5_0_112, List.forall_mem_cons.2 ⟨subd5_0_113, List.forall_mem_cons.2 ⟨subd5_0_114, List.forall_mem_cons.2 ⟨subd5_0_115, List.forall_mem_cons.2 ⟨subd5_0_116, List.forall_mem_cons.2 ⟨subd5_0_117, List.forall_mem_cons.2 ⟨subd5_0_118, List.forall_mem_cons.2 ⟨subd5_0_119, List.forall_mem_cons.2 ⟨subd5_0_120, List.forall_mem_cons.2 ⟨subd5_0_121, List.forall_mem_cons.2 ⟨subd5_0_122, List.forall_mem_cons.2 ⟨subd5_0_123, List.forall_mem_cons.2 ⟨subd5_0_124, List.forall_mem_cons.2 ⟨subd5_0_125, List.forall_mem_cons.2 ⟨subd5_0_126, List.forall_mem_cons.2 ⟨subd5_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_128 : subd5_0 [1, 0, -6] = true := by decide +kernel
theorem subd5_0_129 : subd5_0 [1, 0, -5] = true := by decide +kernel
theorem subd5_0_130 : subd5_0 [1, 0, -4] = true := by decide +kernel
theorem subd5_0_131 : subd5_0 [1, 0, -3] = true := by decide +kernel
theorem subd5_0_132 : subd5_0 [1, 0, -2] = true := by decide +kernel
theorem subd5_0_133 : subd5_0 [1, 0, -1] = true := by decide +kernel
theorem subd5_0_134 : subd5_0 [1, 0, 0] = true := by decide +kernel
theorem subd5_0_135 : subd5_0 [1, 0, 1] = true := by decide +kernel
theorem subd5_0_136 : subd5_0 [1, 0, 2] = true := by decide +kernel
theorem subd5_0_137 : subd5_0 [1, 0, 3] = true := by decide +kernel
theorem subd5_0_138 : subd5_0 [1, 0, 4] = true := by decide +kernel
theorem subd5_0_139 : subd5_0 [1, 0, 5] = true := by decide +kernel
theorem subd5_0_140 : subd5_0 [1, 0, 6] = true := by decide +kernel
theorem subd5_0_141 : subd5_0 [1, 0, 7] = true := by decide +kernel
theorem subd5_0_142 : subd5_0 [1, 1, -7] = true := by decide +kernel
theorem subd5_0_143 : subd5_0 [1, 1, -6] = true := by decide +kernel
theorem subd5_0_144 : subd5_0 [1, 1, -5] = true := by decide +kernel
theorem subd5_0_145 : subd5_0 [1, 1, -4] = true := by decide +kernel
theorem subd5_0_146 : subd5_0 [1, 1, -3] = true := by decide +kernel
theorem subd5_0_147 : subd5_0 [1, 1, -2] = true := by decide +kernel
theorem subd5_0_148 : subd5_0 [1, 1, -1] = true := by decide +kernel
theorem subd5_0_149 : subd5_0 [1, 1, 0] = true := by decide +kernel
theorem subd5_0_150 : subd5_0 [1, 1, 1] = true := by decide +kernel
theorem subd5_0_151 : subd5_0 [1, 1, 2] = true := by decide +kernel
theorem subd5_0_152 : subd5_0 [1, 1, 3] = true := by decide +kernel
theorem subd5_0_153 : subd5_0 [1, 1, 4] = true := by decide +kernel
theorem subd5_0_154 : subd5_0 [1, 1, 5] = true := by decide +kernel
theorem subd5_0_155 : subd5_0 [1, 1, 6] = true := by decide +kernel
theorem subd5_0_156 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_157 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_158 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_159 : subd5_0 [2, -2] = true := by decide +kernel
theorem sbd5_0_4 : ∀ q ∈ blkd5_0_4, subd5_0 q = true := by
  unfold blkd5_0_4
  exact List.forall_mem_cons.2 ⟨subd5_0_128, List.forall_mem_cons.2 ⟨subd5_0_129, List.forall_mem_cons.2 ⟨subd5_0_130, List.forall_mem_cons.2 ⟨subd5_0_131, List.forall_mem_cons.2 ⟨subd5_0_132, List.forall_mem_cons.2 ⟨subd5_0_133, List.forall_mem_cons.2 ⟨subd5_0_134, List.forall_mem_cons.2 ⟨subd5_0_135, List.forall_mem_cons.2 ⟨subd5_0_136, List.forall_mem_cons.2 ⟨subd5_0_137, List.forall_mem_cons.2 ⟨subd5_0_138, List.forall_mem_cons.2 ⟨subd5_0_139, List.forall_mem_cons.2 ⟨subd5_0_140, List.forall_mem_cons.2 ⟨subd5_0_141, List.forall_mem_cons.2 ⟨subd5_0_142, List.forall_mem_cons.2 ⟨subd5_0_143, List.forall_mem_cons.2 ⟨subd5_0_144, List.forall_mem_cons.2 ⟨subd5_0_145, List.forall_mem_cons.2 ⟨subd5_0_146, List.forall_mem_cons.2 ⟨subd5_0_147, List.forall_mem_cons.2 ⟨subd5_0_148, List.forall_mem_cons.2 ⟨subd5_0_149, List.forall_mem_cons.2 ⟨subd5_0_150, List.forall_mem_cons.2 ⟨subd5_0_151, List.forall_mem_cons.2 ⟨subd5_0_152, List.forall_mem_cons.2 ⟨subd5_0_153, List.forall_mem_cons.2 ⟨subd5_0_154, List.forall_mem_cons.2 ⟨subd5_0_155, List.forall_mem_cons.2 ⟨subd5_0_156, List.forall_mem_cons.2 ⟨subd5_0_157, List.forall_mem_cons.2 ⟨subd5_0_158, List.forall_mem_cons.2 ⟨subd5_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C084
