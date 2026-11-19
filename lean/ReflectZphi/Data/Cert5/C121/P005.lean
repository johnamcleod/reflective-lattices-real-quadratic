import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_1_32 : subd4_1 [0, -5] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_34 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_35 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_36 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_37 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_38 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_39 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_40 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_41 : subd4_1 [0, 4] = true := by decide +kernel
theorem subd4_1_42 : subd4_1 [0, 5] = true := by decide +kernel
theorem subd4_1_43 : subd4_1 [1, -6] = true := by decide +kernel
theorem subd4_1_44 : subd4_1 [1, -5] = true := by decide +kernel
theorem subd4_1_45 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_46 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_47 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_48 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_49 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_50 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_51 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_52 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_53 : subd4_1 [1, 4] = true := by decide +kernel
theorem subd4_1_54 : subd4_1 [2, -6] = true := by decide +kernel
theorem subd4_1_55 : subd4_1 [2, -5] = true := by decide +kernel
theorem subd4_1_56 : subd4_1 [2, -4] = true := by decide +kernel
theorem subd4_1_57 : subd4_1 [2, -3] = true := by decide +kernel
theorem subd4_1_58 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_59 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_60 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_61 : subd4_1 [2, 1] = true := by decide +kernel
theorem subd4_1_62 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_63 : subd4_1 [2, 3] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_cons.2 ⟨subd4_1_34, List.forall_mem_cons.2 ⟨subd4_1_35, List.forall_mem_cons.2 ⟨subd4_1_36, List.forall_mem_cons.2 ⟨subd4_1_37, List.forall_mem_cons.2 ⟨subd4_1_38, List.forall_mem_cons.2 ⟨subd4_1_39, List.forall_mem_cons.2 ⟨subd4_1_40, List.forall_mem_cons.2 ⟨subd4_1_41, List.forall_mem_cons.2 ⟨subd4_1_42, List.forall_mem_cons.2 ⟨subd4_1_43, List.forall_mem_cons.2 ⟨subd4_1_44, List.forall_mem_cons.2 ⟨subd4_1_45, List.forall_mem_cons.2 ⟨subd4_1_46, List.forall_mem_cons.2 ⟨subd4_1_47, List.forall_mem_cons.2 ⟨subd4_1_48, List.forall_mem_cons.2 ⟨subd4_1_49, List.forall_mem_cons.2 ⟨subd4_1_50, List.forall_mem_cons.2 ⟨subd4_1_51, List.forall_mem_cons.2 ⟨subd4_1_52, List.forall_mem_cons.2 ⟨subd4_1_53, List.forall_mem_cons.2 ⟨subd4_1_54, List.forall_mem_cons.2 ⟨subd4_1_55, List.forall_mem_cons.2 ⟨subd4_1_56, List.forall_mem_cons.2 ⟨subd4_1_57, List.forall_mem_cons.2 ⟨subd4_1_58, List.forall_mem_cons.2 ⟨subd4_1_59, List.forall_mem_cons.2 ⟨subd4_1_60, List.forall_mem_cons.2 ⟨subd4_1_61, List.forall_mem_cons.2 ⟨subd4_1_62, List.forall_mem_cons.2 ⟨subd4_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_64 : subd4_1 [3, -6] = true := by decide +kernel
theorem subd4_1_65 : subd4_1 [3, -5] = true := by decide +kernel
theorem subd4_1_66 : subd4_1 [3, -4] = true := by decide +kernel
theorem subd4_1_67 : subd4_1 [3, -3] = true := by decide +kernel
theorem subd4_1_68 : subd4_1 [3, -2] = true := by decide +kernel
theorem subd4_1_69 : subd4_1 [3, -1] = true := by decide +kernel
theorem subd4_1_70 : subd4_1 [3, 0] = true := by decide +kernel
theorem subd4_1_71 : subd4_1 [3, 1] = true := by decide +kernel
theorem subd4_1_72 : subd4_1 [3, 2] = true := by decide +kernel
theorem subd4_1_73 : subd4_1 [4] = true := by decide +kernel
theorem sbd4_1_2 : ∀ q ∈ blkd4_1_2, subd4_1 q = true := by
  unfold blkd4_1_2
  exact List.forall_mem_cons.2 ⟨subd4_1_64, List.forall_mem_cons.2 ⟨subd4_1_65, List.forall_mem_cons.2 ⟨subd4_1_66, List.forall_mem_cons.2 ⟨subd4_1_67, List.forall_mem_cons.2 ⟨subd4_1_68, List.forall_mem_cons.2 ⟨subd4_1_69, List.forall_mem_cons.2 ⟨subd4_1_70, List.forall_mem_cons.2 ⟨subd4_1_71, List.forall_mem_cons.2 ⟨subd4_1_72, List.forall_mem_cons.2 ⟨subd4_1_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-6] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-5, -7] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-5, -6] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-5, -5] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-5, -4] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-5, -3] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-5, -2] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-5, -1] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [-5, 0] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [-5, 1] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [-5, 2] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [-4, -8] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [-4, -7] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [-4, -6] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [-4, -5] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [-4, -4, -9] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [-4, -4, -8] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [-4, -4, -7] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [-4, -4, -6] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [-4, -4, -5] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [-4, -4, -4] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [-4, -4, -3] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [-4, -4, -2] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [-4, -4, -1] = true := by decide +kernel
theorem subd4_2_24 : subd4_2 [-4, -4, 0] = true := by decide +kernel
theorem subd4_2_25 : subd4_2 [-4, -4, 1] = true := by decide +kernel
theorem subd4_2_26 : subd4_2 [-4, -4, 2] = true := by decide +kernel
theorem subd4_2_27 : subd4_2 [-4, -4, 3] = true := by decide +kernel
theorem subd4_2_28 : subd4_2 [-4, -4, 4] = true := by decide +kernel
theorem subd4_2_29 : subd4_2 [-4, -4, 5] = true := by decide +kernel
theorem subd4_2_30 : subd4_2 [-4, -3, -9] = true := by decide +kernel
theorem subd4_2_31 : subd4_2 [-4, -3, -8] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_cons.2 ⟨subd4_2_24, List.forall_mem_cons.2 ⟨subd4_2_25, List.forall_mem_cons.2 ⟨subd4_2_26, List.forall_mem_cons.2 ⟨subd4_2_27, List.forall_mem_cons.2 ⟨subd4_2_28, List.forall_mem_cons.2 ⟨subd4_2_29, List.forall_mem_cons.2 ⟨subd4_2_30, List.forall_mem_cons.2 ⟨subd4_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_32 : subd4_2 [-4, -3, -7] = true := by decide +kernel
theorem subd4_2_33 : subd4_2 [-4, -3, -6] = true := by decide +kernel
theorem subd4_2_34 : subd4_2 [-4, -3, -5] = true := by decide +kernel
theorem subd4_2_35 : subd4_2 [-4, -3, -4] = true := by decide +kernel
theorem subd4_2_36 : subd4_2 [-4, -3, -3] = true := by decide +kernel
theorem subd4_2_37 : subd4_2 [-4, -3, -2] = true := by decide +kernel
theorem subd4_2_38 : subd4_2 [-4, -3, -1] = true := by decide +kernel
theorem subd4_2_39 : subd4_2 [-4, -3, 0] = true := by decide +kernel
theorem subd4_2_40 : subd4_2 [-4, -3, 1] = true := by decide +kernel
theorem subd4_2_41 : subd4_2 [-4, -3, 2] = true := by decide +kernel
theorem subd4_2_42 : subd4_2 [-4, -3, 3] = true := by decide +kernel
theorem subd4_2_43 : subd4_2 [-4, -3, 4] = true := by decide +kernel
theorem subd4_2_44 : subd4_2 [-4, -3, 5] = true := by decide +kernel
theorem subd4_2_45 : subd4_2 [-4, -3, 6] = true := by decide +kernel
theorem subd4_2_46 : subd4_2 [-4, -2, -9] = true := by decide +kernel
theorem subd4_2_47 : subd4_2 [-4, -2, -8] = true := by decide +kernel
theorem subd4_2_48 : subd4_2 [-4, -2, -7] = true := by decide +kernel
theorem subd4_2_49 : subd4_2 [-4, -2, -6] = true := by decide +kernel
theorem subd4_2_50 : subd4_2 [-4, -2, -5] = true := by decide +kernel
theorem subd4_2_51 : subd4_2 [-4, -2, -4] = true := by decide +kernel
theorem subd4_2_52 : subd4_2 [-4, -2, -3] = true := by decide +kernel
theorem subd4_2_53 : subd4_2 [-4, -2, -2] = true := by decide +kernel
theorem subd4_2_54 : subd4_2 [-4, -2, -1] = true := by decide +kernel
theorem subd4_2_55 : subd4_2 [-4, -2, 0] = true := by decide +kernel
theorem subd4_2_56 : subd4_2 [-4, -2, 1] = true := by decide +kernel
theorem subd4_2_57 : subd4_2 [-4, -2, 2] = true := by decide +kernel
theorem subd4_2_58 : subd4_2 [-4, -2, 3] = true := by decide +kernel
theorem subd4_2_59 : subd4_2 [-4, -2, 4] = true := by decide +kernel
theorem subd4_2_60 : subd4_2 [-4, -2, 5] = true := by decide +kernel
theorem subd4_2_61 : subd4_2 [-4, -2, 6] = true := by decide +kernel
theorem subd4_2_62 : subd4_2 [-4, -1, -9] = true := by decide +kernel
theorem subd4_2_63 : subd4_2 [-4, -1, -8] = true := by decide +kernel
theorem sbd4_2_1 : ∀ q ∈ blkd4_2_1, subd4_2 q = true := by
  unfold blkd4_2_1
  exact List.forall_mem_cons.2 ⟨subd4_2_32, List.forall_mem_cons.2 ⟨subd4_2_33, List.forall_mem_cons.2 ⟨subd4_2_34, List.forall_mem_cons.2 ⟨subd4_2_35, List.forall_mem_cons.2 ⟨subd4_2_36, List.forall_mem_cons.2 ⟨subd4_2_37, List.forall_mem_cons.2 ⟨subd4_2_38, List.forall_mem_cons.2 ⟨subd4_2_39, List.forall_mem_cons.2 ⟨subd4_2_40, List.forall_mem_cons.2 ⟨subd4_2_41, List.forall_mem_cons.2 ⟨subd4_2_42, List.forall_mem_cons.2 ⟨subd4_2_43, List.forall_mem_cons.2 ⟨subd4_2_44, List.forall_mem_cons.2 ⟨subd4_2_45, List.forall_mem_cons.2 ⟨subd4_2_46, List.forall_mem_cons.2 ⟨subd4_2_47, List.forall_mem_cons.2 ⟨subd4_2_48, List.forall_mem_cons.2 ⟨subd4_2_49, List.forall_mem_cons.2 ⟨subd4_2_50, List.forall_mem_cons.2 ⟨subd4_2_51, List.forall_mem_cons.2 ⟨subd4_2_52, List.forall_mem_cons.2 ⟨subd4_2_53, List.forall_mem_cons.2 ⟨subd4_2_54, List.forall_mem_cons.2 ⟨subd4_2_55, List.forall_mem_cons.2 ⟨subd4_2_56, List.forall_mem_cons.2 ⟨subd4_2_57, List.forall_mem_cons.2 ⟨subd4_2_58, List.forall_mem_cons.2 ⟨subd4_2_59, List.forall_mem_cons.2 ⟨subd4_2_60, List.forall_mem_cons.2 ⟨subd4_2_61, List.forall_mem_cons.2 ⟨subd4_2_62, List.forall_mem_cons.2 ⟨subd4_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_64 : subd4_2 [-4, -1, -7] = true := by decide +kernel
theorem subd4_2_65 : subd4_2 [-4, -1, -6] = true := by decide +kernel
theorem subd4_2_66 : subd4_2 [-4, -1, -5] = true := by decide +kernel
theorem subd4_2_67 : subd4_2 [-4, -1, -4] = true := by decide +kernel
theorem subd4_2_68 : subd4_2 [-4, -1, -3] = true := by decide +kernel
theorem subd4_2_69 : subd4_2 [-4, -1, -2] = true := by decide +kernel
theorem subd4_2_70 : subd4_2 [-4, -1, -1] = true := by decide +kernel
theorem subd4_2_71 : subd4_2 [-4, -1, 0] = true := by decide +kernel
theorem subd4_2_72 : subd4_2 [-4, -1, 1] = true := by decide +kernel
theorem subd4_2_73 : subd4_2 [-4, -1, 2] = true := by decide +kernel
theorem subd4_2_74 : subd4_2 [-4, -1, 3] = true := by decide +kernel
theorem subd4_2_75 : subd4_2 [-4, -1, 4] = true := by decide +kernel
theorem subd4_2_76 : subd4_2 [-4, -1, 5] = true := by decide +kernel
theorem subd4_2_77 : subd4_2 [-4, -1, 6] = true := by decide +kernel
theorem subd4_2_78 : subd4_2 [-4, -1, 7] = true := by decide +kernel
theorem subd4_2_79 : subd4_2 [-4, 0, -8] = true := by decide +kernel
theorem subd4_2_80 : subd4_2 [-4, 0, -7] = true := by decide +kernel
theorem subd4_2_81 : subd4_2 [-4, 0, -6] = true := by decide +kernel
theorem subd4_2_82 : subd4_2 [-4, 0, -5] = true := by decide +kernel
theorem subd4_2_83 : subd4_2 [-4, 0, -4] = true := by decide +kernel
theorem subd4_2_84 : subd4_2 [-4, 0, -3] = true := by decide +kernel
theorem subd4_2_85 : subd4_2 [-4, 0, -2] = true := by decide +kernel
theorem subd4_2_86 : subd4_2 [-4, 0, -1] = true := by decide +kernel
theorem subd4_2_87 : subd4_2 [-4, 0, 0] = true := by decide +kernel
theorem subd4_2_88 : subd4_2 [-4, 0, 1] = true := by decide +kernel
theorem subd4_2_89 : subd4_2 [-4, 0, 2] = true := by decide +kernel
theorem subd4_2_90 : subd4_2 [-4, 0, 3] = true := by decide +kernel
theorem subd4_2_91 : subd4_2 [-4, 0, 4] = true := by decide +kernel
theorem subd4_2_92 : subd4_2 [-4, 0, 5] = true := by decide +kernel
theorem subd4_2_93 : subd4_2 [-4, 0, 6] = true := by decide +kernel
theorem subd4_2_94 : subd4_2 [-4, 0, 7] = true := by decide +kernel
theorem subd4_2_95 : subd4_2 [-4, 1, -7] = true := by decide +kernel
theorem sbd4_2_2 : ∀ q ∈ blkd4_2_2, subd4_2 q = true := by
  unfold blkd4_2_2
  exact List.forall_mem_cons.2 ⟨subd4_2_64, List.forall_mem_cons.2 ⟨subd4_2_65, List.forall_mem_cons.2 ⟨subd4_2_66, List.forall_mem_cons.2 ⟨subd4_2_67, List.forall_mem_cons.2 ⟨subd4_2_68, List.forall_mem_cons.2 ⟨subd4_2_69, List.forall_mem_cons.2 ⟨subd4_2_70, List.forall_mem_cons.2 ⟨subd4_2_71, List.forall_mem_cons.2 ⟨subd4_2_72, List.forall_mem_cons.2 ⟨subd4_2_73, List.forall_mem_cons.2 ⟨subd4_2_74, List.forall_mem_cons.2 ⟨subd4_2_75, List.forall_mem_cons.2 ⟨subd4_2_76, List.forall_mem_cons.2 ⟨subd4_2_77, List.forall_mem_cons.2 ⟨subd4_2_78, List.forall_mem_cons.2 ⟨subd4_2_79, List.forall_mem_cons.2 ⟨subd4_2_80, List.forall_mem_cons.2 ⟨subd4_2_81, List.forall_mem_cons.2 ⟨subd4_2_82, List.forall_mem_cons.2 ⟨subd4_2_83, List.forall_mem_cons.2 ⟨subd4_2_84, List.forall_mem_cons.2 ⟨subd4_2_85, List.forall_mem_cons.2 ⟨subd4_2_86, List.forall_mem_cons.2 ⟨subd4_2_87, List.forall_mem_cons.2 ⟨subd4_2_88, List.forall_mem_cons.2 ⟨subd4_2_89, List.forall_mem_cons.2 ⟨subd4_2_90, List.forall_mem_cons.2 ⟨subd4_2_91, List.forall_mem_cons.2 ⟨subd4_2_92, List.forall_mem_cons.2 ⟨subd4_2_93, List.forall_mem_cons.2 ⟨subd4_2_94, List.forall_mem_cons.2 ⟨subd4_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_96 : subd4_2 [-4, 1, -6] = true := by decide +kernel
theorem subd4_2_97 : subd4_2 [-4, 1, -5] = true := by decide +kernel
theorem subd4_2_98 : subd4_2 [-4, 1, -4] = true := by decide +kernel
theorem subd4_2_99 : subd4_2 [-4, 1, -3] = true := by decide +kernel
theorem subd4_2_100 : subd4_2 [-4, 1, -2] = true := by decide +kernel
theorem subd4_2_101 : subd4_2 [-4, 1, -1] = true := by decide +kernel
theorem subd4_2_102 : subd4_2 [-4, 1, 0] = true := by decide +kernel
theorem subd4_2_103 : subd4_2 [-4, 1, 1] = true := by decide +kernel
theorem subd4_2_104 : subd4_2 [-4, 1, 2] = true := by decide +kernel
theorem subd4_2_105 : subd4_2 [-4, 1, 3] = true := by decide +kernel
theorem subd4_2_106 : subd4_2 [-4, 1, 4] = true := by decide +kernel
theorem subd4_2_107 : subd4_2 [-4, 1, 5] = true := by decide +kernel
theorem subd4_2_108 : subd4_2 [-4, 1, 6] = true := by decide +kernel
theorem subd4_2_109 : subd4_2 [-4, 2] = true := by decide +kernel
theorem subd4_2_110 : subd4_2 [-4, 3] = true := by decide +kernel
theorem subd4_2_111 : subd4_2 [-3, -8] = true := by decide +kernel
theorem subd4_2_112 : subd4_2 [-3, -7] = true := by decide +kernel
theorem subd4_2_113 : subd4_2 [-3, -6] = true := by decide +kernel
theorem subd4_2_114 : subd4_2 [-3, -5, -9] = true := by decide +kernel
theorem subd4_2_115 : subd4_2 [-3, -5, -8] = true := by decide +kernel
theorem subd4_2_116 : subd4_2 [-3, -5, -7] = true := by decide +kernel
theorem subd4_2_117 : subd4_2 [-3, -5, -6] = true := by decide +kernel
theorem subd4_2_118 : subd4_2 [-3, -5, -5] = true := by decide +kernel
theorem subd4_2_119 : subd4_2 [-3, -5, -4] = true := by decide +kernel
theorem subd4_2_120 : subd4_2 [-3, -5, -3] = true := by decide +kernel
theorem subd4_2_121 : subd4_2 [-3, -5, -2] = true := by decide +kernel
theorem subd4_2_122 : subd4_2 [-3, -5, -1] = true := by decide +kernel
theorem subd4_2_123 : subd4_2 [-3, -5, 0] = true := by decide +kernel
theorem subd4_2_124 : subd4_2 [-3, -5, 1] = true := by decide +kernel
theorem subd4_2_125 : subd4_2 [-3, -5, 2] = true := by decide +kernel
theorem subd4_2_126 : subd4_2 [-3, -5, 3] = true := by decide +kernel
theorem subd4_2_127 : subd4_2 [-3, -5, 4] = true := by decide +kernel
theorem sbd4_2_3 : ∀ q ∈ blkd4_2_3, subd4_2 q = true := by
  unfold blkd4_2_3
  exact List.forall_mem_cons.2 ⟨subd4_2_96, List.forall_mem_cons.2 ⟨subd4_2_97, List.forall_mem_cons.2 ⟨subd4_2_98, List.forall_mem_cons.2 ⟨subd4_2_99, List.forall_mem_cons.2 ⟨subd4_2_100, List.forall_mem_cons.2 ⟨subd4_2_101, List.forall_mem_cons.2 ⟨subd4_2_102, List.forall_mem_cons.2 ⟨subd4_2_103, List.forall_mem_cons.2 ⟨subd4_2_104, List.forall_mem_cons.2 ⟨subd4_2_105, List.forall_mem_cons.2 ⟨subd4_2_106, List.forall_mem_cons.2 ⟨subd4_2_107, List.forall_mem_cons.2 ⟨subd4_2_108, List.forall_mem_cons.2 ⟨subd4_2_109, List.forall_mem_cons.2 ⟨subd4_2_110, List.forall_mem_cons.2 ⟨subd4_2_111, List.forall_mem_cons.2 ⟨subd4_2_112, List.forall_mem_cons.2 ⟨subd4_2_113, List.forall_mem_cons.2 ⟨subd4_2_114, List.forall_mem_cons.2 ⟨subd4_2_115, List.forall_mem_cons.2 ⟨subd4_2_116, List.forall_mem_cons.2 ⟨subd4_2_117, List.forall_mem_cons.2 ⟨subd4_2_118, List.forall_mem_cons.2 ⟨subd4_2_119, List.forall_mem_cons.2 ⟨subd4_2_120, List.forall_mem_cons.2 ⟨subd4_2_121, List.forall_mem_cons.2 ⟨subd4_2_122, List.forall_mem_cons.2 ⟨subd4_2_123, List.forall_mem_cons.2 ⟨subd4_2_124, List.forall_mem_cons.2 ⟨subd4_2_125, List.forall_mem_cons.2 ⟨subd4_2_126, List.forall_mem_cons.2 ⟨subd4_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_128 : subd4_2 [-3, -5, 5] = true := by decide +kernel
theorem subd4_2_129 : subd4_2 [-3, -4, -9] = true := by decide +kernel
theorem subd4_2_130 : subd4_2 [-3, -4, -8] = true := by decide +kernel
theorem subd4_2_131 : subd4_2 [-3, -4, -7] = true := by decide +kernel
theorem subd4_2_132 : subd4_2 [-3, -4, -6] = true := by decide +kernel
theorem subd4_2_133 : subd4_2 [-3, -4, -5] = true := by decide +kernel
theorem subd4_2_134 : subd4_2 [-3, -4, -4] = true := by decide +kernel
theorem subd4_2_135 : subd4_2 [-3, -4, -3] = true := by decide +kernel
theorem subd4_2_136 : subd4_2 [-3, -4, -2] = true := by decide +kernel
theorem subd4_2_137 : subd4_2 [-3, -4, -1] = true := by decide +kernel
theorem subd4_2_138 : subd4_2 [-3, -4, 0] = true := by decide +kernel
theorem subd4_2_139 : subd4_2 [-3, -4, 1] = true := by decide +kernel
theorem subd4_2_140 : subd4_2 [-3, -4, 2] = true := by decide +kernel
theorem subd4_2_141 : subd4_2 [-3, -4, 3] = true := by decide +kernel
theorem subd4_2_142 : subd4_2 [-3, -4, 4] = true := by decide +kernel
theorem subd4_2_143 : subd4_2 [-3, -4, 5] = true := by decide +kernel
theorem subd4_2_144 : subd4_2 [-3, -4, 6] = true := by decide +kernel
theorem subd4_2_145 : subd4_2 [-3, -3, -10] = true := by decide +kernel
theorem subd4_2_146 : subd4_2 [-3, -3, -9] = true := by decide +kernel
theorem subd4_2_147 : subd4_2 [-3, -3, -8] = true := by decide +kernel
theorem subd4_2_148 : subd4_2 [-3, -3, -7] = true := by decide +kernel
theorem subd4_2_149 : subd4_2 [-3, -3, -6] = true := by decide +kernel
theorem subd4_2_150 : subd4_2 [-3, -3, -5] = true := by decide +kernel
theorem subd4_2_151 : subd4_2 [-3, -3, -4] = true := by decide +kernel
theorem subd4_2_152 : subd4_2 [-3, -3, -3] = true := by decide +kernel
theorem subd4_2_153 : subd4_2 [-3, -3, -2] = true := by decide +kernel
theorem subd4_2_154 : subd4_2 [-3, -3, -1] = true := by decide +kernel
theorem subd4_2_155 : subd4_2 [-3, -3, 0] = true := by decide +kernel
theorem subd4_2_156 : subd4_2 [-3, -3, 1] = true := by decide +kernel
theorem subd4_2_157 : subd4_2 [-3, -3, 2] = true := by decide +kernel
theorem subd4_2_158 : subd4_2 [-3, -3, 3] = true := by decide +kernel
theorem subd4_2_159 : subd4_2 [-3, -3, 4] = true := by decide +kernel
theorem sbd4_2_4 : ∀ q ∈ blkd4_2_4, subd4_2 q = true := by
  unfold blkd4_2_4
  exact List.forall_mem_cons.2 ⟨subd4_2_128, List.forall_mem_cons.2 ⟨subd4_2_129, List.forall_mem_cons.2 ⟨subd4_2_130, List.forall_mem_cons.2 ⟨subd4_2_131, List.forall_mem_cons.2 ⟨subd4_2_132, List.forall_mem_cons.2 ⟨subd4_2_133, List.forall_mem_cons.2 ⟨subd4_2_134, List.forall_mem_cons.2 ⟨subd4_2_135, List.forall_mem_cons.2 ⟨subd4_2_136, List.forall_mem_cons.2 ⟨subd4_2_137, List.forall_mem_cons.2 ⟨subd4_2_138, List.forall_mem_cons.2 ⟨subd4_2_139, List.forall_mem_cons.2 ⟨subd4_2_140, List.forall_mem_cons.2 ⟨subd4_2_141, List.forall_mem_cons.2 ⟨subd4_2_142, List.forall_mem_cons.2 ⟨subd4_2_143, List.forall_mem_cons.2 ⟨subd4_2_144, List.forall_mem_cons.2 ⟨subd4_2_145, List.forall_mem_cons.2 ⟨subd4_2_146, List.forall_mem_cons.2 ⟨subd4_2_147, List.forall_mem_cons.2 ⟨subd4_2_148, List.forall_mem_cons.2 ⟨subd4_2_149, List.forall_mem_cons.2 ⟨subd4_2_150, List.forall_mem_cons.2 ⟨subd4_2_151, List.forall_mem_cons.2 ⟨subd4_2_152, List.forall_mem_cons.2 ⟨subd4_2_153, List.forall_mem_cons.2 ⟨subd4_2_154, List.forall_mem_cons.2 ⟨subd4_2_155, List.forall_mem_cons.2 ⟨subd4_2_156, List.forall_mem_cons.2 ⟨subd4_2_157, List.forall_mem_cons.2 ⟨subd4_2_158, List.forall_mem_cons.2 ⟨subd4_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_160 : subd4_2 [-3, -3, 5] = true := by decide +kernel
theorem subd4_2_161 : subd4_2 [-3, -3, 6] = true := by decide +kernel
theorem subd4_2_162 : subd4_2 [-3, -3, 7] = true := by decide +kernel
theorem subd4_2_163 : subd4_2 [-3, -2, -10] = true := by decide +kernel
theorem subd4_2_164 : subd4_2 [-3, -2, -9] = true := by decide +kernel
theorem subd4_2_165 : subd4_2 [-3, -2, -8] = true := by decide +kernel
theorem subd4_2_166 : subd4_2 [-3, -2, -7] = true := by decide +kernel
theorem subd4_2_167 : subd4_2 [-3, -2, -6] = true := by decide +kernel
theorem subd4_2_168 : subd4_2 [-3, -2, -5] = true := by decide +kernel
theorem subd4_2_169 : subd4_2 [-3, -2, -4] = true := by decide +kernel
theorem subd4_2_170 : subd4_2 [-3, -2, -3] = true := by decide +kernel
theorem subd4_2_171 : subd4_2 [-3, -2, -2] = true := by decide +kernel
theorem subd4_2_172 : subd4_2 [-3, -2, -1] = true := by decide +kernel
theorem subd4_2_173 : subd4_2 [-3, -2, 0] = true := by decide +kernel
theorem subd4_2_174 : subd4_2 [-3, -2, 1] = true := by decide +kernel
theorem subd4_2_175 : subd4_2 [-3, -2, 2] = true := by decide +kernel
theorem subd4_2_176 : subd4_2 [-3, -2, 3] = true := by decide +kernel
theorem subd4_2_177 : subd4_2 [-3, -2, 4] = true := by decide +kernel
theorem subd4_2_178 : subd4_2 [-3, -2, 5] = true := by decide +kernel
theorem subd4_2_179 : subd4_2 [-3, -2, 6] = true := by decide +kernel
theorem subd4_2_180 : subd4_2 [-3, -2, 7] = true := by decide +kernel
theorem subd4_2_181 : subd4_2 [-3, -1, -10] = true := by decide +kernel
theorem subd4_2_182 : subd4_2 [-3, -1, -9] = true := by decide +kernel
theorem subd4_2_183 : subd4_2 [-3, -1, -8] = true := by decide +kernel
theorem subd4_2_184 : subd4_2 [-3, -1, -7] = true := by decide +kernel
theorem subd4_2_185 : subd4_2 [-3, -1, -6] = true := by decide +kernel
theorem subd4_2_186 : subd4_2 [-3, -1, -5] = true := by decide +kernel
theorem subd4_2_187 : subd4_2 [-3, -1, -4] = true := by decide +kernel
theorem subd4_2_188 : subd4_2 [-3, -1, -3] = true := by decide +kernel
theorem subd4_2_189 : subd4_2 [-3, -1, -2] = true := by decide +kernel
theorem subd4_2_190 : subd4_2 [-3, -1, -1] = true := by decide +kernel
theorem subd4_2_191 : subd4_2 [-3, -1, 0] = true := by decide +kernel
theorem sbd4_2_5 : ∀ q ∈ blkd4_2_5, subd4_2 q = true := by
  unfold blkd4_2_5
  exact List.forall_mem_cons.2 ⟨subd4_2_160, List.forall_mem_cons.2 ⟨subd4_2_161, List.forall_mem_cons.2 ⟨subd4_2_162, List.forall_mem_cons.2 ⟨subd4_2_163, List.forall_mem_cons.2 ⟨subd4_2_164, List.forall_mem_cons.2 ⟨subd4_2_165, List.forall_mem_cons.2 ⟨subd4_2_166, List.forall_mem_cons.2 ⟨subd4_2_167, List.forall_mem_cons.2 ⟨subd4_2_168, List.forall_mem_cons.2 ⟨subd4_2_169, List.forall_mem_cons.2 ⟨subd4_2_170, List.forall_mem_cons.2 ⟨subd4_2_171, List.forall_mem_cons.2 ⟨subd4_2_172, List.forall_mem_cons.2 ⟨subd4_2_173, List.forall_mem_cons.2 ⟨subd4_2_174, List.forall_mem_cons.2 ⟨subd4_2_175, List.forall_mem_cons.2 ⟨subd4_2_176, List.forall_mem_cons.2 ⟨subd4_2_177, List.forall_mem_cons.2 ⟨subd4_2_178, List.forall_mem_cons.2 ⟨subd4_2_179, List.forall_mem_cons.2 ⟨subd4_2_180, List.forall_mem_cons.2 ⟨subd4_2_181, List.forall_mem_cons.2 ⟨subd4_2_182, List.forall_mem_cons.2 ⟨subd4_2_183, List.forall_mem_cons.2 ⟨subd4_2_184, List.forall_mem_cons.2 ⟨subd4_2_185, List.forall_mem_cons.2 ⟨subd4_2_186, List.forall_mem_cons.2 ⟨subd4_2_187, List.forall_mem_cons.2 ⟨subd4_2_188, List.forall_mem_cons.2 ⟨subd4_2_189, List.forall_mem_cons.2 ⟨subd4_2_190, List.forall_mem_cons.2 ⟨subd4_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_192 : subd4_2 [-3, -1, 1] = true := by decide +kernel
theorem subd4_2_193 : subd4_2 [-3, -1, 2] = true := by decide +kernel
theorem subd4_2_194 : subd4_2 [-3, -1, 3] = true := by decide +kernel
theorem subd4_2_195 : subd4_2 [-3, -1, 4] = true := by decide +kernel
theorem subd4_2_196 : subd4_2 [-3, -1, 5] = true := by decide +kernel
theorem subd4_2_197 : subd4_2 [-3, -1, 6] = true := by decide +kernel
theorem subd4_2_198 : subd4_2 [-3, -1, 7] = true := by decide +kernel
theorem subd4_2_199 : subd4_2 [-3, -1, 8] = true := by decide +kernel
theorem subd4_2_200 : subd4_2 [-3, 0, -9] = true := by decide +kernel
theorem subd4_2_201 : subd4_2 [-3, 0, -8] = true := by decide +kernel
theorem subd4_2_202 : subd4_2 [-3, 0, -7] = true := by decide +kernel
theorem subd4_2_203 : subd4_2 [-3, 0, -6] = true := by decide +kernel
theorem subd4_2_204 : subd4_2 [-3, 0, -5] = true := by decide +kernel
theorem subd4_2_205 : subd4_2 [-3, 0, -4] = true := by decide +kernel
theorem subd4_2_206 : subd4_2 [-3, 0, -3] = true := by decide +kernel
theorem subd4_2_207 : subd4_2 [-3, 0, -2] = true := by decide +kernel
theorem subd4_2_208 : subd4_2 [-3, 0, -1] = true := by decide +kernel
theorem subd4_2_209 : subd4_2 [-3, 0, 0] = true := by decide +kernel
theorem subd4_2_210 : subd4_2 [-3, 0, 1] = true := by decide +kernel
theorem subd4_2_211 : subd4_2 [-3, 0, 2] = true := by decide +kernel
theorem subd4_2_212 : subd4_2 [-3, 0, 3] = true := by decide +kernel
theorem subd4_2_213 : subd4_2 [-3, 0, 4] = true := by decide +kernel
theorem subd4_2_214 : subd4_2 [-3, 0, 5] = true := by decide +kernel
theorem subd4_2_215 : subd4_2 [-3, 0, 6] = true := by decide +kernel
theorem subd4_2_216 : subd4_2 [-3, 0, 7] = true := by decide +kernel
theorem subd4_2_217 : subd4_2 [-3, 0, 8] = true := by decide +kernel
theorem subd4_2_218 : subd4_2 [-3, 1, -8] = true := by decide +kernel
theorem subd4_2_219 : subd4_2 [-3, 1, -7] = true := by decide +kernel
theorem subd4_2_220 : subd4_2 [-3, 1, -6] = true := by decide +kernel
theorem subd4_2_221 : subd4_2 [-3, 1, -5] = true := by decide +kernel
theorem subd4_2_222 : subd4_2 [-3, 1, -4] = true := by decide +kernel
theorem subd4_2_223 : subd4_2 [-3, 1, -3] = true := by decide +kernel
theorem sbd4_2_6 : ∀ q ∈ blkd4_2_6, subd4_2 q = true := by
  unfold blkd4_2_6
  exact List.forall_mem_cons.2 ⟨subd4_2_192, List.forall_mem_cons.2 ⟨subd4_2_193, List.forall_mem_cons.2 ⟨subd4_2_194, List.forall_mem_cons.2 ⟨subd4_2_195, List.forall_mem_cons.2 ⟨subd4_2_196, List.forall_mem_cons.2 ⟨subd4_2_197, List.forall_mem_cons.2 ⟨subd4_2_198, List.forall_mem_cons.2 ⟨subd4_2_199, List.forall_mem_cons.2 ⟨subd4_2_200, List.forall_mem_cons.2 ⟨subd4_2_201, List.forall_mem_cons.2 ⟨subd4_2_202, List.forall_mem_cons.2 ⟨subd4_2_203, List.forall_mem_cons.2 ⟨subd4_2_204, List.forall_mem_cons.2 ⟨subd4_2_205, List.forall_mem_cons.2 ⟨subd4_2_206, List.forall_mem_cons.2 ⟨subd4_2_207, List.forall_mem_cons.2 ⟨subd4_2_208, List.forall_mem_cons.2 ⟨subd4_2_209, List.forall_mem_cons.2 ⟨subd4_2_210, List.forall_mem_cons.2 ⟨subd4_2_211, List.forall_mem_cons.2 ⟨subd4_2_212, List.forall_mem_cons.2 ⟨subd4_2_213, List.forall_mem_cons.2 ⟨subd4_2_214, List.forall_mem_cons.2 ⟨subd4_2_215, List.forall_mem_cons.2 ⟨subd4_2_216, List.forall_mem_cons.2 ⟨subd4_2_217, List.forall_mem_cons.2 ⟨subd4_2_218, List.forall_mem_cons.2 ⟨subd4_2_219, List.forall_mem_cons.2 ⟨subd4_2_220, List.forall_mem_cons.2 ⟨subd4_2_221, List.forall_mem_cons.2 ⟨subd4_2_222, List.forall_mem_cons.2 ⟨subd4_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
