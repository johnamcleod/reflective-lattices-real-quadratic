import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_32 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [0, 0, -7] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [0, 0, -6] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [0, 0, -5] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [0, 0, -4] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [0, 0, -3] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [0, 0, -2] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [0, 0, -1] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [0, 0, 0] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [0, 0, 1] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [0, 0, 2] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [0, 0, 3] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [0, 0, 4] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [0, 0, 5] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [0, 0, 6] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [0, 4] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [2, -5] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_64 : subd9_3 [2, -4] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [2, -3] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [2, -2] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [2, -1] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [2, 0] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [2, 1] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [2, 2] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [2, 3] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [3, -4] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [3, -3] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [3, -2] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [3, -1] = true := by decide +kernel
theorem subd9_3_76 : subd9_3 [3, 0] = true := by decide +kernel
theorem subd9_3_77 : subd9_3 [3, 1] = true := by decide +kernel
theorem subd9_3_78 : subd9_3 [3, 2] = true := by decide +kernel
theorem subd9_3_79 : subd9_3 [4, -4] = true := by decide +kernel
theorem subd9_3_80 : subd9_3 [4, -3] = true := by decide +kernel
theorem subd9_3_81 : subd9_3 [4, -2] = true := by decide +kernel
theorem subd9_3_82 : subd9_3 [4, -1] = true := by decide +kernel
theorem subd9_3_83 : subd9_3 [4, 0] = true := by decide +kernel
theorem subd9_3_84 : subd9_3 [4, 1] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_cons.2 ⟨subd9_3_76, List.forall_mem_cons.2 ⟨subd9_3_77, List.forall_mem_cons.2 ⟨subd9_3_78, List.forall_mem_cons.2 ⟨subd9_3_79, List.forall_mem_cons.2 ⟨subd9_3_80, List.forall_mem_cons.2 ⟨subd9_3_81, List.forall_mem_cons.2 ⟨subd9_3_82, List.forall_mem_cons.2 ⟨subd9_3_83, List.forall_mem_cons.2 ⟨subd9_3_84, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel
theorem subd9_4_0 : subd9_4 [-1, -3] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [-1, -2] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [-1, -1, -7] = true := by decide +kernel
theorem subd9_4_3 : subd9_4 [-1, -1, -6] = true := by decide +kernel
theorem subd9_4_4 : subd9_4 [-1, -1, -5] = true := by decide +kernel
theorem subd9_4_5 : subd9_4 [-1, -1, -4] = true := by decide +kernel
theorem subd9_4_6 : subd9_4 [-1, -1, -3] = true := by decide +kernel
theorem subd9_4_7 : subd9_4 [-1, -1, -2] = true := by decide +kernel
theorem subd9_4_8 : subd9_4 [-1, -1, -1] = true := by decide +kernel
theorem subd9_4_9 : subd9_4 [-1, -1, 0] = true := by decide +kernel
theorem subd9_4_10 : subd9_4 [-1, -1, 1] = true := by decide +kernel
theorem subd9_4_11 : subd9_4 [-1, -1, 2] = true := by decide +kernel
theorem subd9_4_12 : subd9_4 [-1, -1, 3] = true := by decide +kernel
theorem subd9_4_13 : subd9_4 [-1, -1, 4] = true := by decide +kernel
theorem subd9_4_14 : subd9_4 [-1, -1, 5] = true := by decide +kernel
theorem subd9_4_15 : subd9_4 [-1, -1, 6] = true := by decide +kernel
theorem subd9_4_16 : subd9_4 [-1, -1, 7] = true := by decide +kernel
theorem subd9_4_17 : subd9_4 [-1, 0, -8] = true := by decide +kernel
theorem subd9_4_18 : subd9_4 [-1, 0, -7] = true := by decide +kernel
theorem subd9_4_19 : subd9_4 [-1, 0, -6] = true := by decide +kernel
theorem subd9_4_20 : subd9_4 [-1, 0, -5] = true := by decide +kernel
theorem subd9_4_21 : subd9_4 [-1, 0, -4] = true := by decide +kernel
theorem subd9_4_22 : subd9_4 [-1, 0, -3] = true := by decide +kernel
theorem subd9_4_23 : subd9_4 [-1, 0, -2] = true := by decide +kernel
theorem subd9_4_24 : subd9_4 [-1, 0, -1] = true := by decide +kernel
theorem subd9_4_25 : subd9_4 [-1, 0, 0] = true := by decide +kernel
theorem subd9_4_26 : subd9_4 [-1, 0, 1] = true := by decide +kernel
theorem subd9_4_27 : subd9_4 [-1, 0, 2] = true := by decide +kernel
theorem subd9_4_28 : subd9_4 [-1, 0, 3] = true := by decide +kernel
theorem subd9_4_29 : subd9_4 [-1, 0, 4] = true := by decide +kernel
theorem subd9_4_30 : subd9_4 [-1, 0, 5] = true := by decide +kernel
theorem subd9_4_31 : subd9_4 [-1, 0, 6] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_cons.2 ⟨subd9_4_3, List.forall_mem_cons.2 ⟨subd9_4_4, List.forall_mem_cons.2 ⟨subd9_4_5, List.forall_mem_cons.2 ⟨subd9_4_6, List.forall_mem_cons.2 ⟨subd9_4_7, List.forall_mem_cons.2 ⟨subd9_4_8, List.forall_mem_cons.2 ⟨subd9_4_9, List.forall_mem_cons.2 ⟨subd9_4_10, List.forall_mem_cons.2 ⟨subd9_4_11, List.forall_mem_cons.2 ⟨subd9_4_12, List.forall_mem_cons.2 ⟨subd9_4_13, List.forall_mem_cons.2 ⟨subd9_4_14, List.forall_mem_cons.2 ⟨subd9_4_15, List.forall_mem_cons.2 ⟨subd9_4_16, List.forall_mem_cons.2 ⟨subd9_4_17, List.forall_mem_cons.2 ⟨subd9_4_18, List.forall_mem_cons.2 ⟨subd9_4_19, List.forall_mem_cons.2 ⟨subd9_4_20, List.forall_mem_cons.2 ⟨subd9_4_21, List.forall_mem_cons.2 ⟨subd9_4_22, List.forall_mem_cons.2 ⟨subd9_4_23, List.forall_mem_cons.2 ⟨subd9_4_24, List.forall_mem_cons.2 ⟨subd9_4_25, List.forall_mem_cons.2 ⟨subd9_4_26, List.forall_mem_cons.2 ⟨subd9_4_27, List.forall_mem_cons.2 ⟨subd9_4_28, List.forall_mem_cons.2 ⟨subd9_4_29, List.forall_mem_cons.2 ⟨subd9_4_30, List.forall_mem_cons.2 ⟨subd9_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_32 : subd9_4 [-1, 0, 7] = true := by decide +kernel
theorem subd9_4_33 : subd9_4 [-1, 1] = true := by decide +kernel
theorem subd9_4_34 : subd9_4 [0, -3] = true := by decide +kernel
theorem subd9_4_35 : subd9_4 [0, -2] = true := by decide +kernel
theorem subd9_4_36 : subd9_4 [0, -1, -8] = true := by decide +kernel
theorem subd9_4_37 : subd9_4 [0, -1, -7] = true := by decide +kernel
theorem subd9_4_38 : subd9_4 [0, -1, -6] = true := by decide +kernel
theorem subd9_4_39 : subd9_4 [0, -1, -5] = true := by decide +kernel
theorem subd9_4_40 : subd9_4 [0, -1, -4] = true := by decide +kernel
theorem subd9_4_41 : subd9_4 [0, -1, -3] = true := by decide +kernel
theorem subd9_4_42 : subd9_4 [0, -1, -2] = true := by decide +kernel
theorem subd9_4_43 : subd9_4 [0, -1, -1] = true := by decide +kernel
theorem subd9_4_44 : subd9_4 [0, -1, 0] = true := by decide +kernel
theorem subd9_4_45 : subd9_4 [0, -1, 1] = true := by decide +kernel
theorem subd9_4_46 : subd9_4 [0, -1, 2] = true := by decide +kernel
theorem subd9_4_47 : subd9_4 [0, -1, 3] = true := by decide +kernel
theorem subd9_4_48 : subd9_4 [0, -1, 4] = true := by decide +kernel
theorem subd9_4_49 : subd9_4 [0, -1, 5] = true := by decide +kernel
theorem subd9_4_50 : subd9_4 [0, -1, 6] = true := by decide +kernel
theorem subd9_4_51 : subd9_4 [0, -1, 7] = true := by decide +kernel
theorem subd9_4_52 : subd9_4 [0, -1, 8] = true := by decide +kernel
theorem subd9_4_53 : subd9_4 [0, 0, -10] = true := by decide +kernel
theorem subd9_4_54 : subd9_4 [0, 0, -9] = true := by decide +kernel
theorem subd9_4_55 : subd9_4 [0, 0, -8] = true := by decide +kernel
theorem subd9_4_56 : subd9_4 [0, 0, -7] = true := by decide +kernel
theorem subd9_4_57 : subd9_4 [0, 0, -6] = true := by decide +kernel
theorem subd9_4_58 : subd9_4 [0, 0, -5] = true := by decide +kernel
theorem subd9_4_59 : subd9_4 [0, 0, -4] = true := by decide +kernel
theorem subd9_4_60 : subd9_4 [0, 0, -3] = true := by decide +kernel
theorem subd9_4_61 : subd9_4 [0, 0, -2] = true := by decide +kernel
theorem subd9_4_62 : subd9_4 [0, 0, -1] = true := by decide +kernel
theorem subd9_4_63 : subd9_4 [0, 0, 0] = true := by decide +kernel
theorem sbd9_4_1 : ∀ q ∈ blkd9_4_1, subd9_4 q = true := by
  unfold blkd9_4_1
  exact List.forall_mem_cons.2 ⟨subd9_4_32, List.forall_mem_cons.2 ⟨subd9_4_33, List.forall_mem_cons.2 ⟨subd9_4_34, List.forall_mem_cons.2 ⟨subd9_4_35, List.forall_mem_cons.2 ⟨subd9_4_36, List.forall_mem_cons.2 ⟨subd9_4_37, List.forall_mem_cons.2 ⟨subd9_4_38, List.forall_mem_cons.2 ⟨subd9_4_39, List.forall_mem_cons.2 ⟨subd9_4_40, List.forall_mem_cons.2 ⟨subd9_4_41, List.forall_mem_cons.2 ⟨subd9_4_42, List.forall_mem_cons.2 ⟨subd9_4_43, List.forall_mem_cons.2 ⟨subd9_4_44, List.forall_mem_cons.2 ⟨subd9_4_45, List.forall_mem_cons.2 ⟨subd9_4_46, List.forall_mem_cons.2 ⟨subd9_4_47, List.forall_mem_cons.2 ⟨subd9_4_48, List.forall_mem_cons.2 ⟨subd9_4_49, List.forall_mem_cons.2 ⟨subd9_4_50, List.forall_mem_cons.2 ⟨subd9_4_51, List.forall_mem_cons.2 ⟨subd9_4_52, List.forall_mem_cons.2 ⟨subd9_4_53, List.forall_mem_cons.2 ⟨subd9_4_54, List.forall_mem_cons.2 ⟨subd9_4_55, List.forall_mem_cons.2 ⟨subd9_4_56, List.forall_mem_cons.2 ⟨subd9_4_57, List.forall_mem_cons.2 ⟨subd9_4_58, List.forall_mem_cons.2 ⟨subd9_4_59, List.forall_mem_cons.2 ⟨subd9_4_60, List.forall_mem_cons.2 ⟨subd9_4_61, List.forall_mem_cons.2 ⟨subd9_4_62, List.forall_mem_cons.2 ⟨subd9_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_64 : subd9_4 [0, 0, 1] = true := by decide +kernel
theorem subd9_4_65 : subd9_4 [0, 0, 2] = true := by decide +kernel
theorem subd9_4_66 : subd9_4 [0, 0, 3] = true := by decide +kernel
theorem subd9_4_67 : subd9_4 [0, 0, 4] = true := by decide +kernel
theorem subd9_4_68 : subd9_4 [0, 0, 5] = true := by decide +kernel
theorem subd9_4_69 : subd9_4 [0, 0, 6] = true := by decide +kernel
theorem subd9_4_70 : subd9_4 [0, 0, 7] = true := by decide +kernel
theorem subd9_4_71 : subd9_4 [0, 0, 8] = true := by decide +kernel
theorem subd9_4_72 : subd9_4 [0, 0, 9] = true := by decide +kernel
theorem subd9_4_73 : subd9_4 [0, 1, -9] = true := by decide +kernel
theorem subd9_4_74 : subd9_4 [0, 1, -8] = true := by decide +kernel
theorem subd9_4_75 : subd9_4 [0, 1, -7] = true := by decide +kernel
theorem subd9_4_76 : subd9_4 [0, 1, -6] = true := by decide +kernel
theorem subd9_4_77 : subd9_4 [0, 1, -5] = true := by decide +kernel
theorem subd9_4_78 : subd9_4 [0, 1, -4] = true := by decide +kernel
theorem subd9_4_79 : subd9_4 [0, 1, -3] = true := by decide +kernel
theorem subd9_4_80 : subd9_4 [0, 1, -2] = true := by decide +kernel
theorem subd9_4_81 : subd9_4 [0, 1, -1] = true := by decide +kernel
theorem subd9_4_82 : subd9_4 [0, 1, 0] = true := by decide +kernel
theorem subd9_4_83 : subd9_4 [0, 1, 1] = true := by decide +kernel
theorem subd9_4_84 : subd9_4 [0, 1, 2] = true := by decide +kernel
theorem subd9_4_85 : subd9_4 [0, 1, 3] = true := by decide +kernel
theorem subd9_4_86 : subd9_4 [0, 1, 4] = true := by decide +kernel
theorem subd9_4_87 : subd9_4 [0, 1, 5] = true := by decide +kernel
theorem subd9_4_88 : subd9_4 [0, 1, 6] = true := by decide +kernel
theorem subd9_4_89 : subd9_4 [0, 1, 7] = true := by decide +kernel
theorem subd9_4_90 : subd9_4 [0, 2] = true := by decide +kernel
theorem subd9_4_91 : subd9_4 [1, -2] = true := by decide +kernel
theorem subd9_4_92 : subd9_4 [1, -1] = true := by decide +kernel
theorem subd9_4_93 : subd9_4 [1, 0, -8] = true := by decide +kernel
theorem subd9_4_94 : subd9_4 [1, 0, -7] = true := by decide +kernel
theorem subd9_4_95 : subd9_4 [1, 0, -6] = true := by decide +kernel
theorem sbd9_4_2 : ∀ q ∈ blkd9_4_2, subd9_4 q = true := by
  unfold blkd9_4_2
  exact List.forall_mem_cons.2 ⟨subd9_4_64, List.forall_mem_cons.2 ⟨subd9_4_65, List.forall_mem_cons.2 ⟨subd9_4_66, List.forall_mem_cons.2 ⟨subd9_4_67, List.forall_mem_cons.2 ⟨subd9_4_68, List.forall_mem_cons.2 ⟨subd9_4_69, List.forall_mem_cons.2 ⟨subd9_4_70, List.forall_mem_cons.2 ⟨subd9_4_71, List.forall_mem_cons.2 ⟨subd9_4_72, List.forall_mem_cons.2 ⟨subd9_4_73, List.forall_mem_cons.2 ⟨subd9_4_74, List.forall_mem_cons.2 ⟨subd9_4_75, List.forall_mem_cons.2 ⟨subd9_4_76, List.forall_mem_cons.2 ⟨subd9_4_77, List.forall_mem_cons.2 ⟨subd9_4_78, List.forall_mem_cons.2 ⟨subd9_4_79, List.forall_mem_cons.2 ⟨subd9_4_80, List.forall_mem_cons.2 ⟨subd9_4_81, List.forall_mem_cons.2 ⟨subd9_4_82, List.forall_mem_cons.2 ⟨subd9_4_83, List.forall_mem_cons.2 ⟨subd9_4_84, List.forall_mem_cons.2 ⟨subd9_4_85, List.forall_mem_cons.2 ⟨subd9_4_86, List.forall_mem_cons.2 ⟨subd9_4_87, List.forall_mem_cons.2 ⟨subd9_4_88, List.forall_mem_cons.2 ⟨subd9_4_89, List.forall_mem_cons.2 ⟨subd9_4_90, List.forall_mem_cons.2 ⟨subd9_4_91, List.forall_mem_cons.2 ⟨subd9_4_92, List.forall_mem_cons.2 ⟨subd9_4_93, List.forall_mem_cons.2 ⟨subd9_4_94, List.forall_mem_cons.2 ⟨subd9_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_96 : subd9_4 [1, 0, -5] = true := by decide +kernel
theorem subd9_4_97 : subd9_4 [1, 0, -4] = true := by decide +kernel
theorem subd9_4_98 : subd9_4 [1, 0, -3] = true := by decide +kernel
theorem subd9_4_99 : subd9_4 [1, 0, -2] = true := by decide +kernel
theorem subd9_4_100 : subd9_4 [1, 0, -1] = true := by decide +kernel
theorem subd9_4_101 : subd9_4 [1, 0, 0] = true := by decide +kernel
theorem subd9_4_102 : subd9_4 [1, 0, 1] = true := by decide +kernel
theorem subd9_4_103 : subd9_4 [1, 0, 2] = true := by decide +kernel
theorem subd9_4_104 : subd9_4 [1, 0, 3] = true := by decide +kernel
theorem subd9_4_105 : subd9_4 [1, 0, 4] = true := by decide +kernel
theorem subd9_4_106 : subd9_4 [1, 0, 5] = true := by decide +kernel
theorem subd9_4_107 : subd9_4 [1, 0, 6] = true := by decide +kernel
theorem subd9_4_108 : subd9_4 [1, 0, 7] = true := by decide +kernel
theorem subd9_4_109 : subd9_4 [1, 1, -8] = true := by decide +kernel
theorem subd9_4_110 : subd9_4 [1, 1, -7] = true := by decide +kernel
theorem subd9_4_111 : subd9_4 [1, 1, -6] = true := by decide +kernel
theorem subd9_4_112 : subd9_4 [1, 1, -5] = true := by decide +kernel
theorem subd9_4_113 : subd9_4 [1, 1, -4] = true := by decide +kernel
theorem subd9_4_114 : subd9_4 [1, 1, -3] = true := by decide +kernel
theorem subd9_4_115 : subd9_4 [1, 1, -2] = true := by decide +kernel
theorem subd9_4_116 : subd9_4 [1, 1, -1] = true := by decide +kernel
theorem subd9_4_117 : subd9_4 [1, 1, 0] = true := by decide +kernel
theorem subd9_4_118 : subd9_4 [1, 1, 1] = true := by decide +kernel
theorem subd9_4_119 : subd9_4 [1, 1, 2] = true := by decide +kernel
theorem subd9_4_120 : subd9_4 [1, 1, 3] = true := by decide +kernel
theorem subd9_4_121 : subd9_4 [1, 1, 4] = true := by decide +kernel
theorem subd9_4_122 : subd9_4 [1, 1, 5] = true := by decide +kernel
theorem subd9_4_123 : subd9_4 [1, 1, 6] = true := by decide +kernel
theorem subd9_4_124 : subd9_4 [1, 2] = true := by decide +kernel
theorem sbd9_4_3 : ∀ q ∈ blkd9_4_3, subd9_4 q = true := by
  unfold blkd9_4_3
  exact List.forall_mem_cons.2 ⟨subd9_4_96, List.forall_mem_cons.2 ⟨subd9_4_97, List.forall_mem_cons.2 ⟨subd9_4_98, List.forall_mem_cons.2 ⟨subd9_4_99, List.forall_mem_cons.2 ⟨subd9_4_100, List.forall_mem_cons.2 ⟨subd9_4_101, List.forall_mem_cons.2 ⟨subd9_4_102, List.forall_mem_cons.2 ⟨subd9_4_103, List.forall_mem_cons.2 ⟨subd9_4_104, List.forall_mem_cons.2 ⟨subd9_4_105, List.forall_mem_cons.2 ⟨subd9_4_106, List.forall_mem_cons.2 ⟨subd9_4_107, List.forall_mem_cons.2 ⟨subd9_4_108, List.forall_mem_cons.2 ⟨subd9_4_109, List.forall_mem_cons.2 ⟨subd9_4_110, List.forall_mem_cons.2 ⟨subd9_4_111, List.forall_mem_cons.2 ⟨subd9_4_112, List.forall_mem_cons.2 ⟨subd9_4_113, List.forall_mem_cons.2 ⟨subd9_4_114, List.forall_mem_cons.2 ⟨subd9_4_115, List.forall_mem_cons.2 ⟨subd9_4_116, List.forall_mem_cons.2 ⟨subd9_4_117, List.forall_mem_cons.2 ⟨subd9_4_118, List.forall_mem_cons.2 ⟨subd9_4_119, List.forall_mem_cons.2 ⟨subd9_4_120, List.forall_mem_cons.2 ⟨subd9_4_121, List.forall_mem_cons.2 ⟨subd9_4_122, List.forall_mem_cons.2 ⟨subd9_4_123, List.forall_mem_cons.2 ⟨subd9_4_124, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-2] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-1] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [0] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [1] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [2] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
