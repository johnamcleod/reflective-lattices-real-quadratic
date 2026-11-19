import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_32 : subd6_2 [0, -6] = true := by decide +kernel
theorem subd6_2_33 : subd6_2 [0, -5] = true := by decide +kernel
theorem subd6_2_34 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_35 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_36 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_37 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_38 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_39 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_40 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_41 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_42 : subd6_2 [0, 4] = true := by decide +kernel
theorem subd6_2_43 : subd6_2 [0, 5] = true := by decide +kernel
theorem subd6_2_44 : subd6_2 [1, -6] = true := by decide +kernel
theorem subd6_2_45 : subd6_2 [1, -5] = true := by decide +kernel
theorem subd6_2_46 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_47 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_48 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_49 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_50 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_51 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_52 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_53 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_54 : subd6_2 [1, 4] = true := by decide +kernel
theorem subd6_2_55 : subd6_2 [2, -6] = true := by decide +kernel
theorem subd6_2_56 : subd6_2 [2, -5] = true := by decide +kernel
theorem subd6_2_57 : subd6_2 [2, -4] = true := by decide +kernel
theorem subd6_2_58 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_59 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_60 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_61 : subd6_2 [2, 0] = true := by decide +kernel
theorem subd6_2_62 : subd6_2 [2, 1] = true := by decide +kernel
theorem subd6_2_63 : subd6_2 [2, 2] = true := by decide +kernel
theorem sbd6_2_1 : ∀ q ∈ blkd6_2_1, subd6_2 q = true := by
  unfold blkd6_2_1
  exact List.forall_mem_cons.2 ⟨subd6_2_32, List.forall_mem_cons.2 ⟨subd6_2_33, List.forall_mem_cons.2 ⟨subd6_2_34, List.forall_mem_cons.2 ⟨subd6_2_35, List.forall_mem_cons.2 ⟨subd6_2_36, List.forall_mem_cons.2 ⟨subd6_2_37, List.forall_mem_cons.2 ⟨subd6_2_38, List.forall_mem_cons.2 ⟨subd6_2_39, List.forall_mem_cons.2 ⟨subd6_2_40, List.forall_mem_cons.2 ⟨subd6_2_41, List.forall_mem_cons.2 ⟨subd6_2_42, List.forall_mem_cons.2 ⟨subd6_2_43, List.forall_mem_cons.2 ⟨subd6_2_44, List.forall_mem_cons.2 ⟨subd6_2_45, List.forall_mem_cons.2 ⟨subd6_2_46, List.forall_mem_cons.2 ⟨subd6_2_47, List.forall_mem_cons.2 ⟨subd6_2_48, List.forall_mem_cons.2 ⟨subd6_2_49, List.forall_mem_cons.2 ⟨subd6_2_50, List.forall_mem_cons.2 ⟨subd6_2_51, List.forall_mem_cons.2 ⟨subd6_2_52, List.forall_mem_cons.2 ⟨subd6_2_53, List.forall_mem_cons.2 ⟨subd6_2_54, List.forall_mem_cons.2 ⟨subd6_2_55, List.forall_mem_cons.2 ⟨subd6_2_56, List.forall_mem_cons.2 ⟨subd6_2_57, List.forall_mem_cons.2 ⟨subd6_2_58, List.forall_mem_cons.2 ⟨subd6_2_59, List.forall_mem_cons.2 ⟨subd6_2_60, List.forall_mem_cons.2 ⟨subd6_2_61, List.forall_mem_cons.2 ⟨subd6_2_62, List.forall_mem_cons.2 ⟨subd6_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_64 : subd6_2 [2, 3] = true := by decide +kernel
theorem subd6_2_65 : subd6_2 [3, -6] = true := by decide +kernel
theorem subd6_2_66 : subd6_2 [3, -5] = true := by decide +kernel
theorem subd6_2_67 : subd6_2 [3, -4] = true := by decide +kernel
theorem subd6_2_68 : subd6_2 [3, -3] = true := by decide +kernel
theorem subd6_2_69 : subd6_2 [3, -2] = true := by decide +kernel
theorem subd6_2_70 : subd6_2 [3, -1] = true := by decide +kernel
theorem subd6_2_71 : subd6_2 [3, 0] = true := by decide +kernel
theorem subd6_2_72 : subd6_2 [3, 1] = true := by decide +kernel
theorem subd6_2_73 : subd6_2 [3, 2] = true := by decide +kernel
theorem subd6_2_74 : subd6_2 [4] = true := by decide +kernel
theorem subd6_2_75 : subd6_2 [5] = true := by decide +kernel
theorem sbd6_2_2 : ∀ q ∈ blkd6_2_2, subd6_2 q = true := by
  unfold blkd6_2_2
  exact List.forall_mem_cons.2 ⟨subd6_2_64, List.forall_mem_cons.2 ⟨subd6_2_65, List.forall_mem_cons.2 ⟨subd6_2_66, List.forall_mem_cons.2 ⟨subd6_2_67, List.forall_mem_cons.2 ⟨subd6_2_68, List.forall_mem_cons.2 ⟨subd6_2_69, List.forall_mem_cons.2 ⟨subd6_2_70, List.forall_mem_cons.2 ⟨subd6_2_71, List.forall_mem_cons.2 ⟨subd6_2_72, List.forall_mem_cons.2 ⟨subd6_2_73, List.forall_mem_cons.2 ⟨subd6_2_74, List.forall_mem_cons.2 ⟨subd6_2_75, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-1] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-5, -6] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-5, -5] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-5, -4] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-5, -3] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-5, -2] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-5, -1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-5, 0] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-5, 1] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-4, -7] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-4, -6] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-4, -5] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-4, -4] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-4, -3] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-4, -2] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-4, -1] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-4, 0] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-4, 1] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [-4, 2] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [-4, 3] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [-3, -7] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [-3, -6] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [-3, -5] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [-3, -4] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [-3, -3] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [-3, -2, -7] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [-3, -2, -6] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [-3, -2, -5] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [-3, -2, -4] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [-3, -2, -3] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [-3, -2, -2] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [-3, -2, -1] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [-3, -2, 0] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [-3, -2, 1] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [-3, -2, 2] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [-3, -2, 3] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [-3, -2, 4] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [-3, -2, 5] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [-3, -2, 6] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [-3, -1, -6] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [-3, -1, -5] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [-3, -1, -4] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [-3, -1, -3] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [-3, -1, -2] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [-3, -1, -1] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [-3, -1, 0] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [-3, -1, 1] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [-3, -1, 2] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [-3, -1, 3] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [-3, -1, 4] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [-3, -1, 5] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [-3, -1, 6] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [-3, -1, 7] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [-3, 0, -6] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [-3, 0, -5] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [-3, 0, -4] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [-3, 0, -3] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [-3, 0, -2] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [-3, 0, -1] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [-3, 0, 0] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [-3, 0, 1] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [-3, 0, 2] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [-3, 0, 3] = true := by decide +kernel
theorem subd7_0_62 : subd7_0 [-3, 0, 4] = true := by decide +kernel
theorem subd7_0_63 : subd7_0 [-3, 0, 5] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_cons.2 ⟨subd7_0_62, List.forall_mem_cons.2 ⟨subd7_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_64 : subd7_0 [-3, 0, 6] = true := by decide +kernel
theorem subd7_0_65 : subd7_0 [-3, 0, 7] = true := by decide +kernel
theorem subd7_0_66 : subd7_0 [-3, 1] = true := by decide +kernel
theorem subd7_0_67 : subd7_0 [-3, 2] = true := by decide +kernel
theorem subd7_0_68 : subd7_0 [-3, 3] = true := by decide +kernel
theorem subd7_0_69 : subd7_0 [-3, 4] = true := by decide +kernel
theorem subd7_0_70 : subd7_0 [-2, -7] = true := by decide +kernel
theorem subd7_0_71 : subd7_0 [-2, -6] = true := by decide +kernel
theorem subd7_0_72 : subd7_0 [-2, -5] = true := by decide +kernel
theorem subd7_0_73 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_74 : subd7_0 [-2, -3, -8] = true := by decide +kernel
theorem subd7_0_75 : subd7_0 [-2, -3, -7] = true := by decide +kernel
theorem subd7_0_76 : subd7_0 [-2, -3, -6] = true := by decide +kernel
theorem subd7_0_77 : subd7_0 [-2, -3, -5] = true := by decide +kernel
theorem subd7_0_78 : subd7_0 [-2, -3, -4] = true := by decide +kernel
theorem subd7_0_79 : subd7_0 [-2, -3, -3] = true := by decide +kernel
theorem subd7_0_80 : subd7_0 [-2, -3, -2] = true := by decide +kernel
theorem subd7_0_81 : subd7_0 [-2, -3, -1] = true := by decide +kernel
theorem subd7_0_82 : subd7_0 [-2, -3, 0] = true := by decide +kernel
theorem subd7_0_83 : subd7_0 [-2, -3, 1] = true := by decide +kernel
theorem subd7_0_84 : subd7_0 [-2, -3, 2] = true := by decide +kernel
theorem subd7_0_85 : subd7_0 [-2, -3, 3] = true := by decide +kernel
theorem subd7_0_86 : subd7_0 [-2, -3, 4] = true := by decide +kernel
theorem subd7_0_87 : subd7_0 [-2, -3, 5] = true := by decide +kernel
theorem subd7_0_88 : subd7_0 [-2, -3, 6] = true := by decide +kernel
theorem subd7_0_89 : subd7_0 [-2, -2, -7] = true := by decide +kernel
theorem subd7_0_90 : subd7_0 [-2, -2, -6] = true := by decide +kernel
theorem subd7_0_91 : subd7_0 [-2, -2, -5] = true := by decide +kernel
theorem subd7_0_92 : subd7_0 [-2, -2, -4] = true := by decide +kernel
theorem subd7_0_93 : subd7_0 [-2, -2, -3] = true := by decide +kernel
theorem subd7_0_94 : subd7_0 [-2, -2, -2] = true := by decide +kernel
theorem subd7_0_95 : subd7_0 [-2, -2, -1] = true := by decide +kernel
theorem sbd7_0_2 : ∀ q ∈ blkd7_0_2, subd7_0 q = true := by
  unfold blkd7_0_2
  exact List.forall_mem_cons.2 ⟨subd7_0_64, List.forall_mem_cons.2 ⟨subd7_0_65, List.forall_mem_cons.2 ⟨subd7_0_66, List.forall_mem_cons.2 ⟨subd7_0_67, List.forall_mem_cons.2 ⟨subd7_0_68, List.forall_mem_cons.2 ⟨subd7_0_69, List.forall_mem_cons.2 ⟨subd7_0_70, List.forall_mem_cons.2 ⟨subd7_0_71, List.forall_mem_cons.2 ⟨subd7_0_72, List.forall_mem_cons.2 ⟨subd7_0_73, List.forall_mem_cons.2 ⟨subd7_0_74, List.forall_mem_cons.2 ⟨subd7_0_75, List.forall_mem_cons.2 ⟨subd7_0_76, List.forall_mem_cons.2 ⟨subd7_0_77, List.forall_mem_cons.2 ⟨subd7_0_78, List.forall_mem_cons.2 ⟨subd7_0_79, List.forall_mem_cons.2 ⟨subd7_0_80, List.forall_mem_cons.2 ⟨subd7_0_81, List.forall_mem_cons.2 ⟨subd7_0_82, List.forall_mem_cons.2 ⟨subd7_0_83, List.forall_mem_cons.2 ⟨subd7_0_84, List.forall_mem_cons.2 ⟨subd7_0_85, List.forall_mem_cons.2 ⟨subd7_0_86, List.forall_mem_cons.2 ⟨subd7_0_87, List.forall_mem_cons.2 ⟨subd7_0_88, List.forall_mem_cons.2 ⟨subd7_0_89, List.forall_mem_cons.2 ⟨subd7_0_90, List.forall_mem_cons.2 ⟨subd7_0_91, List.forall_mem_cons.2 ⟨subd7_0_92, List.forall_mem_cons.2 ⟨subd7_0_93, List.forall_mem_cons.2 ⟨subd7_0_94, List.forall_mem_cons.2 ⟨subd7_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
