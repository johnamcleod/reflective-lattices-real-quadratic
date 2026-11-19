import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_7_32 : subd6_7 [-1, -6] = true := by decide +kernel
theorem subd6_7_33 : subd6_7 [-1, -5] = true := by decide +kernel
theorem subd6_7_34 : subd6_7 [-1, -4] = true := by decide +kernel
theorem subd6_7_35 : subd6_7 [-1, -3] = true := by decide +kernel
theorem subd6_7_36 : subd6_7 [-1, -2] = true := by decide +kernel
theorem subd6_7_37 : subd6_7 [-1, -1] = true := by decide +kernel
theorem subd6_7_38 : subd6_7 [-1, 0] = true := by decide +kernel
theorem subd6_7_39 : subd6_7 [-1, 1] = true := by decide +kernel
theorem subd6_7_40 : subd6_7 [-1, 2] = true := by decide +kernel
theorem subd6_7_41 : subd6_7 [-1, 3] = true := by decide +kernel
theorem subd6_7_42 : subd6_7 [-1, 4] = true := by decide +kernel
theorem subd6_7_43 : subd6_7 [-1, 5] = true := by decide +kernel
theorem subd6_7_44 : subd6_7 [0, -6] = true := by decide +kernel
theorem subd6_7_45 : subd6_7 [0, -5] = true := by decide +kernel
theorem subd6_7_46 : subd6_7 [0, -4] = true := by decide +kernel
theorem subd6_7_47 : subd6_7 [0, -3] = true := by decide +kernel
theorem subd6_7_48 : subd6_7 [0, -2] = true := by decide +kernel
theorem subd6_7_49 : subd6_7 [0, -1] = true := by decide +kernel
theorem subd6_7_50 : subd6_7 [0, 0] = true := by decide +kernel
theorem subd6_7_51 : subd6_7 [0, 1] = true := by decide +kernel
theorem subd6_7_52 : subd6_7 [0, 2] = true := by decide +kernel
theorem subd6_7_53 : subd6_7 [0, 3] = true := by decide +kernel
theorem subd6_7_54 : subd6_7 [0, 4] = true := by decide +kernel
theorem subd6_7_55 : subd6_7 [0, 5] = true := by decide +kernel
theorem subd6_7_56 : subd6_7 [1, -6] = true := by decide +kernel
theorem subd6_7_57 : subd6_7 [1, -5] = true := by decide +kernel
theorem subd6_7_58 : subd6_7 [1, -4] = true := by decide +kernel
theorem subd6_7_59 : subd6_7 [1, -3] = true := by decide +kernel
theorem subd6_7_60 : subd6_7 [1, -2] = true := by decide +kernel
theorem subd6_7_61 : subd6_7 [1, -1] = true := by decide +kernel
theorem subd6_7_62 : subd6_7 [1, 0] = true := by decide +kernel
theorem subd6_7_63 : subd6_7 [1, 1] = true := by decide +kernel
theorem sbd6_7_1 : ∀ q ∈ blkd6_7_1, subd6_7 q = true := by
  unfold blkd6_7_1
  exact List.forall_mem_cons.2 ⟨subd6_7_32, List.forall_mem_cons.2 ⟨subd6_7_33, List.forall_mem_cons.2 ⟨subd6_7_34, List.forall_mem_cons.2 ⟨subd6_7_35, List.forall_mem_cons.2 ⟨subd6_7_36, List.forall_mem_cons.2 ⟨subd6_7_37, List.forall_mem_cons.2 ⟨subd6_7_38, List.forall_mem_cons.2 ⟨subd6_7_39, List.forall_mem_cons.2 ⟨subd6_7_40, List.forall_mem_cons.2 ⟨subd6_7_41, List.forall_mem_cons.2 ⟨subd6_7_42, List.forall_mem_cons.2 ⟨subd6_7_43, List.forall_mem_cons.2 ⟨subd6_7_44, List.forall_mem_cons.2 ⟨subd6_7_45, List.forall_mem_cons.2 ⟨subd6_7_46, List.forall_mem_cons.2 ⟨subd6_7_47, List.forall_mem_cons.2 ⟨subd6_7_48, List.forall_mem_cons.2 ⟨subd6_7_49, List.forall_mem_cons.2 ⟨subd6_7_50, List.forall_mem_cons.2 ⟨subd6_7_51, List.forall_mem_cons.2 ⟨subd6_7_52, List.forall_mem_cons.2 ⟨subd6_7_53, List.forall_mem_cons.2 ⟨subd6_7_54, List.forall_mem_cons.2 ⟨subd6_7_55, List.forall_mem_cons.2 ⟨subd6_7_56, List.forall_mem_cons.2 ⟨subd6_7_57, List.forall_mem_cons.2 ⟨subd6_7_58, List.forall_mem_cons.2 ⟨subd6_7_59, List.forall_mem_cons.2 ⟨subd6_7_60, List.forall_mem_cons.2 ⟨subd6_7_61, List.forall_mem_cons.2 ⟨subd6_7_62, List.forall_mem_cons.2 ⟨subd6_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_64 : subd6_7 [1, 2] = true := by decide +kernel
theorem subd6_7_65 : subd6_7 [1, 3] = true := by decide +kernel
theorem subd6_7_66 : subd6_7 [1, 4] = true := by decide +kernel
theorem subd6_7_67 : subd6_7 [1, 5] = true := by decide +kernel
theorem subd6_7_68 : subd6_7 [2, -5] = true := by decide +kernel
theorem subd6_7_69 : subd6_7 [2, -4] = true := by decide +kernel
theorem subd6_7_70 : subd6_7 [2, -3] = true := by decide +kernel
theorem subd6_7_71 : subd6_7 [2, -2] = true := by decide +kernel
theorem subd6_7_72 : subd6_7 [2, -1] = true := by decide +kernel
theorem subd6_7_73 : subd6_7 [2, 0] = true := by decide +kernel
theorem subd6_7_74 : subd6_7 [2, 1] = true := by decide +kernel
theorem subd6_7_75 : subd6_7 [2, 2] = true := by decide +kernel
theorem subd6_7_76 : subd6_7 [2, 3] = true := by decide +kernel
theorem subd6_7_77 : subd6_7 [2, 4] = true := by decide +kernel
theorem subd6_7_78 : subd6_7 [2, 5] = true := by decide +kernel
theorem subd6_7_79 : subd6_7 [3, -5] = true := by decide +kernel
theorem subd6_7_80 : subd6_7 [3, -4] = true := by decide +kernel
theorem subd6_7_81 : subd6_7 [3, -3] = true := by decide +kernel
theorem subd6_7_82 : subd6_7 [3, -2] = true := by decide +kernel
theorem subd6_7_83 : subd6_7 [3, -1] = true := by decide +kernel
theorem subd6_7_84 : subd6_7 [3, 0] = true := by decide +kernel
theorem subd6_7_85 : subd6_7 [3, 1] = true := by decide +kernel
theorem subd6_7_86 : subd6_7 [3, 2] = true := by decide +kernel
theorem subd6_7_87 : subd6_7 [3, 3] = true := by decide +kernel
theorem subd6_7_88 : subd6_7 [3, 4] = true := by decide +kernel
theorem subd6_7_89 : subd6_7 [3, 5] = true := by decide +kernel
theorem subd6_7_90 : subd6_7 [4, -4] = true := by decide +kernel
theorem subd6_7_91 : subd6_7 [4, -3] = true := by decide +kernel
theorem subd6_7_92 : subd6_7 [4, -2] = true := by decide +kernel
theorem subd6_7_93 : subd6_7 [4, -1] = true := by decide +kernel
theorem subd6_7_94 : subd6_7 [4, 0] = true := by decide +kernel
theorem subd6_7_95 : subd6_7 [4, 1] = true := by decide +kernel
theorem sbd6_7_2 : ∀ q ∈ blkd6_7_2, subd6_7 q = true := by
  unfold blkd6_7_2
  exact List.forall_mem_cons.2 ⟨subd6_7_64, List.forall_mem_cons.2 ⟨subd6_7_65, List.forall_mem_cons.2 ⟨subd6_7_66, List.forall_mem_cons.2 ⟨subd6_7_67, List.forall_mem_cons.2 ⟨subd6_7_68, List.forall_mem_cons.2 ⟨subd6_7_69, List.forall_mem_cons.2 ⟨subd6_7_70, List.forall_mem_cons.2 ⟨subd6_7_71, List.forall_mem_cons.2 ⟨subd6_7_72, List.forall_mem_cons.2 ⟨subd6_7_73, List.forall_mem_cons.2 ⟨subd6_7_74, List.forall_mem_cons.2 ⟨subd6_7_75, List.forall_mem_cons.2 ⟨subd6_7_76, List.forall_mem_cons.2 ⟨subd6_7_77, List.forall_mem_cons.2 ⟨subd6_7_78, List.forall_mem_cons.2 ⟨subd6_7_79, List.forall_mem_cons.2 ⟨subd6_7_80, List.forall_mem_cons.2 ⟨subd6_7_81, List.forall_mem_cons.2 ⟨subd6_7_82, List.forall_mem_cons.2 ⟨subd6_7_83, List.forall_mem_cons.2 ⟨subd6_7_84, List.forall_mem_cons.2 ⟨subd6_7_85, List.forall_mem_cons.2 ⟨subd6_7_86, List.forall_mem_cons.2 ⟨subd6_7_87, List.forall_mem_cons.2 ⟨subd6_7_88, List.forall_mem_cons.2 ⟨subd6_7_89, List.forall_mem_cons.2 ⟨subd6_7_90, List.forall_mem_cons.2 ⟨subd6_7_91, List.forall_mem_cons.2 ⟨subd6_7_92, List.forall_mem_cons.2 ⟨subd6_7_93, List.forall_mem_cons.2 ⟨subd6_7_94, List.forall_mem_cons.2 ⟨subd6_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_96 : subd6_7 [4, 2] = true := by decide +kernel
theorem subd6_7_97 : subd6_7 [4, 3] = true := by decide +kernel
theorem subd6_7_98 : subd6_7 [4, 4] = true := by decide +kernel
theorem subd6_7_99 : subd6_7 [5] = true := by decide +kernel
theorem sbd6_7_3 : ∀ q ∈ blkd6_7_3, subd6_7 q = true := by
  unfold blkd6_7_3
  exact List.forall_mem_cons.2 ⟨subd6_7_96, List.forall_mem_cons.2 ⟨subd6_7_97, List.forall_mem_cons.2 ⟨subd6_7_98, List.forall_mem_cons.2 ⟨subd6_7_99, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-5] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-4, -6] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-4, -5] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-4, -4] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-4, -3] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-4, -2] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-4, -1] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-4, 0] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-4, 1] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-3, -6] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-3, -5] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-3, -4] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-3, -3] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-3, -2] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-3, -1] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-3, 0] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-3, 1] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [-3, 2] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [-3, 3] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [-2, -7] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [-2, -6] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [-2, -5] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [-2, -3] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [-2, -2] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [-2, -1] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [-2, 0] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [-2, 1] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [-2, 2] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [-2, 3] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [-2, 4] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [-1, -7] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [-1, -6] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [-1, -5] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [-1, 4] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [-1, 5] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [0, -6] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [0, -5] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [0, 4] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [0, 5] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [1, -6] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [1, -5] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_62 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_63 : subd7_0 [1, 1] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_cons.2 ⟨subd7_0_62, List.forall_mem_cons.2 ⟨subd7_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
