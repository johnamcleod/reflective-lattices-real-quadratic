import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_6_32 : subd7_6 [-1, -4] = true := by decide +kernel
theorem subd7_6_33 : subd7_6 [-1, -3] = true := by decide +kernel
theorem subd7_6_34 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_35 : subd7_6 [-1, -1] = true := by decide +kernel
theorem subd7_6_36 : subd7_6 [-1, 0] = true := by decide +kernel
theorem subd7_6_37 : subd7_6 [-1, 1] = true := by decide +kernel
theorem subd7_6_38 : subd7_6 [-1, 2] = true := by decide +kernel
theorem subd7_6_39 : subd7_6 [-1, 3] = true := by decide +kernel
theorem subd7_6_40 : subd7_6 [-1, 4] = true := by decide +kernel
theorem subd7_6_41 : subd7_6 [-1, 5] = true := by decide +kernel
theorem subd7_6_42 : subd7_6 [0, -6] = true := by decide +kernel
theorem subd7_6_43 : subd7_6 [0, -5] = true := by decide +kernel
theorem subd7_6_44 : subd7_6 [0, -4] = true := by decide +kernel
theorem subd7_6_45 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_46 : subd7_6 [0, -2] = true := by decide +kernel
theorem subd7_6_47 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_48 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_49 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_50 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_51 : subd7_6 [0, 3] = true := by decide +kernel
theorem subd7_6_52 : subd7_6 [0, 4] = true := by decide +kernel
theorem subd7_6_53 : subd7_6 [0, 5] = true := by decide +kernel
theorem subd7_6_54 : subd7_6 [1, -6] = true := by decide +kernel
theorem subd7_6_55 : subd7_6 [1, -5] = true := by decide +kernel
theorem subd7_6_56 : subd7_6 [1, -4] = true := by decide +kernel
theorem subd7_6_57 : subd7_6 [1, -3] = true := by decide +kernel
theorem subd7_6_58 : subd7_6 [1, -2] = true := by decide +kernel
theorem subd7_6_59 : subd7_6 [1, -1] = true := by decide +kernel
theorem subd7_6_60 : subd7_6 [1, 0] = true := by decide +kernel
theorem subd7_6_61 : subd7_6 [1, 1] = true := by decide +kernel
theorem subd7_6_62 : subd7_6 [1, 2] = true := by decide +kernel
theorem subd7_6_63 : subd7_6 [1, 3] = true := by decide +kernel
theorem sbd7_6_1 : ∀ q ∈ blkd7_6_1, subd7_6 q = true := by
  unfold blkd7_6_1
  exact List.forall_mem_cons.2 ⟨subd7_6_32, List.forall_mem_cons.2 ⟨subd7_6_33, List.forall_mem_cons.2 ⟨subd7_6_34, List.forall_mem_cons.2 ⟨subd7_6_35, List.forall_mem_cons.2 ⟨subd7_6_36, List.forall_mem_cons.2 ⟨subd7_6_37, List.forall_mem_cons.2 ⟨subd7_6_38, List.forall_mem_cons.2 ⟨subd7_6_39, List.forall_mem_cons.2 ⟨subd7_6_40, List.forall_mem_cons.2 ⟨subd7_6_41, List.forall_mem_cons.2 ⟨subd7_6_42, List.forall_mem_cons.2 ⟨subd7_6_43, List.forall_mem_cons.2 ⟨subd7_6_44, List.forall_mem_cons.2 ⟨subd7_6_45, List.forall_mem_cons.2 ⟨subd7_6_46, List.forall_mem_cons.2 ⟨subd7_6_47, List.forall_mem_cons.2 ⟨subd7_6_48, List.forall_mem_cons.2 ⟨subd7_6_49, List.forall_mem_cons.2 ⟨subd7_6_50, List.forall_mem_cons.2 ⟨subd7_6_51, List.forall_mem_cons.2 ⟨subd7_6_52, List.forall_mem_cons.2 ⟨subd7_6_53, List.forall_mem_cons.2 ⟨subd7_6_54, List.forall_mem_cons.2 ⟨subd7_6_55, List.forall_mem_cons.2 ⟨subd7_6_56, List.forall_mem_cons.2 ⟨subd7_6_57, List.forall_mem_cons.2 ⟨subd7_6_58, List.forall_mem_cons.2 ⟨subd7_6_59, List.forall_mem_cons.2 ⟨subd7_6_60, List.forall_mem_cons.2 ⟨subd7_6_61, List.forall_mem_cons.2 ⟨subd7_6_62, List.forall_mem_cons.2 ⟨subd7_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_64 : subd7_6 [1, 4] = true := by decide +kernel
theorem subd7_6_65 : subd7_6 [1, 5] = true := by decide +kernel
theorem subd7_6_66 : subd7_6 [2, -6] = true := by decide +kernel
theorem subd7_6_67 : subd7_6 [2, -5] = true := by decide +kernel
theorem subd7_6_68 : subd7_6 [2, -4] = true := by decide +kernel
theorem subd7_6_69 : subd7_6 [2, -3] = true := by decide +kernel
theorem subd7_6_70 : subd7_6 [2, -2] = true := by decide +kernel
theorem subd7_6_71 : subd7_6 [2, -1] = true := by decide +kernel
theorem subd7_6_72 : subd7_6 [2, 0] = true := by decide +kernel
theorem subd7_6_73 : subd7_6 [2, 1] = true := by decide +kernel
theorem subd7_6_74 : subd7_6 [2, 2] = true := by decide +kernel
theorem subd7_6_75 : subd7_6 [2, 3] = true := by decide +kernel
theorem subd7_6_76 : subd7_6 [2, 4] = true := by decide +kernel
theorem subd7_6_77 : subd7_6 [3, -6] = true := by decide +kernel
theorem subd7_6_78 : subd7_6 [3, -5] = true := by decide +kernel
theorem subd7_6_79 : subd7_6 [3, -4] = true := by decide +kernel
theorem subd7_6_80 : subd7_6 [3, -3] = true := by decide +kernel
theorem subd7_6_81 : subd7_6 [3, -2] = true := by decide +kernel
theorem subd7_6_82 : subd7_6 [3, -1] = true := by decide +kernel
theorem subd7_6_83 : subd7_6 [3, 0] = true := by decide +kernel
theorem subd7_6_84 : subd7_6 [3, 1] = true := by decide +kernel
theorem subd7_6_85 : subd7_6 [3, 2] = true := by decide +kernel
theorem subd7_6_86 : subd7_6 [3, 3] = true := by decide +kernel
theorem subd7_6_87 : subd7_6 [4, -5] = true := by decide +kernel
theorem subd7_6_88 : subd7_6 [4, -4] = true := by decide +kernel
theorem subd7_6_89 : subd7_6 [4, -3] = true := by decide +kernel
theorem subd7_6_90 : subd7_6 [4, -2] = true := by decide +kernel
theorem subd7_6_91 : subd7_6 [4, -1] = true := by decide +kernel
theorem subd7_6_92 : subd7_6 [4, 0] = true := by decide +kernel
theorem subd7_6_93 : subd7_6 [4, 1] = true := by decide +kernel
theorem subd7_6_94 : subd7_6 [4, 2] = true := by decide +kernel
theorem subd7_6_95 : subd7_6 [5] = true := by decide +kernel
theorem sbd7_6_2 : ∀ q ∈ blkd7_6_2, subd7_6 q = true := by
  unfold blkd7_6_2
  exact List.forall_mem_cons.2 ⟨subd7_6_64, List.forall_mem_cons.2 ⟨subd7_6_65, List.forall_mem_cons.2 ⟨subd7_6_66, List.forall_mem_cons.2 ⟨subd7_6_67, List.forall_mem_cons.2 ⟨subd7_6_68, List.forall_mem_cons.2 ⟨subd7_6_69, List.forall_mem_cons.2 ⟨subd7_6_70, List.forall_mem_cons.2 ⟨subd7_6_71, List.forall_mem_cons.2 ⟨subd7_6_72, List.forall_mem_cons.2 ⟨subd7_6_73, List.forall_mem_cons.2 ⟨subd7_6_74, List.forall_mem_cons.2 ⟨subd7_6_75, List.forall_mem_cons.2 ⟨subd7_6_76, List.forall_mem_cons.2 ⟨subd7_6_77, List.forall_mem_cons.2 ⟨subd7_6_78, List.forall_mem_cons.2 ⟨subd7_6_79, List.forall_mem_cons.2 ⟨subd7_6_80, List.forall_mem_cons.2 ⟨subd7_6_81, List.forall_mem_cons.2 ⟨subd7_6_82, List.forall_mem_cons.2 ⟨subd7_6_83, List.forall_mem_cons.2 ⟨subd7_6_84, List.forall_mem_cons.2 ⟨subd7_6_85, List.forall_mem_cons.2 ⟨subd7_6_86, List.forall_mem_cons.2 ⟨subd7_6_87, List.forall_mem_cons.2 ⟨subd7_6_88, List.forall_mem_cons.2 ⟨subd7_6_89, List.forall_mem_cons.2 ⟨subd7_6_90, List.forall_mem_cons.2 ⟨subd7_6_91, List.forall_mem_cons.2 ⟨subd7_6_92, List.forall_mem_cons.2 ⟨subd7_6_93, List.forall_mem_cons.2 ⟨subd7_6_94, List.forall_mem_cons.2 ⟨subd7_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel
theorem subd7_7_0 : subd7_7 [-5, -3] = true := by decide +kernel
theorem subd7_7_1 : subd7_7 [-5, -2] = true := by decide +kernel
theorem subd7_7_2 : subd7_7 [-5, -1] = true := by decide +kernel
theorem subd7_7_3 : subd7_7 [-5, 0] = true := by decide +kernel
theorem subd7_7_4 : subd7_7 [-5, 1] = true := by decide +kernel
theorem subd7_7_5 : subd7_7 [-5, 2] = true := by decide +kernel
theorem subd7_7_6 : subd7_7 [-5, 3] = true := by decide +kernel
theorem subd7_7_7 : subd7_7 [-4, -5] = true := by decide +kernel
theorem subd7_7_8 : subd7_7 [-4, -4] = true := by decide +kernel
theorem subd7_7_9 : subd7_7 [-4, -3] = true := by decide +kernel
theorem subd7_7_10 : subd7_7 [-4, -2] = true := by decide +kernel
theorem subd7_7_11 : subd7_7 [-4, -1] = true := by decide +kernel
theorem subd7_7_12 : subd7_7 [-4, 0] = true := by decide +kernel
theorem subd7_7_13 : subd7_7 [-4, 1] = true := by decide +kernel
theorem subd7_7_14 : subd7_7 [-4, 2] = true := by decide +kernel
theorem subd7_7_15 : subd7_7 [-4, 3] = true := by decide +kernel
theorem subd7_7_16 : subd7_7 [-4, 4] = true := by decide +kernel
theorem subd7_7_17 : subd7_7 [-3, -6] = true := by decide +kernel
theorem subd7_7_18 : subd7_7 [-3, -5] = true := by decide +kernel
theorem subd7_7_19 : subd7_7 [-3, -4] = true := by decide +kernel
theorem subd7_7_20 : subd7_7 [-3, -3] = true := by decide +kernel
theorem subd7_7_21 : subd7_7 [-3, -2] = true := by decide +kernel
theorem subd7_7_22 : subd7_7 [-3, -1] = true := by decide +kernel
theorem subd7_7_23 : subd7_7 [-3, 0] = true := by decide +kernel
theorem subd7_7_24 : subd7_7 [-3, 1] = true := by decide +kernel
theorem subd7_7_25 : subd7_7 [-3, 2] = true := by decide +kernel
theorem subd7_7_26 : subd7_7 [-3, 3] = true := by decide +kernel
theorem subd7_7_27 : subd7_7 [-3, 4] = true := by decide +kernel
theorem subd7_7_28 : subd7_7 [-3, 5] = true := by decide +kernel
theorem subd7_7_29 : subd7_7 [-2, -6] = true := by decide +kernel
theorem subd7_7_30 : subd7_7 [-2, -5] = true := by decide +kernel
theorem subd7_7_31 : subd7_7 [-2, -4] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_cons.2 ⟨subd7_7_1, List.forall_mem_cons.2 ⟨subd7_7_2, List.forall_mem_cons.2 ⟨subd7_7_3, List.forall_mem_cons.2 ⟨subd7_7_4, List.forall_mem_cons.2 ⟨subd7_7_5, List.forall_mem_cons.2 ⟨subd7_7_6, List.forall_mem_cons.2 ⟨subd7_7_7, List.forall_mem_cons.2 ⟨subd7_7_8, List.forall_mem_cons.2 ⟨subd7_7_9, List.forall_mem_cons.2 ⟨subd7_7_10, List.forall_mem_cons.2 ⟨subd7_7_11, List.forall_mem_cons.2 ⟨subd7_7_12, List.forall_mem_cons.2 ⟨subd7_7_13, List.forall_mem_cons.2 ⟨subd7_7_14, List.forall_mem_cons.2 ⟨subd7_7_15, List.forall_mem_cons.2 ⟨subd7_7_16, List.forall_mem_cons.2 ⟨subd7_7_17, List.forall_mem_cons.2 ⟨subd7_7_18, List.forall_mem_cons.2 ⟨subd7_7_19, List.forall_mem_cons.2 ⟨subd7_7_20, List.forall_mem_cons.2 ⟨subd7_7_21, List.forall_mem_cons.2 ⟨subd7_7_22, List.forall_mem_cons.2 ⟨subd7_7_23, List.forall_mem_cons.2 ⟨subd7_7_24, List.forall_mem_cons.2 ⟨subd7_7_25, List.forall_mem_cons.2 ⟨subd7_7_26, List.forall_mem_cons.2 ⟨subd7_7_27, List.forall_mem_cons.2 ⟨subd7_7_28, List.forall_mem_cons.2 ⟨subd7_7_29, List.forall_mem_cons.2 ⟨subd7_7_30, List.forall_mem_cons.2 ⟨subd7_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_32 : subd7_7 [-2, -3] = true := by decide +kernel
theorem subd7_7_33 : subd7_7 [-2, -2] = true := by decide +kernel
theorem subd7_7_34 : subd7_7 [-2, -1] = true := by decide +kernel
theorem subd7_7_35 : subd7_7 [-2, 0] = true := by decide +kernel
theorem subd7_7_36 : subd7_7 [-2, 1] = true := by decide +kernel
theorem subd7_7_37 : subd7_7 [-2, 2] = true := by decide +kernel
theorem subd7_7_38 : subd7_7 [-2, 3] = true := by decide +kernel
theorem subd7_7_39 : subd7_7 [-2, 4] = true := by decide +kernel
theorem subd7_7_40 : subd7_7 [-2, 5] = true := by decide +kernel
theorem subd7_7_41 : subd7_7 [-2, 6] = true := by decide +kernel
theorem subd7_7_42 : subd7_7 [-1, -7] = true := by decide +kernel
theorem subd7_7_43 : subd7_7 [-1, -6] = true := by decide +kernel
theorem subd7_7_44 : subd7_7 [-1, -5] = true := by decide +kernel
theorem subd7_7_45 : subd7_7 [-1, -4] = true := by decide +kernel
theorem subd7_7_46 : subd7_7 [-1, -3] = true := by decide +kernel
theorem subd7_7_47 : subd7_7 [-1, -2] = true := by decide +kernel
theorem subd7_7_48 : subd7_7 [-1, -1] = true := by decide +kernel
theorem subd7_7_49 : subd7_7 [-1, 0] = true := by decide +kernel
theorem subd7_7_50 : subd7_7 [-1, 1] = true := by decide +kernel
theorem subd7_7_51 : subd7_7 [-1, 2] = true := by decide +kernel
theorem subd7_7_52 : subd7_7 [-1, 3] = true := by decide +kernel
theorem subd7_7_53 : subd7_7 [-1, 4] = true := by decide +kernel
theorem subd7_7_54 : subd7_7 [-1, 5] = true := by decide +kernel
theorem subd7_7_55 : subd7_7 [-1, 6] = true := by decide +kernel
theorem subd7_7_56 : subd7_7 [0, -7] = true := by decide +kernel
theorem subd7_7_57 : subd7_7 [0, -6] = true := by decide +kernel
theorem subd7_7_58 : subd7_7 [0, -5] = true := by decide +kernel
theorem subd7_7_59 : subd7_7 [0, -4] = true := by decide +kernel
theorem subd7_7_60 : subd7_7 [0, -3] = true := by decide +kernel
theorem subd7_7_61 : subd7_7 [0, -2] = true := by decide +kernel
theorem subd7_7_62 : subd7_7 [0, -1] = true := by decide +kernel
theorem subd7_7_63 : subd7_7 [0, 0] = true := by decide +kernel
theorem sbd7_7_1 : ∀ q ∈ blkd7_7_1, subd7_7 q = true := by
  unfold blkd7_7_1
  exact List.forall_mem_cons.2 ⟨subd7_7_32, List.forall_mem_cons.2 ⟨subd7_7_33, List.forall_mem_cons.2 ⟨subd7_7_34, List.forall_mem_cons.2 ⟨subd7_7_35, List.forall_mem_cons.2 ⟨subd7_7_36, List.forall_mem_cons.2 ⟨subd7_7_37, List.forall_mem_cons.2 ⟨subd7_7_38, List.forall_mem_cons.2 ⟨subd7_7_39, List.forall_mem_cons.2 ⟨subd7_7_40, List.forall_mem_cons.2 ⟨subd7_7_41, List.forall_mem_cons.2 ⟨subd7_7_42, List.forall_mem_cons.2 ⟨subd7_7_43, List.forall_mem_cons.2 ⟨subd7_7_44, List.forall_mem_cons.2 ⟨subd7_7_45, List.forall_mem_cons.2 ⟨subd7_7_46, List.forall_mem_cons.2 ⟨subd7_7_47, List.forall_mem_cons.2 ⟨subd7_7_48, List.forall_mem_cons.2 ⟨subd7_7_49, List.forall_mem_cons.2 ⟨subd7_7_50, List.forall_mem_cons.2 ⟨subd7_7_51, List.forall_mem_cons.2 ⟨subd7_7_52, List.forall_mem_cons.2 ⟨subd7_7_53, List.forall_mem_cons.2 ⟨subd7_7_54, List.forall_mem_cons.2 ⟨subd7_7_55, List.forall_mem_cons.2 ⟨subd7_7_56, List.forall_mem_cons.2 ⟨subd7_7_57, List.forall_mem_cons.2 ⟨subd7_7_58, List.forall_mem_cons.2 ⟨subd7_7_59, List.forall_mem_cons.2 ⟨subd7_7_60, List.forall_mem_cons.2 ⟨subd7_7_61, List.forall_mem_cons.2 ⟨subd7_7_62, List.forall_mem_cons.2 ⟨subd7_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
