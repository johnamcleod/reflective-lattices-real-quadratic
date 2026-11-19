import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_64 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_65 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_66 : subd7_0 [1, 4] = true := by decide +kernel
theorem subd7_0_67 : subd7_0 [1, 5] = true := by decide +kernel
theorem subd7_0_68 : subd7_0 [1, 6] = true := by decide +kernel
theorem subd7_0_69 : subd7_0 [2, -5] = true := by decide +kernel
theorem subd7_0_70 : subd7_0 [2, -4] = true := by decide +kernel
theorem subd7_0_71 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_72 : subd7_0 [2, -2] = true := by decide +kernel
theorem subd7_0_73 : subd7_0 [2, -1] = true := by decide +kernel
theorem subd7_0_74 : subd7_0 [2, 0] = true := by decide +kernel
theorem subd7_0_75 : subd7_0 [2, 1] = true := by decide +kernel
theorem subd7_0_76 : subd7_0 [2, 2] = true := by decide +kernel
theorem subd7_0_77 : subd7_0 [2, 3] = true := by decide +kernel
theorem subd7_0_78 : subd7_0 [2, 4] = true := by decide +kernel
theorem subd7_0_79 : subd7_0 [2, 5] = true := by decide +kernel
theorem subd7_0_80 : subd7_0 [2, 6] = true := by decide +kernel
theorem subd7_0_81 : subd7_0 [3, -4] = true := by decide +kernel
theorem subd7_0_82 : subd7_0 [3, -3] = true := by decide +kernel
theorem subd7_0_83 : subd7_0 [3, -2] = true := by decide +kernel
theorem subd7_0_84 : subd7_0 [3, -1] = true := by decide +kernel
theorem subd7_0_85 : subd7_0 [3, 0] = true := by decide +kernel
theorem subd7_0_86 : subd7_0 [3, 1] = true := by decide +kernel
theorem subd7_0_87 : subd7_0 [3, 2] = true := by decide +kernel
theorem subd7_0_88 : subd7_0 [3, 3] = true := by decide +kernel
theorem subd7_0_89 : subd7_0 [3, 4] = true := by decide +kernel
theorem subd7_0_90 : subd7_0 [3, 5] = true := by decide +kernel
theorem subd7_0_91 : subd7_0 [4, -2] = true := by decide +kernel
theorem subd7_0_92 : subd7_0 [4, -1] = true := by decide +kernel
theorem subd7_0_93 : subd7_0 [4, 0] = true := by decide +kernel
theorem subd7_0_94 : subd7_0 [4, 1] = true := by decide +kernel
theorem subd7_0_95 : subd7_0 [4, 2] = true := by decide +kernel
theorem sbd7_0_2 : ∀ q ∈ blkd7_0_2, subd7_0 q = true := by
  unfold blkd7_0_2
  exact List.forall_mem_cons.2 ⟨subd7_0_64, List.forall_mem_cons.2 ⟨subd7_0_65, List.forall_mem_cons.2 ⟨subd7_0_66, List.forall_mem_cons.2 ⟨subd7_0_67, List.forall_mem_cons.2 ⟨subd7_0_68, List.forall_mem_cons.2 ⟨subd7_0_69, List.forall_mem_cons.2 ⟨subd7_0_70, List.forall_mem_cons.2 ⟨subd7_0_71, List.forall_mem_cons.2 ⟨subd7_0_72, List.forall_mem_cons.2 ⟨subd7_0_73, List.forall_mem_cons.2 ⟨subd7_0_74, List.forall_mem_cons.2 ⟨subd7_0_75, List.forall_mem_cons.2 ⟨subd7_0_76, List.forall_mem_cons.2 ⟨subd7_0_77, List.forall_mem_cons.2 ⟨subd7_0_78, List.forall_mem_cons.2 ⟨subd7_0_79, List.forall_mem_cons.2 ⟨subd7_0_80, List.forall_mem_cons.2 ⟨subd7_0_81, List.forall_mem_cons.2 ⟨subd7_0_82, List.forall_mem_cons.2 ⟨subd7_0_83, List.forall_mem_cons.2 ⟨subd7_0_84, List.forall_mem_cons.2 ⟨subd7_0_85, List.forall_mem_cons.2 ⟨subd7_0_86, List.forall_mem_cons.2 ⟨subd7_0_87, List.forall_mem_cons.2 ⟨subd7_0_88, List.forall_mem_cons.2 ⟨subd7_0_89, List.forall_mem_cons.2 ⟨subd7_0_90, List.forall_mem_cons.2 ⟨subd7_0_91, List.forall_mem_cons.2 ⟨subd7_0_92, List.forall_mem_cons.2 ⟨subd7_0_93, List.forall_mem_cons.2 ⟨subd7_0_94, List.forall_mem_cons.2 ⟨subd7_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_96 : subd7_0 [4, 3] = true := by decide +kernel
theorem subd7_0_97 : subd7_0 [4, 4] = true := by decide +kernel
theorem subd7_0_98 : subd7_0 [4, 5] = true := by decide +kernel
theorem subd7_0_99 : subd7_0 [5] = true := by decide +kernel
theorem sbd7_0_3 : ∀ q ∈ blkd7_0_3, subd7_0 q = true := by
  unfold blkd7_0_3
  exact List.forall_mem_cons.2 ⟨subd7_0_96, List.forall_mem_cons.2 ⟨subd7_0_97, List.forall_mem_cons.2 ⟨subd7_0_98, List.forall_mem_cons.2 ⟨subd7_0_99, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-5, -6] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-5, -5] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-5, -4] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-5, -3] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-5, -2] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-5, -1] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-5, 0] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-5, 1] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-5, 2] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-4, -7] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [-4, -6] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [-4, -5] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [-4, -4] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [-4, -3] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [-4, -2] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [-4, -1] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [-4, 0] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [-4, 1] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [-4, 2] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [-4, 3] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [-3, -8] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [-3, -7] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [-3, -6] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [-3, -5] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [-3, -4] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [-3, -3] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [-3, -2] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [-3, -1] = true := by decide +kernel
theorem subd7_1_28 : subd7_1 [-3, 0] = true := by decide +kernel
theorem subd7_1_29 : subd7_1 [-3, 1] = true := by decide +kernel
theorem subd7_1_30 : subd7_1 [-3, 2] = true := by decide +kernel
theorem subd7_1_31 : subd7_1 [-3, 3] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_cons.2 ⟨subd7_1_28, List.forall_mem_cons.2 ⟨subd7_1_29, List.forall_mem_cons.2 ⟨subd7_1_30, List.forall_mem_cons.2 ⟨subd7_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_32 : subd7_1 [-3, 4] = true := by decide +kernel
theorem subd7_1_33 : subd7_1 [-3, 5] = true := by decide +kernel
theorem subd7_1_34 : subd7_1 [-2, -8] = true := by decide +kernel
theorem subd7_1_35 : subd7_1 [-2, -7] = true := by decide +kernel
theorem subd7_1_36 : subd7_1 [-2, -6] = true := by decide +kernel
theorem subd7_1_37 : subd7_1 [-2, -5] = true := by decide +kernel
theorem subd7_1_38 : subd7_1 [-2, -4] = true := by decide +kernel
theorem subd7_1_39 : subd7_1 [-2, -3] = true := by decide +kernel
theorem subd7_1_40 : subd7_1 [-2, -2] = true := by decide +kernel
theorem subd7_1_41 : subd7_1 [-2, -1, -6] = true := by decide +kernel
theorem subd7_1_42 : subd7_1 [-2, -1, -5] = true := by decide +kernel
theorem subd7_1_43 : subd7_1 [-2, -1, -4] = true := by decide +kernel
theorem subd7_1_44 : subd7_1 [-2, -1, -3] = true := by decide +kernel
theorem subd7_1_45 : subd7_1 [-2, -1, -2] = true := by decide +kernel
theorem subd7_1_46 : subd7_1 [-2, -1, -1] = true := by decide +kernel
theorem subd7_1_47 : subd7_1 [-2, -1, 0] = true := by decide +kernel
theorem subd7_1_48 : subd7_1 [-2, -1, 1] = true := by decide +kernel
theorem subd7_1_49 : subd7_1 [-2, -1, 2] = true := by decide +kernel
theorem subd7_1_50 : subd7_1 [-2, -1, 3] = true := by decide +kernel
theorem subd7_1_51 : subd7_1 [-2, -1, 4] = true := by decide +kernel
theorem subd7_1_52 : subd7_1 [-2, -1, 5] = true := by decide +kernel
theorem subd7_1_53 : subd7_1 [-2, -1, 6] = true := by decide +kernel
theorem subd7_1_54 : subd7_1 [-2, 0, -6] = true := by decide +kernel
theorem subd7_1_55 : subd7_1 [-2, 0, -5] = true := by decide +kernel
theorem subd7_1_56 : subd7_1 [-2, 0, -4] = true := by decide +kernel
theorem subd7_1_57 : subd7_1 [-2, 0, -3] = true := by decide +kernel
theorem subd7_1_58 : subd7_1 [-2, 0, -2] = true := by decide +kernel
theorem subd7_1_59 : subd7_1 [-2, 0, -1] = true := by decide +kernel
theorem subd7_1_60 : subd7_1 [-2, 0, 0] = true := by decide +kernel
theorem subd7_1_61 : subd7_1 [-2, 0, 1] = true := by decide +kernel
theorem subd7_1_62 : subd7_1 [-2, 0, 2] = true := by decide +kernel
theorem subd7_1_63 : subd7_1 [-2, 0, 3] = true := by decide +kernel
theorem sbd7_1_1 : ∀ q ∈ blkd7_1_1, subd7_1 q = true := by
  unfold blkd7_1_1
  exact List.forall_mem_cons.2 ⟨subd7_1_32, List.forall_mem_cons.2 ⟨subd7_1_33, List.forall_mem_cons.2 ⟨subd7_1_34, List.forall_mem_cons.2 ⟨subd7_1_35, List.forall_mem_cons.2 ⟨subd7_1_36, List.forall_mem_cons.2 ⟨subd7_1_37, List.forall_mem_cons.2 ⟨subd7_1_38, List.forall_mem_cons.2 ⟨subd7_1_39, List.forall_mem_cons.2 ⟨subd7_1_40, List.forall_mem_cons.2 ⟨subd7_1_41, List.forall_mem_cons.2 ⟨subd7_1_42, List.forall_mem_cons.2 ⟨subd7_1_43, List.forall_mem_cons.2 ⟨subd7_1_44, List.forall_mem_cons.2 ⟨subd7_1_45, List.forall_mem_cons.2 ⟨subd7_1_46, List.forall_mem_cons.2 ⟨subd7_1_47, List.forall_mem_cons.2 ⟨subd7_1_48, List.forall_mem_cons.2 ⟨subd7_1_49, List.forall_mem_cons.2 ⟨subd7_1_50, List.forall_mem_cons.2 ⟨subd7_1_51, List.forall_mem_cons.2 ⟨subd7_1_52, List.forall_mem_cons.2 ⟨subd7_1_53, List.forall_mem_cons.2 ⟨subd7_1_54, List.forall_mem_cons.2 ⟨subd7_1_55, List.forall_mem_cons.2 ⟨subd7_1_56, List.forall_mem_cons.2 ⟨subd7_1_57, List.forall_mem_cons.2 ⟨subd7_1_58, List.forall_mem_cons.2 ⟨subd7_1_59, List.forall_mem_cons.2 ⟨subd7_1_60, List.forall_mem_cons.2 ⟨subd7_1_61, List.forall_mem_cons.2 ⟨subd7_1_62, List.forall_mem_cons.2 ⟨subd7_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_64 : subd7_1 [-2, 0, 4] = true := by decide +kernel
theorem subd7_1_65 : subd7_1 [-2, 0, 5] = true := by decide +kernel
theorem subd7_1_66 : subd7_1 [-2, 0, 6] = true := by decide +kernel
theorem subd7_1_67 : subd7_1 [-2, 1] = true := by decide +kernel
theorem subd7_1_68 : subd7_1 [-2, 2] = true := by decide +kernel
theorem subd7_1_69 : subd7_1 [-2, 3] = true := by decide +kernel
theorem subd7_1_70 : subd7_1 [-2, 4] = true := by decide +kernel
theorem subd7_1_71 : subd7_1 [-2, 5] = true := by decide +kernel
theorem subd7_1_72 : subd7_1 [-2, 6] = true := by decide +kernel
theorem subd7_1_73 : subd7_1 [-1, -8] = true := by decide +kernel
theorem subd7_1_74 : subd7_1 [-1, -7] = true := by decide +kernel
theorem subd7_1_75 : subd7_1 [-1, -6] = true := by decide +kernel
theorem subd7_1_76 : subd7_1 [-1, -5] = true := by decide +kernel
theorem subd7_1_77 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_78 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_79 : subd7_1 [-1, -2, -6] = true := by decide +kernel
theorem subd7_1_80 : subd7_1 [-1, -2, -5] = true := by decide +kernel
theorem subd7_1_81 : subd7_1 [-1, -2, -4] = true := by decide +kernel
theorem subd7_1_82 : subd7_1 [-1, -2, -3] = true := by decide +kernel
theorem subd7_1_83 : subd7_1 [-1, -2, -2] = true := by decide +kernel
theorem subd7_1_84 : subd7_1 [-1, -2, -1] = true := by decide +kernel
theorem subd7_1_85 : subd7_1 [-1, -2, 0] = true := by decide +kernel
theorem subd7_1_86 : subd7_1 [-1, -2, 1] = true := by decide +kernel
theorem subd7_1_87 : subd7_1 [-1, -2, 2] = true := by decide +kernel
theorem subd7_1_88 : subd7_1 [-1, -2, 3] = true := by decide +kernel
theorem subd7_1_89 : subd7_1 [-1, -2, 4] = true := by decide +kernel
theorem subd7_1_90 : subd7_1 [-1, -2, 5] = true := by decide +kernel
theorem subd7_1_91 : subd7_1 [-1, -2, 6] = true := by decide +kernel
theorem subd7_1_92 : subd7_1 [-1, -1, -6] = true := by decide +kernel
theorem subd7_1_93 : subd7_1 [-1, -1, -5] = true := by decide +kernel
theorem subd7_1_94 : subd7_1 [-1, -1, -4] = true := by decide +kernel
theorem subd7_1_95 : subd7_1 [-1, -1, -3] = true := by decide +kernel
theorem sbd7_1_2 : ∀ q ∈ blkd7_1_2, subd7_1 q = true := by
  unfold blkd7_1_2
  exact List.forall_mem_cons.2 ⟨subd7_1_64, List.forall_mem_cons.2 ⟨subd7_1_65, List.forall_mem_cons.2 ⟨subd7_1_66, List.forall_mem_cons.2 ⟨subd7_1_67, List.forall_mem_cons.2 ⟨subd7_1_68, List.forall_mem_cons.2 ⟨subd7_1_69, List.forall_mem_cons.2 ⟨subd7_1_70, List.forall_mem_cons.2 ⟨subd7_1_71, List.forall_mem_cons.2 ⟨subd7_1_72, List.forall_mem_cons.2 ⟨subd7_1_73, List.forall_mem_cons.2 ⟨subd7_1_74, List.forall_mem_cons.2 ⟨subd7_1_75, List.forall_mem_cons.2 ⟨subd7_1_76, List.forall_mem_cons.2 ⟨subd7_1_77, List.forall_mem_cons.2 ⟨subd7_1_78, List.forall_mem_cons.2 ⟨subd7_1_79, List.forall_mem_cons.2 ⟨subd7_1_80, List.forall_mem_cons.2 ⟨subd7_1_81, List.forall_mem_cons.2 ⟨subd7_1_82, List.forall_mem_cons.2 ⟨subd7_1_83, List.forall_mem_cons.2 ⟨subd7_1_84, List.forall_mem_cons.2 ⟨subd7_1_85, List.forall_mem_cons.2 ⟨subd7_1_86, List.forall_mem_cons.2 ⟨subd7_1_87, List.forall_mem_cons.2 ⟨subd7_1_88, List.forall_mem_cons.2 ⟨subd7_1_89, List.forall_mem_cons.2 ⟨subd7_1_90, List.forall_mem_cons.2 ⟨subd7_1_91, List.forall_mem_cons.2 ⟨subd7_1_92, List.forall_mem_cons.2 ⟨subd7_1_93, List.forall_mem_cons.2 ⟨subd7_1_94, List.forall_mem_cons.2 ⟨subd7_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_96 : subd7_1 [-1, -1, -2] = true := by decide +kernel
theorem subd7_1_97 : subd7_1 [-1, -1, -1] = true := by decide +kernel
theorem subd7_1_98 : subd7_1 [-1, -1, 0] = true := by decide +kernel
theorem subd7_1_99 : subd7_1 [-1, -1, 1] = true := by decide +kernel
theorem subd7_1_100 : subd7_1 [-1, -1, 2] = true := by decide +kernel
theorem subd7_1_101 : subd7_1 [-1, -1, 3] = true := by decide +kernel
theorem subd7_1_102 : subd7_1 [-1, -1, 4] = true := by decide +kernel
theorem subd7_1_103 : subd7_1 [-1, -1, 5] = true := by decide +kernel
theorem subd7_1_104 : subd7_1 [-1, -1, 6] = true := by decide +kernel
theorem subd7_1_105 : subd7_1 [-1, 0, -7] = true := by decide +kernel
theorem subd7_1_106 : subd7_1 [-1, 0, -6] = true := by decide +kernel
theorem subd7_1_107 : subd7_1 [-1, 0, -5] = true := by decide +kernel
theorem subd7_1_108 : subd7_1 [-1, 0, -4] = true := by decide +kernel
theorem subd7_1_109 : subd7_1 [-1, 0, -3] = true := by decide +kernel
theorem subd7_1_110 : subd7_1 [-1, 0, -2] = true := by decide +kernel
theorem subd7_1_111 : subd7_1 [-1, 0, -1] = true := by decide +kernel
theorem subd7_1_112 : subd7_1 [-1, 0, 0] = true := by decide +kernel
theorem subd7_1_113 : subd7_1 [-1, 0, 1] = true := by decide +kernel
theorem subd7_1_114 : subd7_1 [-1, 0, 2] = true := by decide +kernel
theorem subd7_1_115 : subd7_1 [-1, 0, 3] = true := by decide +kernel
theorem subd7_1_116 : subd7_1 [-1, 0, 4] = true := by decide +kernel
theorem subd7_1_117 : subd7_1 [-1, 0, 5] = true := by decide +kernel
theorem subd7_1_118 : subd7_1 [-1, 0, 6] = true := by decide +kernel
theorem subd7_1_119 : subd7_1 [-1, 1, -7] = true := by decide +kernel
theorem subd7_1_120 : subd7_1 [-1, 1, -6] = true := by decide +kernel
theorem subd7_1_121 : subd7_1 [-1, 1, -5] = true := by decide +kernel
theorem subd7_1_122 : subd7_1 [-1, 1, -4] = true := by decide +kernel
theorem subd7_1_123 : subd7_1 [-1, 1, -3] = true := by decide +kernel
theorem subd7_1_124 : subd7_1 [-1, 1, -2] = true := by decide +kernel
theorem subd7_1_125 : subd7_1 [-1, 1, -1] = true := by decide +kernel
theorem subd7_1_126 : subd7_1 [-1, 1, 0] = true := by decide +kernel
theorem subd7_1_127 : subd7_1 [-1, 1, 1] = true := by decide +kernel
theorem sbd7_1_3 : ∀ q ∈ blkd7_1_3, subd7_1 q = true := by
  unfold blkd7_1_3
  exact List.forall_mem_cons.2 ⟨subd7_1_96, List.forall_mem_cons.2 ⟨subd7_1_97, List.forall_mem_cons.2 ⟨subd7_1_98, List.forall_mem_cons.2 ⟨subd7_1_99, List.forall_mem_cons.2 ⟨subd7_1_100, List.forall_mem_cons.2 ⟨subd7_1_101, List.forall_mem_cons.2 ⟨subd7_1_102, List.forall_mem_cons.2 ⟨subd7_1_103, List.forall_mem_cons.2 ⟨subd7_1_104, List.forall_mem_cons.2 ⟨subd7_1_105, List.forall_mem_cons.2 ⟨subd7_1_106, List.forall_mem_cons.2 ⟨subd7_1_107, List.forall_mem_cons.2 ⟨subd7_1_108, List.forall_mem_cons.2 ⟨subd7_1_109, List.forall_mem_cons.2 ⟨subd7_1_110, List.forall_mem_cons.2 ⟨subd7_1_111, List.forall_mem_cons.2 ⟨subd7_1_112, List.forall_mem_cons.2 ⟨subd7_1_113, List.forall_mem_cons.2 ⟨subd7_1_114, List.forall_mem_cons.2 ⟨subd7_1_115, List.forall_mem_cons.2 ⟨subd7_1_116, List.forall_mem_cons.2 ⟨subd7_1_117, List.forall_mem_cons.2 ⟨subd7_1_118, List.forall_mem_cons.2 ⟨subd7_1_119, List.forall_mem_cons.2 ⟨subd7_1_120, List.forall_mem_cons.2 ⟨subd7_1_121, List.forall_mem_cons.2 ⟨subd7_1_122, List.forall_mem_cons.2 ⟨subd7_1_123, List.forall_mem_cons.2 ⟨subd7_1_124, List.forall_mem_cons.2 ⟨subd7_1_125, List.forall_mem_cons.2 ⟨subd7_1_126, List.forall_mem_cons.2 ⟨subd7_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
