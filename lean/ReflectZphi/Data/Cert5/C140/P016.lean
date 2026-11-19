import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-5] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-4, -5] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [-4, -4] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [-4, -3] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [-4, -2] = true := by decide +kernel
theorem subd12_3_5 : subd12_3 [-4, -1] = true := by decide +kernel
theorem subd12_3_6 : subd12_3 [-4, 0] = true := by decide +kernel
theorem subd12_3_7 : subd12_3 [-4, 1] = true := by decide +kernel
theorem subd12_3_8 : subd12_3 [-4, 2] = true := by decide +kernel
theorem subd12_3_9 : subd12_3 [-4, 3] = true := by decide +kernel
theorem subd12_3_10 : subd12_3 [-3, -6] = true := by decide +kernel
theorem subd12_3_11 : subd12_3 [-3, -5] = true := by decide +kernel
theorem subd12_3_12 : subd12_3 [-3, -4] = true := by decide +kernel
theorem subd12_3_13 : subd12_3 [-3, -3] = true := by decide +kernel
theorem subd12_3_14 : subd12_3 [-3, -2] = true := by decide +kernel
theorem subd12_3_15 : subd12_3 [-3, -1] = true := by decide +kernel
theorem subd12_3_16 : subd12_3 [-3, 0] = true := by decide +kernel
theorem subd12_3_17 : subd12_3 [-3, 1] = true := by decide +kernel
theorem subd12_3_18 : subd12_3 [-3, 2] = true := by decide +kernel
theorem subd12_3_19 : subd12_3 [-3, 3] = true := by decide +kernel
theorem subd12_3_20 : subd12_3 [-3, 4] = true := by decide +kernel
theorem subd12_3_21 : subd12_3 [-2, -6] = true := by decide +kernel
theorem subd12_3_22 : subd12_3 [-2, -5] = true := by decide +kernel
theorem subd12_3_23 : subd12_3 [-2, -4] = true := by decide +kernel
theorem subd12_3_24 : subd12_3 [-2, -3] = true := by decide +kernel
theorem subd12_3_25 : subd12_3 [-2, -2] = true := by decide +kernel
theorem subd12_3_26 : subd12_3 [-2, -1] = true := by decide +kernel
theorem subd12_3_27 : subd12_3 [-2, 0] = true := by decide +kernel
theorem subd12_3_28 : subd12_3 [-2, 1] = true := by decide +kernel
theorem subd12_3_29 : subd12_3 [-2, 2] = true := by decide +kernel
theorem subd12_3_30 : subd12_3 [-2, 3] = true := by decide +kernel
theorem subd12_3_31 : subd12_3 [-2, 4] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_cons.2 ⟨subd12_3_5, List.forall_mem_cons.2 ⟨subd12_3_6, List.forall_mem_cons.2 ⟨subd12_3_7, List.forall_mem_cons.2 ⟨subd12_3_8, List.forall_mem_cons.2 ⟨subd12_3_9, List.forall_mem_cons.2 ⟨subd12_3_10, List.forall_mem_cons.2 ⟨subd12_3_11, List.forall_mem_cons.2 ⟨subd12_3_12, List.forall_mem_cons.2 ⟨subd12_3_13, List.forall_mem_cons.2 ⟨subd12_3_14, List.forall_mem_cons.2 ⟨subd12_3_15, List.forall_mem_cons.2 ⟨subd12_3_16, List.forall_mem_cons.2 ⟨subd12_3_17, List.forall_mem_cons.2 ⟨subd12_3_18, List.forall_mem_cons.2 ⟨subd12_3_19, List.forall_mem_cons.2 ⟨subd12_3_20, List.forall_mem_cons.2 ⟨subd12_3_21, List.forall_mem_cons.2 ⟨subd12_3_22, List.forall_mem_cons.2 ⟨subd12_3_23, List.forall_mem_cons.2 ⟨subd12_3_24, List.forall_mem_cons.2 ⟨subd12_3_25, List.forall_mem_cons.2 ⟨subd12_3_26, List.forall_mem_cons.2 ⟨subd12_3_27, List.forall_mem_cons.2 ⟨subd12_3_28, List.forall_mem_cons.2 ⟨subd12_3_29, List.forall_mem_cons.2 ⟨subd12_3_30, List.forall_mem_cons.2 ⟨subd12_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_32 : subd12_3 [-2, 5] = true := by decide +kernel
theorem subd12_3_33 : subd12_3 [-1, -7] = true := by decide +kernel
theorem subd12_3_34 : subd12_3 [-1, -6] = true := by decide +kernel
theorem subd12_3_35 : subd12_3 [-1, -5] = true := by decide +kernel
theorem subd12_3_36 : subd12_3 [-1, -4] = true := by decide +kernel
theorem subd12_3_37 : subd12_3 [-1, -3] = true := by decide +kernel
theorem subd12_3_38 : subd12_3 [-1, -2] = true := by decide +kernel
theorem subd12_3_39 : subd12_3 [-1, -1] = true := by decide +kernel
theorem subd12_3_40 : subd12_3 [-1, 0] = true := by decide +kernel
theorem subd12_3_41 : subd12_3 [-1, 1] = true := by decide +kernel
theorem subd12_3_42 : subd12_3 [-1, 2] = true := by decide +kernel
theorem subd12_3_43 : subd12_3 [-1, 3] = true := by decide +kernel
theorem subd12_3_44 : subd12_3 [-1, 4] = true := by decide +kernel
theorem subd12_3_45 : subd12_3 [-1, 5] = true := by decide +kernel
theorem subd12_3_46 : subd12_3 [0, -6] = true := by decide +kernel
theorem subd12_3_47 : subd12_3 [0, -5] = true := by decide +kernel
theorem subd12_3_48 : subd12_3 [0, -4] = true := by decide +kernel
theorem subd12_3_49 : subd12_3 [0, -3] = true := by decide +kernel
theorem subd12_3_50 : subd12_3 [0, -2] = true := by decide +kernel
theorem subd12_3_51 : subd12_3 [0, -1] = true := by decide +kernel
theorem subd12_3_52 : subd12_3 [0, 0] = true := by decide +kernel
theorem subd12_3_53 : subd12_3 [0, 1] = true := by decide +kernel
theorem subd12_3_54 : subd12_3 [0, 2] = true := by decide +kernel
theorem subd12_3_55 : subd12_3 [0, 3] = true := by decide +kernel
theorem subd12_3_56 : subd12_3 [0, 4] = true := by decide +kernel
theorem subd12_3_57 : subd12_3 [0, 5] = true := by decide +kernel
theorem subd12_3_58 : subd12_3 [1, -6] = true := by decide +kernel
theorem subd12_3_59 : subd12_3 [1, -5] = true := by decide +kernel
theorem subd12_3_60 : subd12_3 [1, -4] = true := by decide +kernel
theorem subd12_3_61 : subd12_3 [1, -3] = true := by decide +kernel
theorem subd12_3_62 : subd12_3 [1, -2] = true := by decide +kernel
theorem subd12_3_63 : subd12_3 [1, -1] = true := by decide +kernel
theorem sbd12_3_1 : ∀ q ∈ blkd12_3_1, subd12_3 q = true := by
  unfold blkd12_3_1
  exact List.forall_mem_cons.2 ⟨subd12_3_32, List.forall_mem_cons.2 ⟨subd12_3_33, List.forall_mem_cons.2 ⟨subd12_3_34, List.forall_mem_cons.2 ⟨subd12_3_35, List.forall_mem_cons.2 ⟨subd12_3_36, List.forall_mem_cons.2 ⟨subd12_3_37, List.forall_mem_cons.2 ⟨subd12_3_38, List.forall_mem_cons.2 ⟨subd12_3_39, List.forall_mem_cons.2 ⟨subd12_3_40, List.forall_mem_cons.2 ⟨subd12_3_41, List.forall_mem_cons.2 ⟨subd12_3_42, List.forall_mem_cons.2 ⟨subd12_3_43, List.forall_mem_cons.2 ⟨subd12_3_44, List.forall_mem_cons.2 ⟨subd12_3_45, List.forall_mem_cons.2 ⟨subd12_3_46, List.forall_mem_cons.2 ⟨subd12_3_47, List.forall_mem_cons.2 ⟨subd12_3_48, List.forall_mem_cons.2 ⟨subd12_3_49, List.forall_mem_cons.2 ⟨subd12_3_50, List.forall_mem_cons.2 ⟨subd12_3_51, List.forall_mem_cons.2 ⟨subd12_3_52, List.forall_mem_cons.2 ⟨subd12_3_53, List.forall_mem_cons.2 ⟨subd12_3_54, List.forall_mem_cons.2 ⟨subd12_3_55, List.forall_mem_cons.2 ⟨subd12_3_56, List.forall_mem_cons.2 ⟨subd12_3_57, List.forall_mem_cons.2 ⟨subd12_3_58, List.forall_mem_cons.2 ⟨subd12_3_59, List.forall_mem_cons.2 ⟨subd12_3_60, List.forall_mem_cons.2 ⟨subd12_3_61, List.forall_mem_cons.2 ⟨subd12_3_62, List.forall_mem_cons.2 ⟨subd12_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_64 : subd12_3 [1, 0] = true := by decide +kernel
theorem subd12_3_65 : subd12_3 [1, 1] = true := by decide +kernel
theorem subd12_3_66 : subd12_3 [1, 2] = true := by decide +kernel
theorem subd12_3_67 : subd12_3 [1, 3] = true := by decide +kernel
theorem subd12_3_68 : subd12_3 [1, 4] = true := by decide +kernel
theorem subd12_3_69 : subd12_3 [1, 5] = true := by decide +kernel
theorem subd12_3_70 : subd12_3 [1, 6] = true := by decide +kernel
theorem subd12_3_71 : subd12_3 [2, -6] = true := by decide +kernel
theorem subd12_3_72 : subd12_3 [2, -5] = true := by decide +kernel
theorem subd12_3_73 : subd12_3 [2, -4] = true := by decide +kernel
theorem subd12_3_74 : subd12_3 [2, -3] = true := by decide +kernel
theorem subd12_3_75 : subd12_3 [2, -2] = true := by decide +kernel
theorem subd12_3_76 : subd12_3 [2, -1] = true := by decide +kernel
theorem subd12_3_77 : subd12_3 [2, 0] = true := by decide +kernel
theorem subd12_3_78 : subd12_3 [2, 1] = true := by decide +kernel
theorem subd12_3_79 : subd12_3 [2, 2] = true := by decide +kernel
theorem subd12_3_80 : subd12_3 [2, 3] = true := by decide +kernel
theorem subd12_3_81 : subd12_3 [2, 4] = true := by decide +kernel
theorem subd12_3_82 : subd12_3 [2, 5] = true := by decide +kernel
theorem subd12_3_83 : subd12_3 [3, -5] = true := by decide +kernel
theorem subd12_3_84 : subd12_3 [3, -4] = true := by decide +kernel
theorem subd12_3_85 : subd12_3 [3, -3] = true := by decide +kernel
theorem subd12_3_86 : subd12_3 [3, -2] = true := by decide +kernel
theorem subd12_3_87 : subd12_3 [3, -1] = true := by decide +kernel
theorem subd12_3_88 : subd12_3 [3, 0] = true := by decide +kernel
theorem subd12_3_89 : subd12_3 [3, 1] = true := by decide +kernel
theorem subd12_3_90 : subd12_3 [3, 2] = true := by decide +kernel
theorem subd12_3_91 : subd12_3 [3, 3] = true := by decide +kernel
theorem subd12_3_92 : subd12_3 [3, 4] = true := by decide +kernel
theorem subd12_3_93 : subd12_3 [3, 5] = true := by decide +kernel
theorem subd12_3_94 : subd12_3 [4, -4] = true := by decide +kernel
theorem subd12_3_95 : subd12_3 [4, -3] = true := by decide +kernel
theorem sbd12_3_2 : ∀ q ∈ blkd12_3_2, subd12_3 q = true := by
  unfold blkd12_3_2
  exact List.forall_mem_cons.2 ⟨subd12_3_64, List.forall_mem_cons.2 ⟨subd12_3_65, List.forall_mem_cons.2 ⟨subd12_3_66, List.forall_mem_cons.2 ⟨subd12_3_67, List.forall_mem_cons.2 ⟨subd12_3_68, List.forall_mem_cons.2 ⟨subd12_3_69, List.forall_mem_cons.2 ⟨subd12_3_70, List.forall_mem_cons.2 ⟨subd12_3_71, List.forall_mem_cons.2 ⟨subd12_3_72, List.forall_mem_cons.2 ⟨subd12_3_73, List.forall_mem_cons.2 ⟨subd12_3_74, List.forall_mem_cons.2 ⟨subd12_3_75, List.forall_mem_cons.2 ⟨subd12_3_76, List.forall_mem_cons.2 ⟨subd12_3_77, List.forall_mem_cons.2 ⟨subd12_3_78, List.forall_mem_cons.2 ⟨subd12_3_79, List.forall_mem_cons.2 ⟨subd12_3_80, List.forall_mem_cons.2 ⟨subd12_3_81, List.forall_mem_cons.2 ⟨subd12_3_82, List.forall_mem_cons.2 ⟨subd12_3_83, List.forall_mem_cons.2 ⟨subd12_3_84, List.forall_mem_cons.2 ⟨subd12_3_85, List.forall_mem_cons.2 ⟨subd12_3_86, List.forall_mem_cons.2 ⟨subd12_3_87, List.forall_mem_cons.2 ⟨subd12_3_88, List.forall_mem_cons.2 ⟨subd12_3_89, List.forall_mem_cons.2 ⟨subd12_3_90, List.forall_mem_cons.2 ⟨subd12_3_91, List.forall_mem_cons.2 ⟨subd12_3_92, List.forall_mem_cons.2 ⟨subd12_3_93, List.forall_mem_cons.2 ⟨subd12_3_94, List.forall_mem_cons.2 ⟨subd12_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_96 : subd12_3 [4, -2] = true := by decide +kernel
theorem subd12_3_97 : subd12_3 [4, -1] = true := by decide +kernel
theorem subd12_3_98 : subd12_3 [4, 0] = true := by decide +kernel
theorem subd12_3_99 : subd12_3 [4, 1] = true := by decide +kernel
theorem subd12_3_100 : subd12_3 [4, 2] = true := by decide +kernel
theorem subd12_3_101 : subd12_3 [4, 3] = true := by decide +kernel
theorem subd12_3_102 : subd12_3 [4, 4] = true := by decide +kernel
theorem subd12_3_103 : subd12_3 [5] = true := by decide +kernel
theorem sbd12_3_3 : ∀ q ∈ blkd12_3_3, subd12_3 q = true := by
  unfold blkd12_3_3
  exact List.forall_mem_cons.2 ⟨subd12_3_96, List.forall_mem_cons.2 ⟨subd12_3_97, List.forall_mem_cons.2 ⟨subd12_3_98, List.forall_mem_cons.2 ⟨subd12_3_99, List.forall_mem_cons.2 ⟨subd12_3_100, List.forall_mem_cons.2 ⟨subd12_3_101, List.forall_mem_cons.2 ⟨subd12_3_102, List.forall_mem_cons.2 ⟨subd12_3_103, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_4 : ldCheck G d12_4.U d12_4.ms ldd12_4 = true := by decide +kernel
theorem pre_okd12_4 : subPre G cell12 d12_4 = true := by decide +kernel
theorem subd12_4_0 : subd12_4 [-4] = true := by decide +kernel
theorem subd12_4_1 : subd12_4 [-3, -5] = true := by decide +kernel
theorem subd12_4_2 : subd12_4 [-3, -4] = true := by decide +kernel
theorem subd12_4_3 : subd12_4 [-3, -3] = true := by decide +kernel
theorem subd12_4_4 : subd12_4 [-3, -2] = true := by decide +kernel
theorem subd12_4_5 : subd12_4 [-3, -1] = true := by decide +kernel
theorem subd12_4_6 : subd12_4 [-3, 0] = true := by decide +kernel
theorem subd12_4_7 : subd12_4 [-3, 1] = true := by decide +kernel
theorem subd12_4_8 : subd12_4 [-3, 2] = true := by decide +kernel
theorem subd12_4_9 : subd12_4 [-3, 3] = true := by decide +kernel
theorem subd12_4_10 : subd12_4 [-2, -5] = true := by decide +kernel
theorem subd12_4_11 : subd12_4 [-2, -4] = true := by decide +kernel
theorem subd12_4_12 : subd12_4 [-2, -3] = true := by decide +kernel
theorem subd12_4_13 : subd12_4 [-2, -2] = true := by decide +kernel
theorem subd12_4_14 : subd12_4 [-2, -1] = true := by decide +kernel
theorem subd12_4_15 : subd12_4 [-2, 0] = true := by decide +kernel
theorem subd12_4_16 : subd12_4 [-2, 1] = true := by decide +kernel
theorem subd12_4_17 : subd12_4 [-2, 2] = true := by decide +kernel
theorem subd12_4_18 : subd12_4 [-2, 3] = true := by decide +kernel
theorem subd12_4_19 : subd12_4 [-2, 4] = true := by decide +kernel
theorem subd12_4_20 : subd12_4 [-1, -5] = true := by decide +kernel
theorem subd12_4_21 : subd12_4 [-1, -4] = true := by decide +kernel
theorem subd12_4_22 : subd12_4 [-1, -3] = true := by decide +kernel
theorem subd12_4_23 : subd12_4 [-1, -2] = true := by decide +kernel
theorem subd12_4_24 : subd12_4 [-1, -1] = true := by decide +kernel
theorem subd12_4_25 : subd12_4 [-1, 0] = true := by decide +kernel
theorem subd12_4_26 : subd12_4 [-1, 1] = true := by decide +kernel
theorem subd12_4_27 : subd12_4 [-1, 2] = true := by decide +kernel
theorem subd12_4_28 : subd12_4 [-1, 3] = true := by decide +kernel
theorem subd12_4_29 : subd12_4 [-1, 4] = true := by decide +kernel
theorem subd12_4_30 : subd12_4 [0, -5] = true := by decide +kernel
theorem subd12_4_31 : subd12_4 [0, -4] = true := by decide +kernel
theorem sbd12_4_0 : ∀ q ∈ blkd12_4_0, subd12_4 q = true := by
  unfold blkd12_4_0
  exact List.forall_mem_cons.2 ⟨subd12_4_0, List.forall_mem_cons.2 ⟨subd12_4_1, List.forall_mem_cons.2 ⟨subd12_4_2, List.forall_mem_cons.2 ⟨subd12_4_3, List.forall_mem_cons.2 ⟨subd12_4_4, List.forall_mem_cons.2 ⟨subd12_4_5, List.forall_mem_cons.2 ⟨subd12_4_6, List.forall_mem_cons.2 ⟨subd12_4_7, List.forall_mem_cons.2 ⟨subd12_4_8, List.forall_mem_cons.2 ⟨subd12_4_9, List.forall_mem_cons.2 ⟨subd12_4_10, List.forall_mem_cons.2 ⟨subd12_4_11, List.forall_mem_cons.2 ⟨subd12_4_12, List.forall_mem_cons.2 ⟨subd12_4_13, List.forall_mem_cons.2 ⟨subd12_4_14, List.forall_mem_cons.2 ⟨subd12_4_15, List.forall_mem_cons.2 ⟨subd12_4_16, List.forall_mem_cons.2 ⟨subd12_4_17, List.forall_mem_cons.2 ⟨subd12_4_18, List.forall_mem_cons.2 ⟨subd12_4_19, List.forall_mem_cons.2 ⟨subd12_4_20, List.forall_mem_cons.2 ⟨subd12_4_21, List.forall_mem_cons.2 ⟨subd12_4_22, List.forall_mem_cons.2 ⟨subd12_4_23, List.forall_mem_cons.2 ⟨subd12_4_24, List.forall_mem_cons.2 ⟨subd12_4_25, List.forall_mem_cons.2 ⟨subd12_4_26, List.forall_mem_cons.2 ⟨subd12_4_27, List.forall_mem_cons.2 ⟨subd12_4_28, List.forall_mem_cons.2 ⟨subd12_4_29, List.forall_mem_cons.2 ⟨subd12_4_30, List.forall_mem_cons.2 ⟨subd12_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
