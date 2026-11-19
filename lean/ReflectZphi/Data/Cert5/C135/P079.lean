import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_3_64 : subd12_3 [1, -2] = true := by decide +kernel
theorem subd12_3_65 : subd12_3 [1, -1] = true := by decide +kernel
theorem subd12_3_66 : subd12_3 [1, 0] = true := by decide +kernel
theorem subd12_3_67 : subd12_3 [1, 1] = true := by decide +kernel
theorem subd12_3_68 : subd12_3 [1, 2] = true := by decide +kernel
theorem subd12_3_69 : subd12_3 [1, 3] = true := by decide +kernel
theorem subd12_3_70 : subd12_3 [1, 4] = true := by decide +kernel
theorem subd12_3_71 : subd12_3 [1, 5] = true := by decide +kernel
theorem subd12_3_72 : subd12_3 [1, 6] = true := by decide +kernel
theorem subd12_3_73 : subd12_3 [2, -6] = true := by decide +kernel
theorem subd12_3_74 : subd12_3 [2, -5] = true := by decide +kernel
theorem subd12_3_75 : subd12_3 [2, -4] = true := by decide +kernel
theorem subd12_3_76 : subd12_3 [2, -3] = true := by decide +kernel
theorem subd12_3_77 : subd12_3 [2, -2] = true := by decide +kernel
theorem subd12_3_78 : subd12_3 [2, -1] = true := by decide +kernel
theorem subd12_3_79 : subd12_3 [2, 0] = true := by decide +kernel
theorem subd12_3_80 : subd12_3 [2, 1] = true := by decide +kernel
theorem subd12_3_81 : subd12_3 [2, 2] = true := by decide +kernel
theorem subd12_3_82 : subd12_3 [2, 3] = true := by decide +kernel
theorem subd12_3_83 : subd12_3 [2, 4] = true := by decide +kernel
theorem subd12_3_84 : subd12_3 [2, 5] = true := by decide +kernel
theorem subd12_3_85 : subd12_3 [3, -5] = true := by decide +kernel
theorem subd12_3_86 : subd12_3 [3, -4] = true := by decide +kernel
theorem subd12_3_87 : subd12_3 [3, -3] = true := by decide +kernel
theorem subd12_3_88 : subd12_3 [3, -2] = true := by decide +kernel
theorem subd12_3_89 : subd12_3 [3, -1] = true := by decide +kernel
theorem subd12_3_90 : subd12_3 [3, 0] = true := by decide +kernel
theorem subd12_3_91 : subd12_3 [3, 1] = true := by decide +kernel
theorem subd12_3_92 : subd12_3 [3, 2] = true := by decide +kernel
theorem subd12_3_93 : subd12_3 [3, 3] = true := by decide +kernel
theorem subd12_3_94 : subd12_3 [3, 4] = true := by decide +kernel
theorem subd12_3_95 : subd12_3 [3, 5] = true := by decide +kernel
theorem sbd12_3_2 : ∀ q ∈ blkd12_3_2, subd12_3 q = true := by
  unfold blkd12_3_2
  exact List.forall_mem_cons.2 ⟨subd12_3_64, List.forall_mem_cons.2 ⟨subd12_3_65, List.forall_mem_cons.2 ⟨subd12_3_66, List.forall_mem_cons.2 ⟨subd12_3_67, List.forall_mem_cons.2 ⟨subd12_3_68, List.forall_mem_cons.2 ⟨subd12_3_69, List.forall_mem_cons.2 ⟨subd12_3_70, List.forall_mem_cons.2 ⟨subd12_3_71, List.forall_mem_cons.2 ⟨subd12_3_72, List.forall_mem_cons.2 ⟨subd12_3_73, List.forall_mem_cons.2 ⟨subd12_3_74, List.forall_mem_cons.2 ⟨subd12_3_75, List.forall_mem_cons.2 ⟨subd12_3_76, List.forall_mem_cons.2 ⟨subd12_3_77, List.forall_mem_cons.2 ⟨subd12_3_78, List.forall_mem_cons.2 ⟨subd12_3_79, List.forall_mem_cons.2 ⟨subd12_3_80, List.forall_mem_cons.2 ⟨subd12_3_81, List.forall_mem_cons.2 ⟨subd12_3_82, List.forall_mem_cons.2 ⟨subd12_3_83, List.forall_mem_cons.2 ⟨subd12_3_84, List.forall_mem_cons.2 ⟨subd12_3_85, List.forall_mem_cons.2 ⟨subd12_3_86, List.forall_mem_cons.2 ⟨subd12_3_87, List.forall_mem_cons.2 ⟨subd12_3_88, List.forall_mem_cons.2 ⟨subd12_3_89, List.forall_mem_cons.2 ⟨subd12_3_90, List.forall_mem_cons.2 ⟨subd12_3_91, List.forall_mem_cons.2 ⟨subd12_3_92, List.forall_mem_cons.2 ⟨subd12_3_93, List.forall_mem_cons.2 ⟨subd12_3_94, List.forall_mem_cons.2 ⟨subd12_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_96 : subd12_3 [4, -4] = true := by decide +kernel
theorem subd12_3_97 : subd12_3 [4, -3] = true := by decide +kernel
theorem subd12_3_98 : subd12_3 [4, -2] = true := by decide +kernel
theorem subd12_3_99 : subd12_3 [4, -1] = true := by decide +kernel
theorem subd12_3_100 : subd12_3 [4, 0] = true := by decide +kernel
theorem subd12_3_101 : subd12_3 [4, 1] = true := by decide +kernel
theorem subd12_3_102 : subd12_3 [4, 2] = true := by decide +kernel
theorem subd12_3_103 : subd12_3 [4, 3] = true := by decide +kernel
theorem subd12_3_104 : subd12_3 [4, 4] = true := by decide +kernel
theorem subd12_3_105 : subd12_3 [5] = true := by decide +kernel
theorem sbd12_3_3 : ∀ q ∈ blkd12_3_3, subd12_3 q = true := by
  unfold blkd12_3_3
  exact List.forall_mem_cons.2 ⟨subd12_3_96, List.forall_mem_cons.2 ⟨subd12_3_97, List.forall_mem_cons.2 ⟨subd12_3_98, List.forall_mem_cons.2 ⟨subd12_3_99, List.forall_mem_cons.2 ⟨subd12_3_100, List.forall_mem_cons.2 ⟨subd12_3_101, List.forall_mem_cons.2 ⟨subd12_3_102, List.forall_mem_cons.2 ⟨subd12_3_103, List.forall_mem_cons.2 ⟨subd12_3_104, List.forall_mem_cons.2 ⟨subd12_3_105, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_4 : ldCheck G d12_4.U d12_4.ms ldd12_4 = true := by decide +kernel
theorem pre_okd12_4 : subPre G cell12 d12_4 = true := by decide +kernel
theorem subd12_4_0 : subd12_4 [-2, -2] = true := by decide +kernel
theorem subd12_4_1 : subd12_4 [-2, -1] = true := by decide +kernel
theorem subd12_4_2 : subd12_4 [-2, 0] = true := by decide +kernel
theorem subd12_4_3 : subd12_4 [-2, 1] = true := by decide +kernel
theorem subd12_4_4 : subd12_4 [-2, 2] = true := by decide +kernel
theorem subd12_4_5 : subd12_4 [-1, -3] = true := by decide +kernel
theorem subd12_4_6 : subd12_4 [-1, -2] = true := by decide +kernel
theorem subd12_4_7 : subd12_4 [-1, -1, -7] = true := by decide +kernel
theorem subd12_4_8 : subd12_4 [-1, -1, -6] = true := by decide +kernel
theorem subd12_4_9 : subd12_4 [-1, -1, -5] = true := by decide +kernel
theorem subd12_4_10 : subd12_4 [-1, -1, -4] = true := by decide +kernel
theorem subd12_4_11 : subd12_4 [-1, -1, -3] = true := by decide +kernel
theorem subd12_4_12 : subd12_4 [-1, -1, -2] = true := by decide +kernel
theorem subd12_4_13 : subd12_4 [-1, -1, -1] = true := by decide +kernel
theorem subd12_4_14 : subd12_4 [-1, -1, 0] = true := by decide +kernel
theorem subd12_4_15 : subd12_4 [-1, -1, 1] = true := by decide +kernel
theorem subd12_4_16 : subd12_4 [-1, -1, 2] = true := by decide +kernel
theorem subd12_4_17 : subd12_4 [-1, -1, 3] = true := by decide +kernel
theorem subd12_4_18 : subd12_4 [-1, -1, 4] = true := by decide +kernel
theorem subd12_4_19 : subd12_4 [-1, -1, 5] = true := by decide +kernel
theorem subd12_4_20 : subd12_4 [-1, -1, 6] = true := by decide +kernel
theorem subd12_4_21 : subd12_4 [-1, 0, -8] = true := by decide +kernel
theorem subd12_4_22 : subd12_4 [-1, 0, -7] = true := by decide +kernel
theorem subd12_4_23 : subd12_4 [-1, 0, -6] = true := by decide +kernel
theorem subd12_4_24 : subd12_4 [-1, 0, -5] = true := by decide +kernel
theorem subd12_4_25 : subd12_4 [-1, 0, -4] = true := by decide +kernel
theorem subd12_4_26 : subd12_4 [-1, 0, -3] = true := by decide +kernel
theorem subd12_4_27 : subd12_4 [-1, 0, -2] = true := by decide +kernel
theorem subd12_4_28 : subd12_4 [-1, 0, -1] = true := by decide +kernel
theorem subd12_4_29 : subd12_4 [-1, 0, 0] = true := by decide +kernel
theorem subd12_4_30 : subd12_4 [-1, 0, 1] = true := by decide +kernel
theorem subd12_4_31 : subd12_4 [-1, 0, 2] = true := by decide +kernel
theorem sbd12_4_0 : ∀ q ∈ blkd12_4_0, subd12_4 q = true := by
  unfold blkd12_4_0
  exact List.forall_mem_cons.2 ⟨subd12_4_0, List.forall_mem_cons.2 ⟨subd12_4_1, List.forall_mem_cons.2 ⟨subd12_4_2, List.forall_mem_cons.2 ⟨subd12_4_3, List.forall_mem_cons.2 ⟨subd12_4_4, List.forall_mem_cons.2 ⟨subd12_4_5, List.forall_mem_cons.2 ⟨subd12_4_6, List.forall_mem_cons.2 ⟨subd12_4_7, List.forall_mem_cons.2 ⟨subd12_4_8, List.forall_mem_cons.2 ⟨subd12_4_9, List.forall_mem_cons.2 ⟨subd12_4_10, List.forall_mem_cons.2 ⟨subd12_4_11, List.forall_mem_cons.2 ⟨subd12_4_12, List.forall_mem_cons.2 ⟨subd12_4_13, List.forall_mem_cons.2 ⟨subd12_4_14, List.forall_mem_cons.2 ⟨subd12_4_15, List.forall_mem_cons.2 ⟨subd12_4_16, List.forall_mem_cons.2 ⟨subd12_4_17, List.forall_mem_cons.2 ⟨subd12_4_18, List.forall_mem_cons.2 ⟨subd12_4_19, List.forall_mem_cons.2 ⟨subd12_4_20, List.forall_mem_cons.2 ⟨subd12_4_21, List.forall_mem_cons.2 ⟨subd12_4_22, List.forall_mem_cons.2 ⟨subd12_4_23, List.forall_mem_cons.2 ⟨subd12_4_24, List.forall_mem_cons.2 ⟨subd12_4_25, List.forall_mem_cons.2 ⟨subd12_4_26, List.forall_mem_cons.2 ⟨subd12_4_27, List.forall_mem_cons.2 ⟨subd12_4_28, List.forall_mem_cons.2 ⟨subd12_4_29, List.forall_mem_cons.2 ⟨subd12_4_30, List.forall_mem_cons.2 ⟨subd12_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_4_32 : subd12_4 [-1, 0, 3] = true := by decide +kernel
theorem subd12_4_33 : subd12_4 [-1, 0, 4] = true := by decide +kernel
theorem subd12_4_34 : subd12_4 [-1, 0, 5] = true := by decide +kernel
theorem subd12_4_35 : subd12_4 [-1, 0, 6] = true := by decide +kernel
theorem subd12_4_36 : subd12_4 [-1, 0, 7] = true := by decide +kernel
theorem subd12_4_37 : subd12_4 [-1, 1, -8] = true := by decide +kernel
theorem subd12_4_38 : subd12_4 [-1, 1, -7] = true := by decide +kernel
theorem subd12_4_39 : subd12_4 [-1, 1, -6] = true := by decide +kernel
theorem subd12_4_40 : subd12_4 [-1, 1, -5] = true := by decide +kernel
theorem subd12_4_41 : subd12_4 [-1, 1, -4] = true := by decide +kernel
theorem subd12_4_42 : subd12_4 [-1, 1, -3] = true := by decide +kernel
theorem subd12_4_43 : subd12_4 [-1, 1, -2] = true := by decide +kernel
theorem subd12_4_44 : subd12_4 [-1, 1, -1] = true := by decide +kernel
theorem subd12_4_45 : subd12_4 [-1, 1, 0] = true := by decide +kernel
theorem subd12_4_46 : subd12_4 [-1, 1, 1] = true := by decide +kernel
theorem subd12_4_47 : subd12_4 [-1, 1, 2] = true := by decide +kernel
theorem subd12_4_48 : subd12_4 [-1, 1, 3] = true := by decide +kernel
theorem subd12_4_49 : subd12_4 [-1, 1, 4] = true := by decide +kernel
theorem subd12_4_50 : subd12_4 [-1, 1, 5] = true := by decide +kernel
theorem subd12_4_51 : subd12_4 [-1, 1, 6] = true := by decide +kernel
theorem subd12_4_52 : subd12_4 [-1, 1, 7] = true := by decide +kernel
theorem subd12_4_53 : subd12_4 [-1, 2] = true := by decide +kernel
theorem subd12_4_54 : subd12_4 [0, -3] = true := by decide +kernel
theorem subd12_4_55 : subd12_4 [0, -2] = true := by decide +kernel
theorem subd12_4_56 : subd12_4 [0, -1, -8] = true := by decide +kernel
theorem subd12_4_57 : subd12_4 [0, -1, -7] = true := by decide +kernel
theorem subd12_4_58 : subd12_4 [0, -1, -6] = true := by decide +kernel
theorem subd12_4_59 : subd12_4 [0, -1, -5] = true := by decide +kernel
theorem subd12_4_60 : subd12_4 [0, -1, -4] = true := by decide +kernel
theorem subd12_4_61 : subd12_4 [0, -1, -3] = true := by decide +kernel
theorem subd12_4_62 : subd12_4 [0, -1, -2] = true := by decide +kernel
theorem subd12_4_63 : subd12_4 [0, -1, -1] = true := by decide +kernel
theorem sbd12_4_1 : ∀ q ∈ blkd12_4_1, subd12_4 q = true := by
  unfold blkd12_4_1
  exact List.forall_mem_cons.2 ⟨subd12_4_32, List.forall_mem_cons.2 ⟨subd12_4_33, List.forall_mem_cons.2 ⟨subd12_4_34, List.forall_mem_cons.2 ⟨subd12_4_35, List.forall_mem_cons.2 ⟨subd12_4_36, List.forall_mem_cons.2 ⟨subd12_4_37, List.forall_mem_cons.2 ⟨subd12_4_38, List.forall_mem_cons.2 ⟨subd12_4_39, List.forall_mem_cons.2 ⟨subd12_4_40, List.forall_mem_cons.2 ⟨subd12_4_41, List.forall_mem_cons.2 ⟨subd12_4_42, List.forall_mem_cons.2 ⟨subd12_4_43, List.forall_mem_cons.2 ⟨subd12_4_44, List.forall_mem_cons.2 ⟨subd12_4_45, List.forall_mem_cons.2 ⟨subd12_4_46, List.forall_mem_cons.2 ⟨subd12_4_47, List.forall_mem_cons.2 ⟨subd12_4_48, List.forall_mem_cons.2 ⟨subd12_4_49, List.forall_mem_cons.2 ⟨subd12_4_50, List.forall_mem_cons.2 ⟨subd12_4_51, List.forall_mem_cons.2 ⟨subd12_4_52, List.forall_mem_cons.2 ⟨subd12_4_53, List.forall_mem_cons.2 ⟨subd12_4_54, List.forall_mem_cons.2 ⟨subd12_4_55, List.forall_mem_cons.2 ⟨subd12_4_56, List.forall_mem_cons.2 ⟨subd12_4_57, List.forall_mem_cons.2 ⟨subd12_4_58, List.forall_mem_cons.2 ⟨subd12_4_59, List.forall_mem_cons.2 ⟨subd12_4_60, List.forall_mem_cons.2 ⟨subd12_4_61, List.forall_mem_cons.2 ⟨subd12_4_62, List.forall_mem_cons.2 ⟨subd12_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_4_64 : subd12_4 [0, -1, 0] = true := by decide +kernel
theorem subd12_4_65 : subd12_4 [0, -1, 1] = true := by decide +kernel
theorem subd12_4_66 : subd12_4 [0, -1, 2] = true := by decide +kernel
theorem subd12_4_67 : subd12_4 [0, -1, 3] = true := by decide +kernel
theorem subd12_4_68 : subd12_4 [0, -1, 4] = true := by decide +kernel
theorem subd12_4_69 : subd12_4 [0, -1, 5] = true := by decide +kernel
theorem subd12_4_70 : subd12_4 [0, -1, 6] = true := by decide +kernel
theorem subd12_4_71 : subd12_4 [0, -1, 7] = true := by decide +kernel
theorem subd12_4_72 : subd12_4 [0, 0, -9] = true := by decide +kernel
theorem subd12_4_73 : subd12_4 [0, 0, -8] = true := by decide +kernel
theorem subd12_4_74 : subd12_4 [0, 0, -7] = true := by decide +kernel
theorem subd12_4_75 : subd12_4 [0, 0, -6] = true := by decide +kernel
theorem subd12_4_76 : subd12_4 [0, 0, -5] = true := by decide +kernel
theorem subd12_4_77 : subd12_4 [0, 0, -4] = true := by decide +kernel
theorem subd12_4_78 : subd12_4 [0, 0, -3] = true := by decide +kernel
theorem subd12_4_79 : subd12_4 [0, 0, -2] = true := by decide +kernel
theorem subd12_4_80 : subd12_4 [0, 0, -1] = true := by decide +kernel
theorem subd12_4_81 : subd12_4 [0, 0, 0] = true := by decide +kernel
theorem subd12_4_82 : subd12_4 [0, 0, 1] = true := by decide +kernel
theorem subd12_4_83 : subd12_4 [0, 0, 2] = true := by decide +kernel
theorem subd12_4_84 : subd12_4 [0, 0, 3] = true := by decide +kernel
theorem subd12_4_85 : subd12_4 [0, 0, 4] = true := by decide +kernel
theorem subd12_4_86 : subd12_4 [0, 0, 5] = true := by decide +kernel
theorem subd12_4_87 : subd12_4 [0, 0, 6] = true := by decide +kernel
theorem subd12_4_88 : subd12_4 [0, 0, 7] = true := by decide +kernel
theorem subd12_4_89 : subd12_4 [0, 0, 8] = true := by decide +kernel
theorem subd12_4_90 : subd12_4 [0, 1, -8] = true := by decide +kernel
theorem subd12_4_91 : subd12_4 [0, 1, -7] = true := by decide +kernel
theorem subd12_4_92 : subd12_4 [0, 1, -6] = true := by decide +kernel
theorem subd12_4_93 : subd12_4 [0, 1, -5] = true := by decide +kernel
theorem subd12_4_94 : subd12_4 [0, 1, -4] = true := by decide +kernel
theorem subd12_4_95 : subd12_4 [0, 1, -3] = true := by decide +kernel
theorem sbd12_4_2 : ∀ q ∈ blkd12_4_2, subd12_4 q = true := by
  unfold blkd12_4_2
  exact List.forall_mem_cons.2 ⟨subd12_4_64, List.forall_mem_cons.2 ⟨subd12_4_65, List.forall_mem_cons.2 ⟨subd12_4_66, List.forall_mem_cons.2 ⟨subd12_4_67, List.forall_mem_cons.2 ⟨subd12_4_68, List.forall_mem_cons.2 ⟨subd12_4_69, List.forall_mem_cons.2 ⟨subd12_4_70, List.forall_mem_cons.2 ⟨subd12_4_71, List.forall_mem_cons.2 ⟨subd12_4_72, List.forall_mem_cons.2 ⟨subd12_4_73, List.forall_mem_cons.2 ⟨subd12_4_74, List.forall_mem_cons.2 ⟨subd12_4_75, List.forall_mem_cons.2 ⟨subd12_4_76, List.forall_mem_cons.2 ⟨subd12_4_77, List.forall_mem_cons.2 ⟨subd12_4_78, List.forall_mem_cons.2 ⟨subd12_4_79, List.forall_mem_cons.2 ⟨subd12_4_80, List.forall_mem_cons.2 ⟨subd12_4_81, List.forall_mem_cons.2 ⟨subd12_4_82, List.forall_mem_cons.2 ⟨subd12_4_83, List.forall_mem_cons.2 ⟨subd12_4_84, List.forall_mem_cons.2 ⟨subd12_4_85, List.forall_mem_cons.2 ⟨subd12_4_86, List.forall_mem_cons.2 ⟨subd12_4_87, List.forall_mem_cons.2 ⟨subd12_4_88, List.forall_mem_cons.2 ⟨subd12_4_89, List.forall_mem_cons.2 ⟨subd12_4_90, List.forall_mem_cons.2 ⟨subd12_4_91, List.forall_mem_cons.2 ⟨subd12_4_92, List.forall_mem_cons.2 ⟨subd12_4_93, List.forall_mem_cons.2 ⟨subd12_4_94, List.forall_mem_cons.2 ⟨subd12_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_4_96 : subd12_4 [0, 1, -2] = true := by decide +kernel
theorem subd12_4_97 : subd12_4 [0, 1, -1] = true := by decide +kernel
theorem subd12_4_98 : subd12_4 [0, 1, 0] = true := by decide +kernel
theorem subd12_4_99 : subd12_4 [0, 1, 1] = true := by decide +kernel
theorem subd12_4_100 : subd12_4 [0, 1, 2] = true := by decide +kernel
theorem subd12_4_101 : subd12_4 [0, 1, 3] = true := by decide +kernel
theorem subd12_4_102 : subd12_4 [0, 1, 4] = true := by decide +kernel
theorem subd12_4_103 : subd12_4 [0, 1, 5] = true := by decide +kernel
theorem subd12_4_104 : subd12_4 [0, 1, 6] = true := by decide +kernel
theorem subd12_4_105 : subd12_4 [0, 1, 7] = true := by decide +kernel
theorem subd12_4_106 : subd12_4 [0, 2] = true := by decide +kernel
theorem subd12_4_107 : subd12_4 [1, -3] = true := by decide +kernel
theorem subd12_4_108 : subd12_4 [1, -2] = true := by decide +kernel
theorem subd12_4_109 : subd12_4 [1, -1, -8] = true := by decide +kernel
theorem subd12_4_110 : subd12_4 [1, -1, -7] = true := by decide +kernel
theorem subd12_4_111 : subd12_4 [1, -1, -6] = true := by decide +kernel
theorem subd12_4_112 : subd12_4 [1, -1, -5] = true := by decide +kernel
theorem subd12_4_113 : subd12_4 [1, -1, -4] = true := by decide +kernel
theorem subd12_4_114 : subd12_4 [1, -1, -3] = true := by decide +kernel
theorem subd12_4_115 : subd12_4 [1, -1, -2] = true := by decide +kernel
theorem subd12_4_116 : subd12_4 [1, -1, -1] = true := by decide +kernel
theorem subd12_4_117 : subd12_4 [1, -1, 0] = true := by decide +kernel
theorem subd12_4_118 : subd12_4 [1, -1, 1] = true := by decide +kernel
theorem subd12_4_119 : subd12_4 [1, -1, 2] = true := by decide +kernel
theorem subd12_4_120 : subd12_4 [1, -1, 3] = true := by decide +kernel
theorem subd12_4_121 : subd12_4 [1, -1, 4] = true := by decide +kernel
theorem subd12_4_122 : subd12_4 [1, -1, 5] = true := by decide +kernel
theorem subd12_4_123 : subd12_4 [1, -1, 6] = true := by decide +kernel
theorem subd12_4_124 : subd12_4 [1, -1, 7] = true := by decide +kernel
theorem subd12_4_125 : subd12_4 [1, 0, -8] = true := by decide +kernel
theorem subd12_4_126 : subd12_4 [1, 0, -7] = true := by decide +kernel
theorem subd12_4_127 : subd12_4 [1, 0, -6] = true := by decide +kernel
theorem sbd12_4_3 : ∀ q ∈ blkd12_4_3, subd12_4 q = true := by
  unfold blkd12_4_3
  exact List.forall_mem_cons.2 ⟨subd12_4_96, List.forall_mem_cons.2 ⟨subd12_4_97, List.forall_mem_cons.2 ⟨subd12_4_98, List.forall_mem_cons.2 ⟨subd12_4_99, List.forall_mem_cons.2 ⟨subd12_4_100, List.forall_mem_cons.2 ⟨subd12_4_101, List.forall_mem_cons.2 ⟨subd12_4_102, List.forall_mem_cons.2 ⟨subd12_4_103, List.forall_mem_cons.2 ⟨subd12_4_104, List.forall_mem_cons.2 ⟨subd12_4_105, List.forall_mem_cons.2 ⟨subd12_4_106, List.forall_mem_cons.2 ⟨subd12_4_107, List.forall_mem_cons.2 ⟨subd12_4_108, List.forall_mem_cons.2 ⟨subd12_4_109, List.forall_mem_cons.2 ⟨subd12_4_110, List.forall_mem_cons.2 ⟨subd12_4_111, List.forall_mem_cons.2 ⟨subd12_4_112, List.forall_mem_cons.2 ⟨subd12_4_113, List.forall_mem_cons.2 ⟨subd12_4_114, List.forall_mem_cons.2 ⟨subd12_4_115, List.forall_mem_cons.2 ⟨subd12_4_116, List.forall_mem_cons.2 ⟨subd12_4_117, List.forall_mem_cons.2 ⟨subd12_4_118, List.forall_mem_cons.2 ⟨subd12_4_119, List.forall_mem_cons.2 ⟨subd12_4_120, List.forall_mem_cons.2 ⟨subd12_4_121, List.forall_mem_cons.2 ⟨subd12_4_122, List.forall_mem_cons.2 ⟨subd12_4_123, List.forall_mem_cons.2 ⟨subd12_4_124, List.forall_mem_cons.2 ⟨subd12_4_125, List.forall_mem_cons.2 ⟨subd12_4_126, List.forall_mem_cons.2 ⟨subd12_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_4_128 : subd12_4 [1, 0, -5] = true := by decide +kernel
theorem subd12_4_129 : subd12_4 [1, 0, -4] = true := by decide +kernel
theorem subd12_4_130 : subd12_4 [1, 0, -3] = true := by decide +kernel
theorem subd12_4_131 : subd12_4 [1, 0, -2] = true := by decide +kernel
theorem subd12_4_132 : subd12_4 [1, 0, -1] = true := by decide +kernel
theorem subd12_4_133 : subd12_4 [1, 0, 0] = true := by decide +kernel
theorem subd12_4_134 : subd12_4 [1, 0, 1] = true := by decide +kernel
theorem subd12_4_135 : subd12_4 [1, 0, 2] = true := by decide +kernel
theorem subd12_4_136 : subd12_4 [1, 0, 3] = true := by decide +kernel
theorem subd12_4_137 : subd12_4 [1, 0, 4] = true := by decide +kernel
theorem subd12_4_138 : subd12_4 [1, 0, 5] = true := by decide +kernel
theorem subd12_4_139 : subd12_4 [1, 0, 6] = true := by decide +kernel
theorem subd12_4_140 : subd12_4 [1, 0, 7] = true := by decide +kernel
theorem subd12_4_141 : subd12_4 [1, 1, -7] = true := by decide +kernel
theorem subd12_4_142 : subd12_4 [1, 1, -6] = true := by decide +kernel
theorem subd12_4_143 : subd12_4 [1, 1, -5] = true := by decide +kernel
theorem subd12_4_144 : subd12_4 [1, 1, -4] = true := by decide +kernel
theorem subd12_4_145 : subd12_4 [1, 1, -3] = true := by decide +kernel
theorem subd12_4_146 : subd12_4 [1, 1, -2] = true := by decide +kernel
theorem subd12_4_147 : subd12_4 [1, 1, -1] = true := by decide +kernel
theorem subd12_4_148 : subd12_4 [1, 1, 0] = true := by decide +kernel
theorem subd12_4_149 : subd12_4 [1, 1, 1] = true := by decide +kernel
theorem subd12_4_150 : subd12_4 [1, 1, 2] = true := by decide +kernel
theorem subd12_4_151 : subd12_4 [1, 1, 3] = true := by decide +kernel
theorem subd12_4_152 : subd12_4 [1, 1, 4] = true := by decide +kernel
theorem subd12_4_153 : subd12_4 [1, 1, 5] = true := by decide +kernel
theorem subd12_4_154 : subd12_4 [1, 1, 6] = true := by decide +kernel
theorem subd12_4_155 : subd12_4 [1, 2] = true := by decide +kernel
theorem subd12_4_156 : subd12_4 [2, -3] = true := by decide +kernel
theorem subd12_4_157 : subd12_4 [2, -2] = true := by decide +kernel
theorem subd12_4_158 : subd12_4 [2, -1] = true := by decide +kernel
theorem subd12_4_159 : subd12_4 [2, 0] = true := by decide +kernel
theorem sbd12_4_4 : ∀ q ∈ blkd12_4_4, subd12_4 q = true := by
  unfold blkd12_4_4
  exact List.forall_mem_cons.2 ⟨subd12_4_128, List.forall_mem_cons.2 ⟨subd12_4_129, List.forall_mem_cons.2 ⟨subd12_4_130, List.forall_mem_cons.2 ⟨subd12_4_131, List.forall_mem_cons.2 ⟨subd12_4_132, List.forall_mem_cons.2 ⟨subd12_4_133, List.forall_mem_cons.2 ⟨subd12_4_134, List.forall_mem_cons.2 ⟨subd12_4_135, List.forall_mem_cons.2 ⟨subd12_4_136, List.forall_mem_cons.2 ⟨subd12_4_137, List.forall_mem_cons.2 ⟨subd12_4_138, List.forall_mem_cons.2 ⟨subd12_4_139, List.forall_mem_cons.2 ⟨subd12_4_140, List.forall_mem_cons.2 ⟨subd12_4_141, List.forall_mem_cons.2 ⟨subd12_4_142, List.forall_mem_cons.2 ⟨subd12_4_143, List.forall_mem_cons.2 ⟨subd12_4_144, List.forall_mem_cons.2 ⟨subd12_4_145, List.forall_mem_cons.2 ⟨subd12_4_146, List.forall_mem_cons.2 ⟨subd12_4_147, List.forall_mem_cons.2 ⟨subd12_4_148, List.forall_mem_cons.2 ⟨subd12_4_149, List.forall_mem_cons.2 ⟨subd12_4_150, List.forall_mem_cons.2 ⟨subd12_4_151, List.forall_mem_cons.2 ⟨subd12_4_152, List.forall_mem_cons.2 ⟨subd12_4_153, List.forall_mem_cons.2 ⟨subd12_4_154, List.forall_mem_cons.2 ⟨subd12_4_155, List.forall_mem_cons.2 ⟨subd12_4_156, List.forall_mem_cons.2 ⟨subd12_4_157, List.forall_mem_cons.2 ⟨subd12_4_158, List.forall_mem_cons.2 ⟨subd12_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_4_160 : subd12_4 [2, 1] = true := by decide +kernel
theorem sbd12_4_5 : ∀ q ∈ blkd12_4_5, subd12_4 q = true := by
  unfold blkd12_4_5
  exact List.forall_mem_cons.2 ⟨subd12_4_160, List.forall_mem_nil _⟩
theorem ld_okd12_5 : ldCheck G d12_5.U d12_5.ms ldd12_5 = true := by decide +kernel
theorem pre_okd12_5 : subPre G cell12 d12_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
