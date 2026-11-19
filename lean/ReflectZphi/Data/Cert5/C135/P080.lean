import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_5_0 : subd12_5 [-2, -2] = true := by decide +kernel
theorem subd12_5_1 : subd12_5 [-2, -1] = true := by decide +kernel
theorem subd12_5_2 : subd12_5 [-2, 0] = true := by decide +kernel
theorem subd12_5_3 : subd12_5 [-2, 1] = true := by decide +kernel
theorem subd12_5_4 : subd12_5 [-2, 2] = true := by decide +kernel
theorem subd12_5_5 : subd12_5 [-1, -3] = true := by decide +kernel
theorem subd12_5_6 : subd12_5 [-1, -2] = true := by decide +kernel
theorem subd12_5_7 : subd12_5 [-1, -1] = true := by decide +kernel
theorem subd12_5_8 : subd12_5 [-1, 0, -7] = true := by decide +kernel
theorem subd12_5_9 : subd12_5 [-1, 0, -6] = true := by decide +kernel
theorem subd12_5_10 : subd12_5 [-1, 0, -5] = true := by decide +kernel
theorem subd12_5_11 : subd12_5 [-1, 0, -4] = true := by decide +kernel
theorem subd12_5_12 : subd12_5 [-1, 0, -3] = true := by decide +kernel
theorem subd12_5_13 : subd12_5 [-1, 0, -2] = true := by decide +kernel
theorem subd12_5_14 : subd12_5 [-1, 0, -1] = true := by decide +kernel
theorem subd12_5_15 : subd12_5 [-1, 0, 0] = true := by decide +kernel
theorem subd12_5_16 : subd12_5 [-1, 0, 1] = true := by decide +kernel
theorem subd12_5_17 : subd12_5 [-1, 0, 2] = true := by decide +kernel
theorem subd12_5_18 : subd12_5 [-1, 0, 3] = true := by decide +kernel
theorem subd12_5_19 : subd12_5 [-1, 0, 4] = true := by decide +kernel
theorem subd12_5_20 : subd12_5 [-1, 0, 5] = true := by decide +kernel
theorem subd12_5_21 : subd12_5 [-1, 1, -7] = true := by decide +kernel
theorem subd12_5_22 : subd12_5 [-1, 1, -6] = true := by decide +kernel
theorem subd12_5_23 : subd12_5 [-1, 1, -5] = true := by decide +kernel
theorem subd12_5_24 : subd12_5 [-1, 1, -4] = true := by decide +kernel
theorem subd12_5_25 : subd12_5 [-1, 1, -3] = true := by decide +kernel
theorem subd12_5_26 : subd12_5 [-1, 1, -2] = true := by decide +kernel
theorem subd12_5_27 : subd12_5 [-1, 1, -1] = true := by decide +kernel
theorem subd12_5_28 : subd12_5 [-1, 1, 0] = true := by decide +kernel
theorem subd12_5_29 : subd12_5 [-1, 1, 1] = true := by decide +kernel
theorem subd12_5_30 : subd12_5 [-1, 1, 2] = true := by decide +kernel
theorem subd12_5_31 : subd12_5 [-1, 1, 3] = true := by decide +kernel
theorem sbd12_5_0 : ∀ q ∈ blkd12_5_0, subd12_5 q = true := by
  unfold blkd12_5_0
  exact List.forall_mem_cons.2 ⟨subd12_5_0, List.forall_mem_cons.2 ⟨subd12_5_1, List.forall_mem_cons.2 ⟨subd12_5_2, List.forall_mem_cons.2 ⟨subd12_5_3, List.forall_mem_cons.2 ⟨subd12_5_4, List.forall_mem_cons.2 ⟨subd12_5_5, List.forall_mem_cons.2 ⟨subd12_5_6, List.forall_mem_cons.2 ⟨subd12_5_7, List.forall_mem_cons.2 ⟨subd12_5_8, List.forall_mem_cons.2 ⟨subd12_5_9, List.forall_mem_cons.2 ⟨subd12_5_10, List.forall_mem_cons.2 ⟨subd12_5_11, List.forall_mem_cons.2 ⟨subd12_5_12, List.forall_mem_cons.2 ⟨subd12_5_13, List.forall_mem_cons.2 ⟨subd12_5_14, List.forall_mem_cons.2 ⟨subd12_5_15, List.forall_mem_cons.2 ⟨subd12_5_16, List.forall_mem_cons.2 ⟨subd12_5_17, List.forall_mem_cons.2 ⟨subd12_5_18, List.forall_mem_cons.2 ⟨subd12_5_19, List.forall_mem_cons.2 ⟨subd12_5_20, List.forall_mem_cons.2 ⟨subd12_5_21, List.forall_mem_cons.2 ⟨subd12_5_22, List.forall_mem_cons.2 ⟨subd12_5_23, List.forall_mem_cons.2 ⟨subd12_5_24, List.forall_mem_cons.2 ⟨subd12_5_25, List.forall_mem_cons.2 ⟨subd12_5_26, List.forall_mem_cons.2 ⟨subd12_5_27, List.forall_mem_cons.2 ⟨subd12_5_28, List.forall_mem_cons.2 ⟨subd12_5_29, List.forall_mem_cons.2 ⟨subd12_5_30, List.forall_mem_cons.2 ⟨subd12_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_5_32 : subd12_5 [-1, 1, 4] = true := by decide +kernel
theorem subd12_5_33 : subd12_5 [-1, 1, 5] = true := by decide +kernel
theorem subd12_5_34 : subd12_5 [-1, 2] = true := by decide +kernel
theorem subd12_5_35 : subd12_5 [0, -3] = true := by decide +kernel
theorem subd12_5_36 : subd12_5 [0, -2] = true := by decide +kernel
theorem subd12_5_37 : subd12_5 [0, -1, -7] = true := by decide +kernel
theorem subd12_5_38 : subd12_5 [0, -1, -6] = true := by decide +kernel
theorem subd12_5_39 : subd12_5 [0, -1, -5] = true := by decide +kernel
theorem subd12_5_40 : subd12_5 [0, -1, -4] = true := by decide +kernel
theorem subd12_5_41 : subd12_5 [0, -1, -3] = true := by decide +kernel
theorem subd12_5_42 : subd12_5 [0, -1, -2] = true := by decide +kernel
theorem subd12_5_43 : subd12_5 [0, -1, -1] = true := by decide +kernel
theorem subd12_5_44 : subd12_5 [0, -1, 0] = true := by decide +kernel
theorem subd12_5_45 : subd12_5 [0, -1, 1] = true := by decide +kernel
theorem subd12_5_46 : subd12_5 [0, -1, 2] = true := by decide +kernel
theorem subd12_5_47 : subd12_5 [0, -1, 3] = true := by decide +kernel
theorem subd12_5_48 : subd12_5 [0, -1, 4] = true := by decide +kernel
theorem subd12_5_49 : subd12_5 [0, -1, 5] = true := by decide +kernel
theorem subd12_5_50 : subd12_5 [0, -1, 6] = true := by decide +kernel
theorem subd12_5_51 : subd12_5 [0, 0, -7] = true := by decide +kernel
theorem subd12_5_52 : subd12_5 [0, 0, -6] = true := by decide +kernel
theorem subd12_5_53 : subd12_5 [0, 0, -5] = true := by decide +kernel
theorem subd12_5_54 : subd12_5 [0, 0, -4] = true := by decide +kernel
theorem subd12_5_55 : subd12_5 [0, 0, -3] = true := by decide +kernel
theorem subd12_5_56 : subd12_5 [0, 0, -2] = true := by decide +kernel
theorem subd12_5_57 : subd12_5 [0, 0, -1] = true := by decide +kernel
theorem subd12_5_58 : subd12_5 [0, 0, 0] = true := by decide +kernel
theorem subd12_5_59 : subd12_5 [0, 0, 1] = true := by decide +kernel
theorem subd12_5_60 : subd12_5 [0, 0, 2] = true := by decide +kernel
theorem subd12_5_61 : subd12_5 [0, 0, 3] = true := by decide +kernel
theorem subd12_5_62 : subd12_5 [0, 0, 4] = true := by decide +kernel
theorem subd12_5_63 : subd12_5 [0, 0, 5] = true := by decide +kernel
theorem sbd12_5_1 : ∀ q ∈ blkd12_5_1, subd12_5 q = true := by
  unfold blkd12_5_1
  exact List.forall_mem_cons.2 ⟨subd12_5_32, List.forall_mem_cons.2 ⟨subd12_5_33, List.forall_mem_cons.2 ⟨subd12_5_34, List.forall_mem_cons.2 ⟨subd12_5_35, List.forall_mem_cons.2 ⟨subd12_5_36, List.forall_mem_cons.2 ⟨subd12_5_37, List.forall_mem_cons.2 ⟨subd12_5_38, List.forall_mem_cons.2 ⟨subd12_5_39, List.forall_mem_cons.2 ⟨subd12_5_40, List.forall_mem_cons.2 ⟨subd12_5_41, List.forall_mem_cons.2 ⟨subd12_5_42, List.forall_mem_cons.2 ⟨subd12_5_43, List.forall_mem_cons.2 ⟨subd12_5_44, List.forall_mem_cons.2 ⟨subd12_5_45, List.forall_mem_cons.2 ⟨subd12_5_46, List.forall_mem_cons.2 ⟨subd12_5_47, List.forall_mem_cons.2 ⟨subd12_5_48, List.forall_mem_cons.2 ⟨subd12_5_49, List.forall_mem_cons.2 ⟨subd12_5_50, List.forall_mem_cons.2 ⟨subd12_5_51, List.forall_mem_cons.2 ⟨subd12_5_52, List.forall_mem_cons.2 ⟨subd12_5_53, List.forall_mem_cons.2 ⟨subd12_5_54, List.forall_mem_cons.2 ⟨subd12_5_55, List.forall_mem_cons.2 ⟨subd12_5_56, List.forall_mem_cons.2 ⟨subd12_5_57, List.forall_mem_cons.2 ⟨subd12_5_58, List.forall_mem_cons.2 ⟨subd12_5_59, List.forall_mem_cons.2 ⟨subd12_5_60, List.forall_mem_cons.2 ⟨subd12_5_61, List.forall_mem_cons.2 ⟨subd12_5_62, List.forall_mem_cons.2 ⟨subd12_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_5_64 : subd12_5 [0, 0, 6] = true := by decide +kernel
theorem subd12_5_65 : subd12_5 [0, 1, -7] = true := by decide +kernel
theorem subd12_5_66 : subd12_5 [0, 1, -6] = true := by decide +kernel
theorem subd12_5_67 : subd12_5 [0, 1, -5] = true := by decide +kernel
theorem subd12_5_68 : subd12_5 [0, 1, -4] = true := by decide +kernel
theorem subd12_5_69 : subd12_5 [0, 1, -3] = true := by decide +kernel
theorem subd12_5_70 : subd12_5 [0, 1, -2] = true := by decide +kernel
theorem subd12_5_71 : subd12_5 [0, 1, -1] = true := by decide +kernel
theorem subd12_5_72 : subd12_5 [0, 1, 0] = true := by decide +kernel
theorem subd12_5_73 : subd12_5 [0, 1, 1] = true := by decide +kernel
theorem subd12_5_74 : subd12_5 [0, 1, 2] = true := by decide +kernel
theorem subd12_5_75 : subd12_5 [0, 1, 3] = true := by decide +kernel
theorem subd12_5_76 : subd12_5 [0, 1, 4] = true := by decide +kernel
theorem subd12_5_77 : subd12_5 [0, 1, 5] = true := by decide +kernel
theorem subd12_5_78 : subd12_5 [0, 1, 6] = true := by decide +kernel
theorem subd12_5_79 : subd12_5 [0, 2] = true := by decide +kernel
theorem subd12_5_80 : subd12_5 [1, -3] = true := by decide +kernel
theorem subd12_5_81 : subd12_5 [1, -2] = true := by decide +kernel
theorem subd12_5_82 : subd12_5 [1, -1, -6] = true := by decide +kernel
theorem subd12_5_83 : subd12_5 [1, -1, -5] = true := by decide +kernel
theorem subd12_5_84 : subd12_5 [1, -1, -4] = true := by decide +kernel
theorem subd12_5_85 : subd12_5 [1, -1, -3] = true := by decide +kernel
theorem subd12_5_86 : subd12_5 [1, -1, -2] = true := by decide +kernel
theorem subd12_5_87 : subd12_5 [1, -1, -1] = true := by decide +kernel
theorem subd12_5_88 : subd12_5 [1, -1, 0] = true := by decide +kernel
theorem subd12_5_89 : subd12_5 [1, -1, 1] = true := by decide +kernel
theorem subd12_5_90 : subd12_5 [1, -1, 2] = true := by decide +kernel
theorem subd12_5_91 : subd12_5 [1, -1, 3] = true := by decide +kernel
theorem subd12_5_92 : subd12_5 [1, -1, 4] = true := by decide +kernel
theorem subd12_5_93 : subd12_5 [1, -1, 5] = true := by decide +kernel
theorem subd12_5_94 : subd12_5 [1, -1, 6] = true := by decide +kernel
theorem subd12_5_95 : subd12_5 [1, 0, -6] = true := by decide +kernel
theorem sbd12_5_2 : ∀ q ∈ blkd12_5_2, subd12_5 q = true := by
  unfold blkd12_5_2
  exact List.forall_mem_cons.2 ⟨subd12_5_64, List.forall_mem_cons.2 ⟨subd12_5_65, List.forall_mem_cons.2 ⟨subd12_5_66, List.forall_mem_cons.2 ⟨subd12_5_67, List.forall_mem_cons.2 ⟨subd12_5_68, List.forall_mem_cons.2 ⟨subd12_5_69, List.forall_mem_cons.2 ⟨subd12_5_70, List.forall_mem_cons.2 ⟨subd12_5_71, List.forall_mem_cons.2 ⟨subd12_5_72, List.forall_mem_cons.2 ⟨subd12_5_73, List.forall_mem_cons.2 ⟨subd12_5_74, List.forall_mem_cons.2 ⟨subd12_5_75, List.forall_mem_cons.2 ⟨subd12_5_76, List.forall_mem_cons.2 ⟨subd12_5_77, List.forall_mem_cons.2 ⟨subd12_5_78, List.forall_mem_cons.2 ⟨subd12_5_79, List.forall_mem_cons.2 ⟨subd12_5_80, List.forall_mem_cons.2 ⟨subd12_5_81, List.forall_mem_cons.2 ⟨subd12_5_82, List.forall_mem_cons.2 ⟨subd12_5_83, List.forall_mem_cons.2 ⟨subd12_5_84, List.forall_mem_cons.2 ⟨subd12_5_85, List.forall_mem_cons.2 ⟨subd12_5_86, List.forall_mem_cons.2 ⟨subd12_5_87, List.forall_mem_cons.2 ⟨subd12_5_88, List.forall_mem_cons.2 ⟨subd12_5_89, List.forall_mem_cons.2 ⟨subd12_5_90, List.forall_mem_cons.2 ⟨subd12_5_91, List.forall_mem_cons.2 ⟨subd12_5_92, List.forall_mem_cons.2 ⟨subd12_5_93, List.forall_mem_cons.2 ⟨subd12_5_94, List.forall_mem_cons.2 ⟨subd12_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_5_96 : subd12_5 [1, 0, -5] = true := by decide +kernel
theorem subd12_5_97 : subd12_5 [1, 0, -4] = true := by decide +kernel
theorem subd12_5_98 : subd12_5 [1, 0, -3] = true := by decide +kernel
theorem subd12_5_99 : subd12_5 [1, 0, -2] = true := by decide +kernel
theorem subd12_5_100 : subd12_5 [1, 0, -1] = true := by decide +kernel
theorem subd12_5_101 : subd12_5 [1, 0, 0] = true := by decide +kernel
theorem subd12_5_102 : subd12_5 [1, 0, 1] = true := by decide +kernel
theorem subd12_5_103 : subd12_5 [1, 0, 2] = true := by decide +kernel
theorem subd12_5_104 : subd12_5 [1, 0, 3] = true := by decide +kernel
theorem subd12_5_105 : subd12_5 [1, 0, 4] = true := by decide +kernel
theorem subd12_5_106 : subd12_5 [1, 0, 5] = true := by decide +kernel
theorem subd12_5_107 : subd12_5 [1, 0, 6] = true := by decide +kernel
theorem subd12_5_108 : subd12_5 [1, 1] = true := by decide +kernel
theorem subd12_5_109 : subd12_5 [1, 2] = true := by decide +kernel
theorem subd12_5_110 : subd12_5 [2, -3] = true := by decide +kernel
theorem subd12_5_111 : subd12_5 [2, -2] = true := by decide +kernel
theorem subd12_5_112 : subd12_5 [2, -1] = true := by decide +kernel
theorem subd12_5_113 : subd12_5 [2, 0] = true := by decide +kernel
theorem subd12_5_114 : subd12_5 [2, 1] = true := by decide +kernel
theorem sbd12_5_3 : ∀ q ∈ blkd12_5_3, subd12_5 q = true := by
  unfold blkd12_5_3
  exact List.forall_mem_cons.2 ⟨subd12_5_96, List.forall_mem_cons.2 ⟨subd12_5_97, List.forall_mem_cons.2 ⟨subd12_5_98, List.forall_mem_cons.2 ⟨subd12_5_99, List.forall_mem_cons.2 ⟨subd12_5_100, List.forall_mem_cons.2 ⟨subd12_5_101, List.forall_mem_cons.2 ⟨subd12_5_102, List.forall_mem_cons.2 ⟨subd12_5_103, List.forall_mem_cons.2 ⟨subd12_5_104, List.forall_mem_cons.2 ⟨subd12_5_105, List.forall_mem_cons.2 ⟨subd12_5_106, List.forall_mem_cons.2 ⟨subd12_5_107, List.forall_mem_cons.2 ⟨subd12_5_108, List.forall_mem_cons.2 ⟨subd12_5_109, List.forall_mem_cons.2 ⟨subd12_5_110, List.forall_mem_cons.2 ⟨subd12_5_111, List.forall_mem_cons.2 ⟨subd12_5_112, List.forall_mem_cons.2 ⟨subd12_5_113, List.forall_mem_cons.2 ⟨subd12_5_114, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_6 : ldCheck G d12_6.U d12_6.ms ldd12_6 = true := by decide +kernel
theorem pre_okd12_6 : subPre G cell12 d12_6 = true := by decide +kernel
theorem subd12_6_0 : subd12_6 [-2] = true := by decide +kernel
theorem subd12_6_1 : subd12_6 [-1, -3] = true := by decide +kernel
theorem subd12_6_2 : subd12_6 [-1, -2] = true := by decide +kernel
theorem subd12_6_3 : subd12_6 [-1, -1] = true := by decide +kernel
theorem subd12_6_4 : subd12_6 [-1, 0] = true := by decide +kernel
theorem subd12_6_5 : subd12_6 [-1, 1] = true := by decide +kernel
theorem subd12_6_6 : subd12_6 [-1, 2] = true := by decide +kernel
theorem subd12_6_7 : subd12_6 [0, -3] = true := by decide +kernel
theorem subd12_6_8 : subd12_6 [0, -2] = true := by decide +kernel
theorem subd12_6_9 : subd12_6 [0, -1] = true := by decide +kernel
theorem subd12_6_10 : subd12_6 [0, 0] = true := by decide +kernel
theorem subd12_6_11 : subd12_6 [0, 1] = true := by decide +kernel
theorem subd12_6_12 : subd12_6 [0, 2] = true := by decide +kernel
theorem subd12_6_13 : subd12_6 [1, -3] = true := by decide +kernel
theorem subd12_6_14 : subd12_6 [1, -2] = true := by decide +kernel
theorem subd12_6_15 : subd12_6 [1, -1] = true := by decide +kernel
theorem subd12_6_16 : subd12_6 [1, 0] = true := by decide +kernel
theorem subd12_6_17 : subd12_6 [1, 1] = true := by decide +kernel
theorem subd12_6_18 : subd12_6 [1, 2] = true := by decide +kernel
theorem subd12_6_19 : subd12_6 [2] = true := by decide +kernel
theorem sbd12_6_0 : ∀ q ∈ blkd12_6_0, subd12_6 q = true := by
  unfold blkd12_6_0
  exact List.forall_mem_cons.2 ⟨subd12_6_0, List.forall_mem_cons.2 ⟨subd12_6_1, List.forall_mem_cons.2 ⟨subd12_6_2, List.forall_mem_cons.2 ⟨subd12_6_3, List.forall_mem_cons.2 ⟨subd12_6_4, List.forall_mem_cons.2 ⟨subd12_6_5, List.forall_mem_cons.2 ⟨subd12_6_6, List.forall_mem_cons.2 ⟨subd12_6_7, List.forall_mem_cons.2 ⟨subd12_6_8, List.forall_mem_cons.2 ⟨subd12_6_9, List.forall_mem_cons.2 ⟨subd12_6_10, List.forall_mem_cons.2 ⟨subd12_6_11, List.forall_mem_cons.2 ⟨subd12_6_12, List.forall_mem_cons.2 ⟨subd12_6_13, List.forall_mem_cons.2 ⟨subd12_6_14, List.forall_mem_cons.2 ⟨subd12_6_15, List.forall_mem_cons.2 ⟨subd12_6_16, List.forall_mem_cons.2 ⟨subd12_6_17, List.forall_mem_cons.2 ⟨subd12_6_18, List.forall_mem_cons.2 ⟨subd12_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_7 : ldCheck G d12_7.U d12_7.ms ldd12_7 = true := by decide +kernel
theorem pre_okd12_7 : subPre G cell12 d12_7 = true := by decide +kernel
theorem subd12_7_0 : subd12_7 [-3] = true := by decide +kernel
theorem subd12_7_1 : subd12_7 [-2, -3] = true := by decide +kernel
theorem subd12_7_2 : subd12_7 [-2, -2] = true := by decide +kernel
theorem subd12_7_3 : subd12_7 [-2, -1] = true := by decide +kernel
theorem subd12_7_4 : subd12_7 [-2, 0] = true := by decide +kernel
theorem subd12_7_5 : subd12_7 [-2, 1] = true := by decide +kernel
theorem subd12_7_6 : subd12_7 [-2, 2] = true := by decide +kernel
theorem subd12_7_7 : subd12_7 [-2, 3] = true := by decide +kernel
theorem subd12_7_8 : subd12_7 [-2, 4] = true := by decide +kernel
theorem subd12_7_9 : subd12_7 [-1, -4] = true := by decide +kernel
theorem subd12_7_10 : subd12_7 [-1, -3] = true := by decide +kernel
theorem subd12_7_11 : subd12_7 [-1, -2] = true := by decide +kernel
theorem subd12_7_12 : subd12_7 [-1, -1] = true := by decide +kernel
theorem subd12_7_13 : subd12_7 [-1, 0] = true := by decide +kernel
theorem subd12_7_14 : subd12_7 [-1, 1] = true := by decide +kernel
theorem subd12_7_15 : subd12_7 [-1, 2] = true := by decide +kernel
theorem subd12_7_16 : subd12_7 [-1, 3] = true := by decide +kernel
theorem subd12_7_17 : subd12_7 [-1, 4] = true := by decide +kernel
theorem subd12_7_18 : subd12_7 [0, -5] = true := by decide +kernel
theorem subd12_7_19 : subd12_7 [0, -4] = true := by decide +kernel
theorem subd12_7_20 : subd12_7 [0, -3] = true := by decide +kernel
theorem subd12_7_21 : subd12_7 [0, -2] = true := by decide +kernel
theorem subd12_7_22 : subd12_7 [0, -1] = true := by decide +kernel
theorem subd12_7_23 : subd12_7 [0, 0] = true := by decide +kernel
theorem subd12_7_24 : subd12_7 [0, 1] = true := by decide +kernel
theorem subd12_7_25 : subd12_7 [0, 2] = true := by decide +kernel
theorem subd12_7_26 : subd12_7 [0, 3] = true := by decide +kernel
theorem subd12_7_27 : subd12_7 [0, 4] = true := by decide +kernel
theorem subd12_7_28 : subd12_7 [1, -5] = true := by decide +kernel
theorem subd12_7_29 : subd12_7 [1, -4] = true := by decide +kernel
theorem subd12_7_30 : subd12_7 [1, -3] = true := by decide +kernel
theorem subd12_7_31 : subd12_7 [1, -2] = true := by decide +kernel
theorem sbd12_7_0 : ∀ q ∈ blkd12_7_0, subd12_7 q = true := by
  unfold blkd12_7_0
  exact List.forall_mem_cons.2 ⟨subd12_7_0, List.forall_mem_cons.2 ⟨subd12_7_1, List.forall_mem_cons.2 ⟨subd12_7_2, List.forall_mem_cons.2 ⟨subd12_7_3, List.forall_mem_cons.2 ⟨subd12_7_4, List.forall_mem_cons.2 ⟨subd12_7_5, List.forall_mem_cons.2 ⟨subd12_7_6, List.forall_mem_cons.2 ⟨subd12_7_7, List.forall_mem_cons.2 ⟨subd12_7_8, List.forall_mem_cons.2 ⟨subd12_7_9, List.forall_mem_cons.2 ⟨subd12_7_10, List.forall_mem_cons.2 ⟨subd12_7_11, List.forall_mem_cons.2 ⟨subd12_7_12, List.forall_mem_cons.2 ⟨subd12_7_13, List.forall_mem_cons.2 ⟨subd12_7_14, List.forall_mem_cons.2 ⟨subd12_7_15, List.forall_mem_cons.2 ⟨subd12_7_16, List.forall_mem_cons.2 ⟨subd12_7_17, List.forall_mem_cons.2 ⟨subd12_7_18, List.forall_mem_cons.2 ⟨subd12_7_19, List.forall_mem_cons.2 ⟨subd12_7_20, List.forall_mem_cons.2 ⟨subd12_7_21, List.forall_mem_cons.2 ⟨subd12_7_22, List.forall_mem_cons.2 ⟨subd12_7_23, List.forall_mem_cons.2 ⟨subd12_7_24, List.forall_mem_cons.2 ⟨subd12_7_25, List.forall_mem_cons.2 ⟨subd12_7_26, List.forall_mem_cons.2 ⟨subd12_7_27, List.forall_mem_cons.2 ⟨subd12_7_28, List.forall_mem_cons.2 ⟨subd12_7_29, List.forall_mem_cons.2 ⟨subd12_7_30, List.forall_mem_cons.2 ⟨subd12_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_7_32 : subd12_7 [1, -1] = true := by decide +kernel
theorem subd12_7_33 : subd12_7 [1, 0] = true := by decide +kernel
theorem subd12_7_34 : subd12_7 [1, 1] = true := by decide +kernel
theorem subd12_7_35 : subd12_7 [1, 2] = true := by decide +kernel
theorem subd12_7_36 : subd12_7 [1, 3] = true := by decide +kernel
theorem subd12_7_37 : subd12_7 [2, -5] = true := by decide +kernel
theorem subd12_7_38 : subd12_7 [2, -4] = true := by decide +kernel
theorem subd12_7_39 : subd12_7 [2, -3] = true := by decide +kernel
theorem subd12_7_40 : subd12_7 [2, -2] = true := by decide +kernel
theorem subd12_7_41 : subd12_7 [2, -1] = true := by decide +kernel
theorem subd12_7_42 : subd12_7 [2, 0] = true := by decide +kernel
theorem subd12_7_43 : subd12_7 [2, 1] = true := by decide +kernel
theorem subd12_7_44 : subd12_7 [2, 2] = true := by decide +kernel
theorem subd12_7_45 : subd12_7 [3] = true := by decide +kernel
theorem sbd12_7_1 : ∀ q ∈ blkd12_7_1, subd12_7 q = true := by
  unfold blkd12_7_1
  exact List.forall_mem_cons.2 ⟨subd12_7_32, List.forall_mem_cons.2 ⟨subd12_7_33, List.forall_mem_cons.2 ⟨subd12_7_34, List.forall_mem_cons.2 ⟨subd12_7_35, List.forall_mem_cons.2 ⟨subd12_7_36, List.forall_mem_cons.2 ⟨subd12_7_37, List.forall_mem_cons.2 ⟨subd12_7_38, List.forall_mem_cons.2 ⟨subd12_7_39, List.forall_mem_cons.2 ⟨subd12_7_40, List.forall_mem_cons.2 ⟨subd12_7_41, List.forall_mem_cons.2 ⟨subd12_7_42, List.forall_mem_cons.2 ⟨subd12_7_43, List.forall_mem_cons.2 ⟨subd12_7_44, List.forall_mem_cons.2 ⟨subd12_7_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
