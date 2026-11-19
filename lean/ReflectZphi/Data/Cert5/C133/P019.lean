import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_3_0 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-1, 0, -7] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-1, 0, -6] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-1, 0, -5] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-1, 0, -4] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-1, 0, -3] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-1, 0, -2] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-1, 0, -1] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [-1, 0, 0] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [-1, 0, 1] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [-1, 0, 2] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [-1, 0, 3] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [-1, 0, 4] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [-1, 0, 5] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [-1, 0, 6] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [-1, 1, -7] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [-1, 1, -6] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [-1, 1, -5] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [-1, 1, -4] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [-1, 1, -3] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [-1, 1, -2] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [-1, 1, -1] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [-1, 1, 0] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [-1, 1, 1] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [-1, 1, 2] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [-1, 1, 3] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [-1, 1, 4] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [-1, 1, 5] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [-1, 1, 6] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_36 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_37 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_38 : subd11_3 [0, -1, -7] = true := by decide +kernel
theorem subd11_3_39 : subd11_3 [0, -1, -6] = true := by decide +kernel
theorem subd11_3_40 : subd11_3 [0, -1, -5] = true := by decide +kernel
theorem subd11_3_41 : subd11_3 [0, -1, -4] = true := by decide +kernel
theorem subd11_3_42 : subd11_3 [0, -1, -3] = true := by decide +kernel
theorem subd11_3_43 : subd11_3 [0, -1, -2] = true := by decide +kernel
theorem subd11_3_44 : subd11_3 [0, -1, -1] = true := by decide +kernel
theorem subd11_3_45 : subd11_3 [0, -1, 0] = true := by decide +kernel
theorem subd11_3_46 : subd11_3 [0, -1, 1] = true := by decide +kernel
theorem subd11_3_47 : subd11_3 [0, -1, 2] = true := by decide +kernel
theorem subd11_3_48 : subd11_3 [0, -1, 3] = true := by decide +kernel
theorem subd11_3_49 : subd11_3 [0, -1, 4] = true := by decide +kernel
theorem subd11_3_50 : subd11_3 [0, -1, 5] = true := by decide +kernel
theorem subd11_3_51 : subd11_3 [0, -1, 6] = true := by decide +kernel
theorem subd11_3_52 : subd11_3 [0, 0, -8] = true := by decide +kernel
theorem subd11_3_53 : subd11_3 [0, 0, -7] = true := by decide +kernel
theorem subd11_3_54 : subd11_3 [0, 0, -6] = true := by decide +kernel
theorem subd11_3_55 : subd11_3 [0, 0, -5] = true := by decide +kernel
theorem subd11_3_56 : subd11_3 [0, 0, -4] = true := by decide +kernel
theorem subd11_3_57 : subd11_3 [0, 0, -3] = true := by decide +kernel
theorem subd11_3_58 : subd11_3 [0, 0, -2] = true := by decide +kernel
theorem subd11_3_59 : subd11_3 [0, 0, -1] = true := by decide +kernel
theorem subd11_3_60 : subd11_3 [0, 0, 0] = true := by decide +kernel
theorem subd11_3_61 : subd11_3 [0, 0, 1] = true := by decide +kernel
theorem subd11_3_62 : subd11_3 [0, 0, 2] = true := by decide +kernel
theorem subd11_3_63 : subd11_3 [0, 0, 3] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_cons.2 ⟨subd11_3_36, List.forall_mem_cons.2 ⟨subd11_3_37, List.forall_mem_cons.2 ⟨subd11_3_38, List.forall_mem_cons.2 ⟨subd11_3_39, List.forall_mem_cons.2 ⟨subd11_3_40, List.forall_mem_cons.2 ⟨subd11_3_41, List.forall_mem_cons.2 ⟨subd11_3_42, List.forall_mem_cons.2 ⟨subd11_3_43, List.forall_mem_cons.2 ⟨subd11_3_44, List.forall_mem_cons.2 ⟨subd11_3_45, List.forall_mem_cons.2 ⟨subd11_3_46, List.forall_mem_cons.2 ⟨subd11_3_47, List.forall_mem_cons.2 ⟨subd11_3_48, List.forall_mem_cons.2 ⟨subd11_3_49, List.forall_mem_cons.2 ⟨subd11_3_50, List.forall_mem_cons.2 ⟨subd11_3_51, List.forall_mem_cons.2 ⟨subd11_3_52, List.forall_mem_cons.2 ⟨subd11_3_53, List.forall_mem_cons.2 ⟨subd11_3_54, List.forall_mem_cons.2 ⟨subd11_3_55, List.forall_mem_cons.2 ⟨subd11_3_56, List.forall_mem_cons.2 ⟨subd11_3_57, List.forall_mem_cons.2 ⟨subd11_3_58, List.forall_mem_cons.2 ⟨subd11_3_59, List.forall_mem_cons.2 ⟨subd11_3_60, List.forall_mem_cons.2 ⟨subd11_3_61, List.forall_mem_cons.2 ⟨subd11_3_62, List.forall_mem_cons.2 ⟨subd11_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_64 : subd11_3 [0, 0, 4] = true := by decide +kernel
theorem subd11_3_65 : subd11_3 [0, 0, 5] = true := by decide +kernel
theorem subd11_3_66 : subd11_3 [0, 0, 6] = true := by decide +kernel
theorem subd11_3_67 : subd11_3 [0, 0, 7] = true := by decide +kernel
theorem subd11_3_68 : subd11_3 [0, 1, -7] = true := by decide +kernel
theorem subd11_3_69 : subd11_3 [0, 1, -6] = true := by decide +kernel
theorem subd11_3_70 : subd11_3 [0, 1, -5] = true := by decide +kernel
theorem subd11_3_71 : subd11_3 [0, 1, -4] = true := by decide +kernel
theorem subd11_3_72 : subd11_3 [0, 1, -3] = true := by decide +kernel
theorem subd11_3_73 : subd11_3 [0, 1, -2] = true := by decide +kernel
theorem subd11_3_74 : subd11_3 [0, 1, -1] = true := by decide +kernel
theorem subd11_3_75 : subd11_3 [0, 1, 0] = true := by decide +kernel
theorem subd11_3_76 : subd11_3 [0, 1, 1] = true := by decide +kernel
theorem subd11_3_77 : subd11_3 [0, 1, 2] = true := by decide +kernel
theorem subd11_3_78 : subd11_3 [0, 1, 3] = true := by decide +kernel
theorem subd11_3_79 : subd11_3 [0, 1, 4] = true := by decide +kernel
theorem subd11_3_80 : subd11_3 [0, 1, 5] = true := by decide +kernel
theorem subd11_3_81 : subd11_3 [0, 1, 6] = true := by decide +kernel
theorem subd11_3_82 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_83 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_84 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_85 : subd11_3 [1, -1, -7] = true := by decide +kernel
theorem subd11_3_86 : subd11_3 [1, -1, -6] = true := by decide +kernel
theorem subd11_3_87 : subd11_3 [1, -1, -5] = true := by decide +kernel
theorem subd11_3_88 : subd11_3 [1, -1, -4] = true := by decide +kernel
theorem subd11_3_89 : subd11_3 [1, -1, -3] = true := by decide +kernel
theorem subd11_3_90 : subd11_3 [1, -1, -2] = true := by decide +kernel
theorem subd11_3_91 : subd11_3 [1, -1, -1] = true := by decide +kernel
theorem subd11_3_92 : subd11_3 [1, -1, 0] = true := by decide +kernel
theorem subd11_3_93 : subd11_3 [1, -1, 1] = true := by decide +kernel
theorem subd11_3_94 : subd11_3 [1, -1, 2] = true := by decide +kernel
theorem subd11_3_95 : subd11_3 [1, -1, 3] = true := by decide +kernel
theorem sbd11_3_2 : ∀ q ∈ blkd11_3_2, subd11_3 q = true := by
  unfold blkd11_3_2
  exact List.forall_mem_cons.2 ⟨subd11_3_64, List.forall_mem_cons.2 ⟨subd11_3_65, List.forall_mem_cons.2 ⟨subd11_3_66, List.forall_mem_cons.2 ⟨subd11_3_67, List.forall_mem_cons.2 ⟨subd11_3_68, List.forall_mem_cons.2 ⟨subd11_3_69, List.forall_mem_cons.2 ⟨subd11_3_70, List.forall_mem_cons.2 ⟨subd11_3_71, List.forall_mem_cons.2 ⟨subd11_3_72, List.forall_mem_cons.2 ⟨subd11_3_73, List.forall_mem_cons.2 ⟨subd11_3_74, List.forall_mem_cons.2 ⟨subd11_3_75, List.forall_mem_cons.2 ⟨subd11_3_76, List.forall_mem_cons.2 ⟨subd11_3_77, List.forall_mem_cons.2 ⟨subd11_3_78, List.forall_mem_cons.2 ⟨subd11_3_79, List.forall_mem_cons.2 ⟨subd11_3_80, List.forall_mem_cons.2 ⟨subd11_3_81, List.forall_mem_cons.2 ⟨subd11_3_82, List.forall_mem_cons.2 ⟨subd11_3_83, List.forall_mem_cons.2 ⟨subd11_3_84, List.forall_mem_cons.2 ⟨subd11_3_85, List.forall_mem_cons.2 ⟨subd11_3_86, List.forall_mem_cons.2 ⟨subd11_3_87, List.forall_mem_cons.2 ⟨subd11_3_88, List.forall_mem_cons.2 ⟨subd11_3_89, List.forall_mem_cons.2 ⟨subd11_3_90, List.forall_mem_cons.2 ⟨subd11_3_91, List.forall_mem_cons.2 ⟨subd11_3_92, List.forall_mem_cons.2 ⟨subd11_3_93, List.forall_mem_cons.2 ⟨subd11_3_94, List.forall_mem_cons.2 ⟨subd11_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_96 : subd11_3 [1, -1, 4] = true := by decide +kernel
theorem subd11_3_97 : subd11_3 [1, -1, 5] = true := by decide +kernel
theorem subd11_3_98 : subd11_3 [1, -1, 6] = true := by decide +kernel
theorem subd11_3_99 : subd11_3 [1, 0, -7] = true := by decide +kernel
theorem subd11_3_100 : subd11_3 [1, 0, -6] = true := by decide +kernel
theorem subd11_3_101 : subd11_3 [1, 0, -5] = true := by decide +kernel
theorem subd11_3_102 : subd11_3 [1, 0, -4] = true := by decide +kernel
theorem subd11_3_103 : subd11_3 [1, 0, -3] = true := by decide +kernel
theorem subd11_3_104 : subd11_3 [1, 0, -2] = true := by decide +kernel
theorem subd11_3_105 : subd11_3 [1, 0, -1] = true := by decide +kernel
theorem subd11_3_106 : subd11_3 [1, 0, 0] = true := by decide +kernel
theorem subd11_3_107 : subd11_3 [1, 0, 1] = true := by decide +kernel
theorem subd11_3_108 : subd11_3 [1, 0, 2] = true := by decide +kernel
theorem subd11_3_109 : subd11_3 [1, 0, 3] = true := by decide +kernel
theorem subd11_3_110 : subd11_3 [1, 0, 4] = true := by decide +kernel
theorem subd11_3_111 : subd11_3 [1, 0, 5] = true := by decide +kernel
theorem subd11_3_112 : subd11_3 [1, 0, 6] = true := by decide +kernel
theorem subd11_3_113 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_114 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_115 : subd11_3 [2, -3] = true := by decide +kernel
theorem subd11_3_116 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_117 : subd11_3 [2, -1] = true := by decide +kernel
theorem subd11_3_118 : subd11_3 [2, 0] = true := by decide +kernel
theorem sbd11_3_3 : ∀ q ∈ blkd11_3_3, subd11_3 q = true := by
  unfold blkd11_3_3
  exact List.forall_mem_cons.2 ⟨subd11_3_96, List.forall_mem_cons.2 ⟨subd11_3_97, List.forall_mem_cons.2 ⟨subd11_3_98, List.forall_mem_cons.2 ⟨subd11_3_99, List.forall_mem_cons.2 ⟨subd11_3_100, List.forall_mem_cons.2 ⟨subd11_3_101, List.forall_mem_cons.2 ⟨subd11_3_102, List.forall_mem_cons.2 ⟨subd11_3_103, List.forall_mem_cons.2 ⟨subd11_3_104, List.forall_mem_cons.2 ⟨subd11_3_105, List.forall_mem_cons.2 ⟨subd11_3_106, List.forall_mem_cons.2 ⟨subd11_3_107, List.forall_mem_cons.2 ⟨subd11_3_108, List.forall_mem_cons.2 ⟨subd11_3_109, List.forall_mem_cons.2 ⟨subd11_3_110, List.forall_mem_cons.2 ⟨subd11_3_111, List.forall_mem_cons.2 ⟨subd11_3_112, List.forall_mem_cons.2 ⟨subd11_3_113, List.forall_mem_cons.2 ⟨subd11_3_114, List.forall_mem_cons.2 ⟨subd11_3_115, List.forall_mem_cons.2 ⟨subd11_3_116, List.forall_mem_cons.2 ⟨subd11_3_117, List.forall_mem_cons.2 ⟨subd11_3_118, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_nil _⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_nil _⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-3] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-2, -4] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [-2, -3] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [-2, -2] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [-2, -1] = true := by decide +kernel
theorem subd12_2_5 : subd12_2 [-2, 0] = true := by decide +kernel
theorem subd12_2_6 : subd12_2 [-2, 1] = true := by decide +kernel
theorem subd12_2_7 : subd12_2 [-2, 2] = true := by decide +kernel
theorem subd12_2_8 : subd12_2 [-2, 3] = true := by decide +kernel
theorem subd12_2_9 : subd12_2 [-1, -5] = true := by decide +kernel
theorem subd12_2_10 : subd12_2 [-1, -4] = true := by decide +kernel
theorem subd12_2_11 : subd12_2 [-1, -3] = true := by decide +kernel
theorem subd12_2_12 : subd12_2 [-1, -2] = true := by decide +kernel
theorem subd12_2_13 : subd12_2 [-1, -1] = true := by decide +kernel
theorem subd12_2_14 : subd12_2 [-1, 0] = true := by decide +kernel
theorem subd12_2_15 : subd12_2 [-1, 1] = true := by decide +kernel
theorem subd12_2_16 : subd12_2 [-1, 2] = true := by decide +kernel
theorem subd12_2_17 : subd12_2 [-1, 3] = true := by decide +kernel
theorem subd12_2_18 : subd12_2 [0, -5] = true := by decide +kernel
theorem subd12_2_19 : subd12_2 [0, -4] = true := by decide +kernel
theorem subd12_2_20 : subd12_2 [0, -3] = true := by decide +kernel
theorem subd12_2_21 : subd12_2 [0, -2] = true := by decide +kernel
theorem subd12_2_22 : subd12_2 [0, -1] = true := by decide +kernel
theorem subd12_2_23 : subd12_2 [0, 0] = true := by decide +kernel
theorem subd12_2_24 : subd12_2 [0, 1] = true := by decide +kernel
theorem subd12_2_25 : subd12_2 [0, 2] = true := by decide +kernel
theorem subd12_2_26 : subd12_2 [0, 3] = true := by decide +kernel
theorem subd12_2_27 : subd12_2 [0, 4] = true := by decide +kernel
theorem subd12_2_28 : subd12_2 [1, -4] = true := by decide +kernel
theorem subd12_2_29 : subd12_2 [1, -3] = true := by decide +kernel
theorem subd12_2_30 : subd12_2 [1, -2] = true := by decide +kernel
theorem subd12_2_31 : subd12_2 [1, -1] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_cons.2 ⟨subd12_2_5, List.forall_mem_cons.2 ⟨subd12_2_6, List.forall_mem_cons.2 ⟨subd12_2_7, List.forall_mem_cons.2 ⟨subd12_2_8, List.forall_mem_cons.2 ⟨subd12_2_9, List.forall_mem_cons.2 ⟨subd12_2_10, List.forall_mem_cons.2 ⟨subd12_2_11, List.forall_mem_cons.2 ⟨subd12_2_12, List.forall_mem_cons.2 ⟨subd12_2_13, List.forall_mem_cons.2 ⟨subd12_2_14, List.forall_mem_cons.2 ⟨subd12_2_15, List.forall_mem_cons.2 ⟨subd12_2_16, List.forall_mem_cons.2 ⟨subd12_2_17, List.forall_mem_cons.2 ⟨subd12_2_18, List.forall_mem_cons.2 ⟨subd12_2_19, List.forall_mem_cons.2 ⟨subd12_2_20, List.forall_mem_cons.2 ⟨subd12_2_21, List.forall_mem_cons.2 ⟨subd12_2_22, List.forall_mem_cons.2 ⟨subd12_2_23, List.forall_mem_cons.2 ⟨subd12_2_24, List.forall_mem_cons.2 ⟨subd12_2_25, List.forall_mem_cons.2 ⟨subd12_2_26, List.forall_mem_cons.2 ⟨subd12_2_27, List.forall_mem_cons.2 ⟨subd12_2_28, List.forall_mem_cons.2 ⟨subd12_2_29, List.forall_mem_cons.2 ⟨subd12_2_30, List.forall_mem_cons.2 ⟨subd12_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_32 : subd12_2 [1, 0] = true := by decide +kernel
theorem subd12_2_33 : subd12_2 [1, 1] = true := by decide +kernel
theorem subd12_2_34 : subd12_2 [1, 2] = true := by decide +kernel
theorem subd12_2_35 : subd12_2 [1, 3] = true := by decide +kernel
theorem subd12_2_36 : subd12_2 [1, 4] = true := by decide +kernel
theorem subd12_2_37 : subd12_2 [2, -4] = true := by decide +kernel
theorem subd12_2_38 : subd12_2 [2, -3] = true := by decide +kernel
theorem subd12_2_39 : subd12_2 [2, -2] = true := by decide +kernel
theorem subd12_2_40 : subd12_2 [2, -1] = true := by decide +kernel
theorem subd12_2_41 : subd12_2 [2, 0] = true := by decide +kernel
theorem subd12_2_42 : subd12_2 [2, 1] = true := by decide +kernel
theorem subd12_2_43 : subd12_2 [2, 2] = true := by decide +kernel
theorem subd12_2_44 : subd12_2 [2, 3] = true := by decide +kernel
theorem subd12_2_45 : subd12_2 [3] = true := by decide +kernel
theorem sbd12_2_1 : ∀ q ∈ blkd12_2_1, subd12_2 q = true := by
  unfold blkd12_2_1
  exact List.forall_mem_cons.2 ⟨subd12_2_32, List.forall_mem_cons.2 ⟨subd12_2_33, List.forall_mem_cons.2 ⟨subd12_2_34, List.forall_mem_cons.2 ⟨subd12_2_35, List.forall_mem_cons.2 ⟨subd12_2_36, List.forall_mem_cons.2 ⟨subd12_2_37, List.forall_mem_cons.2 ⟨subd12_2_38, List.forall_mem_cons.2 ⟨subd12_2_39, List.forall_mem_cons.2 ⟨subd12_2_40, List.forall_mem_cons.2 ⟨subd12_2_41, List.forall_mem_cons.2 ⟨subd12_2_42, List.forall_mem_cons.2 ⟨subd12_2_43, List.forall_mem_cons.2 ⟨subd12_2_44, List.forall_mem_cons.2 ⟨subd12_2_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-2] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-1, -3] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [-1, -2] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [-1, -1] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [-1, 0] = true := by decide +kernel
theorem subd12_3_5 : subd12_3 [-1, 1] = true := by decide +kernel
theorem subd12_3_6 : subd12_3 [-1, 2] = true := by decide +kernel
theorem subd12_3_7 : subd12_3 [0, -3] = true := by decide +kernel
theorem subd12_3_8 : subd12_3 [0, -2] = true := by decide +kernel
theorem subd12_3_9 : subd12_3 [0, -1] = true := by decide +kernel
theorem subd12_3_10 : subd12_3 [0, 0] = true := by decide +kernel
theorem subd12_3_11 : subd12_3 [0, 1] = true := by decide +kernel
theorem subd12_3_12 : subd12_3 [0, 2] = true := by decide +kernel
theorem subd12_3_13 : subd12_3 [1, -3] = true := by decide +kernel
theorem subd12_3_14 : subd12_3 [1, -2] = true := by decide +kernel
theorem subd12_3_15 : subd12_3 [1, -1] = true := by decide +kernel
theorem subd12_3_16 : subd12_3 [1, 0] = true := by decide +kernel
theorem subd12_3_17 : subd12_3 [1, 1] = true := by decide +kernel
theorem subd12_3_18 : subd12_3 [1, 2] = true := by decide +kernel
theorem subd12_3_19 : subd12_3 [2] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_cons.2 ⟨subd12_3_5, List.forall_mem_cons.2 ⟨subd12_3_6, List.forall_mem_cons.2 ⟨subd12_3_7, List.forall_mem_cons.2 ⟨subd12_3_8, List.forall_mem_cons.2 ⟨subd12_3_9, List.forall_mem_cons.2 ⟨subd12_3_10, List.forall_mem_cons.2 ⟨subd12_3_11, List.forall_mem_cons.2 ⟨subd12_3_12, List.forall_mem_cons.2 ⟨subd12_3_13, List.forall_mem_cons.2 ⟨subd12_3_14, List.forall_mem_cons.2 ⟨subd12_3_15, List.forall_mem_cons.2 ⟨subd12_3_16, List.forall_mem_cons.2 ⟨subd12_3_17, List.forall_mem_cons.2 ⟨subd12_3_18, List.forall_mem_cons.2 ⟨subd12_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C133
