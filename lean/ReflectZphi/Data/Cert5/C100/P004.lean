import ReflectZphi.Data.Cert5.C100.Base

namespace ReflectZphi.Data.Cert5.C100

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_32 : subd5_0 [-2, -3] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [-2, -2] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [-2, -1] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [-2, 0] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [-2, 1] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [-2, 2] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [-2, 3] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [-2, 4] = true := by decide +kernel
theorem subd5_0_40 : subd5_0 [-2, 5] = true := by decide +kernel
theorem subd5_0_41 : subd5_0 [-1, -7] = true := by decide +kernel
theorem subd5_0_42 : subd5_0 [-1, -6] = true := by decide +kernel
theorem subd5_0_43 : subd5_0 [-1, -5] = true := by decide +kernel
theorem subd5_0_44 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_45 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_46 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_47 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_48 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_49 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_50 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_51 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_52 : subd5_0 [-1, 4] = true := by decide +kernel
theorem subd5_0_53 : subd5_0 [-1, 5] = true := by decide +kernel
theorem subd5_0_54 : subd5_0 [0, -7] = true := by decide +kernel
theorem subd5_0_55 : subd5_0 [0, -6] = true := by decide +kernel
theorem subd5_0_56 : subd5_0 [0, -5] = true := by decide +kernel
theorem subd5_0_57 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_58 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_59 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_60 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_61 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_62 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_63 : subd5_0 [0, 2] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_cons.2 ⟨subd5_0_40, List.forall_mem_cons.2 ⟨subd5_0_41, List.forall_mem_cons.2 ⟨subd5_0_42, List.forall_mem_cons.2 ⟨subd5_0_43, List.forall_mem_cons.2 ⟨subd5_0_44, List.forall_mem_cons.2 ⟨subd5_0_45, List.forall_mem_cons.2 ⟨subd5_0_46, List.forall_mem_cons.2 ⟨subd5_0_47, List.forall_mem_cons.2 ⟨subd5_0_48, List.forall_mem_cons.2 ⟨subd5_0_49, List.forall_mem_cons.2 ⟨subd5_0_50, List.forall_mem_cons.2 ⟨subd5_0_51, List.forall_mem_cons.2 ⟨subd5_0_52, List.forall_mem_cons.2 ⟨subd5_0_53, List.forall_mem_cons.2 ⟨subd5_0_54, List.forall_mem_cons.2 ⟨subd5_0_55, List.forall_mem_cons.2 ⟨subd5_0_56, List.forall_mem_cons.2 ⟨subd5_0_57, List.forall_mem_cons.2 ⟨subd5_0_58, List.forall_mem_cons.2 ⟨subd5_0_59, List.forall_mem_cons.2 ⟨subd5_0_60, List.forall_mem_cons.2 ⟨subd5_0_61, List.forall_mem_cons.2 ⟨subd5_0_62, List.forall_mem_cons.2 ⟨subd5_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_64 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_65 : subd5_0 [0, 4] = true := by decide +kernel
theorem subd5_0_66 : subd5_0 [0, 5] = true := by decide +kernel
theorem subd5_0_67 : subd5_0 [0, 6] = true := by decide +kernel
theorem subd5_0_68 : subd5_0 [1, -6] = true := by decide +kernel
theorem subd5_0_69 : subd5_0 [1, -5] = true := by decide +kernel
theorem subd5_0_70 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_71 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_72 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_73 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_74 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_75 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_76 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_77 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_78 : subd5_0 [1, 4] = true := by decide +kernel
theorem subd5_0_79 : subd5_0 [1, 5] = true := by decide +kernel
theorem subd5_0_80 : subd5_0 [1, 6] = true := by decide +kernel
theorem subd5_0_81 : subd5_0 [2, -6] = true := by decide +kernel
theorem subd5_0_82 : subd5_0 [2, -5] = true := by decide +kernel
theorem subd5_0_83 : subd5_0 [2, -4] = true := by decide +kernel
theorem subd5_0_84 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_85 : subd5_0 [2, -2] = true := by decide +kernel
theorem subd5_0_86 : subd5_0 [2, -1] = true := by decide +kernel
theorem subd5_0_87 : subd5_0 [2, 0] = true := by decide +kernel
theorem subd5_0_88 : subd5_0 [2, 1] = true := by decide +kernel
theorem subd5_0_89 : subd5_0 [2, 2] = true := by decide +kernel
theorem subd5_0_90 : subd5_0 [2, 3] = true := by decide +kernel
theorem subd5_0_91 : subd5_0 [2, 4] = true := by decide +kernel
theorem subd5_0_92 : subd5_0 [2, 5] = true := by decide +kernel
theorem subd5_0_93 : subd5_0 [2, 6] = true := by decide +kernel
theorem subd5_0_94 : subd5_0 [3, -5] = true := by decide +kernel
theorem subd5_0_95 : subd5_0 [3, -4] = true := by decide +kernel
theorem sbd5_0_2 : ∀ q ∈ blkd5_0_2, subd5_0 q = true := by
  unfold blkd5_0_2
  exact List.forall_mem_cons.2 ⟨subd5_0_64, List.forall_mem_cons.2 ⟨subd5_0_65, List.forall_mem_cons.2 ⟨subd5_0_66, List.forall_mem_cons.2 ⟨subd5_0_67, List.forall_mem_cons.2 ⟨subd5_0_68, List.forall_mem_cons.2 ⟨subd5_0_69, List.forall_mem_cons.2 ⟨subd5_0_70, List.forall_mem_cons.2 ⟨subd5_0_71, List.forall_mem_cons.2 ⟨subd5_0_72, List.forall_mem_cons.2 ⟨subd5_0_73, List.forall_mem_cons.2 ⟨subd5_0_74, List.forall_mem_cons.2 ⟨subd5_0_75, List.forall_mem_cons.2 ⟨subd5_0_76, List.forall_mem_cons.2 ⟨subd5_0_77, List.forall_mem_cons.2 ⟨subd5_0_78, List.forall_mem_cons.2 ⟨subd5_0_79, List.forall_mem_cons.2 ⟨subd5_0_80, List.forall_mem_cons.2 ⟨subd5_0_81, List.forall_mem_cons.2 ⟨subd5_0_82, List.forall_mem_cons.2 ⟨subd5_0_83, List.forall_mem_cons.2 ⟨subd5_0_84, List.forall_mem_cons.2 ⟨subd5_0_85, List.forall_mem_cons.2 ⟨subd5_0_86, List.forall_mem_cons.2 ⟨subd5_0_87, List.forall_mem_cons.2 ⟨subd5_0_88, List.forall_mem_cons.2 ⟨subd5_0_89, List.forall_mem_cons.2 ⟨subd5_0_90, List.forall_mem_cons.2 ⟨subd5_0_91, List.forall_mem_cons.2 ⟨subd5_0_92, List.forall_mem_cons.2 ⟨subd5_0_93, List.forall_mem_cons.2 ⟨subd5_0_94, List.forall_mem_cons.2 ⟨subd5_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_96 : subd5_0 [3, -3] = true := by decide +kernel
theorem subd5_0_97 : subd5_0 [3, -2] = true := by decide +kernel
theorem subd5_0_98 : subd5_0 [3, -1] = true := by decide +kernel
theorem subd5_0_99 : subd5_0 [3, 0] = true := by decide +kernel
theorem subd5_0_100 : subd5_0 [3, 1] = true := by decide +kernel
theorem subd5_0_101 : subd5_0 [3, 2] = true := by decide +kernel
theorem subd5_0_102 : subd5_0 [3, 3] = true := by decide +kernel
theorem subd5_0_103 : subd5_0 [3, 4] = true := by decide +kernel
theorem subd5_0_104 : subd5_0 [3, 5] = true := by decide +kernel
theorem subd5_0_105 : subd5_0 [4, -4] = true := by decide +kernel
theorem subd5_0_106 : subd5_0 [4, -3] = true := by decide +kernel
theorem subd5_0_107 : subd5_0 [4, -2] = true := by decide +kernel
theorem subd5_0_108 : subd5_0 [4, -1] = true := by decide +kernel
theorem subd5_0_109 : subd5_0 [4, 0] = true := by decide +kernel
theorem subd5_0_110 : subd5_0 [4, 1] = true := by decide +kernel
theorem subd5_0_111 : subd5_0 [4, 2] = true := by decide +kernel
theorem subd5_0_112 : subd5_0 [4, 3] = true := by decide +kernel
theorem subd5_0_113 : subd5_0 [4, 4] = true := by decide +kernel
theorem subd5_0_114 : subd5_0 [4, 5] = true := by decide +kernel
theorem subd5_0_115 : subd5_0 [5, -3] = true := by decide +kernel
theorem subd5_0_116 : subd5_0 [5, -2] = true := by decide +kernel
theorem subd5_0_117 : subd5_0 [5, -1] = true := by decide +kernel
theorem subd5_0_118 : subd5_0 [5, 0] = true := by decide +kernel
theorem subd5_0_119 : subd5_0 [5, 1] = true := by decide +kernel
theorem subd5_0_120 : subd5_0 [5, 2] = true := by decide +kernel
theorem subd5_0_121 : subd5_0 [5, 3] = true := by decide +kernel
theorem sbd5_0_3 : ∀ q ∈ blkd5_0_3, subd5_0 q = true := by
  unfold blkd5_0_3
  exact List.forall_mem_cons.2 ⟨subd5_0_96, List.forall_mem_cons.2 ⟨subd5_0_97, List.forall_mem_cons.2 ⟨subd5_0_98, List.forall_mem_cons.2 ⟨subd5_0_99, List.forall_mem_cons.2 ⟨subd5_0_100, List.forall_mem_cons.2 ⟨subd5_0_101, List.forall_mem_cons.2 ⟨subd5_0_102, List.forall_mem_cons.2 ⟨subd5_0_103, List.forall_mem_cons.2 ⟨subd5_0_104, List.forall_mem_cons.2 ⟨subd5_0_105, List.forall_mem_cons.2 ⟨subd5_0_106, List.forall_mem_cons.2 ⟨subd5_0_107, List.forall_mem_cons.2 ⟨subd5_0_108, List.forall_mem_cons.2 ⟨subd5_0_109, List.forall_mem_cons.2 ⟨subd5_0_110, List.forall_mem_cons.2 ⟨subd5_0_111, List.forall_mem_cons.2 ⟨subd5_0_112, List.forall_mem_cons.2 ⟨subd5_0_113, List.forall_mem_cons.2 ⟨subd5_0_114, List.forall_mem_cons.2 ⟨subd5_0_115, List.forall_mem_cons.2 ⟨subd5_0_116, List.forall_mem_cons.2 ⟨subd5_0_117, List.forall_mem_cons.2 ⟨subd5_0_118, List.forall_mem_cons.2 ⟨subd5_0_119, List.forall_mem_cons.2 ⟨subd5_0_120, List.forall_mem_cons.2 ⟨subd5_0_121, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [0, 0, -8] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [0, 0, -7] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [0, 0, -6] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [0, 0, -5] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [0, 0, -4] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [0, 0, -3] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [0, 0, -2] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [0, 0, -1] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [0, 0, 0] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [0, 0, 1] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [0, 0, 2] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [0, 0, 3] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [0, 0, 4] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [0, 0, 5] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [0, 0, 6] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [0, 0, 7] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [1, 2] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C100
