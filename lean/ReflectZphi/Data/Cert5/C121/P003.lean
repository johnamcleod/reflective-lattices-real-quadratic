import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_2_0 : subd3_2 [-6] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-5, -4] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-5, -3] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-5, -2] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-5, -1] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-5, 0] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-5, 1] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [-5, 2] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [-5, 3] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [-5, 4] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [-5, 5] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [-4, -5] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [-4, -4] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [-4, -3] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [-4, -2] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [-4, -1] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [-4, 0] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [-4, 1] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [-4, 2] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [-4, 3] = true := by decide +kernel
theorem subd3_2_20 : subd3_2 [-4, 4] = true := by decide +kernel
theorem subd3_2_21 : subd3_2 [-4, 5] = true := by decide +kernel
theorem subd3_2_22 : subd3_2 [-4, 6] = true := by decide +kernel
theorem subd3_2_23 : subd3_2 [-3, -6] = true := by decide +kernel
theorem subd3_2_24 : subd3_2 [-3, -5] = true := by decide +kernel
theorem subd3_2_25 : subd3_2 [-3, -4] = true := by decide +kernel
theorem subd3_2_26 : subd3_2 [-3, -3] = true := by decide +kernel
theorem subd3_2_27 : subd3_2 [-3, -2] = true := by decide +kernel
theorem subd3_2_28 : subd3_2 [-3, -1] = true := by decide +kernel
theorem subd3_2_29 : subd3_2 [-3, 0] = true := by decide +kernel
theorem subd3_2_30 : subd3_2 [-3, 1] = true := by decide +kernel
theorem subd3_2_31 : subd3_2 [-3, 2] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_cons.2 ⟨subd3_2_20, List.forall_mem_cons.2 ⟨subd3_2_21, List.forall_mem_cons.2 ⟨subd3_2_22, List.forall_mem_cons.2 ⟨subd3_2_23, List.forall_mem_cons.2 ⟨subd3_2_24, List.forall_mem_cons.2 ⟨subd3_2_25, List.forall_mem_cons.2 ⟨subd3_2_26, List.forall_mem_cons.2 ⟨subd3_2_27, List.forall_mem_cons.2 ⟨subd3_2_28, List.forall_mem_cons.2 ⟨subd3_2_29, List.forall_mem_cons.2 ⟨subd3_2_30, List.forall_mem_cons.2 ⟨subd3_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_2_32 : subd3_2 [-3, 3] = true := by decide +kernel
theorem subd3_2_33 : subd3_2 [-3, 4] = true := by decide +kernel
theorem subd3_2_34 : subd3_2 [-3, 5] = true := by decide +kernel
theorem subd3_2_35 : subd3_2 [-3, 6] = true := by decide +kernel
theorem subd3_2_36 : subd3_2 [-2, -7] = true := by decide +kernel
theorem subd3_2_37 : subd3_2 [-2, -6] = true := by decide +kernel
theorem subd3_2_38 : subd3_2 [-2, -5] = true := by decide +kernel
theorem subd3_2_39 : subd3_2 [-2, -4] = true := by decide +kernel
theorem subd3_2_40 : subd3_2 [-2, -3] = true := by decide +kernel
theorem subd3_2_41 : subd3_2 [-2, -2] = true := by decide +kernel
theorem subd3_2_42 : subd3_2 [-2, -1] = true := by decide +kernel
theorem subd3_2_43 : subd3_2 [-2, 0] = true := by decide +kernel
theorem subd3_2_44 : subd3_2 [-2, 1] = true := by decide +kernel
theorem subd3_2_45 : subd3_2 [-2, 2] = true := by decide +kernel
theorem subd3_2_46 : subd3_2 [-2, 3] = true := by decide +kernel
theorem subd3_2_47 : subd3_2 [-2, 4] = true := by decide +kernel
theorem subd3_2_48 : subd3_2 [-2, 5] = true := by decide +kernel
theorem subd3_2_49 : subd3_2 [-2, 6] = true := by decide +kernel
theorem subd3_2_50 : subd3_2 [-2, 7] = true := by decide +kernel
theorem subd3_2_51 : subd3_2 [-1, -7] = true := by decide +kernel
theorem subd3_2_52 : subd3_2 [-1, -6] = true := by decide +kernel
theorem subd3_2_53 : subd3_2 [-1, -5] = true := by decide +kernel
theorem subd3_2_54 : subd3_2 [-1, -4] = true := by decide +kernel
theorem subd3_2_55 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_56 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_57 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_58 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_59 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_60 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_61 : subd3_2 [-1, 3] = true := by decide +kernel
theorem subd3_2_62 : subd3_2 [-1, 4] = true := by decide +kernel
theorem subd3_2_63 : subd3_2 [-1, 5] = true := by decide +kernel
theorem sbd3_2_1 : ∀ q ∈ blkd3_2_1, subd3_2 q = true := by
  unfold blkd3_2_1
  exact List.forall_mem_cons.2 ⟨subd3_2_32, List.forall_mem_cons.2 ⟨subd3_2_33, List.forall_mem_cons.2 ⟨subd3_2_34, List.forall_mem_cons.2 ⟨subd3_2_35, List.forall_mem_cons.2 ⟨subd3_2_36, List.forall_mem_cons.2 ⟨subd3_2_37, List.forall_mem_cons.2 ⟨subd3_2_38, List.forall_mem_cons.2 ⟨subd3_2_39, List.forall_mem_cons.2 ⟨subd3_2_40, List.forall_mem_cons.2 ⟨subd3_2_41, List.forall_mem_cons.2 ⟨subd3_2_42, List.forall_mem_cons.2 ⟨subd3_2_43, List.forall_mem_cons.2 ⟨subd3_2_44, List.forall_mem_cons.2 ⟨subd3_2_45, List.forall_mem_cons.2 ⟨subd3_2_46, List.forall_mem_cons.2 ⟨subd3_2_47, List.forall_mem_cons.2 ⟨subd3_2_48, List.forall_mem_cons.2 ⟨subd3_2_49, List.forall_mem_cons.2 ⟨subd3_2_50, List.forall_mem_cons.2 ⟨subd3_2_51, List.forall_mem_cons.2 ⟨subd3_2_52, List.forall_mem_cons.2 ⟨subd3_2_53, List.forall_mem_cons.2 ⟨subd3_2_54, List.forall_mem_cons.2 ⟨subd3_2_55, List.forall_mem_cons.2 ⟨subd3_2_56, List.forall_mem_cons.2 ⟨subd3_2_57, List.forall_mem_cons.2 ⟨subd3_2_58, List.forall_mem_cons.2 ⟨subd3_2_59, List.forall_mem_cons.2 ⟨subd3_2_60, List.forall_mem_cons.2 ⟨subd3_2_61, List.forall_mem_cons.2 ⟨subd3_2_62, List.forall_mem_cons.2 ⟨subd3_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_2_64 : subd3_2 [-1, 6] = true := by decide +kernel
theorem subd3_2_65 : subd3_2 [-1, 7] = true := by decide +kernel
theorem subd3_2_66 : subd3_2 [0, -8] = true := by decide +kernel
theorem subd3_2_67 : subd3_2 [0, -7] = true := by decide +kernel
theorem subd3_2_68 : subd3_2 [0, -6] = true := by decide +kernel
theorem subd3_2_69 : subd3_2 [0, -5] = true := by decide +kernel
theorem subd3_2_70 : subd3_2 [0, -4] = true := by decide +kernel
theorem subd3_2_71 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_72 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_73 : subd3_2 [0, -1] = true := by decide +kernel
theorem subd3_2_74 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_75 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_76 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_77 : subd3_2 [0, 3] = true := by decide +kernel
theorem subd3_2_78 : subd3_2 [0, 4] = true := by decide +kernel
theorem subd3_2_79 : subd3_2 [0, 5] = true := by decide +kernel
theorem subd3_2_80 : subd3_2 [0, 6] = true := by decide +kernel
theorem subd3_2_81 : subd3_2 [0, 7] = true := by decide +kernel
theorem subd3_2_82 : subd3_2 [1, -8] = true := by decide +kernel
theorem subd3_2_83 : subd3_2 [1, -7] = true := by decide +kernel
theorem subd3_2_84 : subd3_2 [1, -6] = true := by decide +kernel
theorem subd3_2_85 : subd3_2 [1, -5] = true := by decide +kernel
theorem subd3_2_86 : subd3_2 [1, -4] = true := by decide +kernel
theorem subd3_2_87 : subd3_2 [1, -3] = true := by decide +kernel
theorem subd3_2_88 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_89 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_90 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_91 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_92 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_93 : subd3_2 [1, 3] = true := by decide +kernel
theorem subd3_2_94 : subd3_2 [1, 4] = true := by decide +kernel
theorem subd3_2_95 : subd3_2 [1, 5] = true := by decide +kernel
theorem sbd3_2_2 : ∀ q ∈ blkd3_2_2, subd3_2 q = true := by
  unfold blkd3_2_2
  exact List.forall_mem_cons.2 ⟨subd3_2_64, List.forall_mem_cons.2 ⟨subd3_2_65, List.forall_mem_cons.2 ⟨subd3_2_66, List.forall_mem_cons.2 ⟨subd3_2_67, List.forall_mem_cons.2 ⟨subd3_2_68, List.forall_mem_cons.2 ⟨subd3_2_69, List.forall_mem_cons.2 ⟨subd3_2_70, List.forall_mem_cons.2 ⟨subd3_2_71, List.forall_mem_cons.2 ⟨subd3_2_72, List.forall_mem_cons.2 ⟨subd3_2_73, List.forall_mem_cons.2 ⟨subd3_2_74, List.forall_mem_cons.2 ⟨subd3_2_75, List.forall_mem_cons.2 ⟨subd3_2_76, List.forall_mem_cons.2 ⟨subd3_2_77, List.forall_mem_cons.2 ⟨subd3_2_78, List.forall_mem_cons.2 ⟨subd3_2_79, List.forall_mem_cons.2 ⟨subd3_2_80, List.forall_mem_cons.2 ⟨subd3_2_81, List.forall_mem_cons.2 ⟨subd3_2_82, List.forall_mem_cons.2 ⟨subd3_2_83, List.forall_mem_cons.2 ⟨subd3_2_84, List.forall_mem_cons.2 ⟨subd3_2_85, List.forall_mem_cons.2 ⟨subd3_2_86, List.forall_mem_cons.2 ⟨subd3_2_87, List.forall_mem_cons.2 ⟨subd3_2_88, List.forall_mem_cons.2 ⟨subd3_2_89, List.forall_mem_cons.2 ⟨subd3_2_90, List.forall_mem_cons.2 ⟨subd3_2_91, List.forall_mem_cons.2 ⟨subd3_2_92, List.forall_mem_cons.2 ⟨subd3_2_93, List.forall_mem_cons.2 ⟨subd3_2_94, List.forall_mem_cons.2 ⟨subd3_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_2_96 : subd3_2 [1, 6] = true := by decide +kernel
theorem subd3_2_97 : subd3_2 [2, -8] = true := by decide +kernel
theorem subd3_2_98 : subd3_2 [2, -7] = true := by decide +kernel
theorem subd3_2_99 : subd3_2 [2, -6] = true := by decide +kernel
theorem subd3_2_100 : subd3_2 [2, -5] = true := by decide +kernel
theorem subd3_2_101 : subd3_2 [2, -4] = true := by decide +kernel
theorem subd3_2_102 : subd3_2 [2, -3] = true := by decide +kernel
theorem subd3_2_103 : subd3_2 [2, -2] = true := by decide +kernel
theorem subd3_2_104 : subd3_2 [2, -1] = true := by decide +kernel
theorem subd3_2_105 : subd3_2 [2, 0] = true := by decide +kernel
theorem subd3_2_106 : subd3_2 [2, 1] = true := by decide +kernel
theorem subd3_2_107 : subd3_2 [2, 2] = true := by decide +kernel
theorem subd3_2_108 : subd3_2 [2, 3] = true := by decide +kernel
theorem subd3_2_109 : subd3_2 [2, 4] = true := by decide +kernel
theorem subd3_2_110 : subd3_2 [2, 5] = true := by decide +kernel
theorem subd3_2_111 : subd3_2 [2, 6] = true := by decide +kernel
theorem subd3_2_112 : subd3_2 [3, -7] = true := by decide +kernel
theorem subd3_2_113 : subd3_2 [3, -6] = true := by decide +kernel
theorem subd3_2_114 : subd3_2 [3, -5] = true := by decide +kernel
theorem subd3_2_115 : subd3_2 [3, -4] = true := by decide +kernel
theorem subd3_2_116 : subd3_2 [3, -3] = true := by decide +kernel
theorem subd3_2_117 : subd3_2 [3, -2] = true := by decide +kernel
theorem subd3_2_118 : subd3_2 [3, -1] = true := by decide +kernel
theorem subd3_2_119 : subd3_2 [3, 0] = true := by decide +kernel
theorem subd3_2_120 : subd3_2 [3, 1] = true := by decide +kernel
theorem subd3_2_121 : subd3_2 [3, 2] = true := by decide +kernel
theorem subd3_2_122 : subd3_2 [3, 3] = true := by decide +kernel
theorem subd3_2_123 : subd3_2 [3, 4] = true := by decide +kernel
theorem subd3_2_124 : subd3_2 [3, 5] = true := by decide +kernel
theorem subd3_2_125 : subd3_2 [4, -7] = true := by decide +kernel
theorem subd3_2_126 : subd3_2 [4, -6] = true := by decide +kernel
theorem subd3_2_127 : subd3_2 [4, -5] = true := by decide +kernel
theorem sbd3_2_3 : ∀ q ∈ blkd3_2_3, subd3_2 q = true := by
  unfold blkd3_2_3
  exact List.forall_mem_cons.2 ⟨subd3_2_96, List.forall_mem_cons.2 ⟨subd3_2_97, List.forall_mem_cons.2 ⟨subd3_2_98, List.forall_mem_cons.2 ⟨subd3_2_99, List.forall_mem_cons.2 ⟨subd3_2_100, List.forall_mem_cons.2 ⟨subd3_2_101, List.forall_mem_cons.2 ⟨subd3_2_102, List.forall_mem_cons.2 ⟨subd3_2_103, List.forall_mem_cons.2 ⟨subd3_2_104, List.forall_mem_cons.2 ⟨subd3_2_105, List.forall_mem_cons.2 ⟨subd3_2_106, List.forall_mem_cons.2 ⟨subd3_2_107, List.forall_mem_cons.2 ⟨subd3_2_108, List.forall_mem_cons.2 ⟨subd3_2_109, List.forall_mem_cons.2 ⟨subd3_2_110, List.forall_mem_cons.2 ⟨subd3_2_111, List.forall_mem_cons.2 ⟨subd3_2_112, List.forall_mem_cons.2 ⟨subd3_2_113, List.forall_mem_cons.2 ⟨subd3_2_114, List.forall_mem_cons.2 ⟨subd3_2_115, List.forall_mem_cons.2 ⟨subd3_2_116, List.forall_mem_cons.2 ⟨subd3_2_117, List.forall_mem_cons.2 ⟨subd3_2_118, List.forall_mem_cons.2 ⟨subd3_2_119, List.forall_mem_cons.2 ⟨subd3_2_120, List.forall_mem_cons.2 ⟨subd3_2_121, List.forall_mem_cons.2 ⟨subd3_2_122, List.forall_mem_cons.2 ⟨subd3_2_123, List.forall_mem_cons.2 ⟨subd3_2_124, List.forall_mem_cons.2 ⟨subd3_2_125, List.forall_mem_cons.2 ⟨subd3_2_126, List.forall_mem_cons.2 ⟨subd3_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
