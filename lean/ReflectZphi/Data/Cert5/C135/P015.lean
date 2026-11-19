import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_4_32 : subd6_4 [-3, 1] = true := by decide +kernel
theorem subd6_4_33 : subd6_4 [-3, 2] = true := by decide +kernel
theorem subd6_4_34 : subd6_4 [-3, 3] = true := by decide +kernel
theorem subd6_4_35 : subd6_4 [-3, 4] = true := by decide +kernel
theorem subd6_4_36 : subd6_4 [-3, 5] = true := by decide +kernel
theorem subd6_4_37 : subd6_4 [-2, -8] = true := by decide +kernel
theorem subd6_4_38 : subd6_4 [-2, -7] = true := by decide +kernel
theorem subd6_4_39 : subd6_4 [-2, -6] = true := by decide +kernel
theorem subd6_4_40 : subd6_4 [-2, -5] = true := by decide +kernel
theorem subd6_4_41 : subd6_4 [-2, -4] = true := by decide +kernel
theorem subd6_4_42 : subd6_4 [-2, -3] = true := by decide +kernel
theorem subd6_4_43 : subd6_4 [-2, -2] = true := by decide +kernel
theorem subd6_4_44 : subd6_4 [-2, -1] = true := by decide +kernel
theorem subd6_4_45 : subd6_4 [-2, 0] = true := by decide +kernel
theorem subd6_4_46 : subd6_4 [-2, 1] = true := by decide +kernel
theorem subd6_4_47 : subd6_4 [-2, 2] = true := by decide +kernel
theorem subd6_4_48 : subd6_4 [-2, 3] = true := by decide +kernel
theorem subd6_4_49 : subd6_4 [-2, 4] = true := by decide +kernel
theorem subd6_4_50 : subd6_4 [-2, 5] = true := by decide +kernel
theorem subd6_4_51 : subd6_4 [-2, 6] = true := by decide +kernel
theorem subd6_4_52 : subd6_4 [-1, -8] = true := by decide +kernel
theorem subd6_4_53 : subd6_4 [-1, -7] = true := by decide +kernel
theorem subd6_4_54 : subd6_4 [-1, -6] = true := by decide +kernel
theorem subd6_4_55 : subd6_4 [-1, -5] = true := by decide +kernel
theorem subd6_4_56 : subd6_4 [-1, -4] = true := by decide +kernel
theorem subd6_4_57 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_58 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_59 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_60 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_61 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_62 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_63 : subd6_4 [-1, 3] = true := by decide +kernel
theorem sbd6_4_1 : ∀ q ∈ blkd6_4_1, subd6_4 q = true := by
  unfold blkd6_4_1
  exact List.forall_mem_cons.2 ⟨subd6_4_32, List.forall_mem_cons.2 ⟨subd6_4_33, List.forall_mem_cons.2 ⟨subd6_4_34, List.forall_mem_cons.2 ⟨subd6_4_35, List.forall_mem_cons.2 ⟨subd6_4_36, List.forall_mem_cons.2 ⟨subd6_4_37, List.forall_mem_cons.2 ⟨subd6_4_38, List.forall_mem_cons.2 ⟨subd6_4_39, List.forall_mem_cons.2 ⟨subd6_4_40, List.forall_mem_cons.2 ⟨subd6_4_41, List.forall_mem_cons.2 ⟨subd6_4_42, List.forall_mem_cons.2 ⟨subd6_4_43, List.forall_mem_cons.2 ⟨subd6_4_44, List.forall_mem_cons.2 ⟨subd6_4_45, List.forall_mem_cons.2 ⟨subd6_4_46, List.forall_mem_cons.2 ⟨subd6_4_47, List.forall_mem_cons.2 ⟨subd6_4_48, List.forall_mem_cons.2 ⟨subd6_4_49, List.forall_mem_cons.2 ⟨subd6_4_50, List.forall_mem_cons.2 ⟨subd6_4_51, List.forall_mem_cons.2 ⟨subd6_4_52, List.forall_mem_cons.2 ⟨subd6_4_53, List.forall_mem_cons.2 ⟨subd6_4_54, List.forall_mem_cons.2 ⟨subd6_4_55, List.forall_mem_cons.2 ⟨subd6_4_56, List.forall_mem_cons.2 ⟨subd6_4_57, List.forall_mem_cons.2 ⟨subd6_4_58, List.forall_mem_cons.2 ⟨subd6_4_59, List.forall_mem_cons.2 ⟨subd6_4_60, List.forall_mem_cons.2 ⟨subd6_4_61, List.forall_mem_cons.2 ⟨subd6_4_62, List.forall_mem_cons.2 ⟨subd6_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_64 : subd6_4 [-1, 4] = true := by decide +kernel
theorem subd6_4_65 : subd6_4 [-1, 5] = true := by decide +kernel
theorem subd6_4_66 : subd6_4 [-1, 6] = true := by decide +kernel
theorem subd6_4_67 : subd6_4 [0, -8] = true := by decide +kernel
theorem subd6_4_68 : subd6_4 [0, -7] = true := by decide +kernel
theorem subd6_4_69 : subd6_4 [0, -6] = true := by decide +kernel
theorem subd6_4_70 : subd6_4 [0, -5] = true := by decide +kernel
theorem subd6_4_71 : subd6_4 [0, -4] = true := by decide +kernel
theorem subd6_4_72 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_73 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_74 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_75 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_76 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_77 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_78 : subd6_4 [0, 3] = true := by decide +kernel
theorem subd6_4_79 : subd6_4 [0, 4] = true := by decide +kernel
theorem subd6_4_80 : subd6_4 [0, 5] = true := by decide +kernel
theorem subd6_4_81 : subd6_4 [0, 6] = true := by decide +kernel
theorem subd6_4_82 : subd6_4 [0, 7] = true := by decide +kernel
theorem subd6_4_83 : subd6_4 [1, -7] = true := by decide +kernel
theorem subd6_4_84 : subd6_4 [1, -6] = true := by decide +kernel
theorem subd6_4_85 : subd6_4 [1, -5] = true := by decide +kernel
theorem subd6_4_86 : subd6_4 [1, -4] = true := by decide +kernel
theorem subd6_4_87 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_88 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_89 : subd6_4 [1, -1] = true := by decide +kernel
theorem subd6_4_90 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_91 : subd6_4 [1, 1] = true := by decide +kernel
theorem subd6_4_92 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_93 : subd6_4 [1, 3] = true := by decide +kernel
theorem subd6_4_94 : subd6_4 [1, 4] = true := by decide +kernel
theorem subd6_4_95 : subd6_4 [1, 5] = true := by decide +kernel
theorem sbd6_4_2 : ∀ q ∈ blkd6_4_2, subd6_4 q = true := by
  unfold blkd6_4_2
  exact List.forall_mem_cons.2 ⟨subd6_4_64, List.forall_mem_cons.2 ⟨subd6_4_65, List.forall_mem_cons.2 ⟨subd6_4_66, List.forall_mem_cons.2 ⟨subd6_4_67, List.forall_mem_cons.2 ⟨subd6_4_68, List.forall_mem_cons.2 ⟨subd6_4_69, List.forall_mem_cons.2 ⟨subd6_4_70, List.forall_mem_cons.2 ⟨subd6_4_71, List.forall_mem_cons.2 ⟨subd6_4_72, List.forall_mem_cons.2 ⟨subd6_4_73, List.forall_mem_cons.2 ⟨subd6_4_74, List.forall_mem_cons.2 ⟨subd6_4_75, List.forall_mem_cons.2 ⟨subd6_4_76, List.forall_mem_cons.2 ⟨subd6_4_77, List.forall_mem_cons.2 ⟨subd6_4_78, List.forall_mem_cons.2 ⟨subd6_4_79, List.forall_mem_cons.2 ⟨subd6_4_80, List.forall_mem_cons.2 ⟨subd6_4_81, List.forall_mem_cons.2 ⟨subd6_4_82, List.forall_mem_cons.2 ⟨subd6_4_83, List.forall_mem_cons.2 ⟨subd6_4_84, List.forall_mem_cons.2 ⟨subd6_4_85, List.forall_mem_cons.2 ⟨subd6_4_86, List.forall_mem_cons.2 ⟨subd6_4_87, List.forall_mem_cons.2 ⟨subd6_4_88, List.forall_mem_cons.2 ⟨subd6_4_89, List.forall_mem_cons.2 ⟨subd6_4_90, List.forall_mem_cons.2 ⟨subd6_4_91, List.forall_mem_cons.2 ⟨subd6_4_92, List.forall_mem_cons.2 ⟨subd6_4_93, List.forall_mem_cons.2 ⟨subd6_4_94, List.forall_mem_cons.2 ⟨subd6_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_96 : subd6_4 [1, 6] = true := by decide +kernel
theorem subd6_4_97 : subd6_4 [1, 7] = true := by decide +kernel
theorem subd6_4_98 : subd6_4 [2, -7] = true := by decide +kernel
theorem subd6_4_99 : subd6_4 [2, -6] = true := by decide +kernel
theorem subd6_4_100 : subd6_4 [2, -5] = true := by decide +kernel
theorem subd6_4_101 : subd6_4 [2, -4] = true := by decide +kernel
theorem subd6_4_102 : subd6_4 [2, -3] = true := by decide +kernel
theorem subd6_4_103 : subd6_4 [2, -2] = true := by decide +kernel
theorem subd6_4_104 : subd6_4 [2, -1] = true := by decide +kernel
theorem subd6_4_105 : subd6_4 [2, 0] = true := by decide +kernel
theorem subd6_4_106 : subd6_4 [2, 1] = true := by decide +kernel
theorem subd6_4_107 : subd6_4 [2, 2] = true := by decide +kernel
theorem subd6_4_108 : subd6_4 [2, 3] = true := by decide +kernel
theorem subd6_4_109 : subd6_4 [2, 4] = true := by decide +kernel
theorem subd6_4_110 : subd6_4 [2, 5] = true := by decide +kernel
theorem subd6_4_111 : subd6_4 [2, 6] = true := by decide +kernel
theorem subd6_4_112 : subd6_4 [2, 7] = true := by decide +kernel
theorem subd6_4_113 : subd6_4 [3, -6] = true := by decide +kernel
theorem subd6_4_114 : subd6_4 [3, -5] = true := by decide +kernel
theorem subd6_4_115 : subd6_4 [3, -4] = true := by decide +kernel
theorem subd6_4_116 : subd6_4 [3, -3] = true := by decide +kernel
theorem subd6_4_117 : subd6_4 [3, -2] = true := by decide +kernel
theorem subd6_4_118 : subd6_4 [3, -1] = true := by decide +kernel
theorem subd6_4_119 : subd6_4 [3, 0] = true := by decide +kernel
theorem subd6_4_120 : subd6_4 [3, 1] = true := by decide +kernel
theorem subd6_4_121 : subd6_4 [3, 2] = true := by decide +kernel
theorem subd6_4_122 : subd6_4 [3, 3] = true := by decide +kernel
theorem subd6_4_123 : subd6_4 [3, 4] = true := by decide +kernel
theorem subd6_4_124 : subd6_4 [3, 5] = true := by decide +kernel
theorem subd6_4_125 : subd6_4 [3, 6] = true := by decide +kernel
theorem subd6_4_126 : subd6_4 [4, -6] = true := by decide +kernel
theorem subd6_4_127 : subd6_4 [4, -5] = true := by decide +kernel
theorem sbd6_4_3 : ∀ q ∈ blkd6_4_3, subd6_4 q = true := by
  unfold blkd6_4_3
  exact List.forall_mem_cons.2 ⟨subd6_4_96, List.forall_mem_cons.2 ⟨subd6_4_97, List.forall_mem_cons.2 ⟨subd6_4_98, List.forall_mem_cons.2 ⟨subd6_4_99, List.forall_mem_cons.2 ⟨subd6_4_100, List.forall_mem_cons.2 ⟨subd6_4_101, List.forall_mem_cons.2 ⟨subd6_4_102, List.forall_mem_cons.2 ⟨subd6_4_103, List.forall_mem_cons.2 ⟨subd6_4_104, List.forall_mem_cons.2 ⟨subd6_4_105, List.forall_mem_cons.2 ⟨subd6_4_106, List.forall_mem_cons.2 ⟨subd6_4_107, List.forall_mem_cons.2 ⟨subd6_4_108, List.forall_mem_cons.2 ⟨subd6_4_109, List.forall_mem_cons.2 ⟨subd6_4_110, List.forall_mem_cons.2 ⟨subd6_4_111, List.forall_mem_cons.2 ⟨subd6_4_112, List.forall_mem_cons.2 ⟨subd6_4_113, List.forall_mem_cons.2 ⟨subd6_4_114, List.forall_mem_cons.2 ⟨subd6_4_115, List.forall_mem_cons.2 ⟨subd6_4_116, List.forall_mem_cons.2 ⟨subd6_4_117, List.forall_mem_cons.2 ⟨subd6_4_118, List.forall_mem_cons.2 ⟨subd6_4_119, List.forall_mem_cons.2 ⟨subd6_4_120, List.forall_mem_cons.2 ⟨subd6_4_121, List.forall_mem_cons.2 ⟨subd6_4_122, List.forall_mem_cons.2 ⟨subd6_4_123, List.forall_mem_cons.2 ⟨subd6_4_124, List.forall_mem_cons.2 ⟨subd6_4_125, List.forall_mem_cons.2 ⟨subd6_4_126, List.forall_mem_cons.2 ⟨subd6_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
