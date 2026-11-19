import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_0_32 : subd13_0 [-2, -4] = true := by decide +kernel
theorem subd13_0_33 : subd13_0 [-2, -3] = true := by decide +kernel
theorem subd13_0_34 : subd13_0 [-2, -2] = true := by decide +kernel
theorem subd13_0_35 : subd13_0 [-2, -1] = true := by decide +kernel
theorem subd13_0_36 : subd13_0 [-2, 0] = true := by decide +kernel
theorem subd13_0_37 : subd13_0 [-2, 1] = true := by decide +kernel
theorem subd13_0_38 : subd13_0 [-2, 2] = true := by decide +kernel
theorem subd13_0_39 : subd13_0 [-2, 3] = true := by decide +kernel
theorem subd13_0_40 : subd13_0 [-2, 4] = true := by decide +kernel
theorem subd13_0_41 : subd13_0 [-2, 5] = true := by decide +kernel
theorem subd13_0_42 : subd13_0 [-2, 6] = true := by decide +kernel
theorem subd13_0_43 : subd13_0 [-1, -6] = true := by decide +kernel
theorem subd13_0_44 : subd13_0 [-1, -5] = true := by decide +kernel
theorem subd13_0_45 : subd13_0 [-1, -4] = true := by decide +kernel
theorem subd13_0_46 : subd13_0 [-1, -3] = true := by decide +kernel
theorem subd13_0_47 : subd13_0 [-1, -2] = true := by decide +kernel
theorem subd13_0_48 : subd13_0 [-1, -1] = true := by decide +kernel
theorem subd13_0_49 : subd13_0 [-1, 0] = true := by decide +kernel
theorem subd13_0_50 : subd13_0 [-1, 1] = true := by decide +kernel
theorem subd13_0_51 : subd13_0 [-1, 2] = true := by decide +kernel
theorem subd13_0_52 : subd13_0 [-1, 3] = true := by decide +kernel
theorem subd13_0_53 : subd13_0 [-1, 4] = true := by decide +kernel
theorem subd13_0_54 : subd13_0 [-1, 5] = true := by decide +kernel
theorem subd13_0_55 : subd13_0 [-1, 6] = true := by decide +kernel
theorem subd13_0_56 : subd13_0 [0, -6] = true := by decide +kernel
theorem subd13_0_57 : subd13_0 [0, -5] = true := by decide +kernel
theorem subd13_0_58 : subd13_0 [0, -4] = true := by decide +kernel
theorem subd13_0_59 : subd13_0 [0, -3] = true := by decide +kernel
theorem subd13_0_60 : subd13_0 [0, -2] = true := by decide +kernel
theorem subd13_0_61 : subd13_0 [0, -1] = true := by decide +kernel
theorem subd13_0_62 : subd13_0 [0, 0] = true := by decide +kernel
theorem subd13_0_63 : subd13_0 [0, 1] = true := by decide +kernel
theorem sbd13_0_1 : ∀ q ∈ blkd13_0_1, subd13_0 q = true := by
  unfold blkd13_0_1
  exact List.forall_mem_cons.2 ⟨subd13_0_32, List.forall_mem_cons.2 ⟨subd13_0_33, List.forall_mem_cons.2 ⟨subd13_0_34, List.forall_mem_cons.2 ⟨subd13_0_35, List.forall_mem_cons.2 ⟨subd13_0_36, List.forall_mem_cons.2 ⟨subd13_0_37, List.forall_mem_cons.2 ⟨subd13_0_38, List.forall_mem_cons.2 ⟨subd13_0_39, List.forall_mem_cons.2 ⟨subd13_0_40, List.forall_mem_cons.2 ⟨subd13_0_41, List.forall_mem_cons.2 ⟨subd13_0_42, List.forall_mem_cons.2 ⟨subd13_0_43, List.forall_mem_cons.2 ⟨subd13_0_44, List.forall_mem_cons.2 ⟨subd13_0_45, List.forall_mem_cons.2 ⟨subd13_0_46, List.forall_mem_cons.2 ⟨subd13_0_47, List.forall_mem_cons.2 ⟨subd13_0_48, List.forall_mem_cons.2 ⟨subd13_0_49, List.forall_mem_cons.2 ⟨subd13_0_50, List.forall_mem_cons.2 ⟨subd13_0_51, List.forall_mem_cons.2 ⟨subd13_0_52, List.forall_mem_cons.2 ⟨subd13_0_53, List.forall_mem_cons.2 ⟨subd13_0_54, List.forall_mem_cons.2 ⟨subd13_0_55, List.forall_mem_cons.2 ⟨subd13_0_56, List.forall_mem_cons.2 ⟨subd13_0_57, List.forall_mem_cons.2 ⟨subd13_0_58, List.forall_mem_cons.2 ⟨subd13_0_59, List.forall_mem_cons.2 ⟨subd13_0_60, List.forall_mem_cons.2 ⟨subd13_0_61, List.forall_mem_cons.2 ⟨subd13_0_62, List.forall_mem_cons.2 ⟨subd13_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_64 : subd13_0 [0, 2] = true := by decide +kernel
theorem subd13_0_65 : subd13_0 [0, 3] = true := by decide +kernel
theorem subd13_0_66 : subd13_0 [0, 4] = true := by decide +kernel
theorem subd13_0_67 : subd13_0 [0, 5] = true := by decide +kernel
theorem subd13_0_68 : subd13_0 [1, -7] = true := by decide +kernel
theorem subd13_0_69 : subd13_0 [1, -6] = true := by decide +kernel
theorem subd13_0_70 : subd13_0 [1, -5] = true := by decide +kernel
theorem subd13_0_71 : subd13_0 [1, -4] = true := by decide +kernel
theorem subd13_0_72 : subd13_0 [1, -3] = true := by decide +kernel
theorem subd13_0_73 : subd13_0 [1, -2] = true := by decide +kernel
theorem subd13_0_74 : subd13_0 [1, -1] = true := by decide +kernel
theorem subd13_0_75 : subd13_0 [1, 0] = true := by decide +kernel
theorem subd13_0_76 : subd13_0 [1, 1] = true := by decide +kernel
theorem subd13_0_77 : subd13_0 [1, 2] = true := by decide +kernel
theorem subd13_0_78 : subd13_0 [1, 3] = true := by decide +kernel
theorem subd13_0_79 : subd13_0 [1, 4] = true := by decide +kernel
theorem subd13_0_80 : subd13_0 [1, 5] = true := by decide +kernel
theorem subd13_0_81 : subd13_0 [2, -7] = true := by decide +kernel
theorem subd13_0_82 : subd13_0 [2, -6] = true := by decide +kernel
theorem subd13_0_83 : subd13_0 [2, -5] = true := by decide +kernel
theorem subd13_0_84 : subd13_0 [2, -4] = true := by decide +kernel
theorem subd13_0_85 : subd13_0 [2, -3] = true := by decide +kernel
theorem subd13_0_86 : subd13_0 [2, -2] = true := by decide +kernel
theorem subd13_0_87 : subd13_0 [2, -1] = true := by decide +kernel
theorem subd13_0_88 : subd13_0 [2, 0] = true := by decide +kernel
theorem subd13_0_89 : subd13_0 [2, 1] = true := by decide +kernel
theorem subd13_0_90 : subd13_0 [2, 2] = true := by decide +kernel
theorem subd13_0_91 : subd13_0 [2, 3] = true := by decide +kernel
theorem subd13_0_92 : subd13_0 [2, 4] = true := by decide +kernel
theorem subd13_0_93 : subd13_0 [3, -7] = true := by decide +kernel
theorem subd13_0_94 : subd13_0 [3, -6] = true := by decide +kernel
theorem subd13_0_95 : subd13_0 [3, -5] = true := by decide +kernel
theorem sbd13_0_2 : ∀ q ∈ blkd13_0_2, subd13_0 q = true := by
  unfold blkd13_0_2
  exact List.forall_mem_cons.2 ⟨subd13_0_64, List.forall_mem_cons.2 ⟨subd13_0_65, List.forall_mem_cons.2 ⟨subd13_0_66, List.forall_mem_cons.2 ⟨subd13_0_67, List.forall_mem_cons.2 ⟨subd13_0_68, List.forall_mem_cons.2 ⟨subd13_0_69, List.forall_mem_cons.2 ⟨subd13_0_70, List.forall_mem_cons.2 ⟨subd13_0_71, List.forall_mem_cons.2 ⟨subd13_0_72, List.forall_mem_cons.2 ⟨subd13_0_73, List.forall_mem_cons.2 ⟨subd13_0_74, List.forall_mem_cons.2 ⟨subd13_0_75, List.forall_mem_cons.2 ⟨subd13_0_76, List.forall_mem_cons.2 ⟨subd13_0_77, List.forall_mem_cons.2 ⟨subd13_0_78, List.forall_mem_cons.2 ⟨subd13_0_79, List.forall_mem_cons.2 ⟨subd13_0_80, List.forall_mem_cons.2 ⟨subd13_0_81, List.forall_mem_cons.2 ⟨subd13_0_82, List.forall_mem_cons.2 ⟨subd13_0_83, List.forall_mem_cons.2 ⟨subd13_0_84, List.forall_mem_cons.2 ⟨subd13_0_85, List.forall_mem_cons.2 ⟨subd13_0_86, List.forall_mem_cons.2 ⟨subd13_0_87, List.forall_mem_cons.2 ⟨subd13_0_88, List.forall_mem_cons.2 ⟨subd13_0_89, List.forall_mem_cons.2 ⟨subd13_0_90, List.forall_mem_cons.2 ⟨subd13_0_91, List.forall_mem_cons.2 ⟨subd13_0_92, List.forall_mem_cons.2 ⟨subd13_0_93, List.forall_mem_cons.2 ⟨subd13_0_94, List.forall_mem_cons.2 ⟨subd13_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_96 : subd13_0 [3, -4] = true := by decide +kernel
theorem subd13_0_97 : subd13_0 [3, -3] = true := by decide +kernel
theorem subd13_0_98 : subd13_0 [3, -2] = true := by decide +kernel
theorem subd13_0_99 : subd13_0 [3, -1] = true := by decide +kernel
theorem subd13_0_100 : subd13_0 [3, 0] = true := by decide +kernel
theorem subd13_0_101 : subd13_0 [3, 1] = true := by decide +kernel
theorem subd13_0_102 : subd13_0 [3, 2] = true := by decide +kernel
theorem subd13_0_103 : subd13_0 [3, 3] = true := by decide +kernel
theorem subd13_0_104 : subd13_0 [3, 4] = true := by decide +kernel
theorem subd13_0_105 : subd13_0 [4, -6] = true := by decide +kernel
theorem subd13_0_106 : subd13_0 [4, -5] = true := by decide +kernel
theorem subd13_0_107 : subd13_0 [4, -4] = true := by decide +kernel
theorem subd13_0_108 : subd13_0 [4, -3] = true := by decide +kernel
theorem subd13_0_109 : subd13_0 [4, -2] = true := by decide +kernel
theorem subd13_0_110 : subd13_0 [4, -1] = true := by decide +kernel
theorem subd13_0_111 : subd13_0 [4, 0] = true := by decide +kernel
theorem subd13_0_112 : subd13_0 [4, 1] = true := by decide +kernel
theorem subd13_0_113 : subd13_0 [4, 2] = true := by decide +kernel
theorem subd13_0_114 : subd13_0 [4, 3] = true := by decide +kernel
theorem subd13_0_115 : subd13_0 [5, -6] = true := by decide +kernel
theorem subd13_0_116 : subd13_0 [5, -5] = true := by decide +kernel
theorem subd13_0_117 : subd13_0 [5, -4] = true := by decide +kernel
theorem subd13_0_118 : subd13_0 [5, -3] = true := by decide +kernel
theorem subd13_0_119 : subd13_0 [5, -2] = true := by decide +kernel
theorem subd13_0_120 : subd13_0 [5, -1] = true := by decide +kernel
theorem subd13_0_121 : subd13_0 [5, 0] = true := by decide +kernel
theorem subd13_0_122 : subd13_0 [5, 1] = true := by decide +kernel
theorem subd13_0_123 : subd13_0 [6] = true := by decide +kernel
theorem sbd13_0_3 : ∀ q ∈ blkd13_0_3, subd13_0 q = true := by
  unfold blkd13_0_3
  exact List.forall_mem_cons.2 ⟨subd13_0_96, List.forall_mem_cons.2 ⟨subd13_0_97, List.forall_mem_cons.2 ⟨subd13_0_98, List.forall_mem_cons.2 ⟨subd13_0_99, List.forall_mem_cons.2 ⟨subd13_0_100, List.forall_mem_cons.2 ⟨subd13_0_101, List.forall_mem_cons.2 ⟨subd13_0_102, List.forall_mem_cons.2 ⟨subd13_0_103, List.forall_mem_cons.2 ⟨subd13_0_104, List.forall_mem_cons.2 ⟨subd13_0_105, List.forall_mem_cons.2 ⟨subd13_0_106, List.forall_mem_cons.2 ⟨subd13_0_107, List.forall_mem_cons.2 ⟨subd13_0_108, List.forall_mem_cons.2 ⟨subd13_0_109, List.forall_mem_cons.2 ⟨subd13_0_110, List.forall_mem_cons.2 ⟨subd13_0_111, List.forall_mem_cons.2 ⟨subd13_0_112, List.forall_mem_cons.2 ⟨subd13_0_113, List.forall_mem_cons.2 ⟨subd13_0_114, List.forall_mem_cons.2 ⟨subd13_0_115, List.forall_mem_cons.2 ⟨subd13_0_116, List.forall_mem_cons.2 ⟨subd13_0_117, List.forall_mem_cons.2 ⟨subd13_0_118, List.forall_mem_cons.2 ⟨subd13_0_119, List.forall_mem_cons.2 ⟨subd13_0_120, List.forall_mem_cons.2 ⟨subd13_0_121, List.forall_mem_cons.2 ⟨subd13_0_122, List.forall_mem_cons.2 ⟨subd13_0_123, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
