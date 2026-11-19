import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_2_32 : subd16_2 [-3, 3] = true := by decide +kernel
theorem subd16_2_33 : subd16_2 [-3, 4] = true := by decide +kernel
theorem subd16_2_34 : subd16_2 [-3, 5] = true := by decide +kernel
theorem subd16_2_35 : subd16_2 [-2, -7] = true := by decide +kernel
theorem subd16_2_36 : subd16_2 [-2, -6] = true := by decide +kernel
theorem subd16_2_37 : subd16_2 [-2, -5] = true := by decide +kernel
theorem subd16_2_38 : subd16_2 [-2, -4] = true := by decide +kernel
theorem subd16_2_39 : subd16_2 [-2, -3] = true := by decide +kernel
theorem subd16_2_40 : subd16_2 [-2, -2] = true := by decide +kernel
theorem subd16_2_41 : subd16_2 [-2, -1] = true := by decide +kernel
theorem subd16_2_42 : subd16_2 [-2, 0] = true := by decide +kernel
theorem subd16_2_43 : subd16_2 [-2, 1] = true := by decide +kernel
theorem subd16_2_44 : subd16_2 [-2, 2] = true := by decide +kernel
theorem subd16_2_45 : subd16_2 [-2, 3] = true := by decide +kernel
theorem subd16_2_46 : subd16_2 [-2, 4] = true := by decide +kernel
theorem subd16_2_47 : subd16_2 [-2, 5] = true := by decide +kernel
theorem subd16_2_48 : subd16_2 [-2, 6] = true := by decide +kernel
theorem subd16_2_49 : subd16_2 [-1, -7] = true := by decide +kernel
theorem subd16_2_50 : subd16_2 [-1, -6] = true := by decide +kernel
theorem subd16_2_51 : subd16_2 [-1, -5] = true := by decide +kernel
theorem subd16_2_52 : subd16_2 [-1, -4] = true := by decide +kernel
theorem subd16_2_53 : subd16_2 [-1, -3] = true := by decide +kernel
theorem subd16_2_54 : subd16_2 [-1, -2] = true := by decide +kernel
theorem subd16_2_55 : subd16_2 [-1, -1] = true := by decide +kernel
theorem subd16_2_56 : subd16_2 [-1, 0] = true := by decide +kernel
theorem subd16_2_57 : subd16_2 [-1, 1] = true := by decide +kernel
theorem subd16_2_58 : subd16_2 [-1, 2] = true := by decide +kernel
theorem subd16_2_59 : subd16_2 [-1, 3] = true := by decide +kernel
theorem subd16_2_60 : subd16_2 [-1, 4] = true := by decide +kernel
theorem subd16_2_61 : subd16_2 [-1, 5] = true := by decide +kernel
theorem subd16_2_62 : subd16_2 [-1, 6] = true := by decide +kernel
theorem subd16_2_63 : subd16_2 [0, -7] = true := by decide +kernel
theorem sbd16_2_1 : ∀ q ∈ blkd16_2_1, subd16_2 q = true := by
  unfold blkd16_2_1
  exact List.forall_mem_cons.2 ⟨subd16_2_32, List.forall_mem_cons.2 ⟨subd16_2_33, List.forall_mem_cons.2 ⟨subd16_2_34, List.forall_mem_cons.2 ⟨subd16_2_35, List.forall_mem_cons.2 ⟨subd16_2_36, List.forall_mem_cons.2 ⟨subd16_2_37, List.forall_mem_cons.2 ⟨subd16_2_38, List.forall_mem_cons.2 ⟨subd16_2_39, List.forall_mem_cons.2 ⟨subd16_2_40, List.forall_mem_cons.2 ⟨subd16_2_41, List.forall_mem_cons.2 ⟨subd16_2_42, List.forall_mem_cons.2 ⟨subd16_2_43, List.forall_mem_cons.2 ⟨subd16_2_44, List.forall_mem_cons.2 ⟨subd16_2_45, List.forall_mem_cons.2 ⟨subd16_2_46, List.forall_mem_cons.2 ⟨subd16_2_47, List.forall_mem_cons.2 ⟨subd16_2_48, List.forall_mem_cons.2 ⟨subd16_2_49, List.forall_mem_cons.2 ⟨subd16_2_50, List.forall_mem_cons.2 ⟨subd16_2_51, List.forall_mem_cons.2 ⟨subd16_2_52, List.forall_mem_cons.2 ⟨subd16_2_53, List.forall_mem_cons.2 ⟨subd16_2_54, List.forall_mem_cons.2 ⟨subd16_2_55, List.forall_mem_cons.2 ⟨subd16_2_56, List.forall_mem_cons.2 ⟨subd16_2_57, List.forall_mem_cons.2 ⟨subd16_2_58, List.forall_mem_cons.2 ⟨subd16_2_59, List.forall_mem_cons.2 ⟨subd16_2_60, List.forall_mem_cons.2 ⟨subd16_2_61, List.forall_mem_cons.2 ⟨subd16_2_62, List.forall_mem_cons.2 ⟨subd16_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_2_64 : subd16_2 [0, -6] = true := by decide +kernel
theorem subd16_2_65 : subd16_2 [0, -5] = true := by decide +kernel
theorem subd16_2_66 : subd16_2 [0, -4] = true := by decide +kernel
theorem subd16_2_67 : subd16_2 [0, -3] = true := by decide +kernel
theorem subd16_2_68 : subd16_2 [0, -2] = true := by decide +kernel
theorem subd16_2_69 : subd16_2 [0, -1] = true := by decide +kernel
theorem subd16_2_70 : subd16_2 [0, 0] = true := by decide +kernel
theorem subd16_2_71 : subd16_2 [0, 1] = true := by decide +kernel
theorem subd16_2_72 : subd16_2 [0, 2] = true := by decide +kernel
theorem subd16_2_73 : subd16_2 [0, 3] = true := by decide +kernel
theorem subd16_2_74 : subd16_2 [0, 4] = true := by decide +kernel
theorem subd16_2_75 : subd16_2 [0, 5] = true := by decide +kernel
theorem subd16_2_76 : subd16_2 [0, 6] = true := by decide +kernel
theorem subd16_2_77 : subd16_2 [1, -7] = true := by decide +kernel
theorem subd16_2_78 : subd16_2 [1, -6] = true := by decide +kernel
theorem subd16_2_79 : subd16_2 [1, -5] = true := by decide +kernel
theorem subd16_2_80 : subd16_2 [1, -4] = true := by decide +kernel
theorem subd16_2_81 : subd16_2 [1, -3] = true := by decide +kernel
theorem subd16_2_82 : subd16_2 [1, -2] = true := by decide +kernel
theorem subd16_2_83 : subd16_2 [1, -1] = true := by decide +kernel
theorem subd16_2_84 : subd16_2 [1, 0] = true := by decide +kernel
theorem subd16_2_85 : subd16_2 [1, 1] = true := by decide +kernel
theorem subd16_2_86 : subd16_2 [1, 2] = true := by decide +kernel
theorem subd16_2_87 : subd16_2 [1, 3] = true := by decide +kernel
theorem subd16_2_88 : subd16_2 [1, 4] = true := by decide +kernel
theorem subd16_2_89 : subd16_2 [1, 5] = true := by decide +kernel
theorem subd16_2_90 : subd16_2 [1, 6] = true := by decide +kernel
theorem subd16_2_91 : subd16_2 [2, -7] = true := by decide +kernel
theorem subd16_2_92 : subd16_2 [2, -6] = true := by decide +kernel
theorem subd16_2_93 : subd16_2 [2, -5] = true := by decide +kernel
theorem subd16_2_94 : subd16_2 [2, -4] = true := by decide +kernel
theorem subd16_2_95 : subd16_2 [2, -3] = true := by decide +kernel
theorem sbd16_2_2 : ∀ q ∈ blkd16_2_2, subd16_2 q = true := by
  unfold blkd16_2_2
  exact List.forall_mem_cons.2 ⟨subd16_2_64, List.forall_mem_cons.2 ⟨subd16_2_65, List.forall_mem_cons.2 ⟨subd16_2_66, List.forall_mem_cons.2 ⟨subd16_2_67, List.forall_mem_cons.2 ⟨subd16_2_68, List.forall_mem_cons.2 ⟨subd16_2_69, List.forall_mem_cons.2 ⟨subd16_2_70, List.forall_mem_cons.2 ⟨subd16_2_71, List.forall_mem_cons.2 ⟨subd16_2_72, List.forall_mem_cons.2 ⟨subd16_2_73, List.forall_mem_cons.2 ⟨subd16_2_74, List.forall_mem_cons.2 ⟨subd16_2_75, List.forall_mem_cons.2 ⟨subd16_2_76, List.forall_mem_cons.2 ⟨subd16_2_77, List.forall_mem_cons.2 ⟨subd16_2_78, List.forall_mem_cons.2 ⟨subd16_2_79, List.forall_mem_cons.2 ⟨subd16_2_80, List.forall_mem_cons.2 ⟨subd16_2_81, List.forall_mem_cons.2 ⟨subd16_2_82, List.forall_mem_cons.2 ⟨subd16_2_83, List.forall_mem_cons.2 ⟨subd16_2_84, List.forall_mem_cons.2 ⟨subd16_2_85, List.forall_mem_cons.2 ⟨subd16_2_86, List.forall_mem_cons.2 ⟨subd16_2_87, List.forall_mem_cons.2 ⟨subd16_2_88, List.forall_mem_cons.2 ⟨subd16_2_89, List.forall_mem_cons.2 ⟨subd16_2_90, List.forall_mem_cons.2 ⟨subd16_2_91, List.forall_mem_cons.2 ⟨subd16_2_92, List.forall_mem_cons.2 ⟨subd16_2_93, List.forall_mem_cons.2 ⟨subd16_2_94, List.forall_mem_cons.2 ⟨subd16_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_2_96 : subd16_2 [2, -2] = true := by decide +kernel
theorem subd16_2_97 : subd16_2 [2, -1] = true := by decide +kernel
theorem subd16_2_98 : subd16_2 [2, 0] = true := by decide +kernel
theorem subd16_2_99 : subd16_2 [2, 1] = true := by decide +kernel
theorem subd16_2_100 : subd16_2 [2, 2] = true := by decide +kernel
theorem subd16_2_101 : subd16_2 [2, 3] = true := by decide +kernel
theorem subd16_2_102 : subd16_2 [2, 4] = true := by decide +kernel
theorem subd16_2_103 : subd16_2 [2, 5] = true := by decide +kernel
theorem subd16_2_104 : subd16_2 [2, 6] = true := by decide +kernel
theorem subd16_2_105 : subd16_2 [3, -6] = true := by decide +kernel
theorem subd16_2_106 : subd16_2 [3, -5] = true := by decide +kernel
theorem subd16_2_107 : subd16_2 [3, -4] = true := by decide +kernel
theorem subd16_2_108 : subd16_2 [3, -3] = true := by decide +kernel
theorem subd16_2_109 : subd16_2 [3, -2] = true := by decide +kernel
theorem subd16_2_110 : subd16_2 [3, -1] = true := by decide +kernel
theorem subd16_2_111 : subd16_2 [3, 0] = true := by decide +kernel
theorem subd16_2_112 : subd16_2 [3, 1] = true := by decide +kernel
theorem subd16_2_113 : subd16_2 [3, 2] = true := by decide +kernel
theorem subd16_2_114 : subd16_2 [3, 3] = true := by decide +kernel
theorem subd16_2_115 : subd16_2 [3, 4] = true := by decide +kernel
theorem subd16_2_116 : subd16_2 [3, 5] = true := by decide +kernel
theorem subd16_2_117 : subd16_2 [4, -6] = true := by decide +kernel
theorem subd16_2_118 : subd16_2 [4, -5] = true := by decide +kernel
theorem subd16_2_119 : subd16_2 [4, -4] = true := by decide +kernel
theorem subd16_2_120 : subd16_2 [4, -3] = true := by decide +kernel
theorem subd16_2_121 : subd16_2 [4, -2] = true := by decide +kernel
theorem subd16_2_122 : subd16_2 [4, -1] = true := by decide +kernel
theorem subd16_2_123 : subd16_2 [4, 0] = true := by decide +kernel
theorem subd16_2_124 : subd16_2 [4, 1] = true := by decide +kernel
theorem subd16_2_125 : subd16_2 [4, 2] = true := by decide +kernel
theorem subd16_2_126 : subd16_2 [4, 3] = true := by decide +kernel
theorem subd16_2_127 : subd16_2 [4, 4] = true := by decide +kernel
theorem sbd16_2_3 : ∀ q ∈ blkd16_2_3, subd16_2 q = true := by
  unfold blkd16_2_3
  exact List.forall_mem_cons.2 ⟨subd16_2_96, List.forall_mem_cons.2 ⟨subd16_2_97, List.forall_mem_cons.2 ⟨subd16_2_98, List.forall_mem_cons.2 ⟨subd16_2_99, List.forall_mem_cons.2 ⟨subd16_2_100, List.forall_mem_cons.2 ⟨subd16_2_101, List.forall_mem_cons.2 ⟨subd16_2_102, List.forall_mem_cons.2 ⟨subd16_2_103, List.forall_mem_cons.2 ⟨subd16_2_104, List.forall_mem_cons.2 ⟨subd16_2_105, List.forall_mem_cons.2 ⟨subd16_2_106, List.forall_mem_cons.2 ⟨subd16_2_107, List.forall_mem_cons.2 ⟨subd16_2_108, List.forall_mem_cons.2 ⟨subd16_2_109, List.forall_mem_cons.2 ⟨subd16_2_110, List.forall_mem_cons.2 ⟨subd16_2_111, List.forall_mem_cons.2 ⟨subd16_2_112, List.forall_mem_cons.2 ⟨subd16_2_113, List.forall_mem_cons.2 ⟨subd16_2_114, List.forall_mem_cons.2 ⟨subd16_2_115, List.forall_mem_cons.2 ⟨subd16_2_116, List.forall_mem_cons.2 ⟨subd16_2_117, List.forall_mem_cons.2 ⟨subd16_2_118, List.forall_mem_cons.2 ⟨subd16_2_119, List.forall_mem_cons.2 ⟨subd16_2_120, List.forall_mem_cons.2 ⟨subd16_2_121, List.forall_mem_cons.2 ⟨subd16_2_122, List.forall_mem_cons.2 ⟨subd16_2_123, List.forall_mem_cons.2 ⟨subd16_2_124, List.forall_mem_cons.2 ⟨subd16_2_125, List.forall_mem_cons.2 ⟨subd16_2_126, List.forall_mem_cons.2 ⟨subd16_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
