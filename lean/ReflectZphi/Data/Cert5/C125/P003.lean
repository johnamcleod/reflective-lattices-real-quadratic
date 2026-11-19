import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_32 : sub4 [-3, 1] = true := by decide +kernel
theorem sub4_33 : sub4 [-3, 2] = true := by decide +kernel
theorem sub4_34 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_35 : sub4 [-3, 4] = true := by decide +kernel
theorem sub4_36 : sub4 [-2, -8] = true := by decide +kernel
theorem sub4_37 : sub4 [-2, -7] = true := by decide +kernel
theorem sub4_38 : sub4 [-2, -6] = true := by decide +kernel
theorem sub4_39 : sub4 [-2, -5] = true := by decide +kernel
theorem sub4_40 : sub4 [-2, -4] = true := by decide +kernel
theorem sub4_41 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_42 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_43 : sub4 [-2, -1] = true := by decide +kernel
theorem sub4_44 : sub4 [-2, 0] = true := by decide +kernel
theorem sub4_45 : sub4 [-2, 1] = true := by decide +kernel
theorem sub4_46 : sub4 [-2, 2] = true := by decide +kernel
theorem sub4_47 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_48 : sub4 [-2, 4] = true := by decide +kernel
theorem sub4_49 : sub4 [-2, 5] = true := by decide +kernel
theorem sub4_50 : sub4 [-1, -7] = true := by decide +kernel
theorem sub4_51 : sub4 [-1, -6] = true := by decide +kernel
theorem sub4_52 : sub4 [-1, -5] = true := by decide +kernel
theorem sub4_53 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_54 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_55 : sub4 [-1, -2] = true := by decide +kernel
theorem sub4_56 : sub4 [-1, -1] = true := by decide +kernel
theorem sub4_57 : sub4 [-1, 0] = true := by decide +kernel
theorem sub4_58 : sub4 [-1, 1] = true := by decide +kernel
theorem sub4_59 : sub4 [-1, 2] = true := by decide +kernel
theorem sub4_60 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_61 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_62 : sub4 [-1, 5] = true := by decide +kernel
theorem sub4_63 : sub4 [-1, 6] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_64 : sub4 [0, -7] = true := by decide +kernel
theorem sub4_65 : sub4 [0, -6] = true := by decide +kernel
theorem sub4_66 : sub4 [0, -5] = true := by decide +kernel
theorem sub4_67 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_68 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_69 : sub4 [0, -2] = true := by decide +kernel
theorem sub4_70 : sub4 [0, -1] = true := by decide +kernel
theorem sub4_71 : sub4 [0, 0] = true := by decide +kernel
theorem sub4_72 : sub4 [0, 1] = true := by decide +kernel
theorem sub4_73 : sub4 [0, 2] = true := by decide +kernel
theorem sub4_74 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_75 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_76 : sub4 [0, 5] = true := by decide +kernel
theorem sub4_77 : sub4 [0, 6] = true := by decide +kernel
theorem sub4_78 : sub4 [1, -7] = true := by decide +kernel
theorem sub4_79 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_80 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_81 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_82 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_83 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_84 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_85 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_86 : sub4 [1, 1] = true := by decide +kernel
theorem sub4_87 : sub4 [1, 2] = true := by decide +kernel
theorem sub4_88 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_89 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_90 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_91 : sub4 [1, 6] = true := by decide +kernel
theorem sub4_92 : sub4 [2, -6] = true := by decide +kernel
theorem sub4_93 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_94 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_95 : sub4 [2, -3] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_97 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_98 : sub4 [2, 0] = true := by decide +kernel
theorem sub4_99 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_100 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_101 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_102 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_103 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_104 : sub4 [2, 6] = true := by decide +kernel
theorem sub4_105 : sub4 [2, 7] = true := by decide +kernel
theorem sub4_106 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_107 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_108 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_109 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_110 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_111 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_112 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_113 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_114 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_115 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_116 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_117 : sub4 [3, 6] = true := by decide +kernel
theorem sub4_118 : sub4 [3, 7] = true := by decide +kernel
theorem sub4_119 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_120 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_121 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_122 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_123 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_124 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_125 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_126 : sub4 [4, 3] = true := by decide +kernel
theorem sub4_127 : sub4 [4, 4] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_128 : sub4 [4, 5] = true := by decide +kernel
theorem sub4_129 : sub4 [4, 6] = true := by decide +kernel
theorem sub4_130 : sub4 [4, 7] = true := by decide +kernel
theorem sub4_131 : sub4 [5, -3] = true := by decide +kernel
theorem sub4_132 : sub4 [5, -2] = true := by decide +kernel
theorem sub4_133 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_134 : sub4 [5, 0] = true := by decide +kernel
theorem sub4_135 : sub4 [5, 1] = true := by decide +kernel
theorem sub4_136 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_137 : sub4 [5, 3] = true := by decide +kernel
theorem sub4_138 : sub4 [5, 4] = true := by decide +kernel
theorem sub4_139 : sub4 [5, 5] = true := by decide +kernel
theorem sub4_140 : sub4 [5, 6] = true := by decide +kernel
theorem sub4_141 : sub4 [6] = true := by decide +kernel
theorem sb4_4 : ∀ q ∈ blk4_4, sub4 q = true := by
  unfold blk4_4
  exact List.forall_mem_cons.2 ⟨sub4_128, List.forall_mem_cons.2 ⟨sub4_129, List.forall_mem_cons.2 ⟨sub4_130, List.forall_mem_cons.2 ⟨sub4_131, List.forall_mem_cons.2 ⟨sub4_132, List.forall_mem_cons.2 ⟨sub4_133, List.forall_mem_cons.2 ⟨sub4_134, List.forall_mem_cons.2 ⟨sub4_135, List.forall_mem_cons.2 ⟨sub4_136, List.forall_mem_cons.2 ⟨sub4_137, List.forall_mem_cons.2 ⟨sub4_138, List.forall_mem_cons.2 ⟨sub4_139, List.forall_mem_cons.2 ⟨sub4_140, List.forall_mem_cons.2 ⟨sub4_141, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
