import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_32 : sub3 [-3, 4] = true := by decide +kernel
theorem sub3_33 : sub3 [-2, -8] = true := by decide +kernel
theorem sub3_34 : sub3 [-2, -7] = true := by decide +kernel
theorem sub3_35 : sub3 [-2, -6] = true := by decide +kernel
theorem sub3_36 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_37 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_38 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_39 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_40 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_41 : sub3 [-2, 0] = true := by decide +kernel
theorem sub3_42 : sub3 [-2, 1] = true := by decide +kernel
theorem sub3_43 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_44 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_45 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_46 : sub3 [-2, 5] = true := by decide +kernel
theorem sub3_47 : sub3 [-1, -7] = true := by decide +kernel
theorem sub3_48 : sub3 [-1, -6] = true := by decide +kernel
theorem sub3_49 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_50 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_51 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_52 : sub3 [-1, -2] = true := by decide +kernel
theorem sub3_53 : sub3 [-1, -1] = true := by decide +kernel
theorem sub3_54 : sub3 [-1, 0] = true := by decide +kernel
theorem sub3_55 : sub3 [-1, 1] = true := by decide +kernel
theorem sub3_56 : sub3 [-1, 2] = true := by decide +kernel
theorem sub3_57 : sub3 [-1, 3] = true := by decide +kernel
theorem sub3_58 : sub3 [-1, 4] = true := by decide +kernel
theorem sub3_59 : sub3 [-1, 5] = true := by decide +kernel
theorem sub3_60 : sub3 [-1, 6] = true := by decide +kernel
theorem sub3_61 : sub3 [0, -7] = true := by decide +kernel
theorem sub3_62 : sub3 [0, -6] = true := by decide +kernel
theorem sub3_63 : sub3 [0, -5] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_64 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_65 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_66 : sub3 [0, -2] = true := by decide +kernel
theorem sub3_67 : sub3 [0, -1] = true := by decide +kernel
theorem sub3_68 : sub3 [0, 0] = true := by decide +kernel
theorem sub3_69 : sub3 [0, 1] = true := by decide +kernel
theorem sub3_70 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_71 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_72 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_73 : sub3 [0, 5] = true := by decide +kernel
theorem sub3_74 : sub3 [0, 6] = true := by decide +kernel
theorem sub3_75 : sub3 [1, -7] = true := by decide +kernel
theorem sub3_76 : sub3 [1, -6] = true := by decide +kernel
theorem sub3_77 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_78 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_79 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_80 : sub3 [1, -2] = true := by decide +kernel
theorem sub3_81 : sub3 [1, -1] = true := by decide +kernel
theorem sub3_82 : sub3 [1, 0] = true := by decide +kernel
theorem sub3_83 : sub3 [1, 1] = true := by decide +kernel
theorem sub3_84 : sub3 [1, 2] = true := by decide +kernel
theorem sub3_85 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_86 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_87 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_88 : sub3 [1, 6] = true := by decide +kernel
theorem sub3_89 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_90 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_91 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_92 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_93 : sub3 [2, -2] = true := by decide +kernel
theorem sub3_94 : sub3 [2, -1] = true := by decide +kernel
theorem sub3_95 : sub3 [2, 0] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_97 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_98 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_99 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_100 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_101 : sub3 [2, 6] = true := by decide +kernel
theorem sub3_102 : sub3 [2, 7] = true := by decide +kernel
theorem sub3_103 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_104 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_105 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_106 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_107 : sub3 [3, -1] = true := by decide +kernel
theorem sub3_108 : sub3 [3, 0] = true := by decide +kernel
theorem sub3_109 : sub3 [3, 1] = true := by decide +kernel
theorem sub3_110 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_111 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_112 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_113 : sub3 [3, 5] = true := by decide +kernel
theorem sub3_114 : sub3 [3, 6] = true := by decide +kernel
theorem sub3_115 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_116 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_117 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_118 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_119 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_120 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_121 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_122 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_123 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_124 : sub3 [4, 5] = true := by decide +kernel
theorem sub3_125 : sub3 [4, 6] = true := by decide +kernel
theorem sub3_126 : sub3 [5, -3] = true := by decide +kernel
theorem sub3_127 : sub3 [5, -2] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_cons.2 ⟨sub3_104, List.forall_mem_cons.2 ⟨sub3_105, List.forall_mem_cons.2 ⟨sub3_106, List.forall_mem_cons.2 ⟨sub3_107, List.forall_mem_cons.2 ⟨sub3_108, List.forall_mem_cons.2 ⟨sub3_109, List.forall_mem_cons.2 ⟨sub3_110, List.forall_mem_cons.2 ⟨sub3_111, List.forall_mem_cons.2 ⟨sub3_112, List.forall_mem_cons.2 ⟨sub3_113, List.forall_mem_cons.2 ⟨sub3_114, List.forall_mem_cons.2 ⟨sub3_115, List.forall_mem_cons.2 ⟨sub3_116, List.forall_mem_cons.2 ⟨sub3_117, List.forall_mem_cons.2 ⟨sub3_118, List.forall_mem_cons.2 ⟨sub3_119, List.forall_mem_cons.2 ⟨sub3_120, List.forall_mem_cons.2 ⟨sub3_121, List.forall_mem_cons.2 ⟨sub3_122, List.forall_mem_cons.2 ⟨sub3_123, List.forall_mem_cons.2 ⟨sub3_124, List.forall_mem_cons.2 ⟨sub3_125, List.forall_mem_cons.2 ⟨sub3_126, List.forall_mem_cons.2 ⟨sub3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_128 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_129 : sub3 [5, 0] = true := by decide +kernel
theorem sub3_130 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_131 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_132 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_133 : sub3 [5, 4] = true := by decide +kernel
theorem sub3_134 : sub3 [5, 5] = true := by decide +kernel
theorem sub3_135 : sub3 [6] = true := by decide +kernel
theorem sb3_4 : ∀ q ∈ blk3_4, sub3 q = true := by
  unfold blk3_4
  exact List.forall_mem_cons.2 ⟨sub3_128, List.forall_mem_cons.2 ⟨sub3_129, List.forall_mem_cons.2 ⟨sub3_130, List.forall_mem_cons.2 ⟨sub3_131, List.forall_mem_cons.2 ⟨sub3_132, List.forall_mem_cons.2 ⟨sub3_133, List.forall_mem_cons.2 ⟨sub3_134, List.forall_mem_cons.2 ⟨sub3_135, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
