import ReflectZphi.Data.Cert5.C027.Base

namespace ReflectZphi.Data.Cert5.C027
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_32 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_35 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_36 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_37 : sub5 [-3, -1] = true := by decide +kernel
theorem sub5_38 : sub5 [-3, 0] = true := by decide +kernel
theorem sub5_39 : sub5 [-3, 1] = true := by decide +kernel
theorem sub5_40 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_41 : sub5 [-3, 3] = true := by decide +kernel
theorem sub5_42 : sub5 [-3, 4] = true := by decide +kernel
theorem sub5_43 : sub5 [-3, 5] = true := by decide +kernel
theorem sub5_44 : sub5 [-3, 6] = true := by decide +kernel
theorem sub5_45 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_46 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_47 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_48 : sub5 [-2, -3] = true := by decide +kernel
theorem sub5_49 : sub5 [-2, -2] = true := by decide +kernel
theorem sub5_50 : sub5 [-2, -1] = true := by decide +kernel
theorem sub5_51 : sub5 [-2, 0] = true := by decide +kernel
theorem sub5_52 : sub5 [-2, 1] = true := by decide +kernel
theorem sub5_53 : sub5 [-2, 2] = true := by decide +kernel
theorem sub5_54 : sub5 [-2, 3] = true := by decide +kernel
theorem sub5_55 : sub5 [-2, 4] = true := by decide +kernel
theorem sub5_56 : sub5 [-2, 5] = true := by decide +kernel
theorem sub5_57 : sub5 [-2, 6] = true := by decide +kernel
theorem sub5_58 : sub5 [-1, -7] = true := by decide +kernel
theorem sub5_59 : sub5 [-1, -6] = true := by decide +kernel
theorem sub5_60 : sub5 [-1, -5] = true := by decide +kernel
theorem sub5_61 : sub5 [-1, -4] = true := by decide +kernel
theorem sub5_62 : sub5 [-1, -3] = true := by decide +kernel
theorem sub5_63 : sub5 [-1, -2] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-1, -1] = true := by decide +kernel
theorem sub5_65 : sub5 [-1, 0] = true := by decide +kernel
theorem sub5_66 : sub5 [-1, 1] = true := by decide +kernel
theorem sub5_67 : sub5 [-1, 2] = true := by decide +kernel
theorem sub5_68 : sub5 [-1, 3] = true := by decide +kernel
theorem sub5_69 : sub5 [-1, 4] = true := by decide +kernel
theorem sub5_70 : sub5 [-1, 5] = true := by decide +kernel
theorem sub5_71 : sub5 [-1, 6] = true := by decide +kernel
theorem sub5_72 : sub5 [0, -7] = true := by decide +kernel
theorem sub5_73 : sub5 [0, -6] = true := by decide +kernel
theorem sub5_74 : sub5 [0, -5] = true := by decide +kernel
theorem sub5_75 : sub5 [0, -4] = true := by decide +kernel
theorem sub5_76 : sub5 [0, -3] = true := by decide +kernel
theorem sub5_77 : sub5 [0, -2] = true := by decide +kernel
theorem sub5_78 : sub5 [0, -1, -7] = true := by decide +kernel
theorem sub5_79 : sub5 [0, -1, -6] = true := by decide +kernel
theorem sub5_80 : sub5 [0, -1, -5] = true := by decide +kernel
theorem sub5_81 : sub5 [0, -1, -4] = true := by decide +kernel
theorem sub5_82 : sub5 [0, -1, -3] = true := by decide +kernel
theorem sub5_83 : sub5 [0, -1, -2] = true := by decide +kernel
theorem sub5_84 : sub5 [0, -1, -1] = true := by decide +kernel
theorem sub5_85 : sub5 [0, -1, 0] = true := by decide +kernel
theorem sub5_86 : sub5 [0, -1, 1] = true := by decide +kernel
theorem sub5_87 : sub5 [0, -1, 2] = true := by decide +kernel
theorem sub5_88 : sub5 [0, -1, 3] = true := by decide +kernel
theorem sub5_89 : sub5 [0, -1, 4] = true := by decide +kernel
theorem sub5_90 : sub5 [0, -1, 5] = true := by decide +kernel
theorem sub5_91 : sub5 [0, -1, 6] = true := by decide +kernel
theorem sub5_92 : sub5 [0, -1, 7] = true := by decide +kernel
theorem sub5_93 : sub5 [0, 0] = true := by decide +kernel
theorem sub5_94 : sub5 [0, 1, -8] = true := by decide +kernel
theorem sub5_95 : sub5 [0, 1, -7] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [0, 1, -6] = true := by decide +kernel
theorem sub5_97 : sub5 [0, 1, -5] = true := by decide +kernel
theorem sub5_98 : sub5 [0, 1, -4] = true := by decide +kernel
theorem sub5_99 : sub5 [0, 1, -3] = true := by decide +kernel
theorem sub5_100 : sub5 [0, 1, -2] = true := by decide +kernel
theorem sub5_101 : sub5 [0, 1, -1] = true := by decide +kernel
theorem sub5_102 : sub5 [0, 1, 0] = true := by decide +kernel
theorem sub5_103 : sub5 [0, 1, 1] = true := by decide +kernel
theorem sub5_104 : sub5 [0, 1, 2] = true := by decide +kernel
theorem sub5_105 : sub5 [0, 1, 3] = true := by decide +kernel
theorem sub5_106 : sub5 [0, 1, 4] = true := by decide +kernel
theorem sub5_107 : sub5 [0, 1, 5] = true := by decide +kernel
theorem sub5_108 : sub5 [0, 1, 6] = true := by decide +kernel
theorem sub5_109 : sub5 [0, 2] = true := by decide +kernel
theorem sub5_110 : sub5 [0, 3] = true := by decide +kernel
theorem sub5_111 : sub5 [0, 4] = true := by decide +kernel
theorem sub5_112 : sub5 [0, 5] = true := by decide +kernel
theorem sub5_113 : sub5 [0, 6] = true := by decide +kernel
theorem sub5_114 : sub5 [1, -7] = true := by decide +kernel
theorem sub5_115 : sub5 [1, -6] = true := by decide +kernel
theorem sub5_116 : sub5 [1, -5] = true := by decide +kernel
theorem sub5_117 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_118 : sub5 [1, -3] = true := by decide +kernel
theorem sub5_119 : sub5 [1, -2] = true := by decide +kernel
theorem sub5_120 : sub5 [1, -1] = true := by decide +kernel
theorem sub5_121 : sub5 [1, 0] = true := by decide +kernel
theorem sub5_122 : sub5 [1, 1] = true := by decide +kernel
theorem sub5_123 : sub5 [1, 2] = true := by decide +kernel
theorem sub5_124 : sub5 [1, 3] = true := by decide +kernel
theorem sub5_125 : sub5 [1, 4] = true := by decide +kernel
theorem sub5_126 : sub5 [1, 5] = true := by decide +kernel
theorem sub5_127 : sub5 [1, 6] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C027
