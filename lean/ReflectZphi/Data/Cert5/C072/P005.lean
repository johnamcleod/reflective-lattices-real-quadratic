import ReflectZphi.Data.Cert5.C072.Base

namespace ReflectZphi.Data.Cert5.C072
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_64 : sub7 [0, 1, -3] = true := by decide +kernel
theorem sub7_65 : sub7 [0, 1, -2] = true := by decide +kernel
theorem sub7_66 : sub7 [0, 1, -1] = true := by decide +kernel
theorem sub7_67 : sub7 [0, 1, 0] = true := by decide +kernel
theorem sub7_68 : sub7 [0, 1, 1] = true := by decide +kernel
theorem sub7_69 : sub7 [0, 1, 2] = true := by decide +kernel
theorem sub7_70 : sub7 [0, 1, 3] = true := by decide +kernel
theorem sub7_71 : sub7 [0, 1, 4] = true := by decide +kernel
theorem sub7_72 : sub7 [0, 1, 5] = true := by decide +kernel
theorem sub7_73 : sub7 [0, 1, 6] = true := by decide +kernel
theorem sub7_74 : sub7 [0, 2] = true := by decide +kernel
theorem sub7_75 : sub7 [0, 3] = true := by decide +kernel
theorem sub7_76 : sub7 [0, 4] = true := by decide +kernel
theorem sub7_77 : sub7 [1, -5] = true := by decide +kernel
theorem sub7_78 : sub7 [1, -4] = true := by decide +kernel
theorem sub7_79 : sub7 [1, -3] = true := by decide +kernel
theorem sub7_80 : sub7 [1, -2] = true := by decide +kernel
theorem sub7_81 : sub7 [1, -1] = true := by decide +kernel
theorem sub7_82 : sub7 [1, 0] = true := by decide +kernel
theorem sub7_83 : sub7 [1, 1] = true := by decide +kernel
theorem sub7_84 : sub7 [1, 2] = true := by decide +kernel
theorem sub7_85 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_86 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_87 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_88 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_89 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_90 : sub7 [2, -1] = true := by decide +kernel
theorem sub7_91 : sub7 [2, 0] = true := by decide +kernel
theorem sub7_92 : sub7 [2, 1] = true := by decide +kernel
theorem sub7_93 : sub7 [2, 2] = true := by decide +kernel
theorem sub7_94 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_95 : sub7 [2, 4] = true := by decide +kernel
theorem sb7_2 : ∀ q ∈ blk7_2, sub7 q = true := by
  unfold blk7_2
  exact List.forall_mem_cons.2 ⟨sub7_64, List.forall_mem_cons.2 ⟨sub7_65, List.forall_mem_cons.2 ⟨sub7_66, List.forall_mem_cons.2 ⟨sub7_67, List.forall_mem_cons.2 ⟨sub7_68, List.forall_mem_cons.2 ⟨sub7_69, List.forall_mem_cons.2 ⟨sub7_70, List.forall_mem_cons.2 ⟨sub7_71, List.forall_mem_cons.2 ⟨sub7_72, List.forall_mem_cons.2 ⟨sub7_73, List.forall_mem_cons.2 ⟨sub7_74, List.forall_mem_cons.2 ⟨sub7_75, List.forall_mem_cons.2 ⟨sub7_76, List.forall_mem_cons.2 ⟨sub7_77, List.forall_mem_cons.2 ⟨sub7_78, List.forall_mem_cons.2 ⟨sub7_79, List.forall_mem_cons.2 ⟨sub7_80, List.forall_mem_cons.2 ⟨sub7_81, List.forall_mem_cons.2 ⟨sub7_82, List.forall_mem_cons.2 ⟨sub7_83, List.forall_mem_cons.2 ⟨sub7_84, List.forall_mem_cons.2 ⟨sub7_85, List.forall_mem_cons.2 ⟨sub7_86, List.forall_mem_cons.2 ⟨sub7_87, List.forall_mem_cons.2 ⟨sub7_88, List.forall_mem_cons.2 ⟨sub7_89, List.forall_mem_cons.2 ⟨sub7_90, List.forall_mem_cons.2 ⟨sub7_91, List.forall_mem_cons.2 ⟨sub7_92, List.forall_mem_cons.2 ⟨sub7_93, List.forall_mem_cons.2 ⟨sub7_94, List.forall_mem_cons.2 ⟨sub7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_96 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_97 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_98 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_99 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_100 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_101 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_102 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_103 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_104 : sub7 [4] = true := by decide +kernel
theorem sb7_3 : ∀ q ∈ blk7_3, sub7 q = true := by
  unfold blk7_3
  exact List.forall_mem_cons.2 ⟨sub7_96, List.forall_mem_cons.2 ⟨sub7_97, List.forall_mem_cons.2 ⟨sub7_98, List.forall_mem_cons.2 ⟨sub7_99, List.forall_mem_cons.2 ⟨sub7_100, List.forall_mem_cons.2 ⟨sub7_101, List.forall_mem_cons.2 ⟨sub7_102, List.forall_mem_cons.2 ⟨sub7_103, List.forall_mem_cons.2 ⟨sub7_104, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C072
