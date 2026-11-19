import ReflectZphi.Data.Cert5.C025.Base

namespace ReflectZphi.Data.Cert5.C025
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_64 : sub3 [1, 0] = true := by decide +kernel
theorem sub3_65 : sub3 [1, 1] = true := by decide +kernel
theorem sub3_66 : sub3 [1, 2] = true := by decide +kernel
theorem sub3_67 : sub3 [1, 3] = true := by decide +kernel
theorem sub3_68 : sub3 [1, 4] = true := by decide +kernel
theorem sub3_69 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_70 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_71 : sub3 [2, -5] = true := by decide +kernel
theorem sub3_72 : sub3 [2, -4] = true := by decide +kernel
theorem sub3_73 : sub3 [2, -3] = true := by decide +kernel
theorem sub3_74 : sub3 [2, -2] = true := by decide +kernel
theorem sub3_75 : sub3 [2, -1] = true := by decide +kernel
theorem sub3_76 : sub3 [2, 0] = true := by decide +kernel
theorem sub3_77 : sub3 [2, 1] = true := by decide +kernel
theorem sub3_78 : sub3 [2, 2] = true := by decide +kernel
theorem sub3_79 : sub3 [2, 3] = true := by decide +kernel
theorem sub3_80 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_81 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_82 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_83 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_84 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_85 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_86 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_87 : sub3 [3, -1] = true := by decide +kernel
theorem sub3_88 : sub3 [3, 0] = true := by decide +kernel
theorem sub3_89 : sub3 [3, 1] = true := by decide +kernel
theorem sub3_90 : sub3 [3, 2] = true := by decide +kernel
theorem sub3_91 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_92 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_93 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_94 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_95 : sub3 [4, -3] = true := by decide +kernel
theorem sb3_2 : ∀ q ∈ blk3_2, sub3 q = true := by
  unfold blk3_2
  exact List.forall_mem_cons.2 ⟨sub3_64, List.forall_mem_cons.2 ⟨sub3_65, List.forall_mem_cons.2 ⟨sub3_66, List.forall_mem_cons.2 ⟨sub3_67, List.forall_mem_cons.2 ⟨sub3_68, List.forall_mem_cons.2 ⟨sub3_69, List.forall_mem_cons.2 ⟨sub3_70, List.forall_mem_cons.2 ⟨sub3_71, List.forall_mem_cons.2 ⟨sub3_72, List.forall_mem_cons.2 ⟨sub3_73, List.forall_mem_cons.2 ⟨sub3_74, List.forall_mem_cons.2 ⟨sub3_75, List.forall_mem_cons.2 ⟨sub3_76, List.forall_mem_cons.2 ⟨sub3_77, List.forall_mem_cons.2 ⟨sub3_78, List.forall_mem_cons.2 ⟨sub3_79, List.forall_mem_cons.2 ⟨sub3_80, List.forall_mem_cons.2 ⟨sub3_81, List.forall_mem_cons.2 ⟨sub3_82, List.forall_mem_cons.2 ⟨sub3_83, List.forall_mem_cons.2 ⟨sub3_84, List.forall_mem_cons.2 ⟨sub3_85, List.forall_mem_cons.2 ⟨sub3_86, List.forall_mem_cons.2 ⟨sub3_87, List.forall_mem_cons.2 ⟨sub3_88, List.forall_mem_cons.2 ⟨sub3_89, List.forall_mem_cons.2 ⟨sub3_90, List.forall_mem_cons.2 ⟨sub3_91, List.forall_mem_cons.2 ⟨sub3_92, List.forall_mem_cons.2 ⟨sub3_93, List.forall_mem_cons.2 ⟨sub3_94, List.forall_mem_cons.2 ⟨sub3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_96 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_97 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_98 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_99 : sub3 [4, 1] = true := by decide +kernel
theorem sub3_100 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_101 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_102 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_103 : sub3 [5] = true := by decide +kernel
theorem sb3_3 : ∀ q ∈ blk3_3, sub3 q = true := by
  unfold blk3_3
  exact List.forall_mem_cons.2 ⟨sub3_96, List.forall_mem_cons.2 ⟨sub3_97, List.forall_mem_cons.2 ⟨sub3_98, List.forall_mem_cons.2 ⟨sub3_99, List.forall_mem_cons.2 ⟨sub3_100, List.forall_mem_cons.2 ⟨sub3_101, List.forall_mem_cons.2 ⟨sub3_102, List.forall_mem_cons.2 ⟨sub3_103, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C025
