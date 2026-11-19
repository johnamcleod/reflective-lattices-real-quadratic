import ReflectZphi.Data.Cert5.C048.Base

namespace ReflectZphi.Data.Cert5.C048
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_96 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_97 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_98 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_99 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_100 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_101 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_102 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_103 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_104 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_105 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_106 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_107 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_108 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_109 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_110 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_111 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_112 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_113 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_114 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_115 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_116 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_117 : sub5 [5, 2] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C048
