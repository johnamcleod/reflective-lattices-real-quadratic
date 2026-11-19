import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub13_928 : sub13 [5, 4] = true := by decide +kernel
theorem sub13_929 : sub13 [6, -6] = true := by decide +kernel
theorem sub13_930 : sub13 [6, -5] = true := by decide +kernel
theorem sub13_931 : sub13 [6, -4] = true := by decide +kernel
theorem sub13_932 : sub13 [6, -3] = true := by decide +kernel
theorem sub13_933 : sub13 [6, -2] = true := by decide +kernel
theorem sub13_934 : sub13 [6, -1] = true := by decide +kernel
theorem sub13_935 : sub13 [6, 0] = true := by decide +kernel
theorem sub13_936 : sub13 [6, 1] = true := by decide +kernel
theorem sub13_937 : sub13 [6, 2] = true := by decide +kernel
theorem sub13_938 : sub13 [7] = true := by decide +kernel
theorem sb13_29 : ∀ q ∈ blk13_29, sub13 q = true := by
  unfold blk13_29
  exact List.forall_mem_cons.2 ⟨sub13_928, List.forall_mem_cons.2 ⟨sub13_929, List.forall_mem_cons.2 ⟨sub13_930, List.forall_mem_cons.2 ⟨sub13_931, List.forall_mem_cons.2 ⟨sub13_932, List.forall_mem_cons.2 ⟨sub13_933, List.forall_mem_cons.2 ⟨sub13_934, List.forall_mem_cons.2 ⟨sub13_935, List.forall_mem_cons.2 ⟨sub13_936, List.forall_mem_cons.2 ⟨sub13_937, List.forall_mem_cons.2 ⟨sub13_938, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
