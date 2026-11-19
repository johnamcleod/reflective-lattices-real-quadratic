import ReflectZphi.Data.Cert5.C071.Base

namespace ReflectZphi.Data.Cert5.C071
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_32 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_33 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_34 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_35 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_36 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_37 : sub6 [3] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C071
