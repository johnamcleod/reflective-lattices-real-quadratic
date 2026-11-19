import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub12_32 : sub12 [2, -2] = true := by decide +kernel
theorem sub12_33 : sub12 [2, -1] = true := by decide +kernel
theorem sub12_34 : sub12 [2, 0] = true := by decide +kernel
theorem sub12_35 : sub12 [2, 1] = true := by decide +kernel
theorem sub12_36 : sub12 [2, 2] = true := by decide +kernel
theorem sub12_37 : sub12 [3] = true := by decide +kernel
theorem sb12_1 : ∀ q ∈ blk12_1, sub12 q = true := by
  unfold blk12_1
  exact List.forall_mem_cons.2 ⟨sub12_32, List.forall_mem_cons.2 ⟨sub12_33, List.forall_mem_cons.2 ⟨sub12_34, List.forall_mem_cons.2 ⟨sub12_35, List.forall_mem_cons.2 ⟨sub12_36, List.forall_mem_cons.2 ⟨sub12_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
