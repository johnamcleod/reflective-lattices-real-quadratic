import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_3_0 : subd15_3 [-2] = true := by decide +kernel
theorem subd15_3_1 : subd15_3 [-1] = true := by decide +kernel
theorem subd15_3_2 : subd15_3 [0] = true := by decide +kernel
theorem subd15_3_3 : subd15_3 [1] = true := by decide +kernel
theorem subd15_3_4 : subd15_3 [2] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_cons.2 ⟨subd15_3_1, List.forall_mem_cons.2 ⟨subd15_3_2, List.forall_mem_cons.2 ⟨subd15_3_3, List.forall_mem_cons.2 ⟨subd15_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C130
