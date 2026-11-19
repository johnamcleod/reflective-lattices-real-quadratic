import ReflectZphi.Data.Cert5.C139.Base

namespace ReflectZphi.Data.Cert5.C139

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_3_32 : subd16_3 [1, 2] = true := by decide +kernel
theorem subd16_3_33 : subd16_3 [1, 3] = true := by decide +kernel
theorem subd16_3_34 : subd16_3 [2, -5] = true := by decide +kernel
theorem subd16_3_35 : subd16_3 [2, -4] = true := by decide +kernel
theorem subd16_3_36 : subd16_3 [2, -3] = true := by decide +kernel
theorem subd16_3_37 : subd16_3 [2, -2] = true := by decide +kernel
theorem subd16_3_38 : subd16_3 [2, -1] = true := by decide +kernel
theorem subd16_3_39 : subd16_3 [2, 0] = true := by decide +kernel
theorem subd16_3_40 : subd16_3 [2, 1] = true := by decide +kernel
theorem subd16_3_41 : subd16_3 [2, 2] = true := by decide +kernel
theorem subd16_3_42 : subd16_3 [3] = true := by decide +kernel
theorem subd16_3_43 : subd16_3 [4] = true := by decide +kernel
theorem sbd16_3_1 : ∀ q ∈ blkd16_3_1, subd16_3 q = true := by
  unfold blkd16_3_1
  exact List.forall_mem_cons.2 ⟨subd16_3_32, List.forall_mem_cons.2 ⟨subd16_3_33, List.forall_mem_cons.2 ⟨subd16_3_34, List.forall_mem_cons.2 ⟨subd16_3_35, List.forall_mem_cons.2 ⟨subd16_3_36, List.forall_mem_cons.2 ⟨subd16_3_37, List.forall_mem_cons.2 ⟨subd16_3_38, List.forall_mem_cons.2 ⟨subd16_3_39, List.forall_mem_cons.2 ⟨subd16_3_40, List.forall_mem_cons.2 ⟨subd16_3_41, List.forall_mem_cons.2 ⟨subd16_3_42, List.forall_mem_cons.2 ⟨subd16_3_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C139
