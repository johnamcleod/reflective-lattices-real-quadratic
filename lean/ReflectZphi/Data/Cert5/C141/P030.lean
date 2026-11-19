import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd21_2 : ldCheck G d21_2.U d21_2.ms ldd21_2 = true := by decide +kernel
theorem pre_okd21_2 : subPre G cell21 d21_2 = true := by decide +kernel
theorem subd21_2_0 : subd21_2 [-2] = true := by decide +kernel
theorem subd21_2_1 : subd21_2 [-1] = true := by decide +kernel
theorem subd21_2_2 : subd21_2 [0] = true := by decide +kernel
theorem subd21_2_3 : subd21_2 [1] = true := by decide +kernel
theorem subd21_2_4 : subd21_2 [2] = true := by decide +kernel
theorem sbd21_2_0 : ∀ q ∈ blkd21_2_0, subd21_2 q = true := by
  unfold blkd21_2_0
  exact List.forall_mem_cons.2 ⟨subd21_2_0, List.forall_mem_cons.2 ⟨subd21_2_1, List.forall_mem_cons.2 ⟨subd21_2_2, List.forall_mem_cons.2 ⟨subd21_2_3, List.forall_mem_cons.2 ⟨subd21_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd21_3 : ldCheck G d21_3.U d21_3.ms ldd21_3 = true := by decide +kernel
theorem pre_okd21_3 : subPre G cell21 d21_3 = true := by decide +kernel
theorem subd21_3_0 : subd21_3 [] = true := by decide +kernel
theorem sbd21_3_0 : ∀ q ∈ blkd21_3_0, subd21_3 q = true := by
  unfold blkd21_3_0
  exact List.forall_mem_cons.2 ⟨subd21_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C141
