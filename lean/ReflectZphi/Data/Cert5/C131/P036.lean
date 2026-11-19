import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd21_1 : ldCheck G d21_1.U d21_1.ms ldd21_1 = true := by decide +kernel
theorem pre_okd21_1 : subPre G cell21 d21_1 = true := by decide +kernel
theorem subd21_1_0 : subd21_1 [] = true := by decide +kernel
theorem sbd21_1_0 : ∀ q ∈ blkd21_1_0, subd21_1 q = true := by
  unfold blkd21_1_0
  exact List.forall_mem_cons.2 ⟨subd21_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C131
