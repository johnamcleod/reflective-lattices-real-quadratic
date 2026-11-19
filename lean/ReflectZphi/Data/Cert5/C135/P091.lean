import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd19_7 : ldCheck G d19_7.U d19_7.ms ldd19_7 = true := by decide +kernel
theorem pre_okd19_7 : subPre G cell19 d19_7 = true := by decide +kernel
theorem subd19_7_0 : subd19_7 [] = true := by decide +kernel
theorem sbd19_7_0 : ∀ q ∈ blkd19_7_0, subd19_7 q = true := by
  unfold blkd19_7_0
  exact List.forall_mem_cons.2 ⟨subd19_7_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C135
