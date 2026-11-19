import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd15_4 : ldCheck G d15_4.U d15_4.ms ldd15_4 = true := by decide +kernel
theorem pre_okd15_4 : subPre G cell15 d15_4 = true := by decide +kernel
theorem subd15_4_0 : subd15_4 [] = true := by decide +kernel
theorem sbd15_4_0 : ∀ q ∈ blkd15_4_0, subd15_4 q = true := by
  unfold blkd15_4_0
  exact List.forall_mem_cons.2 ⟨subd15_4_0, List.forall_mem_nil _⟩
theorem ld_okd15_5 : ldCheck G d15_5.U d15_5.ms ldd15_5 = true := by decide +kernel
theorem pre_okd15_5 : subPre G cell15 d15_5 = true := by decide +kernel
theorem subd15_5_0 : subd15_5 [] = true := by decide +kernel
theorem sbd15_5_0 : ∀ q ∈ blkd15_5_0, subd15_5 q = true := by
  unfold blkd15_5_0
  exact List.forall_mem_cons.2 ⟨subd15_5_0, List.forall_mem_nil _⟩
theorem ld_okd15_6 : ldCheck G d15_6.U d15_6.ms ldd15_6 = true := by decide +kernel
theorem pre_okd15_6 : subPre G cell15 d15_6 = true := by decide +kernel
theorem subd15_6_0 : subd15_6 [] = true := by decide +kernel
theorem sbd15_6_0 : ∀ q ∈ blkd15_6_0, subd15_6 q = true := by
  unfold blkd15_6_0
  exact List.forall_mem_cons.2 ⟨subd15_6_0, List.forall_mem_nil _⟩
theorem ld_okd15_7 : ldCheck G d15_7.U d15_7.ms ldd15_7 = true := by decide +kernel
theorem pre_okd15_7 : subPre G cell15 d15_7 = true := by decide +kernel
theorem subd15_7_0 : subd15_7 [] = true := by decide +kernel
theorem sbd15_7_0 : ∀ q ∈ blkd15_7_0, subd15_7 q = true := by
  unfold blkd15_7_0
  exact List.forall_mem_cons.2 ⟨subd15_7_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C126
