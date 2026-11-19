import ReflectZphi.Data.Cert5.C065.Base

namespace ReflectZphi.Data.Cert5.C065

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_9 : ldCheck G d3_9.U d3_9.ms ldd3_9 = true := by decide +kernel
theorem pre_okd3_9 : subPre G cell3 d3_9 = true := by decide +kernel
theorem subd3_9_0 : subd3_9 [] = true := by decide +kernel
theorem sbd3_9_0 : ∀ q ∈ blkd3_9_0, subd3_9 q = true := by
  unfold blkd3_9_0
  exact List.forall_mem_cons.2 ⟨subd3_9_0, List.forall_mem_nil _⟩
theorem ld_okd3_10 : ldCheck G d3_10.U d3_10.ms ldd3_10 = true := by decide +kernel
theorem pre_okd3_10 : subPre G cell3 d3_10 = true := by decide +kernel
theorem subd3_10_0 : subd3_10 [] = true := by decide +kernel
theorem sbd3_10_0 : ∀ q ∈ blkd3_10_0, subd3_10 q = true := by
  unfold blkd3_10_0
  exact List.forall_mem_cons.2 ⟨subd3_10_0, List.forall_mem_nil _⟩
theorem ld_okd3_11 : ldCheck G d3_11.U d3_11.ms ldd3_11 = true := by decide +kernel
theorem pre_okd3_11 : subPre G cell3 d3_11 = true := by decide +kernel
theorem subd3_11_0 : subd3_11 [] = true := by decide +kernel
theorem sbd3_11_0 : ∀ q ∈ blkd3_11_0, subd3_11 q = true := by
  unfold blkd3_11_0
  exact List.forall_mem_cons.2 ⟨subd3_11_0, List.forall_mem_nil _⟩
theorem ld_okd3_12 : ldCheck G d3_12.U d3_12.ms ldd3_12 = true := by decide +kernel
theorem pre_okd3_12 : subPre G cell3 d3_12 = true := by decide +kernel
theorem subd3_12_0 : subd3_12 [] = true := by decide +kernel
theorem sbd3_12_0 : ∀ q ∈ blkd3_12_0, subd3_12 q = true := by
  unfold blkd3_12_0
  exact List.forall_mem_cons.2 ⟨subd3_12_0, List.forall_mem_nil _⟩
theorem ld_okd3_13 : ldCheck G d3_13.U d3_13.ms ldd3_13 = true := by decide +kernel
theorem pre_okd3_13 : subPre G cell3 d3_13 = true := by decide +kernel
theorem subd3_13_0 : subd3_13 [] = true := by decide +kernel
theorem sbd3_13_0 : ∀ q ∈ blkd3_13_0, subd3_13 q = true := by
  unfold blkd3_13_0
  exact List.forall_mem_cons.2 ⟨subd3_13_0, List.forall_mem_nil _⟩
theorem ld_okd3_14 : ldCheck G d3_14.U d3_14.ms ldd3_14 = true := by decide +kernel
theorem pre_okd3_14 : subPre G cell3 d3_14 = true := by decide +kernel
theorem subd3_14_0 : subd3_14 [-1] = true := by decide +kernel
theorem subd3_14_1 : subd3_14 [0] = true := by decide +kernel
theorem subd3_14_2 : subd3_14 [1] = true := by decide +kernel
theorem sbd3_14_0 : ∀ q ∈ blkd3_14_0, subd3_14 q = true := by
  unfold blkd3_14_0
  exact List.forall_mem_cons.2 ⟨subd3_14_0, List.forall_mem_cons.2 ⟨subd3_14_1, List.forall_mem_cons.2 ⟨subd3_14_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C065
