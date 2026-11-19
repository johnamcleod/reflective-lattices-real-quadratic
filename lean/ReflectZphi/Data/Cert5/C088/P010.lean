import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_nil _⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel
theorem subd6_6_0 : subd6_6 [] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_nil _⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_nil _⟩
theorem ld_okd6_8 : ldCheck G d6_8.U d6_8.ms ldd6_8 = true := by decide +kernel
theorem pre_okd6_8 : subPre G cell6 d6_8 = true := by decide +kernel
theorem subd6_8_0 : subd6_8 [] = true := by decide +kernel
theorem sbd6_8_0 : ∀ q ∈ blkd6_8_0, subd6_8 q = true := by
  unfold blkd6_8_0
  exact List.forall_mem_cons.2 ⟨subd6_8_0, List.forall_mem_nil _⟩
theorem ld_okd6_9 : ldCheck G d6_9.U d6_9.ms ldd6_9 = true := by decide +kernel
theorem pre_okd6_9 : subPre G cell6 d6_9 = true := by decide +kernel
theorem subd6_9_0 : subd6_9 [] = true := by decide +kernel
theorem sbd6_9_0 : ∀ q ∈ blkd6_9_0, subd6_9 q = true := by
  unfold blkd6_9_0
  exact List.forall_mem_cons.2 ⟨subd6_9_0, List.forall_mem_nil _⟩
theorem ld_okd6_10 : ldCheck G d6_10.U d6_10.ms ldd6_10 = true := by decide +kernel
theorem pre_okd6_10 : subPre G cell6 d6_10 = true := by decide +kernel
theorem subd6_10_0 : subd6_10 [] = true := by decide +kernel
theorem sbd6_10_0 : ∀ q ∈ blkd6_10_0, subd6_10 q = true := by
  unfold blkd6_10_0
  exact List.forall_mem_cons.2 ⟨subd6_10_0, List.forall_mem_nil _⟩
theorem ld_okd6_11 : ldCheck G d6_11.U d6_11.ms ldd6_11 = true := by decide +kernel
theorem pre_okd6_11 : subPre G cell6 d6_11 = true := by decide +kernel
theorem subd6_11_0 : subd6_11 [] = true := by decide +kernel
theorem sbd6_11_0 : ∀ q ∈ blkd6_11_0, subd6_11 q = true := by
  unfold blkd6_11_0
  exact List.forall_mem_cons.2 ⟨subd6_11_0, List.forall_mem_nil _⟩
theorem ld_okd6_12 : ldCheck G d6_12.U d6_12.ms ldd6_12 = true := by decide +kernel
theorem pre_okd6_12 : subPre G cell6 d6_12 = true := by decide +kernel
theorem subd6_12_0 : subd6_12 [] = true := by decide +kernel
theorem sbd6_12_0 : ∀ q ∈ blkd6_12_0, subd6_12 q = true := by
  unfold blkd6_12_0
  exact List.forall_mem_cons.2 ⟨subd6_12_0, List.forall_mem_nil _⟩
theorem ld_okd6_13 : ldCheck G d6_13.U d6_13.ms ldd6_13 = true := by decide +kernel
theorem pre_okd6_13 : subPre G cell6 d6_13 = true := by decide +kernel
theorem subd6_13_0 : subd6_13 [] = true := by decide +kernel
theorem sbd6_13_0 : ∀ q ∈ blkd6_13_0, subd6_13 q = true := by
  unfold blkd6_13_0
  exact List.forall_mem_cons.2 ⟨subd6_13_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
