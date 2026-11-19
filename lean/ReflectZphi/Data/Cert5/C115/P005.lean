import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

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
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_nil _⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_nil _⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_nil _⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_nil _⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-1] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [0] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [1] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
