import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_10 : ldCheck G d3_10.U d3_10.ms ldd3_10 = true := by decide +kernel
theorem pre_okd3_10 : subPre G cell3 d3_10 = true := by decide +kernel
theorem subd3_10_0 : subd3_10 [-2] = true := by decide +kernel
theorem subd3_10_1 : subd3_10 [-1] = true := by decide +kernel
theorem subd3_10_2 : subd3_10 [0] = true := by decide +kernel
theorem subd3_10_3 : subd3_10 [1] = true := by decide +kernel
theorem subd3_10_4 : subd3_10 [2] = true := by decide +kernel
theorem sbd3_10_0 : ∀ q ∈ blkd3_10_0, subd3_10 q = true := by
  unfold blkd3_10_0
  exact List.forall_mem_cons.2 ⟨subd3_10_0, List.forall_mem_cons.2 ⟨subd3_10_1, List.forall_mem_cons.2 ⟨subd3_10_2, List.forall_mem_cons.2 ⟨subd3_10_3, List.forall_mem_cons.2 ⟨subd3_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_11 : ldCheck G d3_11.U d3_11.ms ldd3_11 = true := by decide +kernel
theorem pre_okd3_11 : subPre G cell3 d3_11 = true := by decide +kernel
theorem subd3_11_0 : subd3_11 [-2] = true := by decide +kernel
theorem subd3_11_1 : subd3_11 [-1] = true := by decide +kernel
theorem subd3_11_2 : subd3_11 [0] = true := by decide +kernel
theorem subd3_11_3 : subd3_11 [1] = true := by decide +kernel
theorem subd3_11_4 : subd3_11 [2] = true := by decide +kernel
theorem sbd3_11_0 : ∀ q ∈ blkd3_11_0, subd3_11 q = true := by
  unfold blkd3_11_0
  exact List.forall_mem_cons.2 ⟨subd3_11_0, List.forall_mem_cons.2 ⟨subd3_11_1, List.forall_mem_cons.2 ⟨subd3_11_2, List.forall_mem_cons.2 ⟨subd3_11_3, List.forall_mem_cons.2 ⟨subd3_11_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
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
theorem subd3_14_1 : subd3_14 [0, -2] = true := by decide +kernel
theorem subd3_14_2 : subd3_14 [0, -1] = true := by decide +kernel
theorem subd3_14_3 : subd3_14 [0, 0] = true := by decide +kernel
theorem subd3_14_4 : subd3_14 [0, 1] = true := by decide +kernel
theorem subd3_14_5 : subd3_14 [1] = true := by decide +kernel
theorem sbd3_14_0 : ∀ q ∈ blkd3_14_0, subd3_14 q = true := by
  unfold blkd3_14_0
  exact List.forall_mem_cons.2 ⟨subd3_14_0, List.forall_mem_cons.2 ⟨subd3_14_1, List.forall_mem_cons.2 ⟨subd3_14_2, List.forall_mem_cons.2 ⟨subd3_14_3, List.forall_mem_cons.2 ⟨subd3_14_4, List.forall_mem_cons.2 ⟨subd3_14_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
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

end ReflectZphi.Data.Cert5.C124
