import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_11_0 : subd3_11 [-1] = true := by decide +kernel
theorem subd3_11_1 : subd3_11 [0] = true := by decide +kernel
theorem subd3_11_2 : subd3_11 [1] = true := by decide +kernel
theorem sbd3_11_0 : ∀ q ∈ blkd3_11_0, subd3_11 q = true := by
  unfold blkd3_11_0
  exact List.forall_mem_cons.2 ⟨subd3_11_0, List.forall_mem_cons.2 ⟨subd3_11_1, List.forall_mem_cons.2 ⟨subd3_11_2, List.forall_mem_nil _⟩⟩⟩
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
theorem subd4_4_0 : subd4_4 [] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_nil _⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_nil _⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
