import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_nil _⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel
theorem subd3_4_0 : subd3_4 [] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_nil _⟩
theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_nil _⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel
theorem subd3_6_0 : subd3_6 [-2] = true := by decide +kernel
theorem subd3_6_1 : subd3_6 [-1] = true := by decide +kernel
theorem subd3_6_2 : subd3_6 [0] = true := by decide +kernel
theorem subd3_6_3 : subd3_6 [1] = true := by decide +kernel
theorem subd3_6_4 : subd3_6 [2] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_cons.2 ⟨subd3_6_1, List.forall_mem_cons.2 ⟨subd3_6_2, List.forall_mem_cons.2 ⟨subd3_6_3, List.forall_mem_cons.2 ⟨subd3_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [-2] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [-1] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [0] = true := by decide +kernel
theorem subd3_7_3 : subd3_7 [1] = true := by decide +kernel
theorem subd3_7_4 : subd3_7 [2] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_cons.2 ⟨subd3_7_3, List.forall_mem_cons.2 ⟨subd3_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_8 : ldCheck G d3_8.U d3_8.ms ldd3_8 = true := by decide +kernel
theorem pre_okd3_8 : subPre G cell3 d3_8 = true := by decide +kernel
theorem subd3_8_0 : subd3_8 [-1] = true := by decide +kernel
theorem subd3_8_1 : subd3_8 [0, -2] = true := by decide +kernel
theorem subd3_8_2 : subd3_8 [0, -1] = true := by decide +kernel
theorem subd3_8_3 : subd3_8 [0, 0] = true := by decide +kernel
theorem subd3_8_4 : subd3_8 [0, 1] = true := by decide +kernel
theorem subd3_8_5 : subd3_8 [1] = true := by decide +kernel
theorem sbd3_8_0 : ∀ q ∈ blkd3_8_0, subd3_8 q = true := by
  unfold blkd3_8_0
  exact List.forall_mem_cons.2 ⟨subd3_8_0, List.forall_mem_cons.2 ⟨subd3_8_1, List.forall_mem_cons.2 ⟨subd3_8_2, List.forall_mem_cons.2 ⟨subd3_8_3, List.forall_mem_cons.2 ⟨subd3_8_4, List.forall_mem_cons.2 ⟨subd3_8_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd3_9 : ldCheck G d3_9.U d3_9.ms ldd3_9 = true := by decide +kernel
theorem pre_okd3_9 : subPre G cell3 d3_9 = true := by decide +kernel
theorem subd3_9_0 : subd3_9 [-2] = true := by decide +kernel
theorem subd3_9_1 : subd3_9 [-1] = true := by decide +kernel
theorem subd3_9_2 : subd3_9 [0, -3] = true := by decide +kernel
theorem subd3_9_3 : subd3_9 [0, -2] = true := by decide +kernel
theorem subd3_9_4 : subd3_9 [0, -1] = true := by decide +kernel
theorem subd3_9_5 : subd3_9 [0, 0] = true := by decide +kernel
theorem subd3_9_6 : subd3_9 [0, 1] = true := by decide +kernel
theorem subd3_9_7 : subd3_9 [0, 2] = true := by decide +kernel
theorem subd3_9_8 : subd3_9 [1] = true := by decide +kernel
theorem subd3_9_9 : subd3_9 [2] = true := by decide +kernel
theorem sbd3_9_0 : ∀ q ∈ blkd3_9_0, subd3_9 q = true := by
  unfold blkd3_9_0
  exact List.forall_mem_cons.2 ⟨subd3_9_0, List.forall_mem_cons.2 ⟨subd3_9_1, List.forall_mem_cons.2 ⟨subd3_9_2, List.forall_mem_cons.2 ⟨subd3_9_3, List.forall_mem_cons.2 ⟨subd3_9_4, List.forall_mem_cons.2 ⟨subd3_9_5, List.forall_mem_cons.2 ⟨subd3_9_6, List.forall_mem_cons.2 ⟨subd3_9_7, List.forall_mem_cons.2 ⟨subd3_9_8, List.forall_mem_cons.2 ⟨subd3_9_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
