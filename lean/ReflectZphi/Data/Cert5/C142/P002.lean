import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_nil _⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-2] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [0, -1] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [1, -3] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [2] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_nil _⟩
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
theorem subd4_2_0 : subd4_2 [-2] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-1, 3] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [0, -4] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [0, 0] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [0, 3] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [1, -4] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [2] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C142
