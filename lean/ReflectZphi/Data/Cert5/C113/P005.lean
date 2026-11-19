import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_8_0 : subd3_8 [-2] = true := by decide +kernel
theorem subd3_8_1 : subd3_8 [-1, -3] = true := by decide +kernel
theorem subd3_8_2 : subd3_8 [-1, -2] = true := by decide +kernel
theorem subd3_8_3 : subd3_8 [-1, -1] = true := by decide +kernel
theorem subd3_8_4 : subd3_8 [-1, 0] = true := by decide +kernel
theorem subd3_8_5 : subd3_8 [-1, 1] = true := by decide +kernel
theorem subd3_8_6 : subd3_8 [-1, 2] = true := by decide +kernel
theorem subd3_8_7 : subd3_8 [-1, 3] = true := by decide +kernel
theorem subd3_8_8 : subd3_8 [0, -4] = true := by decide +kernel
theorem subd3_8_9 : subd3_8 [0, -3] = true := by decide +kernel
theorem subd3_8_10 : subd3_8 [0, -2] = true := by decide +kernel
theorem subd3_8_11 : subd3_8 [0, -1] = true := by decide +kernel
theorem subd3_8_12 : subd3_8 [0, 0] = true := by decide +kernel
theorem subd3_8_13 : subd3_8 [0, 1] = true := by decide +kernel
theorem subd3_8_14 : subd3_8 [0, 2] = true := by decide +kernel
theorem subd3_8_15 : subd3_8 [0, 3] = true := by decide +kernel
theorem subd3_8_16 : subd3_8 [1, -4] = true := by decide +kernel
theorem subd3_8_17 : subd3_8 [1, -3] = true := by decide +kernel
theorem subd3_8_18 : subd3_8 [1, -2] = true := by decide +kernel
theorem subd3_8_19 : subd3_8 [1, -1] = true := by decide +kernel
theorem subd3_8_20 : subd3_8 [1, 0] = true := by decide +kernel
theorem subd3_8_21 : subd3_8 [1, 1] = true := by decide +kernel
theorem subd3_8_22 : subd3_8 [1, 2] = true := by decide +kernel
theorem subd3_8_23 : subd3_8 [2] = true := by decide +kernel
theorem sbd3_8_0 : ∀ q ∈ blkd3_8_0, subd3_8 q = true := by
  unfold blkd3_8_0
  exact List.forall_mem_cons.2 ⟨subd3_8_0, List.forall_mem_cons.2 ⟨subd3_8_1, List.forall_mem_cons.2 ⟨subd3_8_2, List.forall_mem_cons.2 ⟨subd3_8_3, List.forall_mem_cons.2 ⟨subd3_8_4, List.forall_mem_cons.2 ⟨subd3_8_5, List.forall_mem_cons.2 ⟨subd3_8_6, List.forall_mem_cons.2 ⟨subd3_8_7, List.forall_mem_cons.2 ⟨subd3_8_8, List.forall_mem_cons.2 ⟨subd3_8_9, List.forall_mem_cons.2 ⟨subd3_8_10, List.forall_mem_cons.2 ⟨subd3_8_11, List.forall_mem_cons.2 ⟨subd3_8_12, List.forall_mem_cons.2 ⟨subd3_8_13, List.forall_mem_cons.2 ⟨subd3_8_14, List.forall_mem_cons.2 ⟨subd3_8_15, List.forall_mem_cons.2 ⟨subd3_8_16, List.forall_mem_cons.2 ⟨subd3_8_17, List.forall_mem_cons.2 ⟨subd3_8_18, List.forall_mem_cons.2 ⟨subd3_8_19, List.forall_mem_cons.2 ⟨subd3_8_20, List.forall_mem_cons.2 ⟨subd3_8_21, List.forall_mem_cons.2 ⟨subd3_8_22, List.forall_mem_cons.2 ⟨subd3_8_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_9 : ldCheck G d3_9.U d3_9.ms ldd3_9 = true := by decide +kernel
theorem pre_okd3_9 : subPre G cell3 d3_9 = true := by decide +kernel
theorem subd3_9_0 : subd3_9 [] = true := by decide +kernel
theorem sbd3_9_0 : ∀ q ∈ blkd3_9_0, subd3_9 q = true := by
  unfold blkd3_9_0
  exact List.forall_mem_cons.2 ⟨subd3_9_0, List.forall_mem_nil _⟩
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

end ReflectZphi.Data.Cert5.C113
