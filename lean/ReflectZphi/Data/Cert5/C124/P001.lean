import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_8_0 : subd0_8 [-2] = true := by decide +kernel
theorem subd0_8_1 : subd0_8 [-1] = true := by decide +kernel
theorem subd0_8_2 : subd0_8 [0] = true := by decide +kernel
theorem subd0_8_3 : subd0_8 [1] = true := by decide +kernel
theorem subd0_8_4 : subd0_8 [2] = true := by decide +kernel
theorem sbd0_8_0 : ∀ q ∈ blkd0_8_0, subd0_8 q = true := by
  unfold blkd0_8_0
  exact List.forall_mem_cons.2 ⟨subd0_8_0, List.forall_mem_cons.2 ⟨subd0_8_1, List.forall_mem_cons.2 ⟨subd0_8_2, List.forall_mem_cons.2 ⟨subd0_8_3, List.forall_mem_cons.2 ⟨subd0_8_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_9 : ldCheck G d0_9.U d0_9.ms ldd0_9 = true := by decide +kernel
theorem pre_okd0_9 : subPre G cell0 d0_9 = true := by decide +kernel
theorem subd0_9_0 : subd0_9 [-2] = true := by decide +kernel
theorem subd0_9_1 : subd0_9 [-1, -3] = true := by decide +kernel
theorem subd0_9_2 : subd0_9 [-1, -2] = true := by decide +kernel
theorem subd0_9_3 : subd0_9 [-1, -1] = true := by decide +kernel
theorem subd0_9_4 : subd0_9 [-1, 0] = true := by decide +kernel
theorem subd0_9_5 : subd0_9 [-1, 1] = true := by decide +kernel
theorem subd0_9_6 : subd0_9 [-1, 2] = true := by decide +kernel
theorem subd0_9_7 : subd0_9 [-1, 3] = true := by decide +kernel
theorem subd0_9_8 : subd0_9 [0, -4] = true := by decide +kernel
theorem subd0_9_9 : subd0_9 [0, -3] = true := by decide +kernel
theorem subd0_9_10 : subd0_9 [0, -2] = true := by decide +kernel
theorem subd0_9_11 : subd0_9 [0, -1] = true := by decide +kernel
theorem subd0_9_12 : subd0_9 [0, 0] = true := by decide +kernel
theorem subd0_9_13 : subd0_9 [0, 1] = true := by decide +kernel
theorem subd0_9_14 : subd0_9 [0, 2] = true := by decide +kernel
theorem subd0_9_15 : subd0_9 [0, 3] = true := by decide +kernel
theorem subd0_9_16 : subd0_9 [1, -4] = true := by decide +kernel
theorem subd0_9_17 : subd0_9 [1, -3] = true := by decide +kernel
theorem subd0_9_18 : subd0_9 [1, -2] = true := by decide +kernel
theorem subd0_9_19 : subd0_9 [1, -1] = true := by decide +kernel
theorem subd0_9_20 : subd0_9 [1, 0] = true := by decide +kernel
theorem subd0_9_21 : subd0_9 [1, 1] = true := by decide +kernel
theorem subd0_9_22 : subd0_9 [1, 2] = true := by decide +kernel
theorem subd0_9_23 : subd0_9 [2] = true := by decide +kernel
theorem sbd0_9_0 : ∀ q ∈ blkd0_9_0, subd0_9 q = true := by
  unfold blkd0_9_0
  exact List.forall_mem_cons.2 ⟨subd0_9_0, List.forall_mem_cons.2 ⟨subd0_9_1, List.forall_mem_cons.2 ⟨subd0_9_2, List.forall_mem_cons.2 ⟨subd0_9_3, List.forall_mem_cons.2 ⟨subd0_9_4, List.forall_mem_cons.2 ⟨subd0_9_5, List.forall_mem_cons.2 ⟨subd0_9_6, List.forall_mem_cons.2 ⟨subd0_9_7, List.forall_mem_cons.2 ⟨subd0_9_8, List.forall_mem_cons.2 ⟨subd0_9_9, List.forall_mem_cons.2 ⟨subd0_9_10, List.forall_mem_cons.2 ⟨subd0_9_11, List.forall_mem_cons.2 ⟨subd0_9_12, List.forall_mem_cons.2 ⟨subd0_9_13, List.forall_mem_cons.2 ⟨subd0_9_14, List.forall_mem_cons.2 ⟨subd0_9_15, List.forall_mem_cons.2 ⟨subd0_9_16, List.forall_mem_cons.2 ⟨subd0_9_17, List.forall_mem_cons.2 ⟨subd0_9_18, List.forall_mem_cons.2 ⟨subd0_9_19, List.forall_mem_cons.2 ⟨subd0_9_20, List.forall_mem_cons.2 ⟨subd0_9_21, List.forall_mem_cons.2 ⟨subd0_9_22, List.forall_mem_cons.2 ⟨subd0_9_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_10 : ldCheck G d0_10.U d0_10.ms ldd0_10 = true := by decide +kernel
theorem pre_okd0_10 : subPre G cell0 d0_10 = true := by decide +kernel
theorem subd0_10_0 : subd0_10 [-2] = true := by decide +kernel
theorem subd0_10_1 : subd0_10 [-1] = true := by decide +kernel
theorem subd0_10_2 : subd0_10 [0] = true := by decide +kernel
theorem subd0_10_3 : subd0_10 [1] = true := by decide +kernel
theorem subd0_10_4 : subd0_10 [2] = true := by decide +kernel
theorem sbd0_10_0 : ∀ q ∈ blkd0_10_0, subd0_10 q = true := by
  unfold blkd0_10_0
  exact List.forall_mem_cons.2 ⟨subd0_10_0, List.forall_mem_cons.2 ⟨subd0_10_1, List.forall_mem_cons.2 ⟨subd0_10_2, List.forall_mem_cons.2 ⟨subd0_10_3, List.forall_mem_cons.2 ⟨subd0_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_11 : ldCheck G d0_11.U d0_11.ms ldd0_11 = true := by decide +kernel
theorem pre_okd0_11 : subPre G cell0 d0_11 = true := by decide +kernel
theorem subd0_11_0 : subd0_11 [-2] = true := by decide +kernel
theorem subd0_11_1 : subd0_11 [-1] = true := by decide +kernel
theorem subd0_11_2 : subd0_11 [0] = true := by decide +kernel
theorem subd0_11_3 : subd0_11 [1] = true := by decide +kernel
theorem subd0_11_4 : subd0_11 [2] = true := by decide +kernel
theorem sbd0_11_0 : ∀ q ∈ blkd0_11_0, subd0_11 q = true := by
  unfold blkd0_11_0
  exact List.forall_mem_cons.2 ⟨subd0_11_0, List.forall_mem_cons.2 ⟨subd0_11_1, List.forall_mem_cons.2 ⟨subd0_11_2, List.forall_mem_cons.2 ⟨subd0_11_3, List.forall_mem_cons.2 ⟨subd0_11_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_12 : ldCheck G d0_12.U d0_12.ms ldd0_12 = true := by decide +kernel
theorem pre_okd0_12 : subPre G cell0 d0_12 = true := by decide +kernel
theorem subd0_12_0 : subd0_12 [] = true := by decide +kernel
theorem sbd0_12_0 : ∀ q ∈ blkd0_12_0, subd0_12 q = true := by
  unfold blkd0_12_0
  exact List.forall_mem_cons.2 ⟨subd0_12_0, List.forall_mem_nil _⟩
theorem ld_okd0_13 : ldCheck G d0_13.U d0_13.ms ldd0_13 = true := by decide +kernel
theorem pre_okd0_13 : subPre G cell0 d0_13 = true := by decide +kernel
theorem subd0_13_0 : subd0_13 [] = true := by decide +kernel
theorem sbd0_13_0 : ∀ q ∈ blkd0_13_0, subd0_13 q = true := by
  unfold blkd0_13_0
  exact List.forall_mem_cons.2 ⟨subd0_13_0, List.forall_mem_nil _⟩
theorem ld_okd0_14 : ldCheck G d0_14.U d0_14.ms ldd0_14 = true := by decide +kernel
theorem pre_okd0_14 : subPre G cell0 d0_14 = true := by decide +kernel
theorem subd0_14_0 : subd0_14 [-1] = true := by decide +kernel
theorem subd0_14_1 : subd0_14 [0] = true := by decide +kernel
theorem subd0_14_2 : subd0_14 [1] = true := by decide +kernel
theorem sbd0_14_0 : ∀ q ∈ blkd0_14_0, subd0_14 q = true := by
  unfold blkd0_14_0
  exact List.forall_mem_cons.2 ⟨subd0_14_0, List.forall_mem_cons.2 ⟨subd0_14_1, List.forall_mem_cons.2 ⟨subd0_14_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C124
