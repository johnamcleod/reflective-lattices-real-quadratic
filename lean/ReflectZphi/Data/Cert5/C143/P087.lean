import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd29_2_0 : subd29_2 [-2] = true := by decide +kernel
theorem subd29_2_1 : subd29_2 [-1] = true := by decide +kernel
theorem subd29_2_2 : subd29_2 [0] = true := by decide +kernel
theorem subd29_2_3 : subd29_2 [1] = true := by decide +kernel
theorem subd29_2_4 : subd29_2 [2] = true := by decide +kernel
theorem sbd29_2_0 : ∀ q ∈ blkd29_2_0, subd29_2 q = true := by
  unfold blkd29_2_0
  exact List.forall_mem_cons.2 ⟨subd29_2_0, List.forall_mem_cons.2 ⟨subd29_2_1, List.forall_mem_cons.2 ⟨subd29_2_2, List.forall_mem_cons.2 ⟨subd29_2_3, List.forall_mem_cons.2 ⟨subd29_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd29_3 : ldCheck G d29_3.U d29_3.ms ldd29_3 = true := by decide +kernel
theorem pre_okd29_3 : subPre G cell29 d29_3 = true := by decide +kernel
theorem subd29_3_0 : subd29_3 [-2] = true := by decide +kernel
theorem subd29_3_1 : subd29_3 [-1, -3] = true := by decide +kernel
theorem subd29_3_2 : subd29_3 [-1, -2] = true := by decide +kernel
theorem subd29_3_3 : subd29_3 [-1, -1] = true := by decide +kernel
theorem subd29_3_4 : subd29_3 [-1, 0] = true := by decide +kernel
theorem subd29_3_5 : subd29_3 [-1, 1] = true := by decide +kernel
theorem subd29_3_6 : subd29_3 [-1, 2] = true := by decide +kernel
theorem subd29_3_7 : subd29_3 [0, -3] = true := by decide +kernel
theorem subd29_3_8 : subd29_3 [0, -2] = true := by decide +kernel
theorem subd29_3_9 : subd29_3 [0, -1] = true := by decide +kernel
theorem subd29_3_10 : subd29_3 [0, 0] = true := by decide +kernel
theorem subd29_3_11 : subd29_3 [0, 1] = true := by decide +kernel
theorem subd29_3_12 : subd29_3 [0, 2] = true := by decide +kernel
theorem subd29_3_13 : subd29_3 [1, -3] = true := by decide +kernel
theorem subd29_3_14 : subd29_3 [1, -2] = true := by decide +kernel
theorem subd29_3_15 : subd29_3 [1, -1] = true := by decide +kernel
theorem subd29_3_16 : subd29_3 [1, 0] = true := by decide +kernel
theorem subd29_3_17 : subd29_3 [1, 1] = true := by decide +kernel
theorem subd29_3_18 : subd29_3 [1, 2] = true := by decide +kernel
theorem subd29_3_19 : subd29_3 [2] = true := by decide +kernel
theorem sbd29_3_0 : ∀ q ∈ blkd29_3_0, subd29_3 q = true := by
  unfold blkd29_3_0
  exact List.forall_mem_cons.2 ⟨subd29_3_0, List.forall_mem_cons.2 ⟨subd29_3_1, List.forall_mem_cons.2 ⟨subd29_3_2, List.forall_mem_cons.2 ⟨subd29_3_3, List.forall_mem_cons.2 ⟨subd29_3_4, List.forall_mem_cons.2 ⟨subd29_3_5, List.forall_mem_cons.2 ⟨subd29_3_6, List.forall_mem_cons.2 ⟨subd29_3_7, List.forall_mem_cons.2 ⟨subd29_3_8, List.forall_mem_cons.2 ⟨subd29_3_9, List.forall_mem_cons.2 ⟨subd29_3_10, List.forall_mem_cons.2 ⟨subd29_3_11, List.forall_mem_cons.2 ⟨subd29_3_12, List.forall_mem_cons.2 ⟨subd29_3_13, List.forall_mem_cons.2 ⟨subd29_3_14, List.forall_mem_cons.2 ⟨subd29_3_15, List.forall_mem_cons.2 ⟨subd29_3_16, List.forall_mem_cons.2 ⟨subd29_3_17, List.forall_mem_cons.2 ⟨subd29_3_18, List.forall_mem_cons.2 ⟨subd29_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd30_0 : ldCheck G d30_0.U d30_0.ms ldd30_0 = true := by decide +kernel
theorem pre_okd30_0 : subPre G cell30 d30_0 = true := by decide +kernel
theorem subd30_0_0 : subd30_0 [-1] = true := by decide +kernel
theorem subd30_0_1 : subd30_0 [0, -2] = true := by decide +kernel
theorem subd30_0_2 : subd30_0 [0, -1] = true := by decide +kernel
theorem subd30_0_3 : subd30_0 [0, 0] = true := by decide +kernel
theorem subd30_0_4 : subd30_0 [0, 1] = true := by decide +kernel
theorem subd30_0_5 : subd30_0 [1] = true := by decide +kernel
theorem sbd30_0_0 : ∀ q ∈ blkd30_0_0, subd30_0 q = true := by
  unfold blkd30_0_0
  exact List.forall_mem_cons.2 ⟨subd30_0_0, List.forall_mem_cons.2 ⟨subd30_0_1, List.forall_mem_cons.2 ⟨subd30_0_2, List.forall_mem_cons.2 ⟨subd30_0_3, List.forall_mem_cons.2 ⟨subd30_0_4, List.forall_mem_cons.2 ⟨subd30_0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd30_1 : ldCheck G d30_1.U d30_1.ms ldd30_1 = true := by decide +kernel
theorem pre_okd30_1 : subPre G cell30 d30_1 = true := by decide +kernel
theorem subd30_1_0 : subd30_1 [-2] = true := by decide +kernel
theorem subd30_1_1 : subd30_1 [-1, -3] = true := by decide +kernel
theorem subd30_1_2 : subd30_1 [-1, -2] = true := by decide +kernel
theorem subd30_1_3 : subd30_1 [-1, -1] = true := by decide +kernel
theorem subd30_1_4 : subd30_1 [-1, 0] = true := by decide +kernel
theorem subd30_1_5 : subd30_1 [-1, 1] = true := by decide +kernel
theorem subd30_1_6 : subd30_1 [-1, 2] = true := by decide +kernel
theorem subd30_1_7 : subd30_1 [-1, 3] = true := by decide +kernel
theorem subd30_1_8 : subd30_1 [0, -4] = true := by decide +kernel
theorem subd30_1_9 : subd30_1 [0, -3] = true := by decide +kernel
theorem subd30_1_10 : subd30_1 [0, -2] = true := by decide +kernel
theorem subd30_1_11 : subd30_1 [0, -1] = true := by decide +kernel
theorem subd30_1_12 : subd30_1 [0, 0] = true := by decide +kernel
theorem subd30_1_13 : subd30_1 [0, 1] = true := by decide +kernel
theorem subd30_1_14 : subd30_1 [0, 2] = true := by decide +kernel
theorem subd30_1_15 : subd30_1 [0, 3] = true := by decide +kernel
theorem subd30_1_16 : subd30_1 [1, -4] = true := by decide +kernel
theorem subd30_1_17 : subd30_1 [1, -3] = true := by decide +kernel
theorem subd30_1_18 : subd30_1 [1, -2] = true := by decide +kernel
theorem subd30_1_19 : subd30_1 [1, -1] = true := by decide +kernel
theorem subd30_1_20 : subd30_1 [1, 0] = true := by decide +kernel
theorem subd30_1_21 : subd30_1 [1, 1] = true := by decide +kernel
theorem subd30_1_22 : subd30_1 [1, 2] = true := by decide +kernel
theorem subd30_1_23 : subd30_1 [2] = true := by decide +kernel
theorem sbd30_1_0 : ∀ q ∈ blkd30_1_0, subd30_1 q = true := by
  unfold blkd30_1_0
  exact List.forall_mem_cons.2 ⟨subd30_1_0, List.forall_mem_cons.2 ⟨subd30_1_1, List.forall_mem_cons.2 ⟨subd30_1_2, List.forall_mem_cons.2 ⟨subd30_1_3, List.forall_mem_cons.2 ⟨subd30_1_4, List.forall_mem_cons.2 ⟨subd30_1_5, List.forall_mem_cons.2 ⟨subd30_1_6, List.forall_mem_cons.2 ⟨subd30_1_7, List.forall_mem_cons.2 ⟨subd30_1_8, List.forall_mem_cons.2 ⟨subd30_1_9, List.forall_mem_cons.2 ⟨subd30_1_10, List.forall_mem_cons.2 ⟨subd30_1_11, List.forall_mem_cons.2 ⟨subd30_1_12, List.forall_mem_cons.2 ⟨subd30_1_13, List.forall_mem_cons.2 ⟨subd30_1_14, List.forall_mem_cons.2 ⟨subd30_1_15, List.forall_mem_cons.2 ⟨subd30_1_16, List.forall_mem_cons.2 ⟨subd30_1_17, List.forall_mem_cons.2 ⟨subd30_1_18, List.forall_mem_cons.2 ⟨subd30_1_19, List.forall_mem_cons.2 ⟨subd30_1_20, List.forall_mem_cons.2 ⟨subd30_1_21, List.forall_mem_cons.2 ⟨subd30_1_22, List.forall_mem_cons.2 ⟨subd30_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd30_2 : ldCheck G d30_2.U d30_2.ms ldd30_2 = true := by decide +kernel
theorem pre_okd30_2 : subPre G cell30 d30_2 = true := by decide +kernel
theorem subd30_2_0 : subd30_2 [-2] = true := by decide +kernel
theorem subd30_2_1 : subd30_2 [-1] = true := by decide +kernel
theorem subd30_2_2 : subd30_2 [0, -3] = true := by decide +kernel
theorem subd30_2_3 : subd30_2 [0, -2] = true := by decide +kernel
theorem subd30_2_4 : subd30_2 [0, -1] = true := by decide +kernel
theorem subd30_2_5 : subd30_2 [0, 0] = true := by decide +kernel
theorem subd30_2_6 : subd30_2 [0, 1] = true := by decide +kernel
theorem subd30_2_7 : subd30_2 [0, 2] = true := by decide +kernel
theorem subd30_2_8 : subd30_2 [1] = true := by decide +kernel
theorem subd30_2_9 : subd30_2 [2] = true := by decide +kernel
theorem sbd30_2_0 : ∀ q ∈ blkd30_2_0, subd30_2 q = true := by
  unfold blkd30_2_0
  exact List.forall_mem_cons.2 ⟨subd30_2_0, List.forall_mem_cons.2 ⟨subd30_2_1, List.forall_mem_cons.2 ⟨subd30_2_2, List.forall_mem_cons.2 ⟨subd30_2_3, List.forall_mem_cons.2 ⟨subd30_2_4, List.forall_mem_cons.2 ⟨subd30_2_5, List.forall_mem_cons.2 ⟨subd30_2_6, List.forall_mem_cons.2 ⟨subd30_2_7, List.forall_mem_cons.2 ⟨subd30_2_8, List.forall_mem_cons.2 ⟨subd30_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd30_3 : ldCheck G d30_3.U d30_3.ms ldd30_3 = true := by decide +kernel
theorem pre_okd30_3 : subPre G cell30 d30_3 = true := by decide +kernel
theorem subd30_3_0 : subd30_3 [-2] = true := by decide +kernel
theorem subd30_3_1 : subd30_3 [-1, -3] = true := by decide +kernel
theorem subd30_3_2 : subd30_3 [-1, -2] = true := by decide +kernel
theorem subd30_3_3 : subd30_3 [-1, -1] = true := by decide +kernel
theorem subd30_3_4 : subd30_3 [-1, 0] = true := by decide +kernel
theorem subd30_3_5 : subd30_3 [-1, 1] = true := by decide +kernel
theorem subd30_3_6 : subd30_3 [-1, 2] = true := by decide +kernel
theorem subd30_3_7 : subd30_3 [0, -3] = true := by decide +kernel
theorem subd30_3_8 : subd30_3 [0, -2] = true := by decide +kernel
theorem subd30_3_9 : subd30_3 [0, -1] = true := by decide +kernel
theorem subd30_3_10 : subd30_3 [0, 0] = true := by decide +kernel
theorem subd30_3_11 : subd30_3 [0, 1] = true := by decide +kernel
theorem subd30_3_12 : subd30_3 [0, 2] = true := by decide +kernel
theorem subd30_3_13 : subd30_3 [1, -3] = true := by decide +kernel
theorem subd30_3_14 : subd30_3 [1, -2] = true := by decide +kernel
theorem subd30_3_15 : subd30_3 [1, -1] = true := by decide +kernel
theorem subd30_3_16 : subd30_3 [1, 0] = true := by decide +kernel
theorem subd30_3_17 : subd30_3 [1, 1] = true := by decide +kernel
theorem subd30_3_18 : subd30_3 [1, 2] = true := by decide +kernel
theorem subd30_3_19 : subd30_3 [2] = true := by decide +kernel
theorem sbd30_3_0 : ∀ q ∈ blkd30_3_0, subd30_3 q = true := by
  unfold blkd30_3_0
  exact List.forall_mem_cons.2 ⟨subd30_3_0, List.forall_mem_cons.2 ⟨subd30_3_1, List.forall_mem_cons.2 ⟨subd30_3_2, List.forall_mem_cons.2 ⟨subd30_3_3, List.forall_mem_cons.2 ⟨subd30_3_4, List.forall_mem_cons.2 ⟨subd30_3_5, List.forall_mem_cons.2 ⟨subd30_3_6, List.forall_mem_cons.2 ⟨subd30_3_7, List.forall_mem_cons.2 ⟨subd30_3_8, List.forall_mem_cons.2 ⟨subd30_3_9, List.forall_mem_cons.2 ⟨subd30_3_10, List.forall_mem_cons.2 ⟨subd30_3_11, List.forall_mem_cons.2 ⟨subd30_3_12, List.forall_mem_cons.2 ⟨subd30_3_13, List.forall_mem_cons.2 ⟨subd30_3_14, List.forall_mem_cons.2 ⟨subd30_3_15, List.forall_mem_cons.2 ⟨subd30_3_16, List.forall_mem_cons.2 ⟨subd30_3_17, List.forall_mem_cons.2 ⟨subd30_3_18, List.forall_mem_cons.2 ⟨subd30_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
