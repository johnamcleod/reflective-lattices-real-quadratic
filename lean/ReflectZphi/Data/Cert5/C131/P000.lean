import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_0 : ldCheck G d0_0.U d0_0.ms ldd0_0 = true := by decide +kernel
theorem pre_okd0_0 : subPre G cell0 d0_0 = true := by decide +kernel
theorem subd0_0_0 : subd0_0 [-2] = true := by decide +kernel
theorem subd0_0_1 : subd0_0 [-1] = true := by decide +kernel
theorem subd0_0_2 : subd0_0 [0] = true := by decide +kernel
theorem subd0_0_3 : subd0_0 [1] = true := by decide +kernel
theorem subd0_0_4 : subd0_0 [2] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_cons.2 ⟨subd0_0_1, List.forall_mem_cons.2 ⟨subd0_0_2, List.forall_mem_cons.2 ⟨subd0_0_3, List.forall_mem_cons.2 ⟨subd0_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_1 : ldCheck G d0_1.U d0_1.ms ldd0_1 = true := by decide +kernel
theorem pre_okd0_1 : subPre G cell0 d0_1 = true := by decide +kernel
theorem subd0_1_0 : subd0_1 [] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_nil _⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [-2] = true := by decide +kernel
theorem subd1_0_1 : subd1_0 [-1, -3] = true := by decide +kernel
theorem subd1_0_2 : subd1_0 [-1, -2] = true := by decide +kernel
theorem subd1_0_3 : subd1_0 [-1, -1] = true := by decide +kernel
theorem subd1_0_4 : subd1_0 [-1, 0] = true := by decide +kernel
theorem subd1_0_5 : subd1_0 [-1, 1] = true := by decide +kernel
theorem subd1_0_6 : subd1_0 [-1, 2] = true := by decide +kernel
theorem subd1_0_7 : subd1_0 [-1, 3] = true := by decide +kernel
theorem subd1_0_8 : subd1_0 [0, -3] = true := by decide +kernel
theorem subd1_0_9 : subd1_0 [0, -2] = true := by decide +kernel
theorem subd1_0_10 : subd1_0 [0, -1] = true := by decide +kernel
theorem subd1_0_11 : subd1_0 [0, 0] = true := by decide +kernel
theorem subd1_0_12 : subd1_0 [0, 1] = true := by decide +kernel
theorem subd1_0_13 : subd1_0 [0, 2] = true := by decide +kernel
theorem subd1_0_14 : subd1_0 [1, -4] = true := by decide +kernel
theorem subd1_0_15 : subd1_0 [1, -3] = true := by decide +kernel
theorem subd1_0_16 : subd1_0 [1, -2] = true := by decide +kernel
theorem subd1_0_17 : subd1_0 [1, -1] = true := by decide +kernel
theorem subd1_0_18 : subd1_0 [1, 0] = true := by decide +kernel
theorem subd1_0_19 : subd1_0 [1, 1] = true := by decide +kernel
theorem subd1_0_20 : subd1_0 [1, 2] = true := by decide +kernel
theorem subd1_0_21 : subd1_0 [2] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_cons.2 ⟨subd1_0_1, List.forall_mem_cons.2 ⟨subd1_0_2, List.forall_mem_cons.2 ⟨subd1_0_3, List.forall_mem_cons.2 ⟨subd1_0_4, List.forall_mem_cons.2 ⟨subd1_0_5, List.forall_mem_cons.2 ⟨subd1_0_6, List.forall_mem_cons.2 ⟨subd1_0_7, List.forall_mem_cons.2 ⟨subd1_0_8, List.forall_mem_cons.2 ⟨subd1_0_9, List.forall_mem_cons.2 ⟨subd1_0_10, List.forall_mem_cons.2 ⟨subd1_0_11, List.forall_mem_cons.2 ⟨subd1_0_12, List.forall_mem_cons.2 ⟨subd1_0_13, List.forall_mem_cons.2 ⟨subd1_0_14, List.forall_mem_cons.2 ⟨subd1_0_15, List.forall_mem_cons.2 ⟨subd1_0_16, List.forall_mem_cons.2 ⟨subd1_0_17, List.forall_mem_cons.2 ⟨subd1_0_18, List.forall_mem_cons.2 ⟨subd1_0_19, List.forall_mem_cons.2 ⟨subd1_0_20, List.forall_mem_cons.2 ⟨subd1_0_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_nil _⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [-2] = true := by decide +kernel
theorem subd2_0_1 : subd2_0 [-1, -3] = true := by decide +kernel
theorem subd2_0_2 : subd2_0 [-1, -2] = true := by decide +kernel
theorem subd2_0_3 : subd2_0 [-1, -1] = true := by decide +kernel
theorem subd2_0_4 : subd2_0 [-1, 0] = true := by decide +kernel
theorem subd2_0_5 : subd2_0 [-1, 1] = true := by decide +kernel
theorem subd2_0_6 : subd2_0 [-1, 2] = true := by decide +kernel
theorem subd2_0_7 : subd2_0 [0, -3] = true := by decide +kernel
theorem subd2_0_8 : subd2_0 [0, -2] = true := by decide +kernel
theorem subd2_0_9 : subd2_0 [0, -1] = true := by decide +kernel
theorem subd2_0_10 : subd2_0 [0, 0] = true := by decide +kernel
theorem subd2_0_11 : subd2_0 [0, 1] = true := by decide +kernel
theorem subd2_0_12 : subd2_0 [0, 2] = true := by decide +kernel
theorem subd2_0_13 : subd2_0 [1, -3] = true := by decide +kernel
theorem subd2_0_14 : subd2_0 [1, -2] = true := by decide +kernel
theorem subd2_0_15 : subd2_0 [1, -1] = true := by decide +kernel
theorem subd2_0_16 : subd2_0 [1, 0] = true := by decide +kernel
theorem subd2_0_17 : subd2_0 [1, 1] = true := by decide +kernel
theorem subd2_0_18 : subd2_0 [1, 2] = true := by decide +kernel
theorem subd2_0_19 : subd2_0 [2] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_cons.2 ⟨subd2_0_1, List.forall_mem_cons.2 ⟨subd2_0_2, List.forall_mem_cons.2 ⟨subd2_0_3, List.forall_mem_cons.2 ⟨subd2_0_4, List.forall_mem_cons.2 ⟨subd2_0_5, List.forall_mem_cons.2 ⟨subd2_0_6, List.forall_mem_cons.2 ⟨subd2_0_7, List.forall_mem_cons.2 ⟨subd2_0_8, List.forall_mem_cons.2 ⟨subd2_0_9, List.forall_mem_cons.2 ⟨subd2_0_10, List.forall_mem_cons.2 ⟨subd2_0_11, List.forall_mem_cons.2 ⟨subd2_0_12, List.forall_mem_cons.2 ⟨subd2_0_13, List.forall_mem_cons.2 ⟨subd2_0_14, List.forall_mem_cons.2 ⟨subd2_0_15, List.forall_mem_cons.2 ⟨subd2_0_16, List.forall_mem_cons.2 ⟨subd2_0_17, List.forall_mem_cons.2 ⟨subd2_0_18, List.forall_mem_cons.2 ⟨subd2_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C131
