import ReflectZphi.Data.Cert5.C117.Base

namespace ReflectZphi.Data.Cert5.C117

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [-3] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [-2] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [-1, -3] = true := by decide +kernel
theorem subd1_2_3 : subd1_2 [-1, -2] = true := by decide +kernel
theorem subd1_2_4 : subd1_2 [-1, -1] = true := by decide +kernel
theorem subd1_2_5 : subd1_2 [-1, 0] = true := by decide +kernel
theorem subd1_2_6 : subd1_2 [-1, 1] = true := by decide +kernel
theorem subd1_2_7 : subd1_2 [-1, 2] = true := by decide +kernel
theorem subd1_2_8 : subd1_2 [0, -3] = true := by decide +kernel
theorem subd1_2_9 : subd1_2 [0, -2] = true := by decide +kernel
theorem subd1_2_10 : subd1_2 [0, -1] = true := by decide +kernel
theorem subd1_2_11 : subd1_2 [0, 0] = true := by decide +kernel
theorem subd1_2_12 : subd1_2 [0, 1] = true := by decide +kernel
theorem subd1_2_13 : subd1_2 [0, 2] = true := by decide +kernel
theorem subd1_2_14 : subd1_2 [1, -3] = true := by decide +kernel
theorem subd1_2_15 : subd1_2 [1, -2] = true := by decide +kernel
theorem subd1_2_16 : subd1_2 [1, -1] = true := by decide +kernel
theorem subd1_2_17 : subd1_2 [1, 0] = true := by decide +kernel
theorem subd1_2_18 : subd1_2 [1, 1] = true := by decide +kernel
theorem subd1_2_19 : subd1_2 [1, 2] = true := by decide +kernel
theorem subd1_2_20 : subd1_2 [2] = true := by decide +kernel
theorem subd1_2_21 : subd1_2 [3] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_cons.2 ⟨subd1_2_3, List.forall_mem_cons.2 ⟨subd1_2_4, List.forall_mem_cons.2 ⟨subd1_2_5, List.forall_mem_cons.2 ⟨subd1_2_6, List.forall_mem_cons.2 ⟨subd1_2_7, List.forall_mem_cons.2 ⟨subd1_2_8, List.forall_mem_cons.2 ⟨subd1_2_9, List.forall_mem_cons.2 ⟨subd1_2_10, List.forall_mem_cons.2 ⟨subd1_2_11, List.forall_mem_cons.2 ⟨subd1_2_12, List.forall_mem_cons.2 ⟨subd1_2_13, List.forall_mem_cons.2 ⟨subd1_2_14, List.forall_mem_cons.2 ⟨subd1_2_15, List.forall_mem_cons.2 ⟨subd1_2_16, List.forall_mem_cons.2 ⟨subd1_2_17, List.forall_mem_cons.2 ⟨subd1_2_18, List.forall_mem_cons.2 ⟨subd1_2_19, List.forall_mem_cons.2 ⟨subd1_2_20, List.forall_mem_cons.2 ⟨subd1_2_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-2] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-1] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [0] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [1] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [2] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [-1] = true := by decide +kernel
theorem subd2_1_1 : subd2_1 [0] = true := by decide +kernel
theorem subd2_1_2 : subd2_1 [1] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_cons.2 ⟨subd2_1_1, List.forall_mem_cons.2 ⟨subd2_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [-3] = true := by decide +kernel
theorem subd2_2_1 : subd2_2 [-2] = true := by decide +kernel
theorem subd2_2_2 : subd2_2 [-1, -3] = true := by decide +kernel
theorem subd2_2_3 : subd2_2 [-1, -2] = true := by decide +kernel
theorem subd2_2_4 : subd2_2 [-1, -1] = true := by decide +kernel
theorem subd2_2_5 : subd2_2 [-1, 0] = true := by decide +kernel
theorem subd2_2_6 : subd2_2 [-1, 1] = true := by decide +kernel
theorem subd2_2_7 : subd2_2 [-1, 2] = true := by decide +kernel
theorem subd2_2_8 : subd2_2 [-1, 3] = true := by decide +kernel
theorem subd2_2_9 : subd2_2 [0, -4] = true := by decide +kernel
theorem subd2_2_10 : subd2_2 [0, -3] = true := by decide +kernel
theorem subd2_2_11 : subd2_2 [0, -2] = true := by decide +kernel
theorem subd2_2_12 : subd2_2 [0, -1] = true := by decide +kernel
theorem subd2_2_13 : subd2_2 [0, 0] = true := by decide +kernel
theorem subd2_2_14 : subd2_2 [0, 1] = true := by decide +kernel
theorem subd2_2_15 : subd2_2 [0, 2] = true := by decide +kernel
theorem subd2_2_16 : subd2_2 [0, 3] = true := by decide +kernel
theorem subd2_2_17 : subd2_2 [1, -4] = true := by decide +kernel
theorem subd2_2_18 : subd2_2 [1, -3] = true := by decide +kernel
theorem subd2_2_19 : subd2_2 [1, -2] = true := by decide +kernel
theorem subd2_2_20 : subd2_2 [1, -1] = true := by decide +kernel
theorem subd2_2_21 : subd2_2 [1, 0] = true := by decide +kernel
theorem subd2_2_22 : subd2_2 [1, 1] = true := by decide +kernel
theorem subd2_2_23 : subd2_2 [1, 2] = true := by decide +kernel
theorem subd2_2_24 : subd2_2 [2] = true := by decide +kernel
theorem subd2_2_25 : subd2_2 [3] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_cons.2 ⟨subd2_2_1, List.forall_mem_cons.2 ⟨subd2_2_2, List.forall_mem_cons.2 ⟨subd2_2_3, List.forall_mem_cons.2 ⟨subd2_2_4, List.forall_mem_cons.2 ⟨subd2_2_5, List.forall_mem_cons.2 ⟨subd2_2_6, List.forall_mem_cons.2 ⟨subd2_2_7, List.forall_mem_cons.2 ⟨subd2_2_8, List.forall_mem_cons.2 ⟨subd2_2_9, List.forall_mem_cons.2 ⟨subd2_2_10, List.forall_mem_cons.2 ⟨subd2_2_11, List.forall_mem_cons.2 ⟨subd2_2_12, List.forall_mem_cons.2 ⟨subd2_2_13, List.forall_mem_cons.2 ⟨subd2_2_14, List.forall_mem_cons.2 ⟨subd2_2_15, List.forall_mem_cons.2 ⟨subd2_2_16, List.forall_mem_cons.2 ⟨subd2_2_17, List.forall_mem_cons.2 ⟨subd2_2_18, List.forall_mem_cons.2 ⟨subd2_2_19, List.forall_mem_cons.2 ⟨subd2_2_20, List.forall_mem_cons.2 ⟨subd2_2_21, List.forall_mem_cons.2 ⟨subd2_2_22, List.forall_mem_cons.2 ⟨subd2_2_23, List.forall_mem_cons.2 ⟨subd2_2_24, List.forall_mem_cons.2 ⟨subd2_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [-1] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [0] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [1] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C117
