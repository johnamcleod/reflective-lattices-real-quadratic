import ReflectZphi.Data.Cert5.C061.Base

namespace ReflectZphi.Data.Cert5.C061

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_nil _⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [-3] = true := by decide +kernel
theorem subd2_0_1 : subd2_0 [-2] = true := by decide +kernel
theorem subd2_0_2 : subd2_0 [-1, -4] = true := by decide +kernel
theorem subd2_0_3 : subd2_0 [-1, -3] = true := by decide +kernel
theorem subd2_0_4 : subd2_0 [-1, -2] = true := by decide +kernel
theorem subd2_0_5 : subd2_0 [-1, -1] = true := by decide +kernel
theorem subd2_0_6 : subd2_0 [-1, 0] = true := by decide +kernel
theorem subd2_0_7 : subd2_0 [-1, 1] = true := by decide +kernel
theorem subd2_0_8 : subd2_0 [-1, 2] = true := by decide +kernel
theorem subd2_0_9 : subd2_0 [-1, 3] = true := by decide +kernel
theorem subd2_0_10 : subd2_0 [0, -4] = true := by decide +kernel
theorem subd2_0_11 : subd2_0 [0, -3] = true := by decide +kernel
theorem subd2_0_12 : subd2_0 [0, -2] = true := by decide +kernel
theorem subd2_0_13 : subd2_0 [0, -1] = true := by decide +kernel
theorem subd2_0_14 : subd2_0 [0, 0] = true := by decide +kernel
theorem subd2_0_15 : subd2_0 [0, 1] = true := by decide +kernel
theorem subd2_0_16 : subd2_0 [0, 2] = true := by decide +kernel
theorem subd2_0_17 : subd2_0 [0, 3] = true := by decide +kernel
theorem subd2_0_18 : subd2_0 [1, -4] = true := by decide +kernel
theorem subd2_0_19 : subd2_0 [1, -3] = true := by decide +kernel
theorem subd2_0_20 : subd2_0 [1, -2] = true := by decide +kernel
theorem subd2_0_21 : subd2_0 [1, -1] = true := by decide +kernel
theorem subd2_0_22 : subd2_0 [1, 0] = true := by decide +kernel
theorem subd2_0_23 : subd2_0 [1, 1] = true := by decide +kernel
theorem subd2_0_24 : subd2_0 [1, 2] = true := by decide +kernel
theorem subd2_0_25 : subd2_0 [1, 3] = true := by decide +kernel
theorem subd2_0_26 : subd2_0 [2] = true := by decide +kernel
theorem subd2_0_27 : subd2_0 [3] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_cons.2 ⟨subd2_0_1, List.forall_mem_cons.2 ⟨subd2_0_2, List.forall_mem_cons.2 ⟨subd2_0_3, List.forall_mem_cons.2 ⟨subd2_0_4, List.forall_mem_cons.2 ⟨subd2_0_5, List.forall_mem_cons.2 ⟨subd2_0_6, List.forall_mem_cons.2 ⟨subd2_0_7, List.forall_mem_cons.2 ⟨subd2_0_8, List.forall_mem_cons.2 ⟨subd2_0_9, List.forall_mem_cons.2 ⟨subd2_0_10, List.forall_mem_cons.2 ⟨subd2_0_11, List.forall_mem_cons.2 ⟨subd2_0_12, List.forall_mem_cons.2 ⟨subd2_0_13, List.forall_mem_cons.2 ⟨subd2_0_14, List.forall_mem_cons.2 ⟨subd2_0_15, List.forall_mem_cons.2 ⟨subd2_0_16, List.forall_mem_cons.2 ⟨subd2_0_17, List.forall_mem_cons.2 ⟨subd2_0_18, List.forall_mem_cons.2 ⟨subd2_0_19, List.forall_mem_cons.2 ⟨subd2_0_20, List.forall_mem_cons.2 ⟨subd2_0_21, List.forall_mem_cons.2 ⟨subd2_0_22, List.forall_mem_cons.2 ⟨subd2_0_23, List.forall_mem_cons.2 ⟨subd2_0_24, List.forall_mem_cons.2 ⟨subd2_0_25, List.forall_mem_cons.2 ⟨subd2_0_26, List.forall_mem_cons.2 ⟨subd2_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [-3] = true := by decide +kernel
theorem subd2_1_1 : subd2_1 [-2] = true := by decide +kernel
theorem subd2_1_2 : subd2_1 [-1, -4] = true := by decide +kernel
theorem subd2_1_3 : subd2_1 [-1, -3] = true := by decide +kernel
theorem subd2_1_4 : subd2_1 [-1, -2] = true := by decide +kernel
theorem subd2_1_5 : subd2_1 [-1, -1] = true := by decide +kernel
theorem subd2_1_6 : subd2_1 [-1, 0] = true := by decide +kernel
theorem subd2_1_7 : subd2_1 [-1, 1] = true := by decide +kernel
theorem subd2_1_8 : subd2_1 [-1, 2] = true := by decide +kernel
theorem subd2_1_9 : subd2_1 [-1, 3] = true := by decide +kernel
theorem subd2_1_10 : subd2_1 [0, -4] = true := by decide +kernel
theorem subd2_1_11 : subd2_1 [0, -3] = true := by decide +kernel
theorem subd2_1_12 : subd2_1 [0, -2] = true := by decide +kernel
theorem subd2_1_13 : subd2_1 [0, -1] = true := by decide +kernel
theorem subd2_1_14 : subd2_1 [0, 0] = true := by decide +kernel
theorem subd2_1_15 : subd2_1 [0, 1] = true := by decide +kernel
theorem subd2_1_16 : subd2_1 [0, 2] = true := by decide +kernel
theorem subd2_1_17 : subd2_1 [0, 3] = true := by decide +kernel
theorem subd2_1_18 : subd2_1 [1, -4] = true := by decide +kernel
theorem subd2_1_19 : subd2_1 [1, -3] = true := by decide +kernel
theorem subd2_1_20 : subd2_1 [1, -2] = true := by decide +kernel
theorem subd2_1_21 : subd2_1 [1, -1] = true := by decide +kernel
theorem subd2_1_22 : subd2_1 [1, 0] = true := by decide +kernel
theorem subd2_1_23 : subd2_1 [1, 1] = true := by decide +kernel
theorem subd2_1_24 : subd2_1 [1, 2] = true := by decide +kernel
theorem subd2_1_25 : subd2_1 [1, 3] = true := by decide +kernel
theorem subd2_1_26 : subd2_1 [2] = true := by decide +kernel
theorem subd2_1_27 : subd2_1 [3] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_cons.2 ⟨subd2_1_1, List.forall_mem_cons.2 ⟨subd2_1_2, List.forall_mem_cons.2 ⟨subd2_1_3, List.forall_mem_cons.2 ⟨subd2_1_4, List.forall_mem_cons.2 ⟨subd2_1_5, List.forall_mem_cons.2 ⟨subd2_1_6, List.forall_mem_cons.2 ⟨subd2_1_7, List.forall_mem_cons.2 ⟨subd2_1_8, List.forall_mem_cons.2 ⟨subd2_1_9, List.forall_mem_cons.2 ⟨subd2_1_10, List.forall_mem_cons.2 ⟨subd2_1_11, List.forall_mem_cons.2 ⟨subd2_1_12, List.forall_mem_cons.2 ⟨subd2_1_13, List.forall_mem_cons.2 ⟨subd2_1_14, List.forall_mem_cons.2 ⟨subd2_1_15, List.forall_mem_cons.2 ⟨subd2_1_16, List.forall_mem_cons.2 ⟨subd2_1_17, List.forall_mem_cons.2 ⟨subd2_1_18, List.forall_mem_cons.2 ⟨subd2_1_19, List.forall_mem_cons.2 ⟨subd2_1_20, List.forall_mem_cons.2 ⟨subd2_1_21, List.forall_mem_cons.2 ⟨subd2_1_22, List.forall_mem_cons.2 ⟨subd2_1_23, List.forall_mem_cons.2 ⟨subd2_1_24, List.forall_mem_cons.2 ⟨subd2_1_25, List.forall_mem_cons.2 ⟨subd2_1_26, List.forall_mem_cons.2 ⟨subd2_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [-2] = true := by decide +kernel
theorem subd2_2_1 : subd2_2 [-1] = true := by decide +kernel
theorem subd2_2_2 : subd2_2 [0] = true := by decide +kernel
theorem subd2_2_3 : subd2_2 [1] = true := by decide +kernel
theorem subd2_2_4 : subd2_2 [2] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_cons.2 ⟨subd2_2_1, List.forall_mem_cons.2 ⟨subd2_2_2, List.forall_mem_cons.2 ⟨subd2_2_3, List.forall_mem_cons.2 ⟨subd2_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [-1] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [0] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [1] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C061
