import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_5 : ldCheck G d1_5.U d1_5.ms ldd1_5 = true := by decide +kernel
theorem pre_okd1_5 : subPre G cell1 d1_5 = true := by decide +kernel
theorem subd1_5_0 : subd1_5 [-2] = true := by decide +kernel
theorem subd1_5_1 : subd1_5 [-1] = true := by decide +kernel
theorem subd1_5_2 : subd1_5 [0, -3] = true := by decide +kernel
theorem subd1_5_3 : subd1_5 [0, -2] = true := by decide +kernel
theorem subd1_5_4 : subd1_5 [0, -1] = true := by decide +kernel
theorem subd1_5_5 : subd1_5 [0, 0] = true := by decide +kernel
theorem subd1_5_6 : subd1_5 [0, 1] = true := by decide +kernel
theorem subd1_5_7 : subd1_5 [0, 2] = true := by decide +kernel
theorem subd1_5_8 : subd1_5 [1] = true := by decide +kernel
theorem subd1_5_9 : subd1_5 [2] = true := by decide +kernel
theorem sbd1_5_0 : ∀ q ∈ blkd1_5_0, subd1_5 q = true := by
  unfold blkd1_5_0
  exact List.forall_mem_cons.2 ⟨subd1_5_0, List.forall_mem_cons.2 ⟨subd1_5_1, List.forall_mem_cons.2 ⟨subd1_5_2, List.forall_mem_cons.2 ⟨subd1_5_3, List.forall_mem_cons.2 ⟨subd1_5_4, List.forall_mem_cons.2 ⟨subd1_5_5, List.forall_mem_cons.2 ⟨subd1_5_6, List.forall_mem_cons.2 ⟨subd1_5_7, List.forall_mem_cons.2 ⟨subd1_5_8, List.forall_mem_cons.2 ⟨subd1_5_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_6 : ldCheck G d1_6.U d1_6.ms ldd1_6 = true := by decide +kernel
theorem pre_okd1_6 : subPre G cell1 d1_6 = true := by decide +kernel
theorem subd1_6_0 : subd1_6 [-3] = true := by decide +kernel
theorem subd1_6_1 : subd1_6 [-2] = true := by decide +kernel
theorem subd1_6_2 : subd1_6 [-1, -4] = true := by decide +kernel
theorem subd1_6_3 : subd1_6 [-1, -3] = true := by decide +kernel
theorem subd1_6_4 : subd1_6 [-1, -2] = true := by decide +kernel
theorem subd1_6_5 : subd1_6 [-1, -1] = true := by decide +kernel
theorem subd1_6_6 : subd1_6 [-1, 0] = true := by decide +kernel
theorem subd1_6_7 : subd1_6 [-1, 1] = true := by decide +kernel
theorem subd1_6_8 : subd1_6 [-1, 2] = true := by decide +kernel
theorem subd1_6_9 : subd1_6 [-1, 3] = true := by decide +kernel
theorem subd1_6_10 : subd1_6 [-1, 4] = true := by decide +kernel
theorem subd1_6_11 : subd1_6 [0, -4] = true := by decide +kernel
theorem subd1_6_12 : subd1_6 [0, -3] = true := by decide +kernel
theorem subd1_6_13 : subd1_6 [0, -2] = true := by decide +kernel
theorem subd1_6_14 : subd1_6 [0, -1] = true := by decide +kernel
theorem subd1_6_15 : subd1_6 [0, 0] = true := by decide +kernel
theorem subd1_6_16 : subd1_6 [0, 1] = true := by decide +kernel
theorem subd1_6_17 : subd1_6 [0, 2] = true := by decide +kernel
theorem subd1_6_18 : subd1_6 [0, 3] = true := by decide +kernel
theorem subd1_6_19 : subd1_6 [1, -5] = true := by decide +kernel
theorem subd1_6_20 : subd1_6 [1, -4] = true := by decide +kernel
theorem subd1_6_21 : subd1_6 [1, -3] = true := by decide +kernel
theorem subd1_6_22 : subd1_6 [1, -2] = true := by decide +kernel
theorem subd1_6_23 : subd1_6 [1, -1] = true := by decide +kernel
theorem subd1_6_24 : subd1_6 [1, 0] = true := by decide +kernel
theorem subd1_6_25 : subd1_6 [1, 1] = true := by decide +kernel
theorem subd1_6_26 : subd1_6 [1, 2] = true := by decide +kernel
theorem subd1_6_27 : subd1_6 [1, 3] = true := by decide +kernel
theorem subd1_6_28 : subd1_6 [2] = true := by decide +kernel
theorem subd1_6_29 : subd1_6 [3] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_cons.2 ⟨subd1_6_1, List.forall_mem_cons.2 ⟨subd1_6_2, List.forall_mem_cons.2 ⟨subd1_6_3, List.forall_mem_cons.2 ⟨subd1_6_4, List.forall_mem_cons.2 ⟨subd1_6_5, List.forall_mem_cons.2 ⟨subd1_6_6, List.forall_mem_cons.2 ⟨subd1_6_7, List.forall_mem_cons.2 ⟨subd1_6_8, List.forall_mem_cons.2 ⟨subd1_6_9, List.forall_mem_cons.2 ⟨subd1_6_10, List.forall_mem_cons.2 ⟨subd1_6_11, List.forall_mem_cons.2 ⟨subd1_6_12, List.forall_mem_cons.2 ⟨subd1_6_13, List.forall_mem_cons.2 ⟨subd1_6_14, List.forall_mem_cons.2 ⟨subd1_6_15, List.forall_mem_cons.2 ⟨subd1_6_16, List.forall_mem_cons.2 ⟨subd1_6_17, List.forall_mem_cons.2 ⟨subd1_6_18, List.forall_mem_cons.2 ⟨subd1_6_19, List.forall_mem_cons.2 ⟨subd1_6_20, List.forall_mem_cons.2 ⟨subd1_6_21, List.forall_mem_cons.2 ⟨subd1_6_22, List.forall_mem_cons.2 ⟨subd1_6_23, List.forall_mem_cons.2 ⟨subd1_6_24, List.forall_mem_cons.2 ⟨subd1_6_25, List.forall_mem_cons.2 ⟨subd1_6_26, List.forall_mem_cons.2 ⟨subd1_6_27, List.forall_mem_cons.2 ⟨subd1_6_28, List.forall_mem_cons.2 ⟨subd1_6_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩
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
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C123
