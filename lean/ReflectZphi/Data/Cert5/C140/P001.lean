import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_nil _⟩
theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_nil _⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-3] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-2, -3] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [-2, -2] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [-2, -1] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [-2, 0] = true := by decide +kernel
theorem subd1_3_5 : subd1_3 [-2, 1] = true := by decide +kernel
theorem subd1_3_6 : subd1_3 [-2, 2] = true := by decide +kernel
theorem subd1_3_7 : subd1_3 [-1, -4] = true := by decide +kernel
theorem subd1_3_8 : subd1_3 [-1, -3] = true := by decide +kernel
theorem subd1_3_9 : subd1_3 [-1, -2] = true := by decide +kernel
theorem subd1_3_10 : subd1_3 [-1, -1] = true := by decide +kernel
theorem subd1_3_11 : subd1_3 [-1, 0] = true := by decide +kernel
theorem subd1_3_12 : subd1_3 [-1, 1] = true := by decide +kernel
theorem subd1_3_13 : subd1_3 [-1, 2] = true := by decide +kernel
theorem subd1_3_14 : subd1_3 [-1, 3] = true := by decide +kernel
theorem subd1_3_15 : subd1_3 [0, -4] = true := by decide +kernel
theorem subd1_3_16 : subd1_3 [0, -3] = true := by decide +kernel
theorem subd1_3_17 : subd1_3 [0, -2] = true := by decide +kernel
theorem subd1_3_18 : subd1_3 [0, -1] = true := by decide +kernel
theorem subd1_3_19 : subd1_3 [0, 0] = true := by decide +kernel
theorem subd1_3_20 : subd1_3 [0, 1] = true := by decide +kernel
theorem subd1_3_21 : subd1_3 [0, 2] = true := by decide +kernel
theorem subd1_3_22 : subd1_3 [0, 3] = true := by decide +kernel
theorem subd1_3_23 : subd1_3 [1, -4] = true := by decide +kernel
theorem subd1_3_24 : subd1_3 [1, -3] = true := by decide +kernel
theorem subd1_3_25 : subd1_3 [1, -2] = true := by decide +kernel
theorem subd1_3_26 : subd1_3 [1, -1] = true := by decide +kernel
theorem subd1_3_27 : subd1_3 [1, 0] = true := by decide +kernel
theorem subd1_3_28 : subd1_3 [1, 1] = true := by decide +kernel
theorem subd1_3_29 : subd1_3 [1, 2] = true := by decide +kernel
theorem subd1_3_30 : subd1_3 [1, 3] = true := by decide +kernel
theorem subd1_3_31 : subd1_3 [2, -3] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_cons.2 ⟨subd1_3_5, List.forall_mem_cons.2 ⟨subd1_3_6, List.forall_mem_cons.2 ⟨subd1_3_7, List.forall_mem_cons.2 ⟨subd1_3_8, List.forall_mem_cons.2 ⟨subd1_3_9, List.forall_mem_cons.2 ⟨subd1_3_10, List.forall_mem_cons.2 ⟨subd1_3_11, List.forall_mem_cons.2 ⟨subd1_3_12, List.forall_mem_cons.2 ⟨subd1_3_13, List.forall_mem_cons.2 ⟨subd1_3_14, List.forall_mem_cons.2 ⟨subd1_3_15, List.forall_mem_cons.2 ⟨subd1_3_16, List.forall_mem_cons.2 ⟨subd1_3_17, List.forall_mem_cons.2 ⟨subd1_3_18, List.forall_mem_cons.2 ⟨subd1_3_19, List.forall_mem_cons.2 ⟨subd1_3_20, List.forall_mem_cons.2 ⟨subd1_3_21, List.forall_mem_cons.2 ⟨subd1_3_22, List.forall_mem_cons.2 ⟨subd1_3_23, List.forall_mem_cons.2 ⟨subd1_3_24, List.forall_mem_cons.2 ⟨subd1_3_25, List.forall_mem_cons.2 ⟨subd1_3_26, List.forall_mem_cons.2 ⟨subd1_3_27, List.forall_mem_cons.2 ⟨subd1_3_28, List.forall_mem_cons.2 ⟨subd1_3_29, List.forall_mem_cons.2 ⟨subd1_3_30, List.forall_mem_cons.2 ⟨subd1_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_3_32 : subd1_3 [2, -2] = true := by decide +kernel
theorem subd1_3_33 : subd1_3 [2, -1] = true := by decide +kernel
theorem subd1_3_34 : subd1_3 [2, 0] = true := by decide +kernel
theorem subd1_3_35 : subd1_3 [2, 1] = true := by decide +kernel
theorem subd1_3_36 : subd1_3 [2, 2] = true := by decide +kernel
theorem subd1_3_37 : subd1_3 [3] = true := by decide +kernel
theorem sbd1_3_1 : ∀ q ∈ blkd1_3_1, subd1_3 q = true := by
  unfold blkd1_3_1
  exact List.forall_mem_cons.2 ⟨subd1_3_32, List.forall_mem_cons.2 ⟨subd1_3_33, List.forall_mem_cons.2 ⟨subd1_3_34, List.forall_mem_cons.2 ⟨subd1_3_35, List.forall_mem_cons.2 ⟨subd1_3_36, List.forall_mem_cons.2 ⟨subd1_3_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd1_4 : ldCheck G d1_4.U d1_4.ms ldd1_4 = true := by decide +kernel
theorem pre_okd1_4 : subPre G cell1 d1_4 = true := by decide +kernel
theorem subd1_4_0 : subd1_4 [-2] = true := by decide +kernel
theorem subd1_4_1 : subd1_4 [-1] = true := by decide +kernel
theorem subd1_4_2 : subd1_4 [0, -3] = true := by decide +kernel
theorem subd1_4_3 : subd1_4 [0, -2] = true := by decide +kernel
theorem subd1_4_4 : subd1_4 [0, -1] = true := by decide +kernel
theorem subd1_4_5 : subd1_4 [0, 0] = true := by decide +kernel
theorem subd1_4_6 : subd1_4 [0, 1] = true := by decide +kernel
theorem subd1_4_7 : subd1_4 [0, 2] = true := by decide +kernel
theorem subd1_4_8 : subd1_4 [1] = true := by decide +kernel
theorem subd1_4_9 : subd1_4 [2] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_cons.2 ⟨subd1_4_1, List.forall_mem_cons.2 ⟨subd1_4_2, List.forall_mem_cons.2 ⟨subd1_4_3, List.forall_mem_cons.2 ⟨subd1_4_4, List.forall_mem_cons.2 ⟨subd1_4_5, List.forall_mem_cons.2 ⟨subd1_4_6, List.forall_mem_cons.2 ⟨subd1_4_7, List.forall_mem_cons.2 ⟨subd1_4_8, List.forall_mem_cons.2 ⟨subd1_4_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_5 : ldCheck G d1_5.U d1_5.ms ldd1_5 = true := by decide +kernel
theorem pre_okd1_5 : subPre G cell1 d1_5 = true := by decide +kernel
theorem subd1_5_0 : subd1_5 [] = true := by decide +kernel
theorem sbd1_5_0 : ∀ q ∈ blkd1_5_0, subd1_5 q = true := by
  unfold blkd1_5_0
  exact List.forall_mem_cons.2 ⟨subd1_5_0, List.forall_mem_nil _⟩
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

end ReflectZphi.Data.Cert5.C140
