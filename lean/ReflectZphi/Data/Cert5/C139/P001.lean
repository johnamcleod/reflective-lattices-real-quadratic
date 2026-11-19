import ReflectZphi.Data.Cert5.C139.Base

namespace ReflectZphi.Data.Cert5.C139

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [-1] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [0] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [1] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-3] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-2] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [-1, -4] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [-1, -3] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [-1, -2] = true := by decide +kernel
theorem subd1_3_5 : subd1_3 [-1, -1] = true := by decide +kernel
theorem subd1_3_6 : subd1_3 [-1, 0] = true := by decide +kernel
theorem subd1_3_7 : subd1_3 [-1, 1] = true := by decide +kernel
theorem subd1_3_8 : subd1_3 [-1, 2] = true := by decide +kernel
theorem subd1_3_9 : subd1_3 [-1, 3] = true := by decide +kernel
theorem subd1_3_10 : subd1_3 [0, -4] = true := by decide +kernel
theorem subd1_3_11 : subd1_3 [0, -3] = true := by decide +kernel
theorem subd1_3_12 : subd1_3 [0, -2] = true := by decide +kernel
theorem subd1_3_13 : subd1_3 [0, -1] = true := by decide +kernel
theorem subd1_3_14 : subd1_3 [0, 0] = true := by decide +kernel
theorem subd1_3_15 : subd1_3 [0, 1] = true := by decide +kernel
theorem subd1_3_16 : subd1_3 [0, 2] = true := by decide +kernel
theorem subd1_3_17 : subd1_3 [0, 3] = true := by decide +kernel
theorem subd1_3_18 : subd1_3 [1, -4] = true := by decide +kernel
theorem subd1_3_19 : subd1_3 [1, -3] = true := by decide +kernel
theorem subd1_3_20 : subd1_3 [1, -2] = true := by decide +kernel
theorem subd1_3_21 : subd1_3 [1, -1] = true := by decide +kernel
theorem subd1_3_22 : subd1_3 [1, 0] = true := by decide +kernel
theorem subd1_3_23 : subd1_3 [1, 1] = true := by decide +kernel
theorem subd1_3_24 : subd1_3 [1, 2] = true := by decide +kernel
theorem subd1_3_25 : subd1_3 [1, 3] = true := by decide +kernel
theorem subd1_3_26 : subd1_3 [2] = true := by decide +kernel
theorem subd1_3_27 : subd1_3 [3] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_cons.2 ⟨subd1_3_5, List.forall_mem_cons.2 ⟨subd1_3_6, List.forall_mem_cons.2 ⟨subd1_3_7, List.forall_mem_cons.2 ⟨subd1_3_8, List.forall_mem_cons.2 ⟨subd1_3_9, List.forall_mem_cons.2 ⟨subd1_3_10, List.forall_mem_cons.2 ⟨subd1_3_11, List.forall_mem_cons.2 ⟨subd1_3_12, List.forall_mem_cons.2 ⟨subd1_3_13, List.forall_mem_cons.2 ⟨subd1_3_14, List.forall_mem_cons.2 ⟨subd1_3_15, List.forall_mem_cons.2 ⟨subd1_3_16, List.forall_mem_cons.2 ⟨subd1_3_17, List.forall_mem_cons.2 ⟨subd1_3_18, List.forall_mem_cons.2 ⟨subd1_3_19, List.forall_mem_cons.2 ⟨subd1_3_20, List.forall_mem_cons.2 ⟨subd1_3_21, List.forall_mem_cons.2 ⟨subd1_3_22, List.forall_mem_cons.2 ⟨subd1_3_23, List.forall_mem_cons.2 ⟨subd1_3_24, List.forall_mem_cons.2 ⟨subd1_3_25, List.forall_mem_cons.2 ⟨subd1_3_26, List.forall_mem_cons.2 ⟨subd1_3_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [-3] = true := by decide +kernel
theorem subd2_1_1 : subd2_1 [-2, -2] = true := by decide +kernel
theorem subd2_1_2 : subd2_1 [-2, -1] = true := by decide +kernel
theorem subd2_1_3 : subd2_1 [-2, 0] = true := by decide +kernel
theorem subd2_1_4 : subd2_1 [-2, 1] = true := by decide +kernel
theorem subd2_1_5 : subd2_1 [-2, 2] = true := by decide +kernel
theorem subd2_1_6 : subd2_1 [-2, 3] = true := by decide +kernel
theorem subd2_1_7 : subd2_1 [-1, -3] = true := by decide +kernel
theorem subd2_1_8 : subd2_1 [-1, -2] = true := by decide +kernel
theorem subd2_1_9 : subd2_1 [-1, -1] = true := by decide +kernel
theorem subd2_1_10 : subd2_1 [-1, 0] = true := by decide +kernel
theorem subd2_1_11 : subd2_1 [-1, 1] = true := by decide +kernel
theorem subd2_1_12 : subd2_1 [-1, 2] = true := by decide +kernel
theorem subd2_1_13 : subd2_1 [-1, 3] = true := by decide +kernel
theorem subd2_1_14 : subd2_1 [0, -4] = true := by decide +kernel
theorem subd2_1_15 : subd2_1 [0, -3] = true := by decide +kernel
theorem subd2_1_16 : subd2_1 [0, -2] = true := by decide +kernel
theorem subd2_1_17 : subd2_1 [0, -1] = true := by decide +kernel
theorem subd2_1_18 : subd2_1 [0, 0] = true := by decide +kernel
theorem subd2_1_19 : subd2_1 [0, 1] = true := by decide +kernel
theorem subd2_1_20 : subd2_1 [0, 2] = true := by decide +kernel
theorem subd2_1_21 : subd2_1 [0, 3] = true := by decide +kernel
theorem subd2_1_22 : subd2_1 [1, -4] = true := by decide +kernel
theorem subd2_1_23 : subd2_1 [1, -3] = true := by decide +kernel
theorem subd2_1_24 : subd2_1 [1, -2] = true := by decide +kernel
theorem subd2_1_25 : subd2_1 [1, -1] = true := by decide +kernel
theorem subd2_1_26 : subd2_1 [1, 0] = true := by decide +kernel
theorem subd2_1_27 : subd2_1 [1, 1] = true := by decide +kernel
theorem subd2_1_28 : subd2_1 [1, 2] = true := by decide +kernel
theorem subd2_1_29 : subd2_1 [2, -4] = true := by decide +kernel
theorem subd2_1_30 : subd2_1 [2, -3] = true := by decide +kernel
theorem subd2_1_31 : subd2_1 [2, -2] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_cons.2 ⟨subd2_1_1, List.forall_mem_cons.2 ⟨subd2_1_2, List.forall_mem_cons.2 ⟨subd2_1_3, List.forall_mem_cons.2 ⟨subd2_1_4, List.forall_mem_cons.2 ⟨subd2_1_5, List.forall_mem_cons.2 ⟨subd2_1_6, List.forall_mem_cons.2 ⟨subd2_1_7, List.forall_mem_cons.2 ⟨subd2_1_8, List.forall_mem_cons.2 ⟨subd2_1_9, List.forall_mem_cons.2 ⟨subd2_1_10, List.forall_mem_cons.2 ⟨subd2_1_11, List.forall_mem_cons.2 ⟨subd2_1_12, List.forall_mem_cons.2 ⟨subd2_1_13, List.forall_mem_cons.2 ⟨subd2_1_14, List.forall_mem_cons.2 ⟨subd2_1_15, List.forall_mem_cons.2 ⟨subd2_1_16, List.forall_mem_cons.2 ⟨subd2_1_17, List.forall_mem_cons.2 ⟨subd2_1_18, List.forall_mem_cons.2 ⟨subd2_1_19, List.forall_mem_cons.2 ⟨subd2_1_20, List.forall_mem_cons.2 ⟨subd2_1_21, List.forall_mem_cons.2 ⟨subd2_1_22, List.forall_mem_cons.2 ⟨subd2_1_23, List.forall_mem_cons.2 ⟨subd2_1_24, List.forall_mem_cons.2 ⟨subd2_1_25, List.forall_mem_cons.2 ⟨subd2_1_26, List.forall_mem_cons.2 ⟨subd2_1_27, List.forall_mem_cons.2 ⟨subd2_1_28, List.forall_mem_cons.2 ⟨subd2_1_29, List.forall_mem_cons.2 ⟨subd2_1_30, List.forall_mem_cons.2 ⟨subd2_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_1_32 : subd2_1 [2, -1] = true := by decide +kernel
theorem subd2_1_33 : subd2_1 [2, 0] = true := by decide +kernel
theorem subd2_1_34 : subd2_1 [2, 1] = true := by decide +kernel
theorem subd2_1_35 : subd2_1 [3] = true := by decide +kernel
theorem sbd2_1_1 : ∀ q ∈ blkd2_1_1, subd2_1 q = true := by
  unfold blkd2_1_1
  exact List.forall_mem_cons.2 ⟨subd2_1_32, List.forall_mem_cons.2 ⟨subd2_1_33, List.forall_mem_cons.2 ⟨subd2_1_34, List.forall_mem_cons.2 ⟨subd2_1_35, List.forall_mem_nil _⟩⟩⟩⟩
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

end ReflectZphi.Data.Cert5.C139
