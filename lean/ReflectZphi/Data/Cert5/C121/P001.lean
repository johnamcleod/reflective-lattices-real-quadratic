import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_2_0 : subd1_2 [-3] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [-2, -5] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [-2, -4] = true := by decide +kernel
theorem subd1_2_3 : subd1_2 [-2, -3] = true := by decide +kernel
theorem subd1_2_4 : subd1_2 [-2, -2] = true := by decide +kernel
theorem subd1_2_5 : subd1_2 [-2, -1] = true := by decide +kernel
theorem subd1_2_6 : subd1_2 [-2, 0] = true := by decide +kernel
theorem subd1_2_7 : subd1_2 [-2, 1] = true := by decide +kernel
theorem subd1_2_8 : subd1_2 [-2, 2] = true := by decide +kernel
theorem subd1_2_9 : subd1_2 [-1, -5] = true := by decide +kernel
theorem subd1_2_10 : subd1_2 [-1, -4] = true := by decide +kernel
theorem subd1_2_11 : subd1_2 [-1, -3] = true := by decide +kernel
theorem subd1_2_12 : subd1_2 [-1, -2] = true := by decide +kernel
theorem subd1_2_13 : subd1_2 [-1, -1] = true := by decide +kernel
theorem subd1_2_14 : subd1_2 [-1, 0] = true := by decide +kernel
theorem subd1_2_15 : subd1_2 [-1, 1] = true := by decide +kernel
theorem subd1_2_16 : subd1_2 [-1, 2] = true := by decide +kernel
theorem subd1_2_17 : subd1_2 [-1, 3] = true := by decide +kernel
theorem subd1_2_18 : subd1_2 [0, -5] = true := by decide +kernel
theorem subd1_2_19 : subd1_2 [0, -4] = true := by decide +kernel
theorem subd1_2_20 : subd1_2 [0, -3] = true := by decide +kernel
theorem subd1_2_21 : subd1_2 [0, -2] = true := by decide +kernel
theorem subd1_2_22 : subd1_2 [0, -1] = true := by decide +kernel
theorem subd1_2_23 : subd1_2 [0, 0] = true := by decide +kernel
theorem subd1_2_24 : subd1_2 [0, 1] = true := by decide +kernel
theorem subd1_2_25 : subd1_2 [0, 2] = true := by decide +kernel
theorem subd1_2_26 : subd1_2 [0, 3] = true := by decide +kernel
theorem subd1_2_27 : subd1_2 [0, 4] = true := by decide +kernel
theorem subd1_2_28 : subd1_2 [1, -4] = true := by decide +kernel
theorem subd1_2_29 : subd1_2 [1, -3] = true := by decide +kernel
theorem subd1_2_30 : subd1_2 [1, -2] = true := by decide +kernel
theorem subd1_2_31 : subd1_2 [1, -1] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_cons.2 ⟨subd1_2_3, List.forall_mem_cons.2 ⟨subd1_2_4, List.forall_mem_cons.2 ⟨subd1_2_5, List.forall_mem_cons.2 ⟨subd1_2_6, List.forall_mem_cons.2 ⟨subd1_2_7, List.forall_mem_cons.2 ⟨subd1_2_8, List.forall_mem_cons.2 ⟨subd1_2_9, List.forall_mem_cons.2 ⟨subd1_2_10, List.forall_mem_cons.2 ⟨subd1_2_11, List.forall_mem_cons.2 ⟨subd1_2_12, List.forall_mem_cons.2 ⟨subd1_2_13, List.forall_mem_cons.2 ⟨subd1_2_14, List.forall_mem_cons.2 ⟨subd1_2_15, List.forall_mem_cons.2 ⟨subd1_2_16, List.forall_mem_cons.2 ⟨subd1_2_17, List.forall_mem_cons.2 ⟨subd1_2_18, List.forall_mem_cons.2 ⟨subd1_2_19, List.forall_mem_cons.2 ⟨subd1_2_20, List.forall_mem_cons.2 ⟨subd1_2_21, List.forall_mem_cons.2 ⟨subd1_2_22, List.forall_mem_cons.2 ⟨subd1_2_23, List.forall_mem_cons.2 ⟨subd1_2_24, List.forall_mem_cons.2 ⟨subd1_2_25, List.forall_mem_cons.2 ⟨subd1_2_26, List.forall_mem_cons.2 ⟨subd1_2_27, List.forall_mem_cons.2 ⟨subd1_2_28, List.forall_mem_cons.2 ⟨subd1_2_29, List.forall_mem_cons.2 ⟨subd1_2_30, List.forall_mem_cons.2 ⟨subd1_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_2_32 : subd1_2 [1, 0] = true := by decide +kernel
theorem subd1_2_33 : subd1_2 [1, 1] = true := by decide +kernel
theorem subd1_2_34 : subd1_2 [1, 2] = true := by decide +kernel
theorem subd1_2_35 : subd1_2 [1, 3] = true := by decide +kernel
theorem subd1_2_36 : subd1_2 [1, 4] = true := by decide +kernel
theorem subd1_2_37 : subd1_2 [2, -3] = true := by decide +kernel
theorem subd1_2_38 : subd1_2 [2, -2] = true := by decide +kernel
theorem subd1_2_39 : subd1_2 [2, -1] = true := by decide +kernel
theorem subd1_2_40 : subd1_2 [2, 0] = true := by decide +kernel
theorem subd1_2_41 : subd1_2 [2, 1] = true := by decide +kernel
theorem subd1_2_42 : subd1_2 [2, 2] = true := by decide +kernel
theorem subd1_2_43 : subd1_2 [2, 3] = true := by decide +kernel
theorem subd1_2_44 : subd1_2 [2, 4] = true := by decide +kernel
theorem subd1_2_45 : subd1_2 [3] = true := by decide +kernel
theorem sbd1_2_1 : ∀ q ∈ blkd1_2_1, subd1_2 q = true := by
  unfold blkd1_2_1
  exact List.forall_mem_cons.2 ⟨subd1_2_32, List.forall_mem_cons.2 ⟨subd1_2_33, List.forall_mem_cons.2 ⟨subd1_2_34, List.forall_mem_cons.2 ⟨subd1_2_35, List.forall_mem_cons.2 ⟨subd1_2_36, List.forall_mem_cons.2 ⟨subd1_2_37, List.forall_mem_cons.2 ⟨subd1_2_38, List.forall_mem_cons.2 ⟨subd1_2_39, List.forall_mem_cons.2 ⟨subd1_2_40, List.forall_mem_cons.2 ⟨subd1_2_41, List.forall_mem_cons.2 ⟨subd1_2_42, List.forall_mem_cons.2 ⟨subd1_2_43, List.forall_mem_cons.2 ⟨subd1_2_44, List.forall_mem_cons.2 ⟨subd1_2_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-1] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [0] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [1] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [-1] = true := by decide +kernel
theorem subd2_1_1 : subd2_1 [0, -2] = true := by decide +kernel
theorem subd2_1_2 : subd2_1 [0, -1] = true := by decide +kernel
theorem subd2_1_3 : subd2_1 [0, 0] = true := by decide +kernel
theorem subd2_1_4 : subd2_1 [0, 1] = true := by decide +kernel
theorem subd2_1_5 : subd2_1 [1] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_cons.2 ⟨subd2_1_1, List.forall_mem_cons.2 ⟨subd2_1_2, List.forall_mem_cons.2 ⟨subd2_1_3, List.forall_mem_cons.2 ⟨subd2_1_4, List.forall_mem_cons.2 ⟨subd2_1_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [-4] = true := by decide +kernel
theorem subd2_2_1 : subd2_2 [-3, -4] = true := by decide +kernel
theorem subd2_2_2 : subd2_2 [-3, -3] = true := by decide +kernel
theorem subd2_2_3 : subd2_2 [-3, -2] = true := by decide +kernel
theorem subd2_2_4 : subd2_2 [-3, -1] = true := by decide +kernel
theorem subd2_2_5 : subd2_2 [-3, 0] = true := by decide +kernel
theorem subd2_2_6 : subd2_2 [-3, 1] = true := by decide +kernel
theorem subd2_2_7 : subd2_2 [-3, 2] = true := by decide +kernel
theorem subd2_2_8 : subd2_2 [-3, 3] = true := by decide +kernel
theorem subd2_2_9 : subd2_2 [-3, 4] = true := by decide +kernel
theorem subd2_2_10 : subd2_2 [-3, 5] = true := by decide +kernel
theorem subd2_2_11 : subd2_2 [-2, -5] = true := by decide +kernel
theorem subd2_2_12 : subd2_2 [-2, -4] = true := by decide +kernel
theorem subd2_2_13 : subd2_2 [-2, -3] = true := by decide +kernel
theorem subd2_2_14 : subd2_2 [-2, -2] = true := by decide +kernel
theorem subd2_2_15 : subd2_2 [-2, -1] = true := by decide +kernel
theorem subd2_2_16 : subd2_2 [-2, 0] = true := by decide +kernel
theorem subd2_2_17 : subd2_2 [-2, 1] = true := by decide +kernel
theorem subd2_2_18 : subd2_2 [-2, 2] = true := by decide +kernel
theorem subd2_2_19 : subd2_2 [-2, 3] = true := by decide +kernel
theorem subd2_2_20 : subd2_2 [-2, 4] = true := by decide +kernel
theorem subd2_2_21 : subd2_2 [-2, 5] = true := by decide +kernel
theorem subd2_2_22 : subd2_2 [-1, -6] = true := by decide +kernel
theorem subd2_2_23 : subd2_2 [-1, -5] = true := by decide +kernel
theorem subd2_2_24 : subd2_2 [-1, -4] = true := by decide +kernel
theorem subd2_2_25 : subd2_2 [-1, -3] = true := by decide +kernel
theorem subd2_2_26 : subd2_2 [-1, -2] = true := by decide +kernel
theorem subd2_2_27 : subd2_2 [-1, -1] = true := by decide +kernel
theorem subd2_2_28 : subd2_2 [-1, 0] = true := by decide +kernel
theorem subd2_2_29 : subd2_2 [-1, 1] = true := by decide +kernel
theorem subd2_2_30 : subd2_2 [-1, 2] = true := by decide +kernel
theorem subd2_2_31 : subd2_2 [-1, 3] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_cons.2 ⟨subd2_2_1, List.forall_mem_cons.2 ⟨subd2_2_2, List.forall_mem_cons.2 ⟨subd2_2_3, List.forall_mem_cons.2 ⟨subd2_2_4, List.forall_mem_cons.2 ⟨subd2_2_5, List.forall_mem_cons.2 ⟨subd2_2_6, List.forall_mem_cons.2 ⟨subd2_2_7, List.forall_mem_cons.2 ⟨subd2_2_8, List.forall_mem_cons.2 ⟨subd2_2_9, List.forall_mem_cons.2 ⟨subd2_2_10, List.forall_mem_cons.2 ⟨subd2_2_11, List.forall_mem_cons.2 ⟨subd2_2_12, List.forall_mem_cons.2 ⟨subd2_2_13, List.forall_mem_cons.2 ⟨subd2_2_14, List.forall_mem_cons.2 ⟨subd2_2_15, List.forall_mem_cons.2 ⟨subd2_2_16, List.forall_mem_cons.2 ⟨subd2_2_17, List.forall_mem_cons.2 ⟨subd2_2_18, List.forall_mem_cons.2 ⟨subd2_2_19, List.forall_mem_cons.2 ⟨subd2_2_20, List.forall_mem_cons.2 ⟨subd2_2_21, List.forall_mem_cons.2 ⟨subd2_2_22, List.forall_mem_cons.2 ⟨subd2_2_23, List.forall_mem_cons.2 ⟨subd2_2_24, List.forall_mem_cons.2 ⟨subd2_2_25, List.forall_mem_cons.2 ⟨subd2_2_26, List.forall_mem_cons.2 ⟨subd2_2_27, List.forall_mem_cons.2 ⟨subd2_2_28, List.forall_mem_cons.2 ⟨subd2_2_29, List.forall_mem_cons.2 ⟨subd2_2_30, List.forall_mem_cons.2 ⟨subd2_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
