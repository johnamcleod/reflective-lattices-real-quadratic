import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd21_0 : ldCheck G d21_0.U d21_0.ms ldd21_0 = true := by decide +kernel
theorem pre_okd21_0 : subPre G cell21 d21_0 = true := by decide +kernel
theorem subd21_0_0 : subd21_0 [-3] = true := by decide +kernel
theorem subd21_0_1 : subd21_0 [-2, -5] = true := by decide +kernel
theorem subd21_0_2 : subd21_0 [-2, -4] = true := by decide +kernel
theorem subd21_0_3 : subd21_0 [-2, -3] = true := by decide +kernel
theorem subd21_0_4 : subd21_0 [-2, -2] = true := by decide +kernel
theorem subd21_0_5 : subd21_0 [-2, -1] = true := by decide +kernel
theorem subd21_0_6 : subd21_0 [-2, 0] = true := by decide +kernel
theorem subd21_0_7 : subd21_0 [-2, 1] = true := by decide +kernel
theorem subd21_0_8 : subd21_0 [-2, 2] = true := by decide +kernel
theorem subd21_0_9 : subd21_0 [-2, 3] = true := by decide +kernel
theorem subd21_0_10 : subd21_0 [-1, -5] = true := by decide +kernel
theorem subd21_0_11 : subd21_0 [-1, -4] = true := by decide +kernel
theorem subd21_0_12 : subd21_0 [-1, -3] = true := by decide +kernel
theorem subd21_0_13 : subd21_0 [-1, -2] = true := by decide +kernel
theorem subd21_0_14 : subd21_0 [-1, -1] = true := by decide +kernel
theorem subd21_0_15 : subd21_0 [-1, 0] = true := by decide +kernel
theorem subd21_0_16 : subd21_0 [-1, 1] = true := by decide +kernel
theorem subd21_0_17 : subd21_0 [-1, 2] = true := by decide +kernel
theorem subd21_0_18 : subd21_0 [-1, 3] = true := by decide +kernel
theorem subd21_0_19 : subd21_0 [-1, 4] = true := by decide +kernel
theorem subd21_0_20 : subd21_0 [0, -5] = true := by decide +kernel
theorem subd21_0_21 : subd21_0 [0, -4] = true := by decide +kernel
theorem subd21_0_22 : subd21_0 [0, -3] = true := by decide +kernel
theorem subd21_0_23 : subd21_0 [0, -2] = true := by decide +kernel
theorem subd21_0_24 : subd21_0 [0, -1] = true := by decide +kernel
theorem subd21_0_25 : subd21_0 [0, 0] = true := by decide +kernel
theorem subd21_0_26 : subd21_0 [0, 1] = true := by decide +kernel
theorem subd21_0_27 : subd21_0 [0, 2] = true := by decide +kernel
theorem subd21_0_28 : subd21_0 [0, 3] = true := by decide +kernel
theorem subd21_0_29 : subd21_0 [0, 4] = true := by decide +kernel
theorem subd21_0_30 : subd21_0 [1, -5] = true := by decide +kernel
theorem subd21_0_31 : subd21_0 [1, -4] = true := by decide +kernel
theorem sbd21_0_0 : ∀ q ∈ blkd21_0_0, subd21_0 q = true := by
  unfold blkd21_0_0
  exact List.forall_mem_cons.2 ⟨subd21_0_0, List.forall_mem_cons.2 ⟨subd21_0_1, List.forall_mem_cons.2 ⟨subd21_0_2, List.forall_mem_cons.2 ⟨subd21_0_3, List.forall_mem_cons.2 ⟨subd21_0_4, List.forall_mem_cons.2 ⟨subd21_0_5, List.forall_mem_cons.2 ⟨subd21_0_6, List.forall_mem_cons.2 ⟨subd21_0_7, List.forall_mem_cons.2 ⟨subd21_0_8, List.forall_mem_cons.2 ⟨subd21_0_9, List.forall_mem_cons.2 ⟨subd21_0_10, List.forall_mem_cons.2 ⟨subd21_0_11, List.forall_mem_cons.2 ⟨subd21_0_12, List.forall_mem_cons.2 ⟨subd21_0_13, List.forall_mem_cons.2 ⟨subd21_0_14, List.forall_mem_cons.2 ⟨subd21_0_15, List.forall_mem_cons.2 ⟨subd21_0_16, List.forall_mem_cons.2 ⟨subd21_0_17, List.forall_mem_cons.2 ⟨subd21_0_18, List.forall_mem_cons.2 ⟨subd21_0_19, List.forall_mem_cons.2 ⟨subd21_0_20, List.forall_mem_cons.2 ⟨subd21_0_21, List.forall_mem_cons.2 ⟨subd21_0_22, List.forall_mem_cons.2 ⟨subd21_0_23, List.forall_mem_cons.2 ⟨subd21_0_24, List.forall_mem_cons.2 ⟨subd21_0_25, List.forall_mem_cons.2 ⟨subd21_0_26, List.forall_mem_cons.2 ⟨subd21_0_27, List.forall_mem_cons.2 ⟨subd21_0_28, List.forall_mem_cons.2 ⟨subd21_0_29, List.forall_mem_cons.2 ⟨subd21_0_30, List.forall_mem_cons.2 ⟨subd21_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd21_0_32 : subd21_0 [1, -3] = true := by decide +kernel
theorem subd21_0_33 : subd21_0 [1, -2] = true := by decide +kernel
theorem subd21_0_34 : subd21_0 [1, -1] = true := by decide +kernel
theorem subd21_0_35 : subd21_0 [1, 0] = true := by decide +kernel
theorem subd21_0_36 : subd21_0 [1, 1] = true := by decide +kernel
theorem subd21_0_37 : subd21_0 [1, 2] = true := by decide +kernel
theorem subd21_0_38 : subd21_0 [1, 3] = true := by decide +kernel
theorem subd21_0_39 : subd21_0 [1, 4] = true := by decide +kernel
theorem subd21_0_40 : subd21_0 [2, -4] = true := by decide +kernel
theorem subd21_0_41 : subd21_0 [2, -3] = true := by decide +kernel
theorem subd21_0_42 : subd21_0 [2, -2] = true := by decide +kernel
theorem subd21_0_43 : subd21_0 [2, -1] = true := by decide +kernel
theorem subd21_0_44 : subd21_0 [2, 0] = true := by decide +kernel
theorem subd21_0_45 : subd21_0 [2, 1] = true := by decide +kernel
theorem subd21_0_46 : subd21_0 [2, 2] = true := by decide +kernel
theorem subd21_0_47 : subd21_0 [2, 3] = true := by decide +kernel
theorem subd21_0_48 : subd21_0 [2, 4] = true := by decide +kernel
theorem subd21_0_49 : subd21_0 [3] = true := by decide +kernel
theorem sbd21_0_1 : ∀ q ∈ blkd21_0_1, subd21_0 q = true := by
  unfold blkd21_0_1
  exact List.forall_mem_cons.2 ⟨subd21_0_32, List.forall_mem_cons.2 ⟨subd21_0_33, List.forall_mem_cons.2 ⟨subd21_0_34, List.forall_mem_cons.2 ⟨subd21_0_35, List.forall_mem_cons.2 ⟨subd21_0_36, List.forall_mem_cons.2 ⟨subd21_0_37, List.forall_mem_cons.2 ⟨subd21_0_38, List.forall_mem_cons.2 ⟨subd21_0_39, List.forall_mem_cons.2 ⟨subd21_0_40, List.forall_mem_cons.2 ⟨subd21_0_41, List.forall_mem_cons.2 ⟨subd21_0_42, List.forall_mem_cons.2 ⟨subd21_0_43, List.forall_mem_cons.2 ⟨subd21_0_44, List.forall_mem_cons.2 ⟨subd21_0_45, List.forall_mem_cons.2 ⟨subd21_0_46, List.forall_mem_cons.2 ⟨subd21_0_47, List.forall_mem_cons.2 ⟨subd21_0_48, List.forall_mem_cons.2 ⟨subd21_0_49, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd21_1 : ldCheck G d21_1.U d21_1.ms ldd21_1 = true := by decide +kernel
theorem pre_okd21_1 : subPre G cell21 d21_1 = true := by decide +kernel
theorem subd21_1_0 : subd21_1 [-2, -3] = true := by decide +kernel
theorem subd21_1_1 : subd21_1 [-2, -2] = true := by decide +kernel
theorem subd21_1_2 : subd21_1 [-2, -1] = true := by decide +kernel
theorem subd21_1_3 : subd21_1 [-2, 0] = true := by decide +kernel
theorem subd21_1_4 : subd21_1 [-2, 1] = true := by decide +kernel
theorem subd21_1_5 : subd21_1 [-1, -3] = true := by decide +kernel
theorem subd21_1_6 : subd21_1 [-1, -2] = true := by decide +kernel
theorem subd21_1_7 : subd21_1 [-1, -1] = true := by decide +kernel
theorem subd21_1_8 : subd21_1 [-1, 0] = true := by decide +kernel
theorem subd21_1_9 : subd21_1 [-1, 1] = true := by decide +kernel
theorem subd21_1_10 : subd21_1 [-1, 2] = true := by decide +kernel
theorem subd21_1_11 : subd21_1 [0, -3] = true := by decide +kernel
theorem subd21_1_12 : subd21_1 [0, -2] = true := by decide +kernel
theorem subd21_1_13 : subd21_1 [0, -1] = true := by decide +kernel
theorem subd21_1_14 : subd21_1 [0, 0, -7] = true := by decide +kernel
theorem subd21_1_15 : subd21_1 [0, 0, -6] = true := by decide +kernel
theorem subd21_1_16 : subd21_1 [0, 0, -5] = true := by decide +kernel
theorem subd21_1_17 : subd21_1 [0, 0, -4] = true := by decide +kernel
theorem subd21_1_18 : subd21_1 [0, 0, -3] = true := by decide +kernel
theorem subd21_1_19 : subd21_1 [0, 0, -2] = true := by decide +kernel
theorem subd21_1_20 : subd21_1 [0, 0, -1] = true := by decide +kernel
theorem subd21_1_21 : subd21_1 [0, 0, 0] = true := by decide +kernel
theorem subd21_1_22 : subd21_1 [0, 0, 1] = true := by decide +kernel
theorem subd21_1_23 : subd21_1 [0, 0, 2] = true := by decide +kernel
theorem subd21_1_24 : subd21_1 [0, 0, 3] = true := by decide +kernel
theorem subd21_1_25 : subd21_1 [0, 0, 4] = true := by decide +kernel
theorem subd21_1_26 : subd21_1 [0, 0, 5] = true := by decide +kernel
theorem subd21_1_27 : subd21_1 [0, 0, 6] = true := by decide +kernel
theorem subd21_1_28 : subd21_1 [0, 1] = true := by decide +kernel
theorem subd21_1_29 : subd21_1 [0, 2] = true := by decide +kernel
theorem subd21_1_30 : subd21_1 [1, -3] = true := by decide +kernel
theorem subd21_1_31 : subd21_1 [1, -2] = true := by decide +kernel
theorem sbd21_1_0 : ∀ q ∈ blkd21_1_0, subd21_1 q = true := by
  unfold blkd21_1_0
  exact List.forall_mem_cons.2 ⟨subd21_1_0, List.forall_mem_cons.2 ⟨subd21_1_1, List.forall_mem_cons.2 ⟨subd21_1_2, List.forall_mem_cons.2 ⟨subd21_1_3, List.forall_mem_cons.2 ⟨subd21_1_4, List.forall_mem_cons.2 ⟨subd21_1_5, List.forall_mem_cons.2 ⟨subd21_1_6, List.forall_mem_cons.2 ⟨subd21_1_7, List.forall_mem_cons.2 ⟨subd21_1_8, List.forall_mem_cons.2 ⟨subd21_1_9, List.forall_mem_cons.2 ⟨subd21_1_10, List.forall_mem_cons.2 ⟨subd21_1_11, List.forall_mem_cons.2 ⟨subd21_1_12, List.forall_mem_cons.2 ⟨subd21_1_13, List.forall_mem_cons.2 ⟨subd21_1_14, List.forall_mem_cons.2 ⟨subd21_1_15, List.forall_mem_cons.2 ⟨subd21_1_16, List.forall_mem_cons.2 ⟨subd21_1_17, List.forall_mem_cons.2 ⟨subd21_1_18, List.forall_mem_cons.2 ⟨subd21_1_19, List.forall_mem_cons.2 ⟨subd21_1_20, List.forall_mem_cons.2 ⟨subd21_1_21, List.forall_mem_cons.2 ⟨subd21_1_22, List.forall_mem_cons.2 ⟨subd21_1_23, List.forall_mem_cons.2 ⟨subd21_1_24, List.forall_mem_cons.2 ⟨subd21_1_25, List.forall_mem_cons.2 ⟨subd21_1_26, List.forall_mem_cons.2 ⟨subd21_1_27, List.forall_mem_cons.2 ⟨subd21_1_28, List.forall_mem_cons.2 ⟨subd21_1_29, List.forall_mem_cons.2 ⟨subd21_1_30, List.forall_mem_cons.2 ⟨subd21_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd21_1_32 : subd21_1 [1, -1] = true := by decide +kernel
theorem subd21_1_33 : subd21_1 [1, 0] = true := by decide +kernel
theorem subd21_1_34 : subd21_1 [1, 1] = true := by decide +kernel
theorem subd21_1_35 : subd21_1 [1, 2] = true := by decide +kernel
theorem subd21_1_36 : subd21_1 [2, -2] = true := by decide +kernel
theorem subd21_1_37 : subd21_1 [2, -1] = true := by decide +kernel
theorem subd21_1_38 : subd21_1 [2, 0] = true := by decide +kernel
theorem subd21_1_39 : subd21_1 [2, 1] = true := by decide +kernel
theorem subd21_1_40 : subd21_1 [2, 2] = true := by decide +kernel
theorem sbd21_1_1 : ∀ q ∈ blkd21_1_1, subd21_1 q = true := by
  unfold blkd21_1_1
  exact List.forall_mem_cons.2 ⟨subd21_1_32, List.forall_mem_cons.2 ⟨subd21_1_33, List.forall_mem_cons.2 ⟨subd21_1_34, List.forall_mem_cons.2 ⟨subd21_1_35, List.forall_mem_cons.2 ⟨subd21_1_36, List.forall_mem_cons.2 ⟨subd21_1_37, List.forall_mem_cons.2 ⟨subd21_1_38, List.forall_mem_cons.2 ⟨subd21_1_39, List.forall_mem_cons.2 ⟨subd21_1_40, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd21_2 : ldCheck G d21_2.U d21_2.ms ldd21_2 = true := by decide +kernel
theorem pre_okd21_2 : subPre G cell21 d21_2 = true := by decide +kernel
theorem subd21_2_0 : subd21_2 [-3] = true := by decide +kernel
theorem subd21_2_1 : subd21_2 [-2, -3] = true := by decide +kernel
theorem subd21_2_2 : subd21_2 [-2, -2] = true := by decide +kernel
theorem subd21_2_3 : subd21_2 [-2, -1] = true := by decide +kernel
theorem subd21_2_4 : subd21_2 [-2, 0] = true := by decide +kernel
theorem subd21_2_5 : subd21_2 [-2, 1] = true := by decide +kernel
theorem subd21_2_6 : subd21_2 [-2, 2] = true := by decide +kernel
theorem subd21_2_7 : subd21_2 [-2, 3] = true := by decide +kernel
theorem subd21_2_8 : subd21_2 [-1, -4] = true := by decide +kernel
theorem subd21_2_9 : subd21_2 [-1, -3] = true := by decide +kernel
theorem subd21_2_10 : subd21_2 [-1, -2] = true := by decide +kernel
theorem subd21_2_11 : subd21_2 [-1, -1] = true := by decide +kernel
theorem subd21_2_12 : subd21_2 [-1, 0] = true := by decide +kernel
theorem subd21_2_13 : subd21_2 [-1, 1] = true := by decide +kernel
theorem subd21_2_14 : subd21_2 [-1, 2] = true := by decide +kernel
theorem subd21_2_15 : subd21_2 [-1, 3] = true := by decide +kernel
theorem subd21_2_16 : subd21_2 [0, -4] = true := by decide +kernel
theorem subd21_2_17 : subd21_2 [0, -3] = true := by decide +kernel
theorem subd21_2_18 : subd21_2 [0, -2] = true := by decide +kernel
theorem subd21_2_19 : subd21_2 [0, -1] = true := by decide +kernel
theorem subd21_2_20 : subd21_2 [0, 0] = true := by decide +kernel
theorem subd21_2_21 : subd21_2 [0, 1] = true := by decide +kernel
theorem subd21_2_22 : subd21_2 [0, 2] = true := by decide +kernel
theorem subd21_2_23 : subd21_2 [0, 3] = true := by decide +kernel
theorem subd21_2_24 : subd21_2 [1, -4] = true := by decide +kernel
theorem subd21_2_25 : subd21_2 [1, -3] = true := by decide +kernel
theorem subd21_2_26 : subd21_2 [1, -2] = true := by decide +kernel
theorem subd21_2_27 : subd21_2 [1, -1] = true := by decide +kernel
theorem subd21_2_28 : subd21_2 [1, 0] = true := by decide +kernel
theorem subd21_2_29 : subd21_2 [1, 1] = true := by decide +kernel
theorem subd21_2_30 : subd21_2 [1, 2] = true := by decide +kernel
theorem subd21_2_31 : subd21_2 [1, 3] = true := by decide +kernel
theorem sbd21_2_0 : ∀ q ∈ blkd21_2_0, subd21_2 q = true := by
  unfold blkd21_2_0
  exact List.forall_mem_cons.2 ⟨subd21_2_0, List.forall_mem_cons.2 ⟨subd21_2_1, List.forall_mem_cons.2 ⟨subd21_2_2, List.forall_mem_cons.2 ⟨subd21_2_3, List.forall_mem_cons.2 ⟨subd21_2_4, List.forall_mem_cons.2 ⟨subd21_2_5, List.forall_mem_cons.2 ⟨subd21_2_6, List.forall_mem_cons.2 ⟨subd21_2_7, List.forall_mem_cons.2 ⟨subd21_2_8, List.forall_mem_cons.2 ⟨subd21_2_9, List.forall_mem_cons.2 ⟨subd21_2_10, List.forall_mem_cons.2 ⟨subd21_2_11, List.forall_mem_cons.2 ⟨subd21_2_12, List.forall_mem_cons.2 ⟨subd21_2_13, List.forall_mem_cons.2 ⟨subd21_2_14, List.forall_mem_cons.2 ⟨subd21_2_15, List.forall_mem_cons.2 ⟨subd21_2_16, List.forall_mem_cons.2 ⟨subd21_2_17, List.forall_mem_cons.2 ⟨subd21_2_18, List.forall_mem_cons.2 ⟨subd21_2_19, List.forall_mem_cons.2 ⟨subd21_2_20, List.forall_mem_cons.2 ⟨subd21_2_21, List.forall_mem_cons.2 ⟨subd21_2_22, List.forall_mem_cons.2 ⟨subd21_2_23, List.forall_mem_cons.2 ⟨subd21_2_24, List.forall_mem_cons.2 ⟨subd21_2_25, List.forall_mem_cons.2 ⟨subd21_2_26, List.forall_mem_cons.2 ⟨subd21_2_27, List.forall_mem_cons.2 ⟨subd21_2_28, List.forall_mem_cons.2 ⟨subd21_2_29, List.forall_mem_cons.2 ⟨subd21_2_30, List.forall_mem_cons.2 ⟨subd21_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
