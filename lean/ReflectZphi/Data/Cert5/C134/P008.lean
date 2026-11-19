import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [-2] = true := by decide +kernel
theorem subd2_4_1 : subd2_4 [-1, -4] = true := by decide +kernel
theorem subd2_4_2 : subd2_4 [-1, -3] = true := by decide +kernel
theorem subd2_4_3 : subd2_4 [-1, -2] = true := by decide +kernel
theorem subd2_4_4 : subd2_4 [-1, -1] = true := by decide +kernel
theorem subd2_4_5 : subd2_4 [-1, 0] = true := by decide +kernel
theorem subd2_4_6 : subd2_4 [-1, 1] = true := by decide +kernel
theorem subd2_4_7 : subd2_4 [-1, 2] = true := by decide +kernel
theorem subd2_4_8 : subd2_4 [0, -3] = true := by decide +kernel
theorem subd2_4_9 : subd2_4 [0, -2] = true := by decide +kernel
theorem subd2_4_10 : subd2_4 [0, -1] = true := by decide +kernel
theorem subd2_4_11 : subd2_4 [0, 0] = true := by decide +kernel
theorem subd2_4_12 : subd2_4 [0, 1] = true := by decide +kernel
theorem subd2_4_13 : subd2_4 [0, 2] = true := by decide +kernel
theorem subd2_4_14 : subd2_4 [1, -3] = true := by decide +kernel
theorem subd2_4_15 : subd2_4 [1, -2] = true := by decide +kernel
theorem subd2_4_16 : subd2_4 [1, -1] = true := by decide +kernel
theorem subd2_4_17 : subd2_4 [1, 0] = true := by decide +kernel
theorem subd2_4_18 : subd2_4 [1, 1] = true := by decide +kernel
theorem subd2_4_19 : subd2_4 [1, 2] = true := by decide +kernel
theorem subd2_4_20 : subd2_4 [1, 3] = true := by decide +kernel
theorem subd2_4_21 : subd2_4 [2] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_cons.2 ⟨subd2_4_1, List.forall_mem_cons.2 ⟨subd2_4_2, List.forall_mem_cons.2 ⟨subd2_4_3, List.forall_mem_cons.2 ⟨subd2_4_4, List.forall_mem_cons.2 ⟨subd2_4_5, List.forall_mem_cons.2 ⟨subd2_4_6, List.forall_mem_cons.2 ⟨subd2_4_7, List.forall_mem_cons.2 ⟨subd2_4_8, List.forall_mem_cons.2 ⟨subd2_4_9, List.forall_mem_cons.2 ⟨subd2_4_10, List.forall_mem_cons.2 ⟨subd2_4_11, List.forall_mem_cons.2 ⟨subd2_4_12, List.forall_mem_cons.2 ⟨subd2_4_13, List.forall_mem_cons.2 ⟨subd2_4_14, List.forall_mem_cons.2 ⟨subd2_4_15, List.forall_mem_cons.2 ⟨subd2_4_16, List.forall_mem_cons.2 ⟨subd2_4_17, List.forall_mem_cons.2 ⟨subd2_4_18, List.forall_mem_cons.2 ⟨subd2_4_19, List.forall_mem_cons.2 ⟨subd2_4_20, List.forall_mem_cons.2 ⟨subd2_4_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel
theorem subd2_5_0 : subd2_5 [-3] = true := by decide +kernel
theorem subd2_5_1 : subd2_5 [-2, -4] = true := by decide +kernel
theorem subd2_5_2 : subd2_5 [-2, -3] = true := by decide +kernel
theorem subd2_5_3 : subd2_5 [-2, -2] = true := by decide +kernel
theorem subd2_5_4 : subd2_5 [-2, -1] = true := by decide +kernel
theorem subd2_5_5 : subd2_5 [-2, 0] = true := by decide +kernel
theorem subd2_5_6 : subd2_5 [-2, 1] = true := by decide +kernel
theorem subd2_5_7 : subd2_5 [-2, 2] = true := by decide +kernel
theorem subd2_5_8 : subd2_5 [-1, -5] = true := by decide +kernel
theorem subd2_5_9 : subd2_5 [-1, -4] = true := by decide +kernel
theorem subd2_5_10 : subd2_5 [-1, -3] = true := by decide +kernel
theorem subd2_5_11 : subd2_5 [-1, -2] = true := by decide +kernel
theorem subd2_5_12 : subd2_5 [-1, -1] = true := by decide +kernel
theorem subd2_5_13 : subd2_5 [-1, 0] = true := by decide +kernel
theorem subd2_5_14 : subd2_5 [-1, 1] = true := by decide +kernel
theorem subd2_5_15 : subd2_5 [-1, 2] = true := by decide +kernel
theorem subd2_5_16 : subd2_5 [-1, 3] = true := by decide +kernel
theorem subd2_5_17 : subd2_5 [0, -5] = true := by decide +kernel
theorem subd2_5_18 : subd2_5 [0, -4] = true := by decide +kernel
theorem subd2_5_19 : subd2_5 [0, -3] = true := by decide +kernel
theorem subd2_5_20 : subd2_5 [0, -2] = true := by decide +kernel
theorem subd2_5_21 : subd2_5 [0, -1] = true := by decide +kernel
theorem subd2_5_22 : subd2_5 [0, 0] = true := by decide +kernel
theorem subd2_5_23 : subd2_5 [0, 1] = true := by decide +kernel
theorem subd2_5_24 : subd2_5 [0, 2] = true := by decide +kernel
theorem subd2_5_25 : subd2_5 [0, 3] = true := by decide +kernel
theorem subd2_5_26 : subd2_5 [0, 4] = true := by decide +kernel
theorem subd2_5_27 : subd2_5 [1, -4] = true := by decide +kernel
theorem subd2_5_28 : subd2_5 [1, -3] = true := by decide +kernel
theorem subd2_5_29 : subd2_5 [1, -2] = true := by decide +kernel
theorem subd2_5_30 : subd2_5 [1, -1] = true := by decide +kernel
theorem subd2_5_31 : subd2_5 [1, 0] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_cons.2 ⟨subd2_5_1, List.forall_mem_cons.2 ⟨subd2_5_2, List.forall_mem_cons.2 ⟨subd2_5_3, List.forall_mem_cons.2 ⟨subd2_5_4, List.forall_mem_cons.2 ⟨subd2_5_5, List.forall_mem_cons.2 ⟨subd2_5_6, List.forall_mem_cons.2 ⟨subd2_5_7, List.forall_mem_cons.2 ⟨subd2_5_8, List.forall_mem_cons.2 ⟨subd2_5_9, List.forall_mem_cons.2 ⟨subd2_5_10, List.forall_mem_cons.2 ⟨subd2_5_11, List.forall_mem_cons.2 ⟨subd2_5_12, List.forall_mem_cons.2 ⟨subd2_5_13, List.forall_mem_cons.2 ⟨subd2_5_14, List.forall_mem_cons.2 ⟨subd2_5_15, List.forall_mem_cons.2 ⟨subd2_5_16, List.forall_mem_cons.2 ⟨subd2_5_17, List.forall_mem_cons.2 ⟨subd2_5_18, List.forall_mem_cons.2 ⟨subd2_5_19, List.forall_mem_cons.2 ⟨subd2_5_20, List.forall_mem_cons.2 ⟨subd2_5_21, List.forall_mem_cons.2 ⟨subd2_5_22, List.forall_mem_cons.2 ⟨subd2_5_23, List.forall_mem_cons.2 ⟨subd2_5_24, List.forall_mem_cons.2 ⟨subd2_5_25, List.forall_mem_cons.2 ⟨subd2_5_26, List.forall_mem_cons.2 ⟨subd2_5_27, List.forall_mem_cons.2 ⟨subd2_5_28, List.forall_mem_cons.2 ⟨subd2_5_29, List.forall_mem_cons.2 ⟨subd2_5_30, List.forall_mem_cons.2 ⟨subd2_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_5_32 : subd2_5 [1, 1] = true := by decide +kernel
theorem subd2_5_33 : subd2_5 [1, 2] = true := by decide +kernel
theorem subd2_5_34 : subd2_5 [1, 3] = true := by decide +kernel
theorem subd2_5_35 : subd2_5 [1, 4] = true := by decide +kernel
theorem subd2_5_36 : subd2_5 [2, -3] = true := by decide +kernel
theorem subd2_5_37 : subd2_5 [2, -2] = true := by decide +kernel
theorem subd2_5_38 : subd2_5 [2, -1] = true := by decide +kernel
theorem subd2_5_39 : subd2_5 [2, 0] = true := by decide +kernel
theorem subd2_5_40 : subd2_5 [2, 1] = true := by decide +kernel
theorem subd2_5_41 : subd2_5 [2, 2] = true := by decide +kernel
theorem subd2_5_42 : subd2_5 [2, 3] = true := by decide +kernel
theorem subd2_5_43 : subd2_5 [3] = true := by decide +kernel
theorem sbd2_5_1 : ∀ q ∈ blkd2_5_1, subd2_5 q = true := by
  unfold blkd2_5_1
  exact List.forall_mem_cons.2 ⟨subd2_5_32, List.forall_mem_cons.2 ⟨subd2_5_33, List.forall_mem_cons.2 ⟨subd2_5_34, List.forall_mem_cons.2 ⟨subd2_5_35, List.forall_mem_cons.2 ⟨subd2_5_36, List.forall_mem_cons.2 ⟨subd2_5_37, List.forall_mem_cons.2 ⟨subd2_5_38, List.forall_mem_cons.2 ⟨subd2_5_39, List.forall_mem_cons.2 ⟨subd2_5_40, List.forall_mem_cons.2 ⟨subd2_5_41, List.forall_mem_cons.2 ⟨subd2_5_42, List.forall_mem_cons.2 ⟨subd2_5_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_6 : ldCheck G d2_6.U d2_6.ms ldd2_6 = true := by decide +kernel
theorem pre_okd2_6 : subPre G cell2 d2_6 = true := by decide +kernel
theorem subd2_6_0 : subd2_6 [-3] = true := by decide +kernel
theorem subd2_6_1 : subd2_6 [-2, -3] = true := by decide +kernel
theorem subd2_6_2 : subd2_6 [-2, -2] = true := by decide +kernel
theorem subd2_6_3 : subd2_6 [-2, -1] = true := by decide +kernel
theorem subd2_6_4 : subd2_6 [-2, 0] = true := by decide +kernel
theorem subd2_6_5 : subd2_6 [-2, 1] = true := by decide +kernel
theorem subd2_6_6 : subd2_6 [-2, 2] = true := by decide +kernel
theorem subd2_6_7 : subd2_6 [-1, -4] = true := by decide +kernel
theorem subd2_6_8 : subd2_6 [-1, -3] = true := by decide +kernel
theorem subd2_6_9 : subd2_6 [-1, -2] = true := by decide +kernel
theorem subd2_6_10 : subd2_6 [-1, -1] = true := by decide +kernel
theorem subd2_6_11 : subd2_6 [-1, 0] = true := by decide +kernel
theorem subd2_6_12 : subd2_6 [-1, 1] = true := by decide +kernel
theorem subd2_6_13 : subd2_6 [-1, 2] = true := by decide +kernel
theorem subd2_6_14 : subd2_6 [-1, 3] = true := by decide +kernel
theorem subd2_6_15 : subd2_6 [0, -4] = true := by decide +kernel
theorem subd2_6_16 : subd2_6 [0, -3] = true := by decide +kernel
theorem subd2_6_17 : subd2_6 [0, -2] = true := by decide +kernel
theorem subd2_6_18 : subd2_6 [0, -1] = true := by decide +kernel
theorem subd2_6_19 : subd2_6 [0, 0] = true := by decide +kernel
theorem subd2_6_20 : subd2_6 [0, 1] = true := by decide +kernel
theorem subd2_6_21 : subd2_6 [0, 2] = true := by decide +kernel
theorem subd2_6_22 : subd2_6 [0, 3] = true := by decide +kernel
theorem subd2_6_23 : subd2_6 [1, -4] = true := by decide +kernel
theorem subd2_6_24 : subd2_6 [1, -3] = true := by decide +kernel
theorem subd2_6_25 : subd2_6 [1, -2] = true := by decide +kernel
theorem subd2_6_26 : subd2_6 [1, -1] = true := by decide +kernel
theorem subd2_6_27 : subd2_6 [1, 0] = true := by decide +kernel
theorem subd2_6_28 : subd2_6 [1, 1] = true := by decide +kernel
theorem subd2_6_29 : subd2_6 [1, 2] = true := by decide +kernel
theorem subd2_6_30 : subd2_6 [1, 3] = true := by decide +kernel
theorem subd2_6_31 : subd2_6 [2, -3] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_cons.2 ⟨subd2_6_1, List.forall_mem_cons.2 ⟨subd2_6_2, List.forall_mem_cons.2 ⟨subd2_6_3, List.forall_mem_cons.2 ⟨subd2_6_4, List.forall_mem_cons.2 ⟨subd2_6_5, List.forall_mem_cons.2 ⟨subd2_6_6, List.forall_mem_cons.2 ⟨subd2_6_7, List.forall_mem_cons.2 ⟨subd2_6_8, List.forall_mem_cons.2 ⟨subd2_6_9, List.forall_mem_cons.2 ⟨subd2_6_10, List.forall_mem_cons.2 ⟨subd2_6_11, List.forall_mem_cons.2 ⟨subd2_6_12, List.forall_mem_cons.2 ⟨subd2_6_13, List.forall_mem_cons.2 ⟨subd2_6_14, List.forall_mem_cons.2 ⟨subd2_6_15, List.forall_mem_cons.2 ⟨subd2_6_16, List.forall_mem_cons.2 ⟨subd2_6_17, List.forall_mem_cons.2 ⟨subd2_6_18, List.forall_mem_cons.2 ⟨subd2_6_19, List.forall_mem_cons.2 ⟨subd2_6_20, List.forall_mem_cons.2 ⟨subd2_6_21, List.forall_mem_cons.2 ⟨subd2_6_22, List.forall_mem_cons.2 ⟨subd2_6_23, List.forall_mem_cons.2 ⟨subd2_6_24, List.forall_mem_cons.2 ⟨subd2_6_25, List.forall_mem_cons.2 ⟨subd2_6_26, List.forall_mem_cons.2 ⟨subd2_6_27, List.forall_mem_cons.2 ⟨subd2_6_28, List.forall_mem_cons.2 ⟨subd2_6_29, List.forall_mem_cons.2 ⟨subd2_6_30, List.forall_mem_cons.2 ⟨subd2_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_6_32 : subd2_6 [2, -2] = true := by decide +kernel
theorem subd2_6_33 : subd2_6 [2, -1] = true := by decide +kernel
theorem subd2_6_34 : subd2_6 [2, 0] = true := by decide +kernel
theorem subd2_6_35 : subd2_6 [2, 1] = true := by decide +kernel
theorem subd2_6_36 : subd2_6 [2, 2] = true := by decide +kernel
theorem subd2_6_37 : subd2_6 [3] = true := by decide +kernel
theorem sbd2_6_1 : ∀ q ∈ blkd2_6_1, subd2_6 q = true := by
  unfold blkd2_6_1
  exact List.forall_mem_cons.2 ⟨subd2_6_32, List.forall_mem_cons.2 ⟨subd2_6_33, List.forall_mem_cons.2 ⟨subd2_6_34, List.forall_mem_cons.2 ⟨subd2_6_35, List.forall_mem_cons.2 ⟨subd2_6_36, List.forall_mem_cons.2 ⟨subd2_6_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd2_7 : ldCheck G d2_7.U d2_7.ms ldd2_7 = true := by decide +kernel
theorem pre_okd2_7 : subPre G cell2 d2_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
