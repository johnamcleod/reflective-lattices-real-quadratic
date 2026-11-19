import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_0 : subd5_1 [-3] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-2, -3] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-2, -2] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-2, -1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-2, 0] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-2, 1] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-2, 2] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-2, 3] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-1, -4] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [-1, 3] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [0, -4] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [0, 3] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [1, -4] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [1, 2] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [1, 3] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [2, -4] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [2, -3] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [2, -2] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [2, -1] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [2, 0] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [2, 1] = true := by decide +kernel
theorem subd5_1_38 : subd5_1 [2, 2] = true := by decide +kernel
theorem subd5_1_39 : subd5_1 [3] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_cons.2 ⟨subd5_1_38, List.forall_mem_cons.2 ⟨subd5_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-3] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-2, -4] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-1, 0] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [0, -5] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [0, 0] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [0, 4] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [1, 0] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [2, 0] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [2, 3] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [3] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-3] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [2, 0] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [2, 1] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [2, 2] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [3] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_nil _⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-3] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-2, -4] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-2, -3] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-2, -2] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-2, -1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-2, 0] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [-2, 1] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [-2, 2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [-2, 3] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [-2, 4] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [-1, -4] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [-1, -3] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [-1, -2] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [-1, -1] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [-1, 0] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [-1, 1] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [-1, 2] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [-1, 3] = true := by decide +kernel
theorem subd5_4_18 : subd5_4 [-1, 4] = true := by decide +kernel
theorem subd5_4_19 : subd5_4 [0, -5] = true := by decide +kernel
theorem subd5_4_20 : subd5_4 [0, -4] = true := by decide +kernel
theorem subd5_4_21 : subd5_4 [0, -3] = true := by decide +kernel
theorem subd5_4_22 : subd5_4 [0, -2] = true := by decide +kernel
theorem subd5_4_23 : subd5_4 [0, -1] = true := by decide +kernel
theorem subd5_4_24 : subd5_4 [0, 0] = true := by decide +kernel
theorem subd5_4_25 : subd5_4 [0, 1] = true := by decide +kernel
theorem subd5_4_26 : subd5_4 [0, 2] = true := by decide +kernel
theorem subd5_4_27 : subd5_4 [0, 3] = true := by decide +kernel
theorem subd5_4_28 : subd5_4 [0, 4] = true := by decide +kernel
theorem subd5_4_29 : subd5_4 [1, -5] = true := by decide +kernel
theorem subd5_4_30 : subd5_4 [1, -4] = true := by decide +kernel
theorem subd5_4_31 : subd5_4 [1, -3] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_cons.2 ⟨subd5_4_18, List.forall_mem_cons.2 ⟨subd5_4_19, List.forall_mem_cons.2 ⟨subd5_4_20, List.forall_mem_cons.2 ⟨subd5_4_21, List.forall_mem_cons.2 ⟨subd5_4_22, List.forall_mem_cons.2 ⟨subd5_4_23, List.forall_mem_cons.2 ⟨subd5_4_24, List.forall_mem_cons.2 ⟨subd5_4_25, List.forall_mem_cons.2 ⟨subd5_4_26, List.forall_mem_cons.2 ⟨subd5_4_27, List.forall_mem_cons.2 ⟨subd5_4_28, List.forall_mem_cons.2 ⟨subd5_4_29, List.forall_mem_cons.2 ⟨subd5_4_30, List.forall_mem_cons.2 ⟨subd5_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C134
