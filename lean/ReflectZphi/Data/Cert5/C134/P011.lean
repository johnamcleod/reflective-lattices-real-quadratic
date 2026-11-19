import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_6_0 : subd3_6 [-3] = true := by decide +kernel
theorem subd3_6_1 : subd3_6 [-2, -4] = true := by decide +kernel
theorem subd3_6_2 : subd3_6 [-2, -3] = true := by decide +kernel
theorem subd3_6_3 : subd3_6 [-2, -2] = true := by decide +kernel
theorem subd3_6_4 : subd3_6 [-2, -1] = true := by decide +kernel
theorem subd3_6_5 : subd3_6 [-2, 0] = true := by decide +kernel
theorem subd3_6_6 : subd3_6 [-2, 1] = true := by decide +kernel
theorem subd3_6_7 : subd3_6 [-2, 2] = true := by decide +kernel
theorem subd3_6_8 : subd3_6 [-1, -4] = true := by decide +kernel
theorem subd3_6_9 : subd3_6 [-1, -3] = true := by decide +kernel
theorem subd3_6_10 : subd3_6 [-1, -2] = true := by decide +kernel
theorem subd3_6_11 : subd3_6 [-1, -1] = true := by decide +kernel
theorem subd3_6_12 : subd3_6 [-1, 0] = true := by decide +kernel
theorem subd3_6_13 : subd3_6 [-1, 1] = true := by decide +kernel
theorem subd3_6_14 : subd3_6 [-1, 2] = true := by decide +kernel
theorem subd3_6_15 : subd3_6 [-1, 3] = true := by decide +kernel
theorem subd3_6_16 : subd3_6 [0, -4] = true := by decide +kernel
theorem subd3_6_17 : subd3_6 [0, -3] = true := by decide +kernel
theorem subd3_6_18 : subd3_6 [0, -2] = true := by decide +kernel
theorem subd3_6_19 : subd3_6 [0, -1] = true := by decide +kernel
theorem subd3_6_20 : subd3_6 [0, 0] = true := by decide +kernel
theorem subd3_6_21 : subd3_6 [0, 1] = true := by decide +kernel
theorem subd3_6_22 : subd3_6 [0, 2] = true := by decide +kernel
theorem subd3_6_23 : subd3_6 [0, 3] = true := by decide +kernel
theorem subd3_6_24 : subd3_6 [1, -4] = true := by decide +kernel
theorem subd3_6_25 : subd3_6 [1, -3] = true := by decide +kernel
theorem subd3_6_26 : subd3_6 [1, -2] = true := by decide +kernel
theorem subd3_6_27 : subd3_6 [1, -1] = true := by decide +kernel
theorem subd3_6_28 : subd3_6 [1, 0] = true := by decide +kernel
theorem subd3_6_29 : subd3_6 [1, 1] = true := by decide +kernel
theorem subd3_6_30 : subd3_6 [1, 2] = true := by decide +kernel
theorem subd3_6_31 : subd3_6 [1, 3] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_cons.2 ⟨subd3_6_1, List.forall_mem_cons.2 ⟨subd3_6_2, List.forall_mem_cons.2 ⟨subd3_6_3, List.forall_mem_cons.2 ⟨subd3_6_4, List.forall_mem_cons.2 ⟨subd3_6_5, List.forall_mem_cons.2 ⟨subd3_6_6, List.forall_mem_cons.2 ⟨subd3_6_7, List.forall_mem_cons.2 ⟨subd3_6_8, List.forall_mem_cons.2 ⟨subd3_6_9, List.forall_mem_cons.2 ⟨subd3_6_10, List.forall_mem_cons.2 ⟨subd3_6_11, List.forall_mem_cons.2 ⟨subd3_6_12, List.forall_mem_cons.2 ⟨subd3_6_13, List.forall_mem_cons.2 ⟨subd3_6_14, List.forall_mem_cons.2 ⟨subd3_6_15, List.forall_mem_cons.2 ⟨subd3_6_16, List.forall_mem_cons.2 ⟨subd3_6_17, List.forall_mem_cons.2 ⟨subd3_6_18, List.forall_mem_cons.2 ⟨subd3_6_19, List.forall_mem_cons.2 ⟨subd3_6_20, List.forall_mem_cons.2 ⟨subd3_6_21, List.forall_mem_cons.2 ⟨subd3_6_22, List.forall_mem_cons.2 ⟨subd3_6_23, List.forall_mem_cons.2 ⟨subd3_6_24, List.forall_mem_cons.2 ⟨subd3_6_25, List.forall_mem_cons.2 ⟨subd3_6_26, List.forall_mem_cons.2 ⟨subd3_6_27, List.forall_mem_cons.2 ⟨subd3_6_28, List.forall_mem_cons.2 ⟨subd3_6_29, List.forall_mem_cons.2 ⟨subd3_6_30, List.forall_mem_cons.2 ⟨subd3_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_32 : subd3_6 [2, -3] = true := by decide +kernel
theorem subd3_6_33 : subd3_6 [2, -2] = true := by decide +kernel
theorem subd3_6_34 : subd3_6 [2, -1] = true := by decide +kernel
theorem subd3_6_35 : subd3_6 [2, 0] = true := by decide +kernel
theorem subd3_6_36 : subd3_6 [2, 1] = true := by decide +kernel
theorem subd3_6_37 : subd3_6 [2, 2] = true := by decide +kernel
theorem subd3_6_38 : subd3_6 [2, 3] = true := by decide +kernel
theorem subd3_6_39 : subd3_6 [3] = true := by decide +kernel
theorem sbd3_6_1 : ∀ q ∈ blkd3_6_1, subd3_6 q = true := by
  unfold blkd3_6_1
  exact List.forall_mem_cons.2 ⟨subd3_6_32, List.forall_mem_cons.2 ⟨subd3_6_33, List.forall_mem_cons.2 ⟨subd3_6_34, List.forall_mem_cons.2 ⟨subd3_6_35, List.forall_mem_cons.2 ⟨subd3_6_36, List.forall_mem_cons.2 ⟨subd3_6_37, List.forall_mem_cons.2 ⟨subd3_6_38, List.forall_mem_cons.2 ⟨subd3_6_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [-4] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [-3] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [-2, -3] = true := by decide +kernel
theorem subd3_7_3 : subd3_7 [-2, -2] = true := by decide +kernel
theorem subd3_7_4 : subd3_7 [-2, -1] = true := by decide +kernel
theorem subd3_7_5 : subd3_7 [-2, 0] = true := by decide +kernel
theorem subd3_7_6 : subd3_7 [-2, 1] = true := by decide +kernel
theorem subd3_7_7 : subd3_7 [-2, 2] = true := by decide +kernel
theorem subd3_7_8 : subd3_7 [-2, 3] = true := by decide +kernel
theorem subd3_7_9 : subd3_7 [-2, 4] = true := by decide +kernel
theorem subd3_7_10 : subd3_7 [-1, -4] = true := by decide +kernel
theorem subd3_7_11 : subd3_7 [-1, -3] = true := by decide +kernel
theorem subd3_7_12 : subd3_7 [-1, -2] = true := by decide +kernel
theorem subd3_7_13 : subd3_7 [-1, -1] = true := by decide +kernel
theorem subd3_7_14 : subd3_7 [-1, 0] = true := by decide +kernel
theorem subd3_7_15 : subd3_7 [-1, 1] = true := by decide +kernel
theorem subd3_7_16 : subd3_7 [-1, 2] = true := by decide +kernel
theorem subd3_7_17 : subd3_7 [-1, 3] = true := by decide +kernel
theorem subd3_7_18 : subd3_7 [-1, 4] = true := by decide +kernel
theorem subd3_7_19 : subd3_7 [0, -4] = true := by decide +kernel
theorem subd3_7_20 : subd3_7 [0, -3] = true := by decide +kernel
theorem subd3_7_21 : subd3_7 [0, -2] = true := by decide +kernel
theorem subd3_7_22 : subd3_7 [0, -1] = true := by decide +kernel
theorem subd3_7_23 : subd3_7 [0, 0] = true := by decide +kernel
theorem subd3_7_24 : subd3_7 [0, 1] = true := by decide +kernel
theorem subd3_7_25 : subd3_7 [0, 2] = true := by decide +kernel
theorem subd3_7_26 : subd3_7 [0, 3] = true := by decide +kernel
theorem subd3_7_27 : subd3_7 [1, -5] = true := by decide +kernel
theorem subd3_7_28 : subd3_7 [1, -4] = true := by decide +kernel
theorem subd3_7_29 : subd3_7 [1, -3] = true := by decide +kernel
theorem subd3_7_30 : subd3_7 [1, -2] = true := by decide +kernel
theorem subd3_7_31 : subd3_7 [1, -1] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_cons.2 ⟨subd3_7_3, List.forall_mem_cons.2 ⟨subd3_7_4, List.forall_mem_cons.2 ⟨subd3_7_5, List.forall_mem_cons.2 ⟨subd3_7_6, List.forall_mem_cons.2 ⟨subd3_7_7, List.forall_mem_cons.2 ⟨subd3_7_8, List.forall_mem_cons.2 ⟨subd3_7_9, List.forall_mem_cons.2 ⟨subd3_7_10, List.forall_mem_cons.2 ⟨subd3_7_11, List.forall_mem_cons.2 ⟨subd3_7_12, List.forall_mem_cons.2 ⟨subd3_7_13, List.forall_mem_cons.2 ⟨subd3_7_14, List.forall_mem_cons.2 ⟨subd3_7_15, List.forall_mem_cons.2 ⟨subd3_7_16, List.forall_mem_cons.2 ⟨subd3_7_17, List.forall_mem_cons.2 ⟨subd3_7_18, List.forall_mem_cons.2 ⟨subd3_7_19, List.forall_mem_cons.2 ⟨subd3_7_20, List.forall_mem_cons.2 ⟨subd3_7_21, List.forall_mem_cons.2 ⟨subd3_7_22, List.forall_mem_cons.2 ⟨subd3_7_23, List.forall_mem_cons.2 ⟨subd3_7_24, List.forall_mem_cons.2 ⟨subd3_7_25, List.forall_mem_cons.2 ⟨subd3_7_26, List.forall_mem_cons.2 ⟨subd3_7_27, List.forall_mem_cons.2 ⟨subd3_7_28, List.forall_mem_cons.2 ⟨subd3_7_29, List.forall_mem_cons.2 ⟨subd3_7_30, List.forall_mem_cons.2 ⟨subd3_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_7_32 : subd3_7 [1, 0] = true := by decide +kernel
theorem subd3_7_33 : subd3_7 [1, 1] = true := by decide +kernel
theorem subd3_7_34 : subd3_7 [1, 2] = true := by decide +kernel
theorem subd3_7_35 : subd3_7 [1, 3] = true := by decide +kernel
theorem subd3_7_36 : subd3_7 [2, -5] = true := by decide +kernel
theorem subd3_7_37 : subd3_7 [2, -4] = true := by decide +kernel
theorem subd3_7_38 : subd3_7 [2, -3] = true := by decide +kernel
theorem subd3_7_39 : subd3_7 [2, -2] = true := by decide +kernel
theorem subd3_7_40 : subd3_7 [2, -1] = true := by decide +kernel
theorem subd3_7_41 : subd3_7 [2, 0] = true := by decide +kernel
theorem subd3_7_42 : subd3_7 [2, 1] = true := by decide +kernel
theorem subd3_7_43 : subd3_7 [2, 2] = true := by decide +kernel
theorem subd3_7_44 : subd3_7 [3] = true := by decide +kernel
theorem subd3_7_45 : subd3_7 [4] = true := by decide +kernel
theorem sbd3_7_1 : ∀ q ∈ blkd3_7_1, subd3_7 q = true := by
  unfold blkd3_7_1
  exact List.forall_mem_cons.2 ⟨subd3_7_32, List.forall_mem_cons.2 ⟨subd3_7_33, List.forall_mem_cons.2 ⟨subd3_7_34, List.forall_mem_cons.2 ⟨subd3_7_35, List.forall_mem_cons.2 ⟨subd3_7_36, List.forall_mem_cons.2 ⟨subd3_7_37, List.forall_mem_cons.2 ⟨subd3_7_38, List.forall_mem_cons.2 ⟨subd3_7_39, List.forall_mem_cons.2 ⟨subd3_7_40, List.forall_mem_cons.2 ⟨subd3_7_41, List.forall_mem_cons.2 ⟨subd3_7_42, List.forall_mem_cons.2 ⟨subd3_7_43, List.forall_mem_cons.2 ⟨subd3_7_44, List.forall_mem_cons.2 ⟨subd3_7_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-3] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-2, -5] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-2, -4] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-2, -3] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-2, -2] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-2, -1] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-2, 0] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [-2, 1] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [-2, 2] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [-1, -5] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [-1, -4] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [-1, 3] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [0, -4] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_20 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_21 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_22 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_23 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_24 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_25 : subd4_0 [0, 3] = true := by decide +kernel
theorem subd4_0_26 : subd4_0 [1, -4] = true := by decide +kernel
theorem subd4_0_27 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_28 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_29 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_30 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_31 : subd4_0 [1, 1] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_cons.2 ⟨subd4_0_20, List.forall_mem_cons.2 ⟨subd4_0_21, List.forall_mem_cons.2 ⟨subd4_0_22, List.forall_mem_cons.2 ⟨subd4_0_23, List.forall_mem_cons.2 ⟨subd4_0_24, List.forall_mem_cons.2 ⟨subd4_0_25, List.forall_mem_cons.2 ⟨subd4_0_26, List.forall_mem_cons.2 ⟨subd4_0_27, List.forall_mem_cons.2 ⟨subd4_0_28, List.forall_mem_cons.2 ⟨subd4_0_29, List.forall_mem_cons.2 ⟨subd4_0_30, List.forall_mem_cons.2 ⟨subd4_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_32 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_33 : subd4_0 [1, 3] = true := by decide +kernel
theorem subd4_0_34 : subd4_0 [1, 4] = true := by decide +kernel
theorem subd4_0_35 : subd4_0 [2, -3] = true := by decide +kernel
theorem subd4_0_36 : subd4_0 [2, -2] = true := by decide +kernel
theorem subd4_0_37 : subd4_0 [2, -1] = true := by decide +kernel
theorem subd4_0_38 : subd4_0 [2, 0] = true := by decide +kernel
theorem subd4_0_39 : subd4_0 [2, 1] = true := by decide +kernel
theorem subd4_0_40 : subd4_0 [2, 2] = true := by decide +kernel
theorem subd4_0_41 : subd4_0 [2, 3] = true := by decide +kernel
theorem subd4_0_42 : subd4_0 [2, 4] = true := by decide +kernel
theorem subd4_0_43 : subd4_0 [3] = true := by decide +kernel
theorem sbd4_0_1 : ∀ q ∈ blkd4_0_1, subd4_0 q = true := by
  unfold blkd4_0_1
  exact List.forall_mem_cons.2 ⟨subd4_0_32, List.forall_mem_cons.2 ⟨subd4_0_33, List.forall_mem_cons.2 ⟨subd4_0_34, List.forall_mem_cons.2 ⟨subd4_0_35, List.forall_mem_cons.2 ⟨subd4_0_36, List.forall_mem_cons.2 ⟨subd4_0_37, List.forall_mem_cons.2 ⟨subd4_0_38, List.forall_mem_cons.2 ⟨subd4_0_39, List.forall_mem_cons.2 ⟨subd4_0_40, List.forall_mem_cons.2 ⟨subd4_0_41, List.forall_mem_cons.2 ⟨subd4_0_42, List.forall_mem_cons.2 ⟨subd4_0_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-3] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-2] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [2] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [3] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C134
