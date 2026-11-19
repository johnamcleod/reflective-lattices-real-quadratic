import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [-2] = true := by decide +kernel
theorem subd0_3_1 : subd0_3 [-1, -3] = true := by decide +kernel
theorem subd0_3_2 : subd0_3 [-1, -2] = true := by decide +kernel
theorem subd0_3_3 : subd0_3 [-1, -1] = true := by decide +kernel
theorem subd0_3_4 : subd0_3 [-1, 0] = true := by decide +kernel
theorem subd0_3_5 : subd0_3 [-1, 1] = true := by decide +kernel
theorem subd0_3_6 : subd0_3 [-1, 2] = true := by decide +kernel
theorem subd0_3_7 : subd0_3 [0, -3] = true := by decide +kernel
theorem subd0_3_8 : subd0_3 [0, -2] = true := by decide +kernel
theorem subd0_3_9 : subd0_3 [0, -1] = true := by decide +kernel
theorem subd0_3_10 : subd0_3 [0, 0, -7] = true := by decide +kernel
theorem subd0_3_11 : subd0_3 [0, 0, -6] = true := by decide +kernel
theorem subd0_3_12 : subd0_3 [0, 0, -5] = true := by decide +kernel
theorem subd0_3_13 : subd0_3 [0, 0, -4] = true := by decide +kernel
theorem subd0_3_14 : subd0_3 [0, 0, -3] = true := by decide +kernel
theorem subd0_3_15 : subd0_3 [0, 0, -2] = true := by decide +kernel
theorem subd0_3_16 : subd0_3 [0, 0, -1] = true := by decide +kernel
theorem subd0_3_17 : subd0_3 [0, 0, 0] = true := by decide +kernel
theorem subd0_3_18 : subd0_3 [0, 0, 1] = true := by decide +kernel
theorem subd0_3_19 : subd0_3 [0, 0, 2] = true := by decide +kernel
theorem subd0_3_20 : subd0_3 [0, 0, 3] = true := by decide +kernel
theorem subd0_3_21 : subd0_3 [0, 0, 4] = true := by decide +kernel
theorem subd0_3_22 : subd0_3 [0, 0, 5] = true := by decide +kernel
theorem subd0_3_23 : subd0_3 [0, 0, 6] = true := by decide +kernel
theorem subd0_3_24 : subd0_3 [0, 1] = true := by decide +kernel
theorem subd0_3_25 : subd0_3 [0, 2] = true := by decide +kernel
theorem subd0_3_26 : subd0_3 [1, -3] = true := by decide +kernel
theorem subd0_3_27 : subd0_3 [1, -2] = true := by decide +kernel
theorem subd0_3_28 : subd0_3 [1, -1] = true := by decide +kernel
theorem subd0_3_29 : subd0_3 [1, 0] = true := by decide +kernel
theorem subd0_3_30 : subd0_3 [1, 1] = true := by decide +kernel
theorem subd0_3_31 : subd0_3 [1, 2] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_cons.2 ⟨subd0_3_1, List.forall_mem_cons.2 ⟨subd0_3_2, List.forall_mem_cons.2 ⟨subd0_3_3, List.forall_mem_cons.2 ⟨subd0_3_4, List.forall_mem_cons.2 ⟨subd0_3_5, List.forall_mem_cons.2 ⟨subd0_3_6, List.forall_mem_cons.2 ⟨subd0_3_7, List.forall_mem_cons.2 ⟨subd0_3_8, List.forall_mem_cons.2 ⟨subd0_3_9, List.forall_mem_cons.2 ⟨subd0_3_10, List.forall_mem_cons.2 ⟨subd0_3_11, List.forall_mem_cons.2 ⟨subd0_3_12, List.forall_mem_cons.2 ⟨subd0_3_13, List.forall_mem_cons.2 ⟨subd0_3_14, List.forall_mem_cons.2 ⟨subd0_3_15, List.forall_mem_cons.2 ⟨subd0_3_16, List.forall_mem_cons.2 ⟨subd0_3_17, List.forall_mem_cons.2 ⟨subd0_3_18, List.forall_mem_cons.2 ⟨subd0_3_19, List.forall_mem_cons.2 ⟨subd0_3_20, List.forall_mem_cons.2 ⟨subd0_3_21, List.forall_mem_cons.2 ⟨subd0_3_22, List.forall_mem_cons.2 ⟨subd0_3_23, List.forall_mem_cons.2 ⟨subd0_3_24, List.forall_mem_cons.2 ⟨subd0_3_25, List.forall_mem_cons.2 ⟨subd0_3_26, List.forall_mem_cons.2 ⟨subd0_3_27, List.forall_mem_cons.2 ⟨subd0_3_28, List.forall_mem_cons.2 ⟨subd0_3_29, List.forall_mem_cons.2 ⟨subd0_3_30, List.forall_mem_cons.2 ⟨subd0_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_3_32 : subd0_3 [2] = true := by decide +kernel
theorem sbd0_3_1 : ∀ q ∈ blkd0_3_1, subd0_3 q = true := by
  unfold blkd0_3_1
  exact List.forall_mem_cons.2 ⟨subd0_3_32, List.forall_mem_nil _⟩
theorem ld_okd0_4 : ldCheck G d0_4.U d0_4.ms ldd0_4 = true := by decide +kernel
theorem pre_okd0_4 : subPre G cell0 d0_4 = true := by decide +kernel
theorem subd0_4_0 : subd0_4 [-3] = true := by decide +kernel
theorem subd0_4_1 : subd0_4 [-2, -5] = true := by decide +kernel
theorem subd0_4_2 : subd0_4 [-2, -4] = true := by decide +kernel
theorem subd0_4_3 : subd0_4 [-2, -3] = true := by decide +kernel
theorem subd0_4_4 : subd0_4 [-2, -2] = true := by decide +kernel
theorem subd0_4_5 : subd0_4 [-2, -1] = true := by decide +kernel
theorem subd0_4_6 : subd0_4 [-2, 0] = true := by decide +kernel
theorem subd0_4_7 : subd0_4 [-2, 1] = true := by decide +kernel
theorem subd0_4_8 : subd0_4 [-2, 2] = true := by decide +kernel
theorem subd0_4_9 : subd0_4 [-2, 3] = true := by decide +kernel
theorem subd0_4_10 : subd0_4 [-1, -5] = true := by decide +kernel
theorem subd0_4_11 : subd0_4 [-1, -4] = true := by decide +kernel
theorem subd0_4_12 : subd0_4 [-1, -3] = true := by decide +kernel
theorem subd0_4_13 : subd0_4 [-1, -2] = true := by decide +kernel
theorem subd0_4_14 : subd0_4 [-1, -1] = true := by decide +kernel
theorem subd0_4_15 : subd0_4 [-1, 0] = true := by decide +kernel
theorem subd0_4_16 : subd0_4 [-1, 1] = true := by decide +kernel
theorem subd0_4_17 : subd0_4 [-1, 2] = true := by decide +kernel
theorem subd0_4_18 : subd0_4 [-1, 3] = true := by decide +kernel
theorem subd0_4_19 : subd0_4 [0, -5] = true := by decide +kernel
theorem subd0_4_20 : subd0_4 [0, -4] = true := by decide +kernel
theorem subd0_4_21 : subd0_4 [0, -3] = true := by decide +kernel
theorem subd0_4_22 : subd0_4 [0, -2] = true := by decide +kernel
theorem subd0_4_23 : subd0_4 [0, -1] = true := by decide +kernel
theorem subd0_4_24 : subd0_4 [0, 0] = true := by decide +kernel
theorem subd0_4_25 : subd0_4 [0, 1] = true := by decide +kernel
theorem subd0_4_26 : subd0_4 [0, 2] = true := by decide +kernel
theorem subd0_4_27 : subd0_4 [0, 3] = true := by decide +kernel
theorem subd0_4_28 : subd0_4 [0, 4] = true := by decide +kernel
theorem subd0_4_29 : subd0_4 [1, -4] = true := by decide +kernel
theorem subd0_4_30 : subd0_4 [1, -3] = true := by decide +kernel
theorem subd0_4_31 : subd0_4 [1, -2] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_cons.2 ⟨subd0_4_1, List.forall_mem_cons.2 ⟨subd0_4_2, List.forall_mem_cons.2 ⟨subd0_4_3, List.forall_mem_cons.2 ⟨subd0_4_4, List.forall_mem_cons.2 ⟨subd0_4_5, List.forall_mem_cons.2 ⟨subd0_4_6, List.forall_mem_cons.2 ⟨subd0_4_7, List.forall_mem_cons.2 ⟨subd0_4_8, List.forall_mem_cons.2 ⟨subd0_4_9, List.forall_mem_cons.2 ⟨subd0_4_10, List.forall_mem_cons.2 ⟨subd0_4_11, List.forall_mem_cons.2 ⟨subd0_4_12, List.forall_mem_cons.2 ⟨subd0_4_13, List.forall_mem_cons.2 ⟨subd0_4_14, List.forall_mem_cons.2 ⟨subd0_4_15, List.forall_mem_cons.2 ⟨subd0_4_16, List.forall_mem_cons.2 ⟨subd0_4_17, List.forall_mem_cons.2 ⟨subd0_4_18, List.forall_mem_cons.2 ⟨subd0_4_19, List.forall_mem_cons.2 ⟨subd0_4_20, List.forall_mem_cons.2 ⟨subd0_4_21, List.forall_mem_cons.2 ⟨subd0_4_22, List.forall_mem_cons.2 ⟨subd0_4_23, List.forall_mem_cons.2 ⟨subd0_4_24, List.forall_mem_cons.2 ⟨subd0_4_25, List.forall_mem_cons.2 ⟨subd0_4_26, List.forall_mem_cons.2 ⟨subd0_4_27, List.forall_mem_cons.2 ⟨subd0_4_28, List.forall_mem_cons.2 ⟨subd0_4_29, List.forall_mem_cons.2 ⟨subd0_4_30, List.forall_mem_cons.2 ⟨subd0_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_4_32 : subd0_4 [1, -1] = true := by decide +kernel
theorem subd0_4_33 : subd0_4 [1, 0] = true := by decide +kernel
theorem subd0_4_34 : subd0_4 [1, 1] = true := by decide +kernel
theorem subd0_4_35 : subd0_4 [1, 2] = true := by decide +kernel
theorem subd0_4_36 : subd0_4 [1, 3] = true := by decide +kernel
theorem subd0_4_37 : subd0_4 [1, 4] = true := by decide +kernel
theorem subd0_4_38 : subd0_4 [2, -4] = true := by decide +kernel
theorem subd0_4_39 : subd0_4 [2, -3] = true := by decide +kernel
theorem subd0_4_40 : subd0_4 [2, -2] = true := by decide +kernel
theorem subd0_4_41 : subd0_4 [2, -1] = true := by decide +kernel
theorem subd0_4_42 : subd0_4 [2, 0] = true := by decide +kernel
theorem subd0_4_43 : subd0_4 [2, 1] = true := by decide +kernel
theorem subd0_4_44 : subd0_4 [2, 2] = true := by decide +kernel
theorem subd0_4_45 : subd0_4 [2, 3] = true := by decide +kernel
theorem subd0_4_46 : subd0_4 [2, 4] = true := by decide +kernel
theorem subd0_4_47 : subd0_4 [3] = true := by decide +kernel
theorem sbd0_4_1 : ∀ q ∈ blkd0_4_1, subd0_4 q = true := by
  unfold blkd0_4_1
  exact List.forall_mem_cons.2 ⟨subd0_4_32, List.forall_mem_cons.2 ⟨subd0_4_33, List.forall_mem_cons.2 ⟨subd0_4_34, List.forall_mem_cons.2 ⟨subd0_4_35, List.forall_mem_cons.2 ⟨subd0_4_36, List.forall_mem_cons.2 ⟨subd0_4_37, List.forall_mem_cons.2 ⟨subd0_4_38, List.forall_mem_cons.2 ⟨subd0_4_39, List.forall_mem_cons.2 ⟨subd0_4_40, List.forall_mem_cons.2 ⟨subd0_4_41, List.forall_mem_cons.2 ⟨subd0_4_42, List.forall_mem_cons.2 ⟨subd0_4_43, List.forall_mem_cons.2 ⟨subd0_4_44, List.forall_mem_cons.2 ⟨subd0_4_45, List.forall_mem_cons.2 ⟨subd0_4_46, List.forall_mem_cons.2 ⟨subd0_4_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_5 : ldCheck G d0_5.U d0_5.ms ldd0_5 = true := by decide +kernel
theorem pre_okd0_5 : subPre G cell0 d0_5 = true := by decide +kernel
theorem subd0_5_0 : subd0_5 [-1, -2] = true := by decide +kernel
theorem subd0_5_1 : subd0_5 [-1, -1] = true := by decide +kernel
theorem subd0_5_2 : subd0_5 [-1, 0, -8] = true := by decide +kernel
theorem subd0_5_3 : subd0_5 [-1, 0, -7] = true := by decide +kernel
theorem subd0_5_4 : subd0_5 [-1, 0, -6] = true := by decide +kernel
theorem subd0_5_5 : subd0_5 [-1, 0, -5] = true := by decide +kernel
theorem subd0_5_6 : subd0_5 [-1, 0, -4] = true := by decide +kernel
theorem subd0_5_7 : subd0_5 [-1, 0, -3] = true := by decide +kernel
theorem subd0_5_8 : subd0_5 [-1, 0, -2] = true := by decide +kernel
theorem subd0_5_9 : subd0_5 [-1, 0, -1] = true := by decide +kernel
theorem subd0_5_10 : subd0_5 [-1, 0, 0] = true := by decide +kernel
theorem subd0_5_11 : subd0_5 [-1, 0, 1] = true := by decide +kernel
theorem subd0_5_12 : subd0_5 [-1, 0, 2] = true := by decide +kernel
theorem subd0_5_13 : subd0_5 [-1, 0, 3] = true := by decide +kernel
theorem subd0_5_14 : subd0_5 [-1, 0, 4] = true := by decide +kernel
theorem subd0_5_15 : subd0_5 [-1, 0, 5] = true := by decide +kernel
theorem subd0_5_16 : subd0_5 [-1, 0, 6] = true := by decide +kernel
theorem subd0_5_17 : subd0_5 [-1, 0, 7] = true := by decide +kernel
theorem subd0_5_18 : subd0_5 [-1, 0, 8] = true := by decide +kernel
theorem subd0_5_19 : subd0_5 [-1, 1] = true := by decide +kernel
theorem subd0_5_20 : subd0_5 [0, -2] = true := by decide +kernel
theorem subd0_5_21 : subd0_5 [0, -1, -8] = true := by decide +kernel
theorem subd0_5_22 : subd0_5 [0, -1, -7] = true := by decide +kernel
theorem subd0_5_23 : subd0_5 [0, -1, -6] = true := by decide +kernel
theorem subd0_5_24 : subd0_5 [0, -1, -5] = true := by decide +kernel
theorem subd0_5_25 : subd0_5 [0, -1, -4] = true := by decide +kernel
theorem subd0_5_26 : subd0_5 [0, -1, -3] = true := by decide +kernel
theorem subd0_5_27 : subd0_5 [0, -1, -2] = true := by decide +kernel
theorem subd0_5_28 : subd0_5 [0, -1, -1] = true := by decide +kernel
theorem subd0_5_29 : subd0_5 [0, -1, 0] = true := by decide +kernel
theorem subd0_5_30 : subd0_5 [0, -1, 1] = true := by decide +kernel
theorem subd0_5_31 : subd0_5 [0, -1, 2] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_cons.2 ⟨subd0_5_1, List.forall_mem_cons.2 ⟨subd0_5_2, List.forall_mem_cons.2 ⟨subd0_5_3, List.forall_mem_cons.2 ⟨subd0_5_4, List.forall_mem_cons.2 ⟨subd0_5_5, List.forall_mem_cons.2 ⟨subd0_5_6, List.forall_mem_cons.2 ⟨subd0_5_7, List.forall_mem_cons.2 ⟨subd0_5_8, List.forall_mem_cons.2 ⟨subd0_5_9, List.forall_mem_cons.2 ⟨subd0_5_10, List.forall_mem_cons.2 ⟨subd0_5_11, List.forall_mem_cons.2 ⟨subd0_5_12, List.forall_mem_cons.2 ⟨subd0_5_13, List.forall_mem_cons.2 ⟨subd0_5_14, List.forall_mem_cons.2 ⟨subd0_5_15, List.forall_mem_cons.2 ⟨subd0_5_16, List.forall_mem_cons.2 ⟨subd0_5_17, List.forall_mem_cons.2 ⟨subd0_5_18, List.forall_mem_cons.2 ⟨subd0_5_19, List.forall_mem_cons.2 ⟨subd0_5_20, List.forall_mem_cons.2 ⟨subd0_5_21, List.forall_mem_cons.2 ⟨subd0_5_22, List.forall_mem_cons.2 ⟨subd0_5_23, List.forall_mem_cons.2 ⟨subd0_5_24, List.forall_mem_cons.2 ⟨subd0_5_25, List.forall_mem_cons.2 ⟨subd0_5_26, List.forall_mem_cons.2 ⟨subd0_5_27, List.forall_mem_cons.2 ⟨subd0_5_28, List.forall_mem_cons.2 ⟨subd0_5_29, List.forall_mem_cons.2 ⟨subd0_5_30, List.forall_mem_cons.2 ⟨subd0_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_5_32 : subd0_5 [0, -1, 3] = true := by decide +kernel
theorem subd0_5_33 : subd0_5 [0, -1, 4] = true := by decide +kernel
theorem subd0_5_34 : subd0_5 [0, -1, 5] = true := by decide +kernel
theorem subd0_5_35 : subd0_5 [0, -1, 6] = true := by decide +kernel
theorem subd0_5_36 : subd0_5 [0, -1, 7] = true := by decide +kernel
theorem subd0_5_37 : subd0_5 [0, 0, -10] = true := by decide +kernel
theorem subd0_5_38 : subd0_5 [0, 0, -9] = true := by decide +kernel
theorem subd0_5_39 : subd0_5 [0, 0, -8] = true := by decide +kernel
theorem subd0_5_40 : subd0_5 [0, 0, -7] = true := by decide +kernel
theorem subd0_5_41 : subd0_5 [0, 0, -6] = true := by decide +kernel
theorem subd0_5_42 : subd0_5 [0, 0, -5] = true := by decide +kernel
theorem subd0_5_43 : subd0_5 [0, 0, -4] = true := by decide +kernel
theorem subd0_5_44 : subd0_5 [0, 0, -3] = true := by decide +kernel
theorem subd0_5_45 : subd0_5 [0, 0, -2] = true := by decide +kernel
theorem subd0_5_46 : subd0_5 [0, 0, -1] = true := by decide +kernel
theorem subd0_5_47 : subd0_5 [0, 0, 0] = true := by decide +kernel
theorem subd0_5_48 : subd0_5 [0, 0, 1] = true := by decide +kernel
theorem subd0_5_49 : subd0_5 [0, 0, 2] = true := by decide +kernel
theorem subd0_5_50 : subd0_5 [0, 0, 3] = true := by decide +kernel
theorem subd0_5_51 : subd0_5 [0, 0, 4] = true := by decide +kernel
theorem subd0_5_52 : subd0_5 [0, 0, 5] = true := by decide +kernel
theorem subd0_5_53 : subd0_5 [0, 0, 6] = true := by decide +kernel
theorem subd0_5_54 : subd0_5 [0, 0, 7] = true := by decide +kernel
theorem subd0_5_55 : subd0_5 [0, 0, 8] = true := by decide +kernel
theorem subd0_5_56 : subd0_5 [0, 0, 9] = true := by decide +kernel
theorem subd0_5_57 : subd0_5 [0, 1, -8] = true := by decide +kernel
theorem subd0_5_58 : subd0_5 [0, 1, -7] = true := by decide +kernel
theorem subd0_5_59 : subd0_5 [0, 1, -6] = true := by decide +kernel
theorem subd0_5_60 : subd0_5 [0, 1, -5] = true := by decide +kernel
theorem subd0_5_61 : subd0_5 [0, 1, -4] = true := by decide +kernel
theorem subd0_5_62 : subd0_5 [0, 1, -3] = true := by decide +kernel
theorem subd0_5_63 : subd0_5 [0, 1, -2] = true := by decide +kernel
theorem sbd0_5_1 : ∀ q ∈ blkd0_5_1, subd0_5 q = true := by
  unfold blkd0_5_1
  exact List.forall_mem_cons.2 ⟨subd0_5_32, List.forall_mem_cons.2 ⟨subd0_5_33, List.forall_mem_cons.2 ⟨subd0_5_34, List.forall_mem_cons.2 ⟨subd0_5_35, List.forall_mem_cons.2 ⟨subd0_5_36, List.forall_mem_cons.2 ⟨subd0_5_37, List.forall_mem_cons.2 ⟨subd0_5_38, List.forall_mem_cons.2 ⟨subd0_5_39, List.forall_mem_cons.2 ⟨subd0_5_40, List.forall_mem_cons.2 ⟨subd0_5_41, List.forall_mem_cons.2 ⟨subd0_5_42, List.forall_mem_cons.2 ⟨subd0_5_43, List.forall_mem_cons.2 ⟨subd0_5_44, List.forall_mem_cons.2 ⟨subd0_5_45, List.forall_mem_cons.2 ⟨subd0_5_46, List.forall_mem_cons.2 ⟨subd0_5_47, List.forall_mem_cons.2 ⟨subd0_5_48, List.forall_mem_cons.2 ⟨subd0_5_49, List.forall_mem_cons.2 ⟨subd0_5_50, List.forall_mem_cons.2 ⟨subd0_5_51, List.forall_mem_cons.2 ⟨subd0_5_52, List.forall_mem_cons.2 ⟨subd0_5_53, List.forall_mem_cons.2 ⟨subd0_5_54, List.forall_mem_cons.2 ⟨subd0_5_55, List.forall_mem_cons.2 ⟨subd0_5_56, List.forall_mem_cons.2 ⟨subd0_5_57, List.forall_mem_cons.2 ⟨subd0_5_58, List.forall_mem_cons.2 ⟨subd0_5_59, List.forall_mem_cons.2 ⟨subd0_5_60, List.forall_mem_cons.2 ⟨subd0_5_61, List.forall_mem_cons.2 ⟨subd0_5_62, List.forall_mem_cons.2 ⟨subd0_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C134
