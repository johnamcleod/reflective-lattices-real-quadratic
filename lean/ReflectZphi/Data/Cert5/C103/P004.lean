import ReflectZphi.Data.Cert5.C103.Base

namespace ReflectZphi.Data.Cert5.C103

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_2_0 : subd4_2 [-3] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-2, -3] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-2, -2] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-2, -1] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-2, 0] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-2, 1] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-2, 2] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-1, -4] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [-1, 3] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [0, -4] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [0, 0, -7] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [0, 0, -6] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [0, 0, -5] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [0, 0, -4] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [0, 0, -3] = true := by decide +kernel
theorem subd4_2_24 : subd4_2 [0, 0, -2] = true := by decide +kernel
theorem subd4_2_25 : subd4_2 [0, 0, -1] = true := by decide +kernel
theorem subd4_2_26 : subd4_2 [0, 0, 0] = true := by decide +kernel
theorem subd4_2_27 : subd4_2 [0, 0, 1] = true := by decide +kernel
theorem subd4_2_28 : subd4_2 [0, 0, 2] = true := by decide +kernel
theorem subd4_2_29 : subd4_2 [0, 0, 3] = true := by decide +kernel
theorem subd4_2_30 : subd4_2 [0, 0, 4] = true := by decide +kernel
theorem subd4_2_31 : subd4_2 [0, 0, 5] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_cons.2 ⟨subd4_2_24, List.forall_mem_cons.2 ⟨subd4_2_25, List.forall_mem_cons.2 ⟨subd4_2_26, List.forall_mem_cons.2 ⟨subd4_2_27, List.forall_mem_cons.2 ⟨subd4_2_28, List.forall_mem_cons.2 ⟨subd4_2_29, List.forall_mem_cons.2 ⟨subd4_2_30, List.forall_mem_cons.2 ⟨subd4_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_32 : subd4_2 [0, 0, 6] = true := by decide +kernel
theorem subd4_2_33 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_34 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_35 : subd4_2 [0, 3] = true := by decide +kernel
theorem subd4_2_36 : subd4_2 [1, -4] = true := by decide +kernel
theorem subd4_2_37 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_38 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_39 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_40 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_41 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_42 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_43 : subd4_2 [1, 3] = true := by decide +kernel
theorem subd4_2_44 : subd4_2 [2, -3] = true := by decide +kernel
theorem subd4_2_45 : subd4_2 [2, -2] = true := by decide +kernel
theorem subd4_2_46 : subd4_2 [2, -1] = true := by decide +kernel
theorem subd4_2_47 : subd4_2 [2, 0] = true := by decide +kernel
theorem subd4_2_48 : subd4_2 [2, 1] = true := by decide +kernel
theorem subd4_2_49 : subd4_2 [2, 2] = true := by decide +kernel
theorem subd4_2_50 : subd4_2 [3] = true := by decide +kernel
theorem sbd4_2_1 : ∀ q ∈ blkd4_2_1, subd4_2 q = true := by
  unfold blkd4_2_1
  exact List.forall_mem_cons.2 ⟨subd4_2_32, List.forall_mem_cons.2 ⟨subd4_2_33, List.forall_mem_cons.2 ⟨subd4_2_34, List.forall_mem_cons.2 ⟨subd4_2_35, List.forall_mem_cons.2 ⟨subd4_2_36, List.forall_mem_cons.2 ⟨subd4_2_37, List.forall_mem_cons.2 ⟨subd4_2_38, List.forall_mem_cons.2 ⟨subd4_2_39, List.forall_mem_cons.2 ⟨subd4_2_40, List.forall_mem_cons.2 ⟨subd4_2_41, List.forall_mem_cons.2 ⟨subd4_2_42, List.forall_mem_cons.2 ⟨subd4_2_43, List.forall_mem_cons.2 ⟨subd4_2_44, List.forall_mem_cons.2 ⟨subd4_2_45, List.forall_mem_cons.2 ⟨subd4_2_46, List.forall_mem_cons.2 ⟨subd4_2_47, List.forall_mem_cons.2 ⟨subd4_2_48, List.forall_mem_cons.2 ⟨subd4_2_49, List.forall_mem_cons.2 ⟨subd4_2_50, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [-3] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-2] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [-1, -3] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [-1, -2] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [-1, -1] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [-1, 0] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [-1, 1] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [-1, 2] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_10 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_11 : subd4_3 [0, 0] = true := by decide +kernel
theorem subd4_3_12 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_13 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_14 : subd4_3 [1, -3] = true := by decide +kernel
theorem subd4_3_15 : subd4_3 [1, -2] = true := by decide +kernel
theorem subd4_3_16 : subd4_3 [1, -1] = true := by decide +kernel
theorem subd4_3_17 : subd4_3 [1, 0] = true := by decide +kernel
theorem subd4_3_18 : subd4_3 [1, 1] = true := by decide +kernel
theorem subd4_3_19 : subd4_3 [1, 2] = true := by decide +kernel
theorem subd4_3_20 : subd4_3 [2] = true := by decide +kernel
theorem subd4_3_21 : subd4_3 [3] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_cons.2 ⟨subd4_3_10, List.forall_mem_cons.2 ⟨subd4_3_11, List.forall_mem_cons.2 ⟨subd4_3_12, List.forall_mem_cons.2 ⟨subd4_3_13, List.forall_mem_cons.2 ⟨subd4_3_14, List.forall_mem_cons.2 ⟨subd4_3_15, List.forall_mem_cons.2 ⟨subd4_3_16, List.forall_mem_cons.2 ⟨subd4_3_17, List.forall_mem_cons.2 ⟨subd4_3_18, List.forall_mem_cons.2 ⟨subd4_3_19, List.forall_mem_cons.2 ⟨subd4_3_20, List.forall_mem_cons.2 ⟨subd4_3_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3, -3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-3, -2] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-3, -1] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-3, 0] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-3, 1] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-3, 2] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-2, -4] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-2, -3] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-2, -2] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-2, -1] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [-2, 0] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [-2, 1] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [-2, 2] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [-2, 3] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [-1, -1, -8] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [-1, -1, -7] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [-1, -1, -6] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [-1, -1, -5] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [-1, -1, -4] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [-1, -1, -3] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [-1, -1, -2] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [-1, -1, -1] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [-1, -1, 0] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [-1, -1, 1] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [-1, -1, 2] = true := by decide +kernel
theorem subd5_0_28 : subd5_0 [-1, -1, 3] = true := by decide +kernel
theorem subd5_0_29 : subd5_0 [-1, -1, 4] = true := by decide +kernel
theorem subd5_0_30 : subd5_0 [-1, -1, 5] = true := by decide +kernel
theorem subd5_0_31 : subd5_0 [-1, -1, 6] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_cons.2 ⟨subd5_0_28, List.forall_mem_cons.2 ⟨subd5_0_29, List.forall_mem_cons.2 ⟨subd5_0_30, List.forall_mem_cons.2 ⟨subd5_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_32 : subd5_0 [-1, 0, -8] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [-1, 0, -7] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [-1, 0, -6] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [-1, 0, -5] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [-1, 0, -4] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [-1, 0, -3] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [-1, 0, -2] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [-1, 0, -1] = true := by decide +kernel
theorem subd5_0_40 : subd5_0 [-1, 0, 0] = true := by decide +kernel
theorem subd5_0_41 : subd5_0 [-1, 0, 1] = true := by decide +kernel
theorem subd5_0_42 : subd5_0 [-1, 0, 2] = true := by decide +kernel
theorem subd5_0_43 : subd5_0 [-1, 0, 3] = true := by decide +kernel
theorem subd5_0_44 : subd5_0 [-1, 0, 4] = true := by decide +kernel
theorem subd5_0_45 : subd5_0 [-1, 0, 5] = true := by decide +kernel
theorem subd5_0_46 : subd5_0 [-1, 0, 6] = true := by decide +kernel
theorem subd5_0_47 : subd5_0 [-1, 0, 7] = true := by decide +kernel
theorem subd5_0_48 : subd5_0 [-1, 1, -8] = true := by decide +kernel
theorem subd5_0_49 : subd5_0 [-1, 1, -7] = true := by decide +kernel
theorem subd5_0_50 : subd5_0 [-1, 1, -6] = true := by decide +kernel
theorem subd5_0_51 : subd5_0 [-1, 1, -5] = true := by decide +kernel
theorem subd5_0_52 : subd5_0 [-1, 1, -4] = true := by decide +kernel
theorem subd5_0_53 : subd5_0 [-1, 1, -3] = true := by decide +kernel
theorem subd5_0_54 : subd5_0 [-1, 1, -2] = true := by decide +kernel
theorem subd5_0_55 : subd5_0 [-1, 1, -1] = true := by decide +kernel
theorem subd5_0_56 : subd5_0 [-1, 1, 0] = true := by decide +kernel
theorem subd5_0_57 : subd5_0 [-1, 1, 1] = true := by decide +kernel
theorem subd5_0_58 : subd5_0 [-1, 1, 2] = true := by decide +kernel
theorem subd5_0_59 : subd5_0 [-1, 1, 3] = true := by decide +kernel
theorem subd5_0_60 : subd5_0 [-1, 1, 4] = true := by decide +kernel
theorem subd5_0_61 : subd5_0 [-1, 1, 5] = true := by decide +kernel
theorem subd5_0_62 : subd5_0 [-1, 1, 6] = true := by decide +kernel
theorem subd5_0_63 : subd5_0 [-1, 1, 7] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_cons.2 ⟨subd5_0_40, List.forall_mem_cons.2 ⟨subd5_0_41, List.forall_mem_cons.2 ⟨subd5_0_42, List.forall_mem_cons.2 ⟨subd5_0_43, List.forall_mem_cons.2 ⟨subd5_0_44, List.forall_mem_cons.2 ⟨subd5_0_45, List.forall_mem_cons.2 ⟨subd5_0_46, List.forall_mem_cons.2 ⟨subd5_0_47, List.forall_mem_cons.2 ⟨subd5_0_48, List.forall_mem_cons.2 ⟨subd5_0_49, List.forall_mem_cons.2 ⟨subd5_0_50, List.forall_mem_cons.2 ⟨subd5_0_51, List.forall_mem_cons.2 ⟨subd5_0_52, List.forall_mem_cons.2 ⟨subd5_0_53, List.forall_mem_cons.2 ⟨subd5_0_54, List.forall_mem_cons.2 ⟨subd5_0_55, List.forall_mem_cons.2 ⟨subd5_0_56, List.forall_mem_cons.2 ⟨subd5_0_57, List.forall_mem_cons.2 ⟨subd5_0_58, List.forall_mem_cons.2 ⟨subd5_0_59, List.forall_mem_cons.2 ⟨subd5_0_60, List.forall_mem_cons.2 ⟨subd5_0_61, List.forall_mem_cons.2 ⟨subd5_0_62, List.forall_mem_cons.2 ⟨subd5_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_64 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_65 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_66 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_67 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_68 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_69 : subd5_0 [0, -1, -8] = true := by decide +kernel
theorem subd5_0_70 : subd5_0 [0, -1, -7] = true := by decide +kernel
theorem subd5_0_71 : subd5_0 [0, -1, -6] = true := by decide +kernel
theorem subd5_0_72 : subd5_0 [0, -1, -5] = true := by decide +kernel
theorem subd5_0_73 : subd5_0 [0, -1, -4] = true := by decide +kernel
theorem subd5_0_74 : subd5_0 [0, -1, -3] = true := by decide +kernel
theorem subd5_0_75 : subd5_0 [0, -1, -2] = true := by decide +kernel
theorem subd5_0_76 : subd5_0 [0, -1, -1] = true := by decide +kernel
theorem subd5_0_77 : subd5_0 [0, -1, 0] = true := by decide +kernel
theorem subd5_0_78 : subd5_0 [0, -1, 1] = true := by decide +kernel
theorem subd5_0_79 : subd5_0 [0, -1, 2] = true := by decide +kernel
theorem subd5_0_80 : subd5_0 [0, -1, 3] = true := by decide +kernel
theorem subd5_0_81 : subd5_0 [0, -1, 4] = true := by decide +kernel
theorem subd5_0_82 : subd5_0 [0, -1, 5] = true := by decide +kernel
theorem subd5_0_83 : subd5_0 [0, -1, 6] = true := by decide +kernel
theorem subd5_0_84 : subd5_0 [0, -1, 7] = true := by decide +kernel
theorem subd5_0_85 : subd5_0 [0, 0, -8] = true := by decide +kernel
theorem subd5_0_86 : subd5_0 [0, 0, -7] = true := by decide +kernel
theorem subd5_0_87 : subd5_0 [0, 0, -6] = true := by decide +kernel
theorem subd5_0_88 : subd5_0 [0, 0, -5] = true := by decide +kernel
theorem subd5_0_89 : subd5_0 [0, 0, -4] = true := by decide +kernel
theorem subd5_0_90 : subd5_0 [0, 0, -3] = true := by decide +kernel
theorem subd5_0_91 : subd5_0 [0, 0, -2] = true := by decide +kernel
theorem subd5_0_92 : subd5_0 [0, 0, -1] = true := by decide +kernel
theorem subd5_0_93 : subd5_0 [0, 0, 0] = true := by decide +kernel
theorem subd5_0_94 : subd5_0 [0, 0, 1] = true := by decide +kernel
theorem subd5_0_95 : subd5_0 [0, 0, 2] = true := by decide +kernel
theorem sbd5_0_2 : ∀ q ∈ blkd5_0_2, subd5_0 q = true := by
  unfold blkd5_0_2
  exact List.forall_mem_cons.2 ⟨subd5_0_64, List.forall_mem_cons.2 ⟨subd5_0_65, List.forall_mem_cons.2 ⟨subd5_0_66, List.forall_mem_cons.2 ⟨subd5_0_67, List.forall_mem_cons.2 ⟨subd5_0_68, List.forall_mem_cons.2 ⟨subd5_0_69, List.forall_mem_cons.2 ⟨subd5_0_70, List.forall_mem_cons.2 ⟨subd5_0_71, List.forall_mem_cons.2 ⟨subd5_0_72, List.forall_mem_cons.2 ⟨subd5_0_73, List.forall_mem_cons.2 ⟨subd5_0_74, List.forall_mem_cons.2 ⟨subd5_0_75, List.forall_mem_cons.2 ⟨subd5_0_76, List.forall_mem_cons.2 ⟨subd5_0_77, List.forall_mem_cons.2 ⟨subd5_0_78, List.forall_mem_cons.2 ⟨subd5_0_79, List.forall_mem_cons.2 ⟨subd5_0_80, List.forall_mem_cons.2 ⟨subd5_0_81, List.forall_mem_cons.2 ⟨subd5_0_82, List.forall_mem_cons.2 ⟨subd5_0_83, List.forall_mem_cons.2 ⟨subd5_0_84, List.forall_mem_cons.2 ⟨subd5_0_85, List.forall_mem_cons.2 ⟨subd5_0_86, List.forall_mem_cons.2 ⟨subd5_0_87, List.forall_mem_cons.2 ⟨subd5_0_88, List.forall_mem_cons.2 ⟨subd5_0_89, List.forall_mem_cons.2 ⟨subd5_0_90, List.forall_mem_cons.2 ⟨subd5_0_91, List.forall_mem_cons.2 ⟨subd5_0_92, List.forall_mem_cons.2 ⟨subd5_0_93, List.forall_mem_cons.2 ⟨subd5_0_94, List.forall_mem_cons.2 ⟨subd5_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C103
