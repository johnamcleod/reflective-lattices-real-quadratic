import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_6_32 : subd9_6 [1, -3] = true := by decide +kernel
theorem subd9_6_33 : subd9_6 [1, -2] = true := by decide +kernel
theorem subd9_6_34 : subd9_6 [1, -1] = true := by decide +kernel
theorem subd9_6_35 : subd9_6 [1, 0] = true := by decide +kernel
theorem subd9_6_36 : subd9_6 [1, 1] = true := by decide +kernel
theorem subd9_6_37 : subd9_6 [1, 2] = true := by decide +kernel
theorem subd9_6_38 : subd9_6 [1, 3] = true := by decide +kernel
theorem subd9_6_39 : subd9_6 [1, 4] = true := by decide +kernel
theorem subd9_6_40 : subd9_6 [2, -4] = true := by decide +kernel
theorem subd9_6_41 : subd9_6 [2, -3] = true := by decide +kernel
theorem subd9_6_42 : subd9_6 [2, -2] = true := by decide +kernel
theorem subd9_6_43 : subd9_6 [2, -1] = true := by decide +kernel
theorem subd9_6_44 : subd9_6 [2, 0] = true := by decide +kernel
theorem subd9_6_45 : subd9_6 [2, 1] = true := by decide +kernel
theorem subd9_6_46 : subd9_6 [2, 2] = true := by decide +kernel
theorem subd9_6_47 : subd9_6 [2, 3] = true := by decide +kernel
theorem subd9_6_48 : subd9_6 [3] = true := by decide +kernel
theorem subd9_6_49 : subd9_6 [4] = true := by decide +kernel
theorem sbd9_6_1 : ∀ q ∈ blkd9_6_1, subd9_6 q = true := by
  unfold blkd9_6_1
  exact List.forall_mem_cons.2 ⟨subd9_6_32, List.forall_mem_cons.2 ⟨subd9_6_33, List.forall_mem_cons.2 ⟨subd9_6_34, List.forall_mem_cons.2 ⟨subd9_6_35, List.forall_mem_cons.2 ⟨subd9_6_36, List.forall_mem_cons.2 ⟨subd9_6_37, List.forall_mem_cons.2 ⟨subd9_6_38, List.forall_mem_cons.2 ⟨subd9_6_39, List.forall_mem_cons.2 ⟨subd9_6_40, List.forall_mem_cons.2 ⟨subd9_6_41, List.forall_mem_cons.2 ⟨subd9_6_42, List.forall_mem_cons.2 ⟨subd9_6_43, List.forall_mem_cons.2 ⟨subd9_6_44, List.forall_mem_cons.2 ⟨subd9_6_45, List.forall_mem_cons.2 ⟨subd9_6_46, List.forall_mem_cons.2 ⟨subd9_6_47, List.forall_mem_cons.2 ⟨subd9_6_48, List.forall_mem_cons.2 ⟨subd9_6_49, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [-3, -3] = true := by decide +kernel
theorem subd9_7_1 : subd9_7 [-3, -2] = true := by decide +kernel
theorem subd9_7_2 : subd9_7 [-3, -1] = true := by decide +kernel
theorem subd9_7_3 : subd9_7 [-3, 0] = true := by decide +kernel
theorem subd9_7_4 : subd9_7 [-3, 1] = true := by decide +kernel
theorem subd9_7_5 : subd9_7 [-2, -4] = true := by decide +kernel
theorem subd9_7_6 : subd9_7 [-2, -3] = true := by decide +kernel
theorem subd9_7_7 : subd9_7 [-2, -2] = true := by decide +kernel
theorem subd9_7_8 : subd9_7 [-2, -1] = true := by decide +kernel
theorem subd9_7_9 : subd9_7 [-2, 0] = true := by decide +kernel
theorem subd9_7_10 : subd9_7 [-2, 1] = true := by decide +kernel
theorem subd9_7_11 : subd9_7 [-2, 2] = true := by decide +kernel
theorem subd9_7_12 : subd9_7 [-1, -4] = true := by decide +kernel
theorem subd9_7_13 : subd9_7 [-1, -3] = true := by decide +kernel
theorem subd9_7_14 : subd9_7 [-1, -2] = true := by decide +kernel
theorem subd9_7_15 : subd9_7 [-1, -1] = true := by decide +kernel
theorem subd9_7_16 : subd9_7 [-1, 0] = true := by decide +kernel
theorem subd9_7_17 : subd9_7 [-1, 1] = true := by decide +kernel
theorem subd9_7_18 : subd9_7 [-1, 2] = true := by decide +kernel
theorem subd9_7_19 : subd9_7 [-1, 3] = true := by decide +kernel
theorem subd9_7_20 : subd9_7 [0, -4] = true := by decide +kernel
theorem subd9_7_21 : subd9_7 [0, -3] = true := by decide +kernel
theorem subd9_7_22 : subd9_7 [0, -2] = true := by decide +kernel
theorem subd9_7_23 : subd9_7 [0, -1] = true := by decide +kernel
theorem subd9_7_24 : subd9_7 [0, 0] = true := by decide +kernel
theorem subd9_7_25 : subd9_7 [0, 1] = true := by decide +kernel
theorem subd9_7_26 : subd9_7 [0, 2] = true := by decide +kernel
theorem subd9_7_27 : subd9_7 [0, 3] = true := by decide +kernel
theorem subd9_7_28 : subd9_7 [1, -4] = true := by decide +kernel
theorem subd9_7_29 : subd9_7 [1, -3] = true := by decide +kernel
theorem subd9_7_30 : subd9_7 [1, -2] = true := by decide +kernel
theorem subd9_7_31 : subd9_7 [1, -1] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_cons.2 ⟨subd9_7_1, List.forall_mem_cons.2 ⟨subd9_7_2, List.forall_mem_cons.2 ⟨subd9_7_3, List.forall_mem_cons.2 ⟨subd9_7_4, List.forall_mem_cons.2 ⟨subd9_7_5, List.forall_mem_cons.2 ⟨subd9_7_6, List.forall_mem_cons.2 ⟨subd9_7_7, List.forall_mem_cons.2 ⟨subd9_7_8, List.forall_mem_cons.2 ⟨subd9_7_9, List.forall_mem_cons.2 ⟨subd9_7_10, List.forall_mem_cons.2 ⟨subd9_7_11, List.forall_mem_cons.2 ⟨subd9_7_12, List.forall_mem_cons.2 ⟨subd9_7_13, List.forall_mem_cons.2 ⟨subd9_7_14, List.forall_mem_cons.2 ⟨subd9_7_15, List.forall_mem_cons.2 ⟨subd9_7_16, List.forall_mem_cons.2 ⟨subd9_7_17, List.forall_mem_cons.2 ⟨subd9_7_18, List.forall_mem_cons.2 ⟨subd9_7_19, List.forall_mem_cons.2 ⟨subd9_7_20, List.forall_mem_cons.2 ⟨subd9_7_21, List.forall_mem_cons.2 ⟨subd9_7_22, List.forall_mem_cons.2 ⟨subd9_7_23, List.forall_mem_cons.2 ⟨subd9_7_24, List.forall_mem_cons.2 ⟨subd9_7_25, List.forall_mem_cons.2 ⟨subd9_7_26, List.forall_mem_cons.2 ⟨subd9_7_27, List.forall_mem_cons.2 ⟨subd9_7_28, List.forall_mem_cons.2 ⟨subd9_7_29, List.forall_mem_cons.2 ⟨subd9_7_30, List.forall_mem_cons.2 ⟨subd9_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_32 : subd9_7 [1, 0] = true := by decide +kernel
theorem subd9_7_33 : subd9_7 [1, 1] = true := by decide +kernel
theorem subd9_7_34 : subd9_7 [1, 2] = true := by decide +kernel
theorem subd9_7_35 : subd9_7 [1, 3] = true := by decide +kernel
theorem subd9_7_36 : subd9_7 [2, -3] = true := by decide +kernel
theorem subd9_7_37 : subd9_7 [2, -2] = true := by decide +kernel
theorem subd9_7_38 : subd9_7 [2, -1] = true := by decide +kernel
theorem subd9_7_39 : subd9_7 [2, 0] = true := by decide +kernel
theorem subd9_7_40 : subd9_7 [2, 1] = true := by decide +kernel
theorem subd9_7_41 : subd9_7 [2, 2] = true := by decide +kernel
theorem subd9_7_42 : subd9_7 [2, 3] = true := by decide +kernel
theorem subd9_7_43 : subd9_7 [3, -2] = true := by decide +kernel
theorem subd9_7_44 : subd9_7 [3, -1] = true := by decide +kernel
theorem subd9_7_45 : subd9_7 [3, 0] = true := by decide +kernel
theorem subd9_7_46 : subd9_7 [3, 1] = true := by decide +kernel
theorem subd9_7_47 : subd9_7 [3, 2] = true := by decide +kernel
theorem sbd9_7_1 : ∀ q ∈ blkd9_7_1, subd9_7 q = true := by
  unfold blkd9_7_1
  exact List.forall_mem_cons.2 ⟨subd9_7_32, List.forall_mem_cons.2 ⟨subd9_7_33, List.forall_mem_cons.2 ⟨subd9_7_34, List.forall_mem_cons.2 ⟨subd9_7_35, List.forall_mem_cons.2 ⟨subd9_7_36, List.forall_mem_cons.2 ⟨subd9_7_37, List.forall_mem_cons.2 ⟨subd9_7_38, List.forall_mem_cons.2 ⟨subd9_7_39, List.forall_mem_cons.2 ⟨subd9_7_40, List.forall_mem_cons.2 ⟨subd9_7_41, List.forall_mem_cons.2 ⟨subd9_7_42, List.forall_mem_cons.2 ⟨subd9_7_43, List.forall_mem_cons.2 ⟨subd9_7_44, List.forall_mem_cons.2 ⟨subd9_7_45, List.forall_mem_cons.2 ⟨subd9_7_46, List.forall_mem_cons.2 ⟨subd9_7_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_8 : ldCheck G d9_8.U d9_8.ms ldd9_8 = true := by decide +kernel
theorem pre_okd9_8 : subPre G cell9 d9_8 = true := by decide +kernel
theorem subd9_8_0 : subd9_8 [-1, -2] = true := by decide +kernel
theorem subd9_8_1 : subd9_8 [-1, -1, -10] = true := by decide +kernel
theorem subd9_8_2 : subd9_8 [-1, -1, -9] = true := by decide +kernel
theorem subd9_8_3 : subd9_8 [-1, -1, -8] = true := by decide +kernel
theorem subd9_8_4 : subd9_8 [-1, -1, -7] = true := by decide +kernel
theorem subd9_8_5 : subd9_8 [-1, -1, -6] = true := by decide +kernel
theorem subd9_8_6 : subd9_8 [-1, -1, -5] = true := by decide +kernel
theorem subd9_8_7 : subd9_8 [-1, -1, -4] = true := by decide +kernel
theorem subd9_8_8 : subd9_8 [-1, -1, -3] = true := by decide +kernel
theorem subd9_8_9 : subd9_8 [-1, -1, -2] = true := by decide +kernel
theorem subd9_8_10 : subd9_8 [-1, -1, -1] = true := by decide +kernel
theorem subd9_8_11 : subd9_8 [-1, -1, 0] = true := by decide +kernel
theorem subd9_8_12 : subd9_8 [-1, -1, 1] = true := by decide +kernel
theorem subd9_8_13 : subd9_8 [-1, -1, 2] = true := by decide +kernel
theorem subd9_8_14 : subd9_8 [-1, -1, 3] = true := by decide +kernel
theorem subd9_8_15 : subd9_8 [-1, -1, 4] = true := by decide +kernel
theorem subd9_8_16 : subd9_8 [-1, -1, 5] = true := by decide +kernel
theorem subd9_8_17 : subd9_8 [-1, -1, 6] = true := by decide +kernel
theorem subd9_8_18 : subd9_8 [-1, -1, 7] = true := by decide +kernel
theorem subd9_8_19 : subd9_8 [-1, -1, 8] = true := by decide +kernel
theorem subd9_8_20 : subd9_8 [-1, -1, 9] = true := by decide +kernel
theorem subd9_8_21 : subd9_8 [-1, -1, 10] = true := by decide +kernel
theorem subd9_8_22 : subd9_8 [-1, 0, -14] = true := by decide +kernel
theorem subd9_8_23 : subd9_8 [-1, 0, -13] = true := by decide +kernel
theorem subd9_8_24 : subd9_8 [-1, 0, -12] = true := by decide +kernel
theorem subd9_8_25 : subd9_8 [-1, 0, -11] = true := by decide +kernel
theorem subd9_8_26 : subd9_8 [-1, 0, -10] = true := by decide +kernel
theorem subd9_8_27 : subd9_8 [-1, 0, -9] = true := by decide +kernel
theorem subd9_8_28 : subd9_8 [-1, 0, -8] = true := by decide +kernel
theorem subd9_8_29 : subd9_8 [-1, 0, -7] = true := by decide +kernel
theorem subd9_8_30 : subd9_8 [-1, 0, -6] = true := by decide +kernel
theorem subd9_8_31 : subd9_8 [-1, 0, -5] = true := by decide +kernel
theorem sbd9_8_0 : ∀ q ∈ blkd9_8_0, subd9_8 q = true := by
  unfold blkd9_8_0
  exact List.forall_mem_cons.2 ⟨subd9_8_0, List.forall_mem_cons.2 ⟨subd9_8_1, List.forall_mem_cons.2 ⟨subd9_8_2, List.forall_mem_cons.2 ⟨subd9_8_3, List.forall_mem_cons.2 ⟨subd9_8_4, List.forall_mem_cons.2 ⟨subd9_8_5, List.forall_mem_cons.2 ⟨subd9_8_6, List.forall_mem_cons.2 ⟨subd9_8_7, List.forall_mem_cons.2 ⟨subd9_8_8, List.forall_mem_cons.2 ⟨subd9_8_9, List.forall_mem_cons.2 ⟨subd9_8_10, List.forall_mem_cons.2 ⟨subd9_8_11, List.forall_mem_cons.2 ⟨subd9_8_12, List.forall_mem_cons.2 ⟨subd9_8_13, List.forall_mem_cons.2 ⟨subd9_8_14, List.forall_mem_cons.2 ⟨subd9_8_15, List.forall_mem_cons.2 ⟨subd9_8_16, List.forall_mem_cons.2 ⟨subd9_8_17, List.forall_mem_cons.2 ⟨subd9_8_18, List.forall_mem_cons.2 ⟨subd9_8_19, List.forall_mem_cons.2 ⟨subd9_8_20, List.forall_mem_cons.2 ⟨subd9_8_21, List.forall_mem_cons.2 ⟨subd9_8_22, List.forall_mem_cons.2 ⟨subd9_8_23, List.forall_mem_cons.2 ⟨subd9_8_24, List.forall_mem_cons.2 ⟨subd9_8_25, List.forall_mem_cons.2 ⟨subd9_8_26, List.forall_mem_cons.2 ⟨subd9_8_27, List.forall_mem_cons.2 ⟨subd9_8_28, List.forall_mem_cons.2 ⟨subd9_8_29, List.forall_mem_cons.2 ⟨subd9_8_30, List.forall_mem_cons.2 ⟨subd9_8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_8_32 : subd9_8 [-1, 0, -4] = true := by decide +kernel
theorem subd9_8_33 : subd9_8 [-1, 0, -3] = true := by decide +kernel
theorem subd9_8_34 : subd9_8 [-1, 0, -2] = true := by decide +kernel
theorem subd9_8_35 : subd9_8 [-1, 0, -1] = true := by decide +kernel
theorem subd9_8_36 : subd9_8 [-1, 0, 0] = true := by decide +kernel
theorem subd9_8_37 : subd9_8 [-1, 0, 1] = true := by decide +kernel
theorem subd9_8_38 : subd9_8 [-1, 0, 2] = true := by decide +kernel
theorem subd9_8_39 : subd9_8 [-1, 0, 3] = true := by decide +kernel
theorem subd9_8_40 : subd9_8 [-1, 0, 4] = true := by decide +kernel
theorem subd9_8_41 : subd9_8 [-1, 0, 5] = true := by decide +kernel
theorem subd9_8_42 : subd9_8 [-1, 0, 6] = true := by decide +kernel
theorem subd9_8_43 : subd9_8 [-1, 0, 7] = true := by decide +kernel
theorem subd9_8_44 : subd9_8 [-1, 0, 8] = true := by decide +kernel
theorem subd9_8_45 : subd9_8 [-1, 0, 9] = true := by decide +kernel
theorem subd9_8_46 : subd9_8 [-1, 0, 10] = true := by decide +kernel
theorem subd9_8_47 : subd9_8 [-1, 0, 11] = true := by decide +kernel
theorem subd9_8_48 : subd9_8 [-1, 0, 12] = true := by decide +kernel
theorem subd9_8_49 : subd9_8 [-1, 0, 13] = true := by decide +kernel
theorem subd9_8_50 : subd9_8 [0, -2] = true := by decide +kernel
theorem subd9_8_51 : subd9_8 [0, -1, -16] = true := by decide +kernel
theorem subd9_8_52 : subd9_8 [0, -1, -15] = true := by decide +kernel
theorem subd9_8_53 : subd9_8 [0, -1, -14] = true := by decide +kernel
theorem subd9_8_54 : subd9_8 [0, -1, -13] = true := by decide +kernel
theorem subd9_8_55 : subd9_8 [0, -1, -12] = true := by decide +kernel
theorem subd9_8_56 : subd9_8 [0, -1, -11] = true := by decide +kernel
theorem subd9_8_57 : subd9_8 [0, -1, -10] = true := by decide +kernel
theorem subd9_8_58 : subd9_8 [0, -1, -9] = true := by decide +kernel
theorem subd9_8_59 : subd9_8 [0, -1, -8] = true := by decide +kernel
theorem subd9_8_60 : subd9_8 [0, -1, -7] = true := by decide +kernel
theorem subd9_8_61 : subd9_8 [0, -1, -6] = true := by decide +kernel
theorem subd9_8_62 : subd9_8 [0, -1, -5] = true := by decide +kernel
theorem subd9_8_63 : subd9_8 [0, -1, -4] = true := by decide +kernel
theorem sbd9_8_1 : ∀ q ∈ blkd9_8_1, subd9_8 q = true := by
  unfold blkd9_8_1
  exact List.forall_mem_cons.2 ⟨subd9_8_32, List.forall_mem_cons.2 ⟨subd9_8_33, List.forall_mem_cons.2 ⟨subd9_8_34, List.forall_mem_cons.2 ⟨subd9_8_35, List.forall_mem_cons.2 ⟨subd9_8_36, List.forall_mem_cons.2 ⟨subd9_8_37, List.forall_mem_cons.2 ⟨subd9_8_38, List.forall_mem_cons.2 ⟨subd9_8_39, List.forall_mem_cons.2 ⟨subd9_8_40, List.forall_mem_cons.2 ⟨subd9_8_41, List.forall_mem_cons.2 ⟨subd9_8_42, List.forall_mem_cons.2 ⟨subd9_8_43, List.forall_mem_cons.2 ⟨subd9_8_44, List.forall_mem_cons.2 ⟨subd9_8_45, List.forall_mem_cons.2 ⟨subd9_8_46, List.forall_mem_cons.2 ⟨subd9_8_47, List.forall_mem_cons.2 ⟨subd9_8_48, List.forall_mem_cons.2 ⟨subd9_8_49, List.forall_mem_cons.2 ⟨subd9_8_50, List.forall_mem_cons.2 ⟨subd9_8_51, List.forall_mem_cons.2 ⟨subd9_8_52, List.forall_mem_cons.2 ⟨subd9_8_53, List.forall_mem_cons.2 ⟨subd9_8_54, List.forall_mem_cons.2 ⟨subd9_8_55, List.forall_mem_cons.2 ⟨subd9_8_56, List.forall_mem_cons.2 ⟨subd9_8_57, List.forall_mem_cons.2 ⟨subd9_8_58, List.forall_mem_cons.2 ⟨subd9_8_59, List.forall_mem_cons.2 ⟨subd9_8_60, List.forall_mem_cons.2 ⟨subd9_8_61, List.forall_mem_cons.2 ⟨subd9_8_62, List.forall_mem_cons.2 ⟨subd9_8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_8_64 : subd9_8 [0, -1, -3] = true := by decide +kernel
theorem subd9_8_65 : subd9_8 [0, -1, -2] = true := by decide +kernel
theorem subd9_8_66 : subd9_8 [0, -1, -1] = true := by decide +kernel
theorem subd9_8_67 : subd9_8 [0, -1, 0] = true := by decide +kernel
theorem subd9_8_68 : subd9_8 [0, -1, 1] = true := by decide +kernel
theorem subd9_8_69 : subd9_8 [0, -1, 2] = true := by decide +kernel
theorem subd9_8_70 : subd9_8 [0, -1, 3] = true := by decide +kernel
theorem subd9_8_71 : subd9_8 [0, -1, 4] = true := by decide +kernel
theorem subd9_8_72 : subd9_8 [0, -1, 5] = true := by decide +kernel
theorem subd9_8_73 : subd9_8 [0, -1, 6] = true := by decide +kernel
theorem subd9_8_74 : subd9_8 [0, -1, 7] = true := by decide +kernel
theorem subd9_8_75 : subd9_8 [0, -1, 8] = true := by decide +kernel
theorem subd9_8_76 : subd9_8 [0, -1, 9] = true := by decide +kernel
theorem subd9_8_77 : subd9_8 [0, -1, 10] = true := by decide +kernel
theorem subd9_8_78 : subd9_8 [0, -1, 11] = true := by decide +kernel
theorem subd9_8_79 : subd9_8 [0, -1, 12] = true := by decide +kernel
theorem subd9_8_80 : subd9_8 [0, -1, 13] = true := by decide +kernel
theorem subd9_8_81 : subd9_8 [0, -1, 14] = true := by decide +kernel
theorem subd9_8_82 : subd9_8 [0, -1, 15] = true := by decide +kernel
theorem subd9_8_83 : subd9_8 [0, 0, -21] = true := by decide +kernel
theorem subd9_8_84 : subd9_8 [0, 0, -20] = true := by decide +kernel
theorem subd9_8_85 : subd9_8 [0, 0, -19] = true := by decide +kernel
theorem subd9_8_86 : subd9_8 [0, 0, -18] = true := by decide +kernel
theorem subd9_8_87 : subd9_8 [0, 0, -17] = true := by decide +kernel
theorem subd9_8_88 : subd9_8 [0, 0, -16] = true := by decide +kernel
theorem subd9_8_89 : subd9_8 [0, 0, -15] = true := by decide +kernel
theorem subd9_8_90 : subd9_8 [0, 0, -14] = true := by decide +kernel
theorem subd9_8_91 : subd9_8 [0, 0, -13] = true := by decide +kernel
theorem subd9_8_92 : subd9_8 [0, 0, -12] = true := by decide +kernel
theorem subd9_8_93 : subd9_8 [0, 0, -11] = true := by decide +kernel
theorem subd9_8_94 : subd9_8 [0, 0, -10] = true := by decide +kernel
theorem subd9_8_95 : subd9_8 [0, 0, -9] = true := by decide +kernel
theorem sbd9_8_2 : ∀ q ∈ blkd9_8_2, subd9_8 q = true := by
  unfold blkd9_8_2
  exact List.forall_mem_cons.2 ⟨subd9_8_64, List.forall_mem_cons.2 ⟨subd9_8_65, List.forall_mem_cons.2 ⟨subd9_8_66, List.forall_mem_cons.2 ⟨subd9_8_67, List.forall_mem_cons.2 ⟨subd9_8_68, List.forall_mem_cons.2 ⟨subd9_8_69, List.forall_mem_cons.2 ⟨subd9_8_70, List.forall_mem_cons.2 ⟨subd9_8_71, List.forall_mem_cons.2 ⟨subd9_8_72, List.forall_mem_cons.2 ⟨subd9_8_73, List.forall_mem_cons.2 ⟨subd9_8_74, List.forall_mem_cons.2 ⟨subd9_8_75, List.forall_mem_cons.2 ⟨subd9_8_76, List.forall_mem_cons.2 ⟨subd9_8_77, List.forall_mem_cons.2 ⟨subd9_8_78, List.forall_mem_cons.2 ⟨subd9_8_79, List.forall_mem_cons.2 ⟨subd9_8_80, List.forall_mem_cons.2 ⟨subd9_8_81, List.forall_mem_cons.2 ⟨subd9_8_82, List.forall_mem_cons.2 ⟨subd9_8_83, List.forall_mem_cons.2 ⟨subd9_8_84, List.forall_mem_cons.2 ⟨subd9_8_85, List.forall_mem_cons.2 ⟨subd9_8_86, List.forall_mem_cons.2 ⟨subd9_8_87, List.forall_mem_cons.2 ⟨subd9_8_88, List.forall_mem_cons.2 ⟨subd9_8_89, List.forall_mem_cons.2 ⟨subd9_8_90, List.forall_mem_cons.2 ⟨subd9_8_91, List.forall_mem_cons.2 ⟨subd9_8_92, List.forall_mem_cons.2 ⟨subd9_8_93, List.forall_mem_cons.2 ⟨subd9_8_94, List.forall_mem_cons.2 ⟨subd9_8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
