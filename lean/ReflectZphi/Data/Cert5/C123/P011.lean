import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_5_0 : subd5_5 [-4] = true := by decide +kernel
theorem subd5_5_1 : subd5_5 [-3, -3] = true := by decide +kernel
theorem subd5_5_2 : subd5_5 [-3, -2] = true := by decide +kernel
theorem subd5_5_3 : subd5_5 [-3, -1] = true := by decide +kernel
theorem subd5_5_4 : subd5_5 [-3, 0] = true := by decide +kernel
theorem subd5_5_5 : subd5_5 [-3, 1] = true := by decide +kernel
theorem subd5_5_6 : subd5_5 [-3, 2] = true := by decide +kernel
theorem subd5_5_7 : subd5_5 [-3, 3] = true := by decide +kernel
theorem subd5_5_8 : subd5_5 [-3, 4] = true := by decide +kernel
theorem subd5_5_9 : subd5_5 [-2, -4] = true := by decide +kernel
theorem subd5_5_10 : subd5_5 [-2, -3] = true := by decide +kernel
theorem subd5_5_11 : subd5_5 [-2, -2] = true := by decide +kernel
theorem subd5_5_12 : subd5_5 [-2, -1] = true := by decide +kernel
theorem subd5_5_13 : subd5_5 [-2, 0] = true := by decide +kernel
theorem subd5_5_14 : subd5_5 [-2, 1] = true := by decide +kernel
theorem subd5_5_15 : subd5_5 [-2, 2] = true := by decide +kernel
theorem subd5_5_16 : subd5_5 [-2, 3] = true := by decide +kernel
theorem subd5_5_17 : subd5_5 [-2, 4] = true := by decide +kernel
theorem subd5_5_18 : subd5_5 [-1, -5] = true := by decide +kernel
theorem subd5_5_19 : subd5_5 [-1, -4] = true := by decide +kernel
theorem subd5_5_20 : subd5_5 [-1, -3] = true := by decide +kernel
theorem subd5_5_21 : subd5_5 [-1, -2] = true := by decide +kernel
theorem subd5_5_22 : subd5_5 [-1, -1] = true := by decide +kernel
theorem subd5_5_23 : subd5_5 [-1, 0] = true := by decide +kernel
theorem subd5_5_24 : subd5_5 [-1, 1] = true := by decide +kernel
theorem subd5_5_25 : subd5_5 [-1, 2] = true := by decide +kernel
theorem subd5_5_26 : subd5_5 [-1, 3] = true := by decide +kernel
theorem subd5_5_27 : subd5_5 [-1, 4] = true := by decide +kernel
theorem subd5_5_28 : subd5_5 [-1, 5] = true := by decide +kernel
theorem subd5_5_29 : subd5_5 [0, -5] = true := by decide +kernel
theorem subd5_5_30 : subd5_5 [0, -4] = true := by decide +kernel
theorem subd5_5_31 : subd5_5 [0, -3] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_cons.2 ⟨subd5_5_1, List.forall_mem_cons.2 ⟨subd5_5_2, List.forall_mem_cons.2 ⟨subd5_5_3, List.forall_mem_cons.2 ⟨subd5_5_4, List.forall_mem_cons.2 ⟨subd5_5_5, List.forall_mem_cons.2 ⟨subd5_5_6, List.forall_mem_cons.2 ⟨subd5_5_7, List.forall_mem_cons.2 ⟨subd5_5_8, List.forall_mem_cons.2 ⟨subd5_5_9, List.forall_mem_cons.2 ⟨subd5_5_10, List.forall_mem_cons.2 ⟨subd5_5_11, List.forall_mem_cons.2 ⟨subd5_5_12, List.forall_mem_cons.2 ⟨subd5_5_13, List.forall_mem_cons.2 ⟨subd5_5_14, List.forall_mem_cons.2 ⟨subd5_5_15, List.forall_mem_cons.2 ⟨subd5_5_16, List.forall_mem_cons.2 ⟨subd5_5_17, List.forall_mem_cons.2 ⟨subd5_5_18, List.forall_mem_cons.2 ⟨subd5_5_19, List.forall_mem_cons.2 ⟨subd5_5_20, List.forall_mem_cons.2 ⟨subd5_5_21, List.forall_mem_cons.2 ⟨subd5_5_22, List.forall_mem_cons.2 ⟨subd5_5_23, List.forall_mem_cons.2 ⟨subd5_5_24, List.forall_mem_cons.2 ⟨subd5_5_25, List.forall_mem_cons.2 ⟨subd5_5_26, List.forall_mem_cons.2 ⟨subd5_5_27, List.forall_mem_cons.2 ⟨subd5_5_28, List.forall_mem_cons.2 ⟨subd5_5_29, List.forall_mem_cons.2 ⟨subd5_5_30, List.forall_mem_cons.2 ⟨subd5_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_32 : subd5_5 [0, -2] = true := by decide +kernel
theorem subd5_5_33 : subd5_5 [0, -1] = true := by decide +kernel
theorem subd5_5_34 : subd5_5 [0, 0] = true := by decide +kernel
theorem subd5_5_35 : subd5_5 [0, 1] = true := by decide +kernel
theorem subd5_5_36 : subd5_5 [0, 2] = true := by decide +kernel
theorem subd5_5_37 : subd5_5 [0, 3] = true := by decide +kernel
theorem subd5_5_38 : subd5_5 [0, 4] = true := by decide +kernel
theorem subd5_5_39 : subd5_5 [1, -6] = true := by decide +kernel
theorem subd5_5_40 : subd5_5 [1, -5] = true := by decide +kernel
theorem subd5_5_41 : subd5_5 [1, -4] = true := by decide +kernel
theorem subd5_5_42 : subd5_5 [1, -3] = true := by decide +kernel
theorem subd5_5_43 : subd5_5 [1, -2] = true := by decide +kernel
theorem subd5_5_44 : subd5_5 [1, -1] = true := by decide +kernel
theorem subd5_5_45 : subd5_5 [1, 0] = true := by decide +kernel
theorem subd5_5_46 : subd5_5 [1, 1] = true := by decide +kernel
theorem subd5_5_47 : subd5_5 [1, 2] = true := by decide +kernel
theorem subd5_5_48 : subd5_5 [1, 3] = true := by decide +kernel
theorem subd5_5_49 : subd5_5 [1, 4] = true := by decide +kernel
theorem subd5_5_50 : subd5_5 [2, -5] = true := by decide +kernel
theorem subd5_5_51 : subd5_5 [2, -4] = true := by decide +kernel
theorem subd5_5_52 : subd5_5 [2, -3] = true := by decide +kernel
theorem subd5_5_53 : subd5_5 [2, -2] = true := by decide +kernel
theorem subd5_5_54 : subd5_5 [2, -1] = true := by decide +kernel
theorem subd5_5_55 : subd5_5 [2, 0] = true := by decide +kernel
theorem subd5_5_56 : subd5_5 [2, 1] = true := by decide +kernel
theorem subd5_5_57 : subd5_5 [2, 2] = true := by decide +kernel
theorem subd5_5_58 : subd5_5 [2, 3] = true := by decide +kernel
theorem subd5_5_59 : subd5_5 [3, -5] = true := by decide +kernel
theorem subd5_5_60 : subd5_5 [3, -4] = true := by decide +kernel
theorem subd5_5_61 : subd5_5 [3, -3] = true := by decide +kernel
theorem subd5_5_62 : subd5_5 [3, -2] = true := by decide +kernel
theorem subd5_5_63 : subd5_5 [3, -1] = true := by decide +kernel
theorem sbd5_5_1 : ∀ q ∈ blkd5_5_1, subd5_5 q = true := by
  unfold blkd5_5_1
  exact List.forall_mem_cons.2 ⟨subd5_5_32, List.forall_mem_cons.2 ⟨subd5_5_33, List.forall_mem_cons.2 ⟨subd5_5_34, List.forall_mem_cons.2 ⟨subd5_5_35, List.forall_mem_cons.2 ⟨subd5_5_36, List.forall_mem_cons.2 ⟨subd5_5_37, List.forall_mem_cons.2 ⟨subd5_5_38, List.forall_mem_cons.2 ⟨subd5_5_39, List.forall_mem_cons.2 ⟨subd5_5_40, List.forall_mem_cons.2 ⟨subd5_5_41, List.forall_mem_cons.2 ⟨subd5_5_42, List.forall_mem_cons.2 ⟨subd5_5_43, List.forall_mem_cons.2 ⟨subd5_5_44, List.forall_mem_cons.2 ⟨subd5_5_45, List.forall_mem_cons.2 ⟨subd5_5_46, List.forall_mem_cons.2 ⟨subd5_5_47, List.forall_mem_cons.2 ⟨subd5_5_48, List.forall_mem_cons.2 ⟨subd5_5_49, List.forall_mem_cons.2 ⟨subd5_5_50, List.forall_mem_cons.2 ⟨subd5_5_51, List.forall_mem_cons.2 ⟨subd5_5_52, List.forall_mem_cons.2 ⟨subd5_5_53, List.forall_mem_cons.2 ⟨subd5_5_54, List.forall_mem_cons.2 ⟨subd5_5_55, List.forall_mem_cons.2 ⟨subd5_5_56, List.forall_mem_cons.2 ⟨subd5_5_57, List.forall_mem_cons.2 ⟨subd5_5_58, List.forall_mem_cons.2 ⟨subd5_5_59, List.forall_mem_cons.2 ⟨subd5_5_60, List.forall_mem_cons.2 ⟨subd5_5_61, List.forall_mem_cons.2 ⟨subd5_5_62, List.forall_mem_cons.2 ⟨subd5_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_64 : subd5_5 [3, 0] = true := by decide +kernel
theorem subd5_5_65 : subd5_5 [3, 1] = true := by decide +kernel
theorem subd5_5_66 : subd5_5 [3, 2] = true := by decide +kernel
theorem subd5_5_67 : subd5_5 [4] = true := by decide +kernel
theorem sbd5_5_2 : ∀ q ∈ blkd5_5_2, subd5_5 q = true := by
  unfold blkd5_5_2
  exact List.forall_mem_cons.2 ⟨subd5_5_64, List.forall_mem_cons.2 ⟨subd5_5_65, List.forall_mem_cons.2 ⟨subd5_5_66, List.forall_mem_cons.2 ⟨subd5_5_67, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [-4, -2] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-4, -1] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [-4, 0] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [-4, 1] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [-4, 2] = true := by decide +kernel
theorem subd5_6_5 : subd5_6 [-3, -4] = true := by decide +kernel
theorem subd5_6_6 : subd5_6 [-3, -3] = true := by decide +kernel
theorem subd5_6_7 : subd5_6 [-3, -2] = true := by decide +kernel
theorem subd5_6_8 : subd5_6 [-3, -1] = true := by decide +kernel
theorem subd5_6_9 : subd5_6 [-3, 0] = true := by decide +kernel
theorem subd5_6_10 : subd5_6 [-3, 1] = true := by decide +kernel
theorem subd5_6_11 : subd5_6 [-3, 2] = true := by decide +kernel
theorem subd5_6_12 : subd5_6 [-3, 3] = true := by decide +kernel
theorem subd5_6_13 : subd5_6 [-2, -5] = true := by decide +kernel
theorem subd5_6_14 : subd5_6 [-2, -4] = true := by decide +kernel
theorem subd5_6_15 : subd5_6 [-2, -3] = true := by decide +kernel
theorem subd5_6_16 : subd5_6 [-2, -2] = true := by decide +kernel
theorem subd5_6_17 : subd5_6 [-2, -1, -8] = true := by decide +kernel
theorem subd5_6_18 : subd5_6 [-2, -1, -7] = true := by decide +kernel
theorem subd5_6_19 : subd5_6 [-2, -1, -6] = true := by decide +kernel
theorem subd5_6_20 : subd5_6 [-2, -1, -5] = true := by decide +kernel
theorem subd5_6_21 : subd5_6 [-2, -1, -4] = true := by decide +kernel
theorem subd5_6_22 : subd5_6 [-2, -1, -3] = true := by decide +kernel
theorem subd5_6_23 : subd5_6 [-2, -1, -2] = true := by decide +kernel
theorem subd5_6_24 : subd5_6 [-2, -1, -1] = true := by decide +kernel
theorem subd5_6_25 : subd5_6 [-2, -1, 0] = true := by decide +kernel
theorem subd5_6_26 : subd5_6 [-2, -1, 1] = true := by decide +kernel
theorem subd5_6_27 : subd5_6 [-2, -1, 2] = true := by decide +kernel
theorem subd5_6_28 : subd5_6 [-2, -1, 3] = true := by decide +kernel
theorem subd5_6_29 : subd5_6 [-2, -1, 4] = true := by decide +kernel
theorem subd5_6_30 : subd5_6 [-2, -1, 5] = true := by decide +kernel
theorem subd5_6_31 : subd5_6 [-2, -1, 6] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_cons.2 ⟨subd5_6_5, List.forall_mem_cons.2 ⟨subd5_6_6, List.forall_mem_cons.2 ⟨subd5_6_7, List.forall_mem_cons.2 ⟨subd5_6_8, List.forall_mem_cons.2 ⟨subd5_6_9, List.forall_mem_cons.2 ⟨subd5_6_10, List.forall_mem_cons.2 ⟨subd5_6_11, List.forall_mem_cons.2 ⟨subd5_6_12, List.forall_mem_cons.2 ⟨subd5_6_13, List.forall_mem_cons.2 ⟨subd5_6_14, List.forall_mem_cons.2 ⟨subd5_6_15, List.forall_mem_cons.2 ⟨subd5_6_16, List.forall_mem_cons.2 ⟨subd5_6_17, List.forall_mem_cons.2 ⟨subd5_6_18, List.forall_mem_cons.2 ⟨subd5_6_19, List.forall_mem_cons.2 ⟨subd5_6_20, List.forall_mem_cons.2 ⟨subd5_6_21, List.forall_mem_cons.2 ⟨subd5_6_22, List.forall_mem_cons.2 ⟨subd5_6_23, List.forall_mem_cons.2 ⟨subd5_6_24, List.forall_mem_cons.2 ⟨subd5_6_25, List.forall_mem_cons.2 ⟨subd5_6_26, List.forall_mem_cons.2 ⟨subd5_6_27, List.forall_mem_cons.2 ⟨subd5_6_28, List.forall_mem_cons.2 ⟨subd5_6_29, List.forall_mem_cons.2 ⟨subd5_6_30, List.forall_mem_cons.2 ⟨subd5_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_32 : subd5_6 [-2, 0, -8] = true := by decide +kernel
theorem subd5_6_33 : subd5_6 [-2, 0, -7] = true := by decide +kernel
theorem subd5_6_34 : subd5_6 [-2, 0, -6] = true := by decide +kernel
theorem subd5_6_35 : subd5_6 [-2, 0, -5] = true := by decide +kernel
theorem subd5_6_36 : subd5_6 [-2, 0, -4] = true := by decide +kernel
theorem subd5_6_37 : subd5_6 [-2, 0, -3] = true := by decide +kernel
theorem subd5_6_38 : subd5_6 [-2, 0, -2] = true := by decide +kernel
theorem subd5_6_39 : subd5_6 [-2, 0, -1] = true := by decide +kernel
theorem subd5_6_40 : subd5_6 [-2, 0, 0] = true := by decide +kernel
theorem subd5_6_41 : subd5_6 [-2, 0, 1] = true := by decide +kernel
theorem subd5_6_42 : subd5_6 [-2, 0, 2] = true := by decide +kernel
theorem subd5_6_43 : subd5_6 [-2, 0, 3] = true := by decide +kernel
theorem subd5_6_44 : subd5_6 [-2, 0, 4] = true := by decide +kernel
theorem subd5_6_45 : subd5_6 [-2, 0, 5] = true := by decide +kernel
theorem subd5_6_46 : subd5_6 [-2, 0, 6] = true := by decide +kernel
theorem subd5_6_47 : subd5_6 [-2, 1, -8] = true := by decide +kernel
theorem subd5_6_48 : subd5_6 [-2, 1, -7] = true := by decide +kernel
theorem subd5_6_49 : subd5_6 [-2, 1, -6] = true := by decide +kernel
theorem subd5_6_50 : subd5_6 [-2, 1, -5] = true := by decide +kernel
theorem subd5_6_51 : subd5_6 [-2, 1, -4] = true := by decide +kernel
theorem subd5_6_52 : subd5_6 [-2, 1, -3] = true := by decide +kernel
theorem subd5_6_53 : subd5_6 [-2, 1, -2] = true := by decide +kernel
theorem subd5_6_54 : subd5_6 [-2, 1, -1] = true := by decide +kernel
theorem subd5_6_55 : subd5_6 [-2, 1, 0] = true := by decide +kernel
theorem subd5_6_56 : subd5_6 [-2, 1, 1] = true := by decide +kernel
theorem subd5_6_57 : subd5_6 [-2, 1, 2] = true := by decide +kernel
theorem subd5_6_58 : subd5_6 [-2, 1, 3] = true := by decide +kernel
theorem subd5_6_59 : subd5_6 [-2, 1, 4] = true := by decide +kernel
theorem subd5_6_60 : subd5_6 [-2, 1, 5] = true := by decide +kernel
theorem subd5_6_61 : subd5_6 [-2, 1, 6] = true := by decide +kernel
theorem subd5_6_62 : subd5_6 [-2, 2, -7] = true := by decide +kernel
theorem subd5_6_63 : subd5_6 [-2, 2, -6] = true := by decide +kernel
theorem sbd5_6_1 : ∀ q ∈ blkd5_6_1, subd5_6 q = true := by
  unfold blkd5_6_1
  exact List.forall_mem_cons.2 ⟨subd5_6_32, List.forall_mem_cons.2 ⟨subd5_6_33, List.forall_mem_cons.2 ⟨subd5_6_34, List.forall_mem_cons.2 ⟨subd5_6_35, List.forall_mem_cons.2 ⟨subd5_6_36, List.forall_mem_cons.2 ⟨subd5_6_37, List.forall_mem_cons.2 ⟨subd5_6_38, List.forall_mem_cons.2 ⟨subd5_6_39, List.forall_mem_cons.2 ⟨subd5_6_40, List.forall_mem_cons.2 ⟨subd5_6_41, List.forall_mem_cons.2 ⟨subd5_6_42, List.forall_mem_cons.2 ⟨subd5_6_43, List.forall_mem_cons.2 ⟨subd5_6_44, List.forall_mem_cons.2 ⟨subd5_6_45, List.forall_mem_cons.2 ⟨subd5_6_46, List.forall_mem_cons.2 ⟨subd5_6_47, List.forall_mem_cons.2 ⟨subd5_6_48, List.forall_mem_cons.2 ⟨subd5_6_49, List.forall_mem_cons.2 ⟨subd5_6_50, List.forall_mem_cons.2 ⟨subd5_6_51, List.forall_mem_cons.2 ⟨subd5_6_52, List.forall_mem_cons.2 ⟨subd5_6_53, List.forall_mem_cons.2 ⟨subd5_6_54, List.forall_mem_cons.2 ⟨subd5_6_55, List.forall_mem_cons.2 ⟨subd5_6_56, List.forall_mem_cons.2 ⟨subd5_6_57, List.forall_mem_cons.2 ⟨subd5_6_58, List.forall_mem_cons.2 ⟨subd5_6_59, List.forall_mem_cons.2 ⟨subd5_6_60, List.forall_mem_cons.2 ⟨subd5_6_61, List.forall_mem_cons.2 ⟨subd5_6_62, List.forall_mem_cons.2 ⟨subd5_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_64 : subd5_6 [-2, 2, -5] = true := by decide +kernel
theorem subd5_6_65 : subd5_6 [-2, 2, -4] = true := by decide +kernel
theorem subd5_6_66 : subd5_6 [-2, 2, -3] = true := by decide +kernel
theorem subd5_6_67 : subd5_6 [-2, 2, -2] = true := by decide +kernel
theorem subd5_6_68 : subd5_6 [-2, 2, -1] = true := by decide +kernel
theorem subd5_6_69 : subd5_6 [-2, 2, 0] = true := by decide +kernel
theorem subd5_6_70 : subd5_6 [-2, 2, 1] = true := by decide +kernel
theorem subd5_6_71 : subd5_6 [-2, 2, 2] = true := by decide +kernel
theorem subd5_6_72 : subd5_6 [-2, 2, 3] = true := by decide +kernel
theorem subd5_6_73 : subd5_6 [-2, 2, 4] = true := by decide +kernel
theorem subd5_6_74 : subd5_6 [-2, 2, 5] = true := by decide +kernel
theorem subd5_6_75 : subd5_6 [-2, 2, 6] = true := by decide +kernel
theorem subd5_6_76 : subd5_6 [-2, 3] = true := by decide +kernel
theorem subd5_6_77 : subd5_6 [-2, 4] = true := by decide +kernel
theorem subd5_6_78 : subd5_6 [-1, -5] = true := by decide +kernel
theorem subd5_6_79 : subd5_6 [-1, -4] = true := by decide +kernel
theorem subd5_6_80 : subd5_6 [-1, -3] = true := by decide +kernel
theorem subd5_6_81 : subd5_6 [-1, -2, -8] = true := by decide +kernel
theorem subd5_6_82 : subd5_6 [-1, -2, -7] = true := by decide +kernel
theorem subd5_6_83 : subd5_6 [-1, -2, -6] = true := by decide +kernel
theorem subd5_6_84 : subd5_6 [-1, -2, -5] = true := by decide +kernel
theorem subd5_6_85 : subd5_6 [-1, -2, -4] = true := by decide +kernel
theorem subd5_6_86 : subd5_6 [-1, -2, -3] = true := by decide +kernel
theorem subd5_6_87 : subd5_6 [-1, -2, -2] = true := by decide +kernel
theorem subd5_6_88 : subd5_6 [-1, -2, -1] = true := by decide +kernel
theorem subd5_6_89 : subd5_6 [-1, -2, 0] = true := by decide +kernel
theorem subd5_6_90 : subd5_6 [-1, -2, 1] = true := by decide +kernel
theorem subd5_6_91 : subd5_6 [-1, -2, 2] = true := by decide +kernel
theorem subd5_6_92 : subd5_6 [-1, -2, 3] = true := by decide +kernel
theorem subd5_6_93 : subd5_6 [-1, -2, 4] = true := by decide +kernel
theorem subd5_6_94 : subd5_6 [-1, -2, 5] = true := by decide +kernel
theorem subd5_6_95 : subd5_6 [-1, -2, 6] = true := by decide +kernel
theorem sbd5_6_2 : ∀ q ∈ blkd5_6_2, subd5_6 q = true := by
  unfold blkd5_6_2
  exact List.forall_mem_cons.2 ⟨subd5_6_64, List.forall_mem_cons.2 ⟨subd5_6_65, List.forall_mem_cons.2 ⟨subd5_6_66, List.forall_mem_cons.2 ⟨subd5_6_67, List.forall_mem_cons.2 ⟨subd5_6_68, List.forall_mem_cons.2 ⟨subd5_6_69, List.forall_mem_cons.2 ⟨subd5_6_70, List.forall_mem_cons.2 ⟨subd5_6_71, List.forall_mem_cons.2 ⟨subd5_6_72, List.forall_mem_cons.2 ⟨subd5_6_73, List.forall_mem_cons.2 ⟨subd5_6_74, List.forall_mem_cons.2 ⟨subd5_6_75, List.forall_mem_cons.2 ⟨subd5_6_76, List.forall_mem_cons.2 ⟨subd5_6_77, List.forall_mem_cons.2 ⟨subd5_6_78, List.forall_mem_cons.2 ⟨subd5_6_79, List.forall_mem_cons.2 ⟨subd5_6_80, List.forall_mem_cons.2 ⟨subd5_6_81, List.forall_mem_cons.2 ⟨subd5_6_82, List.forall_mem_cons.2 ⟨subd5_6_83, List.forall_mem_cons.2 ⟨subd5_6_84, List.forall_mem_cons.2 ⟨subd5_6_85, List.forall_mem_cons.2 ⟨subd5_6_86, List.forall_mem_cons.2 ⟨subd5_6_87, List.forall_mem_cons.2 ⟨subd5_6_88, List.forall_mem_cons.2 ⟨subd5_6_89, List.forall_mem_cons.2 ⟨subd5_6_90, List.forall_mem_cons.2 ⟨subd5_6_91, List.forall_mem_cons.2 ⟨subd5_6_92, List.forall_mem_cons.2 ⟨subd5_6_93, List.forall_mem_cons.2 ⟨subd5_6_94, List.forall_mem_cons.2 ⟨subd5_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_6_96 : subd5_6 [-1, -1, -8] = true := by decide +kernel
theorem subd5_6_97 : subd5_6 [-1, -1, -7] = true := by decide +kernel
theorem subd5_6_98 : subd5_6 [-1, -1, -6] = true := by decide +kernel
theorem subd5_6_99 : subd5_6 [-1, -1, -5] = true := by decide +kernel
theorem subd5_6_100 : subd5_6 [-1, -1, -4] = true := by decide +kernel
theorem subd5_6_101 : subd5_6 [-1, -1, -3] = true := by decide +kernel
theorem subd5_6_102 : subd5_6 [-1, -1, -2] = true := by decide +kernel
theorem subd5_6_103 : subd5_6 [-1, -1, -1] = true := by decide +kernel
theorem subd5_6_104 : subd5_6 [-1, -1, 0] = true := by decide +kernel
theorem subd5_6_105 : subd5_6 [-1, -1, 1] = true := by decide +kernel
theorem subd5_6_106 : subd5_6 [-1, -1, 2] = true := by decide +kernel
theorem subd5_6_107 : subd5_6 [-1, -1, 3] = true := by decide +kernel
theorem subd5_6_108 : subd5_6 [-1, -1, 4] = true := by decide +kernel
theorem subd5_6_109 : subd5_6 [-1, -1, 5] = true := by decide +kernel
theorem subd5_6_110 : subd5_6 [-1, -1, 6] = true := by decide +kernel
theorem subd5_6_111 : subd5_6 [-1, -1, 7] = true := by decide +kernel
theorem subd5_6_112 : subd5_6 [-1, 0, -8] = true := by decide +kernel
theorem subd5_6_113 : subd5_6 [-1, 0, -7] = true := by decide +kernel
theorem subd5_6_114 : subd5_6 [-1, 0, -6] = true := by decide +kernel
theorem subd5_6_115 : subd5_6 [-1, 0, -5] = true := by decide +kernel
theorem subd5_6_116 : subd5_6 [-1, 0, -4] = true := by decide +kernel
theorem subd5_6_117 : subd5_6 [-1, 0, -3] = true := by decide +kernel
theorem subd5_6_118 : subd5_6 [-1, 0, -2] = true := by decide +kernel
theorem subd5_6_119 : subd5_6 [-1, 0, -1] = true := by decide +kernel
theorem subd5_6_120 : subd5_6 [-1, 0, 0] = true := by decide +kernel
theorem subd5_6_121 : subd5_6 [-1, 0, 1] = true := by decide +kernel
theorem subd5_6_122 : subd5_6 [-1, 0, 2] = true := by decide +kernel
theorem subd5_6_123 : subd5_6 [-1, 0, 3] = true := by decide +kernel
theorem subd5_6_124 : subd5_6 [-1, 0, 4] = true := by decide +kernel
theorem subd5_6_125 : subd5_6 [-1, 0, 5] = true := by decide +kernel
theorem subd5_6_126 : subd5_6 [-1, 0, 6] = true := by decide +kernel
theorem subd5_6_127 : subd5_6 [-1, 0, 7] = true := by decide +kernel
theorem sbd5_6_3 : ∀ q ∈ blkd5_6_3, subd5_6 q = true := by
  unfold blkd5_6_3
  exact List.forall_mem_cons.2 ⟨subd5_6_96, List.forall_mem_cons.2 ⟨subd5_6_97, List.forall_mem_cons.2 ⟨subd5_6_98, List.forall_mem_cons.2 ⟨subd5_6_99, List.forall_mem_cons.2 ⟨subd5_6_100, List.forall_mem_cons.2 ⟨subd5_6_101, List.forall_mem_cons.2 ⟨subd5_6_102, List.forall_mem_cons.2 ⟨subd5_6_103, List.forall_mem_cons.2 ⟨subd5_6_104, List.forall_mem_cons.2 ⟨subd5_6_105, List.forall_mem_cons.2 ⟨subd5_6_106, List.forall_mem_cons.2 ⟨subd5_6_107, List.forall_mem_cons.2 ⟨subd5_6_108, List.forall_mem_cons.2 ⟨subd5_6_109, List.forall_mem_cons.2 ⟨subd5_6_110, List.forall_mem_cons.2 ⟨subd5_6_111, List.forall_mem_cons.2 ⟨subd5_6_112, List.forall_mem_cons.2 ⟨subd5_6_113, List.forall_mem_cons.2 ⟨subd5_6_114, List.forall_mem_cons.2 ⟨subd5_6_115, List.forall_mem_cons.2 ⟨subd5_6_116, List.forall_mem_cons.2 ⟨subd5_6_117, List.forall_mem_cons.2 ⟨subd5_6_118, List.forall_mem_cons.2 ⟨subd5_6_119, List.forall_mem_cons.2 ⟨subd5_6_120, List.forall_mem_cons.2 ⟨subd5_6_121, List.forall_mem_cons.2 ⟨subd5_6_122, List.forall_mem_cons.2 ⟨subd5_6_123, List.forall_mem_cons.2 ⟨subd5_6_124, List.forall_mem_cons.2 ⟨subd5_6_125, List.forall_mem_cons.2 ⟨subd5_6_126, List.forall_mem_cons.2 ⟨subd5_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
