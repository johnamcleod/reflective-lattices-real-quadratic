import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_13 : ldCheck G d6_13.U d6_13.ms ldd6_13 = true := by decide +kernel
theorem pre_okd6_13 : subPre G cell6 d6_13 = true := by decide +kernel
theorem subd6_13_0 : subd6_13 [-4] = true := by decide +kernel
theorem subd6_13_1 : subd6_13 [-3, -3] = true := by decide +kernel
theorem subd6_13_2 : subd6_13 [-3, -2] = true := by decide +kernel
theorem subd6_13_3 : subd6_13 [-3, -1] = true := by decide +kernel
theorem subd6_13_4 : subd6_13 [-3, 0] = true := by decide +kernel
theorem subd6_13_5 : subd6_13 [-3, 1] = true := by decide +kernel
theorem subd6_13_6 : subd6_13 [-3, 2] = true := by decide +kernel
theorem subd6_13_7 : subd6_13 [-3, 3] = true := by decide +kernel
theorem subd6_13_8 : subd6_13 [-2, -4] = true := by decide +kernel
theorem subd6_13_9 : subd6_13 [-2, -3] = true := by decide +kernel
theorem subd6_13_10 : subd6_13 [-2, -2] = true := by decide +kernel
theorem subd6_13_11 : subd6_13 [-2, -1] = true := by decide +kernel
theorem subd6_13_12 : subd6_13 [-2, 0] = true := by decide +kernel
theorem subd6_13_13 : subd6_13 [-2, 1] = true := by decide +kernel
theorem subd6_13_14 : subd6_13 [-2, 2] = true := by decide +kernel
theorem subd6_13_15 : subd6_13 [-2, 3] = true := by decide +kernel
theorem subd6_13_16 : subd6_13 [-2, 4] = true := by decide +kernel
theorem subd6_13_17 : subd6_13 [-1, -5] = true := by decide +kernel
theorem subd6_13_18 : subd6_13 [-1, -4] = true := by decide +kernel
theorem subd6_13_19 : subd6_13 [-1, -3] = true := by decide +kernel
theorem subd6_13_20 : subd6_13 [-1, -2] = true := by decide +kernel
theorem subd6_13_21 : subd6_13 [-1, -1] = true := by decide +kernel
theorem subd6_13_22 : subd6_13 [-1, 0] = true := by decide +kernel
theorem subd6_13_23 : subd6_13 [-1, 1] = true := by decide +kernel
theorem subd6_13_24 : subd6_13 [-1, 2] = true := by decide +kernel
theorem subd6_13_25 : subd6_13 [-1, 3] = true := by decide +kernel
theorem subd6_13_26 : subd6_13 [-1, 4] = true := by decide +kernel
theorem subd6_13_27 : subd6_13 [0, -5] = true := by decide +kernel
theorem subd6_13_28 : subd6_13 [0, -4] = true := by decide +kernel
theorem subd6_13_29 : subd6_13 [0, -3] = true := by decide +kernel
theorem subd6_13_30 : subd6_13 [0, -2] = true := by decide +kernel
theorem subd6_13_31 : subd6_13 [0, -1] = true := by decide +kernel
theorem sbd6_13_0 : ∀ q ∈ blkd6_13_0, subd6_13 q = true := by
  unfold blkd6_13_0
  exact List.forall_mem_cons.2 ⟨subd6_13_0, List.forall_mem_cons.2 ⟨subd6_13_1, List.forall_mem_cons.2 ⟨subd6_13_2, List.forall_mem_cons.2 ⟨subd6_13_3, List.forall_mem_cons.2 ⟨subd6_13_4, List.forall_mem_cons.2 ⟨subd6_13_5, List.forall_mem_cons.2 ⟨subd6_13_6, List.forall_mem_cons.2 ⟨subd6_13_7, List.forall_mem_cons.2 ⟨subd6_13_8, List.forall_mem_cons.2 ⟨subd6_13_9, List.forall_mem_cons.2 ⟨subd6_13_10, List.forall_mem_cons.2 ⟨subd6_13_11, List.forall_mem_cons.2 ⟨subd6_13_12, List.forall_mem_cons.2 ⟨subd6_13_13, List.forall_mem_cons.2 ⟨subd6_13_14, List.forall_mem_cons.2 ⟨subd6_13_15, List.forall_mem_cons.2 ⟨subd6_13_16, List.forall_mem_cons.2 ⟨subd6_13_17, List.forall_mem_cons.2 ⟨subd6_13_18, List.forall_mem_cons.2 ⟨subd6_13_19, List.forall_mem_cons.2 ⟨subd6_13_20, List.forall_mem_cons.2 ⟨subd6_13_21, List.forall_mem_cons.2 ⟨subd6_13_22, List.forall_mem_cons.2 ⟨subd6_13_23, List.forall_mem_cons.2 ⟨subd6_13_24, List.forall_mem_cons.2 ⟨subd6_13_25, List.forall_mem_cons.2 ⟨subd6_13_26, List.forall_mem_cons.2 ⟨subd6_13_27, List.forall_mem_cons.2 ⟨subd6_13_28, List.forall_mem_cons.2 ⟨subd6_13_29, List.forall_mem_cons.2 ⟨subd6_13_30, List.forall_mem_cons.2 ⟨subd6_13_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_13_32 : subd6_13 [0, 0] = true := by decide +kernel
theorem subd6_13_33 : subd6_13 [0, 1] = true := by decide +kernel
theorem subd6_13_34 : subd6_13 [0, 2] = true := by decide +kernel
theorem subd6_13_35 : subd6_13 [0, 3] = true := by decide +kernel
theorem subd6_13_36 : subd6_13 [0, 4] = true := by decide +kernel
theorem subd6_13_37 : subd6_13 [1, -5] = true := by decide +kernel
theorem subd6_13_38 : subd6_13 [1, -4] = true := by decide +kernel
theorem subd6_13_39 : subd6_13 [1, -3] = true := by decide +kernel
theorem subd6_13_40 : subd6_13 [1, -2] = true := by decide +kernel
theorem subd6_13_41 : subd6_13 [1, -1] = true := by decide +kernel
theorem subd6_13_42 : subd6_13 [1, 0] = true := by decide +kernel
theorem subd6_13_43 : subd6_13 [1, 1] = true := by decide +kernel
theorem subd6_13_44 : subd6_13 [1, 2] = true := by decide +kernel
theorem subd6_13_45 : subd6_13 [1, 3] = true := by decide +kernel
theorem subd6_13_46 : subd6_13 [1, 4] = true := by decide +kernel
theorem subd6_13_47 : subd6_13 [2, -5] = true := by decide +kernel
theorem subd6_13_48 : subd6_13 [2, -4] = true := by decide +kernel
theorem subd6_13_49 : subd6_13 [2, -3] = true := by decide +kernel
theorem subd6_13_50 : subd6_13 [2, -2] = true := by decide +kernel
theorem subd6_13_51 : subd6_13 [2, -1] = true := by decide +kernel
theorem subd6_13_52 : subd6_13 [2, 0] = true := by decide +kernel
theorem subd6_13_53 : subd6_13 [2, 1] = true := by decide +kernel
theorem subd6_13_54 : subd6_13 [2, 2] = true := by decide +kernel
theorem subd6_13_55 : subd6_13 [2, 3] = true := by decide +kernel
theorem subd6_13_56 : subd6_13 [3, -4] = true := by decide +kernel
theorem subd6_13_57 : subd6_13 [3, -3] = true := by decide +kernel
theorem subd6_13_58 : subd6_13 [3, -2] = true := by decide +kernel
theorem subd6_13_59 : subd6_13 [3, -1] = true := by decide +kernel
theorem subd6_13_60 : subd6_13 [3, 0] = true := by decide +kernel
theorem subd6_13_61 : subd6_13 [3, 1] = true := by decide +kernel
theorem subd6_13_62 : subd6_13 [3, 2] = true := by decide +kernel
theorem subd6_13_63 : subd6_13 [4] = true := by decide +kernel
theorem sbd6_13_1 : ∀ q ∈ blkd6_13_1, subd6_13 q = true := by
  unfold blkd6_13_1
  exact List.forall_mem_cons.2 ⟨subd6_13_32, List.forall_mem_cons.2 ⟨subd6_13_33, List.forall_mem_cons.2 ⟨subd6_13_34, List.forall_mem_cons.2 ⟨subd6_13_35, List.forall_mem_cons.2 ⟨subd6_13_36, List.forall_mem_cons.2 ⟨subd6_13_37, List.forall_mem_cons.2 ⟨subd6_13_38, List.forall_mem_cons.2 ⟨subd6_13_39, List.forall_mem_cons.2 ⟨subd6_13_40, List.forall_mem_cons.2 ⟨subd6_13_41, List.forall_mem_cons.2 ⟨subd6_13_42, List.forall_mem_cons.2 ⟨subd6_13_43, List.forall_mem_cons.2 ⟨subd6_13_44, List.forall_mem_cons.2 ⟨subd6_13_45, List.forall_mem_cons.2 ⟨subd6_13_46, List.forall_mem_cons.2 ⟨subd6_13_47, List.forall_mem_cons.2 ⟨subd6_13_48, List.forall_mem_cons.2 ⟨subd6_13_49, List.forall_mem_cons.2 ⟨subd6_13_50, List.forall_mem_cons.2 ⟨subd6_13_51, List.forall_mem_cons.2 ⟨subd6_13_52, List.forall_mem_cons.2 ⟨subd6_13_53, List.forall_mem_cons.2 ⟨subd6_13_54, List.forall_mem_cons.2 ⟨subd6_13_55, List.forall_mem_cons.2 ⟨subd6_13_56, List.forall_mem_cons.2 ⟨subd6_13_57, List.forall_mem_cons.2 ⟨subd6_13_58, List.forall_mem_cons.2 ⟨subd6_13_59, List.forall_mem_cons.2 ⟨subd6_13_60, List.forall_mem_cons.2 ⟨subd6_13_61, List.forall_mem_cons.2 ⟨subd6_13_62, List.forall_mem_cons.2 ⟨subd6_13_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_14 : ldCheck G d6_14.U d6_14.ms ldd6_14 = true := by decide +kernel
theorem pre_okd6_14 : subPre G cell6 d6_14 = true := by decide +kernel
theorem subd6_14_0 : subd6_14 [-4, -3] = true := by decide +kernel
theorem subd6_14_1 : subd6_14 [-4, -2] = true := by decide +kernel
theorem subd6_14_2 : subd6_14 [-4, -1] = true := by decide +kernel
theorem subd6_14_3 : subd6_14 [-4, 0, -7] = true := by decide +kernel
theorem subd6_14_4 : subd6_14 [-4, 0, -6] = true := by decide +kernel
theorem subd6_14_5 : subd6_14 [-4, 0, -5] = true := by decide +kernel
theorem subd6_14_6 : subd6_14 [-4, 0, -4] = true := by decide +kernel
theorem subd6_14_7 : subd6_14 [-4, 0, -3] = true := by decide +kernel
theorem subd6_14_8 : subd6_14 [-4, 0, -2] = true := by decide +kernel
theorem subd6_14_9 : subd6_14 [-4, 0, -1] = true := by decide +kernel
theorem subd6_14_10 : subd6_14 [-4, 0, 0] = true := by decide +kernel
theorem subd6_14_11 : subd6_14 [-4, 0, 1] = true := by decide +kernel
theorem subd6_14_12 : subd6_14 [-4, 0, 2] = true := by decide +kernel
theorem subd6_14_13 : subd6_14 [-4, 0, 3] = true := by decide +kernel
theorem subd6_14_14 : subd6_14 [-4, 0, 4] = true := by decide +kernel
theorem subd6_14_15 : subd6_14 [-4, 0, 5] = true := by decide +kernel
theorem subd6_14_16 : subd6_14 [-4, 0, 6] = true := by decide +kernel
theorem subd6_14_17 : subd6_14 [-4, 1] = true := by decide +kernel
theorem subd6_14_18 : subd6_14 [-4, 2] = true := by decide +kernel
theorem subd6_14_19 : subd6_14 [-3, -4] = true := by decide +kernel
theorem subd6_14_20 : subd6_14 [-3, -3] = true := by decide +kernel
theorem subd6_14_21 : subd6_14 [-3, -2, -9] = true := by decide +kernel
theorem subd6_14_22 : subd6_14 [-3, -2, -8] = true := by decide +kernel
theorem subd6_14_23 : subd6_14 [-3, -2, -7] = true := by decide +kernel
theorem subd6_14_24 : subd6_14 [-3, -2, -6] = true := by decide +kernel
theorem subd6_14_25 : subd6_14 [-3, -2, -5] = true := by decide +kernel
theorem subd6_14_26 : subd6_14 [-3, -2, -4] = true := by decide +kernel
theorem subd6_14_27 : subd6_14 [-3, -2, -3] = true := by decide +kernel
theorem subd6_14_28 : subd6_14 [-3, -2, -2] = true := by decide +kernel
theorem subd6_14_29 : subd6_14 [-3, -2, -1] = true := by decide +kernel
theorem subd6_14_30 : subd6_14 [-3, -2, 0] = true := by decide +kernel
theorem subd6_14_31 : subd6_14 [-3, -2, 1] = true := by decide +kernel
theorem sbd6_14_0 : ∀ q ∈ blkd6_14_0, subd6_14 q = true := by
  unfold blkd6_14_0
  exact List.forall_mem_cons.2 ⟨subd6_14_0, List.forall_mem_cons.2 ⟨subd6_14_1, List.forall_mem_cons.2 ⟨subd6_14_2, List.forall_mem_cons.2 ⟨subd6_14_3, List.forall_mem_cons.2 ⟨subd6_14_4, List.forall_mem_cons.2 ⟨subd6_14_5, List.forall_mem_cons.2 ⟨subd6_14_6, List.forall_mem_cons.2 ⟨subd6_14_7, List.forall_mem_cons.2 ⟨subd6_14_8, List.forall_mem_cons.2 ⟨subd6_14_9, List.forall_mem_cons.2 ⟨subd6_14_10, List.forall_mem_cons.2 ⟨subd6_14_11, List.forall_mem_cons.2 ⟨subd6_14_12, List.forall_mem_cons.2 ⟨subd6_14_13, List.forall_mem_cons.2 ⟨subd6_14_14, List.forall_mem_cons.2 ⟨subd6_14_15, List.forall_mem_cons.2 ⟨subd6_14_16, List.forall_mem_cons.2 ⟨subd6_14_17, List.forall_mem_cons.2 ⟨subd6_14_18, List.forall_mem_cons.2 ⟨subd6_14_19, List.forall_mem_cons.2 ⟨subd6_14_20, List.forall_mem_cons.2 ⟨subd6_14_21, List.forall_mem_cons.2 ⟨subd6_14_22, List.forall_mem_cons.2 ⟨subd6_14_23, List.forall_mem_cons.2 ⟨subd6_14_24, List.forall_mem_cons.2 ⟨subd6_14_25, List.forall_mem_cons.2 ⟨subd6_14_26, List.forall_mem_cons.2 ⟨subd6_14_27, List.forall_mem_cons.2 ⟨subd6_14_28, List.forall_mem_cons.2 ⟨subd6_14_29, List.forall_mem_cons.2 ⟨subd6_14_30, List.forall_mem_cons.2 ⟨subd6_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_32 : subd6_14 [-3, -2, 2] = true := by decide +kernel
theorem subd6_14_33 : subd6_14 [-3, -2, 3] = true := by decide +kernel
theorem subd6_14_34 : subd6_14 [-3, -2, 4] = true := by decide +kernel
theorem subd6_14_35 : subd6_14 [-3, -2, 5] = true := by decide +kernel
theorem subd6_14_36 : subd6_14 [-3, -2, 6] = true := by decide +kernel
theorem subd6_14_37 : subd6_14 [-3, -2, 7] = true := by decide +kernel
theorem subd6_14_38 : subd6_14 [-3, -1, -10] = true := by decide +kernel
theorem subd6_14_39 : subd6_14 [-3, -1, -9] = true := by decide +kernel
theorem subd6_14_40 : subd6_14 [-3, -1, -8] = true := by decide +kernel
theorem subd6_14_41 : subd6_14 [-3, -1, -7] = true := by decide +kernel
theorem subd6_14_42 : subd6_14 [-3, -1, -6] = true := by decide +kernel
theorem subd6_14_43 : subd6_14 [-3, -1, -5] = true := by decide +kernel
theorem subd6_14_44 : subd6_14 [-3, -1, -4] = true := by decide +kernel
theorem subd6_14_45 : subd6_14 [-3, -1, -3] = true := by decide +kernel
theorem subd6_14_46 : subd6_14 [-3, -1, -2] = true := by decide +kernel
theorem subd6_14_47 : subd6_14 [-3, -1, -1] = true := by decide +kernel
theorem subd6_14_48 : subd6_14 [-3, -1, 0] = true := by decide +kernel
theorem subd6_14_49 : subd6_14 [-3, -1, 1] = true := by decide +kernel
theorem subd6_14_50 : subd6_14 [-3, -1, 2] = true := by decide +kernel
theorem subd6_14_51 : subd6_14 [-3, -1, 3] = true := by decide +kernel
theorem subd6_14_52 : subd6_14 [-3, -1, 4] = true := by decide +kernel
theorem subd6_14_53 : subd6_14 [-3, -1, 5] = true := by decide +kernel
theorem subd6_14_54 : subd6_14 [-3, -1, 6] = true := by decide +kernel
theorem subd6_14_55 : subd6_14 [-3, -1, 7] = true := by decide +kernel
theorem subd6_14_56 : subd6_14 [-3, -1, 8] = true := by decide +kernel
theorem subd6_14_57 : subd6_14 [-3, 0, -10] = true := by decide +kernel
theorem subd6_14_58 : subd6_14 [-3, 0, -9] = true := by decide +kernel
theorem subd6_14_59 : subd6_14 [-3, 0, -8] = true := by decide +kernel
theorem subd6_14_60 : subd6_14 [-3, 0, -7] = true := by decide +kernel
theorem subd6_14_61 : subd6_14 [-3, 0, -6] = true := by decide +kernel
theorem subd6_14_62 : subd6_14 [-3, 0, -5] = true := by decide +kernel
theorem subd6_14_63 : subd6_14 [-3, 0, -4] = true := by decide +kernel
theorem sbd6_14_1 : ∀ q ∈ blkd6_14_1, subd6_14 q = true := by
  unfold blkd6_14_1
  exact List.forall_mem_cons.2 ⟨subd6_14_32, List.forall_mem_cons.2 ⟨subd6_14_33, List.forall_mem_cons.2 ⟨subd6_14_34, List.forall_mem_cons.2 ⟨subd6_14_35, List.forall_mem_cons.2 ⟨subd6_14_36, List.forall_mem_cons.2 ⟨subd6_14_37, List.forall_mem_cons.2 ⟨subd6_14_38, List.forall_mem_cons.2 ⟨subd6_14_39, List.forall_mem_cons.2 ⟨subd6_14_40, List.forall_mem_cons.2 ⟨subd6_14_41, List.forall_mem_cons.2 ⟨subd6_14_42, List.forall_mem_cons.2 ⟨subd6_14_43, List.forall_mem_cons.2 ⟨subd6_14_44, List.forall_mem_cons.2 ⟨subd6_14_45, List.forall_mem_cons.2 ⟨subd6_14_46, List.forall_mem_cons.2 ⟨subd6_14_47, List.forall_mem_cons.2 ⟨subd6_14_48, List.forall_mem_cons.2 ⟨subd6_14_49, List.forall_mem_cons.2 ⟨subd6_14_50, List.forall_mem_cons.2 ⟨subd6_14_51, List.forall_mem_cons.2 ⟨subd6_14_52, List.forall_mem_cons.2 ⟨subd6_14_53, List.forall_mem_cons.2 ⟨subd6_14_54, List.forall_mem_cons.2 ⟨subd6_14_55, List.forall_mem_cons.2 ⟨subd6_14_56, List.forall_mem_cons.2 ⟨subd6_14_57, List.forall_mem_cons.2 ⟨subd6_14_58, List.forall_mem_cons.2 ⟨subd6_14_59, List.forall_mem_cons.2 ⟨subd6_14_60, List.forall_mem_cons.2 ⟨subd6_14_61, List.forall_mem_cons.2 ⟨subd6_14_62, List.forall_mem_cons.2 ⟨subd6_14_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_64 : subd6_14 [-3, 0, -3] = true := by decide +kernel
theorem subd6_14_65 : subd6_14 [-3, 0, -2] = true := by decide +kernel
theorem subd6_14_66 : subd6_14 [-3, 0, -1] = true := by decide +kernel
theorem subd6_14_67 : subd6_14 [-3, 0, 0] = true := by decide +kernel
theorem subd6_14_68 : subd6_14 [-3, 0, 1] = true := by decide +kernel
theorem subd6_14_69 : subd6_14 [-3, 0, 2] = true := by decide +kernel
theorem subd6_14_70 : subd6_14 [-3, 0, 3] = true := by decide +kernel
theorem subd6_14_71 : subd6_14 [-3, 0, 4] = true := by decide +kernel
theorem subd6_14_72 : subd6_14 [-3, 0, 5] = true := by decide +kernel
theorem subd6_14_73 : subd6_14 [-3, 0, 6] = true := by decide +kernel
theorem subd6_14_74 : subd6_14 [-3, 0, 7] = true := by decide +kernel
theorem subd6_14_75 : subd6_14 [-3, 0, 8] = true := by decide +kernel
theorem subd6_14_76 : subd6_14 [-3, 0, 9] = true := by decide +kernel
theorem subd6_14_77 : subd6_14 [-3, 1, -9] = true := by decide +kernel
theorem subd6_14_78 : subd6_14 [-3, 1, -8] = true := by decide +kernel
theorem subd6_14_79 : subd6_14 [-3, 1, -7] = true := by decide +kernel
theorem subd6_14_80 : subd6_14 [-3, 1, -6] = true := by decide +kernel
theorem subd6_14_81 : subd6_14 [-3, 1, -5] = true := by decide +kernel
theorem subd6_14_82 : subd6_14 [-3, 1, -4] = true := by decide +kernel
theorem subd6_14_83 : subd6_14 [-3, 1, -3] = true := by decide +kernel
theorem subd6_14_84 : subd6_14 [-3, 1, -2] = true := by decide +kernel
theorem subd6_14_85 : subd6_14 [-3, 1, -1] = true := by decide +kernel
theorem subd6_14_86 : subd6_14 [-3, 1, 0] = true := by decide +kernel
theorem subd6_14_87 : subd6_14 [-3, 1, 1] = true := by decide +kernel
theorem subd6_14_88 : subd6_14 [-3, 1, 2] = true := by decide +kernel
theorem subd6_14_89 : subd6_14 [-3, 1, 3] = true := by decide +kernel
theorem subd6_14_90 : subd6_14 [-3, 1, 4] = true := by decide +kernel
theorem subd6_14_91 : subd6_14 [-3, 1, 5] = true := by decide +kernel
theorem subd6_14_92 : subd6_14 [-3, 1, 6] = true := by decide +kernel
theorem subd6_14_93 : subd6_14 [-3, 1, 7] = true := by decide +kernel
theorem subd6_14_94 : subd6_14 [-3, 1, 8] = true := by decide +kernel
theorem subd6_14_95 : subd6_14 [-3, 1, 9] = true := by decide +kernel
theorem sbd6_14_2 : ∀ q ∈ blkd6_14_2, subd6_14 q = true := by
  unfold blkd6_14_2
  exact List.forall_mem_cons.2 ⟨subd6_14_64, List.forall_mem_cons.2 ⟨subd6_14_65, List.forall_mem_cons.2 ⟨subd6_14_66, List.forall_mem_cons.2 ⟨subd6_14_67, List.forall_mem_cons.2 ⟨subd6_14_68, List.forall_mem_cons.2 ⟨subd6_14_69, List.forall_mem_cons.2 ⟨subd6_14_70, List.forall_mem_cons.2 ⟨subd6_14_71, List.forall_mem_cons.2 ⟨subd6_14_72, List.forall_mem_cons.2 ⟨subd6_14_73, List.forall_mem_cons.2 ⟨subd6_14_74, List.forall_mem_cons.2 ⟨subd6_14_75, List.forall_mem_cons.2 ⟨subd6_14_76, List.forall_mem_cons.2 ⟨subd6_14_77, List.forall_mem_cons.2 ⟨subd6_14_78, List.forall_mem_cons.2 ⟨subd6_14_79, List.forall_mem_cons.2 ⟨subd6_14_80, List.forall_mem_cons.2 ⟨subd6_14_81, List.forall_mem_cons.2 ⟨subd6_14_82, List.forall_mem_cons.2 ⟨subd6_14_83, List.forall_mem_cons.2 ⟨subd6_14_84, List.forall_mem_cons.2 ⟨subd6_14_85, List.forall_mem_cons.2 ⟨subd6_14_86, List.forall_mem_cons.2 ⟨subd6_14_87, List.forall_mem_cons.2 ⟨subd6_14_88, List.forall_mem_cons.2 ⟨subd6_14_89, List.forall_mem_cons.2 ⟨subd6_14_90, List.forall_mem_cons.2 ⟨subd6_14_91, List.forall_mem_cons.2 ⟨subd6_14_92, List.forall_mem_cons.2 ⟨subd6_14_93, List.forall_mem_cons.2 ⟨subd6_14_94, List.forall_mem_cons.2 ⟨subd6_14_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_96 : subd6_14 [-3, 2, -8] = true := by decide +kernel
theorem subd6_14_97 : subd6_14 [-3, 2, -7] = true := by decide +kernel
theorem subd6_14_98 : subd6_14 [-3, 2, -6] = true := by decide +kernel
theorem subd6_14_99 : subd6_14 [-3, 2, -5] = true := by decide +kernel
theorem subd6_14_100 : subd6_14 [-3, 2, -4] = true := by decide +kernel
theorem subd6_14_101 : subd6_14 [-3, 2, -3] = true := by decide +kernel
theorem subd6_14_102 : subd6_14 [-3, 2, -2] = true := by decide +kernel
theorem subd6_14_103 : subd6_14 [-3, 2, -1] = true := by decide +kernel
theorem subd6_14_104 : subd6_14 [-3, 2, 0] = true := by decide +kernel
theorem subd6_14_105 : subd6_14 [-3, 2, 1] = true := by decide +kernel
theorem subd6_14_106 : subd6_14 [-3, 2, 2] = true := by decide +kernel
theorem subd6_14_107 : subd6_14 [-3, 2, 3] = true := by decide +kernel
theorem subd6_14_108 : subd6_14 [-3, 2, 4] = true := by decide +kernel
theorem subd6_14_109 : subd6_14 [-3, 2, 5] = true := by decide +kernel
theorem subd6_14_110 : subd6_14 [-3, 2, 6] = true := by decide +kernel
theorem subd6_14_111 : subd6_14 [-3, 2, 7] = true := by decide +kernel
theorem subd6_14_112 : subd6_14 [-3, 2, 8] = true := by decide +kernel
theorem subd6_14_113 : subd6_14 [-3, 3] = true := by decide +kernel
theorem subd6_14_114 : subd6_14 [-2, -5] = true := by decide +kernel
theorem subd6_14_115 : subd6_14 [-2, -4] = true := by decide +kernel
theorem subd6_14_116 : subd6_14 [-2, -3, -9] = true := by decide +kernel
theorem subd6_14_117 : subd6_14 [-2, -3, -8] = true := by decide +kernel
theorem subd6_14_118 : subd6_14 [-2, -3, -7] = true := by decide +kernel
theorem subd6_14_119 : subd6_14 [-2, -3, -6] = true := by decide +kernel
theorem subd6_14_120 : subd6_14 [-2, -3, -5] = true := by decide +kernel
theorem subd6_14_121 : subd6_14 [-2, -3, -4] = true := by decide +kernel
theorem subd6_14_122 : subd6_14 [-2, -3, -3] = true := by decide +kernel
theorem subd6_14_123 : subd6_14 [-2, -3, -2] = true := by decide +kernel
theorem subd6_14_124 : subd6_14 [-2, -3, -1] = true := by decide +kernel
theorem subd6_14_125 : subd6_14 [-2, -3, 0] = true := by decide +kernel
theorem subd6_14_126 : subd6_14 [-2, -3, 1] = true := by decide +kernel
theorem subd6_14_127 : subd6_14 [-2, -3, 2] = true := by decide +kernel
theorem sbd6_14_3 : ∀ q ∈ blkd6_14_3, subd6_14 q = true := by
  unfold blkd6_14_3
  exact List.forall_mem_cons.2 ⟨subd6_14_96, List.forall_mem_cons.2 ⟨subd6_14_97, List.forall_mem_cons.2 ⟨subd6_14_98, List.forall_mem_cons.2 ⟨subd6_14_99, List.forall_mem_cons.2 ⟨subd6_14_100, List.forall_mem_cons.2 ⟨subd6_14_101, List.forall_mem_cons.2 ⟨subd6_14_102, List.forall_mem_cons.2 ⟨subd6_14_103, List.forall_mem_cons.2 ⟨subd6_14_104, List.forall_mem_cons.2 ⟨subd6_14_105, List.forall_mem_cons.2 ⟨subd6_14_106, List.forall_mem_cons.2 ⟨subd6_14_107, List.forall_mem_cons.2 ⟨subd6_14_108, List.forall_mem_cons.2 ⟨subd6_14_109, List.forall_mem_cons.2 ⟨subd6_14_110, List.forall_mem_cons.2 ⟨subd6_14_111, List.forall_mem_cons.2 ⟨subd6_14_112, List.forall_mem_cons.2 ⟨subd6_14_113, List.forall_mem_cons.2 ⟨subd6_14_114, List.forall_mem_cons.2 ⟨subd6_14_115, List.forall_mem_cons.2 ⟨subd6_14_116, List.forall_mem_cons.2 ⟨subd6_14_117, List.forall_mem_cons.2 ⟨subd6_14_118, List.forall_mem_cons.2 ⟨subd6_14_119, List.forall_mem_cons.2 ⟨subd6_14_120, List.forall_mem_cons.2 ⟨subd6_14_121, List.forall_mem_cons.2 ⟨subd6_14_122, List.forall_mem_cons.2 ⟨subd6_14_123, List.forall_mem_cons.2 ⟨subd6_14_124, List.forall_mem_cons.2 ⟨subd6_14_125, List.forall_mem_cons.2 ⟨subd6_14_126, List.forall_mem_cons.2 ⟨subd6_14_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_128 : subd6_14 [-2, -3, 3] = true := by decide +kernel
theorem subd6_14_129 : subd6_14 [-2, -3, 4] = true := by decide +kernel
theorem subd6_14_130 : subd6_14 [-2, -3, 5] = true := by decide +kernel
theorem subd6_14_131 : subd6_14 [-2, -3, 6] = true := by decide +kernel
theorem subd6_14_132 : subd6_14 [-2, -2, -11] = true := by decide +kernel
theorem subd6_14_133 : subd6_14 [-2, -2, -10] = true := by decide +kernel
theorem subd6_14_134 : subd6_14 [-2, -2, -9] = true := by decide +kernel
theorem subd6_14_135 : subd6_14 [-2, -2, -8] = true := by decide +kernel
theorem subd6_14_136 : subd6_14 [-2, -2, -7] = true := by decide +kernel
theorem subd6_14_137 : subd6_14 [-2, -2, -6] = true := by decide +kernel
theorem subd6_14_138 : subd6_14 [-2, -2, -5] = true := by decide +kernel
theorem subd6_14_139 : subd6_14 [-2, -2, -4] = true := by decide +kernel
theorem subd6_14_140 : subd6_14 [-2, -2, -3] = true := by decide +kernel
theorem subd6_14_141 : subd6_14 [-2, -2, -2] = true := by decide +kernel
theorem subd6_14_142 : subd6_14 [-2, -2, -1] = true := by decide +kernel
theorem subd6_14_143 : subd6_14 [-2, -2, 0] = true := by decide +kernel
theorem subd6_14_144 : subd6_14 [-2, -2, 1] = true := by decide +kernel
theorem subd6_14_145 : subd6_14 [-2, -2, 2] = true := by decide +kernel
theorem subd6_14_146 : subd6_14 [-2, -2, 3] = true := by decide +kernel
theorem subd6_14_147 : subd6_14 [-2, -2, 4] = true := by decide +kernel
theorem subd6_14_148 : subd6_14 [-2, -2, 5] = true := by decide +kernel
theorem subd6_14_149 : subd6_14 [-2, -2, 6] = true := by decide +kernel
theorem subd6_14_150 : subd6_14 [-2, -2, 7] = true := by decide +kernel
theorem subd6_14_151 : subd6_14 [-2, -2, 8] = true := by decide +kernel
theorem subd6_14_152 : subd6_14 [-2, -2, 9] = true := by decide +kernel
theorem subd6_14_153 : subd6_14 [-2, -1, -11] = true := by decide +kernel
theorem subd6_14_154 : subd6_14 [-2, -1, -10] = true := by decide +kernel
theorem subd6_14_155 : subd6_14 [-2, -1, -9] = true := by decide +kernel
theorem subd6_14_156 : subd6_14 [-2, -1, -8] = true := by decide +kernel
theorem subd6_14_157 : subd6_14 [-2, -1, -7] = true := by decide +kernel
theorem subd6_14_158 : subd6_14 [-2, -1, -6] = true := by decide +kernel
theorem subd6_14_159 : subd6_14 [-2, -1, -5] = true := by decide +kernel
theorem sbd6_14_4 : ∀ q ∈ blkd6_14_4, subd6_14 q = true := by
  unfold blkd6_14_4
  exact List.forall_mem_cons.2 ⟨subd6_14_128, List.forall_mem_cons.2 ⟨subd6_14_129, List.forall_mem_cons.2 ⟨subd6_14_130, List.forall_mem_cons.2 ⟨subd6_14_131, List.forall_mem_cons.2 ⟨subd6_14_132, List.forall_mem_cons.2 ⟨subd6_14_133, List.forall_mem_cons.2 ⟨subd6_14_134, List.forall_mem_cons.2 ⟨subd6_14_135, List.forall_mem_cons.2 ⟨subd6_14_136, List.forall_mem_cons.2 ⟨subd6_14_137, List.forall_mem_cons.2 ⟨subd6_14_138, List.forall_mem_cons.2 ⟨subd6_14_139, List.forall_mem_cons.2 ⟨subd6_14_140, List.forall_mem_cons.2 ⟨subd6_14_141, List.forall_mem_cons.2 ⟨subd6_14_142, List.forall_mem_cons.2 ⟨subd6_14_143, List.forall_mem_cons.2 ⟨subd6_14_144, List.forall_mem_cons.2 ⟨subd6_14_145, List.forall_mem_cons.2 ⟨subd6_14_146, List.forall_mem_cons.2 ⟨subd6_14_147, List.forall_mem_cons.2 ⟨subd6_14_148, List.forall_mem_cons.2 ⟨subd6_14_149, List.forall_mem_cons.2 ⟨subd6_14_150, List.forall_mem_cons.2 ⟨subd6_14_151, List.forall_mem_cons.2 ⟨subd6_14_152, List.forall_mem_cons.2 ⟨subd6_14_153, List.forall_mem_cons.2 ⟨subd6_14_154, List.forall_mem_cons.2 ⟨subd6_14_155, List.forall_mem_cons.2 ⟨subd6_14_156, List.forall_mem_cons.2 ⟨subd6_14_157, List.forall_mem_cons.2 ⟨subd6_14_158, List.forall_mem_cons.2 ⟨subd6_14_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
