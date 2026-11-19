import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-4] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-3, -5] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-3, -4] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-3, -3] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-3, -2] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-3, -1] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-3, 0] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-3, 1] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-3, 2] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-2, -5] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-2, -4] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-2, -3] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [-2, -2] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [-2, -1] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [-2, 0] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [-2, 1] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [-2, 2] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [-2, 3] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [-1, -5] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [-1, -4] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [-1, -3] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [-1, -2] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [-1, -1] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [-1, 0] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [-1, 1] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [-1, 2] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [-1, 3] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [0, -5] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [0, -4] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [0, -3] = true := by decide +kernel
theorem subd14_1_30 : subd14_1 [0, -2] = true := by decide +kernel
theorem subd14_1_31 : subd14_1 [0, -1] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_cons.2 ⟨subd14_1_30, List.forall_mem_cons.2 ⟨subd14_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_32 : subd14_1 [0, 0] = true := by decide +kernel
theorem subd14_1_33 : subd14_1 [0, 1] = true := by decide +kernel
theorem subd14_1_34 : subd14_1 [0, 2] = true := by decide +kernel
theorem subd14_1_35 : subd14_1 [0, 3] = true := by decide +kernel
theorem subd14_1_36 : subd14_1 [0, 4] = true := by decide +kernel
theorem subd14_1_37 : subd14_1 [1, -4] = true := by decide +kernel
theorem subd14_1_38 : subd14_1 [1, -3] = true := by decide +kernel
theorem subd14_1_39 : subd14_1 [1, -2] = true := by decide +kernel
theorem subd14_1_40 : subd14_1 [1, -1] = true := by decide +kernel
theorem subd14_1_41 : subd14_1 [1, 0] = true := by decide +kernel
theorem subd14_1_42 : subd14_1 [1, 1] = true := by decide +kernel
theorem subd14_1_43 : subd14_1 [1, 2] = true := by decide +kernel
theorem subd14_1_44 : subd14_1 [1, 3] = true := by decide +kernel
theorem subd14_1_45 : subd14_1 [1, 4] = true := by decide +kernel
theorem subd14_1_46 : subd14_1 [2, -4] = true := by decide +kernel
theorem subd14_1_47 : subd14_1 [2, -3] = true := by decide +kernel
theorem subd14_1_48 : subd14_1 [2, -2] = true := by decide +kernel
theorem subd14_1_49 : subd14_1 [2, -1] = true := by decide +kernel
theorem subd14_1_50 : subd14_1 [2, 0] = true := by decide +kernel
theorem subd14_1_51 : subd14_1 [2, 1] = true := by decide +kernel
theorem subd14_1_52 : subd14_1 [2, 2] = true := by decide +kernel
theorem subd14_1_53 : subd14_1 [2, 3] = true := by decide +kernel
theorem subd14_1_54 : subd14_1 [2, 4] = true := by decide +kernel
theorem subd14_1_55 : subd14_1 [3, -3] = true := by decide +kernel
theorem subd14_1_56 : subd14_1 [3, -2] = true := by decide +kernel
theorem subd14_1_57 : subd14_1 [3, -1] = true := by decide +kernel
theorem subd14_1_58 : subd14_1 [3, 0] = true := by decide +kernel
theorem subd14_1_59 : subd14_1 [3, 1] = true := by decide +kernel
theorem subd14_1_60 : subd14_1 [3, 2] = true := by decide +kernel
theorem subd14_1_61 : subd14_1 [3, 3] = true := by decide +kernel
theorem subd14_1_62 : subd14_1 [3, 4] = true := by decide +kernel
theorem subd14_1_63 : subd14_1 [4] = true := by decide +kernel
theorem sbd14_1_1 : ∀ q ∈ blkd14_1_1, subd14_1 q = true := by
  unfold blkd14_1_1
  exact List.forall_mem_cons.2 ⟨subd14_1_32, List.forall_mem_cons.2 ⟨subd14_1_33, List.forall_mem_cons.2 ⟨subd14_1_34, List.forall_mem_cons.2 ⟨subd14_1_35, List.forall_mem_cons.2 ⟨subd14_1_36, List.forall_mem_cons.2 ⟨subd14_1_37, List.forall_mem_cons.2 ⟨subd14_1_38, List.forall_mem_cons.2 ⟨subd14_1_39, List.forall_mem_cons.2 ⟨subd14_1_40, List.forall_mem_cons.2 ⟨subd14_1_41, List.forall_mem_cons.2 ⟨subd14_1_42, List.forall_mem_cons.2 ⟨subd14_1_43, List.forall_mem_cons.2 ⟨subd14_1_44, List.forall_mem_cons.2 ⟨subd14_1_45, List.forall_mem_cons.2 ⟨subd14_1_46, List.forall_mem_cons.2 ⟨subd14_1_47, List.forall_mem_cons.2 ⟨subd14_1_48, List.forall_mem_cons.2 ⟨subd14_1_49, List.forall_mem_cons.2 ⟨subd14_1_50, List.forall_mem_cons.2 ⟨subd14_1_51, List.forall_mem_cons.2 ⟨subd14_1_52, List.forall_mem_cons.2 ⟨subd14_1_53, List.forall_mem_cons.2 ⟨subd14_1_54, List.forall_mem_cons.2 ⟨subd14_1_55, List.forall_mem_cons.2 ⟨subd14_1_56, List.forall_mem_cons.2 ⟨subd14_1_57, List.forall_mem_cons.2 ⟨subd14_1_58, List.forall_mem_cons.2 ⟨subd14_1_59, List.forall_mem_cons.2 ⟨subd14_1_60, List.forall_mem_cons.2 ⟨subd14_1_61, List.forall_mem_cons.2 ⟨subd14_1_62, List.forall_mem_cons.2 ⟨subd14_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-3, -4] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [-3, -3] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [-3, -2] = true := by decide +kernel
theorem subd15_0_3 : subd15_0 [-3, -1] = true := by decide +kernel
theorem subd15_0_4 : subd15_0 [-3, 0] = true := by decide +kernel
theorem subd15_0_5 : subd15_0 [-3, 1] = true := by decide +kernel
theorem subd15_0_6 : subd15_0 [-2, -5] = true := by decide +kernel
theorem subd15_0_7 : subd15_0 [-2, -4] = true := by decide +kernel
theorem subd15_0_8 : subd15_0 [-2, -3] = true := by decide +kernel
theorem subd15_0_9 : subd15_0 [-2, -2] = true := by decide +kernel
theorem subd15_0_10 : subd15_0 [-2, -1] = true := by decide +kernel
theorem subd15_0_11 : subd15_0 [-2, 0] = true := by decide +kernel
theorem subd15_0_12 : subd15_0 [-2, 1] = true := by decide +kernel
theorem subd15_0_13 : subd15_0 [-2, 2] = true := by decide +kernel
theorem subd15_0_14 : subd15_0 [-2, 3] = true := by decide +kernel
theorem subd15_0_15 : subd15_0 [-1, -5] = true := by decide +kernel
theorem subd15_0_16 : subd15_0 [-1, -4] = true := by decide +kernel
theorem subd15_0_17 : subd15_0 [-1, -3] = true := by decide +kernel
theorem subd15_0_18 : subd15_0 [-1, -2] = true := by decide +kernel
theorem subd15_0_19 : subd15_0 [-1, -1, -7] = true := by decide +kernel
theorem subd15_0_20 : subd15_0 [-1, -1, -6] = true := by decide +kernel
theorem subd15_0_21 : subd15_0 [-1, -1, -5] = true := by decide +kernel
theorem subd15_0_22 : subd15_0 [-1, -1, -4] = true := by decide +kernel
theorem subd15_0_23 : subd15_0 [-1, -1, -3] = true := by decide +kernel
theorem subd15_0_24 : subd15_0 [-1, -1, -2] = true := by decide +kernel
theorem subd15_0_25 : subd15_0 [-1, -1, -1] = true := by decide +kernel
theorem subd15_0_26 : subd15_0 [-1, -1, 0] = true := by decide +kernel
theorem subd15_0_27 : subd15_0 [-1, -1, 1] = true := by decide +kernel
theorem subd15_0_28 : subd15_0 [-1, -1, 2] = true := by decide +kernel
theorem subd15_0_29 : subd15_0 [-1, -1, 3] = true := by decide +kernel
theorem subd15_0_30 : subd15_0 [-1, -1, 4] = true := by decide +kernel
theorem subd15_0_31 : subd15_0 [-1, -1, 5] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_cons.2 ⟨subd15_0_3, List.forall_mem_cons.2 ⟨subd15_0_4, List.forall_mem_cons.2 ⟨subd15_0_5, List.forall_mem_cons.2 ⟨subd15_0_6, List.forall_mem_cons.2 ⟨subd15_0_7, List.forall_mem_cons.2 ⟨subd15_0_8, List.forall_mem_cons.2 ⟨subd15_0_9, List.forall_mem_cons.2 ⟨subd15_0_10, List.forall_mem_cons.2 ⟨subd15_0_11, List.forall_mem_cons.2 ⟨subd15_0_12, List.forall_mem_cons.2 ⟨subd15_0_13, List.forall_mem_cons.2 ⟨subd15_0_14, List.forall_mem_cons.2 ⟨subd15_0_15, List.forall_mem_cons.2 ⟨subd15_0_16, List.forall_mem_cons.2 ⟨subd15_0_17, List.forall_mem_cons.2 ⟨subd15_0_18, List.forall_mem_cons.2 ⟨subd15_0_19, List.forall_mem_cons.2 ⟨subd15_0_20, List.forall_mem_cons.2 ⟨subd15_0_21, List.forall_mem_cons.2 ⟨subd15_0_22, List.forall_mem_cons.2 ⟨subd15_0_23, List.forall_mem_cons.2 ⟨subd15_0_24, List.forall_mem_cons.2 ⟨subd15_0_25, List.forall_mem_cons.2 ⟨subd15_0_26, List.forall_mem_cons.2 ⟨subd15_0_27, List.forall_mem_cons.2 ⟨subd15_0_28, List.forall_mem_cons.2 ⟨subd15_0_29, List.forall_mem_cons.2 ⟨subd15_0_30, List.forall_mem_cons.2 ⟨subd15_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_32 : subd15_0 [-1, -1, 6] = true := by decide +kernel
theorem subd15_0_33 : subd15_0 [-1, 0, -7] = true := by decide +kernel
theorem subd15_0_34 : subd15_0 [-1, 0, -6] = true := by decide +kernel
theorem subd15_0_35 : subd15_0 [-1, 0, -5] = true := by decide +kernel
theorem subd15_0_36 : subd15_0 [-1, 0, -4] = true := by decide +kernel
theorem subd15_0_37 : subd15_0 [-1, 0, -3] = true := by decide +kernel
theorem subd15_0_38 : subd15_0 [-1, 0, -2] = true := by decide +kernel
theorem subd15_0_39 : subd15_0 [-1, 0, -1] = true := by decide +kernel
theorem subd15_0_40 : subd15_0 [-1, 0, 0] = true := by decide +kernel
theorem subd15_0_41 : subd15_0 [-1, 0, 1] = true := by decide +kernel
theorem subd15_0_42 : subd15_0 [-1, 0, 2] = true := by decide +kernel
theorem subd15_0_43 : subd15_0 [-1, 0, 3] = true := by decide +kernel
theorem subd15_0_44 : subd15_0 [-1, 0, 4] = true := by decide +kernel
theorem subd15_0_45 : subd15_0 [-1, 0, 5] = true := by decide +kernel
theorem subd15_0_46 : subd15_0 [-1, 0, 6] = true := by decide +kernel
theorem subd15_0_47 : subd15_0 [-1, 1, -6] = true := by decide +kernel
theorem subd15_0_48 : subd15_0 [-1, 1, -5] = true := by decide +kernel
theorem subd15_0_49 : subd15_0 [-1, 1, -4] = true := by decide +kernel
theorem subd15_0_50 : subd15_0 [-1, 1, -3] = true := by decide +kernel
theorem subd15_0_51 : subd15_0 [-1, 1, -2] = true := by decide +kernel
theorem subd15_0_52 : subd15_0 [-1, 1, -1] = true := by decide +kernel
theorem subd15_0_53 : subd15_0 [-1, 1, 0] = true := by decide +kernel
theorem subd15_0_54 : subd15_0 [-1, 1, 1] = true := by decide +kernel
theorem subd15_0_55 : subd15_0 [-1, 1, 2] = true := by decide +kernel
theorem subd15_0_56 : subd15_0 [-1, 1, 3] = true := by decide +kernel
theorem subd15_0_57 : subd15_0 [-1, 1, 4] = true := by decide +kernel
theorem subd15_0_58 : subd15_0 [-1, 1, 5] = true := by decide +kernel
theorem subd15_0_59 : subd15_0 [-1, 1, 6] = true := by decide +kernel
theorem subd15_0_60 : subd15_0 [-1, 2] = true := by decide +kernel
theorem subd15_0_61 : subd15_0 [-1, 3] = true := by decide +kernel
theorem subd15_0_62 : subd15_0 [0, -5] = true := by decide +kernel
theorem subd15_0_63 : subd15_0 [0, -4] = true := by decide +kernel
theorem sbd15_0_1 : ∀ q ∈ blkd15_0_1, subd15_0 q = true := by
  unfold blkd15_0_1
  exact List.forall_mem_cons.2 ⟨subd15_0_32, List.forall_mem_cons.2 ⟨subd15_0_33, List.forall_mem_cons.2 ⟨subd15_0_34, List.forall_mem_cons.2 ⟨subd15_0_35, List.forall_mem_cons.2 ⟨subd15_0_36, List.forall_mem_cons.2 ⟨subd15_0_37, List.forall_mem_cons.2 ⟨subd15_0_38, List.forall_mem_cons.2 ⟨subd15_0_39, List.forall_mem_cons.2 ⟨subd15_0_40, List.forall_mem_cons.2 ⟨subd15_0_41, List.forall_mem_cons.2 ⟨subd15_0_42, List.forall_mem_cons.2 ⟨subd15_0_43, List.forall_mem_cons.2 ⟨subd15_0_44, List.forall_mem_cons.2 ⟨subd15_0_45, List.forall_mem_cons.2 ⟨subd15_0_46, List.forall_mem_cons.2 ⟨subd15_0_47, List.forall_mem_cons.2 ⟨subd15_0_48, List.forall_mem_cons.2 ⟨subd15_0_49, List.forall_mem_cons.2 ⟨subd15_0_50, List.forall_mem_cons.2 ⟨subd15_0_51, List.forall_mem_cons.2 ⟨subd15_0_52, List.forall_mem_cons.2 ⟨subd15_0_53, List.forall_mem_cons.2 ⟨subd15_0_54, List.forall_mem_cons.2 ⟨subd15_0_55, List.forall_mem_cons.2 ⟨subd15_0_56, List.forall_mem_cons.2 ⟨subd15_0_57, List.forall_mem_cons.2 ⟨subd15_0_58, List.forall_mem_cons.2 ⟨subd15_0_59, List.forall_mem_cons.2 ⟨subd15_0_60, List.forall_mem_cons.2 ⟨subd15_0_61, List.forall_mem_cons.2 ⟨subd15_0_62, List.forall_mem_cons.2 ⟨subd15_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_64 : subd15_0 [0, -3] = true := by decide +kernel
theorem subd15_0_65 : subd15_0 [0, -2] = true := by decide +kernel
theorem subd15_0_66 : subd15_0 [0, -1, -7] = true := by decide +kernel
theorem subd15_0_67 : subd15_0 [0, -1, -6] = true := by decide +kernel
theorem subd15_0_68 : subd15_0 [0, -1, -5] = true := by decide +kernel
theorem subd15_0_69 : subd15_0 [0, -1, -4] = true := by decide +kernel
theorem subd15_0_70 : subd15_0 [0, -1, -3] = true := by decide +kernel
theorem subd15_0_71 : subd15_0 [0, -1, -2] = true := by decide +kernel
theorem subd15_0_72 : subd15_0 [0, -1, -1] = true := by decide +kernel
theorem subd15_0_73 : subd15_0 [0, -1, 0] = true := by decide +kernel
theorem subd15_0_74 : subd15_0 [0, -1, 1] = true := by decide +kernel
theorem subd15_0_75 : subd15_0 [0, -1, 2] = true := by decide +kernel
theorem subd15_0_76 : subd15_0 [0, -1, 3] = true := by decide +kernel
theorem subd15_0_77 : subd15_0 [0, -1, 4] = true := by decide +kernel
theorem subd15_0_78 : subd15_0 [0, -1, 5] = true := by decide +kernel
theorem subd15_0_79 : subd15_0 [0, -1, 6] = true := by decide +kernel
theorem subd15_0_80 : subd15_0 [0, 0, -7] = true := by decide +kernel
theorem subd15_0_81 : subd15_0 [0, 0, -6] = true := by decide +kernel
theorem subd15_0_82 : subd15_0 [0, 0, -5] = true := by decide +kernel
theorem subd15_0_83 : subd15_0 [0, 0, -4] = true := by decide +kernel
theorem subd15_0_84 : subd15_0 [0, 0, -3] = true := by decide +kernel
theorem subd15_0_85 : subd15_0 [0, 0, -2] = true := by decide +kernel
theorem subd15_0_86 : subd15_0 [0, 0, -1] = true := by decide +kernel
theorem subd15_0_87 : subd15_0 [0, 0, 0] = true := by decide +kernel
theorem subd15_0_88 : subd15_0 [0, 0, 1] = true := by decide +kernel
theorem subd15_0_89 : subd15_0 [0, 0, 2] = true := by decide +kernel
theorem subd15_0_90 : subd15_0 [0, 0, 3] = true := by decide +kernel
theorem subd15_0_91 : subd15_0 [0, 0, 4] = true := by decide +kernel
theorem subd15_0_92 : subd15_0 [0, 0, 5] = true := by decide +kernel
theorem subd15_0_93 : subd15_0 [0, 0, 6] = true := by decide +kernel
theorem subd15_0_94 : subd15_0 [0, 1, -7] = true := by decide +kernel
theorem subd15_0_95 : subd15_0 [0, 1, -6] = true := by decide +kernel
theorem sbd15_0_2 : ∀ q ∈ blkd15_0_2, subd15_0 q = true := by
  unfold blkd15_0_2
  exact List.forall_mem_cons.2 ⟨subd15_0_64, List.forall_mem_cons.2 ⟨subd15_0_65, List.forall_mem_cons.2 ⟨subd15_0_66, List.forall_mem_cons.2 ⟨subd15_0_67, List.forall_mem_cons.2 ⟨subd15_0_68, List.forall_mem_cons.2 ⟨subd15_0_69, List.forall_mem_cons.2 ⟨subd15_0_70, List.forall_mem_cons.2 ⟨subd15_0_71, List.forall_mem_cons.2 ⟨subd15_0_72, List.forall_mem_cons.2 ⟨subd15_0_73, List.forall_mem_cons.2 ⟨subd15_0_74, List.forall_mem_cons.2 ⟨subd15_0_75, List.forall_mem_cons.2 ⟨subd15_0_76, List.forall_mem_cons.2 ⟨subd15_0_77, List.forall_mem_cons.2 ⟨subd15_0_78, List.forall_mem_cons.2 ⟨subd15_0_79, List.forall_mem_cons.2 ⟨subd15_0_80, List.forall_mem_cons.2 ⟨subd15_0_81, List.forall_mem_cons.2 ⟨subd15_0_82, List.forall_mem_cons.2 ⟨subd15_0_83, List.forall_mem_cons.2 ⟨subd15_0_84, List.forall_mem_cons.2 ⟨subd15_0_85, List.forall_mem_cons.2 ⟨subd15_0_86, List.forall_mem_cons.2 ⟨subd15_0_87, List.forall_mem_cons.2 ⟨subd15_0_88, List.forall_mem_cons.2 ⟨subd15_0_89, List.forall_mem_cons.2 ⟨subd15_0_90, List.forall_mem_cons.2 ⟨subd15_0_91, List.forall_mem_cons.2 ⟨subd15_0_92, List.forall_mem_cons.2 ⟨subd15_0_93, List.forall_mem_cons.2 ⟨subd15_0_94, List.forall_mem_cons.2 ⟨subd15_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
