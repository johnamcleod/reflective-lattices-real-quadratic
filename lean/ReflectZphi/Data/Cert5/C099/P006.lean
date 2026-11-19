import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_7_32 : subd4_7 [1, -4] = true := by decide +kernel
theorem subd4_7_33 : subd4_7 [1, -3] = true := by decide +kernel
theorem subd4_7_34 : subd4_7 [1, -2] = true := by decide +kernel
theorem subd4_7_35 : subd4_7 [1, -1] = true := by decide +kernel
theorem subd4_7_36 : subd4_7 [1, 0] = true := by decide +kernel
theorem subd4_7_37 : subd4_7 [1, 1] = true := by decide +kernel
theorem subd4_7_38 : subd4_7 [1, 2] = true := by decide +kernel
theorem subd4_7_39 : subd4_7 [1, 3] = true := by decide +kernel
theorem subd4_7_40 : subd4_7 [1, 4] = true := by decide +kernel
theorem subd4_7_41 : subd4_7 [2, -4] = true := by decide +kernel
theorem subd4_7_42 : subd4_7 [2, -3] = true := by decide +kernel
theorem subd4_7_43 : subd4_7 [2, -2] = true := by decide +kernel
theorem subd4_7_44 : subd4_7 [2, -1] = true := by decide +kernel
theorem subd4_7_45 : subd4_7 [2, 0] = true := by decide +kernel
theorem subd4_7_46 : subd4_7 [2, 1] = true := by decide +kernel
theorem subd4_7_47 : subd4_7 [2, 2] = true := by decide +kernel
theorem subd4_7_48 : subd4_7 [2, 3] = true := by decide +kernel
theorem subd4_7_49 : subd4_7 [2, 4] = true := by decide +kernel
theorem subd4_7_50 : subd4_7 [3] = true := by decide +kernel
theorem subd4_7_51 : subd4_7 [4] = true := by decide +kernel
theorem sbd4_7_1 : ∀ q ∈ blkd4_7_1, subd4_7 q = true := by
  unfold blkd4_7_1
  exact List.forall_mem_cons.2 ⟨subd4_7_32, List.forall_mem_cons.2 ⟨subd4_7_33, List.forall_mem_cons.2 ⟨subd4_7_34, List.forall_mem_cons.2 ⟨subd4_7_35, List.forall_mem_cons.2 ⟨subd4_7_36, List.forall_mem_cons.2 ⟨subd4_7_37, List.forall_mem_cons.2 ⟨subd4_7_38, List.forall_mem_cons.2 ⟨subd4_7_39, List.forall_mem_cons.2 ⟨subd4_7_40, List.forall_mem_cons.2 ⟨subd4_7_41, List.forall_mem_cons.2 ⟨subd4_7_42, List.forall_mem_cons.2 ⟨subd4_7_43, List.forall_mem_cons.2 ⟨subd4_7_44, List.forall_mem_cons.2 ⟨subd4_7_45, List.forall_mem_cons.2 ⟨subd4_7_46, List.forall_mem_cons.2 ⟨subd4_7_47, List.forall_mem_cons.2 ⟨subd4_7_48, List.forall_mem_cons.2 ⟨subd4_7_49, List.forall_mem_cons.2 ⟨subd4_7_50, List.forall_mem_cons.2 ⟨subd4_7_51, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-2, -3] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-2, -2] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-2, -1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-2, 0] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-2, 1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-2, 2] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-2, 3] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_28 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_29 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_30 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_31 : subd5_0 [1, 3] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_cons.2 ⟨subd5_0_28, List.forall_mem_cons.2 ⟨subd5_0_29, List.forall_mem_cons.2 ⟨subd5_0_30, List.forall_mem_cons.2 ⟨subd5_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_32 : subd5_0 [2, -4] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [2, -2] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [2, -1] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [2, 0] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [2, 1] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [2, 2] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [3] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-1, 0, -8] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-1, 0, -7] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-1, 0, -6] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-1, 0, -5] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-1, 0, -4] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-1, 0, -3] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-1, 0, -2] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-1, 0, -1] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-1, 0, 0] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-1, 0, 1] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-1, 0, 2] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-1, 0, 3] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [-1, 0, 4] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [-1, 0, 5] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [-1, 0, 6] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [-1, 1, -8] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [-1, 1, -7] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [-1, 1, -6] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [-1, 1, -5] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [-1, 1, -4] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [-1, 1, -3] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [-1, 1, -2] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [-1, 1, -1] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [-1, 1, 0] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [-1, 1, 1] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [-1, 1, 2] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [-1, 1, 3] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [-1, 1, 4] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [-1, 1, 5] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [-1, 1, 6] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [0, -1, -8] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [0, -1, -7] = true := by decide +kernel
theorem subd5_1_38 : subd5_1 [0, -1, -6] = true := by decide +kernel
theorem subd5_1_39 : subd5_1 [0, -1, -5] = true := by decide +kernel
theorem subd5_1_40 : subd5_1 [0, -1, -4] = true := by decide +kernel
theorem subd5_1_41 : subd5_1 [0, -1, -3] = true := by decide +kernel
theorem subd5_1_42 : subd5_1 [0, -1, -2] = true := by decide +kernel
theorem subd5_1_43 : subd5_1 [0, -1, -1] = true := by decide +kernel
theorem subd5_1_44 : subd5_1 [0, -1, 0] = true := by decide +kernel
theorem subd5_1_45 : subd5_1 [0, -1, 1] = true := by decide +kernel
theorem subd5_1_46 : subd5_1 [0, -1, 2] = true := by decide +kernel
theorem subd5_1_47 : subd5_1 [0, -1, 3] = true := by decide +kernel
theorem subd5_1_48 : subd5_1 [0, -1, 4] = true := by decide +kernel
theorem subd5_1_49 : subd5_1 [0, -1, 5] = true := by decide +kernel
theorem subd5_1_50 : subd5_1 [0, -1, 6] = true := by decide +kernel
theorem subd5_1_51 : subd5_1 [0, -1, 7] = true := by decide +kernel
theorem subd5_1_52 : subd5_1 [0, 0, -9] = true := by decide +kernel
theorem subd5_1_53 : subd5_1 [0, 0, -8] = true := by decide +kernel
theorem subd5_1_54 : subd5_1 [0, 0, -7] = true := by decide +kernel
theorem subd5_1_55 : subd5_1 [0, 0, -6] = true := by decide +kernel
theorem subd5_1_56 : subd5_1 [0, 0, -5] = true := by decide +kernel
theorem subd5_1_57 : subd5_1 [0, 0, -4] = true := by decide +kernel
theorem subd5_1_58 : subd5_1 [0, 0, -3] = true := by decide +kernel
theorem subd5_1_59 : subd5_1 [0, 0, -2] = true := by decide +kernel
theorem subd5_1_60 : subd5_1 [0, 0, -1] = true := by decide +kernel
theorem subd5_1_61 : subd5_1 [0, 0, 0] = true := by decide +kernel
theorem subd5_1_62 : subd5_1 [0, 0, 1] = true := by decide +kernel
theorem subd5_1_63 : subd5_1 [0, 0, 2] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_cons.2 ⟨subd5_1_38, List.forall_mem_cons.2 ⟨subd5_1_39, List.forall_mem_cons.2 ⟨subd5_1_40, List.forall_mem_cons.2 ⟨subd5_1_41, List.forall_mem_cons.2 ⟨subd5_1_42, List.forall_mem_cons.2 ⟨subd5_1_43, List.forall_mem_cons.2 ⟨subd5_1_44, List.forall_mem_cons.2 ⟨subd5_1_45, List.forall_mem_cons.2 ⟨subd5_1_46, List.forall_mem_cons.2 ⟨subd5_1_47, List.forall_mem_cons.2 ⟨subd5_1_48, List.forall_mem_cons.2 ⟨subd5_1_49, List.forall_mem_cons.2 ⟨subd5_1_50, List.forall_mem_cons.2 ⟨subd5_1_51, List.forall_mem_cons.2 ⟨subd5_1_52, List.forall_mem_cons.2 ⟨subd5_1_53, List.forall_mem_cons.2 ⟨subd5_1_54, List.forall_mem_cons.2 ⟨subd5_1_55, List.forall_mem_cons.2 ⟨subd5_1_56, List.forall_mem_cons.2 ⟨subd5_1_57, List.forall_mem_cons.2 ⟨subd5_1_58, List.forall_mem_cons.2 ⟨subd5_1_59, List.forall_mem_cons.2 ⟨subd5_1_60, List.forall_mem_cons.2 ⟨subd5_1_61, List.forall_mem_cons.2 ⟨subd5_1_62, List.forall_mem_cons.2 ⟨subd5_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_64 : subd5_1 [0, 0, 3] = true := by decide +kernel
theorem subd5_1_65 : subd5_1 [0, 0, 4] = true := by decide +kernel
theorem subd5_1_66 : subd5_1 [0, 0, 5] = true := by decide +kernel
theorem subd5_1_67 : subd5_1 [0, 0, 6] = true := by decide +kernel
theorem subd5_1_68 : subd5_1 [0, 0, 7] = true := by decide +kernel
theorem subd5_1_69 : subd5_1 [0, 0, 8] = true := by decide +kernel
theorem subd5_1_70 : subd5_1 [0, 1, -8] = true := by decide +kernel
theorem subd5_1_71 : subd5_1 [0, 1, -7] = true := by decide +kernel
theorem subd5_1_72 : subd5_1 [0, 1, -6] = true := by decide +kernel
theorem subd5_1_73 : subd5_1 [0, 1, -5] = true := by decide +kernel
theorem subd5_1_74 : subd5_1 [0, 1, -4] = true := by decide +kernel
theorem subd5_1_75 : subd5_1 [0, 1, -3] = true := by decide +kernel
theorem subd5_1_76 : subd5_1 [0, 1, -2] = true := by decide +kernel
theorem subd5_1_77 : subd5_1 [0, 1, -1] = true := by decide +kernel
theorem subd5_1_78 : subd5_1 [0, 1, 0] = true := by decide +kernel
theorem subd5_1_79 : subd5_1 [0, 1, 1] = true := by decide +kernel
theorem subd5_1_80 : subd5_1 [0, 1, 2] = true := by decide +kernel
theorem subd5_1_81 : subd5_1 [0, 1, 3] = true := by decide +kernel
theorem subd5_1_82 : subd5_1 [0, 1, 4] = true := by decide +kernel
theorem subd5_1_83 : subd5_1 [0, 1, 5] = true := by decide +kernel
theorem subd5_1_84 : subd5_1 [0, 1, 6] = true := by decide +kernel
theorem subd5_1_85 : subd5_1 [0, 1, 7] = true := by decide +kernel
theorem subd5_1_86 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_87 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_88 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_89 : subd5_1 [1, -1, -7] = true := by decide +kernel
theorem subd5_1_90 : subd5_1 [1, -1, -6] = true := by decide +kernel
theorem subd5_1_91 : subd5_1 [1, -1, -5] = true := by decide +kernel
theorem subd5_1_92 : subd5_1 [1, -1, -4] = true := by decide +kernel
theorem subd5_1_93 : subd5_1 [1, -1, -3] = true := by decide +kernel
theorem subd5_1_94 : subd5_1 [1, -1, -2] = true := by decide +kernel
theorem subd5_1_95 : subd5_1 [1, -1, -1] = true := by decide +kernel
theorem sbd5_1_2 : ∀ q ∈ blkd5_1_2, subd5_1 q = true := by
  unfold blkd5_1_2
  exact List.forall_mem_cons.2 ⟨subd5_1_64, List.forall_mem_cons.2 ⟨subd5_1_65, List.forall_mem_cons.2 ⟨subd5_1_66, List.forall_mem_cons.2 ⟨subd5_1_67, List.forall_mem_cons.2 ⟨subd5_1_68, List.forall_mem_cons.2 ⟨subd5_1_69, List.forall_mem_cons.2 ⟨subd5_1_70, List.forall_mem_cons.2 ⟨subd5_1_71, List.forall_mem_cons.2 ⟨subd5_1_72, List.forall_mem_cons.2 ⟨subd5_1_73, List.forall_mem_cons.2 ⟨subd5_1_74, List.forall_mem_cons.2 ⟨subd5_1_75, List.forall_mem_cons.2 ⟨subd5_1_76, List.forall_mem_cons.2 ⟨subd5_1_77, List.forall_mem_cons.2 ⟨subd5_1_78, List.forall_mem_cons.2 ⟨subd5_1_79, List.forall_mem_cons.2 ⟨subd5_1_80, List.forall_mem_cons.2 ⟨subd5_1_81, List.forall_mem_cons.2 ⟨subd5_1_82, List.forall_mem_cons.2 ⟨subd5_1_83, List.forall_mem_cons.2 ⟨subd5_1_84, List.forall_mem_cons.2 ⟨subd5_1_85, List.forall_mem_cons.2 ⟨subd5_1_86, List.forall_mem_cons.2 ⟨subd5_1_87, List.forall_mem_cons.2 ⟨subd5_1_88, List.forall_mem_cons.2 ⟨subd5_1_89, List.forall_mem_cons.2 ⟨subd5_1_90, List.forall_mem_cons.2 ⟨subd5_1_91, List.forall_mem_cons.2 ⟨subd5_1_92, List.forall_mem_cons.2 ⟨subd5_1_93, List.forall_mem_cons.2 ⟨subd5_1_94, List.forall_mem_cons.2 ⟨subd5_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_96 : subd5_1 [1, -1, 0] = true := by decide +kernel
theorem subd5_1_97 : subd5_1 [1, -1, 1] = true := by decide +kernel
theorem subd5_1_98 : subd5_1 [1, -1, 2] = true := by decide +kernel
theorem subd5_1_99 : subd5_1 [1, -1, 3] = true := by decide +kernel
theorem subd5_1_100 : subd5_1 [1, -1, 4] = true := by decide +kernel
theorem subd5_1_101 : subd5_1 [1, -1, 5] = true := by decide +kernel
theorem subd5_1_102 : subd5_1 [1, -1, 6] = true := by decide +kernel
theorem subd5_1_103 : subd5_1 [1, -1, 7] = true := by decide +kernel
theorem subd5_1_104 : subd5_1 [1, 0, -7] = true := by decide +kernel
theorem subd5_1_105 : subd5_1 [1, 0, -6] = true := by decide +kernel
theorem subd5_1_106 : subd5_1 [1, 0, -5] = true := by decide +kernel
theorem subd5_1_107 : subd5_1 [1, 0, -4] = true := by decide +kernel
theorem subd5_1_108 : subd5_1 [1, 0, -3] = true := by decide +kernel
theorem subd5_1_109 : subd5_1 [1, 0, -2] = true := by decide +kernel
theorem subd5_1_110 : subd5_1 [1, 0, -1] = true := by decide +kernel
theorem subd5_1_111 : subd5_1 [1, 0, 0] = true := by decide +kernel
theorem subd5_1_112 : subd5_1 [1, 0, 1] = true := by decide +kernel
theorem subd5_1_113 : subd5_1 [1, 0, 2] = true := by decide +kernel
theorem subd5_1_114 : subd5_1 [1, 0, 3] = true := by decide +kernel
theorem subd5_1_115 : subd5_1 [1, 0, 4] = true := by decide +kernel
theorem subd5_1_116 : subd5_1 [1, 0, 5] = true := by decide +kernel
theorem subd5_1_117 : subd5_1 [1, 0, 6] = true := by decide +kernel
theorem subd5_1_118 : subd5_1 [1, 0, 7] = true := by decide +kernel
theorem subd5_1_119 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_120 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_3 : ∀ q ∈ blkd5_1_3, subd5_1 q = true := by
  unfold blkd5_1_3
  exact List.forall_mem_cons.2 ⟨subd5_1_96, List.forall_mem_cons.2 ⟨subd5_1_97, List.forall_mem_cons.2 ⟨subd5_1_98, List.forall_mem_cons.2 ⟨subd5_1_99, List.forall_mem_cons.2 ⟨subd5_1_100, List.forall_mem_cons.2 ⟨subd5_1_101, List.forall_mem_cons.2 ⟨subd5_1_102, List.forall_mem_cons.2 ⟨subd5_1_103, List.forall_mem_cons.2 ⟨subd5_1_104, List.forall_mem_cons.2 ⟨subd5_1_105, List.forall_mem_cons.2 ⟨subd5_1_106, List.forall_mem_cons.2 ⟨subd5_1_107, List.forall_mem_cons.2 ⟨subd5_1_108, List.forall_mem_cons.2 ⟨subd5_1_109, List.forall_mem_cons.2 ⟨subd5_1_110, List.forall_mem_cons.2 ⟨subd5_1_111, List.forall_mem_cons.2 ⟨subd5_1_112, List.forall_mem_cons.2 ⟨subd5_1_113, List.forall_mem_cons.2 ⟨subd5_1_114, List.forall_mem_cons.2 ⟨subd5_1_115, List.forall_mem_cons.2 ⟨subd5_1_116, List.forall_mem_cons.2 ⟨subd5_1_117, List.forall_mem_cons.2 ⟨subd5_1_118, List.forall_mem_cons.2 ⟨subd5_1_119, List.forall_mem_cons.2 ⟨subd5_1_120, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C099
