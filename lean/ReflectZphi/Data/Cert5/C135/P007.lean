import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_3_32 : subd5_3 [-1, 4] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [-1, 5] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [0, -6] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [0, -5] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_40 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_41 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_42 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_43 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_44 : subd5_3 [0, 4] = true := by decide +kernel
theorem subd5_3_45 : subd5_3 [0, 5] = true := by decide +kernel
theorem subd5_3_46 : subd5_3 [1, -6] = true := by decide +kernel
theorem subd5_3_47 : subd5_3 [1, -5] = true := by decide +kernel
theorem subd5_3_48 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_49 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_50 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_51 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_52 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_53 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_54 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_55 : subd5_3 [1, 3] = true := by decide +kernel
theorem subd5_3_56 : subd5_3 [1, 4] = true := by decide +kernel
theorem subd5_3_57 : subd5_3 [1, 5] = true := by decide +kernel
theorem subd5_3_58 : subd5_3 [2, -5] = true := by decide +kernel
theorem subd5_3_59 : subd5_3 [2, -4] = true := by decide +kernel
theorem subd5_3_60 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_61 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_62 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_63 : subd5_3 [2, 0] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_cons.2 ⟨subd5_3_40, List.forall_mem_cons.2 ⟨subd5_3_41, List.forall_mem_cons.2 ⟨subd5_3_42, List.forall_mem_cons.2 ⟨subd5_3_43, List.forall_mem_cons.2 ⟨subd5_3_44, List.forall_mem_cons.2 ⟨subd5_3_45, List.forall_mem_cons.2 ⟨subd5_3_46, List.forall_mem_cons.2 ⟨subd5_3_47, List.forall_mem_cons.2 ⟨subd5_3_48, List.forall_mem_cons.2 ⟨subd5_3_49, List.forall_mem_cons.2 ⟨subd5_3_50, List.forall_mem_cons.2 ⟨subd5_3_51, List.forall_mem_cons.2 ⟨subd5_3_52, List.forall_mem_cons.2 ⟨subd5_3_53, List.forall_mem_cons.2 ⟨subd5_3_54, List.forall_mem_cons.2 ⟨subd5_3_55, List.forall_mem_cons.2 ⟨subd5_3_56, List.forall_mem_cons.2 ⟨subd5_3_57, List.forall_mem_cons.2 ⟨subd5_3_58, List.forall_mem_cons.2 ⟨subd5_3_59, List.forall_mem_cons.2 ⟨subd5_3_60, List.forall_mem_cons.2 ⟨subd5_3_61, List.forall_mem_cons.2 ⟨subd5_3_62, List.forall_mem_cons.2 ⟨subd5_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_64 : subd5_3 [2, 1] = true := by decide +kernel
theorem subd5_3_65 : subd5_3 [2, 2] = true := by decide +kernel
theorem subd5_3_66 : subd5_3 [2, 3] = true := by decide +kernel
theorem subd5_3_67 : subd5_3 [2, 4] = true := by decide +kernel
theorem subd5_3_68 : subd5_3 [2, 5] = true := by decide +kernel
theorem subd5_3_69 : subd5_3 [3, -4] = true := by decide +kernel
theorem subd5_3_70 : subd5_3 [3, -3] = true := by decide +kernel
theorem subd5_3_71 : subd5_3 [3, -2] = true := by decide +kernel
theorem subd5_3_72 : subd5_3 [3, -1] = true := by decide +kernel
theorem subd5_3_73 : subd5_3 [3, 0] = true := by decide +kernel
theorem subd5_3_74 : subd5_3 [3, 1] = true := by decide +kernel
theorem subd5_3_75 : subd5_3 [3, 2] = true := by decide +kernel
theorem subd5_3_76 : subd5_3 [3, 3] = true := by decide +kernel
theorem subd5_3_77 : subd5_3 [3, 4] = true := by decide +kernel
theorem subd5_3_78 : subd5_3 [3, 5] = true := by decide +kernel
theorem subd5_3_79 : subd5_3 [4] = true := by decide +kernel
theorem sbd5_3_2 : ∀ q ∈ blkd5_3_2, subd5_3 q = true := by
  unfold blkd5_3_2
  exact List.forall_mem_cons.2 ⟨subd5_3_64, List.forall_mem_cons.2 ⟨subd5_3_65, List.forall_mem_cons.2 ⟨subd5_3_66, List.forall_mem_cons.2 ⟨subd5_3_67, List.forall_mem_cons.2 ⟨subd5_3_68, List.forall_mem_cons.2 ⟨subd5_3_69, List.forall_mem_cons.2 ⟨subd5_3_70, List.forall_mem_cons.2 ⟨subd5_3_71, List.forall_mem_cons.2 ⟨subd5_3_72, List.forall_mem_cons.2 ⟨subd5_3_73, List.forall_mem_cons.2 ⟨subd5_3_74, List.forall_mem_cons.2 ⟨subd5_3_75, List.forall_mem_cons.2 ⟨subd5_3_76, List.forall_mem_cons.2 ⟨subd5_3_77, List.forall_mem_cons.2 ⟨subd5_3_78, List.forall_mem_cons.2 ⟨subd5_3_79, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-4] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-3, -4] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-3, -3] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-3, -2] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-3, -1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-3, 0] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [-3, 1] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [-3, 2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [-3, 3] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [-2, -4] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [-2, -3] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [-2, -2] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [-2, -1] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [-2, 0] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [-2, 1] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [-2, 2] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [-2, 3] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [-2, 4] = true := by decide +kernel
theorem subd5_4_18 : subd5_4 [-1, -5] = true := by decide +kernel
theorem subd5_4_19 : subd5_4 [-1, -4] = true := by decide +kernel
theorem subd5_4_20 : subd5_4 [-1, -3] = true := by decide +kernel
theorem subd5_4_21 : subd5_4 [-1, -2] = true := by decide +kernel
theorem subd5_4_22 : subd5_4 [-1, -1] = true := by decide +kernel
theorem subd5_4_23 : subd5_4 [-1, 0] = true := by decide +kernel
theorem subd5_4_24 : subd5_4 [-1, 1] = true := by decide +kernel
theorem subd5_4_25 : subd5_4 [-1, 2] = true := by decide +kernel
theorem subd5_4_26 : subd5_4 [-1, 3] = true := by decide +kernel
theorem subd5_4_27 : subd5_4 [-1, 4] = true := by decide +kernel
theorem subd5_4_28 : subd5_4 [0, -5] = true := by decide +kernel
theorem subd5_4_29 : subd5_4 [0, -4] = true := by decide +kernel
theorem subd5_4_30 : subd5_4 [0, -3] = true := by decide +kernel
theorem subd5_4_31 : subd5_4 [0, -2] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_cons.2 ⟨subd5_4_18, List.forall_mem_cons.2 ⟨subd5_4_19, List.forall_mem_cons.2 ⟨subd5_4_20, List.forall_mem_cons.2 ⟨subd5_4_21, List.forall_mem_cons.2 ⟨subd5_4_22, List.forall_mem_cons.2 ⟨subd5_4_23, List.forall_mem_cons.2 ⟨subd5_4_24, List.forall_mem_cons.2 ⟨subd5_4_25, List.forall_mem_cons.2 ⟨subd5_4_26, List.forall_mem_cons.2 ⟨subd5_4_27, List.forall_mem_cons.2 ⟨subd5_4_28, List.forall_mem_cons.2 ⟨subd5_4_29, List.forall_mem_cons.2 ⟨subd5_4_30, List.forall_mem_cons.2 ⟨subd5_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_32 : subd5_4 [0, -1] = true := by decide +kernel
theorem subd5_4_33 : subd5_4 [0, 0] = true := by decide +kernel
theorem subd5_4_34 : subd5_4 [0, 1] = true := by decide +kernel
theorem subd5_4_35 : subd5_4 [0, 2] = true := by decide +kernel
theorem subd5_4_36 : subd5_4 [0, 3] = true := by decide +kernel
theorem subd5_4_37 : subd5_4 [0, 4] = true := by decide +kernel
theorem subd5_4_38 : subd5_4 [1, -5] = true := by decide +kernel
theorem subd5_4_39 : subd5_4 [1, -4] = true := by decide +kernel
theorem subd5_4_40 : subd5_4 [1, -3] = true := by decide +kernel
theorem subd5_4_41 : subd5_4 [1, -2] = true := by decide +kernel
theorem subd5_4_42 : subd5_4 [1, -1] = true := by decide +kernel
theorem subd5_4_43 : subd5_4 [1, 0] = true := by decide +kernel
theorem subd5_4_44 : subd5_4 [1, 1] = true := by decide +kernel
theorem subd5_4_45 : subd5_4 [1, 2] = true := by decide +kernel
theorem subd5_4_46 : subd5_4 [1, 3] = true := by decide +kernel
theorem subd5_4_47 : subd5_4 [1, 4] = true := by decide +kernel
theorem subd5_4_48 : subd5_4 [2, -5] = true := by decide +kernel
theorem subd5_4_49 : subd5_4 [2, -4] = true := by decide +kernel
theorem subd5_4_50 : subd5_4 [2, -3] = true := by decide +kernel
theorem subd5_4_51 : subd5_4 [2, -2] = true := by decide +kernel
theorem subd5_4_52 : subd5_4 [2, -1] = true := by decide +kernel
theorem subd5_4_53 : subd5_4 [2, 0] = true := by decide +kernel
theorem subd5_4_54 : subd5_4 [2, 1] = true := by decide +kernel
theorem subd5_4_55 : subd5_4 [2, 2] = true := by decide +kernel
theorem subd5_4_56 : subd5_4 [2, 3] = true := by decide +kernel
theorem subd5_4_57 : subd5_4 [3, -4] = true := by decide +kernel
theorem subd5_4_58 : subd5_4 [3, -3] = true := by decide +kernel
theorem subd5_4_59 : subd5_4 [3, -2] = true := by decide +kernel
theorem subd5_4_60 : subd5_4 [3, -1] = true := by decide +kernel
theorem subd5_4_61 : subd5_4 [3, 0] = true := by decide +kernel
theorem subd5_4_62 : subd5_4 [3, 1] = true := by decide +kernel
theorem subd5_4_63 : subd5_4 [3, 2] = true := by decide +kernel
theorem sbd5_4_1 : ∀ q ∈ blkd5_4_1, subd5_4 q = true := by
  unfold blkd5_4_1
  exact List.forall_mem_cons.2 ⟨subd5_4_32, List.forall_mem_cons.2 ⟨subd5_4_33, List.forall_mem_cons.2 ⟨subd5_4_34, List.forall_mem_cons.2 ⟨subd5_4_35, List.forall_mem_cons.2 ⟨subd5_4_36, List.forall_mem_cons.2 ⟨subd5_4_37, List.forall_mem_cons.2 ⟨subd5_4_38, List.forall_mem_cons.2 ⟨subd5_4_39, List.forall_mem_cons.2 ⟨subd5_4_40, List.forall_mem_cons.2 ⟨subd5_4_41, List.forall_mem_cons.2 ⟨subd5_4_42, List.forall_mem_cons.2 ⟨subd5_4_43, List.forall_mem_cons.2 ⟨subd5_4_44, List.forall_mem_cons.2 ⟨subd5_4_45, List.forall_mem_cons.2 ⟨subd5_4_46, List.forall_mem_cons.2 ⟨subd5_4_47, List.forall_mem_cons.2 ⟨subd5_4_48, List.forall_mem_cons.2 ⟨subd5_4_49, List.forall_mem_cons.2 ⟨subd5_4_50, List.forall_mem_cons.2 ⟨subd5_4_51, List.forall_mem_cons.2 ⟨subd5_4_52, List.forall_mem_cons.2 ⟨subd5_4_53, List.forall_mem_cons.2 ⟨subd5_4_54, List.forall_mem_cons.2 ⟨subd5_4_55, List.forall_mem_cons.2 ⟨subd5_4_56, List.forall_mem_cons.2 ⟨subd5_4_57, List.forall_mem_cons.2 ⟨subd5_4_58, List.forall_mem_cons.2 ⟨subd5_4_59, List.forall_mem_cons.2 ⟨subd5_4_60, List.forall_mem_cons.2 ⟨subd5_4_61, List.forall_mem_cons.2 ⟨subd5_4_62, List.forall_mem_cons.2 ⟨subd5_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_64 : subd5_4 [3, 3] = true := by decide +kernel
theorem subd5_4_65 : subd5_4 [4] = true := by decide +kernel
theorem sbd5_4_2 : ∀ q ∈ blkd5_4_2, subd5_4 q = true := by
  unfold blkd5_4_2
  exact List.forall_mem_cons.2 ⟨subd5_4_64, List.forall_mem_cons.2 ⟨subd5_4_65, List.forall_mem_nil _⟩⟩
theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [-2] = true := by decide +kernel
theorem subd5_5_1 : subd5_5 [-1, -3] = true := by decide +kernel
theorem subd5_5_2 : subd5_5 [-1, -2] = true := by decide +kernel
theorem subd5_5_3 : subd5_5 [-1, -1] = true := by decide +kernel
theorem subd5_5_4 : subd5_5 [-1, 0] = true := by decide +kernel
theorem subd5_5_5 : subd5_5 [-1, 1] = true := by decide +kernel
theorem subd5_5_6 : subd5_5 [0, -3] = true := by decide +kernel
theorem subd5_5_7 : subd5_5 [0, -2] = true := by decide +kernel
theorem subd5_5_8 : subd5_5 [0, -1] = true := by decide +kernel
theorem subd5_5_9 : subd5_5 [0, 0, -7] = true := by decide +kernel
theorem subd5_5_10 : subd5_5 [0, 0, -6] = true := by decide +kernel
theorem subd5_5_11 : subd5_5 [0, 0, -5] = true := by decide +kernel
theorem subd5_5_12 : subd5_5 [0, 0, -4] = true := by decide +kernel
theorem subd5_5_13 : subd5_5 [0, 0, -3] = true := by decide +kernel
theorem subd5_5_14 : subd5_5 [0, 0, -2] = true := by decide +kernel
theorem subd5_5_15 : subd5_5 [0, 0, -1] = true := by decide +kernel
theorem subd5_5_16 : subd5_5 [0, 0, 0] = true := by decide +kernel
theorem subd5_5_17 : subd5_5 [0, 0, 1] = true := by decide +kernel
theorem subd5_5_18 : subd5_5 [0, 0, 2] = true := by decide +kernel
theorem subd5_5_19 : subd5_5 [0, 0, 3] = true := by decide +kernel
theorem subd5_5_20 : subd5_5 [0, 0, 4] = true := by decide +kernel
theorem subd5_5_21 : subd5_5 [0, 0, 5] = true := by decide +kernel
theorem subd5_5_22 : subd5_5 [0, 0, 6] = true := by decide +kernel
theorem subd5_5_23 : subd5_5 [0, 1] = true := by decide +kernel
theorem subd5_5_24 : subd5_5 [0, 2] = true := by decide +kernel
theorem subd5_5_25 : subd5_5 [1, -2] = true := by decide +kernel
theorem subd5_5_26 : subd5_5 [1, -1] = true := by decide +kernel
theorem subd5_5_27 : subd5_5 [1, 0] = true := by decide +kernel
theorem subd5_5_28 : subd5_5 [1, 1] = true := by decide +kernel
theorem subd5_5_29 : subd5_5 [1, 2] = true := by decide +kernel
theorem subd5_5_30 : subd5_5 [2] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_cons.2 ⟨subd5_5_1, List.forall_mem_cons.2 ⟨subd5_5_2, List.forall_mem_cons.2 ⟨subd5_5_3, List.forall_mem_cons.2 ⟨subd5_5_4, List.forall_mem_cons.2 ⟨subd5_5_5, List.forall_mem_cons.2 ⟨subd5_5_6, List.forall_mem_cons.2 ⟨subd5_5_7, List.forall_mem_cons.2 ⟨subd5_5_8, List.forall_mem_cons.2 ⟨subd5_5_9, List.forall_mem_cons.2 ⟨subd5_5_10, List.forall_mem_cons.2 ⟨subd5_5_11, List.forall_mem_cons.2 ⟨subd5_5_12, List.forall_mem_cons.2 ⟨subd5_5_13, List.forall_mem_cons.2 ⟨subd5_5_14, List.forall_mem_cons.2 ⟨subd5_5_15, List.forall_mem_cons.2 ⟨subd5_5_16, List.forall_mem_cons.2 ⟨subd5_5_17, List.forall_mem_cons.2 ⟨subd5_5_18, List.forall_mem_cons.2 ⟨subd5_5_19, List.forall_mem_cons.2 ⟨subd5_5_20, List.forall_mem_cons.2 ⟨subd5_5_21, List.forall_mem_cons.2 ⟨subd5_5_22, List.forall_mem_cons.2 ⟨subd5_5_23, List.forall_mem_cons.2 ⟨subd5_5_24, List.forall_mem_cons.2 ⟨subd5_5_25, List.forall_mem_cons.2 ⟨subd5_5_26, List.forall_mem_cons.2 ⟨subd5_5_27, List.forall_mem_cons.2 ⟨subd5_5_28, List.forall_mem_cons.2 ⟨subd5_5_29, List.forall_mem_cons.2 ⟨subd5_5_30, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
