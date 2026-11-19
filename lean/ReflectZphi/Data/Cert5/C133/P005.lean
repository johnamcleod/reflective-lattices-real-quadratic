import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-4] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-3, -2] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-3, -1] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-3, 0] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-3, 1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-3, 2] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-3, 3] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-3, 4] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-2, -4] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-2, 4] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [-1, 0] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [-1, 4] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [0, -5] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [0, 0] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [0, 4] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [1, 0] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_44 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_45 : subd5_2 [2, -5] = true := by decide +kernel
theorem subd5_2_46 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_47 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_48 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_49 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_50 : subd5_2 [2, 0] = true := by decide +kernel
theorem subd5_2_51 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_52 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_53 : subd5_2 [2, 3] = true := by decide +kernel
theorem subd5_2_54 : subd5_2 [3, -5] = true := by decide +kernel
theorem subd5_2_55 : subd5_2 [3, -4] = true := by decide +kernel
theorem subd5_2_56 : subd5_2 [3, -3] = true := by decide +kernel
theorem subd5_2_57 : subd5_2 [3, -2] = true := by decide +kernel
theorem subd5_2_58 : subd5_2 [3, -1] = true := by decide +kernel
theorem subd5_2_59 : subd5_2 [3, 0] = true := by decide +kernel
theorem subd5_2_60 : subd5_2 [3, 1] = true := by decide +kernel
theorem subd5_2_61 : subd5_2 [4] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_cons.2 ⟨subd5_2_44, List.forall_mem_cons.2 ⟨subd5_2_45, List.forall_mem_cons.2 ⟨subd5_2_46, List.forall_mem_cons.2 ⟨subd5_2_47, List.forall_mem_cons.2 ⟨subd5_2_48, List.forall_mem_cons.2 ⟨subd5_2_49, List.forall_mem_cons.2 ⟨subd5_2_50, List.forall_mem_cons.2 ⟨subd5_2_51, List.forall_mem_cons.2 ⟨subd5_2_52, List.forall_mem_cons.2 ⟨subd5_2_53, List.forall_mem_cons.2 ⟨subd5_2_54, List.forall_mem_cons.2 ⟨subd5_2_55, List.forall_mem_cons.2 ⟨subd5_2_56, List.forall_mem_cons.2 ⟨subd5_2_57, List.forall_mem_cons.2 ⟨subd5_2_58, List.forall_mem_cons.2 ⟨subd5_2_59, List.forall_mem_cons.2 ⟨subd5_2_60, List.forall_mem_cons.2 ⟨subd5_2_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-1, 0, -9] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-1, 0, -8] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-1, 0, -7] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-1, 0, -6] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-1, 0, -5] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-1, 0, -4] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-1, 0, -3] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-1, 0, -2] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [-1, 0, -1] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [-1, 0, 0] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [-1, 0, 1] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [-1, 0, 2] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [-1, 0, 3] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [-1, 0, 4] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [-1, 0, 5] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [-1, 0, 6] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [-1, 0, 7] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [-1, 1, -8] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [-1, 1, -7] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [-1, 1, -6] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [-1, 1, -5] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [-1, 1, -4] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [-1, 1, -3] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [-1, 1, -2] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [-1, 1, -1] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [-1, 1, 0] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [-1, 1, 1] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [-1, 1, 2] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [-1, 1, 3] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [-1, 1, 4] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [-1, 1, 5] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [-1, 1, 6] = true := by decide +kernel
theorem subd5_3_40 : subd5_3 [-1, 1, 7] = true := by decide +kernel
theorem subd5_3_41 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_42 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_43 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_44 : subd5_3 [0, -1, -9] = true := by decide +kernel
theorem subd5_3_45 : subd5_3 [0, -1, -8] = true := by decide +kernel
theorem subd5_3_46 : subd5_3 [0, -1, -7] = true := by decide +kernel
theorem subd5_3_47 : subd5_3 [0, -1, -6] = true := by decide +kernel
theorem subd5_3_48 : subd5_3 [0, -1, -5] = true := by decide +kernel
theorem subd5_3_49 : subd5_3 [0, -1, -4] = true := by decide +kernel
theorem subd5_3_50 : subd5_3 [0, -1, -3] = true := by decide +kernel
theorem subd5_3_51 : subd5_3 [0, -1, -2] = true := by decide +kernel
theorem subd5_3_52 : subd5_3 [0, -1, -1] = true := by decide +kernel
theorem subd5_3_53 : subd5_3 [0, -1, 0] = true := by decide +kernel
theorem subd5_3_54 : subd5_3 [0, -1, 1] = true := by decide +kernel
theorem subd5_3_55 : subd5_3 [0, -1, 2] = true := by decide +kernel
theorem subd5_3_56 : subd5_3 [0, -1, 3] = true := by decide +kernel
theorem subd5_3_57 : subd5_3 [0, -1, 4] = true := by decide +kernel
theorem subd5_3_58 : subd5_3 [0, -1, 5] = true := by decide +kernel
theorem subd5_3_59 : subd5_3 [0, -1, 6] = true := by decide +kernel
theorem subd5_3_60 : subd5_3 [0, -1, 7] = true := by decide +kernel
theorem subd5_3_61 : subd5_3 [0, 0, -9] = true := by decide +kernel
theorem subd5_3_62 : subd5_3 [0, 0, -8] = true := by decide +kernel
theorem subd5_3_63 : subd5_3 [0, 0, -7] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_cons.2 ⟨subd5_3_40, List.forall_mem_cons.2 ⟨subd5_3_41, List.forall_mem_cons.2 ⟨subd5_3_42, List.forall_mem_cons.2 ⟨subd5_3_43, List.forall_mem_cons.2 ⟨subd5_3_44, List.forall_mem_cons.2 ⟨subd5_3_45, List.forall_mem_cons.2 ⟨subd5_3_46, List.forall_mem_cons.2 ⟨subd5_3_47, List.forall_mem_cons.2 ⟨subd5_3_48, List.forall_mem_cons.2 ⟨subd5_3_49, List.forall_mem_cons.2 ⟨subd5_3_50, List.forall_mem_cons.2 ⟨subd5_3_51, List.forall_mem_cons.2 ⟨subd5_3_52, List.forall_mem_cons.2 ⟨subd5_3_53, List.forall_mem_cons.2 ⟨subd5_3_54, List.forall_mem_cons.2 ⟨subd5_3_55, List.forall_mem_cons.2 ⟨subd5_3_56, List.forall_mem_cons.2 ⟨subd5_3_57, List.forall_mem_cons.2 ⟨subd5_3_58, List.forall_mem_cons.2 ⟨subd5_3_59, List.forall_mem_cons.2 ⟨subd5_3_60, List.forall_mem_cons.2 ⟨subd5_3_61, List.forall_mem_cons.2 ⟨subd5_3_62, List.forall_mem_cons.2 ⟨subd5_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C133
