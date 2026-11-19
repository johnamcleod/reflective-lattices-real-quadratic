import ReflectZphi.Data.Cert5.C118.Base

namespace ReflectZphi.Data.Cert5.C118

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_3_0 : subd4_3 [-3, -2] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-3, -1] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [-3, 0] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [-3, 1] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [-3, 2] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [-3, 3] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [-2, -3] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [-2, -2] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [-2, -1] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [-2, 0] = true := by decide +kernel
theorem subd4_3_10 : subd4_3 [-2, 1] = true := by decide +kernel
theorem subd4_3_11 : subd4_3 [-2, 2] = true := by decide +kernel
theorem subd4_3_12 : subd4_3 [-2, 3] = true := by decide +kernel
theorem subd4_3_13 : subd4_3 [-1, -4] = true := by decide +kernel
theorem subd4_3_14 : subd4_3 [-1, -3] = true := by decide +kernel
theorem subd4_3_15 : subd4_3 [-1, -2] = true := by decide +kernel
theorem subd4_3_16 : subd4_3 [-1, -1] = true := by decide +kernel
theorem subd4_3_17 : subd4_3 [-1, 0] = true := by decide +kernel
theorem subd4_3_18 : subd4_3 [-1, 1] = true := by decide +kernel
theorem subd4_3_19 : subd4_3 [-1, 2] = true := by decide +kernel
theorem subd4_3_20 : subd4_3 [-1, 3] = true := by decide +kernel
theorem subd4_3_21 : subd4_3 [-1, 4] = true := by decide +kernel
theorem subd4_3_22 : subd4_3 [0, -5] = true := by decide +kernel
theorem subd4_3_23 : subd4_3 [0, -4] = true := by decide +kernel
theorem subd4_3_24 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_25 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_26 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_27 : subd4_3 [0, 0, -7] = true := by decide +kernel
theorem subd4_3_28 : subd4_3 [0, 0, -6] = true := by decide +kernel
theorem subd4_3_29 : subd4_3 [0, 0, -5] = true := by decide +kernel
theorem subd4_3_30 : subd4_3 [0, 0, -4] = true := by decide +kernel
theorem subd4_3_31 : subd4_3 [0, 0, -3] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_cons.2 ⟨subd4_3_10, List.forall_mem_cons.2 ⟨subd4_3_11, List.forall_mem_cons.2 ⟨subd4_3_12, List.forall_mem_cons.2 ⟨subd4_3_13, List.forall_mem_cons.2 ⟨subd4_3_14, List.forall_mem_cons.2 ⟨subd4_3_15, List.forall_mem_cons.2 ⟨subd4_3_16, List.forall_mem_cons.2 ⟨subd4_3_17, List.forall_mem_cons.2 ⟨subd4_3_18, List.forall_mem_cons.2 ⟨subd4_3_19, List.forall_mem_cons.2 ⟨subd4_3_20, List.forall_mem_cons.2 ⟨subd4_3_21, List.forall_mem_cons.2 ⟨subd4_3_22, List.forall_mem_cons.2 ⟨subd4_3_23, List.forall_mem_cons.2 ⟨subd4_3_24, List.forall_mem_cons.2 ⟨subd4_3_25, List.forall_mem_cons.2 ⟨subd4_3_26, List.forall_mem_cons.2 ⟨subd4_3_27, List.forall_mem_cons.2 ⟨subd4_3_28, List.forall_mem_cons.2 ⟨subd4_3_29, List.forall_mem_cons.2 ⟨subd4_3_30, List.forall_mem_cons.2 ⟨subd4_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_3_32 : subd4_3 [0, 0, -2] = true := by decide +kernel
theorem subd4_3_33 : subd4_3 [0, 0, -1] = true := by decide +kernel
theorem subd4_3_34 : subd4_3 [0, 0, 0] = true := by decide +kernel
theorem subd4_3_35 : subd4_3 [0, 0, 1] = true := by decide +kernel
theorem subd4_3_36 : subd4_3 [0, 0, 2] = true := by decide +kernel
theorem subd4_3_37 : subd4_3 [0, 0, 3] = true := by decide +kernel
theorem subd4_3_38 : subd4_3 [0, 0, 4] = true := by decide +kernel
theorem subd4_3_39 : subd4_3 [0, 0, 5] = true := by decide +kernel
theorem subd4_3_40 : subd4_3 [0, 0, 6] = true := by decide +kernel
theorem subd4_3_41 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_42 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_43 : subd4_3 [0, 3] = true := by decide +kernel
theorem subd4_3_44 : subd4_3 [0, 4] = true := by decide +kernel
theorem subd4_3_45 : subd4_3 [1, -5] = true := by decide +kernel
theorem subd4_3_46 : subd4_3 [1, -4] = true := by decide +kernel
theorem subd4_3_47 : subd4_3 [1, -3] = true := by decide +kernel
theorem subd4_3_48 : subd4_3 [1, -2] = true := by decide +kernel
theorem subd4_3_49 : subd4_3 [1, -1] = true := by decide +kernel
theorem subd4_3_50 : subd4_3 [1, 0] = true := by decide +kernel
theorem subd4_3_51 : subd4_3 [1, 1] = true := by decide +kernel
theorem subd4_3_52 : subd4_3 [1, 2] = true := by decide +kernel
theorem subd4_3_53 : subd4_3 [1, 3] = true := by decide +kernel
theorem subd4_3_54 : subd4_3 [2, -4] = true := by decide +kernel
theorem subd4_3_55 : subd4_3 [2, -3] = true := by decide +kernel
theorem subd4_3_56 : subd4_3 [2, -2] = true := by decide +kernel
theorem subd4_3_57 : subd4_3 [2, -1] = true := by decide +kernel
theorem subd4_3_58 : subd4_3 [2, 0] = true := by decide +kernel
theorem subd4_3_59 : subd4_3 [2, 1] = true := by decide +kernel
theorem subd4_3_60 : subd4_3 [2, 2] = true := by decide +kernel
theorem subd4_3_61 : subd4_3 [3, -4] = true := by decide +kernel
theorem subd4_3_62 : subd4_3 [3, -3] = true := by decide +kernel
theorem subd4_3_63 : subd4_3 [3, -2] = true := by decide +kernel
theorem sbd4_3_1 : ∀ q ∈ blkd4_3_1, subd4_3 q = true := by
  unfold blkd4_3_1
  exact List.forall_mem_cons.2 ⟨subd4_3_32, List.forall_mem_cons.2 ⟨subd4_3_33, List.forall_mem_cons.2 ⟨subd4_3_34, List.forall_mem_cons.2 ⟨subd4_3_35, List.forall_mem_cons.2 ⟨subd4_3_36, List.forall_mem_cons.2 ⟨subd4_3_37, List.forall_mem_cons.2 ⟨subd4_3_38, List.forall_mem_cons.2 ⟨subd4_3_39, List.forall_mem_cons.2 ⟨subd4_3_40, List.forall_mem_cons.2 ⟨subd4_3_41, List.forall_mem_cons.2 ⟨subd4_3_42, List.forall_mem_cons.2 ⟨subd4_3_43, List.forall_mem_cons.2 ⟨subd4_3_44, List.forall_mem_cons.2 ⟨subd4_3_45, List.forall_mem_cons.2 ⟨subd4_3_46, List.forall_mem_cons.2 ⟨subd4_3_47, List.forall_mem_cons.2 ⟨subd4_3_48, List.forall_mem_cons.2 ⟨subd4_3_49, List.forall_mem_cons.2 ⟨subd4_3_50, List.forall_mem_cons.2 ⟨subd4_3_51, List.forall_mem_cons.2 ⟨subd4_3_52, List.forall_mem_cons.2 ⟨subd4_3_53, List.forall_mem_cons.2 ⟨subd4_3_54, List.forall_mem_cons.2 ⟨subd4_3_55, List.forall_mem_cons.2 ⟨subd4_3_56, List.forall_mem_cons.2 ⟨subd4_3_57, List.forall_mem_cons.2 ⟨subd4_3_58, List.forall_mem_cons.2 ⟨subd4_3_59, List.forall_mem_cons.2 ⟨subd4_3_60, List.forall_mem_cons.2 ⟨subd4_3_61, List.forall_mem_cons.2 ⟨subd4_3_62, List.forall_mem_cons.2 ⟨subd4_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_3_64 : subd4_3 [3, -1] = true := by decide +kernel
theorem subd4_3_65 : subd4_3 [3, 0] = true := by decide +kernel
theorem subd4_3_66 : subd4_3 [3, 1] = true := by decide +kernel
theorem sbd4_3_2 : ∀ q ∈ blkd4_3_2, subd4_3 q = true := by
  unfold blkd4_3_2
  exact List.forall_mem_cons.2 ⟨subd4_3_64, List.forall_mem_cons.2 ⟨subd4_3_65, List.forall_mem_cons.2 ⟨subd4_3_66, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-3] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-2] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [-1, -4] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [-1, -3] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [-1, -2] = true := by decide +kernel
theorem subd4_4_5 : subd4_4 [-1, -1] = true := by decide +kernel
theorem subd4_4_6 : subd4_4 [-1, 0] = true := by decide +kernel
theorem subd4_4_7 : subd4_4 [-1, 1] = true := by decide +kernel
theorem subd4_4_8 : subd4_4 [-1, 2] = true := by decide +kernel
theorem subd4_4_9 : subd4_4 [0, -4] = true := by decide +kernel
theorem subd4_4_10 : subd4_4 [0, -3] = true := by decide +kernel
theorem subd4_4_11 : subd4_4 [0, -2] = true := by decide +kernel
theorem subd4_4_12 : subd4_4 [0, -1] = true := by decide +kernel
theorem subd4_4_13 : subd4_4 [0, 0] = true := by decide +kernel
theorem subd4_4_14 : subd4_4 [0, 1] = true := by decide +kernel
theorem subd4_4_15 : subd4_4 [0, 2] = true := by decide +kernel
theorem subd4_4_16 : subd4_4 [0, 3] = true := by decide +kernel
theorem subd4_4_17 : subd4_4 [1, -3] = true := by decide +kernel
theorem subd4_4_18 : subd4_4 [1, -2] = true := by decide +kernel
theorem subd4_4_19 : subd4_4 [1, -1] = true := by decide +kernel
theorem subd4_4_20 : subd4_4 [1, 0] = true := by decide +kernel
theorem subd4_4_21 : subd4_4 [1, 1] = true := by decide +kernel
theorem subd4_4_22 : subd4_4 [1, 2] = true := by decide +kernel
theorem subd4_4_23 : subd4_4 [1, 3] = true := by decide +kernel
theorem subd4_4_24 : subd4_4 [2] = true := by decide +kernel
theorem subd4_4_25 : subd4_4 [3] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_cons.2 ⟨subd4_4_5, List.forall_mem_cons.2 ⟨subd4_4_6, List.forall_mem_cons.2 ⟨subd4_4_7, List.forall_mem_cons.2 ⟨subd4_4_8, List.forall_mem_cons.2 ⟨subd4_4_9, List.forall_mem_cons.2 ⟨subd4_4_10, List.forall_mem_cons.2 ⟨subd4_4_11, List.forall_mem_cons.2 ⟨subd4_4_12, List.forall_mem_cons.2 ⟨subd4_4_13, List.forall_mem_cons.2 ⟨subd4_4_14, List.forall_mem_cons.2 ⟨subd4_4_15, List.forall_mem_cons.2 ⟨subd4_4_16, List.forall_mem_cons.2 ⟨subd4_4_17, List.forall_mem_cons.2 ⟨subd4_4_18, List.forall_mem_cons.2 ⟨subd4_4_19, List.forall_mem_cons.2 ⟨subd4_4_20, List.forall_mem_cons.2 ⟨subd4_4_21, List.forall_mem_cons.2 ⟨subd4_4_22, List.forall_mem_cons.2 ⟨subd4_4_23, List.forall_mem_cons.2 ⟨subd4_4_24, List.forall_mem_cons.2 ⟨subd4_4_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-1] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [1] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C118
