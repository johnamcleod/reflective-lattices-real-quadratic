import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_6_0 : subd5_6 [-3] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-2] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [-1, -4] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [-1, -3] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [-1, -2] = true := by decide +kernel
theorem subd5_6_5 : subd5_6 [-1, -1] = true := by decide +kernel
theorem subd5_6_6 : subd5_6 [-1, 0] = true := by decide +kernel
theorem subd5_6_7 : subd5_6 [-1, 1] = true := by decide +kernel
theorem subd5_6_8 : subd5_6 [-1, 2] = true := by decide +kernel
theorem subd5_6_9 : subd5_6 [0, -4] = true := by decide +kernel
theorem subd5_6_10 : subd5_6 [0, -3] = true := by decide +kernel
theorem subd5_6_11 : subd5_6 [0, -2] = true := by decide +kernel
theorem subd5_6_12 : subd5_6 [0, -1] = true := by decide +kernel
theorem subd5_6_13 : subd5_6 [0, 0] = true := by decide +kernel
theorem subd5_6_14 : subd5_6 [0, 1] = true := by decide +kernel
theorem subd5_6_15 : subd5_6 [0, 2] = true := by decide +kernel
theorem subd5_6_16 : subd5_6 [0, 3] = true := by decide +kernel
theorem subd5_6_17 : subd5_6 [1, -3] = true := by decide +kernel
theorem subd5_6_18 : subd5_6 [1, -2] = true := by decide +kernel
theorem subd5_6_19 : subd5_6 [1, -1] = true := by decide +kernel
theorem subd5_6_20 : subd5_6 [1, 0] = true := by decide +kernel
theorem subd5_6_21 : subd5_6 [1, 1] = true := by decide +kernel
theorem subd5_6_22 : subd5_6 [1, 2] = true := by decide +kernel
theorem subd5_6_23 : subd5_6 [1, 3] = true := by decide +kernel
theorem subd5_6_24 : subd5_6 [2] = true := by decide +kernel
theorem subd5_6_25 : subd5_6 [3] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_cons.2 ⟨subd5_6_5, List.forall_mem_cons.2 ⟨subd5_6_6, List.forall_mem_cons.2 ⟨subd5_6_7, List.forall_mem_cons.2 ⟨subd5_6_8, List.forall_mem_cons.2 ⟨subd5_6_9, List.forall_mem_cons.2 ⟨subd5_6_10, List.forall_mem_cons.2 ⟨subd5_6_11, List.forall_mem_cons.2 ⟨subd5_6_12, List.forall_mem_cons.2 ⟨subd5_6_13, List.forall_mem_cons.2 ⟨subd5_6_14, List.forall_mem_cons.2 ⟨subd5_6_15, List.forall_mem_cons.2 ⟨subd5_6_16, List.forall_mem_cons.2 ⟨subd5_6_17, List.forall_mem_cons.2 ⟨subd5_6_18, List.forall_mem_cons.2 ⟨subd5_6_19, List.forall_mem_cons.2 ⟨subd5_6_20, List.forall_mem_cons.2 ⟨subd5_6_21, List.forall_mem_cons.2 ⟨subd5_6_22, List.forall_mem_cons.2 ⟨subd5_6_23, List.forall_mem_cons.2 ⟨subd5_6_24, List.forall_mem_cons.2 ⟨subd5_6_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-2] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-1, -1] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-1, 0] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [0, -1] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [0, 0] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [0, 1] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [0, 2] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [1, -1] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [1, 0] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [1, 1] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [2] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-4] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-3, -4] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-3, -3] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-3, -2] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-3, -1] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-3, 0] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-3, 1] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-3, 2] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-3, 3] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-2, -4] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [-2, -3] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [-2, -2] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [-2, -1] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [-2, 0] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [-2, 1] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [-2, 2] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [-2, 3] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [-1, -5] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [-1, -4] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [-1, 4] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [0, -5] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [0, -1] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_32 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_33 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_34 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_35 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_36 : subd6_0 [0, 4] = true := by decide +kernel
theorem subd6_0_37 : subd6_0 [1, -5] = true := by decide +kernel
theorem subd6_0_38 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_39 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_40 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_41 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_42 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_43 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_44 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_45 : subd6_0 [1, 3] = true := by decide +kernel
theorem subd6_0_46 : subd6_0 [1, 4] = true := by decide +kernel
theorem subd6_0_47 : subd6_0 [2, -4] = true := by decide +kernel
theorem subd6_0_48 : subd6_0 [2, -3] = true := by decide +kernel
theorem subd6_0_49 : subd6_0 [2, -2] = true := by decide +kernel
theorem subd6_0_50 : subd6_0 [2, -1] = true := by decide +kernel
theorem subd6_0_51 : subd6_0 [2, 0] = true := by decide +kernel
theorem subd6_0_52 : subd6_0 [2, 1] = true := by decide +kernel
theorem subd6_0_53 : subd6_0 [2, 2] = true := by decide +kernel
theorem subd6_0_54 : subd6_0 [2, 3] = true := by decide +kernel
theorem subd6_0_55 : subd6_0 [3, -4] = true := by decide +kernel
theorem subd6_0_56 : subd6_0 [3, -3] = true := by decide +kernel
theorem subd6_0_57 : subd6_0 [3, -2] = true := by decide +kernel
theorem subd6_0_58 : subd6_0 [3, -1] = true := by decide +kernel
theorem subd6_0_59 : subd6_0 [3, 0] = true := by decide +kernel
theorem subd6_0_60 : subd6_0 [3, 1] = true := by decide +kernel
theorem subd6_0_61 : subd6_0 [3, 2] = true := by decide +kernel
theorem subd6_0_62 : subd6_0 [3, 3] = true := by decide +kernel
theorem subd6_0_63 : subd6_0 [4] = true := by decide +kernel
theorem sbd6_0_1 : ∀ q ∈ blkd6_0_1, subd6_0 q = true := by
  unfold blkd6_0_1
  exact List.forall_mem_cons.2 ⟨subd6_0_32, List.forall_mem_cons.2 ⟨subd6_0_33, List.forall_mem_cons.2 ⟨subd6_0_34, List.forall_mem_cons.2 ⟨subd6_0_35, List.forall_mem_cons.2 ⟨subd6_0_36, List.forall_mem_cons.2 ⟨subd6_0_37, List.forall_mem_cons.2 ⟨subd6_0_38, List.forall_mem_cons.2 ⟨subd6_0_39, List.forall_mem_cons.2 ⟨subd6_0_40, List.forall_mem_cons.2 ⟨subd6_0_41, List.forall_mem_cons.2 ⟨subd6_0_42, List.forall_mem_cons.2 ⟨subd6_0_43, List.forall_mem_cons.2 ⟨subd6_0_44, List.forall_mem_cons.2 ⟨subd6_0_45, List.forall_mem_cons.2 ⟨subd6_0_46, List.forall_mem_cons.2 ⟨subd6_0_47, List.forall_mem_cons.2 ⟨subd6_0_48, List.forall_mem_cons.2 ⟨subd6_0_49, List.forall_mem_cons.2 ⟨subd6_0_50, List.forall_mem_cons.2 ⟨subd6_0_51, List.forall_mem_cons.2 ⟨subd6_0_52, List.forall_mem_cons.2 ⟨subd6_0_53, List.forall_mem_cons.2 ⟨subd6_0_54, List.forall_mem_cons.2 ⟨subd6_0_55, List.forall_mem_cons.2 ⟨subd6_0_56, List.forall_mem_cons.2 ⟨subd6_0_57, List.forall_mem_cons.2 ⟨subd6_0_58, List.forall_mem_cons.2 ⟨subd6_0_59, List.forall_mem_cons.2 ⟨subd6_0_60, List.forall_mem_cons.2 ⟨subd6_0_61, List.forall_mem_cons.2 ⟨subd6_0_62, List.forall_mem_cons.2 ⟨subd6_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
