import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_3_0 : subd5_3 [-4] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-3, -5] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-3, -4] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-3, -3] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-3, -2] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-3, -1] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-3, 0] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-3, 1] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-2, -5] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-2, -4] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [-1, -5] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [-1, 3] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [0, -5] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [0, 1] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [0, 4] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_40 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_41 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_42 : subd5_3 [1, 3] = true := by decide +kernel
theorem subd5_3_43 : subd5_3 [1, 4] = true := by decide +kernel
theorem subd5_3_44 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_45 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_46 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_47 : subd5_3 [2, 0] = true := by decide +kernel
theorem subd5_3_48 : subd5_3 [2, 1] = true := by decide +kernel
theorem subd5_3_49 : subd5_3 [2, 2] = true := by decide +kernel
theorem subd5_3_50 : subd5_3 [2, 3] = true := by decide +kernel
theorem subd5_3_51 : subd5_3 [2, 4] = true := by decide +kernel
theorem subd5_3_52 : subd5_3 [3, -2] = true := by decide +kernel
theorem subd5_3_53 : subd5_3 [3, -1] = true := by decide +kernel
theorem subd5_3_54 : subd5_3 [3, 0] = true := by decide +kernel
theorem subd5_3_55 : subd5_3 [3, 1] = true := by decide +kernel
theorem subd5_3_56 : subd5_3 [3, 2] = true := by decide +kernel
theorem subd5_3_57 : subd5_3 [3, 3] = true := by decide +kernel
theorem subd5_3_58 : subd5_3 [3, 4] = true := by decide +kernel
theorem subd5_3_59 : subd5_3 [4] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_cons.2 ⟨subd5_3_40, List.forall_mem_cons.2 ⟨subd5_3_41, List.forall_mem_cons.2 ⟨subd5_3_42, List.forall_mem_cons.2 ⟨subd5_3_43, List.forall_mem_cons.2 ⟨subd5_3_44, List.forall_mem_cons.2 ⟨subd5_3_45, List.forall_mem_cons.2 ⟨subd5_3_46, List.forall_mem_cons.2 ⟨subd5_3_47, List.forall_mem_cons.2 ⟨subd5_3_48, List.forall_mem_cons.2 ⟨subd5_3_49, List.forall_mem_cons.2 ⟨subd5_3_50, List.forall_mem_cons.2 ⟨subd5_3_51, List.forall_mem_cons.2 ⟨subd5_3_52, List.forall_mem_cons.2 ⟨subd5_3_53, List.forall_mem_cons.2 ⟨subd5_3_54, List.forall_mem_cons.2 ⟨subd5_3_55, List.forall_mem_cons.2 ⟨subd5_3_56, List.forall_mem_cons.2 ⟨subd5_3_57, List.forall_mem_cons.2 ⟨subd5_3_58, List.forall_mem_cons.2 ⟨subd5_3_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-1] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [0] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [1] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [2] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-3] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-2, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-2, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-2, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-2, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-2, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-2, 3] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [-1, 3] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [1, 3] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [2, -4] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [2, -3] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [2, -2] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [2, -1] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [2, 0] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [2, 1] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [2, 2] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [3] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C136
