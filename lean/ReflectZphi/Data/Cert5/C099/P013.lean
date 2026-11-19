import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-2] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-1, 3] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [1, -4] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [1, -1] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [1, 1] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [2] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-4] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-3, -4] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [-3, -3] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [-3, -2] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [-3, -1] = true := by decide +kernel
theorem subd6_5_5 : subd6_5 [-3, 0] = true := by decide +kernel
theorem subd6_5_6 : subd6_5 [-3, 1] = true := by decide +kernel
theorem subd6_5_7 : subd6_5 [-3, 2] = true := by decide +kernel
theorem subd6_5_8 : subd6_5 [-2, -5] = true := by decide +kernel
theorem subd6_5_9 : subd6_5 [-2, -4] = true := by decide +kernel
theorem subd6_5_10 : subd6_5 [-2, -3] = true := by decide +kernel
theorem subd6_5_11 : subd6_5 [-2, -2] = true := by decide +kernel
theorem subd6_5_12 : subd6_5 [-2, -1] = true := by decide +kernel
theorem subd6_5_13 : subd6_5 [-2, 0] = true := by decide +kernel
theorem subd6_5_14 : subd6_5 [-2, 1] = true := by decide +kernel
theorem subd6_5_15 : subd6_5 [-2, 2] = true := by decide +kernel
theorem subd6_5_16 : subd6_5 [-2, 3] = true := by decide +kernel
theorem subd6_5_17 : subd6_5 [-1, -5] = true := by decide +kernel
theorem subd6_5_18 : subd6_5 [-1, -4] = true := by decide +kernel
theorem subd6_5_19 : subd6_5 [-1, -3] = true := by decide +kernel
theorem subd6_5_20 : subd6_5 [-1, -2] = true := by decide +kernel
theorem subd6_5_21 : subd6_5 [-1, -1] = true := by decide +kernel
theorem subd6_5_22 : subd6_5 [-1, 0] = true := by decide +kernel
theorem subd6_5_23 : subd6_5 [-1, 1] = true := by decide +kernel
theorem subd6_5_24 : subd6_5 [-1, 2] = true := by decide +kernel
theorem subd6_5_25 : subd6_5 [-1, 3] = true := by decide +kernel
theorem subd6_5_26 : subd6_5 [0, -5] = true := by decide +kernel
theorem subd6_5_27 : subd6_5 [0, -4] = true := by decide +kernel
theorem subd6_5_28 : subd6_5 [0, -3] = true := by decide +kernel
theorem subd6_5_29 : subd6_5 [0, -2] = true := by decide +kernel
theorem subd6_5_30 : subd6_5 [0, -1] = true := by decide +kernel
theorem subd6_5_31 : subd6_5 [0, 0] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_cons.2 ⟨subd6_5_5, List.forall_mem_cons.2 ⟨subd6_5_6, List.forall_mem_cons.2 ⟨subd6_5_7, List.forall_mem_cons.2 ⟨subd6_5_8, List.forall_mem_cons.2 ⟨subd6_5_9, List.forall_mem_cons.2 ⟨subd6_5_10, List.forall_mem_cons.2 ⟨subd6_5_11, List.forall_mem_cons.2 ⟨subd6_5_12, List.forall_mem_cons.2 ⟨subd6_5_13, List.forall_mem_cons.2 ⟨subd6_5_14, List.forall_mem_cons.2 ⟨subd6_5_15, List.forall_mem_cons.2 ⟨subd6_5_16, List.forall_mem_cons.2 ⟨subd6_5_17, List.forall_mem_cons.2 ⟨subd6_5_18, List.forall_mem_cons.2 ⟨subd6_5_19, List.forall_mem_cons.2 ⟨subd6_5_20, List.forall_mem_cons.2 ⟨subd6_5_21, List.forall_mem_cons.2 ⟨subd6_5_22, List.forall_mem_cons.2 ⟨subd6_5_23, List.forall_mem_cons.2 ⟨subd6_5_24, List.forall_mem_cons.2 ⟨subd6_5_25, List.forall_mem_cons.2 ⟨subd6_5_26, List.forall_mem_cons.2 ⟨subd6_5_27, List.forall_mem_cons.2 ⟨subd6_5_28, List.forall_mem_cons.2 ⟨subd6_5_29, List.forall_mem_cons.2 ⟨subd6_5_30, List.forall_mem_cons.2 ⟨subd6_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_5_32 : subd6_5 [0, 1] = true := by decide +kernel
theorem subd6_5_33 : subd6_5 [0, 2] = true := by decide +kernel
theorem subd6_5_34 : subd6_5 [0, 3] = true := by decide +kernel
theorem subd6_5_35 : subd6_5 [0, 4] = true := by decide +kernel
theorem subd6_5_36 : subd6_5 [1, -4] = true := by decide +kernel
theorem subd6_5_37 : subd6_5 [1, -3] = true := by decide +kernel
theorem subd6_5_38 : subd6_5 [1, -2] = true := by decide +kernel
theorem subd6_5_39 : subd6_5 [1, -1] = true := by decide +kernel
theorem subd6_5_40 : subd6_5 [1, 0] = true := by decide +kernel
theorem subd6_5_41 : subd6_5 [1, 1] = true := by decide +kernel
theorem subd6_5_42 : subd6_5 [1, 2] = true := by decide +kernel
theorem subd6_5_43 : subd6_5 [1, 3] = true := by decide +kernel
theorem subd6_5_44 : subd6_5 [1, 4] = true := by decide +kernel
theorem subd6_5_45 : subd6_5 [2, -4] = true := by decide +kernel
theorem subd6_5_46 : subd6_5 [2, -3] = true := by decide +kernel
theorem subd6_5_47 : subd6_5 [2, -2] = true := by decide +kernel
theorem subd6_5_48 : subd6_5 [2, -1] = true := by decide +kernel
theorem subd6_5_49 : subd6_5 [2, 0] = true := by decide +kernel
theorem subd6_5_50 : subd6_5 [2, 1] = true := by decide +kernel
theorem subd6_5_51 : subd6_5 [2, 2] = true := by decide +kernel
theorem subd6_5_52 : subd6_5 [2, 3] = true := by decide +kernel
theorem subd6_5_53 : subd6_5 [2, 4] = true := by decide +kernel
theorem subd6_5_54 : subd6_5 [3, -3] = true := by decide +kernel
theorem subd6_5_55 : subd6_5 [3, -2] = true := by decide +kernel
theorem subd6_5_56 : subd6_5 [3, -1] = true := by decide +kernel
theorem subd6_5_57 : subd6_5 [3, 0] = true := by decide +kernel
theorem subd6_5_58 : subd6_5 [3, 1] = true := by decide +kernel
theorem subd6_5_59 : subd6_5 [3, 2] = true := by decide +kernel
theorem subd6_5_60 : subd6_5 [3, 3] = true := by decide +kernel
theorem subd6_5_61 : subd6_5 [4] = true := by decide +kernel
theorem sbd6_5_1 : ∀ q ∈ blkd6_5_1, subd6_5 q = true := by
  unfold blkd6_5_1
  exact List.forall_mem_cons.2 ⟨subd6_5_32, List.forall_mem_cons.2 ⟨subd6_5_33, List.forall_mem_cons.2 ⟨subd6_5_34, List.forall_mem_cons.2 ⟨subd6_5_35, List.forall_mem_cons.2 ⟨subd6_5_36, List.forall_mem_cons.2 ⟨subd6_5_37, List.forall_mem_cons.2 ⟨subd6_5_38, List.forall_mem_cons.2 ⟨subd6_5_39, List.forall_mem_cons.2 ⟨subd6_5_40, List.forall_mem_cons.2 ⟨subd6_5_41, List.forall_mem_cons.2 ⟨subd6_5_42, List.forall_mem_cons.2 ⟨subd6_5_43, List.forall_mem_cons.2 ⟨subd6_5_44, List.forall_mem_cons.2 ⟨subd6_5_45, List.forall_mem_cons.2 ⟨subd6_5_46, List.forall_mem_cons.2 ⟨subd6_5_47, List.forall_mem_cons.2 ⟨subd6_5_48, List.forall_mem_cons.2 ⟨subd6_5_49, List.forall_mem_cons.2 ⟨subd6_5_50, List.forall_mem_cons.2 ⟨subd6_5_51, List.forall_mem_cons.2 ⟨subd6_5_52, List.forall_mem_cons.2 ⟨subd6_5_53, List.forall_mem_cons.2 ⟨subd6_5_54, List.forall_mem_cons.2 ⟨subd6_5_55, List.forall_mem_cons.2 ⟨subd6_5_56, List.forall_mem_cons.2 ⟨subd6_5_57, List.forall_mem_cons.2 ⟨subd6_5_58, List.forall_mem_cons.2 ⟨subd6_5_59, List.forall_mem_cons.2 ⟨subd6_5_60, List.forall_mem_cons.2 ⟨subd6_5_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C099
