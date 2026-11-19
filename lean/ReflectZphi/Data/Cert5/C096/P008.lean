import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_4_0 : subd6_4 [-3] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-2] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [0, -4] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [0, 3] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [1, -1] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [1, 1] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_22 : subd6_4 [2] = true := by decide +kernel
theorem subd6_4_23 : subd6_4 [3] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_cons.2 ⟨subd6_4_22, List.forall_mem_cons.2 ⟨subd6_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-4] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-3, -3] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-3, -2] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-3, -1] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-3, 0] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-3, 1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-3, 2] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-3, 3] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-2, -3] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-2, -2] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-2, -1] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-2, 0] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-2, 1] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-2, 2] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-2, 3] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-2, 4] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [-1, -5] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [-1, 4] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [0, -5] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [0, -1] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [0, 4] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [1, -5] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [1, 4] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [2, -5] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [2, -4] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [2, -2] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [2, -1] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [2, 0] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [2, 1] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [2, 2] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [2, 3] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [3, -4] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [3, -3] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [3, -2] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [3, -1] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [3, 0] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [3, 1] = true := by decide +kernel
theorem subd7_0_62 : subd7_0 [3, 2] = true := by decide +kernel
theorem subd7_0_63 : subd7_0 [4] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_cons.2 ⟨subd7_0_62, List.forall_mem_cons.2 ⟨subd7_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
