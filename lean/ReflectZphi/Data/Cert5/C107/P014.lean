import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-3] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-2] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-1, -4] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [-1, -3] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [-1, -2] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [-1, -1] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [-1, 0] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [-1, 1] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [-1, 2] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [0, -4] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [0, -3] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [0, -2] = true := by decide +kernel
theorem subd7_5_12 : subd7_5 [0, -1] = true := by decide +kernel
theorem subd7_5_13 : subd7_5 [0, 0] = true := by decide +kernel
theorem subd7_5_14 : subd7_5 [0, 1] = true := by decide +kernel
theorem subd7_5_15 : subd7_5 [0, 2] = true := by decide +kernel
theorem subd7_5_16 : subd7_5 [0, 3] = true := by decide +kernel
theorem subd7_5_17 : subd7_5 [1, -3] = true := by decide +kernel
theorem subd7_5_18 : subd7_5 [1, -2] = true := by decide +kernel
theorem subd7_5_19 : subd7_5 [1, -1] = true := by decide +kernel
theorem subd7_5_20 : subd7_5 [1, 0] = true := by decide +kernel
theorem subd7_5_21 : subd7_5 [1, 1] = true := by decide +kernel
theorem subd7_5_22 : subd7_5 [1, 2] = true := by decide +kernel
theorem subd7_5_23 : subd7_5 [1, 3] = true := by decide +kernel
theorem subd7_5_24 : subd7_5 [2] = true := by decide +kernel
theorem subd7_5_25 : subd7_5 [3] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_cons.2 ⟨subd7_5_12, List.forall_mem_cons.2 ⟨subd7_5_13, List.forall_mem_cons.2 ⟨subd7_5_14, List.forall_mem_cons.2 ⟨subd7_5_15, List.forall_mem_cons.2 ⟨subd7_5_16, List.forall_mem_cons.2 ⟨subd7_5_17, List.forall_mem_cons.2 ⟨subd7_5_18, List.forall_mem_cons.2 ⟨subd7_5_19, List.forall_mem_cons.2 ⟨subd7_5_20, List.forall_mem_cons.2 ⟨subd7_5_21, List.forall_mem_cons.2 ⟨subd7_5_22, List.forall_mem_cons.2 ⟨subd7_5_23, List.forall_mem_cons.2 ⟨subd7_5_24, List.forall_mem_cons.2 ⟨subd7_5_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-5] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-4, -7] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-4, -6] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-4, -5] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-4, -4] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-4, -3] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [-4, -2] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [-4, -1] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [-4, 0] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [-4, 1] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [-4, 2] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [-3, -7] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [-3, -6] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [-3, -5] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [-3, -4] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [-3, -3] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [-3, -2] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [-3, -1] = true := by decide +kernel
theorem subd7_6_18 : subd7_6 [-3, 0] = true := by decide +kernel
theorem subd7_6_19 : subd7_6 [-3, 1] = true := by decide +kernel
theorem subd7_6_20 : subd7_6 [-3, 2] = true := by decide +kernel
theorem subd7_6_21 : subd7_6 [-3, 3] = true := by decide +kernel
theorem subd7_6_22 : subd7_6 [-2, -7] = true := by decide +kernel
theorem subd7_6_23 : subd7_6 [-2, -6] = true := by decide +kernel
theorem subd7_6_24 : subd7_6 [-2, -5] = true := by decide +kernel
theorem subd7_6_25 : subd7_6 [-2, -4] = true := by decide +kernel
theorem subd7_6_26 : subd7_6 [-2, -3] = true := by decide +kernel
theorem subd7_6_27 : subd7_6 [-2, -2] = true := by decide +kernel
theorem subd7_6_28 : subd7_6 [-2, -1] = true := by decide +kernel
theorem subd7_6_29 : subd7_6 [-2, 0] = true := by decide +kernel
theorem subd7_6_30 : subd7_6 [-2, 1] = true := by decide +kernel
theorem subd7_6_31 : subd7_6 [-2, 2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_cons.2 ⟨subd7_6_18, List.forall_mem_cons.2 ⟨subd7_6_19, List.forall_mem_cons.2 ⟨subd7_6_20, List.forall_mem_cons.2 ⟨subd7_6_21, List.forall_mem_cons.2 ⟨subd7_6_22, List.forall_mem_cons.2 ⟨subd7_6_23, List.forall_mem_cons.2 ⟨subd7_6_24, List.forall_mem_cons.2 ⟨subd7_6_25, List.forall_mem_cons.2 ⟨subd7_6_26, List.forall_mem_cons.2 ⟨subd7_6_27, List.forall_mem_cons.2 ⟨subd7_6_28, List.forall_mem_cons.2 ⟨subd7_6_29, List.forall_mem_cons.2 ⟨subd7_6_30, List.forall_mem_cons.2 ⟨subd7_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_32 : subd7_6 [-2, 3] = true := by decide +kernel
theorem subd7_6_33 : subd7_6 [-2, 4] = true := by decide +kernel
theorem subd7_6_34 : subd7_6 [-1, -7] = true := by decide +kernel
theorem subd7_6_35 : subd7_6 [-1, -6] = true := by decide +kernel
theorem subd7_6_36 : subd7_6 [-1, -5] = true := by decide +kernel
theorem subd7_6_37 : subd7_6 [-1, -4] = true := by decide +kernel
theorem subd7_6_38 : subd7_6 [-1, -3] = true := by decide +kernel
theorem subd7_6_39 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_40 : subd7_6 [-1, -1] = true := by decide +kernel
theorem subd7_6_41 : subd7_6 [-1, 0] = true := by decide +kernel
theorem subd7_6_42 : subd7_6 [-1, 1] = true := by decide +kernel
theorem subd7_6_43 : subd7_6 [-1, 2] = true := by decide +kernel
theorem subd7_6_44 : subd7_6 [-1, 3] = true := by decide +kernel
theorem subd7_6_45 : subd7_6 [-1, 4] = true := by decide +kernel
theorem subd7_6_46 : subd7_6 [-1, 5] = true := by decide +kernel
theorem subd7_6_47 : subd7_6 [0, -7] = true := by decide +kernel
theorem subd7_6_48 : subd7_6 [0, -6] = true := by decide +kernel
theorem subd7_6_49 : subd7_6 [0, -5] = true := by decide +kernel
theorem subd7_6_50 : subd7_6 [0, -4] = true := by decide +kernel
theorem subd7_6_51 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_52 : subd7_6 [0, -2] = true := by decide +kernel
theorem subd7_6_53 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_54 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_55 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_56 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_57 : subd7_6 [0, 3] = true := by decide +kernel
theorem subd7_6_58 : subd7_6 [0, 4] = true := by decide +kernel
theorem subd7_6_59 : subd7_6 [0, 5] = true := by decide +kernel
theorem subd7_6_60 : subd7_6 [0, 6] = true := by decide +kernel
theorem subd7_6_61 : subd7_6 [1, -6] = true := by decide +kernel
theorem subd7_6_62 : subd7_6 [1, -5] = true := by decide +kernel
theorem subd7_6_63 : subd7_6 [1, -4] = true := by decide +kernel
theorem sbd7_6_1 : ∀ q ∈ blkd7_6_1, subd7_6 q = true := by
  unfold blkd7_6_1
  exact List.forall_mem_cons.2 ⟨subd7_6_32, List.forall_mem_cons.2 ⟨subd7_6_33, List.forall_mem_cons.2 ⟨subd7_6_34, List.forall_mem_cons.2 ⟨subd7_6_35, List.forall_mem_cons.2 ⟨subd7_6_36, List.forall_mem_cons.2 ⟨subd7_6_37, List.forall_mem_cons.2 ⟨subd7_6_38, List.forall_mem_cons.2 ⟨subd7_6_39, List.forall_mem_cons.2 ⟨subd7_6_40, List.forall_mem_cons.2 ⟨subd7_6_41, List.forall_mem_cons.2 ⟨subd7_6_42, List.forall_mem_cons.2 ⟨subd7_6_43, List.forall_mem_cons.2 ⟨subd7_6_44, List.forall_mem_cons.2 ⟨subd7_6_45, List.forall_mem_cons.2 ⟨subd7_6_46, List.forall_mem_cons.2 ⟨subd7_6_47, List.forall_mem_cons.2 ⟨subd7_6_48, List.forall_mem_cons.2 ⟨subd7_6_49, List.forall_mem_cons.2 ⟨subd7_6_50, List.forall_mem_cons.2 ⟨subd7_6_51, List.forall_mem_cons.2 ⟨subd7_6_52, List.forall_mem_cons.2 ⟨subd7_6_53, List.forall_mem_cons.2 ⟨subd7_6_54, List.forall_mem_cons.2 ⟨subd7_6_55, List.forall_mem_cons.2 ⟨subd7_6_56, List.forall_mem_cons.2 ⟨subd7_6_57, List.forall_mem_cons.2 ⟨subd7_6_58, List.forall_mem_cons.2 ⟨subd7_6_59, List.forall_mem_cons.2 ⟨subd7_6_60, List.forall_mem_cons.2 ⟨subd7_6_61, List.forall_mem_cons.2 ⟨subd7_6_62, List.forall_mem_cons.2 ⟨subd7_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
