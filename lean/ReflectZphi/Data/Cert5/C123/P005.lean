import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [-4] = true := by decide +kernel
theorem subd3_5_1 : subd3_5 [-3, -2] = true := by decide +kernel
theorem subd3_5_2 : subd3_5 [-3, -1] = true := by decide +kernel
theorem subd3_5_3 : subd3_5 [-3, 0] = true := by decide +kernel
theorem subd3_5_4 : subd3_5 [-3, 1] = true := by decide +kernel
theorem subd3_5_5 : subd3_5 [-3, 2] = true := by decide +kernel
theorem subd3_5_6 : subd3_5 [-3, 3] = true := by decide +kernel
theorem subd3_5_7 : subd3_5 [-3, 4] = true := by decide +kernel
theorem subd3_5_8 : subd3_5 [-2, -4] = true := by decide +kernel
theorem subd3_5_9 : subd3_5 [-2, -3] = true := by decide +kernel
theorem subd3_5_10 : subd3_5 [-2, -2] = true := by decide +kernel
theorem subd3_5_11 : subd3_5 [-2, -1] = true := by decide +kernel
theorem subd3_5_12 : subd3_5 [-2, 0] = true := by decide +kernel
theorem subd3_5_13 : subd3_5 [-2, 1] = true := by decide +kernel
theorem subd3_5_14 : subd3_5 [-2, 2] = true := by decide +kernel
theorem subd3_5_15 : subd3_5 [-2, 3] = true := by decide +kernel
theorem subd3_5_16 : subd3_5 [-2, 4] = true := by decide +kernel
theorem subd3_5_17 : subd3_5 [-1, -4] = true := by decide +kernel
theorem subd3_5_18 : subd3_5 [-1, -3] = true := by decide +kernel
theorem subd3_5_19 : subd3_5 [-1, -2] = true := by decide +kernel
theorem subd3_5_20 : subd3_5 [-1, -1] = true := by decide +kernel
theorem subd3_5_21 : subd3_5 [-1, 0] = true := by decide +kernel
theorem subd3_5_22 : subd3_5 [-1, 1] = true := by decide +kernel
theorem subd3_5_23 : subd3_5 [-1, 2] = true := by decide +kernel
theorem subd3_5_24 : subd3_5 [-1, 3] = true := by decide +kernel
theorem subd3_5_25 : subd3_5 [-1, 4] = true := by decide +kernel
theorem subd3_5_26 : subd3_5 [0, -5] = true := by decide +kernel
theorem subd3_5_27 : subd3_5 [0, -4] = true := by decide +kernel
theorem subd3_5_28 : subd3_5 [0, -3] = true := by decide +kernel
theorem subd3_5_29 : subd3_5 [0, -2] = true := by decide +kernel
theorem subd3_5_30 : subd3_5 [0, -1] = true := by decide +kernel
theorem subd3_5_31 : subd3_5 [0, 0] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_cons.2 ⟨subd3_5_1, List.forall_mem_cons.2 ⟨subd3_5_2, List.forall_mem_cons.2 ⟨subd3_5_3, List.forall_mem_cons.2 ⟨subd3_5_4, List.forall_mem_cons.2 ⟨subd3_5_5, List.forall_mem_cons.2 ⟨subd3_5_6, List.forall_mem_cons.2 ⟨subd3_5_7, List.forall_mem_cons.2 ⟨subd3_5_8, List.forall_mem_cons.2 ⟨subd3_5_9, List.forall_mem_cons.2 ⟨subd3_5_10, List.forall_mem_cons.2 ⟨subd3_5_11, List.forall_mem_cons.2 ⟨subd3_5_12, List.forall_mem_cons.2 ⟨subd3_5_13, List.forall_mem_cons.2 ⟨subd3_5_14, List.forall_mem_cons.2 ⟨subd3_5_15, List.forall_mem_cons.2 ⟨subd3_5_16, List.forall_mem_cons.2 ⟨subd3_5_17, List.forall_mem_cons.2 ⟨subd3_5_18, List.forall_mem_cons.2 ⟨subd3_5_19, List.forall_mem_cons.2 ⟨subd3_5_20, List.forall_mem_cons.2 ⟨subd3_5_21, List.forall_mem_cons.2 ⟨subd3_5_22, List.forall_mem_cons.2 ⟨subd3_5_23, List.forall_mem_cons.2 ⟨subd3_5_24, List.forall_mem_cons.2 ⟨subd3_5_25, List.forall_mem_cons.2 ⟨subd3_5_26, List.forall_mem_cons.2 ⟨subd3_5_27, List.forall_mem_cons.2 ⟨subd3_5_28, List.forall_mem_cons.2 ⟨subd3_5_29, List.forall_mem_cons.2 ⟨subd3_5_30, List.forall_mem_cons.2 ⟨subd3_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_32 : subd3_5 [0, 1] = true := by decide +kernel
theorem subd3_5_33 : subd3_5 [0, 2] = true := by decide +kernel
theorem subd3_5_34 : subd3_5 [0, 3] = true := by decide +kernel
theorem subd3_5_35 : subd3_5 [0, 4] = true := by decide +kernel
theorem subd3_5_36 : subd3_5 [1, -5] = true := by decide +kernel
theorem subd3_5_37 : subd3_5 [1, -4] = true := by decide +kernel
theorem subd3_5_38 : subd3_5 [1, -3] = true := by decide +kernel
theorem subd3_5_39 : subd3_5 [1, -2] = true := by decide +kernel
theorem subd3_5_40 : subd3_5 [1, -1] = true := by decide +kernel
theorem subd3_5_41 : subd3_5 [1, 0] = true := by decide +kernel
theorem subd3_5_42 : subd3_5 [1, 1] = true := by decide +kernel
theorem subd3_5_43 : subd3_5 [1, 2] = true := by decide +kernel
theorem subd3_5_44 : subd3_5 [1, 3] = true := by decide +kernel
theorem subd3_5_45 : subd3_5 [2, -5] = true := by decide +kernel
theorem subd3_5_46 : subd3_5 [2, -4] = true := by decide +kernel
theorem subd3_5_47 : subd3_5 [2, -3] = true := by decide +kernel
theorem subd3_5_48 : subd3_5 [2, -2] = true := by decide +kernel
theorem subd3_5_49 : subd3_5 [2, -1] = true := by decide +kernel
theorem subd3_5_50 : subd3_5 [2, 0] = true := by decide +kernel
theorem subd3_5_51 : subd3_5 [2, 1] = true := by decide +kernel
theorem subd3_5_52 : subd3_5 [2, 2] = true := by decide +kernel
theorem subd3_5_53 : subd3_5 [2, 3] = true := by decide +kernel
theorem subd3_5_54 : subd3_5 [3, -5] = true := by decide +kernel
theorem subd3_5_55 : subd3_5 [3, -4] = true := by decide +kernel
theorem subd3_5_56 : subd3_5 [3, -3] = true := by decide +kernel
theorem subd3_5_57 : subd3_5 [3, -2] = true := by decide +kernel
theorem subd3_5_58 : subd3_5 [3, -1] = true := by decide +kernel
theorem subd3_5_59 : subd3_5 [3, 0] = true := by decide +kernel
theorem subd3_5_60 : subd3_5 [3, 1] = true := by decide +kernel
theorem subd3_5_61 : subd3_5 [4] = true := by decide +kernel
theorem sbd3_5_1 : ∀ q ∈ blkd3_5_1, subd3_5 q = true := by
  unfold blkd3_5_1
  exact List.forall_mem_cons.2 ⟨subd3_5_32, List.forall_mem_cons.2 ⟨subd3_5_33, List.forall_mem_cons.2 ⟨subd3_5_34, List.forall_mem_cons.2 ⟨subd3_5_35, List.forall_mem_cons.2 ⟨subd3_5_36, List.forall_mem_cons.2 ⟨subd3_5_37, List.forall_mem_cons.2 ⟨subd3_5_38, List.forall_mem_cons.2 ⟨subd3_5_39, List.forall_mem_cons.2 ⟨subd3_5_40, List.forall_mem_cons.2 ⟨subd3_5_41, List.forall_mem_cons.2 ⟨subd3_5_42, List.forall_mem_cons.2 ⟨subd3_5_43, List.forall_mem_cons.2 ⟨subd3_5_44, List.forall_mem_cons.2 ⟨subd3_5_45, List.forall_mem_cons.2 ⟨subd3_5_46, List.forall_mem_cons.2 ⟨subd3_5_47, List.forall_mem_cons.2 ⟨subd3_5_48, List.forall_mem_cons.2 ⟨subd3_5_49, List.forall_mem_cons.2 ⟨subd3_5_50, List.forall_mem_cons.2 ⟨subd3_5_51, List.forall_mem_cons.2 ⟨subd3_5_52, List.forall_mem_cons.2 ⟨subd3_5_53, List.forall_mem_cons.2 ⟨subd3_5_54, List.forall_mem_cons.2 ⟨subd3_5_55, List.forall_mem_cons.2 ⟨subd3_5_56, List.forall_mem_cons.2 ⟨subd3_5_57, List.forall_mem_cons.2 ⟨subd3_5_58, List.forall_mem_cons.2 ⟨subd3_5_59, List.forall_mem_cons.2 ⟨subd3_5_60, List.forall_mem_cons.2 ⟨subd3_5_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel
theorem subd3_6_0 : subd3_6 [-5] = true := by decide +kernel
theorem subd3_6_1 : subd3_6 [-4, -3] = true := by decide +kernel
theorem subd3_6_2 : subd3_6 [-4, -2] = true := by decide +kernel
theorem subd3_6_3 : subd3_6 [-4, -1] = true := by decide +kernel
theorem subd3_6_4 : subd3_6 [-4, 0] = true := by decide +kernel
theorem subd3_6_5 : subd3_6 [-4, 1] = true := by decide +kernel
theorem subd3_6_6 : subd3_6 [-4, 2] = true := by decide +kernel
theorem subd3_6_7 : subd3_6 [-4, 3] = true := by decide +kernel
theorem subd3_6_8 : subd3_6 [-4, 4] = true := by decide +kernel
theorem subd3_6_9 : subd3_6 [-4, 5] = true := by decide +kernel
theorem subd3_6_10 : subd3_6 [-3, -5] = true := by decide +kernel
theorem subd3_6_11 : subd3_6 [-3, -4] = true := by decide +kernel
theorem subd3_6_12 : subd3_6 [-3, -3] = true := by decide +kernel
theorem subd3_6_13 : subd3_6 [-3, -2] = true := by decide +kernel
theorem subd3_6_14 : subd3_6 [-3, -1] = true := by decide +kernel
theorem subd3_6_15 : subd3_6 [-3, 0] = true := by decide +kernel
theorem subd3_6_16 : subd3_6 [-3, 1] = true := by decide +kernel
theorem subd3_6_17 : subd3_6 [-3, 2] = true := by decide +kernel
theorem subd3_6_18 : subd3_6 [-3, 3] = true := by decide +kernel
theorem subd3_6_19 : subd3_6 [-3, 4] = true := by decide +kernel
theorem subd3_6_20 : subd3_6 [-3, 5] = true := by decide +kernel
theorem subd3_6_21 : subd3_6 [-3, 6] = true := by decide +kernel
theorem subd3_6_22 : subd3_6 [-2, -6] = true := by decide +kernel
theorem subd3_6_23 : subd3_6 [-2, -5] = true := by decide +kernel
theorem subd3_6_24 : subd3_6 [-2, -4] = true := by decide +kernel
theorem subd3_6_25 : subd3_6 [-2, -3] = true := by decide +kernel
theorem subd3_6_26 : subd3_6 [-2, -2] = true := by decide +kernel
theorem subd3_6_27 : subd3_6 [-2, -1] = true := by decide +kernel
theorem subd3_6_28 : subd3_6 [-2, 0] = true := by decide +kernel
theorem subd3_6_29 : subd3_6 [-2, 1] = true := by decide +kernel
theorem subd3_6_30 : subd3_6 [-2, 2] = true := by decide +kernel
theorem subd3_6_31 : subd3_6 [-2, 3] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_cons.2 ⟨subd3_6_1, List.forall_mem_cons.2 ⟨subd3_6_2, List.forall_mem_cons.2 ⟨subd3_6_3, List.forall_mem_cons.2 ⟨subd3_6_4, List.forall_mem_cons.2 ⟨subd3_6_5, List.forall_mem_cons.2 ⟨subd3_6_6, List.forall_mem_cons.2 ⟨subd3_6_7, List.forall_mem_cons.2 ⟨subd3_6_8, List.forall_mem_cons.2 ⟨subd3_6_9, List.forall_mem_cons.2 ⟨subd3_6_10, List.forall_mem_cons.2 ⟨subd3_6_11, List.forall_mem_cons.2 ⟨subd3_6_12, List.forall_mem_cons.2 ⟨subd3_6_13, List.forall_mem_cons.2 ⟨subd3_6_14, List.forall_mem_cons.2 ⟨subd3_6_15, List.forall_mem_cons.2 ⟨subd3_6_16, List.forall_mem_cons.2 ⟨subd3_6_17, List.forall_mem_cons.2 ⟨subd3_6_18, List.forall_mem_cons.2 ⟨subd3_6_19, List.forall_mem_cons.2 ⟨subd3_6_20, List.forall_mem_cons.2 ⟨subd3_6_21, List.forall_mem_cons.2 ⟨subd3_6_22, List.forall_mem_cons.2 ⟨subd3_6_23, List.forall_mem_cons.2 ⟨subd3_6_24, List.forall_mem_cons.2 ⟨subd3_6_25, List.forall_mem_cons.2 ⟨subd3_6_26, List.forall_mem_cons.2 ⟨subd3_6_27, List.forall_mem_cons.2 ⟨subd3_6_28, List.forall_mem_cons.2 ⟨subd3_6_29, List.forall_mem_cons.2 ⟨subd3_6_30, List.forall_mem_cons.2 ⟨subd3_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
