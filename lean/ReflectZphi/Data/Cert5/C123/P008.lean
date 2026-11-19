import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_5_0 : subd4_5 [-4] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [-3, -4] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [-3, -3] = true := by decide +kernel
theorem subd4_5_3 : subd4_5 [-3, -2] = true := by decide +kernel
theorem subd4_5_4 : subd4_5 [-3, -1] = true := by decide +kernel
theorem subd4_5_5 : subd4_5 [-3, 0] = true := by decide +kernel
theorem subd4_5_6 : subd4_5 [-3, 1] = true := by decide +kernel
theorem subd4_5_7 : subd4_5 [-3, 2] = true := by decide +kernel
theorem subd4_5_8 : subd4_5 [-2, -5] = true := by decide +kernel
theorem subd4_5_9 : subd4_5 [-2, -4] = true := by decide +kernel
theorem subd4_5_10 : subd4_5 [-2, -3] = true := by decide +kernel
theorem subd4_5_11 : subd4_5 [-2, -2] = true := by decide +kernel
theorem subd4_5_12 : subd4_5 [-2, -1] = true := by decide +kernel
theorem subd4_5_13 : subd4_5 [-2, 0] = true := by decide +kernel
theorem subd4_5_14 : subd4_5 [-2, 1] = true := by decide +kernel
theorem subd4_5_15 : subd4_5 [-2, 2] = true := by decide +kernel
theorem subd4_5_16 : subd4_5 [-2, 3] = true := by decide +kernel
theorem subd4_5_17 : subd4_5 [-1, -5] = true := by decide +kernel
theorem subd4_5_18 : subd4_5 [-1, -4] = true := by decide +kernel
theorem subd4_5_19 : subd4_5 [-1, -3] = true := by decide +kernel
theorem subd4_5_20 : subd4_5 [-1, -2] = true := by decide +kernel
theorem subd4_5_21 : subd4_5 [-1, -1] = true := by decide +kernel
theorem subd4_5_22 : subd4_5 [-1, 0] = true := by decide +kernel
theorem subd4_5_23 : subd4_5 [-1, 1] = true := by decide +kernel
theorem subd4_5_24 : subd4_5 [-1, 2] = true := by decide +kernel
theorem subd4_5_25 : subd4_5 [-1, 3] = true := by decide +kernel
theorem subd4_5_26 : subd4_5 [0, -4] = true := by decide +kernel
theorem subd4_5_27 : subd4_5 [0, -3] = true := by decide +kernel
theorem subd4_5_28 : subd4_5 [0, -2] = true := by decide +kernel
theorem subd4_5_29 : subd4_5 [0, -1] = true := by decide +kernel
theorem subd4_5_30 : subd4_5 [0, 0] = true := by decide +kernel
theorem subd4_5_31 : subd4_5 [0, 1] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_cons.2 ⟨subd4_5_3, List.forall_mem_cons.2 ⟨subd4_5_4, List.forall_mem_cons.2 ⟨subd4_5_5, List.forall_mem_cons.2 ⟨subd4_5_6, List.forall_mem_cons.2 ⟨subd4_5_7, List.forall_mem_cons.2 ⟨subd4_5_8, List.forall_mem_cons.2 ⟨subd4_5_9, List.forall_mem_cons.2 ⟨subd4_5_10, List.forall_mem_cons.2 ⟨subd4_5_11, List.forall_mem_cons.2 ⟨subd4_5_12, List.forall_mem_cons.2 ⟨subd4_5_13, List.forall_mem_cons.2 ⟨subd4_5_14, List.forall_mem_cons.2 ⟨subd4_5_15, List.forall_mem_cons.2 ⟨subd4_5_16, List.forall_mem_cons.2 ⟨subd4_5_17, List.forall_mem_cons.2 ⟨subd4_5_18, List.forall_mem_cons.2 ⟨subd4_5_19, List.forall_mem_cons.2 ⟨subd4_5_20, List.forall_mem_cons.2 ⟨subd4_5_21, List.forall_mem_cons.2 ⟨subd4_5_22, List.forall_mem_cons.2 ⟨subd4_5_23, List.forall_mem_cons.2 ⟨subd4_5_24, List.forall_mem_cons.2 ⟨subd4_5_25, List.forall_mem_cons.2 ⟨subd4_5_26, List.forall_mem_cons.2 ⟨subd4_5_27, List.forall_mem_cons.2 ⟨subd4_5_28, List.forall_mem_cons.2 ⟨subd4_5_29, List.forall_mem_cons.2 ⟨subd4_5_30, List.forall_mem_cons.2 ⟨subd4_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_32 : subd4_5 [0, 2] = true := by decide +kernel
theorem subd4_5_33 : subd4_5 [0, 3] = true := by decide +kernel
theorem subd4_5_34 : subd4_5 [1, -4] = true := by decide +kernel
theorem subd4_5_35 : subd4_5 [1, -3] = true := by decide +kernel
theorem subd4_5_36 : subd4_5 [1, -2] = true := by decide +kernel
theorem subd4_5_37 : subd4_5 [1, -1] = true := by decide +kernel
theorem subd4_5_38 : subd4_5 [1, 0] = true := by decide +kernel
theorem subd4_5_39 : subd4_5 [1, 1] = true := by decide +kernel
theorem subd4_5_40 : subd4_5 [1, 2] = true := by decide +kernel
theorem subd4_5_41 : subd4_5 [1, 3] = true := by decide +kernel
theorem subd4_5_42 : subd4_5 [1, 4] = true := by decide +kernel
theorem subd4_5_43 : subd4_5 [2, -4] = true := by decide +kernel
theorem subd4_5_44 : subd4_5 [2, -3] = true := by decide +kernel
theorem subd4_5_45 : subd4_5 [2, -2] = true := by decide +kernel
theorem subd4_5_46 : subd4_5 [2, -1] = true := by decide +kernel
theorem subd4_5_47 : subd4_5 [2, 0] = true := by decide +kernel
theorem subd4_5_48 : subd4_5 [2, 1] = true := by decide +kernel
theorem subd4_5_49 : subd4_5 [2, 2] = true := by decide +kernel
theorem subd4_5_50 : subd4_5 [2, 3] = true := by decide +kernel
theorem subd4_5_51 : subd4_5 [2, 4] = true := by decide +kernel
theorem subd4_5_52 : subd4_5 [3, -3] = true := by decide +kernel
theorem subd4_5_53 : subd4_5 [3, -2] = true := by decide +kernel
theorem subd4_5_54 : subd4_5 [3, -1] = true := by decide +kernel
theorem subd4_5_55 : subd4_5 [3, 0] = true := by decide +kernel
theorem subd4_5_56 : subd4_5 [3, 1] = true := by decide +kernel
theorem subd4_5_57 : subd4_5 [3, 2] = true := by decide +kernel
theorem subd4_5_58 : subd4_5 [3, 3] = true := by decide +kernel
theorem subd4_5_59 : subd4_5 [4] = true := by decide +kernel
theorem sbd4_5_1 : ∀ q ∈ blkd4_5_1, subd4_5 q = true := by
  unfold blkd4_5_1
  exact List.forall_mem_cons.2 ⟨subd4_5_32, List.forall_mem_cons.2 ⟨subd4_5_33, List.forall_mem_cons.2 ⟨subd4_5_34, List.forall_mem_cons.2 ⟨subd4_5_35, List.forall_mem_cons.2 ⟨subd4_5_36, List.forall_mem_cons.2 ⟨subd4_5_37, List.forall_mem_cons.2 ⟨subd4_5_38, List.forall_mem_cons.2 ⟨subd4_5_39, List.forall_mem_cons.2 ⟨subd4_5_40, List.forall_mem_cons.2 ⟨subd4_5_41, List.forall_mem_cons.2 ⟨subd4_5_42, List.forall_mem_cons.2 ⟨subd4_5_43, List.forall_mem_cons.2 ⟨subd4_5_44, List.forall_mem_cons.2 ⟨subd4_5_45, List.forall_mem_cons.2 ⟨subd4_5_46, List.forall_mem_cons.2 ⟨subd4_5_47, List.forall_mem_cons.2 ⟨subd4_5_48, List.forall_mem_cons.2 ⟨subd4_5_49, List.forall_mem_cons.2 ⟨subd4_5_50, List.forall_mem_cons.2 ⟨subd4_5_51, List.forall_mem_cons.2 ⟨subd4_5_52, List.forall_mem_cons.2 ⟨subd4_5_53, List.forall_mem_cons.2 ⟨subd4_5_54, List.forall_mem_cons.2 ⟨subd4_5_55, List.forall_mem_cons.2 ⟨subd4_5_56, List.forall_mem_cons.2 ⟨subd4_5_57, List.forall_mem_cons.2 ⟨subd4_5_58, List.forall_mem_cons.2 ⟨subd4_5_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-5] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-4, -3] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [-4, -2] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [-4, -1] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [-4, 0] = true := by decide +kernel
theorem subd4_6_5 : subd4_6 [-4, 1] = true := by decide +kernel
theorem subd4_6_6 : subd4_6 [-4, 2] = true := by decide +kernel
theorem subd4_6_7 : subd4_6 [-4, 3] = true := by decide +kernel
theorem subd4_6_8 : subd4_6 [-4, 4] = true := by decide +kernel
theorem subd4_6_9 : subd4_6 [-4, 5] = true := by decide +kernel
theorem subd4_6_10 : subd4_6 [-3, -5] = true := by decide +kernel
theorem subd4_6_11 : subd4_6 [-3, -4] = true := by decide +kernel
theorem subd4_6_12 : subd4_6 [-3, -3] = true := by decide +kernel
theorem subd4_6_13 : subd4_6 [-3, -2] = true := by decide +kernel
theorem subd4_6_14 : subd4_6 [-3, -1] = true := by decide +kernel
theorem subd4_6_15 : subd4_6 [-3, 0] = true := by decide +kernel
theorem subd4_6_16 : subd4_6 [-3, 1] = true := by decide +kernel
theorem subd4_6_17 : subd4_6 [-3, 2] = true := by decide +kernel
theorem subd4_6_18 : subd4_6 [-3, 3] = true := by decide +kernel
theorem subd4_6_19 : subd4_6 [-3, 4] = true := by decide +kernel
theorem subd4_6_20 : subd4_6 [-3, 5] = true := by decide +kernel
theorem subd4_6_21 : subd4_6 [-2, -6] = true := by decide +kernel
theorem subd4_6_22 : subd4_6 [-2, -5] = true := by decide +kernel
theorem subd4_6_23 : subd4_6 [-2, -4] = true := by decide +kernel
theorem subd4_6_24 : subd4_6 [-2, -3] = true := by decide +kernel
theorem subd4_6_25 : subd4_6 [-2, -2] = true := by decide +kernel
theorem subd4_6_26 : subd4_6 [-2, -1] = true := by decide +kernel
theorem subd4_6_27 : subd4_6 [-2, 0] = true := by decide +kernel
theorem subd4_6_28 : subd4_6 [-2, 1] = true := by decide +kernel
theorem subd4_6_29 : subd4_6 [-2, 2] = true := by decide +kernel
theorem subd4_6_30 : subd4_6 [-2, 3] = true := by decide +kernel
theorem subd4_6_31 : subd4_6 [-2, 4] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_cons.2 ⟨subd4_6_5, List.forall_mem_cons.2 ⟨subd4_6_6, List.forall_mem_cons.2 ⟨subd4_6_7, List.forall_mem_cons.2 ⟨subd4_6_8, List.forall_mem_cons.2 ⟨subd4_6_9, List.forall_mem_cons.2 ⟨subd4_6_10, List.forall_mem_cons.2 ⟨subd4_6_11, List.forall_mem_cons.2 ⟨subd4_6_12, List.forall_mem_cons.2 ⟨subd4_6_13, List.forall_mem_cons.2 ⟨subd4_6_14, List.forall_mem_cons.2 ⟨subd4_6_15, List.forall_mem_cons.2 ⟨subd4_6_16, List.forall_mem_cons.2 ⟨subd4_6_17, List.forall_mem_cons.2 ⟨subd4_6_18, List.forall_mem_cons.2 ⟨subd4_6_19, List.forall_mem_cons.2 ⟨subd4_6_20, List.forall_mem_cons.2 ⟨subd4_6_21, List.forall_mem_cons.2 ⟨subd4_6_22, List.forall_mem_cons.2 ⟨subd4_6_23, List.forall_mem_cons.2 ⟨subd4_6_24, List.forall_mem_cons.2 ⟨subd4_6_25, List.forall_mem_cons.2 ⟨subd4_6_26, List.forall_mem_cons.2 ⟨subd4_6_27, List.forall_mem_cons.2 ⟨subd4_6_28, List.forall_mem_cons.2 ⟨subd4_6_29, List.forall_mem_cons.2 ⟨subd4_6_30, List.forall_mem_cons.2 ⟨subd4_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_32 : subd4_6 [-2, 5] = true := by decide +kernel
theorem subd4_6_33 : subd4_6 [-2, 6] = true := by decide +kernel
theorem subd4_6_34 : subd4_6 [-1, -6] = true := by decide +kernel
theorem subd4_6_35 : subd4_6 [-1, -5] = true := by decide +kernel
theorem subd4_6_36 : subd4_6 [-1, -4] = true := by decide +kernel
theorem subd4_6_37 : subd4_6 [-1, -3] = true := by decide +kernel
theorem subd4_6_38 : subd4_6 [-1, -2] = true := by decide +kernel
theorem subd4_6_39 : subd4_6 [-1, -1] = true := by decide +kernel
theorem subd4_6_40 : subd4_6 [-1, 0] = true := by decide +kernel
theorem subd4_6_41 : subd4_6 [-1, 1] = true := by decide +kernel
theorem subd4_6_42 : subd4_6 [-1, 2] = true := by decide +kernel
theorem subd4_6_43 : subd4_6 [-1, 3] = true := by decide +kernel
theorem subd4_6_44 : subd4_6 [-1, 4] = true := by decide +kernel
theorem subd4_6_45 : subd4_6 [-1, 5] = true := by decide +kernel
theorem subd4_6_46 : subd4_6 [-1, 6] = true := by decide +kernel
theorem subd4_6_47 : subd4_6 [0, -7] = true := by decide +kernel
theorem subd4_6_48 : subd4_6 [0, -6] = true := by decide +kernel
theorem subd4_6_49 : subd4_6 [0, -5] = true := by decide +kernel
theorem subd4_6_50 : subd4_6 [0, -4] = true := by decide +kernel
theorem subd4_6_51 : subd4_6 [0, -3] = true := by decide +kernel
theorem subd4_6_52 : subd4_6 [0, -2] = true := by decide +kernel
theorem subd4_6_53 : subd4_6 [0, -1] = true := by decide +kernel
theorem subd4_6_54 : subd4_6 [0, 0] = true := by decide +kernel
theorem subd4_6_55 : subd4_6 [0, 1] = true := by decide +kernel
theorem subd4_6_56 : subd4_6 [0, 2] = true := by decide +kernel
theorem subd4_6_57 : subd4_6 [0, 3] = true := by decide +kernel
theorem subd4_6_58 : subd4_6 [0, 4] = true := by decide +kernel
theorem subd4_6_59 : subd4_6 [0, 5] = true := by decide +kernel
theorem subd4_6_60 : subd4_6 [0, 6] = true := by decide +kernel
theorem subd4_6_61 : subd4_6 [1, -7] = true := by decide +kernel
theorem subd4_6_62 : subd4_6 [1, -6] = true := by decide +kernel
theorem subd4_6_63 : subd4_6 [1, -5] = true := by decide +kernel
theorem sbd4_6_1 : ∀ q ∈ blkd4_6_1, subd4_6 q = true := by
  unfold blkd4_6_1
  exact List.forall_mem_cons.2 ⟨subd4_6_32, List.forall_mem_cons.2 ⟨subd4_6_33, List.forall_mem_cons.2 ⟨subd4_6_34, List.forall_mem_cons.2 ⟨subd4_6_35, List.forall_mem_cons.2 ⟨subd4_6_36, List.forall_mem_cons.2 ⟨subd4_6_37, List.forall_mem_cons.2 ⟨subd4_6_38, List.forall_mem_cons.2 ⟨subd4_6_39, List.forall_mem_cons.2 ⟨subd4_6_40, List.forall_mem_cons.2 ⟨subd4_6_41, List.forall_mem_cons.2 ⟨subd4_6_42, List.forall_mem_cons.2 ⟨subd4_6_43, List.forall_mem_cons.2 ⟨subd4_6_44, List.forall_mem_cons.2 ⟨subd4_6_45, List.forall_mem_cons.2 ⟨subd4_6_46, List.forall_mem_cons.2 ⟨subd4_6_47, List.forall_mem_cons.2 ⟨subd4_6_48, List.forall_mem_cons.2 ⟨subd4_6_49, List.forall_mem_cons.2 ⟨subd4_6_50, List.forall_mem_cons.2 ⟨subd4_6_51, List.forall_mem_cons.2 ⟨subd4_6_52, List.forall_mem_cons.2 ⟨subd4_6_53, List.forall_mem_cons.2 ⟨subd4_6_54, List.forall_mem_cons.2 ⟨subd4_6_55, List.forall_mem_cons.2 ⟨subd4_6_56, List.forall_mem_cons.2 ⟨subd4_6_57, List.forall_mem_cons.2 ⟨subd4_6_58, List.forall_mem_cons.2 ⟨subd4_6_59, List.forall_mem_cons.2 ⟨subd4_6_60, List.forall_mem_cons.2 ⟨subd4_6_61, List.forall_mem_cons.2 ⟨subd4_6_62, List.forall_mem_cons.2 ⟨subd4_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
