import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_32 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [0, 4] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [1, -4] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [1, -1] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [1, 0] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [1, 1] = true := by decide +kernel
theorem subd10_1_42 : subd10_1 [1, 2] = true := by decide +kernel
theorem subd10_1_43 : subd10_1 [1, 3] = true := by decide +kernel
theorem subd10_1_44 : subd10_1 [1, 4] = true := by decide +kernel
theorem subd10_1_45 : subd10_1 [2, -4] = true := by decide +kernel
theorem subd10_1_46 : subd10_1 [2, -3] = true := by decide +kernel
theorem subd10_1_47 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_48 : subd10_1 [2, -1] = true := by decide +kernel
theorem subd10_1_49 : subd10_1 [2, 0] = true := by decide +kernel
theorem subd10_1_50 : subd10_1 [2, 1] = true := by decide +kernel
theorem subd10_1_51 : subd10_1 [2, 2] = true := by decide +kernel
theorem subd10_1_52 : subd10_1 [2, 3] = true := by decide +kernel
theorem subd10_1_53 : subd10_1 [2, 4] = true := by decide +kernel
theorem subd10_1_54 : subd10_1 [3, -3] = true := by decide +kernel
theorem subd10_1_55 : subd10_1 [3, -2] = true := by decide +kernel
theorem subd10_1_56 : subd10_1 [3, -1] = true := by decide +kernel
theorem subd10_1_57 : subd10_1 [3, 0] = true := by decide +kernel
theorem subd10_1_58 : subd10_1 [3, 1] = true := by decide +kernel
theorem subd10_1_59 : subd10_1 [3, 2] = true := by decide +kernel
theorem subd10_1_60 : subd10_1 [3, 3] = true := by decide +kernel
theorem subd10_1_61 : subd10_1 [4] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_cons.2 ⟨subd10_1_42, List.forall_mem_cons.2 ⟨subd10_1_43, List.forall_mem_cons.2 ⟨subd10_1_44, List.forall_mem_cons.2 ⟨subd10_1_45, List.forall_mem_cons.2 ⟨subd10_1_46, List.forall_mem_cons.2 ⟨subd10_1_47, List.forall_mem_cons.2 ⟨subd10_1_48, List.forall_mem_cons.2 ⟨subd10_1_49, List.forall_mem_cons.2 ⟨subd10_1_50, List.forall_mem_cons.2 ⟨subd10_1_51, List.forall_mem_cons.2 ⟨subd10_1_52, List.forall_mem_cons.2 ⟨subd10_1_53, List.forall_mem_cons.2 ⟨subd10_1_54, List.forall_mem_cons.2 ⟨subd10_1_55, List.forall_mem_cons.2 ⟨subd10_1_56, List.forall_mem_cons.2 ⟨subd10_1_57, List.forall_mem_cons.2 ⟨subd10_1_58, List.forall_mem_cons.2 ⟨subd10_1_59, List.forall_mem_cons.2 ⟨subd10_1_60, List.forall_mem_cons.2 ⟨subd10_1_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-3] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-2, -2] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-2, -1] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-2, 0] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-2, 1] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-2, 2] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-1, -3] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-1, -2] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [-1, -1] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [-1, 0] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [-1, 1] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [-1, 2] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [1, -3] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [1, -2] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [1, -1] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [1, 0] = true := by decide +kernel
theorem subd10_2_22 : subd10_2 [1, 1] = true := by decide +kernel
theorem subd10_2_23 : subd10_2 [1, 2] = true := by decide +kernel
theorem subd10_2_24 : subd10_2 [2, -3] = true := by decide +kernel
theorem subd10_2_25 : subd10_2 [2, -2] = true := by decide +kernel
theorem subd10_2_26 : subd10_2 [2, -1] = true := by decide +kernel
theorem subd10_2_27 : subd10_2 [2, 0] = true := by decide +kernel
theorem subd10_2_28 : subd10_2 [2, 1] = true := by decide +kernel
theorem subd10_2_29 : subd10_2 [3] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_cons.2 ⟨subd10_2_22, List.forall_mem_cons.2 ⟨subd10_2_23, List.forall_mem_cons.2 ⟨subd10_2_24, List.forall_mem_cons.2 ⟨subd10_2_25, List.forall_mem_cons.2 ⟨subd10_2_26, List.forall_mem_cons.2 ⟨subd10_2_27, List.forall_mem_cons.2 ⟨subd10_2_28, List.forall_mem_cons.2 ⟨subd10_2_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-4] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-3, -2] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-3, -1] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-3, 0] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-3, 1] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-3, 2] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-3, 3] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-3, 4] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-2, -3] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-2, -1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-2, 0] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-2, 1] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-2, 2] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-2, 3] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-2, 4] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-1, -4] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [-1, 3] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [0, -4] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [0, 3] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_32 : subd10_3 [1, -4] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [1, 3] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [2, -5] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [2, -4] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [2, -3] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [2, -2] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [2, -1] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [2, 0] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [2, 1] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [3, -5] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [3, -4] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [3, -3] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [3, -2] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [3, -1] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [3, 0] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [3, 1] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [4] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C130
