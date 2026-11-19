import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_0 : subd7_3 [-4] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-3, -5] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-3, -4] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-3, -3] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-3, -2] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-3, -1] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-3, 0] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-3, 1] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-3, 2] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-2, -5] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-2, -4] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-2, -3] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-2, -2] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-2, -1] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-2, 0] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-2, 1] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-2, 2] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-2, 3] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-1, -6] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-1, -5] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-1, -4] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-1, -2] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-1, -1] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-1, 0] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-1, 1] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-1, 2] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-1, 3] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-1, 4] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [0, -5] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [0, -4] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [0, -3] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [0, -1] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [0, 0] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [0, 1] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [0, 3] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [0, 4] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [1, -5] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [1, -4] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [1, -3] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [1, -2] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [1, -1] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [1, 0] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [1, 1] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [1, 2] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [1, 3] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [1, 4] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [1, 5] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [2, -4] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [2, -3] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [2, -2] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [2, -1] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [2, 0] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [2, 1] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [2, 2] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [2, 3] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [2, 4] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [3, -3] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [3, -2] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [3, -1] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [3, 0] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [3, 1] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_64 : subd7_3 [3, 2] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [3, 3] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [3, 4] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [4] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [0] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [1] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-3] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [2, 0] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [3] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C121
