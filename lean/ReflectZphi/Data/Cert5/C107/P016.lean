import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-1, 3] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [0, -4] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [0, 3] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [1, -4] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [1, 1] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [2] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-4] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-3, -3] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-3, -2] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-3, -1] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-3, 0] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-3, 1] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-3, 2] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-3, 3] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-3, 4] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-2, -4] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-2, -1] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-2, 0] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-2, 1] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [-2, 4] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [-2, 5] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [-1, -5] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [-1, 4] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [-1, 5] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [0, -5] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [0, -4] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [0, 4] = true := by decide +kernel
theorem subd8_3_40 : subd8_3 [1, -6] = true := by decide +kernel
theorem subd8_3_41 : subd8_3 [1, -5] = true := by decide +kernel
theorem subd8_3_42 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_43 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_44 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_45 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_46 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_47 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_48 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_49 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_50 : subd8_3 [1, 4] = true := by decide +kernel
theorem subd8_3_51 : subd8_3 [2, -6] = true := by decide +kernel
theorem subd8_3_52 : subd8_3 [2, -5] = true := by decide +kernel
theorem subd8_3_53 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_54 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_55 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_56 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_57 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_58 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_59 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_60 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_61 : subd8_3 [3, -5] = true := by decide +kernel
theorem subd8_3_62 : subd8_3 [3, -4] = true := by decide +kernel
theorem subd8_3_63 : subd8_3 [3, -3] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_cons.2 ⟨subd8_3_40, List.forall_mem_cons.2 ⟨subd8_3_41, List.forall_mem_cons.2 ⟨subd8_3_42, List.forall_mem_cons.2 ⟨subd8_3_43, List.forall_mem_cons.2 ⟨subd8_3_44, List.forall_mem_cons.2 ⟨subd8_3_45, List.forall_mem_cons.2 ⟨subd8_3_46, List.forall_mem_cons.2 ⟨subd8_3_47, List.forall_mem_cons.2 ⟨subd8_3_48, List.forall_mem_cons.2 ⟨subd8_3_49, List.forall_mem_cons.2 ⟨subd8_3_50, List.forall_mem_cons.2 ⟨subd8_3_51, List.forall_mem_cons.2 ⟨subd8_3_52, List.forall_mem_cons.2 ⟨subd8_3_53, List.forall_mem_cons.2 ⟨subd8_3_54, List.forall_mem_cons.2 ⟨subd8_3_55, List.forall_mem_cons.2 ⟨subd8_3_56, List.forall_mem_cons.2 ⟨subd8_3_57, List.forall_mem_cons.2 ⟨subd8_3_58, List.forall_mem_cons.2 ⟨subd8_3_59, List.forall_mem_cons.2 ⟨subd8_3_60, List.forall_mem_cons.2 ⟨subd8_3_61, List.forall_mem_cons.2 ⟨subd8_3_62, List.forall_mem_cons.2 ⟨subd8_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
