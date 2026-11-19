import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-1] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [0, -1] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [0, 0] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [0, 1] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [1] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-3, -3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-3, -2] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-3, -1] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-3, 0] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-3, 1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-3, 2] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-2, -4] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-2, -3] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [-2, -2] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [-2, -1] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [-2, 0] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [-2, 1] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [-2, 2] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [-2, 3] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [-1, -4] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [-1, 3] = true := by decide +kernel
theorem subd8_0_22 : subd8_0 [0, -4] = true := by decide +kernel
theorem subd8_0_23 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_24 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_25 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_26 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_27 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_28 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_29 : subd8_0 [0, 3] = true := by decide +kernel
theorem subd8_0_30 : subd8_0 [1, -4] = true := by decide +kernel
theorem subd8_0_31 : subd8_0 [1, -3] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_cons.2 ⟨subd8_0_22, List.forall_mem_cons.2 ⟨subd8_0_23, List.forall_mem_cons.2 ⟨subd8_0_24, List.forall_mem_cons.2 ⟨subd8_0_25, List.forall_mem_cons.2 ⟨subd8_0_26, List.forall_mem_cons.2 ⟨subd8_0_27, List.forall_mem_cons.2 ⟨subd8_0_28, List.forall_mem_cons.2 ⟨subd8_0_29, List.forall_mem_cons.2 ⟨subd8_0_30, List.forall_mem_cons.2 ⟨subd8_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_32 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_33 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_34 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_35 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_36 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_37 : subd8_0 [1, 3] = true := by decide +kernel
theorem subd8_0_38 : subd8_0 [2, -4] = true := by decide +kernel
theorem subd8_0_39 : subd8_0 [2, -3] = true := by decide +kernel
theorem subd8_0_40 : subd8_0 [2, -2] = true := by decide +kernel
theorem subd8_0_41 : subd8_0 [2, -1] = true := by decide +kernel
theorem subd8_0_42 : subd8_0 [2, 0] = true := by decide +kernel
theorem subd8_0_43 : subd8_0 [2, 1] = true := by decide +kernel
theorem subd8_0_44 : subd8_0 [2, 2] = true := by decide +kernel
theorem subd8_0_45 : subd8_0 [2, 3] = true := by decide +kernel
theorem subd8_0_46 : subd8_0 [3, -3] = true := by decide +kernel
theorem subd8_0_47 : subd8_0 [3, -2] = true := by decide +kernel
theorem subd8_0_48 : subd8_0 [3, -1] = true := by decide +kernel
theorem subd8_0_49 : subd8_0 [3, 0] = true := by decide +kernel
theorem subd8_0_50 : subd8_0 [3, 1] = true := by decide +kernel
theorem subd8_0_51 : subd8_0 [3, 2] = true := by decide +kernel
theorem sbd8_0_1 : ∀ q ∈ blkd8_0_1, subd8_0 q = true := by
  unfold blkd8_0_1
  exact List.forall_mem_cons.2 ⟨subd8_0_32, List.forall_mem_cons.2 ⟨subd8_0_33, List.forall_mem_cons.2 ⟨subd8_0_34, List.forall_mem_cons.2 ⟨subd8_0_35, List.forall_mem_cons.2 ⟨subd8_0_36, List.forall_mem_cons.2 ⟨subd8_0_37, List.forall_mem_cons.2 ⟨subd8_0_38, List.forall_mem_cons.2 ⟨subd8_0_39, List.forall_mem_cons.2 ⟨subd8_0_40, List.forall_mem_cons.2 ⟨subd8_0_41, List.forall_mem_cons.2 ⟨subd8_0_42, List.forall_mem_cons.2 ⟨subd8_0_43, List.forall_mem_cons.2 ⟨subd8_0_44, List.forall_mem_cons.2 ⟨subd8_0_45, List.forall_mem_cons.2 ⟨subd8_0_46, List.forall_mem_cons.2 ⟨subd8_0_47, List.forall_mem_cons.2 ⟨subd8_0_48, List.forall_mem_cons.2 ⟨subd8_0_49, List.forall_mem_cons.2 ⟨subd8_0_50, List.forall_mem_cons.2 ⟨subd8_0_51, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-3] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-2, 3] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-2, 4] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [-1, 4] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [0, -5] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [0, 4] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [1, -5] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [1, -2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [2, -5] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [3] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
