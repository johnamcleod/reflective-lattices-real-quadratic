import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-2] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [0, -1, -6] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [0, -1, -5] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [0, -1, -4] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [0, -1, -3] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, -1, -2] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [0, -1, -1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [0, -1, 0] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [0, -1, 1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [0, -1, 2] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [0, -1, 3] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [0, -1, 4] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [0, -1, 5] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [0, -1, 6] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [0, 0, -7] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [0, 0, -6] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [0, 0, -5] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [0, 0, -4] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [0, 0, -3] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [0, 0, -2] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [0, 0, -1] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [0, 0, 0] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [0, 0, 1] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [0, 0, 2] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [0, 0, 3] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [0, 0, 4] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [0, 0, 5] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [0, 0, 6] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [0, 1, -7] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [0, 1, -6] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [0, 1, -5] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [0, 1, -4] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [0, 1, -3] = true := by decide +kernel
theorem subd6_1_40 : subd6_1 [0, 1, -2] = true := by decide +kernel
theorem subd6_1_41 : subd6_1 [0, 1, -1] = true := by decide +kernel
theorem subd6_1_42 : subd6_1 [0, 1, 0] = true := by decide +kernel
theorem subd6_1_43 : subd6_1 [0, 1, 1] = true := by decide +kernel
theorem subd6_1_44 : subd6_1 [0, 1, 2] = true := by decide +kernel
theorem subd6_1_45 : subd6_1 [0, 1, 3] = true := by decide +kernel
theorem subd6_1_46 : subd6_1 [0, 1, 4] = true := by decide +kernel
theorem subd6_1_47 : subd6_1 [0, 1, 5] = true := by decide +kernel
theorem subd6_1_48 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_49 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_50 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_51 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_52 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_53 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_54 : subd6_1 [2] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_cons.2 ⟨subd6_1_40, List.forall_mem_cons.2 ⟨subd6_1_41, List.forall_mem_cons.2 ⟨subd6_1_42, List.forall_mem_cons.2 ⟨subd6_1_43, List.forall_mem_cons.2 ⟨subd6_1_44, List.forall_mem_cons.2 ⟨subd6_1_45, List.forall_mem_cons.2 ⟨subd6_1_46, List.forall_mem_cons.2 ⟨subd6_1_47, List.forall_mem_cons.2 ⟨subd6_1_48, List.forall_mem_cons.2 ⟨subd6_1_49, List.forall_mem_cons.2 ⟨subd6_1_50, List.forall_mem_cons.2 ⟨subd6_1_51, List.forall_mem_cons.2 ⟨subd6_1_52, List.forall_mem_cons.2 ⟨subd6_1_53, List.forall_mem_cons.2 ⟨subd6_1_54, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2, -3] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-2, -2] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-2, -1] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-2, 0] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-2, 1] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-2, 2] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-2, 3] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-2, 4] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-1, -4] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [-1, 4] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [0, -5] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [0, 4] = true := by decide +kernel
theorem subd6_2_28 : subd6_2 [1, -5] = true := by decide +kernel
theorem subd6_2_29 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_30 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_31 : subd6_2 [1, -2] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_cons.2 ⟨subd6_2_28, List.forall_mem_cons.2 ⟨subd6_2_29, List.forall_mem_cons.2 ⟨subd6_2_30, List.forall_mem_cons.2 ⟨subd6_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_32 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_33 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_34 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_35 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_36 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_37 : subd6_2 [2, -5] = true := by decide +kernel
theorem subd6_2_38 : subd6_2 [2, -4] = true := by decide +kernel
theorem subd6_2_39 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_40 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_41 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_42 : subd6_2 [2, 0] = true := by decide +kernel
theorem subd6_2_43 : subd6_2 [2, 1] = true := by decide +kernel
theorem subd6_2_44 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_45 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_1 : ∀ q ∈ blkd6_2_1, subd6_2 q = true := by
  unfold blkd6_2_1
  exact List.forall_mem_cons.2 ⟨subd6_2_32, List.forall_mem_cons.2 ⟨subd6_2_33, List.forall_mem_cons.2 ⟨subd6_2_34, List.forall_mem_cons.2 ⟨subd6_2_35, List.forall_mem_cons.2 ⟨subd6_2_36, List.forall_mem_cons.2 ⟨subd6_2_37, List.forall_mem_cons.2 ⟨subd6_2_38, List.forall_mem_cons.2 ⟨subd6_2_39, List.forall_mem_cons.2 ⟨subd6_2_40, List.forall_mem_cons.2 ⟨subd6_2_41, List.forall_mem_cons.2 ⟨subd6_2_42, List.forall_mem_cons.2 ⟨subd6_2_43, List.forall_mem_cons.2 ⟨subd6_2_44, List.forall_mem_cons.2 ⟨subd6_2_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-2] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-1] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [0] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [1] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [2] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
