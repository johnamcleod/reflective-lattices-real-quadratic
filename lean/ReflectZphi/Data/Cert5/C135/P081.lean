import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_0_0 : subd13_0 [-3] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [-2] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [-1, -4] = true := by decide +kernel
theorem subd13_0_3 : subd13_0 [-1, -3] = true := by decide +kernel
theorem subd13_0_4 : subd13_0 [-1, -2] = true := by decide +kernel
theorem subd13_0_5 : subd13_0 [-1, -1] = true := by decide +kernel
theorem subd13_0_6 : subd13_0 [-1, 0] = true := by decide +kernel
theorem subd13_0_7 : subd13_0 [-1, 1] = true := by decide +kernel
theorem subd13_0_8 : subd13_0 [-1, 2] = true := by decide +kernel
theorem subd13_0_9 : subd13_0 [0, -4] = true := by decide +kernel
theorem subd13_0_10 : subd13_0 [0, -3] = true := by decide +kernel
theorem subd13_0_11 : subd13_0 [0, -2] = true := by decide +kernel
theorem subd13_0_12 : subd13_0 [0, -1] = true := by decide +kernel
theorem subd13_0_13 : subd13_0 [0, 0] = true := by decide +kernel
theorem subd13_0_14 : subd13_0 [0, 1] = true := by decide +kernel
theorem subd13_0_15 : subd13_0 [0, 2] = true := by decide +kernel
theorem subd13_0_16 : subd13_0 [0, 3] = true := by decide +kernel
theorem subd13_0_17 : subd13_0 [1, -3] = true := by decide +kernel
theorem subd13_0_18 : subd13_0 [1, -2] = true := by decide +kernel
theorem subd13_0_19 : subd13_0 [1, -1] = true := by decide +kernel
theorem subd13_0_20 : subd13_0 [1, 0] = true := by decide +kernel
theorem subd13_0_21 : subd13_0 [1, 1] = true := by decide +kernel
theorem subd13_0_22 : subd13_0 [1, 2] = true := by decide +kernel
theorem subd13_0_23 : subd13_0 [1, 3] = true := by decide +kernel
theorem subd13_0_24 : subd13_0 [2] = true := by decide +kernel
theorem subd13_0_25 : subd13_0 [3] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_cons.2 ⟨subd13_0_3, List.forall_mem_cons.2 ⟨subd13_0_4, List.forall_mem_cons.2 ⟨subd13_0_5, List.forall_mem_cons.2 ⟨subd13_0_6, List.forall_mem_cons.2 ⟨subd13_0_7, List.forall_mem_cons.2 ⟨subd13_0_8, List.forall_mem_cons.2 ⟨subd13_0_9, List.forall_mem_cons.2 ⟨subd13_0_10, List.forall_mem_cons.2 ⟨subd13_0_11, List.forall_mem_cons.2 ⟨subd13_0_12, List.forall_mem_cons.2 ⟨subd13_0_13, List.forall_mem_cons.2 ⟨subd13_0_14, List.forall_mem_cons.2 ⟨subd13_0_15, List.forall_mem_cons.2 ⟨subd13_0_16, List.forall_mem_cons.2 ⟨subd13_0_17, List.forall_mem_cons.2 ⟨subd13_0_18, List.forall_mem_cons.2 ⟨subd13_0_19, List.forall_mem_cons.2 ⟨subd13_0_20, List.forall_mem_cons.2 ⟨subd13_0_21, List.forall_mem_cons.2 ⟨subd13_0_22, List.forall_mem_cons.2 ⟨subd13_0_23, List.forall_mem_cons.2 ⟨subd13_0_24, List.forall_mem_cons.2 ⟨subd13_0_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [-2] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-1, -3] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-1, -2] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [-1, -1] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [-1, 0] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [-1, 1] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [0, -3] = true := by decide +kernel
theorem subd13_1_7 : subd13_1 [0, -2] = true := by decide +kernel
theorem subd13_1_8 : subd13_1 [0, -1, -7] = true := by decide +kernel
theorem subd13_1_9 : subd13_1 [0, -1, -6] = true := by decide +kernel
theorem subd13_1_10 : subd13_1 [0, -1, -5] = true := by decide +kernel
theorem subd13_1_11 : subd13_1 [0, -1, -4] = true := by decide +kernel
theorem subd13_1_12 : subd13_1 [0, -1, -3] = true := by decide +kernel
theorem subd13_1_13 : subd13_1 [0, -1, -2] = true := by decide +kernel
theorem subd13_1_14 : subd13_1 [0, -1, -1] = true := by decide +kernel
theorem subd13_1_15 : subd13_1 [0, -1, 0] = true := by decide +kernel
theorem subd13_1_16 : subd13_1 [0, -1, 1] = true := by decide +kernel
theorem subd13_1_17 : subd13_1 [0, -1, 2] = true := by decide +kernel
theorem subd13_1_18 : subd13_1 [0, -1, 3] = true := by decide +kernel
theorem subd13_1_19 : subd13_1 [0, -1, 4] = true := by decide +kernel
theorem subd13_1_20 : subd13_1 [0, -1, 5] = true := by decide +kernel
theorem subd13_1_21 : subd13_1 [0, -1, 6] = true := by decide +kernel
theorem subd13_1_22 : subd13_1 [0, -1, 7] = true := by decide +kernel
theorem subd13_1_23 : subd13_1 [0, 0, -8] = true := by decide +kernel
theorem subd13_1_24 : subd13_1 [0, 0, -7] = true := by decide +kernel
theorem subd13_1_25 : subd13_1 [0, 0, -6] = true := by decide +kernel
theorem subd13_1_26 : subd13_1 [0, 0, -5] = true := by decide +kernel
theorem subd13_1_27 : subd13_1 [0, 0, -4] = true := by decide +kernel
theorem subd13_1_28 : subd13_1 [0, 0, -3] = true := by decide +kernel
theorem subd13_1_29 : subd13_1 [0, 0, -2] = true := by decide +kernel
theorem subd13_1_30 : subd13_1 [0, 0, -1] = true := by decide +kernel
theorem subd13_1_31 : subd13_1 [0, 0, 0] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_cons.2 ⟨subd13_1_7, List.forall_mem_cons.2 ⟨subd13_1_8, List.forall_mem_cons.2 ⟨subd13_1_9, List.forall_mem_cons.2 ⟨subd13_1_10, List.forall_mem_cons.2 ⟨subd13_1_11, List.forall_mem_cons.2 ⟨subd13_1_12, List.forall_mem_cons.2 ⟨subd13_1_13, List.forall_mem_cons.2 ⟨subd13_1_14, List.forall_mem_cons.2 ⟨subd13_1_15, List.forall_mem_cons.2 ⟨subd13_1_16, List.forall_mem_cons.2 ⟨subd13_1_17, List.forall_mem_cons.2 ⟨subd13_1_18, List.forall_mem_cons.2 ⟨subd13_1_19, List.forall_mem_cons.2 ⟨subd13_1_20, List.forall_mem_cons.2 ⟨subd13_1_21, List.forall_mem_cons.2 ⟨subd13_1_22, List.forall_mem_cons.2 ⟨subd13_1_23, List.forall_mem_cons.2 ⟨subd13_1_24, List.forall_mem_cons.2 ⟨subd13_1_25, List.forall_mem_cons.2 ⟨subd13_1_26, List.forall_mem_cons.2 ⟨subd13_1_27, List.forall_mem_cons.2 ⟨subd13_1_28, List.forall_mem_cons.2 ⟨subd13_1_29, List.forall_mem_cons.2 ⟨subd13_1_30, List.forall_mem_cons.2 ⟨subd13_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_32 : subd13_1 [0, 0, 1] = true := by decide +kernel
theorem subd13_1_33 : subd13_1 [0, 0, 2] = true := by decide +kernel
theorem subd13_1_34 : subd13_1 [0, 0, 3] = true := by decide +kernel
theorem subd13_1_35 : subd13_1 [0, 0, 4] = true := by decide +kernel
theorem subd13_1_36 : subd13_1 [0, 0, 5] = true := by decide +kernel
theorem subd13_1_37 : subd13_1 [0, 0, 6] = true := by decide +kernel
theorem subd13_1_38 : subd13_1 [0, 0, 7] = true := by decide +kernel
theorem subd13_1_39 : subd13_1 [0, 1, -8] = true := by decide +kernel
theorem subd13_1_40 : subd13_1 [0, 1, -7] = true := by decide +kernel
theorem subd13_1_41 : subd13_1 [0, 1, -6] = true := by decide +kernel
theorem subd13_1_42 : subd13_1 [0, 1, -5] = true := by decide +kernel
theorem subd13_1_43 : subd13_1 [0, 1, -4] = true := by decide +kernel
theorem subd13_1_44 : subd13_1 [0, 1, -3] = true := by decide +kernel
theorem subd13_1_45 : subd13_1 [0, 1, -2] = true := by decide +kernel
theorem subd13_1_46 : subd13_1 [0, 1, -1] = true := by decide +kernel
theorem subd13_1_47 : subd13_1 [0, 1, 0] = true := by decide +kernel
theorem subd13_1_48 : subd13_1 [0, 1, 1] = true := by decide +kernel
theorem subd13_1_49 : subd13_1 [0, 1, 2] = true := by decide +kernel
theorem subd13_1_50 : subd13_1 [0, 1, 3] = true := by decide +kernel
theorem subd13_1_51 : subd13_1 [0, 1, 4] = true := by decide +kernel
theorem subd13_1_52 : subd13_1 [0, 1, 5] = true := by decide +kernel
theorem subd13_1_53 : subd13_1 [0, 1, 6] = true := by decide +kernel
theorem subd13_1_54 : subd13_1 [0, 2] = true := by decide +kernel
theorem subd13_1_55 : subd13_1 [1, -2] = true := by decide +kernel
theorem subd13_1_56 : subd13_1 [1, -1] = true := by decide +kernel
theorem subd13_1_57 : subd13_1 [1, 0] = true := by decide +kernel
theorem subd13_1_58 : subd13_1 [1, 1] = true := by decide +kernel
theorem subd13_1_59 : subd13_1 [1, 2] = true := by decide +kernel
theorem subd13_1_60 : subd13_1 [2] = true := by decide +kernel
theorem sbd13_1_1 : ∀ q ∈ blkd13_1_1, subd13_1 q = true := by
  unfold blkd13_1_1
  exact List.forall_mem_cons.2 ⟨subd13_1_32, List.forall_mem_cons.2 ⟨subd13_1_33, List.forall_mem_cons.2 ⟨subd13_1_34, List.forall_mem_cons.2 ⟨subd13_1_35, List.forall_mem_cons.2 ⟨subd13_1_36, List.forall_mem_cons.2 ⟨subd13_1_37, List.forall_mem_cons.2 ⟨subd13_1_38, List.forall_mem_cons.2 ⟨subd13_1_39, List.forall_mem_cons.2 ⟨subd13_1_40, List.forall_mem_cons.2 ⟨subd13_1_41, List.forall_mem_cons.2 ⟨subd13_1_42, List.forall_mem_cons.2 ⟨subd13_1_43, List.forall_mem_cons.2 ⟨subd13_1_44, List.forall_mem_cons.2 ⟨subd13_1_45, List.forall_mem_cons.2 ⟨subd13_1_46, List.forall_mem_cons.2 ⟨subd13_1_47, List.forall_mem_cons.2 ⟨subd13_1_48, List.forall_mem_cons.2 ⟨subd13_1_49, List.forall_mem_cons.2 ⟨subd13_1_50, List.forall_mem_cons.2 ⟨subd13_1_51, List.forall_mem_cons.2 ⟨subd13_1_52, List.forall_mem_cons.2 ⟨subd13_1_53, List.forall_mem_cons.2 ⟨subd13_1_54, List.forall_mem_cons.2 ⟨subd13_1_55, List.forall_mem_cons.2 ⟨subd13_1_56, List.forall_mem_cons.2 ⟨subd13_1_57, List.forall_mem_cons.2 ⟨subd13_1_58, List.forall_mem_cons.2 ⟨subd13_1_59, List.forall_mem_cons.2 ⟨subd13_1_60, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-2, -2] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-2, -1] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [-2, 0] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [-2, 1] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [-2, 2] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [-1, -3] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [-1, -2] = true := by decide +kernel
theorem subd13_2_7 : subd13_2 [-1, -1] = true := by decide +kernel
theorem subd13_2_8 : subd13_2 [-1, 0] = true := by decide +kernel
theorem subd13_2_9 : subd13_2 [-1, 1] = true := by decide +kernel
theorem subd13_2_10 : subd13_2 [-1, 2] = true := by decide +kernel
theorem subd13_2_11 : subd13_2 [0, -3] = true := by decide +kernel
theorem subd13_2_12 : subd13_2 [0, -2] = true := by decide +kernel
theorem subd13_2_13 : subd13_2 [0, -1] = true := by decide +kernel
theorem subd13_2_14 : subd13_2 [0, 0] = true := by decide +kernel
theorem subd13_2_15 : subd13_2 [0, 1] = true := by decide +kernel
theorem subd13_2_16 : subd13_2 [0, 2] = true := by decide +kernel
theorem subd13_2_17 : subd13_2 [1, -3] = true := by decide +kernel
theorem subd13_2_18 : subd13_2 [1, -2] = true := by decide +kernel
theorem subd13_2_19 : subd13_2 [1, -1] = true := by decide +kernel
theorem subd13_2_20 : subd13_2 [1, 0] = true := by decide +kernel
theorem subd13_2_21 : subd13_2 [1, 1] = true := by decide +kernel
theorem subd13_2_22 : subd13_2 [1, 2] = true := by decide +kernel
theorem subd13_2_23 : subd13_2 [2, -3] = true := by decide +kernel
theorem subd13_2_24 : subd13_2 [2, -2] = true := by decide +kernel
theorem subd13_2_25 : subd13_2 [2, -1] = true := by decide +kernel
theorem subd13_2_26 : subd13_2 [2, 0] = true := by decide +kernel
theorem subd13_2_27 : subd13_2 [2, 1] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_cons.2 ⟨subd13_2_7, List.forall_mem_cons.2 ⟨subd13_2_8, List.forall_mem_cons.2 ⟨subd13_2_9, List.forall_mem_cons.2 ⟨subd13_2_10, List.forall_mem_cons.2 ⟨subd13_2_11, List.forall_mem_cons.2 ⟨subd13_2_12, List.forall_mem_cons.2 ⟨subd13_2_13, List.forall_mem_cons.2 ⟨subd13_2_14, List.forall_mem_cons.2 ⟨subd13_2_15, List.forall_mem_cons.2 ⟨subd13_2_16, List.forall_mem_cons.2 ⟨subd13_2_17, List.forall_mem_cons.2 ⟨subd13_2_18, List.forall_mem_cons.2 ⟨subd13_2_19, List.forall_mem_cons.2 ⟨subd13_2_20, List.forall_mem_cons.2 ⟨subd13_2_21, List.forall_mem_cons.2 ⟨subd13_2_22, List.forall_mem_cons.2 ⟨subd13_2_23, List.forall_mem_cons.2 ⟨subd13_2_24, List.forall_mem_cons.2 ⟨subd13_2_25, List.forall_mem_cons.2 ⟨subd13_2_26, List.forall_mem_cons.2 ⟨subd13_2_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
