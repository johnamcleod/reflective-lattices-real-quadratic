import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-4] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-3, -2] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [-3, -1] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [-3, 0] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [-3, 1] = true := by decide +kernel
theorem subd14_3_5 : subd14_3 [-3, 2] = true := by decide +kernel
theorem subd14_3_6 : subd14_3 [-3, 3] = true := by decide +kernel
theorem subd14_3_7 : subd14_3 [-3, 4] = true := by decide +kernel
theorem subd14_3_8 : subd14_3 [-2, -3] = true := by decide +kernel
theorem subd14_3_9 : subd14_3 [-2, -2] = true := by decide +kernel
theorem subd14_3_10 : subd14_3 [-2, -1] = true := by decide +kernel
theorem subd14_3_11 : subd14_3 [-2, 0] = true := by decide +kernel
theorem subd14_3_12 : subd14_3 [-2, 1] = true := by decide +kernel
theorem subd14_3_13 : subd14_3 [-2, 2] = true := by decide +kernel
theorem subd14_3_14 : subd14_3 [-2, 3] = true := by decide +kernel
theorem subd14_3_15 : subd14_3 [-2, 4] = true := by decide +kernel
theorem subd14_3_16 : subd14_3 [-1, -4] = true := by decide +kernel
theorem subd14_3_17 : subd14_3 [-1, -3] = true := by decide +kernel
theorem subd14_3_18 : subd14_3 [-1, -2] = true := by decide +kernel
theorem subd14_3_19 : subd14_3 [-1, -1] = true := by decide +kernel
theorem subd14_3_20 : subd14_3 [-1, 0] = true := by decide +kernel
theorem subd14_3_21 : subd14_3 [-1, 1] = true := by decide +kernel
theorem subd14_3_22 : subd14_3 [-1, 2] = true := by decide +kernel
theorem subd14_3_23 : subd14_3 [-1, 3] = true := by decide +kernel
theorem subd14_3_24 : subd14_3 [-1, 4] = true := by decide +kernel
theorem subd14_3_25 : subd14_3 [0, -5] = true := by decide +kernel
theorem subd14_3_26 : subd14_3 [0, -4] = true := by decide +kernel
theorem subd14_3_27 : subd14_3 [0, -3] = true := by decide +kernel
theorem subd14_3_28 : subd14_3 [0, -2] = true := by decide +kernel
theorem subd14_3_29 : subd14_3 [0, -1] = true := by decide +kernel
theorem subd14_3_30 : subd14_3 [0, 0] = true := by decide +kernel
theorem subd14_3_31 : subd14_3 [0, 1] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_cons.2 ⟨subd14_3_5, List.forall_mem_cons.2 ⟨subd14_3_6, List.forall_mem_cons.2 ⟨subd14_3_7, List.forall_mem_cons.2 ⟨subd14_3_8, List.forall_mem_cons.2 ⟨subd14_3_9, List.forall_mem_cons.2 ⟨subd14_3_10, List.forall_mem_cons.2 ⟨subd14_3_11, List.forall_mem_cons.2 ⟨subd14_3_12, List.forall_mem_cons.2 ⟨subd14_3_13, List.forall_mem_cons.2 ⟨subd14_3_14, List.forall_mem_cons.2 ⟨subd14_3_15, List.forall_mem_cons.2 ⟨subd14_3_16, List.forall_mem_cons.2 ⟨subd14_3_17, List.forall_mem_cons.2 ⟨subd14_3_18, List.forall_mem_cons.2 ⟨subd14_3_19, List.forall_mem_cons.2 ⟨subd14_3_20, List.forall_mem_cons.2 ⟨subd14_3_21, List.forall_mem_cons.2 ⟨subd14_3_22, List.forall_mem_cons.2 ⟨subd14_3_23, List.forall_mem_cons.2 ⟨subd14_3_24, List.forall_mem_cons.2 ⟨subd14_3_25, List.forall_mem_cons.2 ⟨subd14_3_26, List.forall_mem_cons.2 ⟨subd14_3_27, List.forall_mem_cons.2 ⟨subd14_3_28, List.forall_mem_cons.2 ⟨subd14_3_29, List.forall_mem_cons.2 ⟨subd14_3_30, List.forall_mem_cons.2 ⟨subd14_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_32 : subd14_3 [0, 2] = true := by decide +kernel
theorem subd14_3_33 : subd14_3 [0, 3] = true := by decide +kernel
theorem subd14_3_34 : subd14_3 [0, 4] = true := by decide +kernel
theorem subd14_3_35 : subd14_3 [1, -5] = true := by decide +kernel
theorem subd14_3_36 : subd14_3 [1, -4] = true := by decide +kernel
theorem subd14_3_37 : subd14_3 [1, -3] = true := by decide +kernel
theorem subd14_3_38 : subd14_3 [1, -2] = true := by decide +kernel
theorem subd14_3_39 : subd14_3 [1, -1] = true := by decide +kernel
theorem subd14_3_40 : subd14_3 [1, 0] = true := by decide +kernel
theorem subd14_3_41 : subd14_3 [1, 1] = true := by decide +kernel
theorem subd14_3_42 : subd14_3 [1, 2] = true := by decide +kernel
theorem subd14_3_43 : subd14_3 [1, 3] = true := by decide +kernel
theorem subd14_3_44 : subd14_3 [2, -5] = true := by decide +kernel
theorem subd14_3_45 : subd14_3 [2, -4] = true := by decide +kernel
theorem subd14_3_46 : subd14_3 [2, -3] = true := by decide +kernel
theorem subd14_3_47 : subd14_3 [2, -2] = true := by decide +kernel
theorem subd14_3_48 : subd14_3 [2, -1] = true := by decide +kernel
theorem subd14_3_49 : subd14_3 [2, 0] = true := by decide +kernel
theorem subd14_3_50 : subd14_3 [2, 1] = true := by decide +kernel
theorem subd14_3_51 : subd14_3 [2, 2] = true := by decide +kernel
theorem subd14_3_52 : subd14_3 [3, -5] = true := by decide +kernel
theorem subd14_3_53 : subd14_3 [3, -4] = true := by decide +kernel
theorem subd14_3_54 : subd14_3 [3, -3] = true := by decide +kernel
theorem subd14_3_55 : subd14_3 [3, -2] = true := by decide +kernel
theorem subd14_3_56 : subd14_3 [3, -1] = true := by decide +kernel
theorem subd14_3_57 : subd14_3 [3, 0] = true := by decide +kernel
theorem subd14_3_58 : subd14_3 [3, 1] = true := by decide +kernel
theorem subd14_3_59 : subd14_3 [4] = true := by decide +kernel
theorem sbd14_3_1 : ∀ q ∈ blkd14_3_1, subd14_3 q = true := by
  unfold blkd14_3_1
  exact List.forall_mem_cons.2 ⟨subd14_3_32, List.forall_mem_cons.2 ⟨subd14_3_33, List.forall_mem_cons.2 ⟨subd14_3_34, List.forall_mem_cons.2 ⟨subd14_3_35, List.forall_mem_cons.2 ⟨subd14_3_36, List.forall_mem_cons.2 ⟨subd14_3_37, List.forall_mem_cons.2 ⟨subd14_3_38, List.forall_mem_cons.2 ⟨subd14_3_39, List.forall_mem_cons.2 ⟨subd14_3_40, List.forall_mem_cons.2 ⟨subd14_3_41, List.forall_mem_cons.2 ⟨subd14_3_42, List.forall_mem_cons.2 ⟨subd14_3_43, List.forall_mem_cons.2 ⟨subd14_3_44, List.forall_mem_cons.2 ⟨subd14_3_45, List.forall_mem_cons.2 ⟨subd14_3_46, List.forall_mem_cons.2 ⟨subd14_3_47, List.forall_mem_cons.2 ⟨subd14_3_48, List.forall_mem_cons.2 ⟨subd14_3_49, List.forall_mem_cons.2 ⟨subd14_3_50, List.forall_mem_cons.2 ⟨subd14_3_51, List.forall_mem_cons.2 ⟨subd14_3_52, List.forall_mem_cons.2 ⟨subd14_3_53, List.forall_mem_cons.2 ⟨subd14_3_54, List.forall_mem_cons.2 ⟨subd14_3_55, List.forall_mem_cons.2 ⟨subd14_3_56, List.forall_mem_cons.2 ⟨subd14_3_57, List.forall_mem_cons.2 ⟨subd14_3_58, List.forall_mem_cons.2 ⟨subd14_3_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_4 : ldCheck G d14_4.U d14_4.ms ldd14_4 = true := by decide +kernel
theorem pre_okd14_4 : subPre G cell14 d14_4 = true := by decide +kernel
theorem subd14_4_0 : subd14_4 [-3] = true := by decide +kernel
theorem subd14_4_1 : subd14_4 [-2] = true := by decide +kernel
theorem subd14_4_2 : subd14_4 [-1, -3] = true := by decide +kernel
theorem subd14_4_3 : subd14_4 [-1, -2] = true := by decide +kernel
theorem subd14_4_4 : subd14_4 [-1, -1] = true := by decide +kernel
theorem subd14_4_5 : subd14_4 [-1, 0] = true := by decide +kernel
theorem subd14_4_6 : subd14_4 [-1, 1] = true := by decide +kernel
theorem subd14_4_7 : subd14_4 [-1, 2] = true := by decide +kernel
theorem subd14_4_8 : subd14_4 [-1, 3] = true := by decide +kernel
theorem subd14_4_9 : subd14_4 [0, -4] = true := by decide +kernel
theorem subd14_4_10 : subd14_4 [0, -3] = true := by decide +kernel
theorem subd14_4_11 : subd14_4 [0, -2] = true := by decide +kernel
theorem subd14_4_12 : subd14_4 [0, -1] = true := by decide +kernel
theorem subd14_4_13 : subd14_4 [0, 0] = true := by decide +kernel
theorem subd14_4_14 : subd14_4 [0, 1] = true := by decide +kernel
theorem subd14_4_15 : subd14_4 [0, 2] = true := by decide +kernel
theorem subd14_4_16 : subd14_4 [0, 3] = true := by decide +kernel
theorem subd14_4_17 : subd14_4 [1, -4] = true := by decide +kernel
theorem subd14_4_18 : subd14_4 [1, -3] = true := by decide +kernel
theorem subd14_4_19 : subd14_4 [1, -2] = true := by decide +kernel
theorem subd14_4_20 : subd14_4 [1, -1] = true := by decide +kernel
theorem subd14_4_21 : subd14_4 [1, 0] = true := by decide +kernel
theorem subd14_4_22 : subd14_4 [1, 1] = true := by decide +kernel
theorem subd14_4_23 : subd14_4 [1, 2] = true := by decide +kernel
theorem subd14_4_24 : subd14_4 [2] = true := by decide +kernel
theorem subd14_4_25 : subd14_4 [3] = true := by decide +kernel
theorem sbd14_4_0 : ∀ q ∈ blkd14_4_0, subd14_4 q = true := by
  unfold blkd14_4_0
  exact List.forall_mem_cons.2 ⟨subd14_4_0, List.forall_mem_cons.2 ⟨subd14_4_1, List.forall_mem_cons.2 ⟨subd14_4_2, List.forall_mem_cons.2 ⟨subd14_4_3, List.forall_mem_cons.2 ⟨subd14_4_4, List.forall_mem_cons.2 ⟨subd14_4_5, List.forall_mem_cons.2 ⟨subd14_4_6, List.forall_mem_cons.2 ⟨subd14_4_7, List.forall_mem_cons.2 ⟨subd14_4_8, List.forall_mem_cons.2 ⟨subd14_4_9, List.forall_mem_cons.2 ⟨subd14_4_10, List.forall_mem_cons.2 ⟨subd14_4_11, List.forall_mem_cons.2 ⟨subd14_4_12, List.forall_mem_cons.2 ⟨subd14_4_13, List.forall_mem_cons.2 ⟨subd14_4_14, List.forall_mem_cons.2 ⟨subd14_4_15, List.forall_mem_cons.2 ⟨subd14_4_16, List.forall_mem_cons.2 ⟨subd14_4_17, List.forall_mem_cons.2 ⟨subd14_4_18, List.forall_mem_cons.2 ⟨subd14_4_19, List.forall_mem_cons.2 ⟨subd14_4_20, List.forall_mem_cons.2 ⟨subd14_4_21, List.forall_mem_cons.2 ⟨subd14_4_22, List.forall_mem_cons.2 ⟨subd14_4_23, List.forall_mem_cons.2 ⟨subd14_4_24, List.forall_mem_cons.2 ⟨subd14_4_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_5 : ldCheck G d14_5.U d14_5.ms ldd14_5 = true := by decide +kernel
theorem pre_okd14_5 : subPre G cell14 d14_5 = true := by decide +kernel
theorem subd14_5_0 : subd14_5 [-2] = true := by decide +kernel
theorem subd14_5_1 : subd14_5 [-1] = true := by decide +kernel
theorem subd14_5_2 : subd14_5 [0] = true := by decide +kernel
theorem subd14_5_3 : subd14_5 [1] = true := by decide +kernel
theorem subd14_5_4 : subd14_5 [2] = true := by decide +kernel
theorem sbd14_5_0 : ∀ q ∈ blkd14_5_0, subd14_5 q = true := by
  unfold blkd14_5_0
  exact List.forall_mem_cons.2 ⟨subd14_5_0, List.forall_mem_cons.2 ⟨subd14_5_1, List.forall_mem_cons.2 ⟨subd14_5_2, List.forall_mem_cons.2 ⟨subd14_5_3, List.forall_mem_cons.2 ⟨subd14_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-1] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [0] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [1] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C140
