import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_3_0 : subd13_3 [-3] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2, -3] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-2, -2] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-2, -1] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-2, 0] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-2, 1] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-2, 2] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [-2, 3] = true := by decide +kernel
theorem subd13_3_8 : subd13_3 [-1, -3] = true := by decide +kernel
theorem subd13_3_9 : subd13_3 [-1, -2] = true := by decide +kernel
theorem subd13_3_10 : subd13_3 [-1, -1] = true := by decide +kernel
theorem subd13_3_11 : subd13_3 [-1, 0] = true := by decide +kernel
theorem subd13_3_12 : subd13_3 [-1, 1] = true := by decide +kernel
theorem subd13_3_13 : subd13_3 [-1, 2] = true := by decide +kernel
theorem subd13_3_14 : subd13_3 [-1, 3] = true := by decide +kernel
theorem subd13_3_15 : subd13_3 [0, -4] = true := by decide +kernel
theorem subd13_3_16 : subd13_3 [0, -3] = true := by decide +kernel
theorem subd13_3_17 : subd13_3 [0, -2] = true := by decide +kernel
theorem subd13_3_18 : subd13_3 [0, -1] = true := by decide +kernel
theorem subd13_3_19 : subd13_3 [0, 0] = true := by decide +kernel
theorem subd13_3_20 : subd13_3 [0, 1] = true := by decide +kernel
theorem subd13_3_21 : subd13_3 [0, 2] = true := by decide +kernel
theorem subd13_3_22 : subd13_3 [0, 3] = true := by decide +kernel
theorem subd13_3_23 : subd13_3 [1, -4] = true := by decide +kernel
theorem subd13_3_24 : subd13_3 [1, -3] = true := by decide +kernel
theorem subd13_3_25 : subd13_3 [1, -2] = true := by decide +kernel
theorem subd13_3_26 : subd13_3 [1, -1] = true := by decide +kernel
theorem subd13_3_27 : subd13_3 [1, 0] = true := by decide +kernel
theorem subd13_3_28 : subd13_3 [1, 1] = true := by decide +kernel
theorem subd13_3_29 : subd13_3 [1, 2] = true := by decide +kernel
theorem subd13_3_30 : subd13_3 [2, -4] = true := by decide +kernel
theorem subd13_3_31 : subd13_3 [2, -3] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_cons.2 ⟨subd13_3_7, List.forall_mem_cons.2 ⟨subd13_3_8, List.forall_mem_cons.2 ⟨subd13_3_9, List.forall_mem_cons.2 ⟨subd13_3_10, List.forall_mem_cons.2 ⟨subd13_3_11, List.forall_mem_cons.2 ⟨subd13_3_12, List.forall_mem_cons.2 ⟨subd13_3_13, List.forall_mem_cons.2 ⟨subd13_3_14, List.forall_mem_cons.2 ⟨subd13_3_15, List.forall_mem_cons.2 ⟨subd13_3_16, List.forall_mem_cons.2 ⟨subd13_3_17, List.forall_mem_cons.2 ⟨subd13_3_18, List.forall_mem_cons.2 ⟨subd13_3_19, List.forall_mem_cons.2 ⟨subd13_3_20, List.forall_mem_cons.2 ⟨subd13_3_21, List.forall_mem_cons.2 ⟨subd13_3_22, List.forall_mem_cons.2 ⟨subd13_3_23, List.forall_mem_cons.2 ⟨subd13_3_24, List.forall_mem_cons.2 ⟨subd13_3_25, List.forall_mem_cons.2 ⟨subd13_3_26, List.forall_mem_cons.2 ⟨subd13_3_27, List.forall_mem_cons.2 ⟨subd13_3_28, List.forall_mem_cons.2 ⟨subd13_3_29, List.forall_mem_cons.2 ⟨subd13_3_30, List.forall_mem_cons.2 ⟨subd13_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_32 : subd13_3 [2, -2] = true := by decide +kernel
theorem subd13_3_33 : subd13_3 [2, -1] = true := by decide +kernel
theorem subd13_3_34 : subd13_3 [2, 0] = true := by decide +kernel
theorem subd13_3_35 : subd13_3 [2, 1] = true := by decide +kernel
theorem subd13_3_36 : subd13_3 [2, 2] = true := by decide +kernel
theorem subd13_3_37 : subd13_3 [3] = true := by decide +kernel
theorem sbd13_3_1 : ∀ q ∈ blkd13_3_1, subd13_3 q = true := by
  unfold blkd13_3_1
  exact List.forall_mem_cons.2 ⟨subd13_3_32, List.forall_mem_cons.2 ⟨subd13_3_33, List.forall_mem_cons.2 ⟨subd13_3_34, List.forall_mem_cons.2 ⟨subd13_3_35, List.forall_mem_cons.2 ⟨subd13_3_36, List.forall_mem_cons.2 ⟨subd13_3_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [-3] = true := by decide +kernel
theorem subd13_4_1 : subd13_4 [-2] = true := by decide +kernel
theorem subd13_4_2 : subd13_4 [-1, -4] = true := by decide +kernel
theorem subd13_4_3 : subd13_4 [-1, -3] = true := by decide +kernel
theorem subd13_4_4 : subd13_4 [-1, -2] = true := by decide +kernel
theorem subd13_4_5 : subd13_4 [-1, -1] = true := by decide +kernel
theorem subd13_4_6 : subd13_4 [-1, 0] = true := by decide +kernel
theorem subd13_4_7 : subd13_4 [-1, 1] = true := by decide +kernel
theorem subd13_4_8 : subd13_4 [-1, 2] = true := by decide +kernel
theorem subd13_4_9 : subd13_4 [-1, 3] = true := by decide +kernel
theorem subd13_4_10 : subd13_4 [0, -4] = true := by decide +kernel
theorem subd13_4_11 : subd13_4 [0, -3] = true := by decide +kernel
theorem subd13_4_12 : subd13_4 [0, -2] = true := by decide +kernel
theorem subd13_4_13 : subd13_4 [0, -1] = true := by decide +kernel
theorem subd13_4_14 : subd13_4 [0, 0] = true := by decide +kernel
theorem subd13_4_15 : subd13_4 [0, 1] = true := by decide +kernel
theorem subd13_4_16 : subd13_4 [0, 2] = true := by decide +kernel
theorem subd13_4_17 : subd13_4 [0, 3] = true := by decide +kernel
theorem subd13_4_18 : subd13_4 [1, -4] = true := by decide +kernel
theorem subd13_4_19 : subd13_4 [1, -3] = true := by decide +kernel
theorem subd13_4_20 : subd13_4 [1, -2] = true := by decide +kernel
theorem subd13_4_21 : subd13_4 [1, -1] = true := by decide +kernel
theorem subd13_4_22 : subd13_4 [1, 0] = true := by decide +kernel
theorem subd13_4_23 : subd13_4 [1, 1] = true := by decide +kernel
theorem subd13_4_24 : subd13_4 [1, 2] = true := by decide +kernel
theorem subd13_4_25 : subd13_4 [1, 3] = true := by decide +kernel
theorem subd13_4_26 : subd13_4 [2] = true := by decide +kernel
theorem subd13_4_27 : subd13_4 [3] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_cons.2 ⟨subd13_4_1, List.forall_mem_cons.2 ⟨subd13_4_2, List.forall_mem_cons.2 ⟨subd13_4_3, List.forall_mem_cons.2 ⟨subd13_4_4, List.forall_mem_cons.2 ⟨subd13_4_5, List.forall_mem_cons.2 ⟨subd13_4_6, List.forall_mem_cons.2 ⟨subd13_4_7, List.forall_mem_cons.2 ⟨subd13_4_8, List.forall_mem_cons.2 ⟨subd13_4_9, List.forall_mem_cons.2 ⟨subd13_4_10, List.forall_mem_cons.2 ⟨subd13_4_11, List.forall_mem_cons.2 ⟨subd13_4_12, List.forall_mem_cons.2 ⟨subd13_4_13, List.forall_mem_cons.2 ⟨subd13_4_14, List.forall_mem_cons.2 ⟨subd13_4_15, List.forall_mem_cons.2 ⟨subd13_4_16, List.forall_mem_cons.2 ⟨subd13_4_17, List.forall_mem_cons.2 ⟨subd13_4_18, List.forall_mem_cons.2 ⟨subd13_4_19, List.forall_mem_cons.2 ⟨subd13_4_20, List.forall_mem_cons.2 ⟨subd13_4_21, List.forall_mem_cons.2 ⟨subd13_4_22, List.forall_mem_cons.2 ⟨subd13_4_23, List.forall_mem_cons.2 ⟨subd13_4_24, List.forall_mem_cons.2 ⟨subd13_4_25, List.forall_mem_cons.2 ⟨subd13_4_26, List.forall_mem_cons.2 ⟨subd13_4_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_5 : ldCheck G d13_5.U d13_5.ms ldd13_5 = true := by decide +kernel
theorem pre_okd13_5 : subPre G cell13 d13_5 = true := by decide +kernel
theorem subd13_5_0 : subd13_5 [-2] = true := by decide +kernel
theorem subd13_5_1 : subd13_5 [-1] = true := by decide +kernel
theorem subd13_5_2 : subd13_5 [0] = true := by decide +kernel
theorem subd13_5_3 : subd13_5 [1] = true := by decide +kernel
theorem subd13_5_4 : subd13_5 [2] = true := by decide +kernel
theorem sbd13_5_0 : ∀ q ∈ blkd13_5_0, subd13_5 q = true := by
  unfold blkd13_5_0
  exact List.forall_mem_cons.2 ⟨subd13_5_0, List.forall_mem_cons.2 ⟨subd13_5_1, List.forall_mem_cons.2 ⟨subd13_5_2, List.forall_mem_cons.2 ⟨subd13_5_3, List.forall_mem_cons.2 ⟨subd13_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-1] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [0] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [1] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_nil _⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [-2] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [-1] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [0] = true := by decide +kernel
theorem subd14_2_3 : subd14_2 [1] = true := by decide +kernel
theorem subd14_2_4 : subd14_2 [2] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_cons.2 ⟨subd14_2_3, List.forall_mem_cons.2 ⟨subd14_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
