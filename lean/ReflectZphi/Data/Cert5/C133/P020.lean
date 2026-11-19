import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_nil _⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_nil _⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-2] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-1, -3] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [-1, -2] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [-1, -1] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [-1, 0] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [-1, 1] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [0, -3] = true := by decide +kernel
theorem subd13_2_7 : subd13_2 [0, -2] = true := by decide +kernel
theorem subd13_2_8 : subd13_2 [0, -1] = true := by decide +kernel
theorem subd13_2_9 : subd13_2 [0, 0] = true := by decide +kernel
theorem subd13_2_10 : subd13_2 [0, 1] = true := by decide +kernel
theorem subd13_2_11 : subd13_2 [0, 2] = true := by decide +kernel
theorem subd13_2_12 : subd13_2 [1, -2] = true := by decide +kernel
theorem subd13_2_13 : subd13_2 [1, -1] = true := by decide +kernel
theorem subd13_2_14 : subd13_2 [1, 0] = true := by decide +kernel
theorem subd13_2_15 : subd13_2 [1, 1] = true := by decide +kernel
theorem subd13_2_16 : subd13_2 [1, 2] = true := by decide +kernel
theorem subd13_2_17 : subd13_2 [2] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_cons.2 ⟨subd13_2_7, List.forall_mem_cons.2 ⟨subd13_2_8, List.forall_mem_cons.2 ⟨subd13_2_9, List.forall_mem_cons.2 ⟨subd13_2_10, List.forall_mem_cons.2 ⟨subd13_2_11, List.forall_mem_cons.2 ⟨subd13_2_12, List.forall_mem_cons.2 ⟨subd13_2_13, List.forall_mem_cons.2 ⟨subd13_2_14, List.forall_mem_cons.2 ⟨subd13_2_15, List.forall_mem_cons.2 ⟨subd13_2_16, List.forall_mem_cons.2 ⟨subd13_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-3] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-1, -4] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-1, -3] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-1, -2] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-1, -1] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-1, 0] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [-1, 1] = true := by decide +kernel
theorem subd13_3_8 : subd13_3 [-1, 2] = true := by decide +kernel
theorem subd13_3_9 : subd13_3 [-1, 3] = true := by decide +kernel
theorem subd13_3_10 : subd13_3 [0, -4] = true := by decide +kernel
theorem subd13_3_11 : subd13_3 [0, -3] = true := by decide +kernel
theorem subd13_3_12 : subd13_3 [0, -2] = true := by decide +kernel
theorem subd13_3_13 : subd13_3 [0, -1] = true := by decide +kernel
theorem subd13_3_14 : subd13_3 [0, 0] = true := by decide +kernel
theorem subd13_3_15 : subd13_3 [0, 1] = true := by decide +kernel
theorem subd13_3_16 : subd13_3 [0, 2] = true := by decide +kernel
theorem subd13_3_17 : subd13_3 [0, 3] = true := by decide +kernel
theorem subd13_3_18 : subd13_3 [1, -4] = true := by decide +kernel
theorem subd13_3_19 : subd13_3 [1, -3] = true := by decide +kernel
theorem subd13_3_20 : subd13_3 [1, -2] = true := by decide +kernel
theorem subd13_3_21 : subd13_3 [1, -1] = true := by decide +kernel
theorem subd13_3_22 : subd13_3 [1, 0] = true := by decide +kernel
theorem subd13_3_23 : subd13_3 [1, 1] = true := by decide +kernel
theorem subd13_3_24 : subd13_3 [1, 2] = true := by decide +kernel
theorem subd13_3_25 : subd13_3 [1, 3] = true := by decide +kernel
theorem subd13_3_26 : subd13_3 [2] = true := by decide +kernel
theorem subd13_3_27 : subd13_3 [3] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_cons.2 ⟨subd13_3_7, List.forall_mem_cons.2 ⟨subd13_3_8, List.forall_mem_cons.2 ⟨subd13_3_9, List.forall_mem_cons.2 ⟨subd13_3_10, List.forall_mem_cons.2 ⟨subd13_3_11, List.forall_mem_cons.2 ⟨subd13_3_12, List.forall_mem_cons.2 ⟨subd13_3_13, List.forall_mem_cons.2 ⟨subd13_3_14, List.forall_mem_cons.2 ⟨subd13_3_15, List.forall_mem_cons.2 ⟨subd13_3_16, List.forall_mem_cons.2 ⟨subd13_3_17, List.forall_mem_cons.2 ⟨subd13_3_18, List.forall_mem_cons.2 ⟨subd13_3_19, List.forall_mem_cons.2 ⟨subd13_3_20, List.forall_mem_cons.2 ⟨subd13_3_21, List.forall_mem_cons.2 ⟨subd13_3_22, List.forall_mem_cons.2 ⟨subd13_3_23, List.forall_mem_cons.2 ⟨subd13_3_24, List.forall_mem_cons.2 ⟨subd13_3_25, List.forall_mem_cons.2 ⟨subd13_3_26, List.forall_mem_cons.2 ⟨subd13_3_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_nil _⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C133
